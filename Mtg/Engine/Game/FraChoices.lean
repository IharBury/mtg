import Mtg.Engine.Game.PriorityActions
import Mtg.Engine.Game.FraHelpers

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
  let origSnap := g.snapshot card
  let face := g.baseCard card
  let mv := g.objectManaValue card
  if mv > budget then
    throw s!"{face.name} has mana value {mv}; only {budget} is left"
  if face.isLand then throw "A land can't be cast"
  if face.isModal && !face.spellModes.any (g.spellModeIsChoosable p) && !face.allowsZeroTargets then
    throw s!"{face.name} requires a target"
  if !face.isModal && (face.requiresTarget || face.isAura) &&
      (g.legalCastTargets p face).isEmpty && !face.allowsZeroTargets then
    throw s!"{face.name} requires a target"
  let rest := ids.filter (· != id)
  let g := g.change .saveProposalCheckpoint
  let (g, newId) := g.move id .stack (some p) (verb := some .cast) (actor := some p)
    (isCopy := some true) (cause := some (.gameRule .spellCast))
  let g := g.putStackEntry p newId
  let g := g.record (GameEvent.proposed g.turnNumber newId p card.zone (.alternative "free copy"))
  let g := g.changes #[.pending .none, .pendingFreeCopies (some (p, rest, budget - mv, castsLeft - 1))]
  let g := g.logMsg s!"{(g.player p).name} casts a copy of {face.name} without paying its mana cost"
  let needsSacrifice :=
    face.additionalCostSacrificeCreature ||
      (face.additionalCostSacrificeArtifactOrCreature && face.additionalCostOrPayGeneric.isNone)
  let prop : ProposedSpell := {
    caster := p, cost := ManaCost.empty, spellId := newId, original := card
    originalSnapshot := origSnap, needsSacrificeOther := needsSacrifice
    alternativeCost := true, resolutionCast := true }
  let g' := g.beginResolutionCastTargets p prop
  return if g'.pending == .none && (g'.findObject? newId).any (·.zone == .stack) then
    g'.finishFraChoice
  else g'

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
  { targeting, resolution := .hawkeyeArrows sorted.toList
    phrase := String.intercalate ". " names }

/-- Reveal the face-up pile, then let an opponent choose which pile goes to hand. -/
def continueRiddlesSplit (g : Game) (controller : PlayerId)
    (faceUp faceDown : Array ObjectId) : Game :=
  let g :=
    if faceUp.isEmpty then g
    else g.record (GameEvent.revealed g.turnNumber controller faceUp
      (cause := some (g.resolvingOrRuleCause controller)))
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
    g.applyRiddlesPiles controller faceUp faceDown false (alreadyRevealed := true)

def answerFraChoice (g : Game) (p : PlayerId) (answer : FraAnswer) : Except String Game := do
  let .fraChoice q choice := g.pending | throw "Nothing to choose now"
  if p != q then
    throw s!"Only {(g.player q).name} may choose"
  let isProposalOrAcceptCast : Bool :=
    match choice with
    | .crew .. | .costPicks .. | .zemoBoastExile .. => true
    | .mayCastCascade .. | .mayCastGrima .. | .mayCastCopy ..
    | .mayCastInstantSorceryFromHand .. | .mayCastUpToFromExile ..
    | .mayCastCards .. | .mayCastFromGraveyard .. => answer != .decline
    | _ => false
  let gPre := g
  let g := g.change (.pending .none)
  let g :=
    if !isProposalOrAcceptCast then
      match g.pendingReplacement with
      | some outer =>
        g.changes #[.pushOuterPendingReplacement outer, .pendingReplacement none]
      | none => g
    else g
  match choice, answer with
  | .discardFromRevealedHand victim permanentOnly, .objects #[id] =>
    if !(g.revealedHandChoices victim permanentOnly).contains id then
      throw "That card can't be chosen"
    return (g.discardFromHand victim id (chooser := some p)).finishFraChoice
  | .discardFromRevealedHand .., _ => throw "Choose one card from the revealed hand"
  | .mayWheel n rest, .accept | .mayWheel n rest, .decline =>
    let restModes := rest.map (·.idx)
    if answer == .accept then
      let hand := (g.player p).hand
      let g := g.withBatch none fun g =>
        g.discardHandIdsLoop p hand (logEach := true)
      let g :=
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishPostStep 41 p (n := n) (modes := restModes))
        else
          g.runPostStep 41 p (n := n) (modes := restModes)
      return g.finishFraChoice
    else
      let g := (g.logMsg s!"{(g.player p).name} keeps their hand").runPostStep 42 p (n := n) (modes := restModes)
      return g.finishFraChoice
  | .mayWheel .., _ => throw "Answer accept or decline"
  | .maySacrificePlaneswalker, .objects #[id] =>
    let some pw := g.findObject? id | throw "no such object"
    if !pw.isOnBattlefield || !g.controlledBy pw p || !g.isPlaneswalker pw then
      throw "Choose a planeswalker you control"
    let g := g.sacrificeToGraveyard pw s!"{(g.player p).name} sacrifices {g.name pw}"
    let g :=
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep 43 p)
      else
        g.runPostStep 43 p
    return g.finishFraChoice
  | .maySacrificePlaneswalker, .decline =>
    return (g.logMsg s!"{(g.player p).name} doesn't sacrifice a planeswalker").finishFraChoice
  | .maySacrificePlaneswalker, _ => throw "Choose a planeswalker to sacrifice, or decline"
  | .topOrBottomDamage id damage sid, .accept | .topOrBottomDamage id damage sid, .decline =>
    match g.findObject? id with
    | none => return g.finishFraChoice
    | some o =>
      if !o.isOnBattlefield then return g.finishFraChoice
      else
        let owner := o.owner
        let oName := g.name o
        let src? := sid.bind g.damageSourceById?
        let pos : LibraryPosition := if answer == .accept then .top else .bottom
        let (g, _) := g.move id (.library owner) none (libraryPosition := some pos)
        if answer == .accept then
          let g := g.logMsg s!"{(g.player owner).name} puts {oName} on top of their library"
          return (g.dealDamageToPlayer owner damage (source := src?)).finishFraChoice
        else
          let g := g.logMsg s!"{(g.player owner).name} puts {oName} on the bottom of their library"
          return g.finishFraChoice
  | .topOrBottomDamage .., _ => throw "Choose top or bottom"
  | .sphinxsApproach spellId, .accept =>
    let onStack := (g.findObject? spellId).any (fun o => o.zone == .stack && !o.isCopy)
    let approaches := g.sphinxsApproachesInGraveyard p
    let toExile : Array ObjectId :=
      if onStack then #[spellId] ++ approaches.extract 0 4
      else approaches.extract 0 5
    if toExile.size < 5 then
      return (g.logMsg "There aren't five cards named Sphinx's Approach to exile").finishFraChoice
    let g := g.withBatch none fun g =>
      toExile.foldl (fun g id =>
        let (g, _) := g.move id .exile none
        g) g
    let g := g.logMsg s!"{(g.player p).name} exiles five cards named Sphinx's Approach"
    let g :=
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep 44 p)
      else
        g.runPostStep 44 p
    return g.finishFraChoice
  | .sphinxsApproach _, .decline => return g.finishFraChoice
  | .sphinxsApproach _, _ => throw "Answer accept or decline"
  | .extrapolateReveal, .objects #[a, b] =>
    let ok (id : ObjectId) := (g.findObject? id).any (·.zone == .outside p)
    if !ok a || !ok b then throw "Choose two cards you own from outside the game"
    if (g.object! a).name == (g.object! b).name then
      throw "The two cards must have different names"
    let g := g.record (GameEvent.revealed g.turnNumber p #[a, b]
      (cause := some (g.resolvingOrRuleCause p)))
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
    let some o := g.findObject? id | throw "no such object"
    if !isPublicZone o.zone then throw s!"{o.name} is no longer in a public zone"
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
    let g :=
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.continueUnifiedAbility p default #[next.toResolution] #[] sourceId none 0)
      else
        g.applyFra p default next.toResolution #[] sourceId
    return g.finishFraChoice
  | .mayDiscardThen .., .decline => return g.finishFraChoice
  | .mayDiscardThen .., _ => throw "Choose a card to discard, or decline"
  | .discardThen _ _ causeId, .objects #[id] =>
    if !(g.player p).hand.contains id then throw "That card is not in your hand"
    let g := g.discardFromHand p id
    let g :=
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep 45 p (sourceId := causeId))
      else
        g.runPostStep 45 p (sourceId := causeId)
    return g.finishFraChoice
  | .discardThen .., _ => throw "Choose a card to discard"
  | .discardThenStun n sourceId, .objects ids =>
    let need := Nat.min n (g.player p).hand.size
    if ids.size != need || !ids.all ((g.player p).hand.contains ·) ||
        ids.toList.eraseDups.length != ids.size then
      throw s!"Choose {need} different cards from your hand"
    let nonland := (ids.filter (fun id => !g.isLand (g.object! id))).size
    let g := g.withBatch none fun g =>
      g.discardHandIdsLoop p ids (logEach := true)
    let g :=
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep 46 p (n := nonland) (sourceId := sourceId))
      else
        g.runPostStep 46 p (n := nonland) (sourceId := sourceId)
    return g.finishFraChoice
  | .discardThenStun .., _ => throw "Choose the cards to discard"
  | .maySacrificeThen types next sourceId, .objects #[id] =>
    let some o := g.findObject? id | throw "no such object"
    let ok := o.isOnBattlefield && g.controlledBy o p && types.any (g.hasType o)
    if !ok then throw s!"Can't sacrifice {g.name o}"
    let g := g.sacrificeToGraveyard o s!"{(g.player p).name} sacrifices {g.name o}"
    let g :=
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.continueUnifiedAbility p default #[next.toResolution] #[] sourceId none 0)
      else
        g.applyFra p default next.toResolution #[] sourceId
    return g.finishFraChoice
  | .maySacrificeThen .., .decline => return g.finishFraChoice
  | .maySacrificeThen .., _ => throw "Choose a permanent to sacrifice, or decline"
  | .mayMovePlusOne sourceId, .accept =>
    match g.findObject? sourceId with
    | some o =>
      if o.isOnBattlefield && o.status.plusOnePlusOne > 0 then
        let g := g.withBatch none fun g =>
          let oName := g.name o
          let g := (g.recordRemoveCounters o.id .plusOnePlusOne 1 (byPlayer := some p)).logMsg
            s!"A +1/+1 counter is removed from {oName}"
          (g.creaturesControlledBy p).foldl (fun g c =>
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
    let g := g.changeObject ex (.exiledBy sourceId)
    return (g.logMsg s!"{(g.player p).name} exiles {name} from {(g.player victim).name}'s hand").finishFraChoice
  | .exileFromRevealedHand .., _ => throw "Choose a nonland card from the revealed hand"
  | .castCopiesFree ids _ _, .decline =>
    let g := g.withBatch none fun g =>
      ids.foldl (fun g id =>
        if (g.findObject? id).any (·.zone == .exile) then
          g.ceaseToExist id (cause := some (.stateBased .copyOutsideStackOrBf))
        else g) g
    return (g.change (.pendingFreeCopies none)).finishFraChoice
  | .castCopiesFree .., _ => throw "Cast a copy, or decline"
  | .allianceMode sourceId available, .mode idx =>
    if !available.contains idx then throw "That Alliance mode has already been chosen this turn"
    return (g.answerChooseMode sourceId idx
      (fun g => g.applyAllianceMode sourceId idx)).finishFraChoice
  | .allianceMode .., _ => throw "Choose an Alliance mode"
  | .gollumMode sourceId available, .mode idx =>
    if !available.contains idx then throw "That mode has already been chosen"
    return (g.answerChooseMode sourceId idx
      (fun g => g.applyGollumMode sourceId idx)).finishFraChoice
  | .gollumMode .., _ => throw "Choose a mode"
  | .triggerModes objId remaining chosen, .mode idx =>
    let some obj := g.findObject? objId | return g.finishFraChoice
    let modes := g.triggerModesOf obj
    let some e := modes[idx]? | throw "No such mode (CR 700.2)"
    if chosen.contains idx then throw "That mode was already chosen (CR 700.2d)"
    if !g.triggerModeChoosable p obj e then
      throw "That mode has no legal target (CR 603.3c / 700.2b)"
    let g := g.logMsg s!"{(g.player p).name} chooses mode {idx + 1} ({e.phrase})"
    let chosen := chosen.push idx
    let left := remaining - 1
    let anyLeft := (List.range modes.size).any (fun i =>
      !chosen.contains i && (modes[i]?.any (g.triggerModeChoosable p obj)))
    if left > 0 && anyLeft then
      return g.change (.pending (.fraChoice p (.triggerModes objId left chosen)))
    match combineTriggerModes modes chosen with
    | none => return g.finishFraChoice
    | some eff =>
      let g := g.changeObject obj.id (.abilityEffect (some eff))
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
  | .sacrificeCreatureEach controller rest chosen, .objects #[id] =>
    let some o := g.findObject? id | throw "no such object"
    if !o.isOnBattlefield || !g.isCreature o || !g.controlledBy o p then
      throw "Choose a creature you control"
    let g := g.logMsg s!"{(g.player p).name} chooses {g.name o}"
    return (g.continueSacrificeEach controller rest (chosen.push id)).finishFraChoice
  | .sacrificeCreatureEach .., _ => throw "Choose a creature to sacrifice"
  | .discardTwo controller rest draws, .objects ids =>
    let hand := (g.player p).hand
    if ids.size != 2 || ids[0]! == ids[1]! || !ids.all hand.contains then
      throw "Choose two different cards from your hand"
    let nonland := (ids.filter (fun id => !g.isLand (g.object! id))).size
    let nextDraws := if nonland < 2 then draws + 1 else draws
    let g := g.withBatch none fun g =>
      g.discardHandIdsLoop p ids (logEach := true)
    let g :=
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep 10 controller (n := nextDraws) (modes := rest.map (fun (q : PlayerId) => q.idx)))
      else
        g.continueDiscardTwo controller rest nextDraws
    return g.finishFraChoice
  | .discardTwo .., _ => throw "Choose two cards to discard"
  | .mayMoveAllCounters fromId toId, .accept =>
    match g.findObject? fromId, g.findObject? toId with
    | some src, some dst =>
      if !src.isOnBattlefield || !dst.isOnBattlefield then return g.finishFraChoice
      else
        let g := g.withBatch none fun g =>
          let moved := src.status
          let srcName := g.name src
          let g := g.removeAllCountersFrom src.id (byPlayer := some p)
          let dst := g.object! toId
          let g := g.putCountersExceptPlusOne dst.id moved (byPlayer := some p)
          let g :=
            if moved.plusOnePlusOne > 0 then g.addPlusOnePlusOneTo (g.object! toId) moved.plusOnePlusOne
            else g
          g.logMsg s!"All counters move from {srcName} onto {g.name (g.object! toId)}"
        return g.finishFraChoice
    | _, _ => return g.finishFraChoice
  | .mayMoveAllCounters .., .decline => return g.finishFraChoice
  | .mayMoveAllCounters .., _ => throw "Answer accept or decline"
  | .crew abilityId vehicleId n, .objects ids =>
    let some vehicle := g.findObject? vehicleId | throw "The Vehicle is gone"
    let vName := g.name vehicle
    if ids.toList.eraseDups.length != ids.size then throw "Choose each creature once"
    let crew ← ids.mapM (fun id => do
      let some c := g.findObject? id | throw "no such object"
      if !c.isOnBattlefield || !g.isCreature c || !g.controlledBy c p || c.status.tapped || id == vehicleId then
        throw s!"{g.name c} can't crew {vName}"
      pure c)
    let total := crew.foldl (fun acc c => acc + (g.power c).toNat) 0
    if total < n then throw s!"Total power {total} is less than {n}"
    let outerCont? := g.pendingReplacement
    let openCont := g.proposalHadOpenContinuation
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let cause := some (EventCause.costPayment .tap p (some abilityId))
    let g := g.withBatch cause fun g =>
      crew.foldl (fun g c =>
        g.becomeTapped (g.object! c.id) (cause := cause)) g
    let paused := match g.pending with | .chooseReplacement .. => true | _ => false
    let g :=
      if !paused then
        match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
      else g
    let g := g.logMsg s!"{(g.player p).name} crews {vName}"
    let g := g.becomeActivated p vName (some vehicleId)
      (abilityId := some abilityId)
      (hadOuterReplacement := outerCont?.isSome)
      (hadOpenContinuation := some openCont)
    let g :=
      if paused then
        match outerCont? with
        | some outer => g.chainPendingReplacement outer.ensureEndsWithFinishFra
        | none => g
      else g
    return g.resumeAfterBecomeCast
  | .crew _ _ _, .decline =>
    let baseTriggers := (g.proposalCheckpoint.map (·.waitingTriggers.size)).getD 0
    let g ← g.reverseToProposalCheckpoint?
    let g := g.logMsg s!"{(g.player p).name} doesn't crew"
    if !g.continuations.isEmpty || g.pendingReplacement.isSome then
      return g.finishFraChoice
    else if g.pending == .none && g.continuations.isEmpty && g.waitingTriggers.size > baseTriggers then
      return g.receivePriority p
    else
      return g
  | .crew .., _ => throw "Choose creatures to tap, or decline"
  | .costPicks sourceId picks _, .objects ids =>
    let some prop := g.proposedSpell | throw "No activation is being paid for"
    let some pick := picks[0]? | throw "No cost is left to pay"
    if (gPre.costPickCandidates p sourceId pick).size < pick.count then
      return (← gPre.reverseProposedSpell? (resumeContinuation := true))
    let outerCont? := g.pendingReplacement
    let openCont := g.proposalHadOpenContinuation
    let g0 := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g ← g0.withProposalActionM .costAction fun g =>
      g.payCostPick p prop.spellId sourceId pick ids
    let restPicks := picks.extract 1 picks.size
    let pausedBeforeContinue := match g.pending with | .chooseReplacement .. => true | _ => false
    if restPicks.isEmpty && !pausedBeforeContinue then
      let g :=
        match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
      let g ← g.continueCostPicks prop restPicks true
        (hadOuterReplacement := outerCont?.isSome)
        (hadOpenContinuation := some openCont)
      if g.proposedSpell.isNone && !(g.findObject? prop.spellId).any (·.zone == .stack) then
        return g
      return g.resumeAfterBecomeCast
    else
      let g ← g.continueCostPicks prop restPicks true
        (hadOuterReplacement := outerCont?.isSome)
        (hadOpenContinuation := some openCont)
      if g.proposedSpell.isNone && !(g.findObject? prop.spellId).any (·.zone == .stack) then
        return g
      let g :=
        match outerCont? with
        | some outer =>
          let nextOuter := if restPicks.isEmpty then outer.ensureEndsWithFinishFra else outer
          g.chainPendingReplacement nextOuter
        | none => g
      return g.resumeAfterBecomeCast
  | .costPicks _ _ false, .decline =>
    g.reverseProposedSpell? (resumeContinuation := true)
  | .costPicks sourceId picks true, .decline =>
    if let some pick := picks[0]? then
      if (gPre.costPickCandidates p sourceId pick).size < pick.count then
        return (← gPre.reverseProposedSpell? (resumeContinuation := true))
    throw "Part of the cost is already paid; the activation can't be cancelled"
  | .costPicks .., _ => throw "Choose what to pay the cost with, or decline to cancel"
  | .chooseCreatureType types, .mode idx =>
    let some sub := types[idx]? | throw "No such creature type"
    let n := ((g.creaturesControlledBy p).filter (fun o => g.hasSubtype o sub)).size
    let g := g.logMsg s!"{(g.player p).name} chooses {sub}"
    return (g.createTreasureTokens p n).finishFraChoice
  | .chooseCreatureType _, .name t =>
    let some sub := CardSubtype.ofOracle? t | throw "Choose a creature type"
    let n := ((g.creaturesControlledBy p).filter (fun o => g.hasSubtype o sub)).size
    let g := g.logMsg s!"{(g.player p).name} chooses {sub}"
    return (g.createTreasureTokens p n).finishFraChoice
  | .chooseCreatureType _, _ => throw "Choose a creature type"
  | .maySacrificeAnotherCreatureForPower sourceId, .objects #[id] =>
    let some o := g.findObject? id | throw "no such object"
    if o.id == sourceId || !o.isOnBattlefield || !g.controlledBy o p || !g.isCreature o then
      throw s!"Can't sacrifice {g.name o}"
    let pw := (g.power o).toNat
    let g := g.sacrificeToGraveyard o s!"{(g.player p).name} sacrifices {g.name o}"
    if g.mayThenDrop > 0 then
      return (g.change (.sacrificedPowerThisWay (some pw))).acceptMayThen
    else
      let g :=
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishPostStep 53 p (n := pw) (sourceId := some sourceId))
        else
          g.runPostStep 53 p (n := pw) (sourceId := some sourceId)
      return g.finishFraChoice
  | .maySacrificeAnotherCreatureForPower _, .decline =>
    if g.mayThenDrop > 0 then return g.declineMayThen else return g.finishFraChoice
  | .maySacrificeAnotherCreatureForPower _, _ => throw "Choose a creature to sacrifice, or decline"
  | .maySacrificeAnotherForDrawTreasure sourceId, .objects #[id] =>
    let some o := g.findObject? id | throw "no such object"
    if o.id == sourceId || !o.isOnBattlefield || !g.controlledBy o p ||
        !(g.isCreature o || g.isArtifact o) then
      throw s!"Can't sacrifice {g.name o}"
    let g := g.sacrificeToGraveyard o s!"{(g.player p).name} sacrifices {g.name o}"
    if g.mayThenDrop > 0 then
      return g.acceptMayThen
    else
      let drawn : Effect := {
        resolution := .sequence [.draw 1, .createTokens .treasure 1]
        phrase := "Draw a card and create a Treasure" }
      let g :=
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement
            (.continueUnifiedAbility p drawn #[.draw 1, .createTokens .treasure 1] #[] (some sourceId) none 0)
        else
          g.applyUnifiedAbility p drawn #[] (some sourceId)
      return g.finishFraChoice
  | .maySacrificeAnotherForDrawTreasure _, .decline =>
    if g.mayThenDrop > 0 then return g.declineMayThen else return g.finishFraChoice
  | .maySacrificeAnotherForDrawTreasure _, _ => throw "Choose a creature or artifact to sacrifice, or decline"
  | .maySacrificeThese n ids, .objects chosen =>
    if chosen.size != n || chosen.toList.eraseDups.length != chosen.size ||
        !chosen.all (ids.contains ·) then
      throw s!"Choose {n} to sacrifice, or decline"
    for id in chosen do
      let some o := g.findObject? id | throw "no such object"
      if !o.isOnBattlefield || !g.controlledBy o p then
        throw s!"Can't sacrifice {g.name o}"
    let preBf := g.battlefield
    let g := g.withBatch none fun g =>
      g.sacrificePermanentsLoop (chosen.map ((p, ·))) (preBattlefield := some preBf)
    if g.mayThenDrop > 0 then
      return g.acceptMayThen
    else
      return g.finishFraChoice
  | .maySacrificeThese _ _, .decline =>
    if g.mayThenDrop > 0 then return g.declineMayThen else return g.finishFraChoice
  | .maySacrificeThese n _, _ => throw s!"Choose {n} to sacrifice, or decline"
  | .mayDiscardThese n ids, .objects chosen =>
    if chosen.size != n || chosen.toList.eraseDups.length != chosen.size ||
        !chosen.all (ids.contains ·) then
      throw s!"Choose {n} to discard, or decline"
    for id in chosen do
      let some o := g.findObject? id | throw "no such object"
      if o.owner != p || o.zone != .hand p then
        throw s!"Can't discard {o.name}"
    let g := g.withBatch none fun g =>
      g.discardHandIdsLoop p chosen (logEach := true)
    if g.mayThenDrop > 0 then
      return g.acceptMayThen
    else
      return g.finishFraChoice
  | .mayDiscardThese _ _, .decline =>
    if g.mayThenDrop > 0 then return g.declineMayThen else return g.finishFraChoice
  | .mayDiscardThese n _, _ => throw s!"Choose {n} to discard, or decline"
  | .mayPaySymbolsThen symbols next sourceId, .accept =>
    let cost : ManaCost := { symbols := symbols }
    if !(g.player p).manaPool.canPay cost then
      throw s!"{(g.player p).name} cannot pay that cost; add mana first"
    let g ← g.payCost p cost
    if g.mayThenDrop > 0 then
      return g.acceptMayThen
    else
      return (g.applyFra p default next.toResolution #[] (some sourceId)).finishFraChoice
  | .mayPaySymbolsThen .., .decline =>
    if g.mayThenDrop > 0 then return g.declineMayThen else return g.finishFraChoice
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
    if attached > 0 && host.isOnBattlefield then
      g := g.change (.equipmentAttachedHost (some hostId))
    return g.finishFraChoice
  | .attachAnyEquipment .., .decline => return g.finishFraChoice
  | .attachAnyEquipment .., _ => throw "Choose Equipment to attach, or decline"
  | .sacrificeLeastPower ids, .objects #[id] =>
    if !ids.contains id then throw "Choose a creature tied for the least power"
    return (g.sacrificeLeastPowerCreature p (some id)).finishFraChoice
  | .sacrificeLeastPower _, _ => throw "Choose a creature tied for the least power"
  | .mayPayPickThen pick next sourceId, .objects ids =>
    let g ← g.payCostPick p sourceId sourceId pick ids
    if g.mayThenDrop > 0 then
      return g.acceptMayThen
    else
      let g :=
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement
            (.continueUnifiedAbility p default #[next.toResolution] #[] (some sourceId) none 0)
        else
          g.applyFra p default next.toResolution #[] (some sourceId)
      return g.finishFraChoice
  | .mayPayPickThen .., .decline =>
    if g.mayThenDrop > 0 then return g.declineMayThen else return g.finishFraChoice
  | .mayPayPickThen pick .., _ => throw s!"Choose what to {pick.phrase}, or decline"
  | .addManaColors left use, .mode idx =>
    let some c := Color.all[idx]? | throw "Choose white, blue, black, red, or green (0-4)"
    let g := g.addMana p (.colored c) 1
      (source := g.currentResolvingContext?.bind Prod.fst)
      (restriction := some (.fra use))
    let g := g.logMsg s!"{(g.player p).name} adds {ManaType.colored c} ({use.label})"
    if left > 1 then return g.change (.pending (.fraChoice p (.addManaColors (left - 1) use)))
    return g.finishFraChoice
  | .addManaColors .., _ => throw "Choose a color for the mana"
  | .mayPayExtort _, .accept =>
    let cost : ManaCost := { symbols := #[.hybrid .white .black] }
    if !(g.player p).manaPool.canPay cost then
      throw s!"{(g.player p).name} cannot pay \{W/B}; add mana first"
    let g ← g.payCost p cost
    return (g.extortDrain p).finishFraChoice
  | .mayPayExtort _, .decline => return (g.logMsg "Extort is not paid").finishFraChoice
  | .mayPayExtort _, _ => throw "Pay {W/B} (accept), or decline"
  | .mayDrawThenDiscard n k, .accept =>
    return (g.drawThenBeginDiscard p n (discardRounds := k)).finishFraChoice
  | .mayDrawThenDiscard .., .decline => return g.finishFraChoice
  | .mayDrawThenDiscard .., _ => throw "Answer accept or decline"
  | .sacrificeNontokenEach rest chosen, .objects #[id] =>
    let some o := g.findObject? id | throw "no such object"
    if !o.isOnBattlefield || !g.isCreature o || o.printed.isToken || !g.controlledBy o p then
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
        let g := g.createEffect (.setBasePTUntilEot o.id (pw, tw))
        return (g.logMsg s!"{g.name o}'s base power and toughness become {pw}/{tw} until end of turn").finishFraChoice
      else return g.finishFraChoice
    | none => return g.finishFraChoice
  | .mayBecomeBasePT .., .decline => return g.finishFraChoice
  | .mayBecomeBasePT .., _ => throw "Answer accept or decline"
  | .mayRevealToHand looked eligible anyOrder, .objects #[id] =>
    if !eligible.contains id then throw "Choose one of the eligible cards"
    let name := (g.object! id).name
    let (g, cause) := g.allocDelayedCause (some p)
    let g := g.record (GameEvent.revealed g.turnNumber p #[id] (cause := some cause))
    let (g, _) := g.move id (.hand p) none (cause := some cause)
    let g := g.logMsg s!"{(g.player p).name} reveals {name} and puts it into their hand"
    let rest := looked.filter (· != id)
    let g :=
      if anyOrder then g.offerBottomAnyOrder p rest (cause := some cause)
      else g.requestOrderInto rest (.library p)
        s!"{(g.player p).name} puts the rest on the bottom of their library in a random order"
        (cause := some cause)
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
    let (g, cause) := g.allocDelayedCause (some p)
    let g := g.enterFromNickFury p id (cause := some cause)
    let g :=
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep 47 p (cardId := some id) (ids := rest) (cause := some cause))
      else
        g.runPostStep 47 p (cardId := some id) (ids := rest) (cause := some cause)
    return g.finishFraChoice
  | .nickFuryPut looked _, .decline =>
    return (g.putRestOnBottomRandom p looked).finishFraChoice
  | .nickFuryPut .., _ => throw "Put a card onto the battlefield, or decline"
  | .nickFuryMayTransform id rest, .accept =>
    let cause := g.lastMoveCauseOf? id
    let g := g.transformPermanent p (some id) (cause := cause)
    return (g.putRestOnBottomRandom p rest (cause := cause)).finishFraChoice
  | .nickFuryMayTransform id rest, .decline =>
    let cause := g.lastMoveCauseOf? id
    return (g.putRestOnBottomRandom p rest (cause := cause)).finishFraChoice
  | .nickFuryMayTransform .., _ => throw "Transform it (accept), or decline"
  | .orderLibraryBottom ids, .objects ordered =>
    if ordered.size != ids.size || ordered.toList.eraseDups.length != ordered.size ||
        !ordered.all (ids.contains ·) then
      throw "Put every remaining card on the bottom, in the order you choose"
    let cause := g.stashedCause.orElse (fun _ => ids[0]?.bind g.lastMoveCauseOf?)
    let g := if g.stashedCause.isSome then g.change (.stashedCause none) else g
    return (g.moveIdsInOrder ordered (.library p) (cause := cause)
      |>.logMsg s!"{(g.player p).name} puts the rest on the bottom of their library in the chosen order").finishFraChoice
  | .orderLibraryBottom ids, .decline =>
    let cause := g.stashedCause.orElse (fun _ => ids[0]?.bind g.lastMoveCauseOf?)
    let g := if g.stashedCause.isSome then g.change (.stashedCause none) else g
    return (g.moveIdsInOrder ids (.library p) (cause := cause)
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
    if g.mayThenDrop > 0 then
      return g.acceptMayThen
    else
      return (g.applyFra p default (.queueMshReflexive kind times) #[] sourceId).finishFraChoice
  | .mayPayManaForReflexive .., .decline =>
    let g := g.logMsg "The cost isn't paid. The reflexive ability doesn't trigger."
    if g.mayThenDrop > 0 then return g.declineMayThen
    else return g.finishFraChoice
  | .mayPayManaForReflexive .., _ => throw "Pay (accept, or a number of times), or decline"
  | .mayTapSourceThen next sourceId, .accept =>
    match g.findObject? sourceId with
    | some o =>
      if o.isOnBattlefield && !o.status.tapped then
        let g := g.becomeTapped o
        if g.mayThenDrop > 0 then
          return g.acceptMayThen
        else
          return (g.applyFra p default next.toResolution #[] (some sourceId)).finishFraChoice
      else throw s!"{o.name} can't be tapped"
    | none => throw "The source is gone"
  | .mayTapSourceThen .., .decline =>
    if g.mayThenDrop > 0 then return g.declineMayThen else return g.finishFraChoice
  | .mayTapSourceThen .., _ => throw "Answer accept or decline"
  | .hawkeyeModes left chosen sourceId, .mode idx =>
    if idx > 2 then throw "Choose Net (0), Explosive (1), or Boomerang (2)"
    if chosen.contains idx then throw "That mode was already chosen (CR 700.2)"
    let chosen := chosen.push idx
    if chosen.size < left && chosen.size < 3 then
      return g.change (.pending (.fraChoice p (.hawkeyeModes left chosen sourceId)))
    return (g.putReflexiveTrigger p sourceId (hawkeyeArrowsEffect chosen) (deferToPriority := true)).finishFraChoice
  | .hawkeyeModes _ chosen sourceId, .decline =>
    if chosen.isEmpty then return g.finishFraChoice
    return (g.putReflexiveTrigger p sourceId (hawkeyeArrowsEffect chosen) (deferToPriority := true)).finishFraChoice
  | .hawkeyeModes .., _ => throw "Choose a mode, or decline to stop"
  | .discardThenDraw, .objects #[id] =>
    if !(g.player p).hand.contains id then throw "That card is not in your hand"
    return ((g.discardFromHand p id).draw p 1).finishFraChoice
  | .discardThenDraw, _ => throw "Choose a card to discard"
  | .zemoBoastExile abilityId sourceId, .objects ids =>
    if ids.toList.eraseDups.length != ids.size then throw "Choose each card once"
    let col :=
      match g.findObject? sourceId with
      | some src => TextChange.applyColor (g.evalLayer3 src) .black
      | none => .black
    if !g.canPayZemoBoast p ids col then
      throw "Choose black cards from your graveyard with fifteen or more black mana symbols among their mana costs"
    let outerCont? := g.pendingReplacement
    let openCont := g.proposalHadOpenContinuation
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let (g, exiled) := ids.foldl (fun (acc : Game × Array ObjectId) id =>
      let (g, ex) := acc.1.move id .exile none
        (cause := some (.costPayment .exile p (some abilityId)))
      (g, acc.2.push ex)) (g, #[])
    let paused := match g.pending with | .chooseReplacement .. => true | _ => false
    let g :=
      if !paused then
        match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
      else g
    let g := g.logMsg s!"{(g.player p).name} exiles {exiled.size} card(s) from their graveyard"
    let g := match g.findObject? sourceId with
      | some src => g.logMsg s!"{src.name}'s boast ability is activated"
      | none => g
    let name := ((g.findObject? sourceId).map (·.name)).getD "Baron Helmut Zemo"
    let g := g.becomeActivated p name (some sourceId) (some ActivatedAbility.zemoBoastAbility)
      (abilityId := some abilityId)
      (hadOuterReplacement := outerCont?.isSome)
      (hadOpenContinuation := some openCont)
    let g :=
      if paused then
        match outerCont? with
        | some outer => g.chainPendingReplacement outer.ensureEndsWithFinishFra
        | none => g
      else g
    return g.resumeAfterBecomeCast
  | .zemoBoastExile _ _, .decline =>
    let baseTriggers := (g.proposalCheckpoint.map (·.waitingTriggers.size)).getD 0
    let g ← g.reverseToProposalCheckpoint?
    let g := g.logMsg s!"{(g.player p).name} doesn't boast"
    if !g.continuations.isEmpty || g.pendingReplacement.isSome then
      return g.finishFraChoice
    else if g.pending == .none && g.continuations.isEmpty && g.waitingTriggers.size > baseTriggers then
      return g.receivePriority p
    else
      return g
  | .zemoBoastExile .., _ => throw "Choose the cards to exile, or decline"
  | .mayCastCascade cardId others, .accept =>
    let g :=
      if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
    let g := g.changes #[
      .postCastCleanup (some (.cascadeBottom p cardId others)),
      .pending .none,
      .saveProposalCheckpoint
    ]
    let g := g.castAsPartOfResolution p cardId (callerCheckpoint := true)
    let g :=
      if g.proposedSpell.isNone && g.postCastCleanup.isSome then
        g.runPostCastCleanup
      else g
    return g.finishFraChoice
  | .mayCastCascade cardId others, .decline =>
    let cause := g.lastMoveCauseOf? cardId
    return (g.requestOrderInto (others.push cardId) (.library p)
      s!"{(g.player p).name} puts the exiled cards on the bottom of their library in a random order"
      (cause := cause)).finishFraChoice
  | .mayCastCascade .., _ => throw "Cast it (accept), or decline"
  | .mayCastGrima cardId others victim, .accept =>
    let g :=
      if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
    let g := g.changes #[
      .postCastCleanup (some (.grimaBottom victim cardId others)),
      .pending .none,
      .saveProposalCheckpoint
    ]
    let g := g.castAsPartOfResolution p cardId (callerCheckpoint := true)
    let g :=
      if g.proposedSpell.isNone && g.postCastCleanup.isSome then
        g.runPostCastCleanup
      else g
    return g.finishFraChoice
  | .mayCastGrima cardId others victim, .decline =>
    let cause := g.lastMoveCauseOf? cardId
    return (g.requestOrderInto (others.push cardId) (.library victim)
      s!"{(g.player victim).name} puts the exiled cards on the bottom of their library in a random order"
      (cause := cause)).finishFraChoice
  | .mayCastGrima .., _ => throw "Cast it (accept), or decline"
  | .mayCastCopy copyId, .accept =>
    let g :=
      if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
    let g := g.changes #[
      .postCastCleanup (some (.copyCeaseToExist copyId)),
      .pending .none,
      .saveProposalCheckpoint
    ]
    let g := g.castAsPartOfResolution p copyId (callerCheckpoint := true)
    let g :=
      if g.proposedSpell.isNone && g.postCastCleanup.isSome then
        g.runPostCastCleanup
      else g
    return g.finishFraChoice
  | .mayCastCopy copyId, .decline =>
    let g :=
      match g.findObject? copyId with
      | some o =>
        (g.ceaseToExist o.id (cause := some (.stateBased .copyOutsideStackOrBf))).logMsg
          s!"The copy of {o.name} ceases to exist"
      | none => g
    return g.finishFraChoice
  | .mayCastCopy _, _ => throw "Cast the copy (accept), or decline"
  | .mayDiscardHandBalin sourceId, .accept =>
    let n := (g.player p).hand.size
    let g := g.discardEntireHand p
    let g :=
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep 48 p (n := n) (sourceId := sourceId))
      else
        g.runPostStep 48 p (n := n) (sourceId := sourceId)
    return g.finishFraChoice
  | .mayDiscardHandBalin _, .decline =>
    return (g.logMsg s!"{(g.player p).name} does not discard their hand").finishFraChoice
  | .mayDiscardHandBalin _, _ => throw "Discard your hand (accept), or decline"
  | .mayDiscardHandDrawFixed n, .accept =>
    if g.mayThenDrop > 0 then
      return (g.discardEntireHand p).acceptMayThen
    else
      return (g.discardHandThenDraw p n).finishFraChoice
  | .mayDiscardHandDrawFixed _, .decline =>
    let g := g.logMsg s!"{(g.player p).name} does not discard their hand"
    if g.mayThenDrop > 0 then return g.declineMayThen else return g.finishFraChoice
  | .mayDiscardHandDrawFixed _, _ => throw "Discard your hand (accept), or decline"
  | .sacrificeDamager ids rest controller chosen, .objects #[id] =>
    if !ids.contains id then throw "Choose a creature that dealt combat damage"
    let some o := g.findObject? id | throw "no such object"
    if !o.isOnBattlefield || !g.isCreature o || !g.controlledBy o p then
      throw s!"Can't sacrifice {g.name o}"
    let g := g.logMsg s!"{(g.player p).name} chooses {g.name o}"
    return (g.beginSacDamagers controller rest (chosen.push (p, id))).finishFraChoice
  | .sacrificeDamager .., _ => throw "Choose a creature that dealt combat damage"
  | .mayCastInstantSorceryFromHand eligible, .objects #[id] =>
    if !eligible.contains id then throw "That card can't be cast this way"
    let some o := g.findObject? id | throw "no such object"
    if o.zone != .hand p || !g.isInstantOrSorcery o then
      throw s!"{o.name} is no longer an instant or sorcery in your hand"
    let face := g.baseCard o
    if face.isModal && !face.spellModes.any (g.spellModeIsChoosable p) && !face.allowsZeroTargets then
      throw s!"{face.name} has no mode with a legal target"
    if !face.isModal && (face.requiresTarget || face.isAura) &&
        (g.legalCastTargets p face).isEmpty && !face.allowsZeroTargets then
      throw s!"{face.name} has no legal target"
    let g := (gPre.change .saveProposalCheckpoint).change (.pending .none)
    return (g.castAsPartOfResolution p id (callerCheckpoint := true)).finishFraChoice
  | .mayCastInstantSorceryFromHand _, .decline =>
    return (g.logMsg s!"{(g.player p).name} declines to cast a spell").finishFraChoice
  | .mayCastInstantSorceryFromHand _, _ => throw "Choose a spell to cast, or decline"
  | .mayCastUpToFromExile eligible left, .objects #[id] =>
    if left == 0 || !eligible.contains id then throw "That card can't be cast this way"
    let some o := g.findObject? id | throw "no such object"
    if o.zone != .exile || g.isLand o then
      throw s!"{o.name} can't be cast this way"
    let rest := eligible.filter (· != id)
    let g := (gPre.change .saveProposalCheckpoint).changes #[
      .pending .none,
      .pendingMayCastFromExile (if left > 1 && !rest.isEmpty then some (p, rest, left - 1) else none)
    ]
    let g := g.castAsPartOfResolution p id (callerCheckpoint := true)
    let g :=
      if g.pending == .none && g.proposedSpell.isNone &&
          (g.followMovedToZone? id (· == .stack)).isNone then
        g.change (.pendingMayCastFromExile none)
      else g
    return g.finishFraChoice
  | .mayCastUpToFromExile _ _, .decline =>
    return ((g.change (.pendingMayCastFromExile none))
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
      return g.change (.pending (.fraChoice p (.hydeRemoveCounter ids)))
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
  | .ultronMayPay _, .accept =>
    let cost := ManaCost.ofGeneric 2
    if !(g.player p).manaPool.canPay cost then
      throw s!"{(g.player p).name} cannot pay {2}; add mana first, or decline"
    let g ← g.payCost p cost
    return g.acceptMayThen
  | .ultronMayPay _, .decline =>
    return (g.logMsg s!"{(g.player p).name} doesn't pay {2}").declineMayThen
  | .ultronMayPay _, _ => throw "Pay {2} (accept), or decline"
  | .visionMode sourceId available, .mode m =>
    if !available.contains m then throw "That mode was already chosen this turn"
    return (g.answerChooseMode sourceId m
      (fun g => g.applyVisionMode p sourceId m)).finishFraChoice
  | .visionMode .., _ => throw "Choose a mode that hasn't been chosen this turn"
  | .moonstoneMayExile cardId, .accept =>
    match g.findObject? cardId with
    | some o =>
      if o.zone != .graveyard p then throw s!"{o.name} is no longer in your graveyard"
      let name := o.name
      let (g, cause) := g.allocDelayedCause (some p)
      let (g, newId) := g.move o.id .exile none (cause := some cause)
      return (g.createEffect (.playPermission newId { player := p } (turnEnds := 2))
        (cause := some cause)
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
        if o.isOnBattlefield && g.isCreature o then
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
    if !isPublicZone o.zone then throw s!"{o.name} is no longer in a public zone"
    let g := g.returnToHand o.id p
    return (g.gainLife p life).finishFraChoice
  | .mayTakeMilled _ life, .decline =>
    return (g.gainLife p life).finishFraChoice
  | .mayTakeMilled .., _ => throw "Put a milled card into your hand, or decline"
  | .mayDrawThenEachOpponentDraws n, .accept =>
    let before := g.loggedDraws p
    let g := g.draw p n
    let g :=
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep 49 p (n := before))
      else
        g.runPostStep 49 p (n := before)
    return g.finishFraChoice
  | .mayDrawThenEachOpponentDraws _, .decline =>
    return (g.logMsg s!"{(g.player p).name} doesn't draw").finishFraChoice
  | .mayDrawThenEachOpponentDraws _, _ => throw "Draw (accept), or decline"
  | .mayPutHeroFromHandOrDraw ids, .objects #[id] =>
    if !ids.contains id then throw "That card can't be put onto the battlefield"
    let some o := g.findObject? id | throw "no such object"
    if o.zone != .hand p || !g.isCreature o || !g.hasSubtype o .hero then
      throw s!"{o.name} is not a Hero creature card in your hand"
    let (g, _) := g.putOntoBattlefield id p
    let g :=
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep 20 p (cardId := some id))
      else
        g.runPostStep 20 p (cardId := some id)
    return g.finishFraChoice
  | .mayPutHeroFromHandOrDraw _, .decline =>
    return (g.draw p 1).finishFraChoice
  | .mayPutHeroFromHandOrDraw _, _ => throw "Put a Hero onto the battlefield, or decline to draw"
  | .oddOrEvenDestroy sourceId, .mode m =>
    if m > 1 then throw "Choose 0 for even or 1 for odd"
    return (g.destroyCreaturesByManaParity sourceId (m == 0)).finishFraChoice
  | .oddOrEvenDestroy _, _ => throw "Choose even (0) or odd (1)"
  | .visionQuestZones lib gy x, .accept =>
    return g.change (.pending (.fraChoice p (.visionQuestPick (lib ++ gy) x true)))
  | .visionQuestZones _ gy x, .decline =>
    if gy.isEmpty then
      return (g.logMsg s!"{(g.player p).name} finds no artifact creature card").finishFraChoice
    else
      return g.change (.pending (.fraChoice p (.visionQuestPick gy x false)))
  | .visionQuestZones .., _ => throw "Search your library as well (accept), or only your graveyard (decline)"
  | .visionQuestPick ids x shuffle, .objects #[id] =>
    if !ids.contains id then throw "That card can't be found"
    return (g.finishVisionQuest p (some id) x shuffle).finishFraChoice
  | .visionQuestPick _ x shuffle, .decline =>
    return (g.finishVisionQuest p none x shuffle).finishFraChoice
  | .visionQuestPick .., _ => throw "Choose an artifact creature, or decline to find nothing"
  | .kingpinMayPay2Life, .accept =>
    let g ← g.payLifeCost p 2
    return ((g.createEffect (.assignCombatDamageEqualToughnessUntilEot p))
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
    let g := g.record (GameEvent.sheHulkDealtDamage g.turnNumber p)
    let g :=
      g.withLegalKindTarget p .playerOrCreature #[target]
        (fun g tgt => g.dealDamageToTarget tgt amount (source := sourceId.bind g.damageSourceById?))
        sourceId none
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
    let lib := (g.player controller).library
    let count := min n lib.size
    let tops := (lib.extract (lib.size - count) lib.size).reverse
    let (g, cause?) : Game × Option EventCause :=
      if n == 0 || lib.isEmpty then (g, none)
      else
        match g.currentResolvingContext? with
        | some (src, ctrl) =>
          let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some controller)) (src.orElse (fun _ => some sourceId))
          (g, some c)
        | none => (g, none)
    let g := g.mill controller n (cause := cause?)
    let g :=
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement
          (.finishPostStep 51 p (ids := tops) (modes := #[controller.idx]) (cause := cause?))
      else
        g.runPostStep 51 p (ids := tops) (modes := #[controller.idx]) (cause := cause?)
    return g.finishFraChoice
  | .palantirMayDraw .., _ => throw "Have that player draw (accept), or decline"
  | .mayCastCards eligible withoutPaying exileInstead, .objects #[id] =>
    if !eligible.contains id then throw "That card can't be cast this way"
    let some o := g.findObject? id | throw "no such object"
    let face := g.baseCard o
    if face.isModal && !face.spellModes.any (g.spellModeIsChoosable p) && !face.allowsZeroTargets then
      throw s!"{face.name} has no mode with a legal target"
    if !face.isModal && (face.requiresTarget || face.isAura) &&
        (g.legalCastTargets p face).isEmpty && !face.allowsZeroTargets then
      throw s!"{face.name} has no legal target"
    let g := (gPre.change .saveProposalCheckpoint).change (.pending .none)
    return (g.castAsPartOfResolution p id (withoutManaCost := withoutPaying)
      (exileInstantSorceryInstead := exileInstead) (callerCheckpoint := true)).finishFraChoice
  | .mayCastCards _ _ _, .decline =>
    return (g.logMsg s!"{(g.player p).name} declines to cast a spell").finishFraChoice
  | .mayCastCards _ _ _, _ => throw "Choose a spell to cast, or decline"
  | .mayCastFromGraveyard eligible, .objects #[id] =>
    if !eligible.contains id then throw "That card can't be cast this way"
    let some o := g.findObject? id | throw "no such object"
    if o.zone != .graveyard o.owner then throw s!"{o.name} is no longer in the graveyard"
    if !(g.isArtifact o || g.isInstantOrSorcery o) then
      throw s!"{o.name} is not an artifact, instant, or sorcery"
    let face := g.baseCard o
    if face.isModal && !face.spellModes.any (g.spellModeIsChoosable p) && !face.allowsZeroTargets then
      throw s!"{face.name} has no mode with a legal target"
    if !face.isModal && (face.requiresTarget || face.isAura) &&
        (g.legalCastTargets p face).isEmpty && !face.allowsZeroTargets then
      throw s!"{face.name} has no legal target"
    let g := (gPre.change .saveProposalCheckpoint).change (.pending .none)
    return (g.castAsPartOfResolution p id (withoutManaCost := false)
      (exileInstantSorceryInstead := true) (callerCheckpoint := true)).finishFraChoice
  | .mayCastFromGraveyard _, .decline =>
    return (g.logMsg s!"{(g.player p).name} declines to cast a spell").finishFraChoice
  | .mayCastFromGraveyard _, _ => throw "Choose a card to cast, or decline"
  | .maySearchLibrary eligible count dest after kind, .accept =>
    if eligible.isEmpty then
      let g := g.record (GameEvent.searched g.turnNumber p p #[]
        (cause := some (g.resolvingOrRuleCause p)))
      let g :=
        (g.logMsg s!"{(g.player p).name} finds no {searchNoun kind}").shuffleSearch p after
      return g.finishFraChoice
    else
      return g.change (.pending (.fraChoice p (.searchLibrary eligible count dest after kind)))
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
    return (g.applyRiddlesPiles controller faceUp faceDown false (alreadyRevealed := true)).finishFraChoice
  | .riddlesChoosePile controller faceUp faceDown, .decline =>
    return (g.applyRiddlesPiles controller faceUp faceDown true (alreadyRevealed := true)).finishFraChoice
  | .riddlesChoosePile .., _ => throw "Choose the face-up pile (accept) or the face-down pile (decline)"
  | .palisadeCreatureType types, .mode idx =>
    let some sub := types[idx]? | throw "No such creature type"
    let g := g.logMsg s!"{(g.player p).name} chooses {sub}"
    return (g.returnCreaturesNotOfType sub).finishFraChoice
  | .palisadeCreatureType types, .name t =>
    let some sub := CardSubtype.ofOracle? t | throw "Choose an existing creature type"
    if !types.contains sub then throw "Choose an existing creature type"
    let g := g.logMsg s!"{(g.player p).name} chooses {sub}"
    return (g.returnCreaturesNotOfType sub).finishFraChoice
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
    let cause := g.stashedCause.orElse (fun _ => ids[0]?.bind g.lastMoveCauseOf?)
    let g := if g.stashedCause.isSome then g.change (.stashedCause none) else g
    return (g.finishChooseCards p chosen purpose (cause := cause)).finishFraChoice
  | .chooseCards ids _ purpose, .decline =>
    match purpose with
    | .toHand true =>
      if !ids.isEmpty then throw "Choose one card"
    | .amassArmy .. => throw "Choose an Army"
    | _ => pure ()
    let cause := g.stashedCause.orElse (fun _ => ids[0]?.bind g.lastMoveCauseOf?)
    let g := if g.stashedCause.isSome then g.change (.stashedCause none) else g
    return (g.finishChooseCards p #[] purpose (cause := cause)).finishFraChoice
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
    let g := g.logMsg s!"{(g.player p).name} chooses {g.targetLogName t} as the copy's new target"
    let rest := copies.extract 1 copies.size
    if rest.isEmpty then return g.finishFraChoice
    return g.change (.pending (.fraChoice p (.newTargetsForCopies rest)))
  | .newTargetsForCopies copies, .decline =>
    let rest := copies.extract 1 copies.size
    if rest.isEmpty then return g.finishFraChoice
    return g.change (.pending (.fraChoice p (.newTargetsForCopies rest)))
  | .newTargetsForCopies .., _ => throw "Choose a new target for the copy, or decline to keep it"
  | .chooseEnteringAttackTarget remaining chosen cause, ans =>
    let some item := remaining[0]?
      | return (g.commitEnteringAttackItems chosen cause).finishFraChoice
    let options := item.options
    let chosen? : Option AttackTarget :=
      match ans with
      | .mode idx => options[idx]?
      | .objects #[oid] =>
        options.find? fun
          | .planeswalker pid | .battle pid => pid == oid
          | .player _ => false
      | _ => none
    let some tgt := chosen?
      | throw "Choose a player, planeswalker, or battle to attack (CR 508.4)"
    let who :=
      match tgt with
      | .player pid => (g.player pid).name
      | .planeswalker oid | .battle oid =>
        ((g.findObject? oid).map g.name).getD "that permanent"
    let nm := g.enteringAttackItemName item
    let g := g.logMsg s!"{(g.player p).name} chooses {who} for {nm} to attack"
    let (restAfter, chosen') :=
      advanceFixedEnteringAttackItems (remaining.extract 1 remaining.size) (chosen.push (item, some tgt))
    match restAfter[0]? with
    | some nextItem =>
      let nextCtrl := nextItem.controller
      let nextNm := g.enteringAttackItemName nextItem
      return (g.change (.pending (.fraChoice nextCtrl (.chooseEnteringAttackTarget restAfter chosen' cause)))).logMsg
        s!"{(g.player nextCtrl).name} chooses what {nextNm} enters attacking"
    | none =>
      let g := g.commitEnteringAttackItems chosen' cause
      return g.finishFraChoice
  | .mayBeginOnBattlefield ids, .accept =>
    let rest := ids.extract 1 ids.size
    match ids[0]? with
    | some id =>
      match g.findObject? id with
      | some o =>
        if o.zone != .hand o.owner then
          return (g.continueOpeningBegin rest).finishFraChoice
        else
          let name := o.name
          let (g, _) := g.move id .battlefield (some o.owner)
            (cause := some (.gameRule .staticAbility))
          let g := g.logMsg s!"{name} begins the game on the battlefield"
          let g :=
            if let .chooseReplacement .. := g.pending then
              g.chainPendingReplacement (.finishBeginOnBattlefield id rest)
            else
              g.finishBeginOnBattlefield id rest
          return g.finishFraChoice
      | none => return (g.continueOpeningBegin rest).finishFraChoice
    | none => return (g.continueOpeningBegin rest).finishFraChoice
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
  | .maySacrificeThese _ _ => .decline
  | .mayDiscardThese _ _ => .decline
  | .mayPaySymbolsThen symbols .. =>
    if (g.player p).manaPool.canPay { symbols := symbols } then .accept else .decline
  | .attachAnyEquipment _ eligible => .choosePermanents eligible
  | .sacrificeLeastPower ids => .choosePermanents (ids.extract 0 1)
  | .addManaColors .. => .chooseMode 0
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
      let yours := ids.filter (fun id => (g.findObject? id).any (g.controlledBy · p))
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
  | .mayCastCards eligible withoutPaying _ =>
    let hasTargets (o : GameObject) : Bool :=
      let face := g.baseCard o
      if face.isModal then face.spellModes.any (g.spellModeIsChoosable p) || face.allowsZeroTargets
      else if face.requiresTarget || face.isAura then
        !(g.legalCastTargets p face).isEmpty || face.allowsZeroTargets
      else true
    if withoutPaying then
      match eligible.find? (fun id => (g.findObject? id).any hasTargets) with
      | some id => .cast id
      | none => .decline
    else
      let available := g.availableMana p
      match eligible.find? (fun id =>
        (g.findObject? id).any (fun o =>
          hasTargets o && available.canPay (g.playManaCost o (g.baseCard o)))) with
      | some id => .cast id
      | none => .decline
  | .mayCastFromGraveyard eligible =>
    let available := g.availableMana p
    match eligible.find? (fun id =>
      (g.findObject? id).any (fun o =>
        let face := g.baseCard o
        let hasTargets :=
          if face.isModal then face.spellModes.any (g.spellModeIsChoosable p) || face.allowsZeroTargets
          else if face.requiresTarget || face.isAura then
            !(g.legalCastTargets p face).isEmpty || face.allowsZeroTargets
          else true
        hasTargets && available.canPay (g.playManaCost o face))) with
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
  | .zemoBoastExile _ sourceId =>
    let col :=
      match g.findObject? sourceId with
      | some src => TextChange.applyColor (g.evalLayer3 src) .black
      | none => .black
    .choosePermanents ((g.player p).graveyard.filter (fun id =>
      (g.findObject? id).any (fun card => (g.colors card).contains col)))
  | .chooseEnteringAttackTarget .. => .chooseMode 0
  | .mayBeginOnBattlefield _ => .decline

end Game
end Mtg.Engine
