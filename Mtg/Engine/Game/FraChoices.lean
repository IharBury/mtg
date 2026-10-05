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
deriving Repr, BEq

/-- Clear the choice and let the game continue. -/
def finishFraChoice (g : Game) : Game :=
  let g := { g with pending := .none }.promptTriggerTargetsIfNeeded
  if g.pending == .none then g.receivePriority g.activePlayer else g

/-- `p` discards `id` from their hand (CR 701.9). -/
def discardFromHand (g : Game) (p : PlayerId) (id : ObjectId) (chooser : Option PlayerId := none) :
    Game :=
  let card := g.object! id
  let g :=
    match chooser with
    | some c => g.logMsg s!"{(g.player c).name} chooses {card.name}. {(g.player p).name} discards it"
    | none => g.logMsg s!"{(g.player p).name} discards {card.name}"
  let (g, _) := g.move id (.graveyard card.owner) none
  g.modifyPlayer p (fun pl => { pl with cardsDiscardedThisTurn := pl.cardsDiscardedThisTurn + 1 })

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

def answerFraChoice (g : Game) (p : PlayerId) (answer : FraAnswer) : Except String Game := do
  let .fraChoice q choice := g.pending | throw "Nothing to choose now"
  if p != q then
    throw s!"Only {(g.player q).name} may choose"
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
  | .triggerModes objId _ chosen =>
    match g.findObject? objId with
    | none => .decline
    | some obj =>
      let modes := g.triggerModesOf obj
      match (List.range modes.size).find? (fun i =>
          !chosen.contains i && modes[i]?.any (g.triggerModeChoosable p obj)) with
      | some i => .chooseMode i
      | none => .decline

end Game
end Mtg.Engine
