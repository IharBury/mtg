import Mtg.Engine.Game.Leaving

/-!
# Draws, shuffles, and library order (CR 121)

Drawing cards with draw replacements, recruit (MSH), shuffle requests
answered by outside randomness, and ordered placement of cards into a
zone (CR 701.20b).
-/

namespace Mtg.Engine
namespace Game

/-- Draw one card with no replacement effects (CR 121). -/
def drawOneCard (g : Game) (p : PlayerId)
    (firstOfTheirDrawStep? : Option Bool := none)
    (cause : Option EventCause := none) : Game :=
  let pl := g.player p
  if pl.library.isEmpty then
    let g := g.changePlayer p (.drewFromEmpty true)
    g.logMsg s!"{pl.name} tries to draw from an empty library"
  else
    let top := pl.library.back!
    let cardName := (g.object! top).name
    let nth := GameEvent.draws g.events g.turnNumber p + 1
    let firstOfTheirDrawStep :=
      firstOfTheirDrawStep?.getD
        (g.step == .draw && g.activePlayer == p &&
          !GameEvent.drewFirstOfDrawStep g.events g.turnNumber p)
    -- Opening hands are drawn before anyone keeps (CR 103.4). They are not
    -- “cards drawn this turn” once that counter is cleared for the first turn.
    let verb : Option ZoneVerb :=
      if pl.keptOpeningHand then some (.draw nth firstOfTheirDrawStep) else some .put
    let cause := cause.orElse (fun _ =>
      if !pl.keptOpeningHand then
        some (.gameRule (if pl.mulligansTaken > 0 then .mulligan else .openingHandDraw))
      else if firstOfTheirDrawStep then
        some (.turnBased .drawStepDraw)
      else none)
    let (g, _) := g.move top (.hand p) none (verb := verb) (actor := some p) (cause := cause)
    let pl := g.player p
    g.logMsg s!"{pl.name} draws {cardName}"

mutual
/-- Run the CR 616.1 replacement loop for a single card draw by `p`
(CR 121.2 / 614.5 / 614.6 / 616.1; ruling 193). Each selected draw replacement
replaces the single draw with `factor` sub-draws carrying `applied.push chosen.id`
and `cause := .replaced chosen.id origCause`. -/
partial def drawOneWithReplacements (g : Game) (p : PlayerId)
    (applied : Array ReplacementId := #[])
    (firstOfYourDrawStep? : Option Bool := none)
    (cause : Option EventCause := none) : Game :=
  let pl := g.player p
  if pl.drewFromEmpty then g
  else
    let firstOfYourDrawStep :=
      firstOfYourDrawStep?.getD
        (g.step == .draw && g.activePlayer == p &&
          !GameEvent.drewFirstOfDrawStep g.events g.turnNumber p)
    let cause := cause.orElse (fun _ =>
      if !pl.keptOpeningHand then
        some (.gameRule (if pl.mulligansTaken > 0 then .mulligan else .openingHandDraw))
      else if firstOfYourDrawStep then
        some (.turnBased .drawStepDraw)
      else none)
    let proposed :=
      GameEvent.drew g.turnNumber p ⟨0⟩ (GameEvent.draws g.events g.turnNumber p + 1)
        firstOfYourDrawStep
    let specs : Array (ReplacementSpec × Nat) :=
      if !pl.keptOpeningHand || !proposed.watches .wouldDraw then #[]
      else Id.run do
        let mut acc : Array (ReplacementSpec × Nat) := #[]
        if !firstOfYourDrawStep then
          for o in g.permanentsOf p do
            if o.printed.drawTwoExceptFirstDrawStep then
              acc := acc.push (
                { id := { kind := .drawTwoExceptFirstDrawStep, object := some o.id }
                  source := some o.id
                  controller := some p
                  affectedPlayer := p
                  kind := .replaceDraw p 2 true }, 2)
        for (_, eff) in g.activeEffects do
          match eff with
          | .replacement spec _ =>
            match spec.kind with
            | .replaceDraw who factor exceptFirst =>
              if who == p && (!exceptFirst || !firstOfYourDrawStep) then
                acc := acc.push (spec, factor)
            | _ => pure ()
          | _ => pure ()
        return acc
    let candidates := specs.map (fun (s, _) => (ReplacementOrPrevention.replacement s).toCandidate)
    match g.selectNextReplacementStep candidates applied with
    | .none =>
      g.drawOneCard p (firstOfTheirDrawStep? := some firstOfYourDrawStep) (cause := cause)
    | .needChoice chooser choices _ =>
      g.promptChooseReplacement chooser choices
        (.drawOne p applied firstOfYourDrawStep cause)
    | .chosen chosen _ =>
      let g := g.consumeReplacementOrder #[chosen.id]
      match specs.find? (fun (s, _) => s.id == chosen.id) with
      | none =>
        g.drawOneCard p (firstOfTheirDrawStep? := some firstOfYourDrawStep) (cause := cause)
      | some (_, factor) =>
        let applied' := applied.push chosen.id
        let cause' := g.wrapReplacedCause chosen.id cause (some p)
        g.drawSubDraws p factor applied' cause'

/-- Execute `remaining` replacement-expanded sub-draws for `p` carrying `applied`
and `cause`, chaining `.drawSubDraws` if any sub-draw pauses on
`Pending.chooseReplacement`. -/
partial def drawSubDraws (g : Game) (p : PlayerId) (remaining : Nat)
    (applied : Array ReplacementId) (cause : Option EventCause := none) : Game := Id.run do
  let mut g := g
  for i in [0:remaining] do
    if (g.player p).drewFromEmpty then
      return g
    g := g.drawOneWithReplacements p (applied := applied) (cause := cause)
    if g.pending != .none then
      let rem := remaining - (i + 1)
      if rem > 0 then
        g := g.chainPendingReplacement (.drawSubDraws p rem applied cause)
      return g
  return g
end

def draw (g : Game) (p : PlayerId) (n : Nat := 1)
    (cause : Option EventCause := none) : Game :=
  let (g0, cause?) : Game × Option EventCause :=
    match cause with
    | some c => (g, some c)
    | none =>
      let pl := g.player p
      let firstOfTheirDrawStep :=
        g.step == .draw && g.activePlayer == p &&
          !GameEvent.drewFirstOfDrawStep g.events g.turnNumber p
      if n == 0 || pl.drewFromEmpty || pl.library.isEmpty || !pl.keptOpeningHand ||
          firstOfTheirDrawStep then
        (g, none)
      else
        match g.currentBatch with
        | some (_, some (.oneShotEffect (some bid) bsrc bctrl)) =>
          (g, some (.oneShotEffect (some bid) bsrc (bctrl.orElse (fun _ => some p))))
        | _ =>
          match g.currentResolvingContext? with
          | some (src, ctrl) =>
            let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some p)) src
            (g, some c)
          | none => (g, none)
  Id.run do
    let mut g := g0
    for i in [0:n] do
      let pl := g.player p
      if pl.drewFromEmpty then
        return g
      g := g.drawOneWithReplacements p (cause := cause?)
      if g.pending != .none then
        let rem := n - (i + 1)
        if rem > 0 then
          g := g.chainPendingReplacement (.draw p rem false cause?)
        return g
    return g

/-- Draw, then discard; if the discarded card is not a land, create a
1/1 white Human Soldier (the Recruit keyword action). -/
def beginRecruit (g : Game) (p : PlayerId) : Game :=
  let g := g.draw p 1
  if (g.player p).hand.isEmpty then
    g.logMsg s!"{(g.player p).name} has no card to discard"
  else
    g.change (.pending (.recruitDiscard p)) |>.logMsg
      s!"{(g.player p).name} discards a card. If it is not a land, they create a Human Soldier token"

/-- Return a spell on the stack to its owner's hand. -/
def returnStackSpell (g : Game) (spellId : ObjectId) : Game :=
  match g.findObject? spellId with
  | none => g.logMsg "The spell is no longer on the stack"
  | some o =>
    if o.zone != .stack then
      g.logMsg s!"{o.name} is no longer on the stack"
    else
      let name := o.name
      let owner := o.owner
      let (g, _) := g.move spellId (.hand owner) none
      g.logMsg s!"{name} is returned to {(g.player owner).name}'s hand"

/-- True when a `--norandom` result is still required. -/
def pendingRandom? (g : Game) : Option RandomRequest :=
  match g.pending with
  | .resolveRandom req => some req
  | _ => none

/-- Shuffle `p`'s library (CR 103.3 / 701.20). A library of two or more cards
becomes `Pending.resolveRandom` unless a choice is already pending. -/
def shuffleLibrary (g : Game) (p : PlayerId) : Game :=
  let pl := g.player p
  if pl.library.size ≤ 1 || g.pending != .none then
    g.logMsg s!"{pl.name} shuffles their library"
  else
    g.change (.pending (.resolveRandom (.shuffleLibrary p)))
      |>.logMsg s!"{pl.name} shuffles their library"

/-- Record `after` and shuffle. If `--norandom` pauses, `after` stays on the
game until the host supplies an order. -/
def requestShuffle (g : Game) (p : PlayerId) (after : AfterRandom := .none) : Game :=
  (g.change (.afterRandom after)).shuffleLibrary p

/-- Move `ids` into `dest` in this order. For a library, first listed becomes
the new bottom of that group. -/
def moveIdsInOrder (g : Game) (ids : Array ObjectId) (dest : Zone)
    (cause : Option EventCause := none) : Game :=
  let defaultCause :=
    cause.orElse (fun _ =>
      if ids.isEmpty then none
      else g.currentResolvingContext?.map fun (src, ctrl) => .oneShotEffect none src ctrl)
  g.withBatch defaultCause fun g =>
  match dest with
  | .library p =>
    Id.run do
      let mut g := g
      for i in [0:ids.size] do
        let id := ids[i]!
        let libSize := ((g.player p).library.filter (· != id)).size
        let pos : LibraryPosition :=
          if i == 0 then .bottom
          else .fromTop (libSize - Nat.min i libSize)
        let (g', _) := g.move id dest none (libraryPosition := some pos) (cause := cause)
        g := g'
      return g
  | _ =>
    ids.foldl (fun acc id => (acc.move id dest none (cause := cause)).1) g

/-- Put `ids` on top of `p`'s library, last listed on top. Cards that are no
longer in that library are skipped. -/
def putIdsOnTop (g : Game) (p : PlayerId) (ids : Array ObjectId) : Game :=
  Id.run do
    let mut g := g
    for id in ids do
      match g.findObject? id with
      | some o =>
        if o.zone == .library p then
          let name := o.name
          g := g.changePlayer p (.library (((g.player p).library.filter (· != id)).push id))
          g := g.logMsg s!"{(g.player p).name} puts {name} on top of their library"
        else pure ()
      | none => pure ()
    return g

/-- Put `ids` into `dest` in a random order. With two or more cards and no
other pending choice, becomes `Pending.resolveRandom`. -/
def requestOrderInto (g : Game) (ids : Array ObjectId) (dest : Zone)
    (log : String) (cause : Option EventCause := none) : Game :=
  let (g, cause) : Game × Option EventCause :=
    match cause with
    | some c => (g, some c)
    | none =>
      if ids.isEmpty then (g, none)
      else
        match g.currentResolvingContext? with
        | some (src, ctrl) =>
          let (g, c) := g.allocDelayedCause ctrl src
          (g, some c)
        | none => (g, none)
  if ids.size ≤ 1 || g.pending != .none then
    g.moveIdsInOrder ids dest (cause := cause) |>.logMsg log
  else
    (g.change (.pending (.resolveRandom (.orderInto ids dest cause)))).logMsg log

/-- The `EventCause` recorded on the most recent zone-change event that moved
an object into `id`. Used to thread a one-shot instruction's `EffectId` across
multi-step library reveal / exile / bottom-of-library effects. -/
def lastMoveCauseOf? (g : Game) (id : ObjectId) : Option EventCause :=
  g.events.findSomeRev? fun e =>
    match e.change with
    | .rules (.zone (.moved _ after ..)) =>
      if after.id == some id then some e.cause else none
    | _ => none

/-- Put `ids` on the bottom of `p`'s library in a random order. The rest of
the library stays above them, in its current order. -/
def putRestOnBottomRandom (g : Game) (p : PlayerId) (ids : Array ObjectId)
    (cause : Option EventCause := none) : Game :=
  if ids.isEmpty then g
  else
    g.requestOrderInto ids (.library p)
      s!"{(g.player p).name} puts the rest on the bottom of their library in a random order"
      (cause := cause)

end Game
end Mtg.Engine
