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
def drawOneCard (g : Game) (p : PlayerId) (cause : Option EventCause := none) : Game :=
  let pl := g.player p
  if pl.library.isEmpty then
    let g := g.changePlayer p (.drewFromEmpty true)
    g.logMsg s!"{pl.name} tries to draw from an empty library"
  else
    let top := pl.library.back!
    let cardName := (g.object! top).name
    let nth := GameEvent.draws g.events g.turnNumber p + 1
    let firstOfTheirDrawStep :=
      g.step == .draw && g.activePlayer == p &&
        !GameEvent.drewFirstOfDrawStep g.events g.turnNumber p
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
    let (g, newId) := g.move top (.hand p) none (verb := verb) (actor := some p) (cause := cause)
    let pl := g.player p
    let g := g.logMsg s!"{pl.name} draws {cardName}"
    if !pl.keptOpeningHand then g
    else
      let happened := GameEvent.drew g.turnNumber p newId nth firstOfTheirDrawStep
      Id.run do
        let mut g := g
        for o in g.permanentsOf p do
          if happened.matchesTrigger p o.id .youDraw then
            g := g.change (.enqueueWaitingTriggers
              (o.waitingTriggersFor p .youDraw))
          if happened.matchesTrigger p o.id .youDrawSecondCard then
            g := g.change (.enqueueWaitingTriggers
              (o.waitingTriggersFor p .youDrawSecondCard))
        if happened.matchesTrigger p ⟨0⟩ .anyPlayerDrawsSecond then
          for q in g.livingPlayers do
            for o in g.permanentsOf q.id do
              if happened.matchesTrigger q.id o.id .anyPlayerDrawsSecond then
                g := g.change (.enqueueWaitingTriggers
                  (o.waitingTriggersFor q.id .anyPlayerDrawsSecond))
        for opp in g.livingOpponents p do
          for o in g.permanentsOf opp.id do
            if happened.matchesTrigger opp.id o.id .opponentDrawsExceptFirstDrawStep then
              g := g.change (.enqueueWaitingTriggers
                (o.waitingTriggersFor opp.id .opponentDrawsExceptFirstDrawStep))
            if happened.matchesTrigger opp.id o.id .opponentDrawsSecondCard then
              g := g.change (.enqueueWaitingTriggers
                (o.waitingTriggersFor opp.id .opponentDrawsSecondCard))
        return g

/-- How many cards replace one draw (`2^n` Bard effects, except the first
card of your draw step). The replacement matches the draw that would happen. -/
def drawMultiplier (g : Game) (p : PlayerId) : Nat :=
  let firstOfYourDrawStep :=
    g.step == .draw && g.activePlayer == p &&
      !GameEvent.drewFirstOfDrawStep g.events g.turnNumber p
  let proposed :=
    GameEvent.drew g.turnNumber p ⟨0⟩ (GameEvent.draws g.events g.turnNumber p + 1)
      firstOfYourDrawStep
  if !proposed.watches .wouldDraw || firstOfYourDrawStep then 1
  else
    let n := (g.permanentsOf p).filter (fun o =>
      o.printed.drawTwoExceptFirstDrawStep) |>.size
    Nat.pow 2 n

def draw (g : Game) (p : PlayerId) (n : Nat := 1)
    (cause : Option EventCause := none) : Game :=
  Id.run do
    let mut g := g
    for _ in [0:n] do
      let copies := g.drawMultiplier p
      for _ in [0:copies] do
        let pl := g.player p
        if pl.drewFromEmpty then
          return g
        g := g.drawOneCard p (cause := cause)
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

/-- Shuffle `p`'s library (CR 103.3 / 701.19). A library of two or more cards
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
def moveIdsInOrder (g : Game) (ids : Array ObjectId) (dest : Zone) : Game :=
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
        let (g', _) := g.move id dest none (libraryPosition := some pos)
        g := g'
      return g
  | _ =>
    ids.foldl (fun acc id => (acc.move id dest none).1) g

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
    (log : String) : Game :=
  if ids.size ≤ 1 || g.pending != .none then
    g.moveIdsInOrder ids dest |>.logMsg log
  else
    (g.change (.pending (.resolveRandom (.orderInto ids dest)))).logMsg log

/-- Put `ids` on the bottom of `p`'s library in a random order. The rest of
the library stays above them, in its current order. -/
def putRestOnBottomRandom (g : Game) (p : PlayerId) (ids : Array ObjectId) : Game :=
  if ids.isEmpty then g
  else
    g.requestOrderInto ids (.library p)
      s!"{(g.player p).name} puts the rest on the bottom of their library in a random order"

end Game
end Mtg.Engine
