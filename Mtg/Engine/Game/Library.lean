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
def drawOneCard (g : Game) (p : PlayerId) : Game :=
  let pl := g.player p
  if pl.library.isEmpty then
    let g := g.setPlayer { pl with drewFromEmpty := true }
    g.logMsg s!"{pl.name} tries to draw from an empty library"
  else
    let top := pl.library.back!
    let cardName := (g.object! top).name
    let rest := pl.library.pop
    let g := g.setPlayer { pl with library := rest }
    let (g, _) := g.move top (.hand p) none
    let pl := g.player p
    let drawn := pl.cardsDrawnThisTurn + 1
    let drawStepDrawn :=
      if g.step == .draw && g.activePlayer == p then
        pl.cardsDrawnThisDrawStep + 1
      else pl.cardsDrawnThisDrawStep
    let g := g.setPlayer { pl with
      cardsDrawnThisTurn := drawn
      cardsDrawnThisDrawStep := drawStepDrawn }
    let g := g.logMsg s!"{pl.name} draws {cardName}"
    let firstOfTheirDrawStep :=
      g.step == .draw && g.activePlayer == p && drawStepDrawn == 1
    Id.run do
      let mut g := g
      for o in g.permanentsOf p do
        g := { g with waitingTriggers :=
          g.waitingTriggers ++ o.waitingTriggersFor p .youDraw }
        if drawn == 2 then
          g := { g with waitingTriggers :=
            g.waitingTriggers ++ o.waitingTriggersFor p .youDrawSecondCard }
      for opp in g.livingOpponents p do
        for o in g.permanentsOf opp.id do
          if !firstOfTheirDrawStep then
            g := { g with waitingTriggers :=
              g.waitingTriggers ++
                o.waitingTriggersFor opp.id .opponentDrawsExceptFirstDrawStep }
          if drawn == 2 then
            g := { g with waitingTriggers :=
              g.waitingTriggers ++
                o.waitingTriggersFor opp.id .opponentDrawsSecondCard }
      return g

/-- How many cards replace one draw (`2^n` Bard effects, except the first
card of your draw step). -/
def drawMultiplier (g : Game) (p : PlayerId) : Nat :=
  let pl := g.player p
  let firstOfYourDrawStep :=
    g.step == .draw && g.activePlayer == p && pl.cardsDrawnThisDrawStep == 0
  if firstOfYourDrawStep then 1
  else
    let n := (g.permanentsOf p).filter (fun o =>
      o.printed.drawTwoExceptFirstDrawStep) |>.size
    Nat.pow 2 n

def draw (g : Game) (p : PlayerId) (n : Nat := 1) : Game :=
  Id.run do
    let mut g := g
    for _ in [0:n] do
      let copies := g.drawMultiplier p
      for _ in [0:copies] do
        let pl := g.player p
        if pl.drewFromEmpty then
          return g
        g := g.drawOneCard p
    return g

/-- Draw, then discard; if the discarded card is not a land, create a
1/1 white Human Soldier (the Recruit keyword action). -/
def beginRecruit (g : Game) (p : PlayerId) : Game :=
  let g := g.draw p 1
  if (g.player p).hand.isEmpty then
    g.logMsg s!"{(g.player p).name} has no card to discard"
  else
    { g with pending := .recruitDiscard p }.logMsg
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

/-- Shuffle `p`'s library (CR 103.3 / 701.19). With `norandom`, a library
of two or more cards becomes `Pending.resolveRandom` instead of using `rng`. -/
def shuffleLibrary (g : Game) (p : PlayerId) : Game :=
  let pl := g.player p
  if g.norandom then
    if pl.library.size ≤ 1 then
      g.logMsg s!"{pl.name} shuffles their library"
    else
      { g with pending := .resolveRandom (.shuffleLibrary p) }
        |>.logMsg s!"{pl.name} shuffles their library"
  else
    let (rng, lib) := g.rng.shuffle pl.library
    { g with rng := rng } |>.setPlayer { pl with library := lib }
     |>.logMsg s!"{pl.name} shuffles their library"

/-- Record `after` and shuffle. If `--norandom` pauses, `after` stays on the
game until the host supplies an order. -/
def requestShuffle (g : Game) (p : PlayerId) (after : AfterRandom := .none) : Game :=
  { g with afterRandom := after }.shuffleLibrary p

/-- Move `ids` into `dest` in this order. For a library, first listed becomes
the new bottom of that group. -/
def moveIdsInOrder (g : Game) (ids : Array ObjectId) (dest : Zone) : Game :=
  match dest with
  | .library owner =>
    Id.run do
      let mut g := g
      let mut newBottom : Array ObjectId := #[]
      for id in ids do
        let (g', newId) := g.move id dest none
        g := g'
        newBottom := newBottom.push newId
      let pl := g.player owner
      let without := newBottom.foldl (fun lib id => lib.filter (· != id)) pl.library
      g.setPlayer { pl with library := newBottom ++ without }
  | _ =>
    ids.foldl (fun acc id => (acc.move id dest none).1) g

/-- Put `ids` into `dest` in a random order. With `norandom` and two or more
cards, becomes `Pending.resolveRandom`. -/
def requestOrderInto (g : Game) (ids : Array ObjectId) (dest : Zone)
    (log : String) : Game :=
  if ids.size ≤ 1 then
    g.moveIdsInOrder ids dest |>.logMsg log
  else if g.norandom then
    { g with pending := .resolveRandom (.orderInto ids dest) }.logMsg log
  else
    let (rng, ordered) := g.rng.shuffle ids
    { g with rng := rng }.moveIdsInOrder ordered dest |>.logMsg log

end Game
end Mtg.Engine
