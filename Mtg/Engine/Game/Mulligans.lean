import Mtg.Engine.Game.PriorityActions

/-!
# Opening hands and mulligans (CR 103.4–5)

The London mulligan including the free first mulligan in multiplayer and
Brawl (CR 103.5c), opening-hand actions, mulligan rounds, and bottoming
cards.
-/

namespace Mtg.Engine
namespace Game

/-- True while players are still keeping or taking mulligans (CR 103.5). -/
def openingHandsPending (g : Game) : Bool :=
  match g.pending with
  | .declareMulligan _ => true
  | .putOnBottom _ _ =>
    !g.mulliganToBottom.isEmpty || !g.mulliganToDeclare.isEmpty
  | _ => false

/-- Players who have not yet kept an opening hand, in turn order from the
starting player (CR 103.5). -/
def playersStillDecidingMulligan (g : Game) : Array PlayerId :=
  g.playersInOrderFrom g.startingPlayer (fun pl => !pl.lost && !pl.keptOpeningHand)

def promptMulligan (g : Game) (p : PlayerId) : Game :=
  { g with pending := .declareMulligan p }
    |>.logMsg s!"{g.player p |>.name} may keep or take a mulligan (CR 103.5)"

/-- CR 103.5c / 903.12g: the first mulligan does not count in a multiplayer
game or in any Brawl game. -/
def freeFirstMulligan (g : Game) : Bool :=
  g.isMultiplayer || g.brawl

/-- Mulligans that count toward bottoming and the zero-card limit
(CR 103.5, 103.5c). -/
def countedMulligans (g : Game) (p : PlayerId) : Nat :=
  let n := (g.player p).mulligansTaken
  if g.freeFirstMulligan then n - 1 else n

def promptBottom (g : Game) (p : PlayerId) : Game :=
  let n := g.countedMulligans p
  let cards := if n == 1 then "1 card" else s!"{n} cards"
  { g with pending := .putOnBottom p n }
    |>.logMsg s!"{g.player p |>.name} puts {cards} on the bottom of their library (CR 103.5)"

/-- Cards that may begin the game on the battlefield from an opening hand
(Quicksilver; MSH 84). -/
def beginsOnBattlefieldFromOpeningHand (o : GameObject) : Bool :=
  o.staticAbilities.any (fun
    | .mayBeginOnBattlefield => true
    | _ => false)

/-- After mulligans, the starting player takes opening-hand actions first,
then each other player in turn order (MSH 84). -/
def applyOpeningHandActions (g : Game) : Game :=
  Id.run do
    let mut g := g
    let order := g.playersInOrderFrom g.startingPlayer (fun pl => !pl.lost)
    for pid in order do
      let ids := (g.player pid).hand
      for id in ids do
        match g.findObject? id with
        | some o =>
          if beginsOnBattlefieldFromOpeningHand o then
            let name := o.name
            let (g', _) := g.move o.id .battlefield (some pid)
            g := g'
            g := g.logMsg s!"{name} begins the game on the battlefield"
        | none => pure ()
    return g

/-- After every remaining player has kept, opening-hand actions resolve,
then the starting player takes their first turn (CR 103.8 / MSH 84). -/
def finishOpeningHands (g : Game) : Game :=
  let g := { g with
    pending := .none
    mulliganToDeclare := #[]
    willMulligan := #[]
    mulliganToBottom := #[] }
  let g := g.applyOpeningHandActions
  let g := g.logMsg s!"{g.player g.startingPlayer |>.name} takes the first turn"
  g.beginTurn

/-- Start (or restart) a CR 103.5 round: eligible players declare in turn
order. When nobody remains, the game begins. -/
def beginMulliganRound (g : Game) : Game :=
  if g.over then g
  else
    let remaining := g.playersStillDecidingMulligan
    if remaining.isEmpty then
      g.finishOpeningHands
    else
      promptMulligan
        { g with
          mulliganToDeclare := remaining
          willMulligan := #[]
          mulliganToBottom := #[] }
        remaining[0]!

/-- Shuffle the cards in `p`'s hand back into their library (CR 103.5). -/
def returnHandToLibrary (g : Game) (p : PlayerId) : Game :=
  Id.run do
    let mut g := g
    let ids := (g.player p).hand
    for id in ids do
      let (g', _) := g.move id (.library p)
      g := g'
    return g

/-- A player may mulligan until that mulligan would leave a zero-card opening
hand, after which they may not take further mulligans (CR 103.5). The first
mulligan in multiplayer or Brawl does not count toward that limit (CR 103.5c). -/
def canTakeMulligan (g : Game) (p : PlayerId) : Bool :=
  let pl := g.player p
  !g.over && !pl.keptOpeningHand && g.countedMulligans p < pl.startingHandSize

/-- Perform one already-declared mulligan: shuffle, then draw a new starting
hand (CR 103.5). Bottoming is a later choice. -/
def executeOneMulligan (g : Game) (p : PlayerId) : Game :=
  let n := (g.player p).mulligansTaken + 1
  let size := (g.player p).startingHandSize
  let g := g.modifyPlayer p (fun pl => { pl with mulligansTaken := n })
  let g := g.logMsg s!"{g.player p |>.name} takes a mulligan ({n})"
  let g := g.returnHandToLibrary p
  g.requestShuffle p (.draw p size) |>.continueIfShuffled

/-- Players whose first mulligan is free put no cards on the bottom
(CR 103.5c). -/
def skipFreeMulliganBottoms (g : Game) : Game :=
  Id.run do
    let mut g := g
    let mut need : Array PlayerId := #[]
    for p in g.mulliganToBottom do
      if g.countedMulligans p == 0 then
        g := g.logMsg
          s!"{g.player p |>.name} puts no cards on the bottom of their library (CR 103.5c)"
      else
        need := need.push p
    return { g with mulliganToBottom := need }

/-- Take remaining declared mulligans, pausing if `--norandom` needs a
library order. `mulliganToBottom` is the original simultaneous group. -/
partial def executeMulliganQueue (g : Game) (rest : Array PlayerId) : Game :=
  match rest[0]? with
  | none =>
    let g := g.skipFreeMulliganBottoms
    if g.mulliganToBottom.isEmpty then
      g.beginMulliganRound
    else
      promptBottom g g.mulliganToBottom[0]!
  | some p =>
    let more := rest.extract 1 rest.size
    let g := g.executeOneMulligan p
    match g.pendingRandom? with
    | some _ =>
      { g with afterRandom := .mulliganQueue p more }
    | none =>
      executeMulliganQueue g more

/-- After every remaining player has declared, those who chose to mulligan
do so at the same time (CR 103.5). -/
def resolveDeclaredMulligans (g : Game) : Game :=
  if g.willMulligan.isEmpty then
    g.beginMulliganRound
  else
    let order := g.playersStillDecidingMulligan.filter (fun p => g.willMulligan.contains p)
    let g := g.logMsg
      "Players who chose to mulligan do so at the same time (CR 103.5)"
    if order.isEmpty then
      g.beginMulliganRound
    else
      let g := { g with willMulligan := #[], mulliganToBottom := order }
      executeMulliganQueue g order

/-- Remove `who` from a sequential CR 103.5 queue, then finish or prompt the
next player. -/
def advancePlayerQueue (g : Game) (who : PlayerId) (queue : Array PlayerId)
    (store : Game → Array PlayerId → Game) (whenEmpty : Game → Game)
    (prompt : Game → PlayerId → Game) : Game :=
  if g.over then g
  else
    let rest := queue.filter (fun q => q != who)
    let g := store g rest
    if rest.isEmpty then whenEmpty g else prompt g rest[0]!

/-- After `who` has declared keep or mulligan, the next declarer in this round
acts. When the round's declarations are complete, pending mulligans are taken
together. -/
def afterDeclaration (g : Game) (who : PlayerId) : Game :=
  g.advancePlayerQueue who g.mulliganToDeclare
    (fun g rest => { g with mulliganToDeclare := rest })
    (·.resolveDeclaredMulligans) (·.promptMulligan)

/-- After `who` has put cards on the bottom, the next such player acts, or a
new declaration round begins. -/
def afterBottom (g : Game) (who : PlayerId) : Game :=
  g.advancePlayerQueue who g.mulliganToBottom
    (fun g rest => { g with mulliganToBottom := rest })
    (·.beginMulliganRound) (·.promptBottom)

end Game
end Mtg.Engine
