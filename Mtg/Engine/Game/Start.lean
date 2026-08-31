import Mtg.Engine.Game.Actions

/-!
# Starting a game (CR 103)

Materializing each seat's deck and `Start.start`, which shuffles,
draws opening hands, and begins the mulligan loop.
-/

namespace Mtg.Engine

namespace Start

def materializeSeat (g : Game) (seatIdx : Nat) (seat : Seat) : Except String Game := do
  if seat.deck.isEmpty then
    throw s!"{seat.name} has an empty deck"
  match validateDeck g.format seat.deck with
  | .error e => throw s!"{seat.name}: {e}"
  | .ok _ => pure ()
  let pid : PlayerId := ⟨seatIdx⟩
  let player : Player := {
    id := pid
    name := seat.name
    life := 20
    startingLife := 20
  }
  let g := { g with players := g.players.push player }
  return Id.run do
    let mut g := g
    for card in seat.deck do
      let (g', obj) := g.allocObject card pid (.library pid)
      g := g'
      g := g.modifyPlayer pid (fun pl => { pl with library := pl.library.push obj.id })
    return g

def start (cfg : StartConfig) : Except String Game := do
  if cfg.seats.size < 2 then
    throw "A game needs at least two players (CR 100.1)"
  let mut g : Game := {
    players := #[]
    objects := #[]
    rng := Rng.ofSeed cfg.seed
    format := cfg.format
    brawl := cfg.brawl
    norandom := cfg.norandom
  }
  for i in [0:cfg.seats.size] do
    g ← materializeSeat g i cfg.seats[i]!
  -- Determine starting player (CR 103.1).
  match cfg.startingPlayer with
  | none =>
    if cfg.norandom then
      g := g.logMsg s!"Rules: {Mtg.Engine.Rules.identification}"
      g := { g with
        pending := .resolveRandom (.chooseIndex g.players.size)
        afterRandom := .setStartingPlayer 0 }
      return g.logMsg
        "Choose who takes the first turn (CR 103.1); the engine will not roll"
    else
      let (rng, r) := g.rng.next
      let startIdx := r.toNat % g.players.size
      let sp : PlayerId := ⟨startIdx⟩
      g := { g with rng := rng, startingPlayer := sp, activePlayer := sp, priority := sp }
      g := g.logMsg s!"Rules: {Mtg.Engine.Rules.identification}"
      g := g.logMsg s!"Starting player: {g.player sp |>.name}"
      for pl in g.players do
        g := g.shuffleLibrary pl.id
      for pl in g.players do
        g := g.draw pl.id (g.player pl.id).startingHandSize
      return g.beginMulliganRound
  | some i =>
    let startIdx := i % g.players.size
    let sp : PlayerId := ⟨startIdx⟩
    g := { g with startingPlayer := sp, activePlayer := sp, priority := sp }
    g := g.logMsg s!"Rules: {Mtg.Engine.Rules.identification}"
    g := g.logMsg s!"Starting player: {g.player sp |>.name}"
    if cfg.norandom then
      return g.continueOpeningShuffles 0
    else
      for pl in g.players do
        g := g.shuffleLibrary pl.id
      for pl in g.players do
        g := g.draw pl.id (g.player pl.id).startingHandSize
      return g.beginMulliganRound

end Start

#guard Format.constructed.minDeckSize == 60

end Mtg.Engine
