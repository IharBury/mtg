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
  let g := g.change (.players (g.players.push player))
  return Id.run do
    let mut g := g
    for card in seat.deck do
      let (g', obj) := g.allocObject card pid (.library pid)
      g := g'
      g := g.changePlayer pid (.pushLibrary obj.id)
    -- CR 400.11b: sideboard cards are outside the game. They become objects
    -- only when an effect reaches outside the game.
    g := g.changePlayer pid (.sideboard seat.sideboard)
    return g

def startWithRng (cfg : StartConfig) : Except String (Game × Rng) := do
  if cfg.seats.size < 2 then
    throw "A game needs at least two players (CR 100.1)"
  let mut g : Game := ({} : Game).changes #[
    .format cfg.format,
    .brawl cfg.brawl ]
  for i in [0:cfg.seats.size] do
    g ← materializeSeat g i cfg.seats[i]!
  let rng := Rng.ofSeed cfg.seed
  -- Determine starting player (CR 103.1).
  let (rng, g1) :=
    match cfg.startingPlayer with
    | none =>
      if cfg.norandom then
        let g1 := g.logMsg s!"Rules: {Mtg.Engine.Rules.identification}"
        let g1 := g1.changes #[
          .pending (.resolveRandom (.chooseIndex g1.players.size)),
          .afterRandom (.setStartingPlayer 0) ]
        let g1 := g1.logMsg
          "Choose who takes the first turn (CR 103.1); the engine will not roll"
        (rng, g1)
      else
        let (rng, r) := rng.next
        let startIdx := r.toNat % g.players.size
        let sp : PlayerId := ⟨startIdx⟩
        let g1 := g.changes #[.startingPlayer sp, .priority sp]
        let g1 := g1.logMsg s!"Rules: {Mtg.Engine.Rules.identification}"
        let g1 := g1.logMsg s!"Starting player: {g1.player sp |>.name}"
        (rng, g1.continueOpeningShuffles 0)
    | some i =>
      let startIdx := i % g.players.size
      let sp : PlayerId := ⟨startIdx⟩
      let g1 := g.changes #[.startingPlayer sp, .priority sp]
      let g1 := g1.logMsg s!"Rules: {Mtg.Engine.Rules.identification}"
      let g1 := g1.logMsg s!"Starting player: {g1.player sp |>.name}"
      (rng, g1.continueOpeningShuffles 0)
  if cfg.norandom then
    return (g1, rng)
  else
    let (rng, g2) := g1.resolvePendingRandom rng
    return (g2, rng)

def start (cfg : StartConfig) : Except String Game :=
  (·.1) <$> startWithRng cfg

end Start

#guard Format.constructed.minDeckSize == 60

end Mtg.Engine
