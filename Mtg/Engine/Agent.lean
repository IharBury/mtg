import Mtg.Engine.Game

/-!
# Demonstration agent

A deterministic heuristic used by `Mtg.Demo` and compile-time smoke tests
to exercise the engine without a human at the console.
-/

namespace Mtg.Engine.Agent

open Mtg.Engine
open Mtg.Engine.Game

/-- Choose a single legal action for `p`, or `none` if that player is not to act. -/
def choose (g : Game) (p : PlayerId) : Option Action :=
  if g.over then none
  else if g.actor != some p then none
  else
    match g.pending with
    | .declareAttackers =>
      let ids := g.battlefield.filter (g.canAttack) |>.map (·.id)
      some (.declareAttackers ids)
    | .declareBlockers =>
      -- Naive: don't block. The demo still exercises the declare-blockers step.
      some (.declareBlockers #[])
    | .none =>
      -- Play a land if possible.
      let lands := (g.handObjects p).filter (·.printed.isLand)
      if g.canPlayLand p then
        match lands[0]? with
        | some land => some (.playLand land.id)
        | none =>
          chooseCast g p
      else
        chooseCast g p
where
  chooseCast (g : Game) (p : PlayerId) : Option Action :=
    let sources := g.manaSources p
    let pool := (g.player p).manaPool
    let hand := g.handObjects p
    let playable := hand.filter (fun o =>
      !o.printed.isLand &&
      (if o.printed.hasSorcerySpeed then g.asSorcery? p else g.hasPriority p))
    let castable := playable.filter (fun o => pool.canPay o.printed.manaCost)
    let opp := Target.player (g.opponent p)
    let ownCreature := (g.permanentsOf p).filter (·.printed.isCreature) |>.back?
    let burn := castable.find? (fun o =>
      match o.printed.spellEffect with
      | some (.dealDamage _) => true
      | _ => false)
    let creature := castable.find? (fun o => o.printed.isCreature)
    let pump :=
      if ownCreature.isSome then
        castable.find? (fun o =>
          match o.printed.spellEffect with
          | some (.pump _ _) => true
          | _ => false)
      else none
    if let some o := burn then
      some (.cast o.id (some opp))
    else if let some o := creature then
      some (.cast o.id none)
    else if let some o := pump then
      match ownCreature with
      | some t => some (.cast o.id (some (.permanent t.id)))
      | none => some .pass
    else
      -- Only tap for mana if a currently-castable spell still needs it.
      let unpaid := playable.filter (fun o => !pool.canPay o.printed.manaCost)
      if unpaid.isEmpty then some .pass
      else
        match sources[0]?, sources[0]?.bind (fun s => s.snd[0]?) with
        | some (src, _), some t => some (.tapForMana src.id t)
        | _, _ => some .pass

/-- Apply the heuristic once. Returns `none` if no actor or the action failed. -/
def step (g : Game) : Except String Game := do
  match g.actor with
  | none => throw "No player has an action"
  | some p =>
    match choose g p with
    | none => g.apply p .pass
    | some a => g.apply p a

/-- Run the heuristic until the game ends or `fuel` actions have been taken. -/
def play (g : Game) (fuel : Nat := 400) : Game :=
  match fuel with
  | 0 => g.logMsg "Stopped: action limit reached"
  | n + 1 =>
    if g.over then g
    else if g.step.playersReceivePriority == false && g.pending == .none then
      -- Should not happen after beginTurn skips untap; recover by advancing.
      play (g.advanceStep) n
    else
      match step g with
      | .ok g' => play g' n
      | .error e => g.logMsg s!"Agent error: {e}"

end Mtg.Engine.Agent
