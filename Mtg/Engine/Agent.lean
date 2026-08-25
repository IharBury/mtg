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
    | .activateManaAbilities _ =>
      chooseManaPayment g p
    | .sacrificePermanent _ sourceId =>
      match (g.sacrificeCreatureOrArtifactChoices p sourceId)[0]? with
      | some sac => some (.sacrifice sac.id)
      | none => some .pass
    | .declareMulligan _ =>
      some .keep
    | .putOnBottom _ n =>
      some (.putOnBottom ((g.player p).hand.extract 0 n))
    | .none =>
      -- Play a land if possible (from hand or from exile under a permission).
      let lands :=
        (g.handObjects p).filter (·.printed.isLand) ++
        (g.exiledPlayable p).filter (·.printed.isLand)
      if g.canPlayLand p then
        match lands[0]? with
        | some land => some (.playLand land.id)
        | none =>
          chooseActivate g p
      else
        chooseActivate g p
where
  /-- During CR 601.2g, tap sources until the locked-in cost is payable, then pay. -/
  chooseManaPayment (g : Game) (p : PlayerId) : Option Action :=
    match g.proposedSpell with
    | none => some .pay
    | some prop =>
      if (g.player p).manaPool.canPay prop.cost then
        some .pay
      else
        match (g.manaSources p)[0]?, (g.manaSources p)[0]?.bind (fun s => s.snd[0]?) with
        | some (src, _), some t => some (.tapForMana src.id t)
        | _, _ => some .pay
  /-- Activate a non-mana ability if the available mana covers its cost. -/
  chooseActivate (g : Game) (p : PlayerId) : Option Action :=
    let available := g.availableMana p
    let candidate := (g.permanentsOf p).find? (fun o =>
      match o.printed.activatedAbilities[0]? with
      | some ab => g.canActivate p o ab && available.canPay ab.cost.mana
      | none => false)
    match candidate with
    | some o => some (.activate o.id 0)
    | none => chooseCast g p
  chooseCast (g : Game) (p : PlayerId) : Option Action :=
    let available := g.availableMana p
    let playable := (g.handObjects p ++ g.exiledPlayable p).filter (fun o =>
      g.canCast p o && available.canPay o.printed.manaCost)
    let opp := Target.player (g.opponent p)
    let ownCreature := (g.permanentsOf p).filter (·.printed.isCreature) |>.back?
    let burn := playable.find? (fun o =>
      match o.printed.spellEffect with
      | some (.dealDamage _) => true
      | _ => false)
    let creature := playable.find? (fun o => o.printed.isCreature)
    let artifact := playable.find? (fun o =>
      o.printed.types.any (· == .artifact) && !o.printed.activatedAbilities.isEmpty)
    let pump :=
      if ownCreature.isSome then
        playable.find? (fun o =>
          match o.printed.spellEffect with
          | some (.pump _ _) => true
          | _ => false)
      else none
    if let some o := burn then
      some (.cast o.id (some opp))
    else if let some o := creature then
      some (.cast o.id none)
    else if let some o := artifact then
      some (.cast o.id none)
    else if let some o := pump then
      match ownCreature with
      | some t => some (.cast o.id (some (.permanent t.id)))
      | none => some .pass
    else
      some .pass

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
    else if !g.playersReceivePriority && g.pending == .none then
      -- Untap, or a cleanup with no CR 514.3a exception: recover by advancing.
      play (g.advanceStep) n
    else
      match step g with
      | .ok g' => play g' n
      | .error e => g.logMsg s!"Agent error: {e}"

end Mtg.Engine.Agent
