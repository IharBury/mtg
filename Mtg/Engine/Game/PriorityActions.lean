import Mtg.Engine.Game.Turns

/-!
# Passing, paying, and conceding

`pay` while a cost is proposed, announcing optional additional generic
costs, `pass` (CR 117.3d), and `concede` (CR 104.3a).
-/

namespace Mtg.Engine
namespace Game

/-- Pay the proposed spell or ability (CR 601.2h / 602.2b). If the cost
cannot be paid, the action is reversed (CR 733.1). -/
def pay (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .activateManaAbilities caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may pay (CR 601.2h)"
    g.finishProposedSpell
  | .chooseMode _ =>
    throw "Choose a mode first (CR 601.2b)"
  | .chooseX _ =>
    throw "Choose a value for X first (CR 107.3a / 601.2b)"
  | .chooseTargets _ =>
    throw "Choose a target first (CR 601.2c)"
  | .chooseAdditionalCost _ =>
    throw "Choose an additional cost first (CR 601.2b)"
  | .payWard q _ .fivePoison =>
    if p != q then
      throw s!"Only {(g.player q).name} may pay ward"
    let g := g.modifyPlayer p (fun pl => { pl with poison := pl.poison + 5 })
    let g := g.logMsg s!"{(g.player p).name} gets five poison counters (ward)"
    return g.afterWardResolved
  | _ => throw "No spell or ability is waiting to be paid for (CR 601.2h)"

/-- Announce whether to pay extra generic mana or sacrifice an artifact or
creature as an additional cost (CR 601.2b), before targets (CR 601.2c). -/
def announceAdditionalCost (g : Game) (p : PlayerId) (payGeneric : Bool) :
    Except String Game := do
  match g.pending with
  | .chooseAdditionalCost q =>
    if p != q then
      throw s!"Only {(g.player q).name} may choose an additional cost (CR 601.2b)"
    let some prop := g.proposedSpell
      | throw "No spell is waiting for an additional cost (CR 601.2b)"
    let some spell := g.findObject? prop.spellId
      | throw "The spell left the stack"
    match spell.printed.additionalCostOrPayGeneric with
    | none => throw "That spell has no alternative additional cost"
    | some n =>
      if payGeneric then
        let prop := { prop with
          cost := prop.cost.addGeneric n
          needsSacrificeOther := false }
        let g := { g with proposedSpell := some prop }
        let g := g.logMsg
          s!"{(g.player p).name} chooses to pay \{{n}} as an additional cost (CR 601.2b)"
        return g.afterAdditionalCostAnnounced
      else
        if (g.sacrificeCreatureOrArtifactChoices p prop.spellId).isEmpty then
          throw s!"{spell.name} requires sacrificing an artifact or creature"
        let prop := { prop with needsSacrificeOther := true }
        let g := { g with proposedSpell := some prop }
        let g := g.logMsg
          s!"{(g.player p).name} chooses to sacrifice an artifact or creature (CR 601.2b)"
        return g.afterAdditionalCostAnnounced
  | _ => throw "Not time to choose an additional cost (CR 601.2b)"

def pass (g : Game) (p : PlayerId) : Except String Game := do
  if g.over then
    throw "The game is over"
  if g.pending != .none then
    throw "A required choice is still pending"
  if !g.playersReceivePriority then
    throw "No player receives priority right now (CR 117.3a / 514.3)"
  if g.priority != p then
    throw "You don't have priority"
  let g := g.logMsg s!"{g.player p |>.name} passes priority"
  let g := { g with consecutivePasses := g.consecutivePasses + 1 }
  if g.consecutivePasses ≥ g.livingPlayers.size then
    if !g.stack.isEmpty then
      let g := g.resolveTop
      if g.pending != .none then
        return g
      return g.receivePriority g.activePlayer
    else
      return g.advanceStep
  else
    return { g with priority := g.nextLiving p }

def concede (g : Game) (p : PlayerId) : Game :=
  if (g.player p).lost then g
  else
    let pl := g.player p
    let g := g.setPlayer { pl with lost := true }
    let g := g.logMsg s!"{pl.name} concedes (CR 104.3a)"
    match g.decideGameIfFinished with
    | some finished => finished
    | none => g.playerLeavesGame p |>.checkSBA

end Game
end Mtg.Engine
