import Mtg.Engine.Game.Activation

/-!
# Sacrifice and discard prompts (CR 701.17 / 701.9)

Multi-player sacrifice and discard flows resolved in APNAP order,
connive (CR 701.58), and sacrifices paid for activations.
-/

namespace Mtg.Engine
namespace Game

/-- First player in `players` who satisfies `pred`, plus those after them. -/
def nextActorWhere (_g : Game) (players : Array PlayerId) (pred : PlayerId → Bool) :
    Option (PlayerId × Array PlayerId) :=
  Id.run do
    for i in [0:players.size] do
      let p := players[i]!
      if pred p then
        return some (p, players.extract (i + 1) players.size)
    return none

/-- First player in `players` who controls a creature, plus those after them. -/
def nextActorWithCreatures (g : Game) (players : Array PlayerId) :
    Option (PlayerId × Array PlayerId) :=
  g.nextActorWhere players (fun p =>
    g.stillInGame p && !(g.creaturesControlledBy p).isEmpty)

/-- First player in `players` who has a card in hand, plus those after them. -/
def nextActorWithHandCard (g : Game) (players : Array PlayerId) :
    Option (PlayerId × Array PlayerId) :=
  g.nextActorWhere players (fun p =>
    g.stillInGame p && !(g.player p).hand.isEmpty)

/-- Sacrifice the chosen creatures simultaneously, then give priority. -/
def finishChosenSacrifices (g : Game) (chosen : Array ObjectId) : Game :=
  Id.run do
    let mut g := { g with pending := .none }
    for id in chosen do
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield && o.isCreature then
          let who := o.controller.getD o.owner
          g := g.sacrificeToGraveyard o
            s!"{(g.player who).name} sacrifices {o.name}"
      | none => pure ()
    return g.receivePriority g.activePlayer

/-- Log `msg` for each player in `ps`. -/
def logForPlayers (g : Game) (ps : Array PlayerId) (msg : PlayerId → String) : Game :=
  ps.foldl (fun g p => g.logMsg (msg p)) g

/-- Ask the next player who can sacrifice a creature, or finish if none remain. -/
def beginSacrificeCreatures (g : Game) (players : Array PlayerId)
    (chosen : Array ObjectId := #[]) : Game :=
  match g.nextActorWithCreatures players with
  | none =>
    let skipped := players.filter (fun p => (g.creaturesControlledBy p).isEmpty)
    let g := g.logForPlayers skipped (fun p =>
      s!"{(g.player p).name} has no creature to sacrifice")
    g.finishChosenSacrifices chosen
  | some (p, rest) =>
    { g with pending := .chooseSacrificeCreature p chosen rest }
      |>.logMsg s!"{(g.player p).name} must sacrifice a creature"

/-- Ask the next player who has a card to discard, or resume priority.
`count` is how many cards that player must discard, one at a time. Calling
this twice does not queue two discards; it would replace the pending choice. -/
def beginDiscardCards (g : Game) (players : Array PlayerId) (count : Nat := 1) :
    Game :=
  let g :=
    if count > 1 then { g with pendingDiscardsLeft := count } else g
  match g.nextActorWithHandCard players with
  | none =>
    let skipped := players.filter (fun p => (g.player p).hand.isEmpty)
    let g := g.logForPlayers skipped (fun p =>
      s!"{(g.player p).name} has no card to discard")
    let g :=
      if g.conniveSource.isSome then
        { g with conniveSource := none }.logMsg
          "No card is discarded; the conniving creature does not receive a +1/+1 counter"
      else g
    { g with pending := .none, thirstDiscardsLeft := 0, pendingDiscardsLeft := 0 }
      |>.receivePriority g.activePlayer
  | some (p, rest) =>
    { g with pending := .chooseDiscardCard p rest }
      |>.logMsg s!"{(g.player p).name} must discard a card"

/-- Draw `cards`, then start `discardRounds` discard choices for `p`. -/
def drawThenBeginDiscard (g : Game) (p : PlayerId) (cards : Nat := 1)
    (discardRounds : Nat := 1) : Game :=
  (g.draw p cards).beginDiscardCards #[p] discardRounds

/-- Draw, then discard. If a nonland is discarded and the source is still on
the battlefield, put a +1/+1 counter on it. The creature still connives if it
has left (MSH / CR 701.47). -/
def applyConnive (g : Game) (controller : PlayerId) (sourceId : Option ObjectId) : Game :=
  let extraDraw :=
    (g.permanentsOf controller).any (fun o =>
      o.staticAbilities.any (fun
        | .extraDrawOnConnive => true
        | _ => false))
  let g := { g with conniveSource := sourceId }
  let g := g.logMsg s!"{(g.player controller).name}'s creature connives"
  let g := if extraDraw then g.draw controller 1 else g
  let g := g.draw controller 1
  if (g.player controller).hand.isEmpty then
    let g := { g with conniveSource := none }
    g.logMsg "No card is discarded; the conniving creature does not receive a +1/+1 counter"
  else
    g.beginDiscardCards #[controller]

/-- Finish a pending connive after a card is discarded. -/
def finishConniveDiscard (g : Game) (discarded : GameObject) : Game :=
  match g.conniveSource with
  | none => g
  | some sid =>
    let g := { g with conniveSource := none }
    if discarded.printed.isLand then
      g.logMsg "A land was discarded; the conniving creature does not receive a +1/+1 counter"
    else
      match g.findObject? sid with
      | some o =>
        if o.isOnBattlefield then
          let g := g.setObject { o with status := { o.status with
            plusOnePlusOne := o.status.plusOnePlusOne + 1 } }
          g.logMsg s!"{o.name} gets a +1/+1 counter"
        else
          g.logMsg "The conniving creature has left the battlefield; no +1/+1 counter is put"
      | none =>
        g.logMsg "The conniving creature has left the battlefield; no +1/+1 counter is put"

/-- Villain that would connive for Baron Strucker: an announced target, the
causing object's id stored as last-known power, or the newest other Villain
that entered this turn. -/
def villainConniveTarget? (g : Game) (controller : PlayerId) (sourceId : ObjectId)
    (targets : Array Target) (lastKnownPower : Option Int) : Option ObjectId :=
  match targets[0]? with
  | some (Target.permanent id) => some id
  | _ =>
    match lastKnownPower with
    | some n => some ⟨n.toNat⟩
    | none =>
      let cands :=
        (g.permanentsOf controller).filter (fun x =>
          x.id != sourceId && g.hasSubtype x "Villain" && x.status.enteredThisTurn)
      if cands.isEmpty then none
      else
        some (cands.foldl (fun acc x =>
          if x.timestamp > acc.timestamp then x else acc) cands[0]!).id

/-- Ask whether to have the entering Villain connive (MSH 422). -/
def beginMayHaveVillainConnive (g : Game) (controller : PlayerId)
    (sourceId villainId : ObjectId) : Game :=
  let who :=
    match g.findObject? villainId with
    | some o => o.name
    | none => "the Villain"
  { g with pending := .mayHaveVillainConnive controller sourceId villainId }.logMsg
    s!"{(g.player controller).name} may have {who} connive (do this only once each turn)"

/-- Accept Baron Strucker's optional connive (MSH 422). -/
def haveVillainConnive (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .mayHaveVillainConnive q sourceId villainId =>
    if p != q then
      throw s!"Only {(g.player q).name} may have the Villain connive"
    let g := { g with pending := .none }
    let g :=
      match g.findObject? sourceId with
      | some src =>
        g.setObject { src with status :=
          { src.status with optionalOnceUsed := true } }
      | none => g
    let g := g.applyConnive p (some villainId)
    return g.receivePriority g.activePlayer
  | _ => throw "Not time to have a Villain connive"

/-- After paying K'un-Lun's optional cost, draw a card. -/
def finishSacArtifactOrDiscardDraw (g : Game) (p : PlayerId) : Game :=
  let g := { g with pending := .none }
  g.draw p 1 |>.receivePriority g.activePlayer

/-- After mana is paid, sacrifice an artifact or creature (CR 601.2h / 602.2b), or sacrifice a creature a resolved trigger requires (CR 608.2d / 701.17). -/
def sacrificeForActivation (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  match g.pending with
  | .sacrificePermanent caster sourceId =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may sacrifice"
    let some sac := g.findObject? id | throw "no such object"
    if !g.canSacrificeAsCreatureOrArtifact p sourceId sac then
      throw s!"Can't sacrifice {sac.name}"
    let g := g.sacrificeToGraveyard sac
      s!"{(g.player p).name} sacrifices {sac.name}"
    match g.proposedSpell with
    | some prop =>
      let g := { g with pending := .none, proposedSpell := none, consecutivePasses := 0 }
      match prop.kind with
      | .spell => return g.becomeCast prop.caster (g.object! prop.spellId)
      | .activatedAbility =>
        return g.becomeActivated p prop.original.name prop.sourceId
    | none =>
      let g := { g with pending := .none, proposedSpell := none, consecutivePasses := 0 }
      return g.becomeActivated p (g.object! sourceId).name (some sourceId)
  | .chooseSacrificeCreature q chosen remaining =>
    if q != p then
      throw s!"Only {(g.player q).name} may sacrifice"
    let some sac := g.findObject? id | throw "no such object"
    if !sac.isOnBattlefield || !sac.isCreature || !sac.controlledBy p then
      throw s!"Can't sacrifice {sac.name}"
    return g.beginSacrificeCreatures remaining (chosen.push id)
  | .sacrificeCreature q =>
    if p != q then
      throw s!"Only {(g.player q).name} may sacrifice"
    let some sac := g.findObject? id | throw "no such object"
    if !g.canSacrificeCreature p sac then
      throw s!"Can't sacrifice {sac.name}"
    let g := g.sacrificeToGraveyard sac
      s!"{(g.player p).name} sacrifices {sac.name}"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | .maySacrificeAnotherBolg q bolgId =>
    if p != q then
      throw s!"Only {(g.player q).name} may sacrifice"
    let some sac := g.findObject? id | throw "no such object"
    if !sac.isOnBattlefield || !sac.isCreature || !sac.controlledBy p ||
        sac.id == bolgId then
      throw s!"Can't sacrifice {sac.name} to Bolg"
    let pw := g.power sac
    let g := g.sacrificeToGraveyard sac
      s!"{(g.player p).name} sacrifices {sac.name} (Bolg)"
    let g := { g with pending := .none }
    match g.findObject? bolgId with
    | none =>
      return g.receivePriority g.activePlayer
    | some bolg =>
      match bolg.controller with
      | none => return g.receivePriority g.activePlayer
      | some c =>
        let g := g.queueTrigger c bolg .onBolgDealSacrificedPower
          .bolgSacrificedForReflexive (lastKnownPower := some pw)
        return g.receivePriority g.activePlayer
  | .payWard q _ .sacrificeLegendary =>
    if p != q then
      throw s!"Only {(g.player q).name} may sacrifice for ward"
    let some sac := g.findObject? id | throw "no such object"
    if !(g.legendaryWardSacrificeChoices p).any (fun o => o.id == id) then
      throw s!"Can't sacrifice {sac.name} to pay ward"
    let g := g.sacrificeToGraveyard sac
      s!"{(g.player p).name} sacrifices {sac.name} (ward)"
    return g.afterWardResolved
  | .maySacArtifactOrDiscard q =>
    if p != q then
      throw s!"Only {(g.player q).name} may sacrifice"
    let some sac := g.findObject? id | throw "no such object"
    if !sac.isOnBattlefield || !sac.printed.isArtifact || !sac.controlledBy p then
      throw s!"Can't sacrifice {sac.name}"
    let g := g.sacrificeToGraveyard sac
      s!"{(g.player p).name} sacrifices {sac.name}"
    return g.finishSacArtifactOrDiscardDraw p
  | _ => throw "Not time to sacrifice a permanent"

end Game
end Mtg.Engine
