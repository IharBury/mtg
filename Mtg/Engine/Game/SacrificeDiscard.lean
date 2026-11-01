import Mtg.Engine.Game.Costs

/-!
# Sacrifice and discard prompts (CR 701.21 / 701.9)

Multi-player sacrifice and discard flows resolved in APNAP order,
connive (CR 701.50), and sacrifices paid for activations.
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
  let validIds := chosen.filter (fun id =>
    (g.findObject? id).any (fun o => o.isOnBattlefield && g.isCreature o))
  let preBf := g.battlefield
  let g := g.withBatch none fun g => Id.run do
    let mut g := g.change (.pending .none)
    for id in validIds do
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield then
          let who := (g.controllerOf o).getD o.owner
          g := g.sacrificeToGraveyard o
            s!"{(g.player who).name} sacrifices {g.name o}"
            (preBattlefield := some preBf)
      | none => pure ()
    return g
  g.receivePriority g.activePlayer

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
    (g.change (.pending (.chooseSacrificeCreature p chosen rest))).logMsg
      s!"{(g.player p).name} must sacrifice a creature"

/-- Ask the next player who has a card to discard, or resume priority.
`count` is how many cards that player must discard, one at a time. Calling
this twice does not queue two discards; it would replace the pending choice. -/
def beginDiscardCards (g : Game) (players : Array PlayerId) (count : Nat := 1) :
    Game :=
  let g :=
    if count > 1 && g.continuations.isEmpty then
      g.change (.pushContinuationFrame {})
    else g
  let g :=
    if count > 1 then g.change (.pendingDiscardsLeft count) else g
  match g.nextActorWithHandCard players with
  | none =>
    let skipped := players.filter (fun p => (g.player p).hand.isEmpty)
    let g := g.logForPlayers skipped (fun p =>
      s!"{(g.player p).name} has no card to discard")
    let g :=
      if g.conniveSource.isSome then
        (g.change (.conniveSource none)).logMsg
          "No card is discarded; the conniving creature does not receive a +1/+1 counter"
      else g
    let g := g.changes #[.pending .none, .thirstDiscardsLeft 0, .pendingDiscardsLeft 0]
    -- A following +1/+1 counter, or the rest of a trigger sequence, waits
    -- until the caller finishes the discards.
    if g.plusOneAfterDiscards.isSome || g.triggerSequenceRest.isSome then g
    else g.receivePriority g.activePlayer
  | some (p, rest) =>
    (g.change (.pending (.chooseDiscardCard p rest))).logMsg
      s!"{(g.player p).name} must discard a card"

/-- Draw `cards`, then start `discardRounds` discard choices for `p`. -/
def drawThenBeginDiscard (g : Game) (p : PlayerId) (cards : Nat := 1)
    (discardRounds : Nat := 1) : Game :=
  let g := g.draw p cards
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishDrawThenBeginDiscard p discardRounds)
  else
    g.beginDiscardCards #[p] discardRounds

/-- Execute the remaining `extraDraws`, connive draw, and discard prompt of
`applyConnive` (`stage` 0 = extra draws + connive draw + discard, 1 = connive
draw + discard, 2 = discard). -/
def finishConniveDraws (g : Game) (controller : PlayerId)
    (extraDraws : Array (Nat × ReplacementId))
    (conniveDrawCause : Option EventCause) (stage : Nat := 0) : Game := Id.run do
  let mut g := g
  if stage == 0 then
    for i in [0:extraDraws.size] do
      let (n, rid) := extraDraws[i]!
      let c := g.wrapReplacedCause rid none (some controller)
      g := g.draw controller n (cause := c)
      if let .chooseReplacement .. := g.pending then
        let rem := extraDraws.extract (i + 1) extraDraws.size
        return g.chainPendingReplacement (.finishConniveDraws controller rem conniveDrawCause 0)
  if stage <= 1 then
    g := g.draw controller 1 (cause := conniveDrawCause)
    if let .chooseReplacement .. := g.pending then
      return g.chainPendingReplacement (.finishConniveDraws controller #[] conniveDrawCause 2)
  if (g.player controller).hand.isEmpty then
    g := g.change (.conniveSource none)
    return g.logMsg "No card is discarded; the conniving creature does not receive a +1/+1 counter"
  else
    return g.beginDiscardCards #[controller]

/-- Draw, then discard. If a nonland is discarded and the source is still on
the battlefield, put a +1/+1 counter on it. The creature still connives if it
has left (MSH / CR 701.50). -/
def applyConnive (g : Game) (controller : PlayerId) (sourceId : Option ObjectId) : Game :=
  let run (g : Game) : Game :=
    -- CR 616.1 replacement loop for Leader's `.extraDrawOnConnive` ("If a
    -- creature you control would connive, draw a card, then that creature
    -- connives instead", CR 614.5).
    let (extraDraws, curApplied, choice?) :
        Array (Nat × ReplacementId) × Array ReplacementId × Option (PlayerId × Array ReplacementId) := Id.run do
      let mut draws : Array (Nat × ReplacementId) := #[]
      let mut curApplied : Array ReplacementId := #[]
      let mut choice? : Option (PlayerId × Array ReplacementId) := none
      let mut fuel := 32
      while fuel > 0 do
        fuel := fuel - 1
        let mut specs : Array (ReplacementSpec × Nat) := #[]
        for o in g.permanentsOf controller do
          if (g.staticAbilities o).any (· == .extraDrawOnConnive) then
            specs := specs.push (
              { id := { kind := .extraDrawOnConnive, object := some o.id }
                source := some o.id
                controller := some controller
                affectedPlayer := controller
                kind := .extraDrawOnConnive controller 1 }, 1)
        for (_, eff) in g.activeEffects do
          match eff with
          | .replacement spec _ =>
            match spec.kind with
            | .extraDrawOnConnive who n =>
              if who == controller then specs := specs.push (spec, n)
            | _ => pure ()
          | _ => pure ()
        let candidates := specs.map (fun (s, _) => (ReplacementOrPrevention.replacement s).toCandidate)
        match g.selectNextReplacementStep candidates curApplied with
        | .none => fuel := 0
        | .needChoice chooser choices _ =>
          choice? := some (chooser, choices)
          fuel := 0
        | .chosen chosen _ =>
          match specs.find? (fun (s, _) => s.id == chosen.id) with
          | none => fuel := 0
          | some (_, n) =>
            curApplied := curApplied.push chosen.id
            draws := draws.push (n, chosen.id)
      return (draws, curApplied, choice?)
    match choice? with
    | some (chooser, choices) =>
      g.promptChooseReplacement chooser choices (.connive controller sourceId)
    | none =>
      let g := g.consumeReplacementOrder curApplied
      let g := g.change (.conniveSource sourceId)
      let g := g.logMsg s!"{(g.player controller).name}'s creature connives"
      let conniveDrawCause :=
        extraDraws.foldl (fun acc (_, rid) =>
          g.wrapReplacedCause rid acc (some controller)) none
      g.finishConniveDraws controller extraDraws conniveDrawCause 0
  g.withContinuationFrame run

/-- Finish a pending connive after a card is discarded. -/
def finishConniveDiscard (g : Game) (discarded : GameObject) : Game :=
  match g.conniveSource with
  | none => g
  | some sid =>
    let g := g.change (.conniveSource none)
    if g.isLand discarded then
      g.logMsg "A land was discarded; the conniving creature does not receive a +1/+1 counter"
    else
      match g.findObject? sid with
      | some o =>
        if o.isOnBattlefield then
          g.addPlusOnePlusOneTo o 1 (byPlayer := g.controllerOf o)
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
          x.id != sourceId && g.hasSubtype x .villain && g.loggedEntered x.id)
      if cands.isEmpty then none
      else
        some (cands.foldl (fun acc x =>
          if x.timestamp > acc.timestamp then x else acc) cands[0]!).id

/-- Ask whether to have the entering Villain connive (MSH 422). -/
def beginMayHaveVillainConnive (g : Game) (controller : PlayerId)
    (sourceId villainId : ObjectId) : Game :=
  let who :=
    match g.findObject? villainId with
    | some o => if o.isOnBattlefield then g.name o else o.name
    | none => "the Villain"
  (g.change (.pending (.mayHaveVillainConnive controller sourceId villainId))).logMsg
    s!"{(g.player controller).name} may have {who} connive (do this only once each turn)"

/-- Accept Baron Strucker's optional connive (MSH 422). -/
def haveVillainConnive (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .mayHaveVillainConnive q sourceId villainId =>
    if p != q then
      throw s!"Only {(g.player q).name} may have the Villain connive"
    let g := g.change (.pending .none)
    let g :=
      if (g.findObject? sourceId).isSome then
        g.record (GameEvent.optionalOnceActed g.turnNumber p sourceId
          (cause := some (.oneShotEffect none (some sourceId) (some p))))
      else g
    let g := g.applyConnive p (some villainId)
    return g.receivePriority g.activePlayer
  | _ => throw "Not time to have a Villain connive"

/-- After paying K'un-Lun's optional cost, draw a card. Inside `mayThen` the
conditional does the draw, so this only records that the cost was paid. -/
def finishSacArtifactOrDiscardDraw (g : Game) (p : PlayerId) (n : Nat) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishSacArtifactOrDiscardDraw p n)
  else if g.mayThenDrop > 0 then
    g.changes #[.pending .none, .mayThenResume true]
  else
    let g := g.change (.pending .none)
    g.draw p n |>.receivePriority g.activePlayer

/-- After mana is paid, sacrifice an artifact or creature (CR 601.2h / 602.2b), or sacrifice a creature a resolved trigger requires (CR 608.2d / 701.21). -/
def sacrificeForActivation (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  match g.pending with
  | .sacrificePermanent caster sourceId =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may sacrifice"
    let some sac := g.findObject? id | throw "no such object"
    if !g.canSacrificeAsCreatureOrArtifact p sourceId sac then
      throw s!"Can't sacrifice {g.name sac}"
    let forObject := g.proposedSpell.map (·.spellId) <|> some sourceId
    let outerCont? := g.pendingReplacement
    let openCont := g.proposalHadOpenContinuation
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := g.withProposalAction .costAction fun g =>
      g.sacrificeToGraveyard sac
        s!"{(g.player p).name} sacrifices {g.name sac}"
        (cause := some (.costPayment .sacrifice p forObject))
    let paused := match g.pending with | .chooseReplacement .. => true | _ => false
    let g :=
      if !paused then
        match outerCont? with
        | some outer => g.chainPendingReplacement outer
        | none => g
      else g
    let clearPending : Array EngineChange :=
      if paused then #[] else #[.pending .none]
    let g :=
      match g.proposedSpell with
      | some prop =>
        let isResCast := prop.resolutionCast
        let g := g.changes (clearPending ++ #[.proposedSpell none, .consecutivePasses 0])
        match prop.kind with
        | .spell =>
          g.becomeCast prop.caster (g.object! prop.spellId)
            (grantPriority := !isResCast)
            (hadOuterReplacement := outerCont?.isSome)
            (hadOpenContinuation := some openCont)
        | .activatedAbility =>
          g.becomeActivated p prop.originalSnapshot.name prop.sourceId prop.activation
            (abilityId := some prop.spellId)
            (sourceSnapshot := some prop.originalSnapshot)
            (sourceOriginal := some prop.original)
            (hadOuterReplacement := outerCont?.isSome)
            (hadOpenContinuation := some openCont)
        | .turnFaceUp => g
      | none =>
        let g := g.changes (clearPending ++ #[.proposedSpell none, .consecutivePasses 0])
        g.becomeActivated p (g.name (g.object! sourceId)) (some sourceId)
          (hadOuterReplacement := outerCont?.isSome)
          (hadOpenContinuation := some openCont)
    let g :=
      if paused then
        match outerCont? with
        | some outer => g.chainPendingReplacement outer.ensureEndsWithFinishFra
        | none => g
      else g
    return g
  | .chooseSacrificeCreature q chosen remaining =>
    if q != p then
      throw s!"Only {(g.player q).name} may sacrifice"
    let some sac := g.findObject? id | throw "no such object"
    if !sac.isOnBattlefield || !g.isCreature sac || !g.controlledBy sac p then
      throw s!"Can't sacrifice {g.name sac}"
    return g.beginSacrificeCreatures remaining (chosen.push id)
  | .sacrificeCreature q =>
    if p != q then
      throw s!"Only {(g.player q).name} may sacrifice"
    let some sac := g.findObject? id | throw "no such object"
    if !g.canSacrificeCreature p sac then
      throw s!"Can't sacrifice {g.name sac}"
    let g := (g.change (.pending .none)).sacrificeToGraveyard sac
      s!"{(g.player p).name} sacrifices {g.name sac}"
    if let .chooseReplacement .. := g.pending then
      return g.chainPendingReplacement (.receivePriority g.activePlayer)
    else
      return g.receivePriority g.activePlayer
  | .maySacrificeAnotherBolg q bolgId =>
    if p != q then
      throw s!"Only {(g.player q).name} may sacrifice"
    let some sac := g.findObject? id | throw "no such object"
    if !sac.isOnBattlefield || !g.isCreature sac || !g.controlledBy sac p ||
        sac.id == bolgId then
      throw s!"Can't sacrifice {g.name sac} to Bolg"
    let g := g.sacrificeToGraveyard sac
      s!"{(g.player p).name} sacrifices {g.name sac} (Bolg)"
    if let .chooseReplacement .. := g.pending then
      return g.chainPendingReplacement (.receivePriority g.activePlayer)
    else
      return (g.change (.pending .none)).receivePriority g.activePlayer
  | .payWard q spellId (.sacrificePermanents left paid) =>
    if p != q then
      throw s!"Only {(g.player q).name} may sacrifice for ward"
    let some sac := g.findObject? id | throw "no such object"
    if !sac.isOnBattlefield || !g.controlledBy sac p then
      throw s!"Can't sacrifice {g.name sac} to pay ward"
    if paid == 0 && (g.permanentsOf p).size < left then
      throw s!"{(g.player p).name} can't sacrifice {left} permanents"
    let g := (g.change (.pending .none)).sacrificeToGraveyard sac
      s!"{(g.player p).name} sacrifices {g.name sac} (ward)"
      (cause := some (.costPayment .ward p (some spellId)))
    if left ≤ 1 then return g.afterWardResolved
    else
      let nextP := Pending.payWard q spellId (.sacrificePermanents (left - 1) (paid + 1))
      if let .chooseReplacement .. := g.pending then
        return g.chainPendingReplacement (.restorePending nextP)
      else
        return g.change (.pending nextP)
  | .payWard q spellId .sacrificeLegendary =>
    if p != q then
      throw s!"Only {(g.player q).name} may sacrifice for ward"
    let some sac := g.findObject? id | throw "no such object"
    if !(g.legendaryWardSacrificeChoices p).any (fun o => o.id == id) then
      throw s!"Can't sacrifice {g.name sac} to pay ward"
    let g := (g.change (.pending .none)).sacrificeToGraveyard sac
      s!"{(g.player p).name} sacrifices {g.name sac} (ward)"
      (cause := some (.costPayment .ward p (some spellId)))
    return g.afterWardResolved
  | .maySacArtifactOrDiscard q n =>
    if p != q then
      throw s!"Only {(g.player q).name} may sacrifice"
    let some sac := g.findObject? id | throw "no such object"
    if !sac.isOnBattlefield || !g.isArtifact sac || !g.controlledBy sac p then
      throw s!"Can't sacrifice {g.name sac}"
    let g := (g.change (.pending .none)).sacrificeToGraveyard sac
      s!"{(g.player p).name} sacrifices {g.name sac}"
    return g.finishSacArtifactOrDiscardDraw p n
  | _ => throw "Not time to sacrifice a permanent"

/-- `p` discards `id` from their hand (CR 701.9). -/
def discardFromHand (g : Game) (p : PlayerId) (id : ObjectId) (chooser : Option PlayerId := none)
    (cause : Option EventCause := none) :
    Game :=
  let card := g.object! id
  let g :=
    match chooser with
    | some c => g.logMsg s!"{(g.player c).name} chooses {card.name}. {(g.player p).name} discards it"
    | none => g.logMsg s!"{(g.player p).name} discards {card.name}"
  let (g, _) := g.move id (.graveyard card.owner) none (verb := some .discard)
    (actor := some p) (cause := cause)
  g

/-- `p` discards `id`, chosen at random (CR 701.9). -/
def discardFromHandRandomly (g : Game) (p : PlayerId) (id : ObjectId) : Game :=
  (g.logMsg s!"{(g.player p).name} discards a card at random").discardFromHand p id

end Game
end Mtg.Engine
