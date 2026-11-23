import Mtg.Engine.Game.Interpreter

/-!
# Triggered-ability resolution (CR 603)

`applyTriggeredAbility` delegates all triggered-ability effects (including Saga
chapters, reflexive triggers, and keyword triggers) to the unified
`Interpreter.applyUnifiedAbility` machine. Also retains the small set of
mode-memory (`applyAllianceMode`, `applyGollumMode`), Palantír choice
(`offerPalantirChoice`), attacking-token (`createAndMarkTokensAttacking`), and
multi-connive (`runConniveObjects`) helpers referenced by interactive choice
and replacement-resumption handlers.
-/

namespace Mtg.Engine
namespace Game

/-- The target opponent may have `controller` draw a card (Palantír). -/
def offerPalantirChoice (g : Game) (controller opp : PlayerId) (sid : ObjectId) : Game :=
  if !g.stillInGame controller then g
  else if !g.stillInGame opp then
    let n := ((g.damageSourceById? sid).map (·.status.influence)).getD 0
    g.mill controller n
  else
    g.beginFraChoice opp (.palantirMayDraw controller sid)
      s!"{(g.player opp).name} may have {(g.player controller).name} draw a card"

/-- Apply one Alliance mode of `sourceId` if it has not been chosen this turn.
If every mode was already chosen, the ability is removed with no effect. -/
def applyAllianceMode (g : Game) (sourceId : ObjectId) (mode : Nat) : Game :=
  match g.findObject? sourceId with
  | none =>
    g.logMsg "The ability is removed from the stack with no effect"
  | some src =>
    let chosen := g.modesChosenThisTurn sourceId
    if chosen.size >= 3 || (g.unusedAllianceModes src).isEmpty then
      g.logMsg
        "all three modes have been chosen this turn. The ability is removed from the stack with no effect"
    else if chosen.contains mode then
      g.logMsg "That Alliance mode has already been chosen this turn"
    else
      let g := g.record (GameEvent.triggerModeChosen g.turnNumber sourceId mode)
      match g.controllerOf src, mode with
      | some c, 0 =>
        let g := g.addMana c (.colored .green) 3 (source := some sourceId)
        g.logMsg s!"{(g.player c).name} adds mana (\{G}\{G}\{G})"
      | some c, 1 =>
        let creatures := (g.battlefield.filter (fun o => g.isCreature o && g.controlledBy o c)).map (·.id)
        let g := g.withBatch none fun g =>
          creatures.foldl (fun g id =>
            match g.findObject? id with
            | some o => g.addPlusOnePlusOneTo o 1
            | none => g) g
        let msg := s!"{(g.player c).name} puts a +1/+1 counter on each creature they control"
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.logMessage msg)
        else
          g.logMsg msg
      | some c, 2 =>
        g.scryThenDraw c 2 1
      | _, _ => g

/-- Apply one unused Gollum mode. If every mode was already chosen, the
ability is removed with no effect and Gollum remains. -/
def applyGollumMode (g : Game) (sourceId : ObjectId) (mode : Nat) : Game :=
  match g.findObject? sourceId with
  | none =>
    g.logMsg "The ability is removed from the stack with no effect"
  | some src =>
    let chosen := g.modesChosenEver sourceId
    if (g.unusedGollumModes src).isEmpty then
      g.logMsg
        "all three modes have been chosen. The ability is removed from the stack with no effect"
    else if chosen.contains mode then
      g.logMsg "That mode has already been chosen"
    else
      let g := g.record (GameEvent.triggerModeChosen g.turnNumber sourceId mode (lifetime := true))
      match g.controllerOf src, mode with
      | some _, 0 =>
        g.addPlusOnePlusOneTo (g.object! sourceId) 1
      | some c, 1 =>
        g.eachOpponentLosesYouGain c 2
      | some c, 2 =>
        g.draw c 1
      | _, _ => g

/-- Create `n` tokens of `kind`, entering tapped (`tapped`) and attacking
(`holds`) under `controller`'s control, prompting for entering-attacking
targets (CR 508.4) and tied copy candidates (CR 707.2) as needed. -/
def createAndMarkTokensAttacking (g : Game) (controller : PlayerId)
    (kind : TokenSpec) (n : Nat) (tapped holds : Bool)
    (sourceId : Option ObjectId := none)
    (cause : Option EventCause := none)
    (copyEnv : StoredEvalEnv := {}) : Game :=
  let effectiveCopyEnv : StoredEvalEnv :=
    { copyEnv with sourceId := copyEnv.sourceId.orElse (fun _ => sourceId) }
  let (g, c) : Game × EventCause :=
    match cause with
    | some existing => (g, existing)
    | none => g.allocDelayedCause (some controller) sourceId
  let cause := some c
  if let .chooseReplacement .. := g.pending then
    if n == 0 then g
    else
      g.chainPendingReplacement
        (.createAndMarkTokensAttacking controller kind n tapped holds sourceId cause effectiveCopyEnv)
  else if !holds then
    g.createKindTokens controller kind n (tapped := tapped) (attacking := false) (cause := cause)
      (copyEnv := effectiveCopyEnv)
  else if !g.stillInGame controller then
    let g := g.change (.recentTokenIds #[])
    if n == 0 then g
    else g.logMsg "no token is created (CR 800.4b)"
  else
    let tiedCopyIds? : Option (Array ObjectId × Array CopyModification) :=
      match kind with
      | .copyOf ref mods =>
        let cands := g.resolveCopyTokenCandidates ref mods 0 effectiveCopyEnv (controller := controller)
        let ids := cands.filterMap Prod.fst
        if cands.size > 1 && ids.size > 1 then some (ids, mods) else none
      | _ => none
    match tiedCopyIds? with
    | some (ids, mods) =>
      let g := g.change (.recentTokenIds #[])
      if n == 0 then g
      else
        g.beginFraChoice controller
          (.chooseTokenCopyObject ids mods n tapped true none #[] cause sourceId)
          s!"{(g.player controller).name} chooses an object to copy"
    | none =>
      match g.resolveTokenPrinted? kind 0 effectiveCopyEnv (controller := controller) with
      | none =>
        let g := g.change (.recentTokenIds #[])
        if n == 0 then g else g.logMsg "no token is created (CR 111.5 / 111.12)"
      | some rawPrinted =>
        let (batches, applied, choice?) := g.replaceTokenCreationChoice {
          controller := controller
          printed := rawPrinted
          count := n
          tapped := tapped
          attacking := true
          cause := cause
        }
        match choice? with
        | some (chooser, choices) =>
          let outerCont? := g.pendingReplacement
          let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
          let g := g.promptChooseReplacement chooser choices
            (.createAndMarkTokensAttacking controller kind n tapped holds sourceId cause effectiveCopyEnv)
          match outerCont? with
          | some outer => g.chainPendingReplacement outer
          | none => g
        | none =>
          let g := g.consumeReplacementOrder applied
          let expanded : Array ProposedTokenBatch := batches.foldl (fun acc b =>
            Id.run do
              let mut acc := acc
              for _ in [0:b.count] do
                acc := acc.push { b with count := 1 }
              return acc) #[]
          if expanded.isEmpty then
            g.change (.recentTokenIds #[])
          else
            let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
            let g := g.change (.stagedAttackTokenBatches expanded)
            let items := expanded.map fun b =>
              let isCreature := g.isCreature (g.tokenBatchProbe b.controller b.printed)
              let opts := if isCreature then g.legalEnteringAttackTargets b.controller else #[]
              let itemKind := (tokenSpecOfCardDef? b.printed).getD kind
              EnteringAttackItem.token b.controller itemKind b.tapped opts (some b.printed.name)
            g.promptEnteringAttackItems items (cause := cause)

/-- Run `applyConnive` across `ids` sequentially, pausing and chaining
`.continueConnives` if a step opens a pending choice or `--norandom` request. -/
partial def runConniveObjects (g : Game) (controller : PlayerId)
    (ids : Array ObjectId) : Game :=
  match ids[0]? with
  | none => g
  | some id =>
    let rest := ids.extract 1 ids.size
    let g := g.applyConnive controller (some id)
    if rest.isEmpty then g
    else if g.pending != .none || g.afterRandom != .none then
      g.chainPendingReplacement (.continueConnives controller rest)
    else
      g.runConniveObjects controller rest

/-- Resolve a triggered ability through the unified `Instruction` interpreter
(`Interpreter.applyUnifiedAbility`, CR 603 / 608). -/
def applyTriggeredAbility (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target := #[])
    (dividedDamage : Array Nat := #[])
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none)
    (_sourceName : String := "") : Game :=
  if ab.optionalOnceEachTurn && sourceId.any g.optionalOnceUsedThisTurn then
    g.logMsg "The optional ability was already chosen this turn. This instance has no effect."
  else if ab.interveningIf?.isSome &&
      !g.triggerInterveningHolds controller ab sourceId targets lastKnownPower
        (g.resolvingAbilityObject?.bind (·.fraCauseId))
        (g.resolvingAbilityObject?.bind (·.fraCauseStatus)) then
    if ab.effect.body == Effect.resourceDrawIfAnotherHeroDamage.body then
      g.logMsg "Human Torch's ability has no effect"
    else if ab.effect.body == Effect.thisAttackIfArtifactEnteredDraw.body then
      g.logMsg "No artifact entered under your control this turn. Iron Man's ability doesn't trigger."
    else if ab.effect.body == Effect.stepDrawToTen.body then
      g.logMsg "You already have ten or more cards in hand"
    else if ab.effect.body == Effect.thisAttackEquippedDrain.body then
      g.logMsg s!"{g.fraSourceName sourceId} isn't equipped"
    else g
  else
    let chosenX := g.resolvingAbility.bind g.chosenXOf? <|> sourceId.bind g.chosenXOf?
    let run (g : Game) : Game :=
      g.applyUnifiedAbility controller ab.effect targets sourceId lastKnownPower
        (chosenX := chosenX) (lastKnownToughness := lastKnownToughness)
    if g.resolvingDivision.isEmpty && !dividedDamage.isEmpty then
      g.withContinuationFrame fun g =>
        let g := g.change (.resolvingDivision dividedDamage)
        run g
    else
      run g

/-- Dispatch an Alliance, Gollum, or Vision mode choice via `fallback`. -/
def answerChooseMode (g : Game) (_sourceId : ObjectId) (_idx : Nat)
    (fallback : Game → Game) : Game :=
  fallback g

end Game
end Mtg.Engine
