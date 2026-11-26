import Mtg.Engine.Game.CastSpell

/-!
# Activating abilities (CR 602)

Activation legality — timing, zones, once-each-turn limits, boast — and
`activateAbility`.
-/

namespace Mtg.Engine
namespace Game

/-- Jace's Machinations lets `p` activate loyalty abilities of Jace
planeswalkers they control any time they could cast an instant. -/
def mayActivateLoyaltyAtInstantSpeed (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  g.jaceLoyaltyAtInstantSpeed p && g.isPlaneswalker o && g.hasSubtype o .jace

/-- Whether `p` can pay the non-mana zone/crew/boast/pick part of `o`'s activation cost. -/
def canPayActivationNonManaCost (g : Game) (p : PlayerId) (o : GameObject) (ab : ActivatedAbility) : Bool :=
  let sacOrExileSrc := ab.cost.sacrificeSource || ab.cost.exileSourceFromBattlefield
  let discOrExileHandSrc := ab.cost.discardSource || ab.cost.exileSourceFromHand
  let allPicks := costPicksWithSacrificeOther (costPicksOf ab) ab.cost.sacrificeAnotherCreatureOrArtifact
  let handOk :=
    (!ab.cost.exileSourceFromHand || (o.zone == .hand o.owner && isDiscardableCard o)) &&
      (!ab.cost.discardSource || (o.zone == .hand o.owner && isDiscardableCard o))
  let bfOk := !ab.cost.exileSourceFromBattlefield || o.isOnBattlefield
  let zemoOk :=
    ab.cost.exileManaSymbols?.isNone ||
      (o.isOnBattlefield &&
        let col := TextChange.applyColor (g.evalLayer3 o) .black
        g.canPayZemoBoast p ((g.player p).graveyard.filter (fun id =>
          (g.findObject? id).any (fun card => isDiscardableCard card && (g.colors card).contains col))) col)
  let crewOrPicksOk :=
    match ab.cost.crewPower? with
    | some n =>
      o.isOnBattlefield &&
        (g.firstPayableCrewSelection? p o.id n allPicks
          (tapSource := ab.cost.tap)
          (sacrificeOrExileSource := sacOrExileSrc)
          (discardOrExileHandSource := discOrExileHandSrc)).isSome
    | none =>
      allPicks.isEmpty ||
        g.costPicksPayable p (some o.id) allPicks
          (tapSource := ab.cost.tap)
          (sacrificeOrExileSource := sacOrExileSrc)
          (discardOrExileHandSource := discOrExileHandSrc)
  handOk && bfOk && zemoOk && crewOrPicksOk

/-- Shared activation legality (CR 602.5a / 602.5d). `canActivate` is this check as a
`Bool`; `activateAbility` reports the first failing reason. -/
def validateActivation (g : Game) (p : PlayerId) (o : GameObject) (ab : ActivatedAbility)
    (idx? : Option Nat := none) :
    Except String Unit := do
  if !g.hasPriority p then
    throw "You don't have priority"
  let resolvedIdx? := idx?.orElse (fun _ => (g.activatedAbilitiesOf o).findIdx? (· == ab))
  if (g.manaAbilityDefs o).any (fun d =>
      d.activatedIdx.isSome && d.activatedIdx == resolvedIdx?) then
    throw s!"{g.name o}'s ability is a mana ability (CR 605)"
  if g.splitSecondOnStack && !isManaActivation ab then
    throw "A spell with split second is on the stack (CR 702.61a)"
  let fromGy := ab.isFromGraveyard
  let fromHand := ab.isFromHand
  if fromGy && fromHand then
    throw s!"{g.name o}'s ability has conflicting hand and graveyard activation zones"
  if (fromGy || fromHand) && ab.needsBattlefieldSource then
    throw s!"{g.name o}'s ability has a battlefield cost that can't be paid from that zone"
  if fromGy then
    if !(o.zone == .graveyard o.owner && o.owner == p && isDiscardableCard o) then
      throw s!"{g.name o}'s ability can be activated only from the graveyard"
  else if fromHand then
    if !(o.zone == .hand o.owner && o.owner == p && isDiscardableCard o) then
      throw s!"{g.name o}'s ability can be activated only from your hand"
  else
    if !o.isOnBattlefield then
      throw s!"{g.name o} is not on the battlefield"
    if !g.controlledBy o p then
      throw "You don't control that permanent"
  match ab.timing with
  | .sorcery =>
    if !g.asSorcery? p then
      throw s!"{g.name o}'s ability can be activated only as a sorcery"
  | .loyalty | .instant => pure ()
  if ab.isBoast || ab.cost.exileManaSymbols?.isSome then
    let boastUsed :=
      match resolvedIdx? with
      | some i => g.abilityActivationsThisTurn o.id i (isBoast := true) > 0
      | none => g.boastUsedThisTurn o.id
    if !g.declaredAsAttackerThisTurn o.id || boastUsed then
      throw s!"{g.name o}'s boast ability can be activated only if it attacked this turn and only once each turn"
  if let some cond := ab.condition? then
    if !EvalExpr.evalActivationCondition g p o.id (some cond) then
      if cond == .isYourTurn then
        throw s!"{g.name o}'s ability can be activated only during your turn"
      else
        throw s!"{g.name o}'s ability can be activated only if {ToOracle.toOracle { capitalize := false } cond}"
  if let some lim := ab.turnLimit? then
    let used :=
      match resolvedIdx? with
      | some i => g.abilityActivationsThisTurn o.id i (isBoast := ab.isBoast)
      | none => g.activationsThisTurn o.id
    if used ≥ lim then
      if ab.isBoast then
        throw s!"{g.name o}'s boast ability can be activated only if it attacked this turn and only once each turn"
      else if lim == 1 then
        throw s!"{g.name o}'s ability can be activated only once each turn"
      else
        throw s!"{g.name o}'s ability can be activated no more than {lim} times each turn"
  if ab.isPowerUp && g.powerUpsForbidden then
    throw "Power-up abilities can't be activated during this extra turn"
  if let some lim := ab.lifetimeLimit? then
    let effLim := if ab.isPowerUp then g.powerUpActivationLimit p else lim
    let used :=
      match resolvedIdx? with
      | some i => g.abilityActivationsSinceEntered o.id i (isPowerUp := ab.isPowerUp) (isExhaust := ab.isExhaust)
      | none =>
        if ab.isPowerUp then Nat.max (g.powerUpActivations o.id) (if g.powerUpUsed o.id then 1 else 0)
        else if ab.isExhaust && g.exhaustUsed o.id then 1
        else 0
    if used ≥ effLim then
      if ab.isExhaust then
        throw s!"{g.name o}'s exhaust ability can be activated only once (CR 702.177)"
      else if ab.isPowerUp then
        throw s!"{g.name o}'s power-up ability can be activated only once"
      else
        throw s!"{g.name o}'s ability can be activated only once"
  if !g.canPayActivationNonManaCost p o ab then
    throw s!"{g.name o}'s ability has a cost that can't be paid"
  if g.combatLocksNonManaAbilities && !isManaActivation ab then
    throw "During combat, players can't activate abilities that aren't mana abilities (Yuriko)"
  if ab.isLoyaltyAbility then
    -- CR 606.3 / 606.5 / 606.6: once per turn per permanent, and only as a sorcery
    -- unless an effect such as Jace's Machinations allows otherwise.
    if g.loyaltyActivatedThisTurn o.id then
      throw s!"A loyalty ability of {g.name o} has already been activated this turn (CR 606.3)"
    if !g.asSorcery? p && !g.mayActivateLoyaltyAtInstantSpeed p o then
      throw s!"{g.name o}'s loyalty abilities can be activated only as a sorcery (CR 606.3)"
    let hasLoyaltyX := ab.cost.loyaltySymbols.any fun
      | .minusX | .plusX => true
      | _ => false
    if !hasLoyaltyX then
      if let some k := ab.cost.netLoyaltyDelta 0 then
        if k < 0 && (o.status.loyaltyCounters : Int) < -k then
          throw s!"{g.name o} doesn't have {-k} loyalty counters to remove (CR 606.4)"
  if ab.cost.tap && o.status.tapped then
    throw s!"{g.name o} is already tapped"
  if ab.cost.tap && g.hasSummoningSickness o && !(g.isCreature o && g.activatesAsThoughHaste p) then
    throw s!"{g.name o} has summoning sickness (CR 302.6)"
  if ab.cost.sacrificeAnotherCreatureOrArtifact &&
      (g.sacrificeCreatureOrArtifactChoices p o.id).isEmpty then
    throw s!"{g.name o}'s ability requires sacrificing another creature or artifact"
  let allPicks := costPicksWithSacrificeOther (costPicksOf ab) ab.cost.sacrificeAnotherCreatureOrArtifact
  if !g.costPicksPayable p (some o.id) allPicks
      (tapSource := ab.cost.tap)
      (sacrificeOrExileSource := ab.cost.sacrificeSource || ab.cost.exileSourceFromBattlefield)
      (discardOrExileHandSource := ab.cost.discardSource || ab.cost.exileSourceFromHand) then
    throw s!"{g.name o}'s ability has a cost that can't be paid"
  if ab.cost.removeStoryCounter && o.status.story == 0 then
    throw s!"{g.name o} doesn't have a story counter to remove"
  if ab.cost.removeIndestructibleCounter && o.status.indestructibleCounters == 0 then
    throw s!"{g.name o} doesn't have an indestructible counter to remove"
  if ab.cost.removeAnyNumberPlusOne && ab.cost.tap && o.status.tapped then
    throw s!"{g.name o} is already tapped"
  if !g.canPayLife p ab.cost.payLife then
    throw s!"{(g.player p).name} cannot pay {ab.cost.payLife} life"
  if !g.abilityCanChooseTarget p ab (sourceId := some o.id) then
    throw s!"{g.name o}'s ability requires a target"

/-- Whether `p` may begin activating `ab` of `o` (CR 602.5). Having
enough mana in the pool is not required; mana abilities are activated at
CR 601.2g. Cycling and other hand abilities use `activeZones := #[.hand]` (CR 702.29).
Turning a face-down Morph permanent face up is a CR 116.2b / 702.37e special
action rather than an activated ability (so Split Second does not forbid it,
CR 702.61b). -/
def canActivate (g : Game) (p : PlayerId) (o : GameObject) (ab : ActivatedAbility)
    (idx? : Option Nat := none) : Bool :=
  if o.status.faceDown && ab.isTurnFaceUp then
    g.hasPriority p && o.isOnBattlefield && g.controlledBy o p &&
      (g.unmaskedCopiableValues o).morph.isSome
  else
    (g.validateActivation p o ab (idx? := idx?)).isOk

def activateAbility (g : Game) (p : PlayerId) (id : ObjectId) (abilityIdx : Nat) :
    Except String Game := do
  let some o := g.findObject? id | throw "no such object"
  let abs := g.activatedAbilitiesOf o
  if abs.isEmpty then
    if o.status.faceDown then
      throw s!"{g.name o} is face down"
    throw s!"{g.name o} has no activated ability"
  let some ab := abs[abilityIdx]?
    | throw s!"{g.name o} has no such activated ability"
  if o.status.faceDown && ab.isTurnFaceUp then
    if !g.hasPriority p then
      throw "You don't have priority"
    if !o.isOnBattlefield then
      throw s!"{g.name o} is not on the battlefield"
    if !g.controlledBy o p then
      throw "You don't control that permanent"
    match (g.unmaskedCopiableValues o).morph with
    | some cost =>
      let pl := g.player p
      let g := g.changes #[.saveProposalCheckpoint, .consecutivePasses 0]
      if cost.includesManaPayment then
        let prop : ProposedSpell := {
          caster := p
          cost
          spellId := o.id
          sourceId := some o.id
          original := o
          originalSnapshot := g.snapshot o
          kind := .turnFaceUp
        }
        let g := g.changes #[.pending (.activateManaAbilities p), .proposedSpell (some prop)]
        return g.logMsg s!"{pl.name} may activate mana abilities to turn {g.name o} face up (CR 601.2g / 702.37e)"
      else
        let localOuter? := g.pendingReplacement
        let g0 := if localOuter?.isSome then g.change (.pendingReplacement none) else g
        let paused0 := match g0.pending with | .chooseReplacement .. => true | _ => false
        let willReverse := !paused0 && !g0.over && g0.proposedSpell.isSome && g0.proposalCheckpoint.isSome &&
          !(g0.stillInGame p &&
            (g0.findObject? o.id).any (fun cur =>
              cur.isOnBattlefield && cur.status.faceDown && g0.controlledBy cur p))
        let (g, callerShouldResume) :=
          g0.completeTurnFaceUp p o.id (hadOuterReplacement := localOuter?.isSome)
        let g :=
          if willReverse then g
          else
            match localOuter? with
            | some outer => g.chainProposalOuterCont p outer
            | none => g
        return if !willReverse && (callerShouldResume || (!g.over && g.pending == .none && localOuter?.isSome)) then
          g.resumeAfterBecomeCastFwd
        else g
    | none => throw s!"{g.name o} is face down"
  let defs := g.manaAbilityDefs o
  if let some i := (List.range defs.size).find? (fun i => defs[i]!.activatedIdx == some abilityIdx) then
    -- A mana ability doesn't use the stack (CR 605.3b).
    let d := defs[i]!
    if d.picks.isEmpty && !d.hasExtraInteractiveCost && d.modeChoices.isEmpty then
      if let .fixed m := d.output then
        return (← g.activateManaAbility p id i m)
    throw s!"{g.name o}'s ability is a mana ability: choose the mana it adds and what pays its cost (CR 605.3)"
  if !g.hasPriority p then
    throw "You don't have priority"
  g.validateActivation p o ab (idx? := some abilityIdx)
  let loyaltyX := ab.cost.loyaltySymbols.any fun
    | .minusX | .plusX => true
    | _ => false
  let o := g.object! id
  let origSnap := g.snapshot o
  let pl := g.player p
  let effect := g.expandEachOpponentEffect p ab.effect
  let g := g.change .saveProposalCheckpoint
  let (g, abilityObj) := g.putStackAbility o p
    (abilityEffect := if ab.isModal then none else some effect)
  let newId := abilityObj.id
  let g := g.logMsg s!"{pl.name} begins activating {g.name o}"
  let manaCost := g.activationManaCost p ab (some o)
  let prop : ProposedSpell := {
    caster := p
    cost := manaCost
    spellId := newId
    original := o
    originalSnapshot := origSnap
    kind := .activatedAbility
    sourceId := some id
    tapSource := ab.cost.tap
    sacrificeSource := ab.cost.sacrificeSource
    needsSacrificeOther := ab.cost.sacrificeAnotherCreatureOrArtifact
    payLife := ab.cost.payLife
    discardSource := ab.cost.discardSource
    abilityModes := ab.allModes
    targetSpecOverride :=
      if effect.targetSpec != ab.effect.targetSpec then some effect.targetSpec else none
    activation := some ab
    abilityIdx := some abilityIdx
    loyaltyX
    removePlusOneX := ab.cost.removeAnyNumberPlusOne
  }
  if !ab.isModal && !effect.requiresTarget && !loyaltyX &&
      !ab.cost.removeAnyNumberPlusOne &&
      !manaCost.includesManaPayment && !manaCost.containsX &&
      !ab.cost.sacrificeAnotherCreatureOrArtifact then
    let g := g.change (.proposedSpell (some prop))
    return (← g.beginActivationPayment prop)
  if loyaltyX || ab.cost.removeAnyNumberPlusOne then
    let g := g.changes #[.pending (.chooseX p), .proposedSpell (some prop)]
    return g.logMsg s!"{pl.name} must choose a value for X (CR 107.3a / 601.2b)"
  return g.enterProposalWindow p pl prop ab.isModal effect.requiresTarget "CR 601.2b"

end Game
end Mtg.Engine
