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

/-- Loyalty counters among Jace planeswalkers `p` controls. -/
def jaceLoyaltyAmong (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).foldl (fun acc o =>
    if g.isPlaneswalker o && g.hasSubtype o .jace then acc + o.status.loyaltyCounters
    else acc) 0

/-- Whether a Reality Fracture “Activate only if …” condition holds. -/
def fraActivationConditionHolds (g : Game) (p : PlayerId) : FraActivationCondition → Bool
  | .none => true
  | .scriedOrSurveilledThisTurn =>
    g.loggedScried p || g.loggedSurveilled p
  | .graveyardAtLeast n => (g.player p).graveyard.size ≥ n
  | .jaceLoyaltyAtLeast n => g.jaceLoyaltyAmong p ≥ n

/-- Whether `p` can pay the Reality Fracture part of `o`'s activation cost. -/
def canPayFraCost (g : Game) (p : PlayerId) (o : GameObject) (ab : ActivatedAbility) : Bool :=
  let sacOrExileSrc := ab.cost.sacrificeSource || ab.cost.fra == .exileSource
  let discOrExileHandSrc := ab.cost.discardSource || ab.cost.fra == .exileSourceFromHand
  match ab.cost.fra with
  | .none => true
  | .exileAnotherCreatureCardFromGraveyard | .sacrificeAnotherArtifact
  | .sacrificeAnotherCreatureOrPlaneswalker | .sacrificeArtifactOrLand
  | .discardLegendaryCard | .tapTwoUntappedArtifacts =>
    g.costPicksPayable p (some o.id) (costPicksOf ab)
      (tapSource := ab.cost.tap)
      (sacrificeOrExileSource := sacOrExileSrc)
      (discardOrExileHandSource := discOrExileHandSrc)
  | .exileSourceFromHand => o.zone == .hand o.owner
  | .exileSource => o.isOnBattlefield
  | .zemoBoast =>
    let col := TextChange.applyColor (g.evalLayer3 o) .black
    g.canPayZemoBoast p ((g.player p).graveyard.filter (fun id =>
      (g.findObject? id).any (fun card => (g.colors card).contains col))) col
  | .crew n =>
    ((g.creaturesControlledBy p).filter (fun c => c.id != o.id && !c.status.tapped)).foldl
      (fun acc c => acc + (g.power c).toNat) 0 ≥ n

/-- Shared activation legality (CR 602.5a / 602.5d). `canActivate` is this check as a
`Bool`; `activateAbility` reports the first failing reason. -/
def validateActivation (g : Game) (p : PlayerId) (o : GameObject) (ab : ActivatedAbility) :
    Except String Unit := do
  if !g.hasPriority p then
    throw "You don't have priority"
  if (g.manaAbilityDefs o).any (fun d =>
      d.activatedIdx.isSome && d.activatedIdx == (g.activatedAbilitiesOf o).findIdx? (· == ab)) then
    throw s!"{g.name o}'s ability is a mana ability (CR 605)"
  if g.splitSecondOnStack && !isManaActivation ab then
    throw "A spell with split second is on the stack (CR 702.61a)"
  if ab.activateFromGraveyard then
    if !(o.zone == .graveyard o.owner && o.owner == p) then
      throw s!"{g.name o}'s ability can be activated only from the graveyard"
  else if ab.activateFromHand then
    if !(o.zone == .hand o.owner && o.owner == p) then
      throw s!"{g.name o}'s ability can be activated only from your hand"
  else
    if !o.isOnBattlefield then
      throw s!"{g.name o} is not on the battlefield"
    if !g.controlledBy o p then
      throw "You don't control that permanent"
  if ab.onlyIfYouControlLegendary && !g.controlsLegendaryCreature p then
    throw s!"{g.name o}'s ability can be activated only if you control a legendary creature"
  if ab.onlyIfYouAttackedWithTwoOrMore && g.loggedAttacks p < 2 then
    throw s!"{g.name o}'s ability can be activated only if you attacked with two or more creatures this turn"
  if ab.onlyIfOpponentDealtNoncombatDamage &&
      !g.players.any (fun q => q.id != p && !g.areTeammates p q.id && g.loggedNoncombatDamage q.id) then
    throw s!"{g.name o}'s ability can be activated only if an opponent has been dealt noncombat damage this turn"
  if ab.onlyAsSorcery && !g.asSorcery? p then
    throw s!"{g.name o}'s ability can be activated only as a sorcery"
  if ab.exhaust && g.exhaustUsed o.id then
    throw s!"{g.name o}'s exhaust ability can be activated only once (CR 702.177)"
  if !g.fraActivationConditionHolds p ab.fraCondition then
    throw s!"{g.name o}'s ability can't be activated now (its \"Activate only if\" condition isn't met)"
  if ab.cost.fra == .zemoBoast && !g.canActivateBoast o then
    throw s!"{g.name o}'s boast ability can be activated only if it attacked this turn and only once each turn"
  if !g.canPayFraCost p o ab then
    throw s!"{g.name o}'s ability has a cost that can't be paid"
  if g.combatLocksNonManaAbilities && !isManaActivation ab then
    throw "During combat, players can't activate abilities that aren't mana abilities (Yuriko)"
  match ab.cost.loyalty with
  | none => pure ()
  | some sym =>
    -- CR 606.3: once per turn per permanent, and only as a sorcery unless an
    -- effect such as Jace's Machinations allows otherwise.
    if g.loyaltyActivatedThisTurn o.id then
      throw s!"A loyalty ability of {g.name o} has already been activated this turn (CR 606.3)"
    if !g.asSorcery? p && !g.mayActivateLoyaltyAtInstantSpeed p o then
      throw s!"{g.name o}'s loyalty abilities can be activated only as a sorcery (CR 606.3)"
    match sym.counters with
    | some k =>
      if k < 0 && (o.status.loyaltyCounters : Int) < -k then
        throw s!"{g.name o} doesn't have {-k} loyalty counters to remove (CR 606.4)"
    | none =>
      if sym != .minusX && sym != .plusX then
        throw s!"{g.name o}'s X loyalty cost is not supported"
  if ab.onlyDuringYourTurn && !g.isOnActiveTeam p then
    throw s!"{g.name o}'s ability can be activated only during your turn"
  if ab.onceEachTurn &&
      (match (g.activatedAbilitiesOf o).findIdx? (· == ab) with
       | some i => (g.abilitiesActivatedThisTurn o.id).contains i
       | none => g.activationsThisTurn o.id != 0) then
    throw s!"{g.name o}'s ability can be activated only once each turn"
  if ab.powerUp && g.powerUpsForbidden then
    throw s!"Power-up abilities can't be activated during this extra turn"
  if ab.powerUp &&
      (Nat.max (g.powerUpActivations o.id) (if g.powerUpUsed o.id then 1 else 0)) ≥
        g.powerUpActivationLimit p then
    throw s!"{g.name o}'s power-up ability can be activated only once"
  if ab.cost.tap && o.status.tapped then
    throw s!"{g.name o} is already tapped"
  if ab.cost.tap && g.hasSummoningSickness o && !(g.isCreature o && g.activatesAsThoughHaste p) then
    throw s!"{g.name o} has summoning sickness (CR 302.6)"
  if ab.cost.sacrificeAnotherCreatureOrArtifact &&
      (g.sacrificeCreatureOrArtifactChoices p o.id).isEmpty then
    throw s!"{g.name o}'s ability requires sacrificing another creature or artifact"
  if !g.costPicksPayable p (some o.id) (costPicksOf ab)
      (tapSource := ab.cost.tap)
      (sacrificeOrExileSource := ab.cost.sacrificeSource || ab.cost.fra == .exileSource)
      (discardOrExileHandSource := ab.cost.discardSource || ab.cost.fra == .exileSourceFromHand) then
    throw s!"{g.name o}'s ability has a cost that can't be paid"
  if ab.cost.removeAnyNumberPlusOne && ab.cost.tap && o.status.tapped then
    throw s!"{g.name o} is already tapped"
  if !g.canPayLife p ab.cost.payLife then
    throw s!"{(g.player p).name} cannot pay {ab.cost.payLife} life"
  if ab.onlyIfYouControlCreatureToughnessAtLeast != 0 &&
      !(g.permanentsOf p).any (fun x =>
        g.isCreature x && g.toughness x >= (ab.onlyIfYouControlCreatureToughnessAtLeast : Int)) then
    throw s!"{g.name o}'s ability can be activated only if you control a creature with toughness {ab.onlyIfYouControlCreatureToughnessAtLeast} or greater"
  if ab.onlyIfGyCreaturesAtLeast != 0 then
    let gy :=
      (g.player p).graveyard.filter (fun id =>
        match g.findObject? id with
        | some c => g.isCreature c
        | none => false) |>.size
    if gy < ab.onlyIfGyCreaturesAtLeast then
      throw s!"{g.name o}'s ability can be activated only if there are {ab.onlyIfGyCreaturesAtLeast} or more creature cards in your graveyard"
  if !g.abilityCanChooseTarget p ab (sourceId := some o.id) then
    throw s!"{g.name o}'s ability requires a target"

/-- Whether `p` may begin activating `ab` of `o` (CR 602.5). Having
enough mana in the pool is not required; mana abilities are activated at
CR 601.2g. Cycling and other hand abilities use `activateFromHand` (CR 702.29).
Turning a face-down Morph permanent face up is a CR 116.2b / 702.37e special
action rather than an activated ability (so Split Second does not forbid it,
CR 702.61b). -/
def canActivate (g : Game) (p : PlayerId) (o : GameObject) (ab : ActivatedAbility) : Bool :=
  if o.status.faceDown && ab.effect.resolution == .frc .turnFaceUp then
    g.hasPriority p && o.isOnBattlefield && g.controlledBy o p &&
      (g.unmaskedCopiableValues o).morph.isSome
  else
    (g.validateActivation p o ab).isOk

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
  if o.status.faceDown && ab.effect.resolution == .frc .turnFaceUp then
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
        let g := g.change .clearProposalCheckpoint
        let pre := g
        let g := g.record
          (GameEvent.turnedFaceUp g.turnNumber (g.snapshot (g.object! o.id))
            (cause := .specialAction .turnFaceUp p))
        let objName := (g.findObject? o.id).map g.name |>.getD (g.name o)
        let g := g.logMsg s!"{pl.name} turns {objName} face up"
        let g :=
          (reconcileControlAfterTransition pre g (cause := some (.specialAction .turnFaceUp p)))
            |>.flushQueuedLinkedExile
        return g.receivePriority p
    | none => throw s!"{g.name o} is face down"
  let defs := g.manaAbilityDefs o
  if let some i := (List.range defs.size).find? (fun i => defs[i]!.activatedIdx == some abilityIdx) then
    -- A mana ability doesn't use the stack (CR 605.3b).
    let d := defs[i]!
    match d.output, d.picks.isEmpty with
    | .fixed m, true => return (← g.activateManaAbility p id i m)
    | _, _ =>
      throw s!"{g.name o}'s ability is a mana ability: choose the mana it adds and what pays its cost (CR 605.3)"
  if !g.hasPriority p then
    throw "You don't have priority"
  g.validateActivation p o ab
  let loyaltyX := ab.cost.loyalty == some .minusX || ab.cost.loyalty == some .plusX
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
    targetKindOverride :=
      if effect.targetKind != ab.effect.targetKind then some effect.targetKind else none
    activation := some ab
    loyaltyX
    removePlusOneX := ab.cost.removeAnyNumberPlusOne
  }
  if ab.cost.fra == .zemoBoast then
    return (g.changes #[
      .proposedSpell (some prop),
      .pending (.fraChoice p (.zemoBoastExile newId id))]).logMsg
      s!"{pl.name} chooses black cards to exile from their graveyard"
  if let .crew n := ab.cost.fra then
    return (g.changes #[
      .proposedSpell (some prop),
      .pending (.fraChoice p (.crew newId id n))]).logMsg
      s!"{pl.name} chooses untapped creatures with total power {n} or more to crew {g.name o}"
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
