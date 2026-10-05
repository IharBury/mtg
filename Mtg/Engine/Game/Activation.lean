import Mtg.Engine.Game.CastSpell

/-!
# Activating abilities (CR 602)

Activation legality — timing, zones, once-each-turn limits, boast — and
`activateAbility`.
-/

namespace Mtg.Engine
namespace Game

/-- Shang-Chi: activate tap abilities as though creatures had haste
(MSH 280). Does not grant haste and does not allow attacking. -/
def activatesAsThoughHaste (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o =>
    o.staticAbilities.any (fun
      | .activateCreaturesAsThoughHaste => true
      | _ => false))

/-- Jace's Machinations lets `p` activate loyalty abilities of Jace
planeswalkers they control any time they could cast an instant. -/
def mayActivateLoyaltyAtInstantSpeed (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  (g.player p).jaceLoyaltyAtInstantSpeed && o.printed.isPlaneswalker && o.hasSubtype "Jace"

/-- Loyalty counters among Jace planeswalkers `p` controls. -/
def jaceLoyaltyAmong (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).foldl (fun acc o =>
    if o.printed.isPlaneswalker && g.hasSubtype o "Jace" then acc + o.status.loyaltyCounters
    else acc) 0

/-- Whether a Reality Fracture “Activate only if …” condition holds. -/
def fraActivationConditionHolds (g : Game) (p : PlayerId) : FraActivationCondition → Bool
  | .none => true
  | .scriedOrSurveilledThisTurn => (g.player p).scriedOrSurveilledThisTurn
  | .graveyardAtLeast n => (g.player p).graveyard.size ≥ n
  | .jaceLoyaltyAtLeast n => g.jaceLoyaltyAmong p ≥ n

/-- Whether `p` can pay the Reality Fracture part of `o`'s activation cost. -/
def canPayFraCost (g : Game) (p : PlayerId) (o : GameObject) : FraCost → Bool
  | .none => true
  | .exileAnotherCreatureCardFromGraveyard =>
    (g.player p).graveyard.any (fun id =>
      id != o.id && (g.findObject? id).any (·.printed.isCreature))
  | .sacrificeAnotherArtifact =>
    (g.permanentsOf p).any (fun x => x.id != o.id && x.printed.isArtifact)
  | .sacrificeAnotherCreatureOrPlaneswalker =>
    (g.permanentsOf p).any (fun x => x.id != o.id && (x.isCreature || x.printed.isPlaneswalker))
  | .sacrificeArtifactOrLand =>
    (g.permanentsOf p).any (fun x => x.printed.isArtifact || x.printed.isLand)
  | .discardLegendaryCard =>
    (g.player p).hand.any (fun id => (g.findObject? id).any (·.isLegendary))
  | .tapTwoUntappedArtifacts =>
    ((g.permanentsOf p).filter (fun x => x.printed.isArtifact && !x.status.tapped)).size ≥ 2
  | .exileSourceFromHand => o.zone == .hand o.owner
  | .exileSource => o.isOnBattlefield
  | .crew n =>
    ((g.creaturesControlledBy p).filter (fun c => c.id != o.id && !c.status.tapped)).foldl
      (fun acc c => acc + (g.power c).toNat) 0 ≥ n

/-- “For each opponent, up to one target … that player controls” as one
optional target slot per opponent (CR 601.2c). -/
def expandEachOpponentEffect (g : Game) (p : PlayerId) (e : Effect) : Effect :=
  match e.targetKind with
  | .filtered f =>
    if f.controller == .eachOpponent then
      let fs := (g.livingOpponents p).map (fun pl => { f with controller := .specific pl.id.idx })
      { e with targeting := .of (.multi fs ((List.range fs.size).toArray)) }
    else e
  | _ => e

/-- Shared activation legality (CR 602.3). `canActivate` is this check as a
`Bool`; `activateAbility` reports the first failing reason. -/
def validateActivation (g : Game) (p : PlayerId) (o : GameObject) (ab : ActivatedAbility) :
    Except String Unit := do
  if !g.hasPriority p then
    throw "You don't have priority"
  if g.splitSecondOnStack && !isManaActivation ab then
    throw "A spell with split second is on the stack (CR 702.61a)"
  if ab.activateFromGraveyard then
    if !(o.zone == .graveyard o.owner && o.owner == p) then
      throw s!"{o.name}'s ability can be activated only from the graveyard"
  else if ab.activateFromHand then
    if !(o.zone == .hand o.owner && o.owner == p) then
      throw s!"{o.name}'s ability can be activated only from your hand"
  else
    if !o.isOnBattlefield then
      throw s!"{o.name} is not on the battlefield"
    if !o.controlledBy p then
      throw "You don't control that permanent"
  if ab.onlyIfYouControlLegendary && !g.controlsLegendaryCreature p then
    throw s!"{o.name}'s ability can be activated only if you control a legendary creature"
  if ab.onlyIfYouAttackedWithTwoOrMore &&
      (g.battlefield.filter (fun x =>
        x.isCreature && x.controlledBy p && x.status.attacking)).size < 2 then
    throw s!"{o.name}'s ability can be activated only if you attacked with two or more creatures this turn"
  if ab.onlyIfOpponentDealtNoncombatDamage &&
      !(g.livingOpponents p).any (·.dealtNoncombatDamageThisTurn) then
    throw s!"{o.name}'s ability can be activated only if an opponent has been dealt noncombat damage this turn"
  if ab.onlyAsSorcery && !g.asSorcery? p then
    throw s!"{o.name}'s ability can be activated only as a sorcery"
  if ab.exhaust && o.status.exhaustUsed then
    throw s!"{o.name}'s exhaust ability can be activated only once (CR 702.177)"
  if !g.fraActivationConditionHolds p ab.fraCondition then
    throw s!"{o.name}'s ability can't be activated now (its \"Activate only if\" condition isn't met)"
  if !g.canPayFraCost p o ab.cost.fra then
    throw s!"{o.name}'s ability has a cost that can't be paid"
  if g.combatLocksNonManaAbilities && !isManaActivation ab then
    throw "During combat, players can't activate abilities that aren't mana abilities (Yuriko)"
  match ab.cost.loyalty with
  | none => pure ()
  | some sym =>
    -- CR 606.3: once per turn per permanent, and only as a sorcery unless an
    -- effect such as Jace's Machinations allows otherwise.
    if o.status.loyaltyActivatedThisTurn then
      throw s!"A loyalty ability of {o.name} has already been activated this turn (CR 606.3)"
    if !g.asSorcery? p && !g.mayActivateLoyaltyAtInstantSpeed p o then
      throw s!"{o.name}'s loyalty abilities can be activated only as a sorcery (CR 606.3)"
    match sym.counters with
    | some k =>
      if k < 0 && (o.status.loyaltyCounters : Int) < -k then
        throw s!"{o.name} doesn't have {-k} loyalty counters to remove (CR 606.4)"
    | none =>
      if sym != .minusX then throw s!"{o.name}'s X loyalty cost is not supported"
  if ab.onlyDuringYourTurn && g.activePlayer != p then
    throw s!"{o.name}'s ability can be activated only during your turn"
  if ab.onceEachTurn && o.status.activationsThisTurn != 0 then
    throw s!"{o.name}'s ability can be activated only once each turn"
  if ab.powerUp &&
      (Nat.max o.status.powerUpActivations (if o.status.powerUpUsed then 1 else 0)) ≥
        g.powerUpActivationLimit p then
    throw s!"{o.name}'s power-up ability can be activated only once"
  if ab.cost.tap && o.status.tapped then
    throw s!"{o.name} is already tapped"
  if ab.cost.tap && o.hasSummoningSickness && !g.activatesAsThoughHaste p && !g.hasHaste o then
    throw s!"{o.name} has summoning sickness (CR 302.6)"
  if ab.cost.sacrificeAnotherCreatureOrArtifact &&
      (g.sacrificeCreatureOrArtifactChoices p o.id).isEmpty then
    throw s!"{o.name}'s ability requires sacrificing another creature or artifact"
  if !g.canPayLife p ab.cost.payLife then
    throw s!"{(g.player p).name} cannot pay {ab.cost.payLife} life"
  if ab.onlyIfYouControlCreatureToughnessAtLeast != 0 &&
      !(g.permanentsOf p).any (fun x =>
        x.isCreature && g.toughness x >= (ab.onlyIfYouControlCreatureToughnessAtLeast : Int)) then
    throw s!"{o.name}'s ability can be activated only if you control a creature with toughness {ab.onlyIfYouControlCreatureToughnessAtLeast} or greater"
  if ab.onlyIfGyCreaturesAtLeast != 0 then
    let gy :=
      (g.player p).graveyard.filter (fun id =>
        match g.findObject? id with
        | some c => c.printed.isCreature
        | none => false) |>.size
    if gy < ab.onlyIfGyCreaturesAtLeast then
      throw s!"{o.name}'s ability can be activated only if there are {ab.onlyIfGyCreaturesAtLeast} or more creature cards in your graveyard"
  if !g.abilityCanChooseTarget p ab then
    throw s!"{o.name}'s ability requires a target"

/-- Whether `p` may begin activating `ab` of `o` (CR 602.3). Having
enough mana in the pool is not required; mana abilities are activated at
CR 601.2g. Cycling and other hand abilities use `activateFromHand` (CR 702.29). -/
def canActivate (g : Game) (p : PlayerId) (o : GameObject) (ab : ActivatedAbility) : Bool :=
  (g.validateActivation p o ab).isOk

def activateAbility (g : Game) (p : PlayerId) (id : ObjectId) (abilityIdx : Nat) :
    Except String Game := do
  if !g.hasPriority p then
    throw "You don't have priority"
  let some o := g.findObject? id | throw "no such object"
  let abs := g.activatedAbilitiesOf o
  if abs.isEmpty then
    throw s!"{o.name} has no activated ability"
  let some ab := abs[abilityIdx]?
    | throw s!"{o.name} has no such activated ability"
  g.validateActivation p o ab
  let loyaltyX := ab.cost.loyalty == some .minusX
  let g :=
    match ab.cost.loyalty with
    | some sym => if loyaltyX then g else (g.payLoyaltyCost o sym).queueLoyaltyActivationTriggers p sym
    | none => g
  let g :=
    if ab.exhaust then
      let o := g.object! id
      g.setObject { o with status := { o.status with exhaustUsed := true } }
    else g
  let o := g.object! id
  let pl := g.player p
  let stackBefore := g.stack
  let manaBefore := pl.manaPool
  let effect := g.expandEachOpponentEffect p ab.effect
  let (g, abilityObj) := g.putStackAbility o p
    (abilityEffect := if ab.isModal then none else some effect)
  let newId := abilityObj.id
  let g := g.logMsg s!"{pl.name} begins activating {o.name}"
  if let .crew n := ab.cost.fra then
    return { g with pending := .fraChoice p (.crew newId id n) }.logMsg
      s!"{pl.name} chooses untapped creatures with total power {n} or more to crew {o.name}"
  if !ab.isModal && !ab.effect.requiresTarget && !loyaltyX &&
      !ab.cost.mana.includesManaPayment && !ab.cost.mana.containsX &&
      !ab.cost.sacrificeAnotherCreatureOrArtifact then
    let g ← g.payActivationExtraCosts p id ab.cost.tap ab.cost.sacrificeSource
      ab.cost.payLife ab.cost.discardSource (some ab)
    return g.becomeActivated p o.name (some id)
  let manaCost := g.activationManaCost p ab (some o)
  let prop : ProposedSpell := {
    caster := p
    cost := manaCost
    spellId := newId
    original := o
    handBefore := pl.hand
    stackBefore := stackBefore
    manaBefore := manaBefore
    kind := .activatedAbility
    sourceId := some id
    tapSource := ab.cost.tap
    sacrificeSource := ab.cost.sacrificeSource
    needsSacrificeOther := ab.cost.sacrificeAnotherCreatureOrArtifact
    payLife := ab.cost.payLife
    discardSource := ab.cost.discardSource
    abilityModes := ab.allModes
    targetKindOverride :=
      match ab.equipSubtype with
      | some t => some (EffectTargetKind.creatureYouControlSubtype t)
      | none => if effect.targetKind != ab.effect.targetKind then some effect.targetKind else none
    activation := some ab
    loyaltyX
  }
  if loyaltyX then
    let g := { g with pending := .chooseX p, proposedSpell := some prop }
    return g.logMsg s!"{pl.name} must choose a value for X (CR 107.3a / 601.2b)"
  return g.enterProposalWindow p pl prop ab.isModal ab.effect.requiresTarget "CR 601.2b"

end Game
end Mtg.Engine
