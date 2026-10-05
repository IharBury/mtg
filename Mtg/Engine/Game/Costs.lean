import Mtg.Engine.Game.Choices

/-!
# Total costs (CR 601.2f–h)

Finishing a proposed spell or ability, cast cost reductions
(CR 601.2f / 118.7), and activation mana costs including power-up
reductions.
-/

namespace Mtg.Engine
namespace Game

/-- Move `id` to `to`'s hand and log the return. -/
def returnToHand (g : Game) (id : ObjectId) (to : PlayerId) : Game :=
  let name := (g.object! id).name
  let (g, _) := g.move id (.hand to) none
  g.logMsg s!"{name} is returned to {(g.player to).name}'s hand"

/-- Legal only during the declare blockers step of the caster's turn. -/
def canCastForSneak (g : Game) (p : PlayerId) : Bool :=
  g.activePlayer == p && g.step == .declareBlockers

/-- Pay sneak: return an unblocked attacker you control to hand and mark
the spell. The creature enters tapped and attacking the same player. -/
def paySneak (g : Game) (p : PlayerId) (spellId : ObjectId) (attackerId : ObjectId) :
    Except String Game := do
  if !g.canCastForSneak p then
    throw "Sneak can be paid only during the declare blockers step on your turn"
  let some attacker := g.findObject? attackerId | throw "no such object"
  if !(attacker.isOnBattlefield && attacker.isCreature && attacker.controlledBy p) then
    throw s!"{attacker.name} is not a creature you control"
  if !attacker.status.attacking then
    throw s!"{attacker.name} is not attacking"
  if attacker.status.blocked then
    throw s!"{attacker.name} is blocked"
  let whom := attacker.status.attackingWhom
  let some _spell := g.findObject? spellId | throw "The spell left the stack"
  let g := g.returnToHand attackerId attacker.owner
  let g := g.setObject { (g.object! spellId) with
    sneakPaid := true, sneakAttackWhom := whom }
  return g.logMsg s!"{(g.player p).name} pays a sneak cost"

/-- Pay the locked-in cost (CR 601.2h / 602.2b). Spells and abilities that still
need an artifact or creature sacrificed, or a card discarded, wait for
that action. -/
def finishProposedSpell (g : Game) : Except String Game := do
  let some prop := g.proposedSpell | throw "No spell or ability is waiting to be paid for"
  let allowElf := g.proposedAllowsElfRestricted prop
  let allowInst := g.proposedAllowsInstRestricted prop
  let allowHero := g.proposedAllowsHeroRestricted prop
  let allowVillain := g.proposedAllowsVillainRestricted prop
  let allowCant := g.proposedAllowsCantNonartifact prop
  let allowCreature := g.proposedAllowsCreatureRestricted prop
  let spend := g.proposedManaSpend prop
  if !(g.player prop.caster).manaPool.canPay prop.cost allowElf allowInst
        allowHero allowVillain allowCant allowCreature spend ||
      !g.sourceStillPayable prop ||
      !g.canPayLife prop.caster prop.payLife then
    return g.reverseProposedSpell
  if prop.needsSacrificeOther then
    let excludeId := prop.sourceId.getD prop.spellId
    if (g.sacrificeCreatureOrArtifactChoices prop.caster excludeId).isEmpty then
      return g.reverseProposedSpell
  if prop.needsDiscardCard && (g.player prop.caster).hand.isEmpty then
    return g.reverseProposedSpell
  let count (g : Game) (u : FraManaUse) :=
    ((g.player prop.caster).manaPool.fraRestricted.filter (·.2 == u)).size
  let paid ← g.payCost prop.caster prop.cost allowElf allowInst
    allowHero allowVillain allowCant allowCreature spend
  let spent (u : FraManaUse) := count paid u < count g u
  let g :=
    match prop.kind, paid.findObject? prop.spellId with
    | .spell, some o =>
      if spent .legendarySpell then
        (paid.setObject { o with treasureManaSpent := o.treasureManaSpent || spent .fromTreasure
                                 uncounterableThisCast := true }).logMsg
          s!"{o.name} can't be countered (Delighted Halfling)"
      else paid.setObject { o with treasureManaSpent := spent .fromTreasure }
    | _, _ => paid
  if prop.kind == .activatedAbility then
    return (← g.beginActivationPayment prop)
  let g ←
    match prop.sneakAttacker with
    | some a =>
      match g.paySneak prop.caster prop.spellId a with
      | .ok g => pure g
      | .error _ => return g.reverseProposedSpell
    | none => pure g
  match prop.kind, prop.needsSacrificeOther, prop.needsDiscardCard with
  | _, true, _ =>
    let g := { g with
      pending := .sacrificePermanent prop.caster prop.spellId
      consecutivePasses := 0 }
    return g.logMsg
      s!"{(g.player prop.caster).name} must sacrifice an artifact or creature"
  | _, _, true =>
    let g := { g with
      pending := .discardForAdditionalCost prop.caster
      consecutivePasses := 0 }
    return g.logMsg
      s!"{(g.player prop.caster).name} must discard a card"
  | _, _, _ =>
    let g := { g with pending := .none, proposedSpell := none, consecutivePasses := 0 }
    return g.becomeCast prop.caster (g.object! prop.spellId)

/-- Starting mana cost of `face` before increases and reductions (CR 118.7). -/
def playCostStart (card : GameObject) (face : CardDef) : ManaCost :=
  if card.castFromGraveyard || card.zone == .graveyard card.owner then
    face.flashback.getD face.manaCost
  else face.manaCost

/-- Apply cost reductions to `start` (CR 118.7 / 601.2f). Increases such as
kicker must already be included in `start`. -/
def applyCastCostReductions (g : Game) (card : GameObject) (face : CardDef)
    (start : ManaCost) : ManaCost :=
  let caster := card.controller.getD card.owner
  let afterDied :=
    if face.costReductionIfCreatureDied > 0 && g.creatureDiedThisTurn then
      start.reduceGeneric face.costReductionIfCreatureDied
    else start
  let afterControl :=
    match face.costReductionIfYouControl with
    | some (n, subtype) =>
      let controls :=
        if subtype == "legendary creature" then
          (g.permanentsOf caster).any (fun o => o.isCreature && o.isLegendary)
        else g.countSubtype caster subtype > 0
      if controls then afterDied.reduceGeneric n
      else afterDied
    | none => afterDied
  let afterGy :=
    match face.costReductionIfGyCreaturesAtLeast with
    | some (min, n) =>
      let gy :=
        (g.player caster).graveyard.filter (fun id =>
          match g.findObject? id with
          | some c => c.printed.isCreature
          | none => false) |>.size
      if gy >= min then afterControl.reduceGeneric n else afterControl
    | none => afterControl
  let afterFly :=
    if face.costReductionEqualFlyingPower then
      let n :=
        (g.permanentsOf caster).foldl (fun acc o =>
          if o.isCreature && g.hasFlying o then acc + (g.power o).toNat else acc) 0
      afterGy.reduceGeneric n
    else afterGy
  -- Ghalta: X is the greatest power or toughness among creatures you
  -- control, determined after the spell is on the stack (rulings 824 / 874).
  let afterGreatest :=
    let creatures := (g.permanentsOf caster).filter (·.isCreature)
    let greatest (f : GameObject → Int) : Nat :=
      creatures.foldl (fun acc o => Nat.max acc (f o).toNat) 0
    let n :=
      (if face.costReductionGreatestPower then greatest g.power else 0) +
        (if face.costReductionGreatestToughness then greatest g.toughness else 0)
    afterFly.reduceGeneric n
  let afterAff :=
    match face.affinityForSubtype with
    | some t =>
      let st := if t == "Elves" then "Elf" else t
      let n := g.countSubtype caster st
      afterGreatest.reduceGeneric n
    | none => afterGreatest
  let afterOpp :=
    if face.costReductionEqualOppArtifacts then
      let n :=
        g.players.foldl (fun acc pl =>
          if pl.id == caster || pl.lost then acc
          else
            let arts :=
              (g.permanentsOf pl.id).filter (fun o => o.printed.isArtifact) |>.size
            max acc arts) 0
      afterAff.reduceGeneric n
    else afterAff
  let afterSpell :=
    if face.isInstant || face.isSorcery then
      let n :=
        (g.permanentsOf caster).foldl (fun acc o =>
          let reduces :=
            o.staticAbilities.any (fun ab =>
              match ab with
              | .instantSorceryCostReductionEqualEquippedPower => true
              | _ => false)
          if !reduces then acc
          else
            match o.attachedTo.bind g.findObject? with
            | some host =>
              if host.isOnBattlefield then acc + (g.power host).toNat else acc
            | none => acc) 0
      afterOpp.reduceGeneric n
    else afterOpp
  let afterFirst :=
    if face.isCreature && (g.player caster).creatureSpellsCastThisTurn == 0 then
      let n :=
        (g.permanentsOf caster).foldl (fun acc o =>
          acc + o.printed.firstCreatureCostsLess) 0
      afterSpell.reduceGeneric n
    else afterSpell
  let notFromHand :=
    match card.zone with
    | .hand _ => 0
    | _ =>
      (g.permanentsOf caster).foldl (fun acc o =>
        acc + o.printed.costReductionNotFromHand) 0
  let afterNotHand := afterFirst.reduceGeneric notFromHand
  let witchLess :=
    if face.isInstant || face.isSorcery then
      let mv := face.manaValue + card.chosenX.getD 0
      if mv < 4 then 0
      else
        (g.permanentsOf caster).foldl (fun acc o =>
          let reduces :=
            o.staticAbilities.any (fun ab =>
              match ab with
              | .instantSorceryCostLessEqualPower => true
              | _ => false)
          if reduces then acc + (g.power o).toNat else acc) 0
    else 0
  let afterX :=
    match card.chosenX with
    | none => afterNotHand
    | some x =>
      { symbols := afterNotHand.symbols.foldl (fun acc s =>
          match s with
          | ManaSymbol.x =>
            if x == 0 then acc else acc.push (ManaSymbol.generic x)
          | _ => acc.push s) (#[] : Array ManaSymbol) }
  let afterWitch := afterX.reduceGeneric witchLess
  let subtypeLess :=
    (g.permanentsOf caster).foldl (fun acc o =>
      o.staticAbilities.foldl (fun acc ab =>
        match ab with
        | .subtypeSpellsCostLess subtype n =>
          if face.hasSubtype subtype then acc + n else acc
        | .typeSpellsCostLess ty n =>
          if face.hasType ty then acc + n else acc
        | .supertypeSpellsCostLess s n =>
          if face.hasSupertype s then acc + n else acc
        | .fra .noncreatureSpellsCostLess => if face.isCreature then acc else acc + 1
        | _ => acc) acc) 0
  let selfLess :=
    if face.staticAbilities.any (· == .fra .costsLessIfCastNoncreature) &&
        (g.player caster).noncreatureSpellsCastThisTurn > 0 then 2
    else 0
  afterWitch.reduceGeneric (subtypeLess + selfLess)

/-- Mana to pay for `face` after alternative costs and pre-target reductions
(CR 118.7 / 601.2f). `withoutManaCost` and a reduction that removes every
mana symbol become `{0}`, not an unpayable empty cost (CR 107.4d / 202.1b).
Target-based reductions lock in after CR 601.2c. Cost increases (kicker)
are applied before these reductions. -/
def playManaCost (g : Game) (card : GameObject) (face : CardDef)
    (increase : ManaCost := ManaCost.empty) : ManaCost :=
  let caster := card.controller.getD card.owner
  -- Thalia, the Survivor: each one an opponent controls adds {1}.
  let tax :=
    if face.isCreature then 0
    else
      (g.livingOpponents caster).foldl (fun acc pl =>
        acc + ((g.permanentsOf pl.id).filter (·.staticAbilities.any
          (· == .fra .opponentsNoncreatureSpellsCostMore))).size) 0
  let increase := if tax == 0 then increase else increase.addCost (ManaCost.ofGeneric tax)
  let start := playCostStart card face
  let afterIncrease := start.addCost increase
  let afterEquip := g.applyCastCostReductions card face afterIncrease
  let freeRG :=
    match g.pendingFreeRGCreature with
    | some p =>
      (card.controller == some p || card.owner == p) && face.isCreature &&
        (face.colors.contains .red || face.colors.contains .green)
    | none => false
  let cost :=
    if freeRG then
      g.applyCastCostReductions card face (ManaCost.empty.addCost increase)
    else
      match card.playPermission with
      | some perm =>
        if perm.withoutManaCost || perm.payLifeEqualManaValue then
          g.applyCastCostReductions card face (ManaCost.empty.addCost increase)
        else if perm.anyMana then ManaCost.ofGeneric afterEquip.manaValue
        else afterEquip
      | none =>
        -- Null Summoner: mana of any type can be spent.
        if card.zone == .exile && card.exiledBy.isSome then
          ManaCost.ofGeneric afterEquip.manaValue
        else afterEquip
  -- Omnipresence: from hand, a spell with mana value at most the number of
  -- creatures you control is cast without paying its mana cost. Spells with
  -- `{X}` are cast normally, so X is never forced to 0. Additional costs are
  -- still paid (rulings 794 / 795).
  let caster := card.owner
  let omnipresent :=
    card.zone == .hand caster && !face.manaCost.containsX &&
      face.manaValue ≤ (g.creaturesControlledBy caster).size &&
      (g.permanentsOf caster).any (fun o =>
        o.staticAbilities.any (fun
          | .castFromHandFreeUpToCreatures => true
          | _ => false))
  let cost :=
    if omnipresent then g.applyCastCostReductions card face (ManaCost.empty.addCost increase)
    else cost
  ManaCost.afterReduction face.manaCost cost

/-- True when `face` has a mana cost that would not be paid to play `card`. -/
def playsWithoutPayingManaCost (g : Game) (card : GameObject)
    (face : CardDef := card.printed) : Bool :=
  face.manaCost.includesManaPayment && !(g.playManaCost card face).includesManaPayment

/-- Extra lifetime power-up activations granted by Wonder Man (MSH). -/
def grantsExtraPowerUp (o : GameObject) : Bool :=
  o.printed.staticAbilities.any (fun ab =>
    match ab with
    | .extraPowerUpActivation => true
    | _ => false)

/-- Extra lifetime power-up activations granted by Wonder Man (MSH). -/
def powerUpActivationLimit (g : Game) (p : PlayerId) : Nat :=
  1 + ((g.permanentsOf p).filter grantsExtraPowerUp).size

/-- True when `o` is Hulk's generic power-up cost reduction. -/
def grantsHulkPowerUpReduction (o : GameObject) : Bool :=
  o.printed.staticAbilities.any (fun ab =>
    match ab with
    | .otherPowerUpCostsLess _ => true
    | _ => false)

/-- Generic mana subtracted from other creatures' power-up costs by Hulk
(MSH ruling 127: only generic mana). -/
def hulkPowerUpGenericReduction (g : Game) (p : PlayerId) (sourceId : ObjectId) : Nat :=
  (g.permanentsOf p).foldl (fun acc o =>
    if o.id == sourceId then acc
    else
      o.printed.staticAbilities.foldl (fun acc ab =>
        match ab with
        | .otherPowerUpCostsLess n => acc + n
        | _ => acc) acc) 0

def activationManaCost (g : Game) (p : PlayerId) (ab : ActivatedAbility)
    (source : Option GameObject := none) (chosenX : Option Nat := none) : ManaCost :=
  let withX (cost : ManaCost) : ManaCost :=
    match chosenX with
    | some x => cost.substituteX x
    | none => cost
  let firstEquipFree :=
    ab.isEquip && g.hasEnduringStory p && (g.player p).equipActivationsThisTurn == 0 &&
      (g.permanentsOf p).any (·.staticAbilities.any (· == .firstEquipFreeIfEnduringStory))
  let cost :=
    if firstEquipFree then ManaCost.empty
    else if ab.powerUp then
      match source with
      | some o =>
        let afterEnter :=
          if o.status.enteredThisTurn then
            ab.cost.mana.reduceByCost o.printed.manaCost
          else ab.cost.mana
        (withX afterEnter).reduceGeneric (g.hulkPowerUpGenericReduction p o.id)
      | none => withX ab.cost.mana
    else if ab.costReductionIfYouControlLegendary > 0 && g.controlsLegendaryCreature p then
      withX (ab.cost.mana.reduceGeneric ab.costReductionIfYouControlLegendary)
    else if ab.costReductionPerEquipment > 0 then
      let n := (g.permanentsOf p).filter (fun o => o.printed.isEquipment) |>.size
      withX (ab.cost.mana.reduceGeneric (ab.costReductionPerEquipment * n))
    else withX ab.cost.mana
  ManaCost.afterReduction ab.cost.mana cost

/-- True when `ab` has a mana cost that `p` would not pay to activate it. -/
def activatesWithoutPayingManaCost (g : Game) (p : PlayerId) (ab : ActivatedAbility)
    (source : Option GameObject := none) : Bool :=
  ab.cost.mana.includesManaPayment && !(g.activationManaCost p ab source).includesManaPayment

end Game
end Mtg.Engine
