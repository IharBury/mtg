import Mtg.Engine.Game.Choices

/-!
# Total costs (CR 601.2f–h)

Paying life (CR 118.3b), additional activation costs, finishing a
proposed spell, cast cost reductions (CR 601.2f / 118.7), and
activation mana costs including power-up reductions.
-/

namespace Mtg.Engine
namespace Game

/-- Whether `p` can pay `n` life (CR 119.4). Paying 0 life is always legal. -/
def canPayLife (g : Game) (p : PlayerId) (n : Nat) : Bool :=
  n == 0 || (g.player p).life ≥ (n : Int)

/-- Pay `n` life as a cost (CR 118.3b / 119.4). Payment of life is not damage. -/
def payLifeCost (g : Game) (p : PlayerId) (n : Nat) : Except String Game := do
  if n == 0 then
    return g
  let pl := g.player p
  if pl.life < (n : Int) then
    throw s!"{pl.name} cannot pay {n} life"
  return g.setLife p (pl.life - (n : Int))
    s!"{pl.name} pays {n} life ({pl.life - (n : Int)} life)"

/-- Sacrifice choice for an activation cost, preferring tokens, then the
permanent with the lowest mana value. -/
def cheapestToSacrifice (g : Game) (cands : Array GameObject) : Option GameObject :=
  cands.foldl (fun acc o =>
    match acc with
    | none => some o
    | some b =>
      let key (x : GameObject) : Nat := (if x.printed.isToken then 0 else 1000) + g.objectManaValue x
      if key o < key b then some o else acc) none

/-- Pay the Reality Fracture part of an activation cost from the battlefield,
choosing the cheapest permanents or cards automatically. -/
def payFraBattlefieldCost (g : Game) (p : PlayerId) (sourceId : ObjectId) (c : FraCost) :
    Except String Game := do
  let sac (g : Game) (pred : GameObject → Bool) (what : String) : Except String Game :=
    match g.cheapestToSacrifice ((g.permanentsOf p).filter pred) with
    | none => throw s!"No {what} to sacrifice"
    | some o => pure (g.sacrificeToGraveyard o s!"{(g.player p).name} sacrifices {o.name}")
  match c with
  | .sacrificeAnotherArtifact =>
    sac g (fun o => o.id != sourceId && o.printed.isArtifact) "other artifact"
  | .sacrificeAnotherCreatureOrPlaneswalker =>
    sac g (fun o => o.id != sourceId && (o.isCreature || o.printed.isPlaneswalker))
      "other creature or planeswalker"
  | .sacrificeArtifactOrLand =>
    match g.cheapestToSacrifice ((g.permanentsOf p).filter (fun o =>
        o.id != sourceId && o.printed.isArtifact)) with
    | some _ => sac g (fun o => o.id != sourceId && o.printed.isArtifact) "artifact"
    | none => sac g (fun o => o.printed.isArtifact || o.printed.isLand) "artifact or land"
  | .discardLegendaryCard =>
    match (g.player p).hand.find? (fun id => (g.findObject? id).any (·.isLegendary)) with
    | none => throw "No legendary card to discard"
    | some hid =>
      let card := g.object! hid
      let g := g.logMsg s!"{(g.player p).name} discards {card.name}"
      let (g, _) := g.move hid (.graveyard card.owner) none
      pure (g.modifyPlayer p (fun pl => { pl with cardsDiscardedThisTurn := pl.cardsDiscardedThisTurn + 1 }))
  | .tapTwoUntappedArtifacts =>
    let arts := (g.permanentsOf p).filter (fun o => o.printed.isArtifact && !o.status.tapped)
    let arts := arts.filter (·.id != sourceId) ++ arts.filter (·.id == sourceId)
    if arts.size < 2 then throw "Not enough untapped artifacts to tap"
    pure ((arts.extract 0 2).foldl (fun g o => g.becomeTapped (g.object! o.id)) g)
  | _ => pure g

/-- Pay `{T}`, life, discard, and/or sacrifice the source as part of an activation cost
(CR 601.2h / 118.3b / 702.29). -/
def payActivationExtraCosts (g : Game) (p : PlayerId) (sourceId : ObjectId)
    (tapSource sacrificeSource : Bool) (payLife : Nat := 0)
    (discardSource : Bool := false)
    (ab : Option ActivatedAbility := none) : Except String Game := do
  let some src := g.findObject? sourceId | throw "The source is no longer in play"
  if ab.any (·.cost.fra == .exileSourceFromHand) then
    if !(src.zone == .hand src.owner && src.owner == p) then
      throw s!"{src.name} is not in your hand"
    let g ← g.payLifeCost p payLife
    let g := g.logMsg s!"{(g.player p).name} exiles {src.name} from their hand"
    return (g.move sourceId .exile none).1
  if discardSource then
    if !(src.zone == .hand src.owner && src.owner == p) then
      throw s!"{src.name} is not in your hand"
    let g ← g.payLifeCost p payLife
    let src := g.object! sourceId
    let g := g.logMsg s!"{(g.player p).name} discards {src.name}"
    let (g, _) := g.move sourceId (.graveyard src.owner) none
    return g
  let fromGraveyard := src.zone == .graveyard src.owner && src.owner == p
  if fromGraveyard && !tapSource && !sacrificeSource then
    let g ← g.payLifeCost p payLife
    let g ←
      if ab.any (·.cost.fra == .exileAnotherCreatureCardFromGraveyard) then
        match (g.player p).graveyard.find? (fun id =>
            id != sourceId && (g.findObject? id).any (·.printed.isCreature)) with
        | none => throw "No other creature card in your graveyard to exile"
        | some cid =>
          let name := (g.object! cid).name
          pure ((g.move cid .exile none).1.logMsg s!"{(g.player p).name} exiles {name} from their graveyard")
      else pure g
    if ab.any (·.cost.exileSourceFromGraveyard) then
      let g := g.logMsg s!"{(g.player p).name} exiles {src.name} from their graveyard"
      return (g.move sourceId .exile none).1
    return g
  if !src.isOnBattlefield then
    throw "The source is no longer on the battlefield"
  if !src.controlledBy p then
    throw "You don't control that permanent"
  let mut g := g
  if tapSource then
    let src := g.object! sourceId
    if src.status.tapped then
      throw s!"{src.name} is already tapped"
    g := g.becomeTapped src
  g := (← g.payLifeCost p payLife)
  match ab with
  | some a =>
    if a.cost.removeIndestructibleCounter then
      g := (← g.payRemoveIndestructibleCounter (g.object! sourceId))
    if a.cost.discardACard then
      match (g.player p).hand[0]? with
      | none => throw "No card to discard"
      | some hid =>
        let card := g.object! hid
        g := g.logMsg s!"{(g.player p).name} discards {card.name}"
        let (g', _) := g.move hid (.graveyard card.owner) none
        g := g'.modifyPlayer p (fun pl =>
          { pl with cardsDiscardedThisTurn := pl.cardsDiscardedThisTurn + 1 })
    if a.cost.discardLegendarySameName then
      let names :=
        (g.permanentsOf p).filterMap (fun o =>
          if o.isLegendary then some o.name else none)
      match (g.player p).hand.findSome? (fun hid =>
        match g.findObject? hid with
        | some o =>
          if o.isLegendary && names.contains o.name then some hid else none
        | none => none) with
      | none => throw "No legendary card of the same name to discard"
      | some hid =>
        let card := g.object! hid
        g := g.logMsg s!"{(g.player p).name} discards {card.name}"
        let (g', _) := g.move hid (.graveyard card.owner) none
        g := g'
    if a.cost.sacrificeLegendaryArtifact then
      match (g.permanentsOf p).find? (fun o =>
        o.printed.isArtifact && o.isLegendary &&
          !(sacrificeSource && o.id == sourceId)) with
      | none => throw "No legendary artifact to sacrifice"
      | some art =>
        g := g.sacrificeToGraveyard art
          s!"{(g.player p).name} sacrifices {art.name}"
    if a.cost.sacrificeArtifact then
      match (g.permanentsOf p).find? (fun o => o.printed.isArtifact) with
      | none => throw "No artifact to sacrifice"
      | some art =>
        g := g.sacrificeToGraveyard art
          s!"{(g.player p).name} sacrifices {art.name}"
    g := (← g.payFraBattlefieldCost p sourceId a.cost.fra)
    if let some t := a.cost.sacrificeAnotherSubtype then
      match (g.permanentsOf p).find? (fun o =>
        o.id != sourceId && g.hasSubtype o t) with
      | none => throw s!"No other {t} to sacrifice"
      | some o =>
        g := g.sacrificeToGraveyard o
          s!"{(g.player p).name} sacrifices {o.name}"
  | none => pure ()
  if sacrificeSource then
    match g.findObject? sourceId with
    | none => pure ()
    | some src =>
      g := g.sacrificeToGraveyard src
        s!"{(g.player p).name} sacrifices {src.name}"
  if ab.any (·.cost.fra == .exileSource) then
    match g.findObject? sourceId with
    | some src =>
      if src.isOnBattlefield then
        g := (g.move sourceId .exile none).1.logMsg s!"{(g.player p).name} exiles {src.name}"
    | none => pure ()
  return g

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
  let g ← g.payCost prop.caster prop.cost allowElf allowInst
    allowHero allowVillain allowCant allowCreature spend
  let g ←
    match prop.kind, prop.sourceId with
    | .activatedAbility, some sid =>
      g.payActivationExtraCosts prop.caster sid prop.tapSource prop.sacrificeSource
        prop.payLife prop.discardSource prop.activation
    | _, _ => pure g
  match prop.kind, prop.needsSacrificeOther, prop.needsDiscardCard, prop.sourceId with
  | .spell, true, _, _ =>
    let g := { g with
      pending := .sacrificePermanent prop.caster prop.spellId
      consecutivePasses := 0 }
    return g.logMsg
      s!"{(g.player prop.caster).name} must sacrifice an artifact or creature"
  | .spell, _, true, _ =>
    let g := { g with
      pending := .discardForAdditionalCost prop.caster
      consecutivePasses := 0 }
    return g.logMsg
      s!"{(g.player prop.caster).name} must discard a card"
  | .spell, _, _, _ =>
    let g := { g with pending := .none, proposedSpell := none, consecutivePasses := 0 }
    return g.becomeCast prop.caster (g.object! prop.spellId)
  | .activatedAbility, true, _, some sid =>
    let g := { g with
      pending := .sacrificePermanent prop.caster sid
      consecutivePasses := 0 }
    return g.logMsg
      s!"{(g.player prop.caster).name} must sacrifice another creature or artifact"
  | .activatedAbility, _, _, _ =>
    let g := { g with pending := .none, proposedSpell := none, consecutivePasses := 0 }
    return g.becomeActivated prop.caster prop.original.name prop.sourceId

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
  let cost :=
    if ab.powerUp then
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
