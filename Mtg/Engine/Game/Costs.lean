import Mtg.Engine.Game.SpellTargets

/-!
# Total costs (CR 601.2f–h)

Finishing a proposed spell or ability, cast cost reductions
(CR 601.2f / 118.7), and activation mana costs including power-up
reductions.
-/

namespace Mtg.Engine
namespace Game

/-- Move `id` to `to`'s hand and log the return if it actually arrives in
`to`'s hand, deferring the log across `Pending.chooseReplacement`. -/
def returnToHand (g : Game) (id : ObjectId) (to : PlayerId)
    (cause : Option EventCause := none) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    let name := g.name o
    let (g, _) := g.move id (.hand to) none (verb := some .returnToHand) (cause := cause)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.logReturnedToHand id to name))
    else if (g.followMovedToZone? id (· == .hand to)).isSome then
      g.logMsg s!"{name} is returned to {(g.player to).name}'s hand"
    else g

/-- Legal only during the declare blockers step of the caster's (or shared team's) turn (CR 805.4a / 810.2). -/
def canCastForSneak (g : Game) (p : PlayerId) : Bool :=
  g.isOnActiveTeam p && g.step == .declareBlockers

/-- Pay sneak: return an unblocked attacker you control to hand and mark
the spell. The creature enters tapped and attacking the same player. -/
def paySneak (g : Game) (p : PlayerId) (spellId : ObjectId) (attackerId : ObjectId) :
    Except String Game := do
  if !g.canCastForSneak p then
    throw "Sneak can be paid only during the declare blockers step on your turn"
  let some attacker := g.findObject? attackerId | throw "no such object"
  if !(attacker.isOnBattlefield && g.isCreature attacker && g.controlledBy attacker p) then
    throw s!"{g.name attacker} is not a creature you control"
  if !attacker.status.attacking then
    throw s!"{g.name attacker} is not attacking"
  if attacker.status.blocked then
    throw s!"{g.name attacker} is blocked"
  let defPlayer := g.defendingPlayerOf attacker
  let atkTarget := attacker.status.attackingTarget.getD (.player defPlayer)
  let some _spell := g.findObject? spellId | throw "The spell left the stack"
  let cause := some (EventCause.costPayment .returnToHand p (some spellId))
  let g := g.returnToHand attackerId attacker.owner (cause := cause)
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishPostStep (.finishPaySneak p spellId attackerId atkTarget cause))
  let g := g.record (GameEvent.announced g.turnNumber spellId
    (costs := #[.sneak attackerId atkTarget]) (cause := cause))
  return g.logMsg s!"{(g.player p).name} pays a sneak cost"

/-- Starting mana cost of `face` before increases and reductions (CR 118.7).
The flashback cost replaces the mana cost only for a cast actually made via Flashback
(CR 702.34a / 601.2b,f): `flashback := some b` states it explicitly (the caster
knows how the spell is being cast); otherwise a card still in a graveyard is assumed
to be cast via its flashback ability (the only way `castSpell` casts a non-free
graveyard card with flashback), and a spell already cast reads
`GameEvent.castWithFlashback` rather than any graveyard origin (so *Bilbo, Thief in
the Night*'s `mayCastFromGraveyard` pays the normal mana cost). -/
def playCostStart (g : Game) (card : GameObject) (face : CardDef)
    (flashback : Option Bool := none) : ManaCost :=
  let inGy := match card.zone with | .graveyard _ => true | _ => false
  if flashback.getD (inGy || GameEvent.castWithFlashback g.events card.id) then
    face.flashback.getD face.manaCost
  else face.manaCost

/-- Un-substituted printed mana cost of `card` when cast as `face` (`none` when
cast face-down via Morph, whose mana value is `0` per CR 702.37c / 708.2a). -/
def actualPrintedManaCost? (g : Game) (card : GameObject) (face : CardDef) : Option ManaCost :=
  if card.status.faceDown || (face.name == "" && card.printed.name != "") then none
  else
    let bc := g.baseCard card
    match bc.adventure.filter (·.name == face.name) with
    | some adv => some adv.manaCost
    | none => some bc.manaCost

/-- Actual spell mana value of `card` cast as `face` (CR 118.9c / 202.3e / 702.37c). -/
def actualCastManaValue (g : Game) (card : GameObject) (face : CardDef) : Nat :=
  match g.actualPrintedManaCost? card face with
  | none => 0
  | some mc => (mc.substituteX (card.chosenX.getD 0)).manaValue

/-- Apply cost reductions to `start` (CR 118.7 / 601.2f). Increases such as
kicker must already be included in `start`. -/
def applyCastCostReductions (g : Game) (card : GameObject) (face : CardDef)
    (start : ManaCost) : ManaCost :=
  let caster := card.controller.getD card.owner
  let start :=
    match card.chosenX with
    | none => start
    | some x => start.substituteX x
  let afterDied :=
    if face.costReductionIfCreatureDied > 0 && g.loggedCreatureDeaths > 0 then
      start.reduceGeneric face.costReductionIfCreatureDied
    else start
  let afterControl :=
    match face.costReductionIfYouControl with
    | some (n, subtype) =>
      let controls :=
        if false then
          (g.permanentsOf caster).any (fun o => g.isCreature o && g.isLegendary o)
        else g.countSubtype caster subtype > 0
      if controls then afterDied.reduceGeneric n
      else afterDied
    | none => afterDied
  let afterControl :=
    if face.costReductionIfYouControlLegendary > 0 &&
        (g.permanentsOf caster).any (fun o => g.isCreature o && g.isLegendary o) then
      afterControl.reduceGeneric face.costReductionIfYouControlLegendary
    else afterControl
  let afterGy :=
    match face.costReductionIfGyCreaturesAtLeast with
    | some (min, n) =>
      let gy :=
        (g.player caster).graveyard.filter (fun id =>
          match g.findObject? id with
          | some c => g.isCreature c
          | none => false) |>.size
      if gy >= min then afterControl.reduceGeneric n else afterControl
    | none => afterControl
  let afterFly :=
    if face.costReductionEqualFlyingPower then
      let n :=
        (g.permanentsOf caster).foldl (fun acc o =>
          if g.isCreature o && g.hasFlying o then acc + (g.power o).toNat else acc) 0
      afterGy.reduceGeneric n
    else afterGy
  -- Ghalta: X is the greatest power or toughness among creatures you
  -- control, determined after the spell is on the stack (rulings 824 / 874).
  let afterGreatest :=
    let creatures := (g.permanentsOf caster).filter (g.isCreature ·)
    let greatest (f : GameObject → Int) : Nat :=
      creatures.foldl (fun acc o => Nat.max acc (f o).toNat) 0
    let n :=
      (if face.costReductionGreatestPower then greatest g.power else 0) +
        (if face.costReductionGreatestToughness then greatest g.toughness else 0)
    afterFly.reduceGeneric n
  let afterAff :=
    match face.affinityForSubtype with
    | some t =>
      let n := g.countSubtype caster t
      afterGreatest.reduceGeneric n
    | none => afterGreatest
  let afterOpp :=
    if face.costReductionEqualOppArtifacts then
      let n :=
        g.players.foldl (fun acc pl =>
          if pl.id == caster || !g.stillInGame pl.id || g.areTeammates caster pl.id then acc
          else
            let arts :=
              (g.permanentsOf pl.id).filter (fun o => g.isArtifact o) |>.size
            max acc arts) 0
      afterAff.reduceGeneric n
    else afterAff
  let afterSpell :=
    if face.isInstant || face.isSorcery then
      let n :=
        (g.permanentsOf caster).foldl (fun acc o =>
          let reduces :=
            (g.staticAbilities o).any (fun ab =>
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
    if face.isCreature && g.loggedCreatureSpells caster == 0 then
      let n :=
        (g.permanentsOf caster).foldl (fun acc o =>
          if g.retainsPrintedAbilities o then acc + (g.baseCard o).firstCreatureCostsLess else acc) 0
      afterSpell.reduceGeneric n
    else afterSpell
  let notFromHand :=
    match card.zone with
    | .hand _ => 0
    | _ =>
      (g.permanentsOf caster).foldl (fun acc o =>
        if g.retainsPrintedAbilities o then acc + (g.baseCard o).costReductionNotFromHand else acc) 0
  let afterNotHand := afterFirst.reduceGeneric notFromHand
  let witchLess :=
    if face.isInstant || face.isSorcery then
      if g.actualCastManaValue card face < 4 then 0
      else
        (g.permanentsOf caster).foldl (fun acc o =>
          let reduces :=
            (g.staticAbilities o).any (fun ab =>
              match ab with
              | .instantSorceryCostLessEqualPower => true
              | _ => false)
          if reduces then acc + (g.power o).toNat else acc) 0
    else 0
  let afterWitch := afterNotHand.reduceGeneric witchLess
  let subtypeLess :=
    (g.permanentsOf caster).foldl (fun acc o =>
      (g.staticAbilities o).foldl (fun acc ab =>
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
        g.loggedNoncreatureSpells caster > 0 then 2
    else 0
  let thisTurnLess :=
    ((g.typeSpellCostLessThisTurn caster).foldl (fun acc (ty, n) =>
      if face.hasType ty then acc + n else acc) 0) +
    ((g.supertypeSpellCostLessThisTurn caster).foldl (fun acc (s, n) =>
      if face.hasSupertype s then acc + n else acc) 0)
  let sphinxLess :=
    if face.hasSubtype .sphinx then
      let zone (o : GameObject) :=
        o.id != card.id && g.controlledBy o caster &&
          (o.zone == .command || (o.isOnBattlefield && g.retainsPrintedAbilities o))
      (g.objects.filter zone).foldl (fun acc o => acc + (g.baseCard o).eminenceSphinxReduction) 0
    else 0
  (afterWitch.reduceGeneric (subtypeLess + selfLess + thisTurnLess)).reduceGeneric sphinxLess

/-- Mana to pay for `face` after alternative costs and pre-target reductions
(CR 118.7 / 118.9a,c / 601.2f). `withoutManaCost` and a reduction that removes
every mana symbol become `{0}`, not an unpayable empty cost (CR 107.4d / 202.1b).
Target-based reductions lock in after CR 601.2c. Cost increases (kicker)
are applied before these reductions. -/
def playManaCost (g : Game) (card : GameObject) (face : CardDef)
    (increase : ManaCost := ManaCost.empty)
    (origPerm : Option PlayPermission := none)
    (flashback : Option Bool := none)
    (explicitAltCost : Bool := false) : ManaCost :=
  let caster := card.controller.getD card.owner
  -- Thalia, the Survivor: each one an opponent controls adds {1}.
  let tax :=
    if face.isCreature then 0
    else
      (g.livingOpponents caster).foldl (fun acc pl =>
        acc + ((g.permanentsOf pl.id).filter (fun o => (g.staticAbilities o).any
          (· == .fra .opponentsNoncreatureSpellsCostMore))).size) 0
  let increase := if tax == 0 then increase else increase.addCost (ManaCost.ofGeneric tax)
  let inGy := match card.zone with | .graveyard _ => true | _ => false
  let effPerm := origPerm <|> g.playPermission card
  let hasFb := face.flashback.isSome || g.flashbackUntilEot card
  let usedFlashback :=
    hasFb && flashback.getD (inGy || GameEvent.castWithFlashback g.events card.id)
  let usedPermAlt := effPerm.any (fun pm => pm.withoutManaCost || pm.payLifeEqualManaValue)
  let printedMc? := g.actualPrintedManaCost? card face
  let usedMorph := printedMc?.isNone
  let usedSubstitutedAlt := printedMc?.any (fun mc => mc != face.manaCost)
  -- CR 118.9a: only one alternative cost can be applied to any one spell.
  let usedAltCost :=
    explicitAltCost || usedFlashback || usedPermAlt || usedMorph || usedSubstitutedAlt
  let start := g.playCostStart card face flashback
  let afterIncrease := start.addCost increase
  let afterEquip := g.applyCastCostReductions card face afterIncrease
  let freeRG :=
    !usedAltCost &&
      match g.pendingFreeRGCreature with
      | some p =>
        caster == p && face.isCreature &&
          (face.colors.contains .red || face.colors.contains .green)
      | none => false
  let cost :=
    if freeRG then
      g.applyCastCostReductions card face (ManaCost.empty.addCost increase)
    else
      match effPerm with
      | some perm =>
        if (perm.withoutManaCost || perm.payLifeEqualManaValue) &&
            !(explicitAltCost || usedFlashback || usedMorph || usedSubstitutedAlt) then
          g.applyCastCostReductions card face (ManaCost.empty.addCost increase)
        else if perm.anyMana then afterEquip.asAnyMana
        else afterEquip
      | none =>
        -- Null Summoner: mana of any type can be spent.
        if card.zone == .exile && card.exiledBy.isSome then
          afterEquip.asAnyMana
        else afterEquip
  -- Omnipresence: from hand, a spell with mana value at most the number of
  -- creatures you control is cast without paying its mana cost. Spells with
  -- `{X}` are cast normally, so X is never forced to 0. Additional costs are
  -- still paid (rulings 794 / 795; CR 118.9a,c).
  let omnipresent :=
    !usedAltCost && !freeRG &&
      card.zone == .hand caster &&
      printedMc?.any (fun mc => !mc.containsX) &&
      g.actualCastManaValue card face ≤ (g.creaturesControlledBy caster).size &&
      (g.permanentsOf caster).any (fun o =>
        (g.staticAbilities o).any (fun
          | .castFromHandFreeUpToCreatures => true
          | _ => false))
  let cost :=
    if omnipresent then g.applyCastCostReductions card face (ManaCost.empty.addCost increase)
    else cost
  -- Flawless Maneuver: if you control a commander, you may cast this spell
  -- without paying its mana cost unless another alternative cost was chosen (CR 118.9a).
  let freeCommander :=
    !usedAltCost && !freeRG && !omnipresent &&
      face.freeCastIfControlCommander &&
      (g.permanentsOf caster).any (·.isCommander)
  let cost :=
    if freeCommander then
      g.applyCastCostReductions card face (ManaCost.empty.addCost increase)
    else cost
  ManaCost.afterReduction face.manaCost cost

/-- True when `face` has a mana cost that would not be paid to play `card`. -/
def playsWithoutPayingManaCost (g : Game) (card : GameObject)
    (face : CardDef := card.printed) : Bool :=
  face.manaCost.includesManaPayment && !(g.playManaCost card face).includesManaPayment

/-- Extra lifetime power-up activations granted by Wonder Man (MSH). -/
def grantsExtraPowerUp (g : Game) (o : GameObject) : Bool :=
  (g.staticAbilities o).any (fun ab =>
    match ab with
    | .extraPowerUpActivation => true
    | _ => false)

/-- Extra lifetime power-up activations granted by Wonder Man (MSH). -/
def powerUpActivationLimit (g : Game) (p : PlayerId) : Nat :=
  1 + ((g.permanentsOf p).filter (g.grantsExtraPowerUp ·)).size

/-- Generic mana subtracted from other creatures' power-up costs by Hulk
(MSH ruling 127: only generic mana). -/
def hulkPowerUpGenericReduction (g : Game) (p : PlayerId) (sourceId : ObjectId) : Nat :=
  (g.permanentsOf p).foldl (fun acc o =>
    if o.id == sourceId then acc
    else
      (g.staticAbilities o).foldl (fun acc ab =>
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
    ab.isEquip && g.hasEnduringStory p && g.loggedEquipActivations p == 0 &&
      (g.permanentsOf p).any (fun o =>
        (g.staticAbilities o).any (· == .firstEquipFreeIfEnduringStory))
  let cost :=
    if firstEquipFree then ManaCost.empty
    else if ab.powerUp then
      match source with
      | some o =>
        let afterEnter :=
          if g.loggedEntered o.id then
            ab.cost.mana.reduceByCost (g.copiableValues o).manaCost
          else ab.cost.mana
        (withX afterEnter).reduceGeneric (g.hulkPowerUpGenericReduction p o.id)
      | none => withX ab.cost.mana
    else if ab.costReductionIfYouControlLegendary > 0 && g.controlsLegendaryCreature p then
      (withX ab.cost.mana).reduceGeneric ab.costReductionIfYouControlLegendary
    else if ab.costReductionPerEquipment > 0 then
      let n := (g.permanentsOf p).filter (fun o => g.isEquipment o) |>.size
      (withX ab.cost.mana).reduceGeneric (ab.costReductionPerEquipment * n)
    else withX ab.cost.mana
  ManaCost.afterReduction ab.cost.mana cost

/-- True when `ab` has a mana cost that `p` would not pay to activate it. -/
def activatesWithoutPayingManaCost (g : Game) (p : PlayerId) (ab : ActivatedAbility)
    (source : Option GameObject := none) : Bool :=
  ab.cost.mana.includesManaPayment && !(g.activationManaCost p ab source).includesManaPayment

end Game
end Mtg.Engine
