import Mtg.Engine.Game.Damage

/-!
# Mana abilities (CR 605)

Every mana ability of a permanent as one definition: its cost, the mana it
can add, and how that mana may be spent (CR 106.6). Activating one adds
the mana immediately, without using the stack (CR 605.3b).
-/

namespace Mtg.Engine
namespace Game

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
    (source : Option GameObject := none) (chosenX : Option Nat := none)
    (targets : Array Target := #[]) : ManaCost :=
  let withX (cost : ManaCost) : ManaCost :=
    match chosenX with
    | some x => cost.substituteX x
    | none => cost
  let firstEquipFree :=
    ab.isEquip && g.hasEnduringStory p && g.loggedEquipActivations p == 0 &&
      (g.permanentsOf p).any (fun o =>
        (g.staticAbilities o).any (· == .firstEquipFreeIfEnduringStory))
  let declRed : Nat :=
    if ab.costReductions.isEmpty then 0
    else EvalExpr.evalActivationCostReductions g p (source.map (·.id)) ab.costReductions targets
  let cost :=
    if firstEquipFree then ManaCost.empty
    else if ab.isPowerUp then
      match source with
      | some o =>
        let afterEnter :=
          if g.loggedEntered o.id then
            ab.cost.mana.reduceByCost (g.copiableValues o).manaCost
          else ab.cost.mana
        (withX afterEnter).reduceGeneric (g.hulkPowerUpGenericReduction p o.id + declRed)
      | none => (withX ab.cost.mana).reduceGeneric declRed
    else if declRed > 0 then
      (withX ab.cost.mana).reduceGeneric declRed
    else withX ab.cost.mana
  ManaCost.afterReduction ab.cost.mana cost

/-- True when `ab` has a mana cost that `p` would not pay to activate it. -/
def activatesWithoutPayingManaCost (g : Game) (p : PlayerId) (ab : ActivatedAbility)
    (source : Option GameObject := none) : Bool :=
  ab.cost.mana.includesManaPayment && !(g.activationManaCost p ab source).includesManaPayment

/-- A mana ability of a permanent (CR 605.1a). -/
structure ManaAbilityDef where
  output : ManaOutput
  tap : Bool := true
  cost : ManaCost := ManaCost.empty
  payLife : Nat := 0
  sacrificeSelf : Bool := false
  exileSelf : Bool := false
  removeStoryCounter : Bool := false
  removeIndestructibleCounter : Bool := false
  putStunCounterOnSource : Bool := false
  /-- Costs paid with objects the player chooses (Bolg's Company). -/
  picks : Array CostPick := #[]
  restriction : Option ManaSpendRestriction := none
  /-- Spell riders carried by mana produced by this ability (CR 106.6 / 106.12). -/
  riders : Array SpellRiderSpec := #[]
  /-- Index among `activatedAbilitiesOf` (CR 613.1f). -/
  activatedIdx : Option Nat := none
  turnLimit? : Option Nat := none
  lifetimeLimit? : Option Nat := none
  isPowerUp : Bool := false
  isExhaust : Bool := false
  isBoast : Bool := false
  sourceAbility : Option ActivatedAbility := none
  /-- Damage this ability deals to its controller as it resolves (CR 605.3b). -/
  damageYou : Nat := 0
deriving Inhabited

private def uniqMana (ts : Array ManaType) : Array ManaType :=
  ts.foldl (fun acc t => if acc.contains t then acc else acc.push t) #[]

private partial def manaNamedPermanents (g : Game) (o : GameObject) (controller : PlayerId) :
    TriggeredAbility.ObjectSelector → Option (Array GameObject)
  | .source | .sourceIfPresent | .sacrificedSource _ | .plan =>
    some (if o.isOnBattlefield then #[o] else #[])
  | .creaturesYouControl => some (g.creaturesControlledBy controller)
  | .othersOfSubtype subtype =>
    some (g.battlefield.filter (fun x =>
      g.controlledBy x controller && x.id != o.id && g.hasSubtype x subtype))
  | .youControl (.subtype s) =>
    some ((g.permanentsOf controller).filter (g.hasSubtype · s))
  | .youControl _ => some (g.creaturesControlledBy controller)
  | .eachOther =>
    some (g.battlefield.filter (fun x =>
      g.isCreature x && g.controlledBy x controller && x.id != o.id))
  | .landsYouControl => some ((g.permanentsOf controller).filter (g.isLand ·))
  | .legendaryCreaturesYouControl =>
    some ((g.permanentsOf controller).filter (fun x => g.isCreature x && g.isLegendary x))
  | .planeswalkersYouControl =>
    some ((g.permanentsOf controller).filter (g.isPlaneswalker ·))
  | .artifact => some ((g.permanentsOf controller).filter (g.isArtifact ·))
  | .anotherCreatureOrArtifact =>
    some ((g.permanentsOf controller).filter (fun x =>
      x.id != o.id && (g.isCreature x || g.isArtifact x)))
  | .attackingCreatures => some (g.battlefield.filter (·.status.attacking))
  | .humans =>
    some (g.battlefield.filter (fun x =>
      g.isCreature x && g.controlledBy x controller && g.hasSubtype x .human))
  | .opponentsCreatures =>
    some (g.battlefield.filter (fun x =>
      g.isCreature x && (g.controllerOf x).any (g.isLivingOpponentOf controller ·)))
  | .eachNonSubtypeAndOpponents subtype =>
    some (g.battlefield.filter (fun x => g.isCreature x && !g.hasSubtype x subtype))
  | .intersection ws =>
    match ws with
    | [] => some #[]
    | w0 :: rest =>
      rest.foldl (fun acc? w =>
        match acc?, manaNamedPermanents g o controller w with
        | some acc, some ys => some (acc.filter fun x => ys.any (·.id == x.id))
        | _, _ => none) (manaNamedPermanents g o controller w0)
  | .union ws =>
    ws.foldl (fun acc? w =>
      match acc?, manaNamedPermanents g o controller w with
      | some acc, some ys =>
        some (ys.foldl (fun a y => if a.any (·.id == y.id) then a else a.push y) acc)
      | _, _ => none) (some #[])
  | _ => none

/-- Evaluate `amount` for a battlefield mana ability on `o` (CR 605.3b). -/
def manaSelectorCount (g : Game) (o : GameObject) (amount : TriggeredAbility.NumberSelector) : Nat :=
  let controller := (g.controllerOf o).getD o.owner
  match amount with
  | .fixed n => n.toNat
  | .double | .chosenCreatureType | .chosenX => 0
  | .greatestPower => (g.greatestPowerAmongCreatures controller).toNat
  | .perLookedAt | .lastKnownPower | .thatManyLost | .spellManaValue
  | .equalToManaSpent | .equalToTargetPower | .blueManaSymbols => 0
  | .perOtherCreature =>
    (g.battlefield.filter (fun c =>
      g.isCreature c && g.controlledBy c controller && c.id != o.id)).size
  | .perPlains => ((g.permanentsOf controller).filter (g.hasSubtype · .plains)).size
  | .equalSourcePower => (g.power o).toNat
  | .equalSourceToughness => (g.toughness o).toNat
  | .subtypeCount subtype | .perSubtype subtype =>
    ((g.permanentsOf controller).filter (g.hasSubtype · subtype)).size
  | .discardedHand => g.handDiscardedThisWay.getD 0
  | .greatestArtifactMv =>
    (g.permanentsOf controller).foldl (fun acc x =>
      if g.isArtifact x then max acc (g.objectManaValue x) else acc) 0
  | .forEachTappedHuman => g.humansTappedThisWay
  | .perFatGraveyard => (g.players.filter (fun pl => pl.graveyard.size >= 7)).size
  | .perControlled ty => ((g.permanentsOf controller).filter (g.hasType · ty)).size
  | .upToHandSize n =>
    let cards := (g.player controller).hand.size
    if cards < n then n - cards else 0
  | .plusOneCounters => if o.isOnBattlefield then o.status.plusOnePlusOne else 0
  | .forEachDestroyedThisWay => g.permanentsDestroyedThisWay
  | .attachedEquipment => g.attachedEquipmentCount o
  | .perBurden => o.status.burden
  | .notedExcess => g.excessDamageThisWay
  | .notedPower => if g.destroyedForAmassThisWay then g.amassAmountThisWay else 0
  | .perChargeCounter =>
    let n := if o.isOnBattlefield then o.status.charge else 0
    if n == 0 then
      match g.lastKnownCounterStatus? o.id with
      | some last => last.charge
      | none => n
    else n
  | .oppArtifacts =>
    (g.battlefield.filter (fun x =>
      g.isArtifact x && (g.controllerOf x).any (g.isLivingOpponentOf controller ·))).size
  | .damagedPlayerArtifacts =>
    match g.loggedLastCombatDamagePlayer.orElse (fun _ => g.firstLivingOpponent? controller) with
    | some pid => ((g.permanentsOf pid).filter (g.isArtifact ·)).size
    | none => 0
  | .cardsDrawnThisTurn => g.loggedDraws controller
  | .libraryCards => (g.player controller).library.size
  | .count what =>
    match what with
    | .questCounters => if o.isOnBattlefield then o.status.quest else 0
    | .creatureCardsInGraveyard =>
      ((g.player controller).graveyard.filter (fun id => (g.findObject? id).any g.isCreature)).size
    | .harnessedSource => if o.status.harnessed then 1 else 0
    | _ => (manaNamedPermanents g o controller what).map (·.size) |>.getD 0

/-- Legacy fallback mana output for activated abilities whose effect is encoded
as a `Resolution.add*` variant rather than `ActivatedAbility.mana?`. -/
private def legacyResolutionManaOutput (g : Game) (o : GameObject) (r : Resolution) :
    Option (ManaOutput × Option ManaSpendRestriction) :=
  let power := (g.power o).toNat
  match r with
  | .addMana types amount =>
    let n := g.manaSelectorCount o amount
    some (.fixed (types.foldl (fun acc t => acc ++ Array.replicate n t) #[]), none)
  | .addAnyColor => some (.oneOf anyColorMana 1, none)
  | .addAnyColorSpendOnlySubtype s => some (.oneOf anyColorMana 1, some (.subtypeSpellOrSource s))
  | .addAnyColorSpendOnlyArtifactSpell => some (.oneOf anyColorMana 1, some .artifactSpell)
  | .addTwoAnyColorCreatureSources => some (.oneOf anyColorMana 2, some .creatureSource)
  | .addBlueCantNonartifact => some (.fixed #[.colored .blue], some .cantNonartifact)
  | .addAnyColorEqualToSourcePower => some (.oneOf anyColorMana power, none)
  | .addFourAnyCombination => some (.combination anyColorMana 4, none)
  | .addTwoAnyColorEquipment => some (.oneOf anyColorMana 2, some .equipmentOrEquip)
  | _ => none

/-- Mana a land can produce from its evaluated Layer-6 mana abilities
(CR 106.7 / 305.6 / 305.7 / 605.1a / 613.1f). Abilities that themselves query
"could produce" (`ManaSpec.usesLandsCouldProduce`) are skipped so two such
lands do not look at each other. -/
def intrinsicLandMana (g : Game) (o : GameObject) : Array ManaType :=
  if !o.isOnBattlefield || !g.isLand o then #[]
  else
    let p := (g.controllerOf o).getD o.owner
    let env : EvalEnv := { controller := p, sourceId := some o.id }
    let produced := (g.activatedAbilitiesOf o).foldl (fun acc ab =>
      if !isManaActivation ab || !EvalExpr.evalActivationCondition g p o.id ab.condition? then acc
      else
        match ab.mana? with
        | some mp =>
          if mp.spec.usesLandsCouldProduce then acc
          else
            let out := EvalExpr.evalManaSpec g env (fun _ _ => #[]) mp.spec
            acc ++ out.producibleTypes
        | none =>
          match legacyResolutionManaOutput g o ab.effect.resolution with
          | some (out, _) => acc ++ out.producibleTypes
          | none => acc) #[]
    uniqMana produced

/-- Mana any of `lands` could produce from intrinsic abilities (CR 106.7). -/
def landsCouldProduce (g : Game) (lands : Array GameObject) : Array ManaType :=
  uniqMana (lands.foldl (fun acc o => acc ++ g.intrinsicLandMana o) #[])

/-- Evaluate a symbolic `ManaPoolPalette` in `(g, env)` with full CR 106.7
`landsCouldProduce` resolution. -/
def evalManaPalette (g : Game) (env : EvalEnv) (palette : ManaPoolPalette) : Array ManaType :=
  EvalExpr.evalManaPalette g env Game.landsCouldProduce palette

/-- Evaluate a symbolic `ManaSpec` in `(g, env)` into a concrete `ManaOutput`
(CR 106.1 / 106.7 / 605). -/
def evalManaSpec (g : Game) (env : EvalEnv) (spec : ManaSpec) : ManaOutput :=
  EvalExpr.evalManaSpec g env Game.landsCouldProduce spec

/-- Build a `ManaAbilityDef` from an evaluated Layer-6 `ActivatedAbility`
satisfying CR 605.1a (`isManaActivation`). -/
def manaAbilityDefOfActivated (g : Game) (o : GameObject) (i : Nat)
    (ab : ActivatedAbility) : Option ManaAbilityDef :=
  if !isManaActivation ab then none
  else
    let p := (g.controllerOf o).getD o.owner
    let env : EvalEnv := { controller := p, sourceId := some o.id }
    let base : ManaAbilityDef := {
      output := .fixed #[]
      tap := ab.cost.tap
      cost := ab.cost.mana
      payLife := ab.cost.payLife
      sacrificeSelf := ab.cost.sacrificeSource
      exileSelf := ab.cost.exileSourceFromBattlefield
      removeStoryCounter := ab.cost.removeStoryCounter
      removeIndestructibleCounter := ab.cost.removeIndestructibleCounter
      putStunCounterOnSource := ab.cost.putStunCounterOnSource
      picks :=
        costPicksOf ab ++
          (if ab.cost.sacrificeAnotherCreatureOrArtifact then
            #[CostPick.sacrificeAnotherCreatureOrArtifact]
           else #[])
      activatedIdx := some i
      turnLimit? := ab.turnLimit?
      lifetimeLimit? := ab.lifetimeLimit?
      isPowerUp := ab.isPowerUp
      isExhaust := ab.isExhaust
      isBoast := ab.isBoast
      sourceAbility := some ab
    }
    match ab.mana? with
    | some mp =>
      let out := g.evalManaSpec env mp.spec
      some { base with
        output := out
        restriction := mp.restriction
        riders := mp.allRiders
        damageYou := mp.damageYou }
    | none =>
      match legacyResolutionManaOutput g o ab.effect.resolution with
      | some (out, r) =>
        some { base with
          output := out
          restriction := r
          riders := match r with | some rr => rr.riders | none => #[] }
      | none => none

/-- Every mana ability `o` has, read exclusively from its evaluated Layer-6
`activatedAbilitiesOf` (CR 305.6 / 305.7 / 605.1a / 613.1f). -/
def manaAbilityDefs (g : Game) (o : GameObject) : Array ManaAbilityDef :=
  let abs := g.activatedAbilitiesOf o
  (List.range abs.size).toArray.filterMap fun i =>
    g.manaAbilityDefOfActivated o i abs[i]!

/-- Effective mana cost of mana ability `d` on `o` for `p`, applying
`activationManaCost` reductions when backed by an `ActivatedAbility`. -/
def manaAbilityEffectiveCost (g : Game) (p : PlayerId) (o : GameObject) (d : ManaAbilityDef) : ManaCost :=
  match d.sourceAbility with
  | some ab => g.activationManaCost p ab (some o)
  | none => d.cost

/-- Whether `d` can be activated by tapping alone, without sacrificing/exiling
the source, removing counters, choosing other objects, paying life, or paying
mana (the `tap` shortcut and automatic payment). -/
def ManaAbilityDef.isPlainTap (d : ManaAbilityDef) : Bool :=
  d.tap && !d.sacrificeSelf && !d.exileSelf &&
    !d.removeStoryCounter && !d.removeIndestructibleCounter && !d.putStunCounterOnSource &&
    d.picks.isEmpty && !d.cost.includesManaPayment && d.payLife == 0

/-- Whether `d` is a plain `{T}` mana ability after `activationManaCost`
reductions on `o` for `p`. -/
def isPlainTapManaAbilityDef (g : Game) (p : PlayerId) (o : GameObject) (d : ManaAbilityDef) : Bool :=
  d.tap && !d.sacrificeSelf && !d.exileSelf &&
    !d.removeStoryCounter && !d.removeIndestructibleCounter && !d.putStunCounterOnSource &&
    d.picks.isEmpty && !(g.manaAbilityEffectiveCost p o d).includesManaPayment && d.payLife == 0

/-- Whether mana ability `d` of permanent `o` currently satisfies its timing,
frequency, condition, life, counter, and choice-cost prerequisites for `p`
(CR 605.3 / 602.5a / 702.177 / 702.193). -/
def manaAbilityDefUsable (g : Game) (p : PlayerId) (o : GameObject) (d : ManaAbilityDef) : Bool :=
  let turnLimitHit : Bool :=
    match d.turnLimit?, d.activatedIdx with
    | some lim, some i => g.abilityActivationsThisTurn o.id i (isBoast := d.isBoast) ≥ lim
    | some lim, none => g.activationsThisTurn o.id ≥ lim
    | none, _ => false
  let lifetimeLimitHit : Bool :=
    match d.lifetimeLimit?, d.activatedIdx with
    | some lim, some i =>
      let effLim := if d.isPowerUp then g.powerUpActivationLimit p else lim
      g.abilityActivationsSinceEntered o.id i (isPowerUp := d.isPowerUp) (isExhaust := d.isExhaust) ≥ effLim
    | some _, none =>
      (d.isExhaust && g.exhaustUsed o.id) ||
        (d.isPowerUp &&
          Nat.max (g.powerUpActivations o.id) (if g.powerUpUsed o.id then 1 else 0) ≥
            g.powerUpActivationLimit p)
    | none, _ => false
  o.isOnBattlefield && g.controlledBy o p &&
    !turnLimitHit &&
    !lifetimeLimitHit &&
    !(d.isPowerUp && g.powerUpsForbidden) &&
    !(d.removeStoryCounter && o.status.story == 0) &&
    !(d.removeIndestructibleCounter && o.status.indestructibleCounters == 0) &&
    g.canPayLife p d.payLife &&
    (d.picks.isEmpty ||
      g.costPicksPayable p (some o.id) d.picks
        (tapSource := d.tap) (sacrificeOrExileSource := d.sacrificeSelf || d.exileSelf)) &&
    d.sourceAbility.all (fun ab =>
      (match ab.timing with
       | .instant => true
       | .sorcery | .loyalty => g.asSorcery? p) &&
      EvalExpr.evalActivationCondition g p o.id ab.condition?)

/-- Mana types `o` can currently add with plain `{T}` mana abilities. -/
@[export mtg_game_mana_abilities_of]
def manaAbilitiesOf (g : Game) (o : GameObject) : Array ManaType :=
  let p := (g.controllerOf o).getD o.owner
  (g.manaAbilityDefs o).foldl (fun acc d =>
    if g.isPlainTapManaAbilityDef p o d && g.manaAbilityDefUsable p o d then
      d.output.types.foldl (fun acc t => if acc.contains t then acc else acc.push t) acc
    else acc) #[]

/-- Add `mana` to `p`'s pool with `r` and `riders` (CR 106.4 / 106.6 / 106.12). -/
def addRestrictedMana (pool : ManaPool) (mana : Array ManaType)
    (r : Option ManaSpendRestriction) (riders : Array SpellRiderSpec := #[]) : ManaPool :=
  mana.foldl (fun pool t => pool.add t (restriction := r) (riders := riders)) pool

/-- `p` may activate abilities of creatures they control as though those
creatures had haste (Shang-Chi, Master of Kung Fu; MSH 280). -/
def activatesAsThoughHaste (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o =>
    (g.staticAbilities o).any (fun
      | .activateCreaturesAsThoughHaste => true
      | _ => false))

/-- Whether `p` can currently tap `o` for a plain `{T}` mana ability (CR 302.6 / 605.3). -/
@[export mtg_game_can_tap_for_plain_mana]
def canTapForPlainMana (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  o.isOnBattlefield && g.controlledBy o p && !o.status.tapped &&
    !(g.manaAbilitiesOf o).isEmpty &&
    !(g.hasSummoningSickness o && !(g.isCreature o && g.activatesAsThoughHaste p))

/-- A player may activate mana abilities with priority, or while paying a
spell they are casting or another mana payment prompt (CR 605.3a / 601.2g / 608.2g). -/
def canActivateManaAbility (g : Game) (p : PlayerId) : Bool :=
  if g.over then false
  else if g.hasPriority p then true
  else
    match g.pending with
    | .activateManaAbilities caster =>
      caster == p && g.proposedSpell.all (·.cost.includesManaPayment)
    | .mayPayGeneric q _ => q == p
    | .fraChoice q (.mayPayThen ..) | .fraChoice q (.mayPayExtort _)
    | .fraChoice q (.mayPayManaForReflexive ..)
    | .fraChoice q (.mayPaySymbolsThen ..)
    | .fraChoice q (.ultronMayPay ..) => q == p
    | .fraChoice q (.mayCastCards _ withoutPaying _) => q == p && !withoutPaying
    | .fraChoice q (.mayCastFromGraveyard _) => q == p
    | .mayCastExiledElseDamage q .. => q == p
    | .declareAttackers =>
      g.activePlayer == p &&
        (g.livingOpponents p).any (fun opp => g.attackTaxPerCreature opp.id > 0)
    | .payOrLetCounter q _ _ => q == p
    | .payWard q _ cost _ =>
      q == p &&
        (cost.mana.includesManaPayment ||
          cost.items.any fun
            | .or choices => choices.any (fun ch => ch.mana.includesManaPayment)
            | _ => false)
    | _ => false

/-- Molten Tide: a triggered mana ability that resolves immediately, attributing
each extra `{R}` to its `.mountainExtraRed` effect's source (CR 106.1 / 605.4a). -/
def finishManaAbilityMountainTrigger (g : Game) (p : PlayerId) (_id : ObjectId) : Game :=
  if g.over || !g.stillInGame p then g
  else
    let entries := g.mountainExtraRedEntriesThisTurn p
    let extraUnits : Array ManaUnit :=
      entries.foldl (fun acc (n, src?) =>
        acc ++ Array.replicate n ({ mana := .colored .red, source := src? } : ManaUnit)) #[]
    if !extraUnits.isEmpty then
      let extraRed := extraUnits.size
      (g.addManaUnits p extraUnits (cause := some (.gameRule .abilityActivated))).logMsg
        (s!"{(g.player p).name} adds an additional " ++ String.join (List.replicate extraRed "{R}"))
    else g

/-- Object whose types decide ability-source mana spending restrictions. -/
def proposedRestrictionSource (g : Game) (prop : ProposedSpell) : Option GameObject :=
  match prop.kind with
  | .spell => g.findObject? prop.spellId
  | .activatedAbility =>
    match prop.sourceId.bind g.findObject? with
    | some src => some src
    | none => some prop.original
  | .turnFaceUp => none

/-- What paying `prop` is for, as `ManaSpendRestriction` checks see it (CR 106.6). -/
def proposedManaSpend (g : Game) (prop : ProposedSpell) : ManaSpend :=
  match prop.kind with
  | .activatedAbility =>
    match g.proposedRestrictionSource prop with
    | some src =>
      { equip := prop.activation.any (·.isEquip)
        abilitySourceTypes := g.types src
        abilitySourceSupertypes := g.supertypes src
        abilitySourceSubtypes := g.subtypes src }
    | none =>
      { equip := prop.activation.any (·.isEquip) }
  | .turnFaceUp => {}
  | .spell =>
    match g.findObject? prop.spellId with
    | some o =>
      { spell := true, fromHand := prop.original.zone == .hand prop.caster
        castFromZone := some prop.original.zone.kind
        supertypes := g.supertypes o
        types := g.types o
        subtypes := g.subtypes o }
    | none => {}

/-- Whether mana with restriction `r` may be spent on `prop` (CR 106.6). -/
def restrictionAllowsProposed (g : Game) (r : Option ManaSpendRestriction) (prop : ProposedSpell) : Bool :=
  match r with
  | none => true
  | some restr => restr.allows (g.proposedManaSpend prop)

private def departedSinceOptionalCkpt (g : Game) (ckpt? : Option ProposalCheckpoint)
    (seed : Array PlayerId := #[]) : Array PlayerId :=
  match ckpt? with
  | some ckpt => g.playersDepartedSinceCheckpoint ckpt seed
  | none =>
    g.players.foldl (fun acc pl =>
      if pl.leftTheGame && !acc.contains pl.id then acc.push pl.id else acc) seed

/-- True when `f` holds only queued replacement/trigger-sequence continuations
(`pendingReplacement`, `outerPendingReplacements`, `triggerSequenceRest`,
`mayThenResume`) rather than an active resolving spell/ability/choice frame. -/
private def isCarrierOnlyFrame (f : ContinuationFrame) : Bool :=
  { f with
    pendingReplacement := none
    outerPendingReplacements := #[]
    triggerSequenceRest := none
    mayThenResume := false } == {}

private def abortDepartedManaAbilityContCore (g : Game) (p : PlayerId) (prevPending : Pending)
    (wasPaused : Bool := true) (hasFollowingSeq : Bool := false) : Game × Bool :=
  Id.run do
    let mut g := g
    let mut didReverseManaCkpt := false
    let manaCkpt? := if g.hasActiveManaProposalCheckpoint then g.proposalCheckpoint else none
    let preDeparted := departedSinceOptionalCkpt g manaCkpt?
    if g.hasActiveManaProposalCheckpoint then
      match g.reverseToProposalCheckpoint? with
      | .ok g' =>
        g := g'
        didReverseManaCkpt := true
      | .error _ =>
        g := g.change .clearProposalCheckpoint
    else if g.proposalCheckpoint.isSome then
      g := g.change .endProposalAction
    let allDeparted := departedSinceOptionalCkpt g manaCkpt? preDeparted
    if !wasPaused && didReverseManaCkpt &&
        manaCkpt?.any (fun ckpt => g.events.size == ckpt.eventsSize) &&
        !g.over && g.stillInGame p then
      return (g, true)
    if !g.over then
      let mut strippedSoloPrev := false
      if didReverseManaCkpt && prevPending != .none &&
          g.pending == .none && g.afterRandom == .none && !g.sbaPaused then
        if let some curCont := g.pendingReplacement then
          let target : PendingReplacement := .restorePending prevPending false
          if PendingReplacement.containsModDeparted target curCont &&
              (PendingReplacement.dropTargetModDeparted target curCont).isNone then
            g := g.change (.pendingReplacement none)
            while g.continuations.back? == some {} do
              g := g.change .popContinuationFrame
            strippedSoloPrev := true
      let shouldRestorePrev :=
        prevPending != .none &&
          if didReverseManaCkpt then
            (g.pending == prevPending || strippedSoloPrev) && g.afterRandom == .none && !g.sbaPaused
          else
            !g.sbaPaused
      if shouldRestorePrev then
        g := g.resumePendingReplacementFwd (.restorePending prevPending false none allDeparted none)
      if !g.over && g.pending == .none && g.afterRandom == .none && !g.sbaPaused &&
          !hasFollowingSeq then
        let prio := if g.stillInGame p then g.priorityInstead p else g.priorityInstead g.activePlayer
        if g.continuations.all isCarrierOnlyFrame then
          g := g.finishAndGrantPriorityFwd prio
        else if g.pendingReplacement.isSome || !g.outerPendingReplacements.isEmpty ||
            g.triggerSequenceRest.isSome || g.mayThenResume then
          if !g.anyContinuationSettlesControlFlowFwd then
            if g.pendingPriority != some prio then
              g := g.change (.pendingPriority (some prio))
            g := g.chainPendingReplacement .finishFraChoice
          else if g.anyContinuationGrantsPriorityFwd &&
              g.hasImplicitPriorityContinuationFwd && g.pendingPriority != some prio then
            g := g.change (.pendingPriority (some prio))
          g := g.drainPendingContinuationsFwd
    return (g, false)

private def abortDepartedManaAbilityCont (g : Game) (p : PlayerId) (prevPending : Pending)
    (wasPaused : Bool := true) (hasFollowingSeq : Bool := false) : Game :=
  (abortDepartedManaAbilityContCore g p prevPending
    (wasPaused := wasPaused) (hasFollowingSeq := hasFollowingSeq)).1

private def manaSourceTapPaidSinceCkpt (g : Game) (p : PlayerId) (id : ObjectId) : Bool :=
  let rec unwrapReplaced : EventCause → EventCause
    | .replaced _ orig => unwrapReplaced orig
    | other => other
  match g.proposalCheckpoint with
  | none => false
  | some ckpt =>
    let slice := g.events.extract (min ckpt.eventsSize g.events.size) g.events.size
    slice.any fun
      | .rules _ (.permanent (.tapped snap _)) cause _ =>
        snap.id == some id &&
          match unwrapReplaced cause with
          | .costPayment .tap q (some f) => q == p && f == id
          | _ => false
      | _ => false

/-- Finish the post-sacrifice steps (`abilityActivated`, `manaAdded`, pain-land
damage, Mountain extra mana, and CR 733.1 / priority cleanup) of a mana ability. -/
def finishActivateManaAbilityPostSac (g : Game) (p : PlayerId) (id : ObjectId) (oname : String)
    (srcSnap : EventObject) (mana : Array ManaType) (tap : Bool)
    (activatedIdx : Option Nat) (restriction : Option ManaSpendRestriction)
    (damageYou : Nat) (isMountain : Bool) (prevPending : Pending)
    (powerUp : Bool := false) (exhaust : Bool := false)
    (riders : Array SpellRiderSpec := #[])
    (wasPaused : Bool := true) (hasFollowingSeq : Bool := false) : Game := Id.run do
  let mut g := g
  if prevPending == .none && !hasFollowingSeq then
    if let some outer := g.pendingReplacement then
      if g.continuations.isEmpty then
        g := g.change (.pushContinuationFrame {})
      g := g.changes #[.pendingReplacement none, .pushOuterPendingReplacement outer]
  if g.over || !g.stillInGame p then
    return abortDepartedManaAbilityCont g p prevPending
      (wasPaused := wasPaused) (hasFollowingSeq := hasFollowingSeq)
  g := g.record (GameEvent.abilityActivated g.turnNumber id srcSnap p (.mana activatedIdx powerUp exhaust))
  let isTreasure := srcSnap.subtypes.contains .treasure
  let addedUnits := mana.map (fun t =>
    ({ mana := t, source := some id, restriction := restriction, riders := riders, fromTreasure := isTreasure } : ManaUnit))
  g := g.record (GameEvent.manaAdded g.turnNumber p addedUnits)
  let produced :=
    match mana[0]? with
    | some t =>
      if !mana.all (· == t) then String.intercalate ", " (mana.toList.map toString)
      else if mana.size == 1 then toString t
      else s!"{t} ×{mana.size}"
    | none => ""
  let verb := if tap then "taps" else "activates"
  let restrNote := ManaSpendRestriction.note restriction
  g :=
    if mana.isEmpty then g.logMsg s!"{(g.player p).name} {verb} {oname} but adds no mana"
    else g.logMsg s!"{(g.player p).name} {verb} {oname} for {produced}{restrNote}"
  if tap then
    g := match g.proposedSpell with
      | some _ => g.changeProposal (.pushTapped id)
      | none => g
  g := g.change (.consecutivePasses 0)
  if damageYou > 0 then
    let dmgSrc := (g.findLiveSourceObject? id).orElse (fun _ => some (damageSourceObjectFromLki srcSnap))
    g := g.dealDamageToPlayer p damageYou (source := dmgSrc)
      (cause := some (.gameRule .abilityActivated))
  let allDeparted := departedSinceOptionalCkpt g g.proposalCheckpoint
  if let .chooseReplacement .. := g.pending then
    if isMountain then
      g := g.chainPendingReplacement (.finishManaAbilityMountainTrigger p id)
    let manaCkpt := g.hasActiveManaProposalCheckpoint
    if g.proposalCheckpoint.isSome then
      g := g.chainPendingReplacement (.endProposalAction manaCkpt)
    if prevPending == .none then
      if !hasFollowingSeq then
        let prio := if g.stillInGame p then g.priorityInstead p else g.priorityInstead g.activePlayer
        if g.continuations.all isCarrierOnlyFrame then
          if g.outerPendingReplacements.isEmpty &&
              g.triggerSequenceRest.isNone && !g.mayThenResume then
            g := g.chainPendingReplacement (.receivePriority prio)
          else if !g.anyContinuationSettlesControlFlowFwd then
            if g.pendingPriority != some prio then
              g := g.change (.pendingPriority (some prio))
            g := g.chainPendingReplacement .finishFraChoice
          else if g.anyContinuationGrantsPriorityFwd &&
              g.hasImplicitPriorityContinuationFwd && g.pendingPriority != some prio then
            g := g.change (.pendingPriority (some prio))
        else if !g.outerPendingReplacements.isEmpty ||
            g.triggerSequenceRest.isSome || g.mayThenResume then
          if !g.anyContinuationSettlesControlFlowFwd then
            if g.pendingPriority != some prio then
              g := g.change (.pendingPriority (some prio))
            g := g.chainPendingReplacement .finishFraChoice
          else if g.anyContinuationGrantsPriorityFwd &&
              g.hasImplicitPriorityContinuationFwd && g.pendingPriority != some prio then
            g := g.change (.pendingPriority (some prio))
        else if g.anyContinuationGrantsPriorityFwd &&
            g.hasImplicitPriorityContinuationFwd && g.pendingPriority != some prio then
          g := g.change (.pendingPriority (some prio))
    else
      g := g.chainPendingReplacement (.restorePending prevPending false none allDeparted none)
    return g
  else
    if isMountain then
      g := g.finishManaAbilityMountainTrigger p id
    let manaCkpt := g.hasActiveManaProposalCheckpoint
    if manaCkpt then
      g := g.change .clearProposalCheckpoint
    if g.proposalCheckpoint.isSome then
      g := g.change .endProposalAction
    if prevPending == .none then
      if !g.over && g.pending == .none && g.afterRandom == .none && !g.sbaPaused &&
          !hasFollowingSeq then
        let prio := if g.stillInGame p then g.priorityInstead p else g.priorityInstead g.activePlayer
        if g.continuations.all isCarrierOnlyFrame then
          g := g.finishAndGrantPriorityFwd prio
        else if g.pendingReplacement.isSome || !g.outerPendingReplacements.isEmpty ||
            g.triggerSequenceRest.isSome || g.mayThenResume then
          if !g.anyContinuationSettlesControlFlowFwd then
            if g.pendingPriority != some prio then
              g := g.change (.pendingPriority (some prio))
            g := g.chainPendingReplacement .finishFraChoice
          else if g.anyContinuationGrantsPriorityFwd &&
              g.hasImplicitPriorityContinuationFwd && g.pendingPriority != some prio then
            g := g.change (.pendingPriority (some prio))
          g := g.drainPendingContinuationsFwd
    else if wasPaused then
      g := g.resumePendingReplacementFwd (.restorePending prevPending false none allDeparted none)
    return g

private def finishActivateManaAbilityPicksCore (g : Game) (p : PlayerId) (id : ObjectId) (oname : String)
    (mana : Array ManaType) (picks : Array CostPick) (costIds : Array ObjectId)
    (tap sacrificeSelf : Bool) (activatedIdx : Option Nat) (restriction : Option ManaSpendRestriction)
    (damageYou : Nat) (isMountain : Bool) (prevPending : Pending)
    (exileSelf : Bool := false) (powerUp : Bool := false) (exhaust : Bool := false)
    (riders : Array SpellRiderSpec := #[])
    (wasPaused : Bool := true) (hasFollowingSeq : Bool := false) : Game × Bool := Id.run do
  let abortNow (g0 : Game) : Game × Bool :=
    abortDepartedManaAbilityContCore g0 p prevPending
      (wasPaused := wasPaused) (hasFollowingSeq := hasFollowingSeq)
  let sacOrExileSelf := sacrificeSelf || exileSelf
  if g.over || !g.stillInGame p then
    return abortNow g
  if wasPaused then
    let tapPrePaid := manaSourceTapPaidSinceCkpt g p id
    let srcPayable : Bool :=
      let needTap := tap && !tapPrePaid
      if !needTap && !sacOrExileSelf then true
      else
        match g.findObject? id with
        | some cur =>
          cur.isOnBattlefield && g.controlledBy cur p && (!needTap || !cur.status.tapped)
        | none => false
    if !srcPayable then
      return abortNow g
    let mut checkRest := costIds
    for pick in picks do
      let slice := checkRest.extract 0 pick.count
      if slice.size != pick.count then
        return abortNow g
      for cid in slice do
        let ok :=
          match g.findObject? cid with
          | some co =>
            g.costPickAllows p (some id) pick co
              (tapSource := tap) (sacrificeOrExileSource := sacOrExileSelf)
          | none => false
        if !ok then
          return abortNow g
      checkRest := checkRest.extract pick.count checkRest.size
  let mut g := g
  let mut rest := costIds
  for i in [0:picks.size] do
    if g.over || !g.stillInGame p then
      return abortNow g
    let pick := picks[i]!
    let slice := rest.extract 0 pick.count
    rest := rest.extract pick.count rest.size
    if i > 0 then
      for cid in slice do
        let ok :=
          match g.findObject? cid with
          | some co =>
            g.costPickAllows p (some id) pick co
              (tapSource := tap) (sacrificeOrExileSource := sacOrExileSelf)
          | none => false
        if !ok then
          return abortNow g
    let isBfSacPick : Bool :=
      match pick with
      | .tapUntappedCreature | .tapTwoUntappedArtifacts
      | .exileAnotherCreatureCardFromGraveyard => false
      | _ => true
    if tap && !sacOrExileSelf && isBfSacPick && slice.contains id then
      if let some cur := g.findObject? id then
        if cur.isOnBattlefield && !cur.status.tapped then
          g := g.becomeTapped cur (cause := some (.costPayment .tap p (some id)))
    let (g', pickPaid) := g.payCostPickItemsChecked p (some id) (some id) pick slice
    g := g'
    if let .chooseReplacement .. := g.pending then
      let remPicks := picks.extract (i + 1) picks.size
      g := g.chainPendingReplacement
        (.finishActivateManaAbilityPicks p id oname mana remPicks rest tap sacrificeSelf
          activatedIdx restriction damageYou isMountain prevPending
          exileSelf powerUp exhaust riders)
      return (g, false)
    if !pickPaid then
      return abortNow g
  if g.over || !g.stillInGame p then
    return abortNow g
  let tapAlreadyPaid := manaSourceTapPaidSinceCkpt g p id
  if tap && !tapAlreadyPaid then
    match g.findObject? id with
    | some cur =>
      if !cur.isOnBattlefield || !g.controlledBy cur p || cur.status.tapped then
        return abortNow g
      g := g.becomeTapped cur (cause := some (.costPayment .tap p (some id)))
    | none =>
      return abortNow g
  let srcSnap : EventObject :=
    match g.findObject? id with
    | some src => g.snapshot src
    | none => (g.lastKnownBefore? id).getD default
  if sacrificeSelf then
    match g.findObject? id with
    | some src =>
      if !src.isOnBattlefield || !g.controlledBy src p then
        return abortNow g
      g := g.sacrificeToGraveyard src s!"{(g.player p).name} sacrifices {g.name src}"
        (cause := some (.costPayment .sacrifice p (some id)))
      if let .chooseReplacement .. := g.pending then
        g := g.chainPendingReplacement
          (.finishActivateManaAbilityPostSac p id oname srcSnap mana tap activatedIdx
            restriction damageYou isMountain prevPending powerUp exhaust riders)
        return (g, false)
    | none =>
      return abortNow g
  else if exileSelf then
    match g.findObject? id with
    | some src =>
      if !src.isOnBattlefield || !g.controlledBy src p then
        return abortNow g
      let msg := s!"{(g.player p).name} exiles {g.name src}"
      g := (g.move id .exile none (cause := some (.costPayment .exile p (some id)))).1
      if let .chooseReplacement .. := g.pending then
        g := g.chainPendingReplacement (.finishPostStep (.logExiledIfInExile id msg))
        g := g.chainPendingReplacement
          (.finishActivateManaAbilityPostSac p id oname srcSnap mana tap activatedIdx
            restriction damageYou isMountain prevPending powerUp exhaust riders)
        return (g, false)
      if (g.followMovedToZone? id (· == .exile)).isSome then
        g := g.logMsg msg
    | none =>
      return abortNow g
  return (g.finishActivateManaAbilityPostSac p id oname srcSnap mana tap activatedIdx
    restriction damageYou isMountain prevPending powerUp exhaust riders
    (wasPaused := wasPaused) (hasFollowingSeq := hasFollowingSeq), false)

/-- Execute the remaining `picks`, `{T}`, and `sacrificeSelf` / `exileSelf` steps of a mana
ability before `finishActivateManaAbilityPostSac`, chaining continuations if any
cost step pauses on `Pending.chooseReplacement`. -/
def finishActivateManaAbilityPicks (g : Game) (p : PlayerId) (id : ObjectId) (oname : String)
    (mana : Array ManaType) (picks : Array CostPick) (costIds : Array ObjectId)
    (tap sacrificeSelf : Bool) (activatedIdx : Option Nat) (restriction : Option ManaSpendRestriction)
    (damageYou : Nat) (isMountain : Bool) (prevPending : Pending)
    (exileSelf : Bool := false) (powerUp : Bool := false) (exhaust : Bool := false)
    (riders : Array SpellRiderSpec := #[])
    (wasPaused : Bool := true) (hasFollowingSeq : Bool := false) : Game :=
  (finishActivateManaAbilityPicksCore g p id oname mana picks costIds tap sacrificeSelf
    activatedIdx restriction damageYou isMountain prevPending
    (exileSelf := exileSelf) (powerUp := powerUp) (exhaust := exhaust) (riders := riders)
    (wasPaused := wasPaused) (hasFollowingSeq := hasFollowingSeq)).1

/-- Activate mana ability `idx` of `id` (CR 605.3), adding `mana`, paying
choice costs with `costIds` in order. The mana is added immediately; the
ability doesn't use the stack (CR 605.3b). -/
def activateManaAbility (g : Game) (p : PlayerId) (id : ObjectId) (idx : Nat)
    (mana : Array ManaType) (costIds : Array ObjectId := #[]) : Except String Game := do
  if !g.canActivateManaAbility p then
    throw "You can't activate a mana ability now (CR 605.3a)"
  let some o := g.findObject? id | throw "no such object"
  if !g.controlledBy o p || !o.isOnBattlefield then
    throw "You don't control that permanent"
  let oname := g.name o
  let some d := (g.manaAbilityDefs o)[idx]? | throw s!"{oname} has no such mana ability"
  if !d.output.allows mana then
    throw s!"{oname}'s mana ability can't add that mana"
  let sinceIdx := (g.targetProposalCheckpoint?.map (·.eventsSize)).getD g.events.size
  let sacOrExileSelf := d.sacrificeSelf || d.exileSelf
  if d.tap then
    if o.status.tapped then
      throw s!"{oname} is already tapped"
    if (match g.proposedSpell with
        | some prop =>
          prop.tapSource && prop.sourceId == some id &&
            !g.sourceTappedForCost id (some prop.spellId) sinceIdx
        | none => false) then
      throw s!"{oname} is needed to pay \{T}"
    if (match g.proposedSpell with
        | some prop => prop.teamworkCreatures.contains id
        | none => false) then
      throw s!"{oname} is already chosen to tap for teamwork"
    if g.hasSummoningSickness o && !(g.isCreature o && g.activatesAsThoughHaste p) then
      throw s!"{oname} has summoning sickness (CR 302.6)"
  if sacOrExileSelf then
    if let some prop := g.proposedSpell then
      if (prop.sourceId == some id && g.proposedNeedsBattlefieldSource prop sinceIdx) ||
          prop.teamworkCreatures.contains id ||
          (prop.sneakAttacker == some id && !g.sneakPaid prop.spellId) then
        throw s!"{oname} is needed on the battlefield for the proposed spell or ability"
  if let some lim := d.turnLimit? then
    let used :=
      match d.activatedIdx with
      | some i => g.abilityActivationsThisTurn o.id i (isBoast := d.isBoast)
      | none => g.activationsThisTurn o.id
    if used ≥ lim then
      if lim == 1 then
        throw s!"{oname}'s ability can be activated only once each turn"
      else
        throw s!"{oname}'s ability can be activated no more than {lim} times each turn"
  if d.isPowerUp && g.powerUpsForbidden then
    throw "Power-up abilities can't be activated during this extra turn"
  if let some lim := d.lifetimeLimit? then
    let effLim := if d.isPowerUp then g.powerUpActivationLimit p else lim
    let used :=
      match d.activatedIdx with
      | some i => g.abilityActivationsSinceEntered o.id i (isPowerUp := d.isPowerUp) (isExhaust := d.isExhaust)
      | none =>
        if d.isPowerUp then Nat.max (g.powerUpActivations o.id) (if g.powerUpUsed o.id then 1 else 0)
        else if d.isExhaust && g.exhaustUsed o.id then 1
        else 0
    if used ≥ effLim then
      if d.isExhaust then
        throw s!"{oname}'s exhaust ability can be activated only once (CR 702.177)"
      else if d.isPowerUp then
        throw s!"{oname}'s power-up ability can be activated only once"
      else
        throw s!"{oname}'s ability can be activated only once"
  if let some ab := d.sourceAbility then
    match ab.timing with
    | .sorcery | .loyalty =>
      if !g.asSorcery? p then
        throw s!"{oname}'s ability can be activated only as a sorcery"
    | .instant => pure ()
    if let some cond := ab.condition? then
      if !EvalExpr.evalActivationCondition g p o.id (some cond) then
        if cond == .isYourTurn then
          throw s!"{oname}'s ability can be activated only during your turn"
        else if cond == ActivatedAbility.condEnteredThisTurnOrControlBasicLand then
          throw s!"{oname}'s colored mana ability can be activated only if this land entered this turn or if you control a basic land"
        else
          throw s!"{oname}'s ability can't be activated now (its \"Activate only if\" condition isn't met)"
  if d.removeStoryCounter then
    if o.status.story == 0 then
      throw s!"{oname} doesn't have a story counter to remove"
    if let some prop := g.proposedSpell then
      if prop.sourceId == some id && prop.activation.any (·.cost.removeStoryCounter) &&
          !g.sourceCounterCostPaidFor id (some prop.spellId) .removeCounters (some .story) sinceIdx &&
          o.status.story ≤ 1 then
        throw s!"{oname}'s story counter is needed for the proposed ability"
  if d.removeIndestructibleCounter then
    if o.status.indestructibleCounters == 0 then
      throw s!"{oname} doesn't have an indestructible counter to remove"
    if let some prop := g.proposedSpell then
      if prop.sourceId == some id && prop.activation.any (·.cost.removeIndestructibleCounter) &&
          !g.sourceCounterCostPaidFor id (some prop.spellId) .removeCounters (some .indestructible) sinceIdx &&
          o.status.indestructibleCounters ≤ 1 then
        throw s!"{oname}'s indestructible counter is needed for the proposed ability"
  if !g.costPicksPayable p (some id) d.picks
      (tapSource := d.tap) (sacrificeOrExileSource := sacOrExileSelf) then
    throw s!"{oname}'s ability has a cost that can't be paid"
  let need := d.picks.foldl (fun acc pick => acc + pick.count) 0
  if costIds.size != need || costIds.toList.eraseDups.length != costIds.size then
    throw s!"Choose what to {String.intercalate " and " (d.picks.map (·.phrase)).toList}"
  let mut checkRest := costIds
  for pick in d.picks do
    let slice := checkRest.extract 0 pick.count
    let isTapPick := pick == .tapUntappedCreature || pick == .tapTwoUntappedArtifacts
    let isNonBfPick := isTapPick || pick == .exileAnotherCreatureCardFromGraveyard
    for cid in slice do
      let some co := g.findObject? cid | throw "no such object"
      if !g.costPickAllows p (some id) pick co
          (tapSource := d.tap) (sacrificeOrExileSource := sacOrExileSelf) then
        throw s!"{g.name co} can't be used to {pick.phrase}"
      if let some prop := g.proposedSpell then
        if isTapPick &&
            ((prop.sourceId == some cid && prop.tapSource &&
              !g.sourceTappedForCost cid (some prop.spellId) sinceIdx) ||
              prop.teamworkCreatures.contains cid) then
          throw s!"{g.name co} is already reserved to tap for the proposed spell or ability"
        if !isNonBfPick && co.isOnBattlefield &&
            ((prop.sourceId == some cid && g.proposedNeedsBattlefieldSource prop sinceIdx) ||
              prop.teamworkCreatures.contains cid ||
              (prop.sneakAttacker == some cid && !g.sneakPaid prop.spellId)) then
          throw s!"{g.name co} is needed on the battlefield for the proposed spell or ability"
    checkRest := checkRest.extract pick.count checkRest.size
  let pl := g.player p
  let effCost := g.manaAbilityEffectiveCost p o d
  let abSpend := ManaSpend.forAbility (g.types o) (g.supertypes o) (g.subtypes o)
  let spentUnits? ←
    if effCost.includesManaPayment then
      match pl.manaPool.payUnits? effCost abSpend with
      | some (_, spentUnits) => pure (some spentUnits)
      | none => throw s!"{pl.name} cannot pay {effCost}"
    else pure none
  if !g.canPayLife p d.payLife then
    throw s!"{pl.name} cannot pay {d.payLife} life"
  let prevPending := g.pending
  let isMountain := g.hasSubtype o .mountain && d.tap && !mana.isEmpty
  let needsManaCkpt :=
    !d.picks.isEmpty || sacOrExileSelf || d.removeStoryCounter ||
      d.removeIndestructibleCounter || d.putStunCounterOnSource
  let hadOuterCkpt := g.proposalCheckpoint.isSome
  let mut g := g
  if needsManaCkpt then
    g := g.change .saveProposalCheckpoint
  if hadOuterCkpt then
    g := g.change (.beginProposalAction (.manaAbility (some id)))
  let outerCont? : Option PendingReplacement :=
    if prevPending == .none then none else g.pendingReplacement
  if prevPending == .none then
    if let some outer := g.pendingReplacement then
      if g.continuations.isEmpty then
        g := g.change (.pushContinuationFrame {})
      g := g.changes #[.pendingReplacement none, .pushOuterPendingReplacement outer]
  else if outerCont?.isSome then
    g := g.change (.pendingReplacement none)
  if let some spentUnits := spentUnits? then
    g := g.record (GameEvent.manaSpent g.turnNumber p spentUnits (some id)
      (cause := some (.costPayment .mana p (some id))))
  g ← g.payLifeCost p d.payLife (forObject := some id)
  if d.removeStoryCounter then
    let some curSrc := g.findObject? id | throw s!"{oname} is no longer on the battlefield"
    if !curSrc.isOnBattlefield || !g.controlledBy curSrc p || curSrc.status.story == 0 then
      throw s!"{oname} doesn't have a story counter to remove"
    let srcName := g.name curSrc
    g := g.recordRemoveCounters id .story 1 (byPlayer := some p)
      (cause := some (.costPayment .removeCounters p (some id)))
    g := g.logMsg s!"{(g.player p).name} removes a story counter from {srcName}"
  if d.removeIndestructibleCounter then
    let some curSrc := g.findObject? id | throw s!"{oname} is no longer on the battlefield"
    if !curSrc.isOnBattlefield || !g.controlledBy curSrc p || curSrc.status.indestructibleCounters == 0 then
      throw s!"{oname} doesn't have an indestructible counter to remove"
    g ← g.payRemoveIndestructibleCounter curSrc (some id)
  if d.putStunCounterOnSource then
    let some curSrc := g.findObject? id | throw s!"{oname} is no longer on the battlefield"
    if !curSrc.isOnBattlefield || !g.controlledBy curSrc p then
      throw s!"{oname} is no longer on the battlefield"
    g := g.putCountersDeferredLog id .stun 1 (some p) (.playerPutsOn p)
      (cause := some (.costPayment .putCounters p (some id)))
    if let .chooseReplacement .. := g.pending then
      g := g.chainPendingReplacement
        (.finishActivateManaAbilityPicks p id oname mana d.picks costIds d.tap d.sacrificeSelf
          d.activatedIdx d.restriction d.damageYou isMountain prevPending
          d.exileSelf d.isPowerUp d.isExhaust d.riders)
      if let some outer := outerCont? then
        g := g.chainPendingReplacement outer
      return g
  let (gAfter, cleanSyncAbort) :=
    finishActivateManaAbilityPicksCore g p id oname mana d.picks costIds d.tap d.sacrificeSelf
      d.activatedIdx d.restriction d.damageYou isMountain prevPending
      (exileSelf := d.exileSelf) (powerUp := d.isPowerUp) (exhaust := d.isExhaust) (riders := d.riders)
      (wasPaused := false) (hasFollowingSeq := outerCont?.isSome)
  if cleanSyncAbort then
    throw s!"{oname}'s ability has a cost that can't be paid"
  g := gAfter
  if let some outer := outerCont? then
    g := g.chainPendingReplacement outer
  return g

/-- Index of the highest-ranked currently usable mana ability of `o` that can
add `mana` by tapping alone, or without object-choice costs when `plainOnly` is
false. Prefers non-empty outputs, abilities spendable on `prop?` (or
`g.proposedSpell`), unrestricted abilities (or higher yield when `prop?` is
active), higher mana yield, plain `{T}` costs, and earlier indices. -/
def manaAbilityIndexFor (g : Game) (o : GameObject) (mana : ManaType) (plainOnly : Bool := true)
    (prop? : Option ProposedSpell := none) : Option Nat :=
  let p := (g.controllerOf o).getD o.owner
  let defs := g.manaAbilityDefs o
  let activeProp? := prop? <|> g.proposedSpell
  let sinceIdx := (g.targetProposalCheckpoint?.map (·.eventsSize)).getD g.events.size
  let abSpend := ManaSpend.forAbility (g.types o) (g.supertypes o) (g.subtypes o)
  let rankBetter
      (a b : Bool × Bool × Nat × Bool × Nat × Bool) : Bool :=
    let (neA, spA, y1A, unA, y2A, plA) := a
    let (neB, spB, y1B, unB, y2B, plB) := b
    if neA != neB then neA
    else if spA != spB then spA
    else if y1A != y1B then y1A > y1B
    else if unA != unB then unA
    else if y2A != y2B then y2A > y2B
    else plA && !plB
  Id.run do
    let mut best? : Option (Nat × (Bool × Bool × Nat × Bool × Nat × Bool)) := none
    for i in [0 : defs.size] do
      let d := defs[i]!
      let isPlain := g.isPlainTapManaAbilityDef p o d
      if g.manaAbilityDefUsable p o d &&
          (if plainOnly then isPlain else d.picks.isEmpty) then
        if let some added := d.output.withType mana then
          let tapOk :=
            !d.tap ||
              (!o.status.tapped &&
                !(g.hasSummoningSickness o && !(g.isCreature o && g.activatesAsThoughHaste p)))
          let costOk :=
            plainOnly ||
              let effCost := g.manaAbilityEffectiveCost p o d
              !effCost.includesManaPayment ||
                ((g.player p).manaPool.payUnits? effCost abSpend).isSome
          let propOk :=
            match activeProp? with
            | none => true
            | some prop =>
              (!d.tap ||
                !((prop.tapSource && prop.sourceId == some o.id &&
                    !g.sourceTappedForCost o.id (some prop.spellId) sinceIdx) ||
                  prop.teamworkCreatures.contains o.id)) &&
              (!(d.sacrificeSelf || d.exileSelf) ||
                !((prop.sourceId == some o.id && g.proposedNeedsBattlefieldSource prop sinceIdx) ||
                  prop.teamworkCreatures.contains o.id ||
                  (prop.sneakAttacker == some o.id && !g.sneakPaid prop.spellId))) &&
              (!d.removeStoryCounter ||
                !(prop.sourceId == some o.id && prop.activation.any (·.cost.removeStoryCounter) &&
                  !g.sourceCounterCostPaidFor o.id (some prop.spellId) .removeCounters (some .story) sinceIdx &&
                  o.status.story ≤ 1)) &&
              (!d.removeIndestructibleCounter ||
                !(prop.sourceId == some o.id && prop.activation.any (·.cost.removeIndestructibleCounter) &&
                  !g.sourceCounterCostPaidFor o.id (some prop.spellId) .removeCounters (some .indestructible) sinceIdx &&
                  o.status.indestructibleCounters ≤ 1))
          if tapOk && costOk && propOk then
            let nonEmpty := !added.isEmpty
            let spendable :=
              match activeProp? with
              | some prop => g.restrictionAllowsProposed d.restriction prop
              | none => true
            let unrestricted := d.restriction.isNone
            let yld := added.size
            let key :=
              (nonEmpty, spendable, (if activeProp?.isSome then yld else 0),
                unrestricted, yld, isPlain)
            match best? with
            | none => best? := some (i, key)
            | some (_, bestKey) =>
              if rankBetter key bestKey then
                best? := some (i, key)
    return best?.map (·.1)

/-- Tap `id` for `mana` with the best currently usable mana ability that can add
it (CR 605.3). Abilities that need other choices use `activateManaAbility`. -/
def tapForMana (g : Game) (p : PlayerId) (id : ObjectId) (mana : ManaType) : Except String Game := do
  let some o := g.findObject? id | throw "no such object"
  let defs := g.manaAbilityDefs o
  let some i := g.manaAbilityIndexFor o mana true <|> g.manaAbilityIndexFor o mana false
    | do
      if let some d := defs.find? (fun d =>
          g.manaAbilityDefUsable p o d && d.picks.isEmpty && (d.output.withType mana).isSome) then
        if !g.canActivateManaAbility p then
          throw "You can't activate a mana ability now (CR 605.3a)"
        let oname := g.name o
        let sinceIdx := (g.targetProposalCheckpoint?.map (·.eventsSize)).getD g.events.size
        if d.tap then
          if o.status.tapped then
            throw s!"{oname} is already tapped"
          if let some prop := g.proposedSpell then
            if prop.tapSource && prop.sourceId == some id &&
                !g.sourceTappedForCost id (some prop.spellId) sinceIdx then
              throw s!"{oname} is needed to pay \{T}"
            if prop.teamworkCreatures.contains id then
              throw s!"{oname} is already chosen to tap for teamwork"
          if g.hasSummoningSickness o && !(g.isCreature o && g.activatesAsThoughHaste p) then
            throw s!"{oname} has summoning sickness (CR 302.6)"
        if d.sacrificeSelf || d.exileSelf then
          if let some prop := g.proposedSpell then
            if (prop.sourceId == some id && g.proposedNeedsBattlefieldSource prop sinceIdx) ||
                prop.teamworkCreatures.contains id ||
                (prop.sneakAttacker == some id && !g.sneakPaid prop.spellId) then
              throw s!"{oname} is needed on the battlefield for the proposed spell or ability"
        if d.removeStoryCounter then
          if let some prop := g.proposedSpell then
            if prop.sourceId == some id && prop.activation.any (·.cost.removeStoryCounter) &&
                !g.sourceCounterCostPaidFor id (some prop.spellId) .removeCounters (some .story) sinceIdx &&
                o.status.story ≤ 1 then
              throw s!"{oname}'s story counter is needed for the proposed ability"
        if d.removeIndestructibleCounter then
          if let some prop := g.proposedSpell then
            if prop.sourceId == some id && prop.activation.any (·.cost.removeIndestructibleCounter) &&
                !g.sourceCounterCostPaidFor id (some prop.spellId) .removeCounters (some .indestructible) sinceIdx &&
                o.status.indestructibleCounters ≤ 1 then
              throw s!"{oname}'s indestructible counter is needed for the proposed ability"
        let effCost := g.manaAbilityEffectiveCost p o d
        if effCost.includesManaPayment then
          throw s!"{(g.player p).name} cannot pay {effCost}"
      if defs.any (fun d =>
          d.sourceAbility.any (·.condition? == some ActivatedAbility.condEnteredThisTurnOrControlBasicLand) &&
          (d.output.withType mana).isSome) && !g.canUseEnteredOrBasicAdd o then
        throw s!"{g.nameWithToken o}'s colored mana ability can be activated only if this land entered this turn or if you control a basic land"
      throw s!"{g.nameWithToken o} cannot produce {mana}"
  let some d := defs[i]? | throw s!"{g.nameWithToken o} cannot produce {mana}"
  let some added := d.output.withType mana | throw s!"{g.nameWithToken o} cannot produce {mana}"
  g.activateManaAbility p id i added

/-- Base mana types `o`'s plain `{T}` mana ability itself adds when tapped for
`mana` (excluding `.mountainExtraRed` triggered `{R}`). -/
def baseManaTypesFromTap (g : Game) (o : GameObject) (mana : ManaType)
    (prop? : Option ProposedSpell := none) : Array ManaType :=
  match g.manaAbilityIndexFor o mana (plainOnly := true) (prop? := prop?) with
  | some i =>
    match (g.manaAbilityDefs o)[i]? with
    | some d => (d.output.withType mana).getD #[]
    | none => #[]
  | none => #[]

/-- Extra unrestricted `{R}` added by `.mountainExtraRed` when `o` is tapped
for non-empty `baseAdded` mana (CR 106.1 / 605.4a). -/
def extraMountainRedFromTap (g : Game) (o : GameObject) (baseAdded : Array ManaType) :
    Array ManaType :=
  let p := (g.controllerOf o).getD o.owner
  if baseAdded.isEmpty || !g.hasSubtype o .mountain || !g.stillInGame p then #[]
  else Array.replicate (g.mountainExtraRedThisTurn p) (.colored .red)

/-- Mana types `o` adds when tapped for `mana` with a plain `{T}` ability
(including mixed-type `.fixed` outputs such as `{U}{R}` and `.mountainExtraRed`
extra `{R}`, CR 106.1 / 605.3b / 605.4a). -/
def manaTypesFromTap (g : Game) (o : GameObject) (mana : ManaType)
    (prop? : Option ProposedSpell := none) : Array ManaType :=
  let base := g.baseManaTypesFromTap o mana (prop? := prop?)
  base ++ g.extraMountainRedFromTap o base

/-- Mana count `o` adds when tapped for `mana` with a plain `{T}` ability. -/
def manaFromTap (g : Game) (o : GameObject) (mana : ManaType)
    (prop? : Option ProposedSpell := none) : Nat :=
  (g.manaTypesFromTap o mana (prop? := prop?)).size

/-- Restriction on the base mana `o` adds when tapped for `mana` with a plain
`{T}` ability. -/
def tapRestrictionOf (g : Game) (o : GameObject) (mana : ManaType)
    (prop? : Option ProposedSpell := none) : Option ManaSpendRestriction :=
  match g.manaAbilityIndexFor o mana (plainOnly := true) (prop? := prop?) with
  | some i => (g.manaAbilityDefs o)[i]?.bind (·.restriction)
  | none => none

/-- Spell riders on the base mana `o` adds when tapped for `mana` with a plain
`{T}` ability (CR 106.6 / 106.12). -/
def tapRidersOf (g : Game) (o : GameObject) (mana : ManaType)
    (prop? : Option ProposedSpell := none) : Array SpellRiderSpec :=
  match g.manaAbilityIndexFor o mana (plainOnly := true) (prop? := prop?) with
  | some i => ((g.manaAbilityDefs o)[i]?.map (·.riders)).getD #[]
  | none => #[]

/-- Add the mana produced by tapping `o` for `mana` to `pool`, applying `o`'s
ability restriction and riders only to `baseManaTypesFromTap` and leaving
`extraMountainRedFromTap` unrestricted (CR 106.1 / 106.6 / 605.4a). -/
def addTapManaToPool (g : Game) (pool : ManaPool) (o : GameObject) (mana : ManaType)
    (prop? : Option ProposedSpell := none) : ManaPool :=
  let base := g.baseManaTypesFromTap o mana (prop? := prop?)
  let r := g.tapRestrictionOf o mana (prop? := prop?)
  let riders := g.tapRidersOf o mana (prop? := prop?)
  let extra := g.extraMountainRedFromTap o base
  addRestrictedMana (addRestrictedMana pool base r riders) extra none

/-- Concrete plain `{T}` mana activation choice on a permanent, supporting both
single-type `.tapForMana` choices and mixed-color `.combination` tuples via
`.activateManaAbility` (CR 106.1 / 605.3b). -/
structure TapManaChoice where
  abilityIdx : Nat
  baseAdded : Array ManaType
  extraRed : Array ManaType := #[]
  restriction : Option ManaSpendRestriction := none
  riders : Array SpellRiderSpec := #[]
  /-- `some t` when `.tapForMana o.id t` executes this exact choice; `none` when
  `.activateManaAbility o.id abilityIdx baseAdded #[]` is required (e.g. a
  mixed-color `.combination` tuple). -/
  singleTapType? : Option ManaType := none
deriving DecidableEq, Repr, Inhabited

def TapManaChoice.totalSize (ch : TapManaChoice) : Nat :=
  ch.baseAdded.size + ch.extraRed.size

def TapManaChoice.primaryType (ch : TapManaChoice) : ManaType :=
  ch.singleTapType?.getD (ch.baseAdded[0]?.getD .colorless)

def TapManaChoice.applyToPool (ch : TapManaChoice) (pool : ManaPool) : ManaPool :=
  addRestrictedMana (addRestrictedMana pool ch.baseAdded ch.restriction ch.riders) ch.extraRed none

/-- Distinct plain `{T}` mana activation choices for `(o, types)` toward `cost`,
including mixed-color `.combination ts n` tuples (with zero-requirement colors
collapsed to avoid combinatorial blow-up). -/
def tapChoicesForSource (g : Game) (o : GameObject) (types : Array ManaType)
    (cost : ManaCost) (dedupSingleTypes : Array ManaType → Array ManaType := id)
    (prop? : Option ProposedSpell := none) : Array TapManaChoice :=
  let p := (g.controllerOf o).getD o.owner
  let defs := g.manaAbilityDefs o
  let activeProp? := prop? <|> g.proposedSpell
  let sinceIdx := (g.targetProposalCheckpoint?.map (·.eventsSize)).getD g.events.size
  let singleTs := dedupSingleTypes types
  let singleChoices : Array TapManaChoice :=
    singleTs.filterMap fun t =>
      match g.manaAbilityIndexFor o t (plainOnly := true) (prop? := prop?) with
      | none => none
      | some i =>
        match defs[i]? with
        | none => none
        | some d =>
          let base := (d.output.withType t).getD #[]
          if base.isEmpty then none
          else
            some {
              abilityIdx := i
              baseAdded := base
              extraRed := g.extraMountainRedFromTap o base
              restriction := d.restriction
              riders := d.riders
              singleTapType? := some t
            }
  let tapPrereqOk : Bool :=
    !o.status.tapped &&
      !(g.hasSummoningSickness o && !(g.isCreature o && g.activatesAsThoughHaste p)) &&
      (match activeProp? with
       | none => true
       | some prop =>
         !((prop.tapSource && prop.sourceId == some o.id &&
             !g.sourceTappedForCost o.id (some prop.spellId) sinceIdx) ||
           prop.teamworkCreatures.contains o.id))
  if !tapPrereqOk then singleChoices
  else Id.run do
    let mut out := singleChoices
    for i in [0 : defs.size] do
      let d := defs[i]!
      if g.isPlainTapManaAbilityDef p o d && g.manaAbilityDefUsable p o d then
        if let .combination comboTs n := d.output then
          if n ≥ 2 then
            let extraSample := g.extraMountainRedFromTap o #[comboTs[0]?.getD .colorless]
            let spendOk :=
              match activeProp? with
              | none => true
              | some prop =>
                g.restrictionAllowsProposed d.restriction prop ||
                  (!extraSample.isEmpty && g.restrictionAllowsProposed none prop)
            if spendOk then
              let allowedTs := comboTs.filter types.contains
              let collapsedTs : Array ManaType := Id.run do
                let mut acc : Array ManaType := #[]
                let mut seenZero : Bool := false
                for t in allowedTs do
                  match t with
                  | .colored c =>
                    if cost.symbolsIncludingColor c == 0 then
                      if !seenZero then
                        seenZero := true
                        acc := acc.push t
                    else
                      acc := acc.push t
                  | .colorless =>
                    acc := acc.push t
                return acc
              for tup in ManaOutput.multisetChoices collapsedTs n do
                if !tup.isEmpty then
                  let alreadySingle :=
                    out.any (fun ch => ch.baseAdded == tup && ch.restriction == d.restriction && ch.riders == d.riders)
                  if !alreadySingle then
                    out := out.push {
                      abilityIdx := i
                      baseAdded := tup
                      extraRed := g.extraMountainRedFromTap o tup
                      restriction := d.restriction
                      riders := d.riders
                      singleTapType? := none
                    }
    return out

end Game
end Mtg.Engine

