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
  let env : EvalEnv := { controller := (g.controllerOf o).getD o.owner, sourceId := some o.id }
  (g.staticAbilities o).any fun ab =>
    ab.anyRule fun cond? r =>
      match r with
      | .player (.extraAbilityActivation .powerUp _ n) =>
        n > 0 && cond?.all (EvalExpr.evalCondition g env)
      | _ => false

/-- Extra lifetime power-up activations granted by Wonder Man (MSH). -/
def powerUpActivationLimit (g : Game) (p : PlayerId) : Nat :=
  let extra :=
    (g.permanentsOf p).foldl (fun acc o =>
      let env : EvalEnv := { controller := p, sourceId := some o.id }
      (g.staticAbilities o).foldl (fun acc ab =>
        match ab with
        | .ruleModifying cond? rule =>
          if !cond?.all (EvalExpr.evalCondition g env) then acc
          else
            rule.flatten.foldl (fun acc rm =>
              match rm with
              | .player (.extraAbilityActivation .powerUp _ n) => acc + n
              | _ => acc) acc
        | _ => acc) acc) 0
  1 + extra

/-- Generic mana subtracted from other creatures' power-up costs by Hulk
(MSH ruling 127: only generic mana). -/
def hulkPowerUpGenericReduction (g : Game) (p : PlayerId) (sourceId : ObjectId) : Nat :=
  let srcObj? := g.findObject? sourceId
  g.battlefield.foldl (fun acc o =>
    let srcCtrl := (g.controllerOf o).getD o.owner
    let env : EvalEnv := { controller := srcCtrl, sourceId := some o.id }
    (g.staticAbilities o).foldl (fun acc ab =>
      match ab with
      | .costModifier cond? (.abilities act (some .powerUp) sc none none) (.reduceGeneric amt) =>
        if EvalExpr.matchesPlayerFilter g env act p &&
            cond?.all (EvalExpr.evalCondition g env) &&
            srcObj?.any (fun s => EvalExpr.evalObjectPred g env (.live s) sc.pred) then
          acc + (EvalExpr.evalValue g env amt).toNat
        else acc
      | _ => acc) acc) 0

def activationManaCost (g : Game) (p : PlayerId) (ab : ActivatedAbility)
    (source : Option GameObject := none) (chosenX : Option Nat := none)
    (targets : Array Target := #[]) : ManaCost :=
  let withX (cost : ManaCost) : ManaCost :=
    match chosenX with
    | some x => cost.substituteX x
    | none => cost
  let firstEquipFree :=
    ab.isEquip && g.loggedEquipActivations p == 0 &&
      g.battlefield.any (fun o =>
        let srcCtrl := (g.controllerOf o).getD o.owner
        let env : EvalEnv := { controller := srcCtrl, sourceId := some o.id }
        (g.staticAbilities o).any fun sab =>
          match sab with
          | .costModifier cond? (.abilities act (some (.equip _)) sc none (some 1)) .alternativeFree =>
            EvalExpr.matchesPlayerFilter g env act p &&
              cond?.all (EvalExpr.evalCondition g env) &&
              source.all (fun s => EvalExpr.evalObjectPred g env (.live s) sc.pred)
          | _ => false)
  let generalAbRed : Nat :=
    if ab.isPowerUp then 0
    else
      g.battlefield.foldl (fun acc o =>
        let srcCtrl := (g.controllerOf o).getD o.owner
        let env : EvalEnv := { controller := srcCtrl, sourceId := some o.id }
        (g.staticAbilities o).foldl (fun acc sab =>
          match sab with
          | .costModifier cond? (.abilities act tag? sc none none) (.reduceGeneric amt) =>
            let tagOk := match tag? with
              | none => true
              | some t => ab.tag? == some t || (match t with | .equip _ => ab.isEquip | _ => false)
            if tagOk && EvalExpr.matchesPlayerFilter g env act p &&
                cond?.all (EvalExpr.evalCondition g env) &&
                source.any (fun s => EvalExpr.evalObjectPred g env (.live s) sc.pred) then
              acc + (EvalExpr.evalValue g env amt).toNat
            else acc
          | _ => acc) acc) 0
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
    else if declRed + generalAbRed > 0 then
      (withX ab.cost.mana).reduceGeneric (declRed + generalAbRed)
    else withX ab.cost.mana
  ManaCost.afterReduction ab.cost.mana cost

/-- True when `ab` has a mana cost that `p` would not pay to activate it. -/
def activatesWithoutPayingManaCost (g : Game) (p : PlayerId) (ab : ActivatedAbility)
    (source : Option GameObject := none) : Bool :=
  ab.cost.mana.includesManaPayment && !(g.activationManaCost p ab source).includesManaPayment

/-- One mode of a modal CR 605.1a mana ability (CR 605.1a / 700.2a). -/
structure ManaAbilityMode where
  effect : Effect
  output? : Option ManaOutput := none
  restriction : Option ManaSpendRestriction := none
  riders : Array SpellRiderSpec := #[]
  damageYou : Nat := 0
deriving Inhabited

/-- A mana ability of an object (CR 605.1a). -/
structure ManaAbilityDef where
  output : ManaOutput
  tap : Bool := true
  cost : ManaCost := ManaCost.empty
  payLife : Nat := 0
  sacrificeSelf : Bool := false
  exileSelf : Bool := false
  fromHand : Bool := false
  fromGraveyard : Bool := false
  exileSelfFromHand : Bool := false
  exileSelfFromGraveyard : Bool := false
  discardSelf : Bool := false
  removeStoryCounter : Bool := false
  removeIndestructibleCounter : Bool := false
  removeAnyNumberPlusOne : Bool := false
  putStunCounterOnSource : Bool := false
  crewPower? : Option Nat := none
  crewExcludesSelf : Bool := true
  exileManaSymbols? : Option (Option Color × Nat × ObjectPred) := none
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
  /-- Per-mode outputs and effects for modal CR 605.1a mana abilities. -/
  modeChoices : Array ManaAbilityMode := #[]
  /-- Optional non-pure-mana effect resolved directly without using the stack. -/
  extraEffect? : Option Effect := none
  /-- True when the source `CostSpec` contains a `CostItem` (or duplicate
  single-slot item) not projected and executed by `activateManaAbility`. -/
  hasUnmodeledCostItem : Bool := false
deriving Inhabited

/-- Whether paying `d`'s cost moves its source out of its current zone. -/
def ManaAbilityDef.removesSource (d : ManaAbilityDef) : Bool :=
  d.sacrificeSelf || d.exileSelf || d.exileSelfFromHand ||
    d.exileSelfFromGraveyard || d.discardSelf

/-- Whether `d` has variable/multi-object extra costs requiring `activateManaAbility`. -/
def ManaAbilityDef.hasExtraInteractiveCost (d : ManaAbilityDef) : Bool :=
  d.removeAnyNumberPlusOne || d.crewPower?.isSome || d.exileManaSymbols?.isSome

/-- Non-battlefield zone from which `d` exiles its source, if any. -/
def ManaAbilityDef.exileFromZone? (d : ManaAbilityDef) : Option ZoneKind :=
  if d.exileSelfFromHand then some .hand
  else if d.exileSelfFromGraveyard then some .graveyard
  else none

/-- Every distinct non-empty mana production tuple `d` can produce across all
modes, paired with its spending restriction and spell riders. -/
def ManaAbilityDef.allChoicesFor (d : ManaAbilityDef)
    (dedupTypes : Array ManaType → Array ManaType := id) :
    Array (Array ManaType × Option ManaSpendRestriction × Array SpellRiderSpec) :=
  if !d.modeChoices.isEmpty then
    d.modeChoices.foldl (fun acc m =>
      match m.output? with
      | some out =>
        acc ++ (out.allChoices dedupTypes).map (fun ts => (ts, m.restriction, m.riders))
      | none => acc) #[]
  else
    (d.output.allChoices dedupTypes).map (fun ts => (ts, d.restriction, d.riders))

private def uniqMana (ts : Array ManaType) : Array ManaType :=
  ts.foldl (fun acc t => if acc.contains t then acc else acc.push t) #[]

/-- True when `item` is projected onto `ManaAbilityDef` and enforced/executed
by `manaAbilityDefUsable` and `activateManaAbility`. -/
private def manaAbilityCostItemModeled : CostItem → Bool
  | .mana _ => true
  | .tapSelf => true
  | .payLife (.const n) => n ≥ 0
  | .sacrifice (.count (.const 1)) .self => true
  | .sacrifice (.count (.const n)) (.filter _) => n > 0
  | .discard (.count (.const 1)) .self => true
  | .discard (.count (.const n)) .hand => n > 0
  | .discard (.count (.const n)) (.matching _) => n > 0
  | .exile (.count (.const 1)) zones .self false =>
    zones.zones.size == 1 &&
      (zones.zones.contains .battlefield || zones.zones.contains .hand || zones.zones.contains .graveyard)
  | .exile (.totalManaSymbolsAtLeast _ (.const n)) zones (.filter _) false =>
    n ≥ 0 && zones.zones == #[.graveyard]
  | .exile (.count (.const n)) zones (.filter _) false =>
    n > 0 && !zones.zones.isEmpty &&
      zones.zones.all (fun z => z == .graveyard || z == .hand || z == .battlefield)
  | .tapObjects (.count (.const n)) _ => n > 0
  | .tapObjects (.totalPowerAtLeast (.const n)) pred =>
    n ≥ 0 &&
      (pred == .all #[.hasType .creature, .tapped false, .controlledBy .you] ||
        pred == .all #[.otherThan .this, .hasType .creature, .tapped false, .controlledBy .you] ||
        pred == .all #[.hasType .creature, .otherThan .this, .tapped false, .controlledBy .you])
  | .removeCounters (.count (.const 1)) (some .story) .self => true
  | .removeCounters (.count (.const 1)) (some .indestructible) .self => true
  | .removeCounters .anyNumber (some .plusOnePlusOne) .self => true
  | .putCounters (.const 1) .stun .self => true
  | .returnToHand (.count (.const n)) (.filter _) => n > 0
  | .or choices =>
    !choices.isEmpty &&
      choices.all fun cs =>
        match cs.items.toList with
        | [.sacrifice (.count (.const 1)) (.filter _)] => true
        | [.discard (.count (.const 1)) .hand] => true
        | [.discard (.count (.const 1)) (.matching _)] => true
        | _ => false
  | _ => false

/-- True when `c` contains any unmodeled `CostItem` or duplicate single-slot
cost item that `ManaAbilityDef` / `activateManaAbility` cannot execute. -/
private def manaAbilityCostHasUnmodeledItems (c : CostSpec) : Bool :=
  if c.items.any (fun item => !manaAbilityCostItemModeled item) then true
  else
    let cnt (p : CostItem → Bool) : Nat := (c.items.filter p).size
    let isSacOtherCreatArt : CostItem → Bool
      | .sacrifice (.count (.const 1)) (.filter (.all #[.otherThan .this, .any #[.hasType .creature, .hasType .artifact]]))
      | .sacrifice (.count (.const 1)) (.filter (.all #[.otherThan .this, .any #[.hasType .artifact, .hasType .creature]])) => true
      | _ => false
    cnt (fun | .tapObjects (.totalPowerAtLeast _) _ => true | _ => false) > 1 ||
      cnt (fun | .exile (.totalManaSymbolsAtLeast _ _) _ _ _ => true | _ => false) > 1 ||
      cnt (fun | .removeCounters (.count (.const 1)) (some .story) .self => true | _ => false) > 1 ||
      cnt (fun | .removeCounters (.count (.const 1)) (some .indestructible) .self => true | _ => false) > 1 ||
      cnt (fun | .removeCounters .anyNumber (some .plusOnePlusOne) .self => true | _ => false) > 1 ||
      cnt (fun | .putCounters (.const 1) .stun .self => true | _ => false) > 1 ||
      cnt isSacOtherCreatArt > 1

/-- Mana a land can produce from its evaluated Layer-6 battlefield mana abilities
(CR 106.7 / 305.6 / 305.7 / 605.1a / 613.1f). Abilities that themselves query
"could produce" (`ManaSpec.usesLandsCouldProduce`) are skipped so two such
lands do not look at each other. -/
def intrinsicLandMana (g : Game) (o : GameObject) : Array ManaType :=
  if !o.isOnBattlefield || !g.isLand o then #[]
  else
    let p := (g.controllerOf o).getD o.owner
    let produced := (g.activatedAbilitiesOf o).foldl (fun acc ab =>
      if !isManaActivation ab || ab.isFromHand || ab.isFromGraveyard ||
          !EvalExpr.evalActivationCondition g p o.id ab.condition? then acc
      else
        let maxX := if ab.cost.removeAnyNumberPlusOne then o.status.plusOnePlusOne else 0
        let env : EvalEnv := { controller := p, sourceId := some o.id, chosenX := maxX }
        ab.allModes.foldl (fun acc m =>
          match m.manaProduction? with
          | some mp =>
            if mp.spec.usesLandsCouldProduce then acc
            else
              let out := EvalExpr.evalManaSpec g env (fun _ _ => #[]) mp.spec
              acc ++ out.producibleTypes
          | none => acc) acc) #[]
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

/-- Evaluate one mode of an activated mana ability on `o` at `chosenX`. -/
private def evalActivatedManaMode (g : Game) (o : GameObject) (p : PlayerId)
    (mode : Effect) (chosenX : Nat := 0) :
    ManaAbilityMode :=
  match mode.manaProduction? with
  | some mp =>
    let env : EvalEnv := { controller := p, sourceId := some o.id, chosenX := chosenX }
    { effect := mode
      output? := some (g.evalManaSpec env mp.spec)
      restriction := mp.restriction
      riders := mp.allRiders
      damageYou := mp.damageYou }
  | none => { effect := mode }

/-- Build a `ManaAbilityDef` from an evaluated Layer-6 `ActivatedAbility`
satisfying CR 605.1a (`isManaActivation`). Always returns `some` whenever
`isManaActivation ab` holds so no CR 605.1a mana ability is routed to the stack. -/
def manaAbilityDefOfActivated (g : Game) (o : GameObject) (i : Nat)
    (ab : ActivatedAbility) : Option ManaAbilityDef :=
  if !isManaActivation ab then none
  else
    let p := (g.controllerOf o).getD o.owner
    let maxX := if ab.cost.removeAnyNumberPlusOne && o.isOnBattlefield then o.status.plusOnePlusOne else 0
    let base : ManaAbilityDef := {
      output := .fixed #[]
      tap := ab.cost.tap
      cost := ab.cost.mana
      payLife := ab.cost.payLife
      sacrificeSelf := ab.cost.sacrificeSource
      exileSelf := ab.cost.exileSourceFromBattlefield
      fromHand := ab.isFromHand
      fromGraveyard := ab.isFromGraveyard
      exileSelfFromHand := ab.cost.exileSourceFromHand
      exileSelfFromGraveyard := ab.cost.exileSourceFromGraveyard
      discardSelf := ab.cost.discardSource
      removeStoryCounter := ab.cost.removeStoryCounter
      removeIndestructibleCounter := ab.cost.removeIndestructibleCounter
      removeAnyNumberPlusOne := ab.cost.removeAnyNumberPlusOne
      putStunCounterOnSource := ab.cost.putStunCounterOnSource
      crewPower? := ab.cost.crewPower?
      crewExcludesSelf := crewExcludesSelf ab.cost
      exileManaSymbols? := ab.cost.exileManaSymbols?
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
      hasUnmodeledCostItem := manaAbilityCostHasUnmodeledItems ab.cost
    }
    if ab.isModal then
      let rawModes := ab.allModes
      let modes := rawModes.map fun mode =>
        evalActivatedManaMode g o p mode (chosenX := maxX)
      let manaOuts := modes.filterMap (·.output?)
      let summaryOut : ManaOutput :=
        if manaOuts.size == 1 then manaOuts[0]!
        else
          let ts := uniqMana (manaOuts.foldl (fun acc out => acc ++ out.producibleTypes) #[])
          if ts.isEmpty then .fixed #[] else .oneOf ts 1
      some { base with output := summaryOut, modeChoices := modes }
    else
      let m0 := evalActivatedManaMode g o p ab.effect (chosenX := maxX)
      match m0.output? with
      | some out =>
        some { base with
          output := out
          restriction := m0.restriction
          riders := m0.riders
          damageYou := m0.damageYou }
      | none =>
        some { base with
          output := .fixed #[]
          extraEffect? := some ab.effect }

/-- Every mana ability `o` has, read exclusively from its evaluated Layer-6
`activatedAbilitiesOf` (CR 305.6 / 305.7 / 605.1a / 613.1f). -/
def manaAbilityDefs (g : Game) (o : GameObject) : Array ManaAbilityDef :=
  let abs := g.activatedAbilitiesOf o
  (List.range abs.size).toArray.filterMap fun i =>
    g.manaAbilityDefOfActivated o i abs[i]!

/-- Re-evaluate a `removeAnyNumberPlusOne` mana ability definition at `chosenX := 0`
(when `o`'s existing +1/+1 counters are reserved for an active proposed spell/ability
cost, CR 605.3a). -/
def manaAbilityDefAtZeroPlusOnes (g : Game) (p : PlayerId) (o : GameObject)
    (d : ManaAbilityDef) : ManaAbilityDef :=
  if !d.removeAnyNumberPlusOne then d
  else
    match d.sourceAbility with
    | none => d
    | some ab =>
      if ab.isModal then
        let modes := ab.allModes.map fun mode =>
          evalActivatedManaMode g o p mode (chosenX := 0)
        let manaOuts := modes.filterMap (·.output?)
        let summaryOut : ManaOutput :=
          if manaOuts.size == 1 then manaOuts[0]!
          else
            let ts := uniqMana (manaOuts.foldl (fun acc out => acc ++ out.producibleTypes) #[])
            if ts.isEmpty then .fixed #[] else .oneOf ts 1
        { d with output := summaryOut, modeChoices := modes }
      else
        let m0 := evalActivatedManaMode g o p ab.effect (chosenX := 0)
        match m0.output? with
        | some out =>
          { d with
            output := out
            restriction := m0.restriction
            riders := m0.riders
            damageYou := m0.damageYou }
        | none =>
          { d with
            output := .fixed #[]
            extraEffect? := some ab.effect }

/-- Effective mana cost of mana ability `d` on `o` for `p`, applying
`activationManaCost` reductions when backed by an `ActivatedAbility`. -/
def manaAbilityEffectiveCost (g : Game) (p : PlayerId) (o : GameObject) (d : ManaAbilityDef) : ManaCost :=
  match d.sourceAbility with
  | some ab => g.activationManaCost p ab (some o)
  | none => d.cost

/-- Number of mana symbols on `card` matching `col?` (`none` counts all symbols). -/
def manaSymbolsCountFor (g : Game) (card : GameObject) (col? : Option Color) : Nat :=
  match col? with
  | some c => (g.baseCard card).manaCost.symbolsIncludingColor c
  | none => (g.baseCard card).manaCost.symbols.size

/-- Whether `card` in `p`'s graveyard satisfies an `exileManaSymbols?` cost predicate. -/
def exileManaSymbolsCardOk (g : Game) (p : PlayerId) (srcId : ObjectId)
    (col? : Option Color) (pred : ObjectPred) (card : GameObject) : Bool :=
  card.zone == .graveyard p && isDiscardableCard card &&
    EvalExpr.evalObjectPred g { controller := p, sourceId := some srcId } (.live card) pred &&
    (match col? with
     | some c => (g.colors card).contains c
     | none => true)

/-- Whether `p` has enough eligible cards in their graveyard to pay an
`exileManaSymbols?` cost (excluding `excludedIds`). -/
def canPayExileManaSymbols (g : Game) (p : PlayerId) (srcId : ObjectId)
    (col? : Option Color) (minSyms : Nat) (pred : ObjectPred)
    (excludedIds : Array ObjectId := #[]) : Bool :=
  if minSyms == 0 then true
  else
    let eligible :=
      (g.player p).graveyard.filterMap fun cid =>
        if excludedIds.contains cid then none
        else
          (g.findObject? cid).bind fun card =>
            if g.exileManaSymbolsCardOk p srcId col? pred card then some card else none
    let total := eligible.foldl (fun acc card => acc + g.manaSymbolsCountFor card col?) 0
    !eligible.isEmpty && total ≥ minSyms

/-- Whether `o` is in the activation zone required by `d` for `p` (CR 113.6 / 605.3). -/
def manaAbilitySourceZoneOk (g : Game) (p : PlayerId) (o : GameObject) (d : ManaAbilityDef) : Bool :=
  if d.fromHand && d.fromGraveyard then false
  else if (d.fromHand || d.fromGraveyard) && d.sourceAbility.any (·.needsBattlefieldSource) then false
  else if d.fromGraveyard then o.zone == .graveyard o.owner && o.owner == p && isDiscardableCard o
  else if d.fromHand then o.zone == .hand o.owner && o.owner == p && isDiscardableCard o
  else o.isOnBattlefield && g.controlledBy o p

/-- Whether `d` can be activated by tapping alone, without sacrificing/exiling
the source, removing counters, choosing other objects, paying life, or paying
mana (the `tap` shortcut and automatic payment). -/
def ManaAbilityDef.isPlainTap (d : ManaAbilityDef) : Bool :=
  let onlyTapOrMana :=
    d.sourceAbility.all fun ab =>
      ab.cost.items.all fun
        | .tapSelf | .mana _ => true
        | _ => false
  d.tap && onlyTapOrMana && !d.hasUnmodeledCostItem && !d.fromHand && !d.fromGraveyard &&
    !d.removesSource && !d.hasExtraInteractiveCost &&
    !d.removeStoryCounter && !d.removeIndestructibleCounter && !d.putStunCounterOnSource &&
    d.picks.isEmpty && d.modeChoices.isEmpty && d.extraEffect?.isNone &&
    !d.cost.includesManaPayment && !d.cost.containsX && d.payLife == 0 && d.damageYou == 0 &&
    d.turnLimit?.isNone && d.lifetimeLimit?.isNone &&
    !d.isExhaust && !d.isPowerUp && !d.isBoast

/-- Whether `d` is a plain `{T}` mana ability after `activationManaCost`
reductions on `o` for `p`. -/
def isPlainTapManaAbilityDef (g : Game) (p : PlayerId) (o : GameObject) (d : ManaAbilityDef) : Bool :=
  let onlyTapOrMana :=
    d.sourceAbility.all fun ab =>
      ab.cost.items.all fun
        | .tapSelf | .mana _ => true
        | _ => false
  let effCost := g.manaAbilityEffectiveCost p o d
  d.tap && onlyTapOrMana && !d.hasUnmodeledCostItem && !d.fromHand && !d.fromGraveyard &&
    !d.removesSource && !d.hasExtraInteractiveCost &&
    !d.removeStoryCounter && !d.removeIndestructibleCounter && !d.putStunCounterOnSource &&
    d.picks.isEmpty && d.modeChoices.isEmpty && d.extraEffect?.isNone &&
    !effCost.includesManaPayment && !effCost.containsX && d.payLife == 0 && d.damageYou == 0 &&
    d.turnLimit?.isNone && d.lifetimeLimit?.isNone &&
    !d.isExhaust && !d.isPowerUp && !d.isBoast

/-- Whether mana ability `d` of object `o` currently satisfies its zone, timing,
frequency, condition, life, counter, crew, exile-symbol, and choice-cost
prerequisites for `p` (CR 605.3 / 602.5a / 702.177 / 702.193). -/
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
  let sacOrExileBf := d.sacrificeSelf || d.exileSelf
  let discOrExileHand := d.discardSelf || d.exileSelfFromHand
  let crewOk : Bool :=
    match d.crewPower? with
    | some n =>
      o.isOnBattlefield &&
        (g.firstPayableCrewSelection? p o.id n d.picks
          (tapSource := d.tap) (sacrificeOrExileSource := sacOrExileBf)
          (discardOrExileHandSource := discOrExileHand)
          (excludeSelf := d.crewExcludesSelf)).isSome
    | none =>
      d.picks.isEmpty ||
        g.costPicksPayable p (some o.id) d.picks
          (tapSource := d.tap) (sacrificeOrExileSource := sacOrExileBf)
          (discardOrExileHandSource := discOrExileHand)
  let exileSymsOk : Bool :=
    match d.exileManaSymbols? with
    | some (col?, minSyms, pred) =>
      g.canPayExileManaSymbols p o.id col? minSyms pred
        (excludedIds := if d.exileSelfFromGraveyard then #[o.id] else #[])
    | none => true
  !d.hasUnmodeledCostItem &&
    !(d.sacrificeSelf && g.cantSacrificeObject p o) &&
    !(g.manaAbilityEffectiveCost p o d).containsX &&
    g.manaAbilitySourceZoneOk p o d &&
    !turnLimitHit &&
    !lifetimeLimitHit &&
    !(d.isBoast && !g.declaredAsAttackerThisTurn o.id) &&
    !(d.isPowerUp && g.powerUpsForbidden) &&
    !(d.removeStoryCounter && o.status.story == 0) &&
    !(d.removeIndestructibleCounter && o.status.indestructibleCounters == 0) &&
    g.canPayLife p d.payLife &&
    crewOk &&
    exileSymsOk &&
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
      d.output.producibleTypes.foldl (fun acc t => if acc.contains t then acc else acc.push t) acc
    else acc) #[]

/-- Add `mana` to `p`'s pool with `r` and `riders` (CR 106.4 / 106.6 / 106.12). -/
def addRestrictedMana (pool : ManaPool) (mana : Array ManaType)
    (r : Option ManaSpendRestriction) (riders : Array SpellRiderSpec := #[])
    (source : Option ObjectId := none) (fromTreasure : Bool := false) : ManaPool :=
  mana.foldl (fun pool t =>
    pool.add t (restriction := r) (source := source) (fromTreasure := fromTreasure)
      (riders := riders)) pool

/-- `p` may activate abilities of creatures they control as though those
creatures had haste (Shang-Chi, Master of Kung Fu; MSH 280). -/
def activatesAsThoughHaste (g : Game) (p : PlayerId) : Bool :=
  g.battlefield.any fun o =>
    let env : EvalEnv := { controller := (g.controllerOf o).getD o.owner, sourceId := some o.id }
    (g.staticAbilities o).any fun ab =>
      ab.anyRule fun cond? r =>
        match r with
        | .player (.activateAsThoughHaste who _) =>
          cond?.all (EvalExpr.evalCondition g env) &&
            EvalExpr.matchesPlayerFilter g env who p
        | _ => false

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
    | .resolutionChoice q (.mayPayThen ..) | .resolutionChoice q (.mayPayExtort _)
    | .resolutionChoice q (.mayPayManaForReflexive ..)
    | .resolutionChoice q (.mayPaySymbolsThen ..)
    | .resolutionChoice q (.ultronMayPay ..) => q == p
    | .resolutionChoice q (.mayCastCards _ withoutPaying _ _) => q == p && !withoutPaying
    | .resolutionChoice q (.mayCastFromGraveyard _) => q == p
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

/-- True when `f` holds only queued replacement/interpreter continuations
(`pendingReplacement`, `outerPendingReplacements`, `interpWait?`) rather than
an active resolving spell/ability/choice frame. -/
private def isCarrierOnlyFrame (f : ContinuationFrame) : Bool :=
  { f with
    pendingReplacement := none
    outerPendingReplacements := #[]
    interpWait? := none } == {}

private def abortDepartedManaAbilityContCore (g : Game) (p : PlayerId) (prevPending : Pending)
    (wasPaused : Bool := true) (hasFollowingSeq : Bool := false)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : Game × Bool :=
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
      let hadOuterProp := prevPending != .none && g.proposedSpell.isSome
      if shouldRestorePrev then
        g := g.resumePendingReplacementFwd (.restorePending prevPending false none allDeparted none)
          (followedByFinishChoice := followedByFinishChoice)
          (followedByExplicitPriority? := followedByExplicitPriority?)
      let reversedOuter := shouldRestorePrev && hadOuterProp && g.proposedSpell.isNone
      if !reversedOuter && !g.over && g.pending == .none && g.afterRandom == .none && !g.sbaPaused &&
          !hasFollowingSeq then
        let prio := if g.stillInGame p then g.priorityInstead p else g.priorityInstead g.activePlayer
        if g.continuations.all isCarrierOnlyFrame then
          g := g.finishAndGrantPriorityFwd prio
        else if g.pendingReplacement.isSome || !g.outerPendingReplacements.isEmpty ||
            g.currentInterpWait?.isSome then
          if !g.anyContinuationSettlesControlFlowFwd then
            if g.pendingPriority != some prio then
              g := g.change (.pendingPriority (some prio))
            g := g.chainPendingReplacement .finishResolutionChoice
          else if g.hasImplicitPendingPriorityContinuationFwd && g.pendingPriority != some prio then
            g := g.change (.pendingPriority (some prio))
          g := g.drainPendingContinuationsFwd
    return (g, false)

private def abortDepartedManaAbilityCont (g : Game) (p : PlayerId) (prevPending : Pending)
    (wasPaused : Bool := true) (hasFollowingSeq : Bool := false)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : Game :=
  (abortDepartedManaAbilityContCore g p prevPending
    (wasPaused := wasPaused) (hasFollowingSeq := hasFollowingSeq)
    (followedByFinishChoice := followedByFinishChoice)
    (followedByExplicitPriority? := followedByExplicitPriority?)).1

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
damage, modal/extra non-mana effect, Mountain extra mana, and CR 734.1 / priority
cleanup) of a mana ability. -/
def finishActivateManaAbilityPostSac (g : Game) (p : PlayerId) (id : ObjectId) (oname : String)
    (srcSnap : EventObject) (mana : Array ManaType) (tap : Bool)
    (activatedIdx : Option Nat) (restriction : Option ManaSpendRestriction)
    (damageYou : Nat) (isMountain : Bool) (prevPending : Pending)
    (powerUp : Bool := false) (exhaust : Bool := false)
    (riders : Array SpellRiderSpec := #[])
    (extraEffect? : Option Effect := none)
    (wasPaused : Bool := true) (hasFollowingSeq : Bool := false)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : Game := Id.run do
  let mut g := g
  if prevPending == .none && !hasFollowingSeq then
    if let some outer := g.pendingReplacement then
      if g.continuations.isEmpty then
        g := g.change (.pushContinuationFrame {})
      g := g.changes #[.pendingReplacement none, .pushOuterPendingReplacement outer]
  if g.over || !g.stillInGame p then
    return abortDepartedManaAbilityCont g p prevPending
      (wasPaused := wasPaused) (hasFollowingSeq := hasFollowingSeq)
      (followedByFinishChoice := followedByFinishChoice)
      (followedByExplicitPriority? := followedByExplicitPriority?)
  g := g.record (GameEvent.abilityActivated g.turnNumber id srcSnap p (.mana activatedIdx powerUp exhaust))
  let isTreasure := srcSnap.subtypes.contains .treasure
  let verb := if tap then "taps" else "activates"
  if !mana.isEmpty || extraEffect?.isNone then
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
    let restrNote := ManaSpendRestriction.note restriction
    g :=
      if mana.isEmpty then g.logMsg s!"{(g.player p).name} {verb} {oname} but adds no mana"
      else g.logMsg s!"{(g.player p).name} {verb} {oname} for {produced}{restrNote}"
  else
    g := g.logMsg s!"{(g.player p).name} {verb} {oname}'s mana ability"
  if tap then
    g := match g.proposedSpell with
      | some _ => g.changeProposal (.pushTapped id)
      | none => g
  g := g.change (.consecutivePasses 0)
  if damageYou > 0 then
    let dmgSrc := (g.findLiveSourceObject? id).orElse (fun _ => some (damageSourceObjectFromLki srcSnap))
    g := g.dealDamageToPlayer p damageYou (source := dmgSrc)
      (cause := some (.gameRule .abilityActivated))
  let mut deferredExtraEff? : Option Effect := none
  if let some eff := extraEffect? then
    if g.pending != .none && g.pending != prevPending then
      deferredExtraEff? := some eff
    else
      g := g.resumePendingReplacementFwd (.runModalManaEffect p id eff)
  let allDeparted := departedSinceOptionalCkpt g g.proposalCheckpoint
  if g.pending != .none && g.pending != prevPending then
    if let some eff := deferredExtraEff? then
      g := g.chainPendingReplacement (.runModalManaEffect p id eff)
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
              g.currentInterpWait?.isNone then
            g := g.chainPendingReplacement (.receivePriority prio)
          else if !(if g.sbaPaused then g.anyContinuationSettlesControlFlowFwd
              else anyPostPromptContinuationSettlesControlFlowFwd g) then
            if g.pendingPriority != some prio then
              g := g.change (.pendingPriority (some prio))
            g := g.chainPendingReplacement .finishResolutionChoice
          else if (if g.sbaPaused then g.hasImplicitPendingPriorityContinuationFwd
              else hasPostPromptImplicitPendingPriorityContinuationFwd g) && g.pendingPriority != some prio then
            g := g.change (.pendingPriority (some prio))
        else if !g.outerPendingReplacements.isEmpty ||
            g.currentInterpWait?.isSome then
          if !(if g.sbaPaused then g.anyContinuationSettlesControlFlowFwd
              else anyPostPromptContinuationSettlesControlFlowFwd g) then
            if g.pendingPriority != some prio then
              g := g.change (.pendingPriority (some prio))
            g := g.chainPendingReplacement .finishResolutionChoice
          else if (if g.sbaPaused then g.hasImplicitPendingPriorityContinuationFwd
              else hasPostPromptImplicitPendingPriorityContinuationFwd g) && g.pendingPriority != some prio then
            g := g.change (.pendingPriority (some prio))
        else if (if g.sbaPaused then g.hasImplicitPendingPriorityContinuationFwd
            else hasPostPromptImplicitPendingPriorityContinuationFwd g) && g.pendingPriority != some prio then
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
            g.currentInterpWait?.isSome then
          if !g.anyContinuationSettlesControlFlowFwd then
            if g.pendingPriority != some prio then
              g := g.change (.pendingPriority (some prio))
            g := g.chainPendingReplacement .finishResolutionChoice
          else if g.hasImplicitPendingPriorityContinuationFwd && g.pendingPriority != some prio then
            g := g.change (.pendingPriority (some prio))
          g := g.drainPendingContinuationsFwd
    else if wasPaused then
      g := g.resumePendingReplacementFwd (.restorePending prevPending false none allDeparted none)
        (followedByFinishChoice := followedByFinishChoice)
        (followedByExplicitPriority? := followedByExplicitPriority?)
    return g

private def finishActivateManaAbilityPicksCore (g : Game) (p : PlayerId) (id : ObjectId) (oname : String)
    (mana : Array ManaType) (picks : Array CostPick) (costIds : Array ObjectId)
    (tap sacrificeSelf : Bool) (activatedIdx : Option Nat) (restriction : Option ManaSpendRestriction)
    (damageYou : Nat) (isMountain : Bool) (prevPending : Pending)
    (exileSelf : Bool := false) (powerUp : Bool := false) (exhaust : Bool := false)
    (riders : Array SpellRiderSpec := #[])
    (exileFromZone? : Option ZoneKind := none) (discardSelf : Bool := false)
    (exileSymIds : Array ObjectId := #[]) (extraEffect? : Option Effect := none)
    (removeIndestructible : Bool := false) (removePlusOnesCount : Nat := 0)
    (crewIds : Array ObjectId := #[]) (putStunOnSource : Bool := false)
    (fromEventIdx? : Option Nat := none)
    (crewPower? : Option Nat := none)
    (wasPaused : Bool := true) (hasFollowingSeq : Bool := false)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : Game × Bool := Id.run do
  let abortNow (g0 : Game) : Game × Bool :=
    abortDepartedManaAbilityContCore g0 p prevPending
      (wasPaused := wasPaused) (hasFollowingSeq := hasFollowingSeq)
      (followedByFinishChoice := followedByFinishChoice)
      (followedByExplicitPriority? := followedByExplicitPriority?)
  let sacOrExileSelf := sacrificeSelf || exileSelf
  let discOrExileHand := discardSelf || exileFromZone? == some .hand
  if g.over || !g.stillInGame p then
    return abortNow g
  if wasPaused then
    let tapPrePaid := manaSourceTapPaidSinceCkpt g p id
    let srcPayable : Bool :=
      let needTap := tap && !tapPrePaid
      let needBfCounter := removeIndestructible || removePlusOnesCount > 0 || putStunOnSource
      if discOrExileHand then
        match g.findObject? id with
        | some cur => cur.zone == .hand cur.owner && cur.owner == p && isDiscardableCard cur
        | none => false
      else if exileFromZone? == some .graveyard then
        match g.findObject? id with
        | some cur => cur.zone == .graveyard cur.owner && cur.owner == p && isDiscardableCard cur
        | none => false
      else if !needTap && !sacOrExileSelf && !needBfCounter then true
      else
        match g.findObject? id with
        | some cur =>
          cur.isOnBattlefield && g.controlledBy cur p &&
            (!needTap || !cur.status.tapped) &&
            (!removeIndestructible || cur.status.indestructibleCounters > 0) &&
            cur.status.plusOnePlusOne ≥ removePlusOnesCount
        | none => false
    if !srcPayable then
      return abortNow g
    let mut crewPow : Nat := 0
    for cid in crewIds do
      match g.findObject? cid with
      | some co =>
        if !co.isOnBattlefield || !g.controlledBy co p || !g.isCreature co || co.status.tapped then
          return abortNow g
        crewPow := crewPow + (g.power co).toNat
      | none => return abortNow g
    if let some crewN := crewPower? then
      if crewPow < crewN then
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
              (discardOrExileHandSource := discOrExileHand)
          | none => false
        if !ok then
          return abortNow g
      checkRest := checkRest.extract pick.count checkRest.size
    for cid in exileSymIds do
      match g.findObject? cid with
      | some co =>
        if co.zone != .graveyard p || !isDiscardableCard co then
          return abortNow g
      | none => return abortNow g
  let mut g := g
  let hasPreExileSymWork :=
    removeIndestructible || removePlusOnesCount > 0 || !crewIds.isEmpty || putStunOnSource || !picks.isEmpty
  let counterFromIdx := fromEventIdx?.getD g.events.size
  let mut removedAnyCounter := fromEventIdx?.isSome && hasPreExileSymWork
  if removeIndestructible then
    match g.findObject? id with
    | some curSrc =>
      if !curSrc.isOnBattlefield || !g.controlledBy curSrc p || curSrc.status.indestructibleCounters == 0 then
        return abortNow g
      let srcName := g.name curSrc
      g := g.recordRemoveCounters id .indestructible 1 (byPlayer := some p)
        (cause := some (.costPayment .removeCounters p (some id))) (deferPlayFromExileLogs := true)
      g := g.logMsg s!"{srcName} loses an indestructible counter"
      removedAnyCounter := true
      if g.sbaPaused then
        g := g.chainPendingReplacement
          (.finishActivateManaAbilityPicks p id oname mana picks costIds tap sacrificeSelf
            activatedIdx restriction damageYou isMountain prevPending
            exileSelf powerUp exhaust riders exileFromZone? discardSelf exileSymIds extraEffect?
            false removePlusOnesCount crewIds putStunOnSource (some counterFromIdx) crewPower?)
        return (g, false)
    | none => return abortNow g
  if removePlusOnesCount > 0 then
    match g.findObject? id with
    | some curSrc =>
      if !curSrc.isOnBattlefield || !g.controlledBy curSrc p || curSrc.status.plusOnePlusOne < removePlusOnesCount then
        return abortNow g
      let srcName := g.name curSrc
      g := g.recordRemoveCounters id .plusOnePlusOne removePlusOnesCount (byPlayer := some p)
        (cause := some (.costPayment .removeCounters p (some id))) (deferPlayFromExileLogs := true)
      g := g.logMsg s!"{(g.player p).name} removes {removePlusOnesCount} +1/+1 counters from {srcName}"
      removedAnyCounter := true
      if g.sbaPaused then
        g := g.chainPendingReplacement
          (.finishActivateManaAbilityPicks p id oname mana picks costIds tap sacrificeSelf
            activatedIdx restriction damageYou isMountain prevPending
            exileSelf powerUp exhaust riders exileFromZone? discardSelf exileSymIds extraEffect?
            false 0 crewIds putStunOnSource (some counterFromIdx) crewPower?)
        return (g, false)
    | none => return abortNow g
  if removedAnyCounter then
    g := emitExpiredPlayFromExileLogsLazy (fun _ => g.mkHistoricalGameAt counterFromIdx) g counterFromIdx
  if let some crewN := crewPower? then
    let mut crewPow : Nat := 0
    for cid in crewIds do
      match g.findObject? cid with
      | some curCrew =>
        if !curCrew.isOnBattlefield || !g.controlledBy curCrew p || !g.isCreature curCrew || curCrew.status.tapped then
          return abortNow g
        crewPow := crewPow + (g.power curCrew).toNat
      | none => return abortNow g
    if crewPow < crewN then
      return abortNow g
  for cid in crewIds do
    match g.findObject? cid with
    | some curCrew =>
      if !curCrew.isOnBattlefield || !g.controlledBy curCrew p || !g.isCreature curCrew || curCrew.status.tapped then
        return abortNow g
      g := g.becomeTapped curCrew (cause := some (.costPayment .tap p (some id)))
      g := g.logMsg s!"{(g.player p).name} taps {g.name curCrew} for {oname}"
    | none => return abortNow g
  if putStunOnSource then
    match g.findObject? id with
    | some curSrc =>
      if !curSrc.isOnBattlefield || !g.controlledBy curSrc p then
        return abortNow g
      g := g.putCountersDeferredLog id .stun 1 (some p) (.playerPutsOn p)
        (cause := some (.costPayment .putCounters p (some id)))
      if let .chooseReplacement .. := g.pending then
        g := g.chainPendingReplacement
          (.finishActivateManaAbilityPicks p id oname mana picks costIds tap sacrificeSelf
            activatedIdx restriction damageYou isMountain prevPending
            exileSelf powerUp exhaust riders exileFromZone? discardSelf exileSymIds extraEffect?)
        return (g, false)
    | none => return abortNow g
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
              (discardOrExileHandSource := discOrExileHand)
          | none => false
        if !ok then
          return abortNow g
    let isBfSacPick : Bool :=
      match pick with
      | .tapUntappedCreature | .tapTwoUntappedArtifacts | .custom (.tapObjects ..)
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
          exileSelf powerUp exhaust riders exileFromZone? discardSelf exileSymIds extraEffect?)
      return (g, false)
    if !pickPaid then
      return abortNow g
  let symFromIdx? : Option Nat :=
    if hasPreExileSymWork then none else fromEventIdx?
  let symFromIdx := symFromIdx?.getD g.events.size
  let needSymEmit := !exileSymIds.isEmpty || symFromIdx?.isSome
  for j in [0:exileSymIds.size] do
    if g.over || !g.stillInGame p then
      return abortNow g
    let cid := exileSymIds[j]!
    match g.findObject? cid with
    | some card =>
      if card.zone != .graveyard p || !isDiscardableCard card then
        return abortNow g
      let msg := s!"{(g.player p).name} exiles {g.name card} from their graveyard"
      g := (g.move cid .exile none (cause := some (.costPayment .exile p (some id)))
        (deferPlayFromExileLogs := true)).1
      if g.sbaPaused || (match g.pending with | .chooseReplacement .. => true | _ => false) then
        let remSyms := exileSymIds.extract (j + 1) exileSymIds.size
        g := g.chainPendingReplacement (.finishPostStep (.logExiledIfInExile cid msg))
        g := g.chainPendingReplacement
          (.finishActivateManaAbilityPicks p id oname mana #[] #[] tap sacrificeSelf
            activatedIdx restriction damageYou isMountain prevPending
            exileSelf powerUp exhaust riders exileFromZone? discardSelf remSyms extraEffect?
            false 0 #[] false (some symFromIdx))
        return (g, false)
      if (g.followMovedToZone? cid (· == .exile)).isSome then
        g := g.logMsg msg
    | none =>
      return abortNow g
  if needSymEmit then
    g := emitExpiredPlayFromExileLogsLazy (fun _ => g.mkHistoricalGameAt symFromIdx) g symFromIdx
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
            restriction damageYou isMountain prevPending powerUp exhaust riders extraEffect?)
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
            restriction damageYou isMountain prevPending powerUp exhaust riders extraEffect?)
        return (g, false)
      if (g.followMovedToZone? id (· == .exile)).isSome then
        g := g.logMsg msg
    | none =>
      return abortNow g
  else if exileFromZone? == some .hand then
    match g.findObject? id with
    | some src =>
      if !(src.zone == .hand src.owner && src.owner == p && isDiscardableCard src) then
        return abortNow g
      let msg := s!"{(g.player p).name} exiles {g.name src} from their hand"
      g := (g.move id .exile none (cause := some (.costPayment .exile p (some id)))).1
      if let .chooseReplacement .. := g.pending then
        g := g.chainPendingReplacement (.finishPostStep (.logExiledIfInExile id msg))
        g := g.chainPendingReplacement
          (.finishActivateManaAbilityPostSac p id oname srcSnap mana tap activatedIdx
            restriction damageYou isMountain prevPending powerUp exhaust riders extraEffect?)
        return (g, false)
      if (g.followMovedToZone? id (· == .exile)).isSome then
        g := g.logMsg msg
    | none =>
      return abortNow g
  else if exileFromZone? == some .graveyard then
    match g.findObject? id with
    | some src =>
      if !(src.zone == .graveyard src.owner && src.owner == p && isDiscardableCard src) then
        return abortNow g
      let msg := s!"{(g.player p).name} exiles {g.name src} from their graveyard"
      g := (g.move id .exile none (cause := some (.costPayment .exile p (some id)))).1
      if let .chooseReplacement .. := g.pending then
        g := g.chainPendingReplacement (.finishPostStep (.logExiledIfInExile id msg))
        g := g.chainPendingReplacement
          (.finishActivateManaAbilityPostSac p id oname srcSnap mana tap activatedIdx
            restriction damageYou isMountain prevPending powerUp exhaust riders extraEffect?)
        return (g, false)
      if (g.followMovedToZone? id (· == .exile)).isSome then
        g := g.logMsg msg
    | none =>
      return abortNow g
  else if discardSelf then
    match g.findObject? id with
    | some src =>
      if !(src.zone == .hand src.owner && src.owner == p && isDiscardableCard src) then
        return abortNow g
      let msg := s!"{(g.player p).name} discards {g.name src}"
      g := (g.move id (.graveyard src.owner) none (verb := some .discard)
        (actor := some p) (cause := some (.costPayment .discard p (some id)))).1
      if let .chooseReplacement .. := g.pending then
        g := g.chainPendingReplacement (.finishPostStep (.logDiscardIfInGraveyard id src.owner msg))
        g := g.chainPendingReplacement
          (.finishActivateManaAbilityPostSac p id oname srcSnap mana tap activatedIdx
            restriction damageYou isMountain prevPending powerUp exhaust riders extraEffect?)
        return (g, false)
      if (g.followMovedToZone? id (· == .graveyard src.owner)).isSome then
        g := g.logMsg msg
    | none =>
      return abortNow g
  return (g.finishActivateManaAbilityPostSac p id oname srcSnap mana tap activatedIdx
    restriction damageYou isMountain prevPending powerUp exhaust riders
    (extraEffect? := extraEffect?) (wasPaused := wasPaused) (hasFollowingSeq := hasFollowingSeq)
    (followedByFinishChoice := followedByFinishChoice)
    (followedByExplicitPriority? := followedByExplicitPriority?), false)

/-- Execute the remaining `picks`, `exileSymIds`, `{T}`, and self-removal steps
of a mana ability before `finishActivateManaAbilityPostSac`, chaining
continuations if any cost step pauses on `Pending.chooseReplacement`. -/
def finishActivateManaAbilityPicks (g : Game) (p : PlayerId) (id : ObjectId) (oname : String)
    (mana : Array ManaType) (picks : Array CostPick) (costIds : Array ObjectId)
    (tap sacrificeSelf : Bool) (activatedIdx : Option Nat) (restriction : Option ManaSpendRestriction)
    (damageYou : Nat) (isMountain : Bool) (prevPending : Pending)
    (exileSelf : Bool := false) (powerUp : Bool := false) (exhaust : Bool := false)
    (riders : Array SpellRiderSpec := #[])
    (exileFromZone? : Option ZoneKind := none) (discardSelf : Bool := false)
    (exileSymIds : Array ObjectId := #[]) (extraEffect? : Option Effect := none)
    (removeIndestructible : Bool := false) (removePlusOnesCount : Nat := 0)
    (crewIds : Array ObjectId := #[]) (putStunOnSource : Bool := false)
    (fromEventIdx? : Option Nat := none)
    (crewPower? : Option Nat := none)
    (wasPaused : Bool := true) (hasFollowingSeq : Bool := false)
    (followedByFinishChoice : Bool := false)
    (followedByExplicitPriority? : Option PlayerId := none) : Game :=
  (finishActivateManaAbilityPicksCore g p id oname mana picks costIds tap sacrificeSelf
    activatedIdx restriction damageYou isMountain prevPending
    (exileSelf := exileSelf) (powerUp := powerUp) (exhaust := exhaust) (riders := riders)
    (exileFromZone? := exileFromZone?) (discardSelf := discardSelf)
    (exileSymIds := exileSymIds) (extraEffect? := extraEffect?)
    (removeIndestructible := removeIndestructible) (removePlusOnesCount := removePlusOnesCount)
    (crewIds := crewIds) (putStunOnSource := putStunOnSource) (fromEventIdx? := fromEventIdx?)
    (crewPower? := crewPower?)
    (wasPaused := wasPaused) (hasFollowingSeq := hasFollowingSeq)
    (followedByFinishChoice := followedByFinishChoice)
    (followedByExplicitPriority? := followedByExplicitPriority?)).1

/-- Activate mana ability `idx` of `id` (CR 605.3), adding `mana`, paying
choice costs with `costIds` in order. The mana is added immediately; the
ability doesn't use the stack (CR 605.3b). -/
def activateManaAbility (g : Game) (p : PlayerId) (id : ObjectId) (idx : Nat)
    (mana : Array ManaType) (costIds : Array ObjectId := #[]) : Except String Game := do
  if !g.canActivateManaAbility p then
    throw "You can't activate a mana ability now (CR 605.3a)"
  let some o := g.findObject? id | throw "no such object"
  let oname := g.name o
  let some d := (g.manaAbilityDefs o)[idx]? | throw s!"{oname} has no such mana ability"
  if d.hasUnmodeledCostItem then
    throw s!"{oname}'s ability has a cost that can't be paid"
  if d.fromHand && d.fromGraveyard then
    throw s!"{oname}'s ability has conflicting hand and graveyard activation zones"
  if (d.fromHand || d.fromGraveyard) && d.sourceAbility.any (·.needsBattlefieldSource) then
    throw s!"{oname}'s ability has a battlefield cost that can't be paid from that zone"
  if d.fromGraveyard then
    if !(o.zone == .graveyard o.owner && o.owner == p && isDiscardableCard o) then
      throw s!"{oname}'s ability can be activated only from the graveyard"
  else if d.fromHand then
    if !(o.zone == .hand o.owner && o.owner == p && isDiscardableCard o) then
      throw s!"{oname}'s ability can be activated only from your hand"
  else
    if !g.controlledBy o p || !o.isOnBattlefield then
      throw "You don't control that permanent"
  let maxX := if d.removeAnyNumberPlusOne && o.isOnBattlefield then o.status.plusOnePlusOne else 0
  let findModeX (mode : Effect) :
      Option (Nat × ManaAbilityMode) :=
    if d.removeAnyNumberPlusOne then
      (List.range (maxX + 1)).findSome? fun x =>
        let m := evalActivatedManaMode g o p mode (chosenX := x)
        if m.output?.any (·.allows mana) then some (x, m) else none
    else
      let m := evalActivatedManaMode g o p mode (chosenX := 0)
      if m.output?.any (·.allows mana) then some (0, m) else none
  let (effRestriction, effRiders, effDamageYou, effExtraEffect?, removePlusOnesCount) ←
    if !d.modeChoices.isEmpty then
      match d.sourceAbility with
      | some ab =>
        let rawModes := ab.allModes
        if !mana.isEmpty then
          match rawModes.findSome? findModeX with
          | some (x, m) => pure (m.restriction, m.riders, m.damageYou, none, x)
          | none => throw s!"{oname}'s mana ability can't add that mana"
        else
          match d.modeChoices.find? (·.output?.isNone) with
          | some m => pure (none, #[], 0, some m.effect, 0)
          | none =>
            match rawModes.findSome? findModeX with
            | some (x, m) => pure (m.restriction, m.riders, m.damageYou, none, x)
            | none => throw s!"{oname}'s mana ability can't add that mana"
      | none =>
        if !mana.isEmpty then
          match d.modeChoices.find? (fun m => m.output?.any (·.allows mana)) with
          | some m => pure (m.restriction, m.riders, m.damageYou, none, 0)
          | none => throw s!"{oname}'s mana ability can't add that mana"
        else
          match d.modeChoices.find? (·.output?.isNone) with
          | some m => pure (none, #[], 0, some m.effect, 0)
          | none =>
            match d.modeChoices.find? (fun m => m.output?.any (·.allows #[])) with
            | some m => pure (m.restriction, m.riders, m.damageYou, none, 0)
            | none => throw s!"{oname}'s mana ability can't add that mana"
    else if let some eff := d.extraEffect? then
      if !mana.isEmpty then
        throw s!"{oname}'s mana ability can't add that mana"
      pure (d.restriction, d.riders, d.damageYou, some eff, 0)
    else if d.removeAnyNumberPlusOne then
      match d.sourceAbility with
      | some ab =>
        match findModeX ab.effect with
        | some (x, m) => pure (m.restriction, m.riders, m.damageYou, none, x)
        | none => throw s!"{oname}'s mana ability can't add that mana"
      | none =>
        if !d.output.allows mana then
          throw s!"{oname}'s mana ability can't add that mana"
        pure (d.restriction, d.riders, d.damageYou, none, 0)
    else
      if !d.output.allows mana then
        throw s!"{oname}'s mana ability can't add that mana"
      pure (d.restriction, d.riders, d.damageYou, none, 0)
  let sinceIdx := (g.targetProposalCheckpoint?.map (·.eventsSize)).getD g.events.size
  let sacOrExileSelf := d.sacrificeSelf || d.exileSelf
  let discOrExileHand := d.discardSelf || d.exileSelfFromHand
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
  if d.sacrificeSelf && g.cantSacrificeObject p o then
    throw s!"You can't sacrifice {oname}"
  if sacOrExileSelf then
    if let some prop := g.proposedSpell then
      if (prop.sourceId == some id && g.proposedNeedsBattlefieldSource prop sinceIdx) ||
          prop.teamworkCreatures.contains id ||
          (prop.sneakAttacker == some id && !g.sneakPaid prop.spellId) ||
          (prop.beamMeUpCreature == some id && !GameEvent.beamMeUpPaid g.events prop.spellId) then
        throw s!"{oname} is needed on the battlefield for the proposed spell or ability"
  if discOrExileHand then
    if let some prop := g.proposedSpell then
      if prop.sourceId == some id &&
          (prop.discardSource ||
            prop.activation.any (fun a =>
              a.cost.discardSource || a.cost.exileSourceFromHand || a.isFromHand)) then
        throw s!"{oname} is needed in your hand for the proposed spell or ability"
  if d.exileSelfFromGraveyard then
    if let some prop := g.proposedSpell then
      if prop.sourceId == some id && prop.activation.any (·.isFromGraveyard) then
        throw s!"{oname} is needed in your graveyard for the proposed spell or ability"
  if d.isBoast && !g.declaredAsAttackerThisTurn o.id then
    throw s!"{oname}'s boast ability can be activated only if it attacked this turn and only once each turn"
  if let some lim := d.turnLimit? then
    let used :=
      match d.activatedIdx with
      | some i => g.abilityActivationsThisTurn o.id i (isBoast := d.isBoast)
      | none => g.activationsThisTurn o.id
    if used ≥ lim then
      if d.isBoast then
        throw s!"{oname}'s boast ability can be activated only if it attacked this turn and only once each turn"
      else if lim == 1 then
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
  if d.removeAnyNumberPlusOne && removePlusOnesCount > 0 then
    if o.status.plusOnePlusOne < removePlusOnesCount then
      throw s!"{oname} doesn't have {removePlusOnesCount} +1/+1 counters"
    if let some prop := g.proposedSpell then
      if prop.sourceId == some id && prop.removePlusOneX &&
          !g.sourceCounterCostPaidFor id (some prop.spellId) .removeCounters (some .plusOnePlusOne) sinceIdx then
        let req := ((g.findObject? prop.spellId).bind (·.chosenX)).getD 0
        if o.status.plusOnePlusOne < removePlusOnesCount + req then
          throw s!"{oname}'s +1/+1 counters are needed for the proposed ability"
  if !g.costPicksPayable p (some id) d.picks
      (tapSource := d.tap) (sacrificeOrExileSource := sacOrExileSelf)
      (discardOrExileHandSource := discOrExileHand) then
    throw s!"{oname}'s ability has a cost that can't be paid"
  let pickNeed := d.picks.foldl (fun acc pick => acc + pick.count) 0
  if costIds.size < pickNeed || costIds.toList.eraseDups.length != costIds.size then
    throw s!"Choose what to {String.intercalate " and " (d.picks.map (·.phrase)).toList}"
  let pickIds := costIds.extract 0 pickNeed
  let extraCostIds := costIds.extract pickNeed costIds.size
  if d.crewPower?.isNone && d.exileManaSymbols?.isNone && !extraCostIds.isEmpty then
    throw s!"Choose what to {String.intercalate " and " (d.picks.map (·.phrase)).toList}"
  let mut checkRest := pickIds
  for pick in d.picks do
    let slice := checkRest.extract 0 pick.count
    let isTapPick :=
      match pick with
      | .tapUntappedCreature | .tapTwoUntappedArtifacts | .custom (.tapObjects ..) => true
      | _ => false
    for cid in slice do
      let some co := g.findObject? cid | throw "no such object"
      if !g.costPickAllows p (some id) pick co
          (tapSource := d.tap) (sacrificeOrExileSource := sacOrExileSelf)
          (discardOrExileHandSource := discOrExileHand) then
        throw s!"{g.name co} can't be used to {pick.phrase}"
      if let some prop := g.proposedSpell then
        if isTapPick &&
            ((prop.sourceId == some cid && prop.tapSource &&
              !g.sourceTappedForCost cid (some prop.spellId) sinceIdx) ||
              prop.teamworkCreatures.contains cid) then
          throw s!"{g.name co} is already reserved to tap for the proposed spell or ability"
        if !isTapPick && co.isOnBattlefield &&
            ((prop.sourceId == some cid && g.proposedNeedsBattlefieldSource prop sinceIdx) ||
              prop.teamworkCreatures.contains cid ||
              (prop.sneakAttacker == some cid && !g.sneakPaid prop.spellId)) then
          throw s!"{g.name co} is needed on the battlefield for the proposed spell or ability"
        if !isTapPick && !co.isOnBattlefield && prop.sourceId == some cid &&
            prop.kind == .activatedAbility &&
            (prop.discardSource ||
              prop.activation.any (fun a =>
                a.cost.discardSource || a.cost.exileSourceFromHand || a.isFromHand || a.isFromGraveyard)) then
          throw s!"{g.name co} is needed for the proposed ability"
    checkRest := checkRest.extract pick.count checkRest.size
  let (crewIds, exileSymIds) ←
    match d.crewPower?, d.exileManaSymbols? with
    | some _, none => pure (extraCostIds, #[])
    | none, some _ => pure (#[], extraCostIds)
    | some _, some _ =>
      let mut cs : Array ObjectId := #[]
      let mut es : Array ObjectId := #[]
      for cid in extraCostIds do
        let some co := g.findObject? cid | throw "no such object"
        if co.zone == .graveyard p then
          es := es.push cid
        else
          cs := cs.push cid
      pure (cs, es)
    | none, none => pure (#[], #[])
  if let some crewN := d.crewPower? then
    let mut crewPow : Nat := 0
    for cid in crewIds do
      let some co := g.findObject? cid | throw "no such object"
      if ((d.crewExcludesSelf || d.tap) && cid == id) || !co.isOnBattlefield || !g.controlledBy co p ||
          !g.isCreature co || co.status.tapped then
        throw s!"{g.name co} can't be tapped to pay {oname}'s crew cost"
      if let some prop := g.proposedSpell then
        if (prop.sourceId == some cid && prop.tapSource &&
              !g.sourceTappedForCost cid (some prop.spellId) sinceIdx) ||
            prop.teamworkCreatures.contains cid then
          throw s!"{g.name co} is already reserved to tap for the proposed spell or ability"
      crewPow := crewPow + (g.power co).toNat
    if crewPow < crewN then
      throw s!"Tap creatures with total power {crewN} or more to activate {oname}"
  if let some (col?, minSyms, pred) := d.exileManaSymbols? then
    let mut symTotal : Nat := 0
    for cid in exileSymIds do
      let some co := g.findObject? cid | throw "no such object"
      if (d.exileSelfFromGraveyard && cid == id) || !g.exileManaSymbolsCardOk p id col? pred co then
        throw s!"{g.name co} can't be exiled to pay {oname}'s ability cost"
      if let some prop := g.proposedSpell then
        if prop.sourceId == some cid && prop.activation.any (·.isFromGraveyard) then
          throw s!"{g.name co} is needed in your graveyard for the proposed spell or ability"
      symTotal := symTotal + g.manaSymbolsCountFor co col?
    if (minSyms > 0 && exileSymIds.isEmpty) || symTotal < minSyms then
      throw s!"Exile cards from your graveyard with at least {minSyms} matching mana symbols to activate {oname}"
  let pl := g.player p
  let effCost := g.manaAbilityEffectiveCost p o d
  if effCost.containsX then
    throw s!"{pl.name} cannot pay {effCost}"
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
  let isMountain := o.isOnBattlefield && g.hasSubtype o .mountain && d.tap && !mana.isEmpty
  let needsManaCkpt :=
    !d.picks.isEmpty || d.removesSource || d.removeStoryCounter ||
      d.removeIndestructibleCounter || d.removeAnyNumberPlusOne ||
      d.putStunCounterOnSource || !crewIds.isEmpty || !exileSymIds.isEmpty
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
  let preCounters := g
  let costFromIdx := g.events.size
  let mut removedAnyCounter := false
  let remPlusOnes := if d.removeAnyNumberPlusOne then removePlusOnesCount else 0
  if d.removeStoryCounter then
    let some curSrc := g.findObject? id | throw s!"{oname} is no longer on the battlefield"
    if !curSrc.isOnBattlefield || !g.controlledBy curSrc p || curSrc.status.story == 0 then
      throw s!"{oname} doesn't have a story counter to remove"
    let srcName := g.name curSrc
    g := g.recordRemoveCounters id .story 1 (byPlayer := some p)
      (cause := some (.costPayment .removeCounters p (some id))) (deferPlayFromExileLogs := true)
    g := g.logMsg s!"{(g.player p).name} removes a story counter from {srcName}"
    removedAnyCounter := true
    if g.sbaPaused then
      g := g.chainPendingReplacement
        (.finishActivateManaAbilityPicks p id oname mana d.picks pickIds d.tap d.sacrificeSelf
          d.activatedIdx effRestriction effDamageYou isMountain prevPending
          d.exileSelf d.isPowerUp d.isExhaust effRiders d.exileFromZone? d.discardSelf exileSymIds effExtraEffect?
          d.removeIndestructibleCounter remPlusOnes crewIds d.putStunCounterOnSource (some costFromIdx)
          d.crewPower?)
      if let some outer := outerCont? then
        g := g.chainPendingReplacement outer
      return g
  if d.removeIndestructibleCounter then
    let some curSrc := g.findObject? id | throw s!"{oname} is no longer on the battlefield"
    if !curSrc.isOnBattlefield || !g.controlledBy curSrc p || curSrc.status.indestructibleCounters == 0 then
      throw s!"{oname} doesn't have an indestructible counter to remove"
    g ← g.payRemoveIndestructibleCounter curSrc (some id) (deferPlayFromExileLogs := true)
    removedAnyCounter := true
    if g.sbaPaused then
      g := g.chainPendingReplacement
        (.finishActivateManaAbilityPicks p id oname mana d.picks pickIds d.tap d.sacrificeSelf
          d.activatedIdx effRestriction effDamageYou isMountain prevPending
          d.exileSelf d.isPowerUp d.isExhaust effRiders d.exileFromZone? d.discardSelf exileSymIds effExtraEffect?
          false remPlusOnes crewIds d.putStunCounterOnSource (some costFromIdx) d.crewPower?)
      if let some outer := outerCont? then
        g := g.chainPendingReplacement outer
      return g
  if d.removeAnyNumberPlusOne && removePlusOnesCount > 0 then
    let some curSrc := g.findObject? id | throw s!"{oname} is no longer on the battlefield"
    if !curSrc.isOnBattlefield || !g.controlledBy curSrc p || curSrc.status.plusOnePlusOne < removePlusOnesCount then
      throw s!"{oname} doesn't have {removePlusOnesCount} +1/+1 counters"
    let srcName := g.name curSrc
    g := g.recordRemoveCounters id .plusOnePlusOne removePlusOnesCount (byPlayer := some p)
      (cause := some (.costPayment .removeCounters p (some id))) (deferPlayFromExileLogs := true)
    g := g.logMsg s!"{(g.player p).name} removes {removePlusOnesCount} +1/+1 counters from {srcName}"
    removedAnyCounter := true
    if g.sbaPaused then
      g := g.chainPendingReplacement
        (.finishActivateManaAbilityPicks p id oname mana d.picks pickIds d.tap d.sacrificeSelf
          d.activatedIdx effRestriction effDamageYou isMountain prevPending
          d.exileSelf d.isPowerUp d.isExhaust effRiders d.exileFromZone? d.discardSelf exileSymIds effExtraEffect?
          false 0 crewIds d.putStunCounterOnSource (some costFromIdx) d.crewPower?)
      if let some outer := outerCont? then
        g := g.chainPendingReplacement outer
      return g
  if removedAnyCounter then
    g := emitExpiredPlayFromExileLogs preCounters g costFromIdx
  if let some crewN := d.crewPower? then
    let mut crewPow : Nat := 0
    for cid in crewIds do
      let some curCrew := g.findObject? cid | throw "no such object"
      if !curCrew.isOnBattlefield || !g.controlledBy curCrew p || !g.isCreature curCrew || curCrew.status.tapped then
        throw s!"{g.name curCrew} can't be tapped to pay {oname}'s crew cost"
      crewPow := crewPow + (g.power curCrew).toNat
    if crewPow < crewN then
      throw s!"Tap creatures with total power {crewN} or more to activate {oname}"
  for cid in crewIds do
    let some curCrew := g.findObject? cid | throw "no such object"
    if !curCrew.isOnBattlefield || !g.controlledBy curCrew p || !g.isCreature curCrew || curCrew.status.tapped then
      throw s!"{g.name curCrew} can't be tapped to pay {oname}'s crew cost"
    g := g.becomeTapped curCrew (cause := some (.costPayment .tap p (some id)))
    g := g.logMsg s!"{(g.player p).name} taps {g.name curCrew} for {oname}"
  if d.putStunCounterOnSource then
    let some curSrc := g.findObject? id | throw s!"{oname} is no longer on the battlefield"
    if !curSrc.isOnBattlefield || !g.controlledBy curSrc p then
      throw s!"{oname} is no longer on the battlefield"
    g := g.putCountersDeferredLog id .stun 1 (some p) (.playerPutsOn p)
      (cause := some (.costPayment .putCounters p (some id)))
    if let .chooseReplacement .. := g.pending then
      g := g.chainPendingReplacement
        (.finishActivateManaAbilityPicks p id oname mana d.picks pickIds d.tap d.sacrificeSelf
          d.activatedIdx effRestriction effDamageYou isMountain prevPending
          d.exileSelf d.isPowerUp d.isExhaust effRiders d.exileFromZone? d.discardSelf exileSymIds effExtraEffect?)
      if let some outer := outerCont? then
        g := g.chainPendingReplacement outer
      return g
  let (gAfter, cleanSyncAbort) :=
    finishActivateManaAbilityPicksCore g p id oname mana d.picks pickIds d.tap d.sacrificeSelf
      d.activatedIdx effRestriction effDamageYou isMountain prevPending
      (exileSelf := d.exileSelf) (powerUp := d.isPowerUp) (exhaust := d.isExhaust) (riders := effRiders)
      (exileFromZone? := d.exileFromZone?) (discardSelf := d.discardSelf)
      (exileSymIds := exileSymIds) (extraEffect? := effExtraEffect?)
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
    (prop? : Option ProposedSpell := none) (spend : ManaSpend := {}) : Option Nat :=
  let p := (g.controllerOf o).getD o.owner
  let defs := g.manaAbilityDefs o
  let activeProp? := prop? <|> g.proposedSpell
  let hasSpendContext := activeProp?.isSome || spend != ({} : ManaSpend)
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
          (if plainOnly then isPlain
           else d.picks.isEmpty && !d.fromHand && !d.fromGraveyard &&
             !d.hasExtraInteractiveCost && d.modeChoices.isEmpty && d.extraEffect?.isNone) then
        if let some added := d.output.withType mana then
          let tapOk :=
            !d.tap ||
              (!o.status.tapped &&
                !(g.hasSummoningSickness o && !(g.isCreature o && g.activatesAsThoughHaste p)))
          let effCost := g.manaAbilityEffectiveCost p o d
          let costOk :=
            !effCost.containsX &&
              (plainOnly ||
                !effCost.includesManaPayment ||
                ((g.player p).manaPool.payUnits? effCost abSpend).isSome)
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
              | none => if hasSpendContext then d.restriction.all (·.allows spend) else true
            let unrestricted := d.restriction.isNone
            let yld := added.size
            let key :=
              (nonEmpty, spendable, (if hasSpendContext then yld else 0),
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
          g.manaAbilityDefUsable p o d && d.picks.isEmpty &&
          !d.fromHand && !d.fromGraveyard && !d.hasExtraInteractiveCost &&
          d.modeChoices.isEmpty && d.extraEffect?.isNone &&
          (d.output.withType mana).isSome) then
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
        if effCost.includesManaPayment || effCost.containsX then
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
    (prop? : Option ProposedSpell := none) (spend : ManaSpend := {}) : Array ManaType :=
  match g.manaAbilityIndexFor o mana (plainOnly := true) (prop? := prop?) (spend := spend) with
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

/-- Extra unrestricted `{R}` `ManaUnit`s (preserving per-entry `source`
attribution from `g.mountainExtraRedEntriesThisTurn`) added by
`.mountainExtraRed` when `o` is tapped for non-empty `baseAdded` mana
(CR 106.1 / 106.6 / 605.4a). -/
def extraMountainRedUnitsFromTap (g : Game) (o : GameObject) (baseAdded : Array ManaType) :
    Array ManaUnit :=
  let p := (g.controllerOf o).getD o.owner
  if baseAdded.isEmpty || !g.hasSubtype o .mountain || !g.stillInGame p then #[]
  else
    (g.mountainExtraRedEntriesThisTurn p).foldl (fun acc (n, src?) =>
      acc ++ Array.replicate n ({ mana := .colored .red, source := src? } : ManaUnit)) #[]

/-- Mana types `o` adds when tapped for `mana` with a plain `{T}` ability
(including mixed-type `.fixed` outputs such as `{U}{R}` and `.mountainExtraRed`
extra `{R}`, CR 106.1 / 605.3b / 605.4a). -/
def manaTypesFromTap (g : Game) (o : GameObject) (mana : ManaType)
    (prop? : Option ProposedSpell := none) (spend : ManaSpend := {}) : Array ManaType :=
  let base := g.baseManaTypesFromTap o mana (prop? := prop?) (spend := spend)
  base ++ g.extraMountainRedFromTap o base

/-- Mana count `o` adds when tapped for `mana` with a plain `{T}` ability. -/
def manaFromTap (g : Game) (o : GameObject) (mana : ManaType)
    (prop? : Option ProposedSpell := none) (spend : ManaSpend := {}) : Nat :=
  (g.manaTypesFromTap o mana (prop? := prop?) (spend := spend)).size

/-- Restriction on the base mana `o` adds when tapped for `mana` with a plain
`{T}` ability. -/
def tapRestrictionOf (g : Game) (o : GameObject) (mana : ManaType)
    (prop? : Option ProposedSpell := none) (spend : ManaSpend := {}) : Option ManaSpendRestriction :=
  match g.manaAbilityIndexFor o mana (plainOnly := true) (prop? := prop?) (spend := spend) with
  | some i => (g.manaAbilityDefs o)[i]?.bind (·.restriction)
  | none => none

/-- Spell riders on the base mana `o` adds when tapped for `mana` with a plain
`{T}` ability (CR 106.6 / 106.12). -/
def tapRidersOf (g : Game) (o : GameObject) (mana : ManaType)
    (prop? : Option ProposedSpell := none) (spend : ManaSpend := {}) : Array SpellRiderSpec :=
  match g.manaAbilityIndexFor o mana (plainOnly := true) (prop? := prop?) (spend := spend) with
  | some i => ((g.manaAbilityDefs o)[i]?.map (·.riders)).getD #[]
  | none => #[]

/-- Add the mana produced by tapping `o` for `mana` to `pool`, applying `o`'s
ability restriction and riders only to `baseManaTypesFromTap` and leaving
`extraMountainRedUnitsFromTap` unrestricted with per-entry source attribution
(CR 106.1 / 106.6 / 605.4a). -/
def addTapManaToPool (g : Game) (pool : ManaPool) (o : GameObject) (mana : ManaType)
    (prop? : Option ProposedSpell := none) (spend : ManaSpend := {}) : ManaPool :=
  let base := g.baseManaTypesFromTap o mana (prop? := prop?) (spend := spend)
  let r := g.tapRestrictionOf o mana (prop? := prop?) (spend := spend)
  let riders := g.tapRidersOf o mana (prop? := prop?) (spend := spend)
  let extra := g.extraMountainRedUnitsFromTap o base
  let isTreasure := g.hasSubtype o .treasure
  (addRestrictedMana pool base r riders (source := some o.id) (fromTreasure := isTreasure)).addUnits
    extra

/-- Concrete plain `{T}` mana activation choice on a permanent, supporting both
single-type `.tapForMana` choices and mixed-color `.combination` tuples via
`.activateManaAbility` (CR 106.1 / 605.3b). -/
structure TapManaChoice where
  abilityIdx : Nat
  baseAdded : Array ManaType
  extraRed : Array ManaUnit := #[]
  restriction : Option ManaSpendRestriction := none
  riders : Array SpellRiderSpec := #[]
  source : Option ObjectId := none
  fromTreasure : Bool := false
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
  (addRestrictedMana pool ch.baseAdded ch.restriction ch.riders
    (source := ch.source) (fromTreasure := ch.fromTreasure)).addUnits ch.extraRed

/-- Distinct plain `{T}` mana activation choices for `(o, types)` toward `cost`,
enumerating every usable plain `{T}` ability on `o` (preserving distinct outputs,
restrictions, and riders across multi-ability permanents) as well as mixed-color
`.combination ts n` tuples (with zero-requirement colors collapsed to avoid
combinatorial blow-up). -/
def tapChoicesForSource (g : Game) (o : GameObject) (types : Array ManaType)
    (cost : ManaCost) (dedupSingleTypes : Array ManaType → Array ManaType := id)
    (prop? : Option ProposedSpell := none) (spend : ManaSpend := {}) : Array TapManaChoice :=
  let p := (g.controllerOf o).getD o.owner
  let defs := g.manaAbilityDefs o
  let activeProp? := prop? <|> g.proposedSpell
  let hasSpendContext := activeProp?.isSome || spend != ({} : ManaSpend)
  let sinceIdx := (g.targetProposalCheckpoint?.map (·.eventsSize)).getD g.events.size
  let isTreasure := g.hasSubtype o .treasure
  let tapPrereqOk : Bool :=
    !o.status.tapped &&
      !(g.hasSummoningSickness o && !(g.isCreature o && g.activatesAsThoughHaste p)) &&
      (match activeProp? with
       | none => true
       | some prop =>
         !((prop.tapSource && prop.sourceId == some o.id &&
             !g.sourceTappedForCost o.id (some prop.spellId) sinceIdx) ||
           prop.teamworkCreatures.contains o.id))
  if !tapPrereqOk then #[]
  else Id.run do
    let mut out : Array TapManaChoice := #[]
    let mut singleTapCache : Array (ManaType × Option Nat) := #[]
    let getSingleTapIdx (t : ManaType) (cache : Array (ManaType × Option Nat)) :
        Option Nat × Array (ManaType × Option Nat) :=
      match cache.find? (·.1 == t) with
      | some (_, idx?) => (idx?, cache)
      | none =>
        let idx? := g.manaAbilityIndexFor o t (plainOnly := true) (prop? := activeProp?)
        (idx?, cache.push (t, idx?))
    let pushChoice (abilityIdx : Nat) (tup : Array ManaType) (d : ManaAbilityDef)
        (singleCands : Array ManaType) (curOut : Array TapManaChoice)
        (cache : Array (ManaType × Option Nat)) :
        Array TapManaChoice × Array (ManaType × Option Nat) :=
      if tup.isEmpty then (curOut, cache)
      else
        let extra := g.extraMountainRedUnitsFromTap o tup
        let dup :=
          curOut.any (fun ch =>
            ch.baseAdded == tup && ch.extraRed == extra &&
              ch.restriction == d.restriction && ch.riders == d.riders)
        if dup then (curOut, cache)
        else
          let (resolvedSingle?, nextCache) := Id.run do
            let mut c := cache
            let mut found? : Option ManaType := none
            for t in singleCands do
              if found?.isNone then
                let (idx?, c') := getSingleTapIdx t c
                c := c'
                if idx? == some abilityIdx && d.output.withType t == some tup then
                  found? := some t
            return (found?, c)
          let ch : TapManaChoice := {
            abilityIdx := abilityIdx
            baseAdded := tup
            extraRed := extra
            restriction := d.restriction
            riders := d.riders
            source := some o.id
            fromTreasure := isTreasure
            singleTapType? := resolvedSingle?
          }
          (curOut.push ch, nextCache)
    for i in [0 : defs.size] do
      let d := defs[i]!
      if g.isPlainTapManaAbilityDef p o d && g.manaAbilityDefUsable p o d then
        let extraSample := g.extraMountainRedFromTap o #[.colorless]
        let spendOk : Bool :=
          match activeProp? with
          | some prop =>
            g.restrictionAllowsProposed d.restriction prop ||
              (!extraSample.isEmpty && g.restrictionAllowsProposed none prop)
          | none =>
            if hasSpendContext then
              (d.restriction.map (·.allows spend)).getD true || !extraSample.isEmpty
            else true
        if spendOk then
          match d.output with
          | .fixed m =>
            if !m.isEmpty && m.any types.contains then
              let cands := types.filter m.contains
              let (out', c') := pushChoice i m d cands out singleTapCache
              out := out'
              singleTapCache := c'
          | .combination comboTs n =>
            let allowedTs := types.filter comboTs.contains
            let dedupTs := dedupSingleTypes allowedTs
            for t in dedupTs do
              if let some tup := d.output.withType t then
                let (out', c') := pushChoice i tup d #[t] out singleTapCache
                out := out'
                singleTapCache := c'
            if n ≥ 2 then
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
                let (out', c') := pushChoice i tup d #[] out singleTapCache
                out := out'
                singleTapCache := c'
          | _ =>
            let prodTs := d.output.producibleTypes
            let allowedTs := types.filter prodTs.contains
            let dedupTs := dedupSingleTypes allowedTs
            for t in dedupTs do
              if let some tup := d.output.withType t then
                let (out', c') := pushChoice i tup d #[t] out singleTapCache
                out := out'
                singleTapCache := c'
    return out

end Game
end Mtg.Engine

