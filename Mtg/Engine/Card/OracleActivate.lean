import Mtg.Engine.Card.CardDef

/-!
Helpers for building the activated abilities the Oracle parser recognizes.
-/

namespace Mtg.Engine.OracleActivate

/-- An activated ability (CR 602.1). -/
def activated (effect : Effect := {}) (mana : ManaCost := ManaCost.empty)
    (tap : Bool := false) (sacrificeSource : Bool := false)
    (sacrificeAnotherCreatureOrArtifact : Bool := false)
    (timing : ActivationTiming := .instant)
    (activeZones : Array ZoneKind := #[.battlefield])
    (turnLimit? : Option Nat := none)
    (lifetimeLimit? : Option Nat := none)
    (condition? : Option Condition := none)
    (costReductions : Array ActivationCostReduction := #[])
    (tag? : Option ActivationMechanicTag := none)
    (manaProd? : Option ManaProductionSpec := none)
    (extraModes : Array Effect := #[]) (payLife : Nat := 0)
    (discardSource : Bool := false)
    (sacrificeAnotherSubtype : Option CardSubtype := none)
    (sacrificeAnotherCreature : Bool := false)
    (discardACard : Bool := false)
    (tapAnUntappedCreatureYouControl : Bool := false)
    (exileSourceFromGraveyard : Bool := false)
    (removeIndestructibleCounter : Bool := false)
    (sacrificeLegendaryArtifact : Bool := false)
    (discardLegendarySameName : Bool := false)
    (sacrificeArtifact : Bool := false)
    (sacrificeArtifactOrCreature : Bool := false)
    (sacrificeArtifactOrDiscardNonland : Bool := false)
    (removeAnyNumberPlusOne : Bool := false)
    (putStunCounterOnSource : Bool := false)
    (sacrificeEquipmentAttachedToSource : Bool := false)
    (loyalty : Option LoyaltySymbol := none)
    (removeStoryCounter : Bool := false)
    (extraCost : CostSpec := {}) :
    ActivatedAbility :=
  let items : Array CostItem := Id.run do
    let mut out : Array CostItem := #[]
    if let some sym := loyalty then out := out.push (.loyalty sym)
    if !mana.symbols.isEmpty then out := out.push (.mana mana)
    if tap then out := out.push .tapSelf
    if payLife != 0 then out := out.push (.payLife (.const payLife))
    if discardSource then out := out.push (.discard (.exact 1) .self)
    if exileSourceFromGraveyard then
      out := out.push (.exile (.exact 1) .yourGraveyard .self false)
    if sacrificeSource then out := out.push (.sacrifice (.exact 1) .self)
    if sacrificeAnotherCreatureOrArtifact then
      out := out ++ CostSpec.sacrificeAnotherCreatureOrArtifactSpec.items
    if sacrificeArtifact && !(sacrificeSource && sacrificeLegendaryArtifact) then
      out := out ++ CostSpec.sacrificeArtifact.items
    if let some t := sacrificeAnotherSubtype then
      out := out ++ (CostSpec.sacrificeAnotherSubtype t).items
    if sacrificeAnotherCreature then
      out := out ++ CostSpec.sacrificeAnotherCreature.items
    if discardACard then out := out ++ CostSpec.discardCard.items
    if sacrificeArtifactOrCreature then
      out := out ++ CostSpec.sacrificeArtifactOrCreature.items
    if sacrificeArtifactOrDiscardNonland then
      out := out ++ CostSpec.sacrificeArtifactOrDiscardNonland.items
    if removeAnyNumberPlusOne then
      out := out.push (.removeCounters .anyNumber (some .plusOnePlusOne) .self)
    if putStunCounterOnSource then
      out := out.push (.putCounters (.const 1) .stun .self)
    if sacrificeEquipmentAttachedToSource then
      out := out ++ CostSpec.sacrificeEquipmentAttached.items
    if tapAnUntappedCreatureYouControl then
      out := out ++ CostSpec.tapUntappedCreature.items
    if removeIndestructibleCounter then
      out := out.push (.removeCounters (.exact 1) (some .indestructible) .self)
    if sacrificeLegendaryArtifact then
      out := out ++ CostSpec.sacrificeLegendaryArtifactSpec.items
    if discardLegendarySameName then
      out := out ++ CostSpec.discardLegendarySameName.items
    if removeStoryCounter then
      out := out.push (.removeCounters (.exact 1) (some .story) .self)
    out := out ++ extraCost.items
    return out
  let equipSub? : Option CardSubtype :=
    match tag? with
    | some (.equip (some (.hasSubtype (.literal sub)))) => some sub
    | _ => none
  let isWorthyEquip : Bool :=
    match tag? with
    | some (.equip (some pred)) => pred == ObjectPred.worthy
    | _ => false
  let effTiming :=
    if loyalty.isSome then .loyalty else timing
  let effLifetime :=
    match lifetimeLimit?, tag? with
    | some n, _ => some n
    | none, some .powerUp | none, some .exhaust => some 1
    | none, _ => none
  let effTurnLimit :=
    match turnLimit?, tag? with
    | some n, _ => some n
    | none, some .boast => some 1
    | none, _ => none
  let effCond :=
    if tag? == some .boast then
      Condition.andOpt condition? (some ActivatedAbility.condSourceAttackedThisTurn)
    else condition?
  let baseEff : Effect :=
    if effect == Effect.attachToTargetCreatureYouControl && (equipSub?.isSome || isWorthyEquip) then
      Effect.equipEffect equipSub? isWorthyEquip
    else
      match manaProd? with
      | some mp =>
        { effect with
          body := .player (.addMana .you mp)
          resolution? := none }
      | none => effect
  let finalEff : Effect :=
    if extraModes.isEmpty then baseEff
    else
      let modes := #[baseEff] ++ extraModes
      { body := .chooseModes { modes }
        phrase := s!"Choose one — {String.intercalate "; " (modes.toList.map Effect.toNotation)}" }
  {
    cost := { items, bindVar? := extraCost.bindVar? }
    effect := finalEff
    timing := effTiming
    activeZones
    turnLimit? := effTurnLimit
    lifetimeLimit? := effLifetime
    condition? := effCond
    costReductions
    tag?
  }

/-- Equip `mana`, only as a sorcery (CR 702.6). -/
def equipAbility (mana : ManaCost) (subtype : Option CardSubtype := none) : ActivatedAbility :=
  activated (Effect.equipEffect subtype false) mana
    (timing := .sorcery)
    (tag? := some (.equip (subtype.map fun s => .hasSubtype (.literal s))))

/-- Equip worthy `mana` (CR 702.6c). -/
def equipWorthyAbility (mana : ManaCost) : ActivatedAbility :=
  activated (Effect.equipEffect none true) mana
    (timing := .sorcery)
    (tag? := some (.equip (some ObjectPred.worthy)))

/-- Typecycling `{cost}` (CR 702.29e). -/
def typecyclingAbility (landType : String) (mana : ManaCost := ManaCost.ofGeneric 1) :
    ActivatedAbility :=
  activated (Effect.searchLandTypeToHand landType) mana
    (activeZones := #[.hand])
    (tag? := some (.cycling (some landType)))
    (discardSource := true)

/-- Activated ability that is a power-up (CR 702.193). -/
def powerUpAbility (effect : Effect) (mana : ManaCost)
    (tap : Bool := false) : ActivatedAbility :=
  activated effect mana (tap := tap) (lifetimeLimit? := some 1) (tag? := some .powerUp)

end Mtg.Engine.OracleActivate
