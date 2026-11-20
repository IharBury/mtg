import Mtg.Engine.Card.CardDef

/-!
Helpers for building the activated abilities the Oracle parser recognizes.
-/

namespace Mtg.Engine.OracleActivate

/-- An activated ability (CR 602.1). -/
def activated (effect : Effect) (mana : ManaCost := ManaCost.empty)
    (tap : Bool := false) (sacrificeSource : Bool := false)
    (sacrificeAnotherCreatureOrArtifact : Bool := false)
    (onlyAsSorcery : Bool := false) (onlyDuringYourTurn : Bool := false)
    (onceEachTurn : Bool := false)
    (otherModes : Array Effect := #[]) (payLife : Nat := 0)
    (activateFromGraveyard : Bool := false)
    (activateFromHand : Bool := false)
    (onlyIfYouControlLegendary : Bool := false)
    (discardSource : Bool := false)
    (costReductionIfYouControlLegendary : Nat := 0)
    (equipSubtype : Option CardSubtype := none)
    (sacrificeAnotherSubtype : Option CardSubtype := none)
    (sacrificeAnotherCreature : Bool := false)
    (discardACard : Bool := false)
    (costReductionPerEquipment : Nat := 0)
    (tapAnUntappedCreatureYouControl : Bool := false)
    (onlyIfYouAttackedWithTwoOrMore : Bool := false)
    (onlyIfOpponentDealtNoncombatDamage : Bool := false)
    (exileSourceFromGraveyard : Bool := false)
    (removeIndestructibleCounter : Bool := false)
    (sacrificeLegendaryArtifact : Bool := false)
    (discardLegendarySameName : Bool := false)
    (sacrificeArtifact : Bool := false)
    (powerUp : Bool := false)
    (equipWorthy : Bool := false)
    (sacrificeArtifactOrCreature : Bool := false)
    (sacrificeArtifactOrDiscardNonland : Bool := false)
    (removeAnyNumberPlusOne : Bool := false)
    (putStunCounterOnSource : Bool := false)
    (sacrificeEquipmentAttachedToSource : Bool := false)
    (onlyIfYouControlCreatureToughnessAtLeast : Nat := 0)
    (onlyIfGyCreaturesAtLeast : Nat := 0)
    (costReductionIfTargetPowerAtMost : Option (Nat × Int) := none)
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
  {
    cost := { items, bindVar? := extraCost.bindVar? }
    effect :=
      if effect == Effect.attachToTargetCreatureYouControl && (equipSubtype.isSome || equipWorthy) then
        Effect.equipEffect equipSubtype equipWorthy
      else
        effect
    otherModes := otherModes
    onlyAsSorcery, onlyDuringYourTurn, onceEachTurn
    activateFromGraveyard, activateFromHand, onlyIfYouControlLegendary
    costReductionIfYouControlLegendary, equipSubtype, costReductionPerEquipment
    onlyIfYouAttackedWithTwoOrMore, onlyIfOpponentDealtNoncombatDamage, powerUp, equipWorthy
    onlyIfYouControlCreatureToughnessAtLeast, onlyIfGyCreaturesAtLeast
    costReductionIfTargetPowerAtMost
  }

/-- Equip `mana`, only as a sorcery. -/
def equipAbility (mana : ManaCost) (subtype : Option CardSubtype := none) : ActivatedAbility :=
  activated (Effect.equipEffect subtype false) mana (onlyAsSorcery := true)
    (equipSubtype := subtype)

/-- Equip worthy `mana`. -/
def equipWorthyAbility (mana : ManaCost) : ActivatedAbility :=
  activated (Effect.equipEffect none true) mana (onlyAsSorcery := true)
    (equipWorthy := true)

/-- Typecycling `{cost}`. -/
def typecyclingAbility (landType : String) (mana : ManaCost := ManaCost.ofGeneric 1) :
    ActivatedAbility :=
  activated (Effect.searchLandTypeToHand landType) mana
    (discardSource := true) (activateFromHand := true)

/-- Activated ability that is a power-up. -/
def powerUpAbility (effect : Effect) (mana : ManaCost)
    (tap : Bool := false) : ActivatedAbility :=
  activated effect mana (tap := tap) (powerUp := true)

end Mtg.Engine.OracleActivate
