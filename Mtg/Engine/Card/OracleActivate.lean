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
    (equipSubtype : Option String := none)
    (sacrificeAnotherSubtype : Option String := none)
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
    (loyalty : Option LoyaltySymbol := none) :
    ActivatedAbility :=
  let picks : Array CostPick :=
    (if discardACard then #[CostPick.discardACard] else #[]) ++
    (if discardLegendarySameName then #[CostPick.discardLegendarySameName] else #[]) ++
    (if sacrificeLegendaryArtifact then #[CostPick.sacrificeLegendaryArtifact] else #[]) ++
    (if sacrificeArtifact then #[CostPick.sacrificeArtifact] else #[]) ++
    (if sacrificeArtifactOrCreature then #[CostPick.sacrificeArtifactOrCreature] else #[]) ++
    (if sacrificeArtifactOrDiscardNonland then #[CostPick.sacrificeArtifactOrDiscardNonland] else #[]) ++
    (if sacrificeEquipmentAttachedToSource then #[CostPick.sacrificeEquipmentAttachedToSource] else #[]) ++
    (if tapAnUntappedCreatureYouControl then #[CostPick.tapUntappedCreature] else #[]) ++
    (match sacrificeAnotherSubtype with
     | some t => #[CostPick.sacrificeAnotherSubtype t]
     | none => #[])
  let condition : ActivationCondition :=
    if onlyIfYouControlLegendary then .youControlLegendary
    else if onlyIfYouAttackedWithTwoOrMore then .youAttackedWithTwoOrMore
    else if onlyIfOpponentDealtNoncombatDamage then .opponentDealtNoncombatDamage
    else if onlyIfYouControlCreatureToughnessAtLeast != 0 then
      .youControlCreatureToughnessAtLeast onlyIfYouControlCreatureToughnessAtLeast
    else if onlyIfGyCreaturesAtLeast != 0 then
      .gyCreaturesAtLeast onlyIfGyCreaturesAtLeast
    else .none
  let extra : ExtraActivationCost :=
    if sacrificeAnotherCreatureOrArtifact then .sacrificeAnotherCreatureOrArtifact
    else if exileSourceFromGraveyard then .exileSourceFromGraveyard
    else if removeIndestructibleCounter then .removeCounter .indestructible
    else if removeAnyNumberPlusOne then .removeAnyNumberPlusOne
    else if putStunCounterOnSource then .putStunCounterOnSource
    else .none
  let costReduction : ActivationCostReduction :=
    if costReductionIfYouControlLegendary != 0 then
      .ifYouControlLegendary costReductionIfYouControlLegendary
    else if costReductionPerEquipment != 0 then
      .perEquipment costReductionPerEquipment
    else match costReductionIfTargetPowerAtMost with
      | some (n, p) => .ifTargetPowerAtMost n p
      | none => .none
  let equipRestriction : EquipRestriction :=
    if equipWorthy then .worthy
    else match equipSubtype with
      | some s => .subtype s
      | none => .none
  {
    cost := {
      mana := mana
      tap := tap
      loyalty := loyalty
      sacrificeSource := sacrificeSource
      payLife := payLife
      discardSource := discardSource
      picks := picks
      extra := extra
    }
    condition := condition
    costReduction := costReduction
    effect := effect
    otherModes := otherModes
    onlyAsSorcery, onlyDuringYourTurn, onceEachTurn
    activateFromGraveyard, activateFromHand
    equipRestriction := equipRestriction
    powerUp
  }

/-- Equip `mana`, only as a sorcery. -/
def equipAbility (mana : ManaCost) (subtype : Option String := none) : ActivatedAbility :=
  activated (Effect.attachToTargetCreatureYouControl) mana (onlyAsSorcery := true)
    (equipSubtype := subtype)

/-- Equip worthy `mana`. -/
def equipWorthyAbility (mana : ManaCost) : ActivatedAbility :=
  activated (Effect.attachToTargetCreatureYouControl) mana (onlyAsSorcery := true)
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
