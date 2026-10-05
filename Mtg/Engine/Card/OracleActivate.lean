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
    ActivatedAbility := {
  cost := {
    mana := mana
    tap := tap
    loyalty := loyalty
    sacrificeSource := sacrificeSource
    sacrificeAnotherCreatureOrArtifact := sacrificeAnotherCreatureOrArtifact
    payLife := payLife
    discardSource := discardSource
    sacrificeAnotherSubtype := sacrificeAnotherSubtype
    discardACard := discardACard
    tapAnUntappedCreatureYouControl := tapAnUntappedCreatureYouControl
    removeIndestructibleCounter := removeIndestructibleCounter
    sacrificeLegendaryArtifact := sacrificeLegendaryArtifact
    discardLegendarySameName := discardLegendarySameName
    sacrificeArtifact := sacrificeArtifact
    sacrificeArtifactOrCreature := sacrificeArtifactOrCreature
    sacrificeArtifactOrDiscardNonland := sacrificeArtifactOrDiscardNonland
    removeAnyNumberPlusOne := removeAnyNumberPlusOne
    putStunCounterOnSource := putStunCounterOnSource
    sacrificeEquipmentAttachedToSource := sacrificeEquipmentAttachedToSource
  }
  effect := effect
  otherModes := otherModes
  onlyAsSorcery, onlyDuringYourTurn, onceEachTurn
  activateFromGraveyard, activateFromHand, onlyIfYouControlLegendary
  costReductionIfYouControlLegendary, equipSubtype, costReductionPerEquipment
  onlyIfYouAttackedWithTwoOrMore, onlyIfOpponentDealtNoncombatDamage, powerUp, equipWorthy
  onlyIfYouControlCreatureToughnessAtLeast, onlyIfGyCreaturesAtLeast
  costReductionIfTargetPowerAtMost
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
