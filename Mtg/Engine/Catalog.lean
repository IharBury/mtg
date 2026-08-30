import Mtg.Engine.Card

/-!
# Sample cards

A small Oracle-faithful catalog used by engine tests. The engine itself is
card-agnostic; these definitions just exercise the rules we model.

Cards from Magic: The Gathering | The Hobbit (HOB) live in
`Mtg.Engine.Catalog.Hobbit`. Cards from The Hobbit Eternal (HOC) live in
`Mtg.Engine.Catalog.HobbitEternal`. Cards from Marvel Super Heroes (MSH) live
in `Mtg.Engine.Catalog.Marvel`. Decklists that use them live in `Mtg.Demo`.
-/

namespace Mtg.Engine.Catalog

open Mtg.Engine

/-- Fill a `CardDef` with the fields catalogs actually set. Type-specific
helpers (`creature`, `instant`, …) are thin wrappers so a new card is one
call instead of repeating `types`, `power := some`, and empty arrays. -/
def card (name : String) (types : Array CardType)
    (manaCost : ManaCost := ManaCost.empty) (subtypes : Array Subtype := #[])
    (oracleText : String := "") (power : Option Int := none)
    (toughness : Option Int := none) (keywords : Keywords := Keywords.none)
    (supertypes : Array Supertype := #[])
    (spellEffect : Option SpellEffect := none)
    (spellModes : Array SpellEffect := #[])
    (additionalCostSacrificeArtifactOrCreature : Bool := false)
    (additionalCostOrPayGeneric : Option Nat := none)
    (costReductionIfCreatureDied : Nat := 0)
    (costReductionIfTargetDamaged : Nat := 0)
    (costReductionIfTargetTapped : Nat := 0)
    (costReductionIfTargetAttackingNontoken : Nat := 0)
    (tapAddMana : Array ManaType := #[])
    (tapAddManaForEach : Array TapAddForEach := #[])
    (tapAddAnyColorEqualToPower : Bool := false)
    (tapAddAnyColorForInstantOrSorcery : Bool := false)
    (entersWithHopePerCreature : Bool := false)
    (entersTapped : Bool := false)
    (tapAddOneOf : Array ManaType := #[])
    (tapAddOneOfIfEnteredOrBasic : Array ManaType := #[])
    (tapAddAnyColor : Bool := false)
    (tapSacrificeAddAnyColor : Bool := false)
    (isToken : Bool := false)
    (cantBeCountered : Bool := false)
    (flashIfYouControlSubtype : Option String := none)
    (ward : Option Nat := none)
    (flashback : Option ManaCost := none)
    (colorIndicator : Option ColorSet := none)
    (entersTappedUnlessLegendary : Bool := false)
    (entersTappedUnlessEquipment : Bool := false)
    (tapAddAnyColorForLegendary : Bool := false)
    (costReductionEqualFlyingPower : Bool := false)
    (crew : Option Nat := none)
    (tapAddTwoAmong : Array ManaType := #[])
    (chooseOneOrBoth : Bool := false)
    (chooseTwoIfYouControlSubtype : Option String := none)
    (tapAddAnyColorAmongLegendaries : Bool := false)
    (tapAddRestricted : Option (Array ManaType × String) := none)
    (tapPayLifeAddOneOf : Option (Nat × Array ManaType) := none)
    (entersTappedUnlessPayLife : Option Nat := none)
    (tapAddCommanderIdentity : Bool := false)
    (additionalCostSacrificeCreature : Bool := false)
    (asEntersChooseCreatureType : Bool := false)
    (saga : Option SagaDef := none)
    (affinityForSubtype : Option String := none)
    (costReductionEqualOppArtifacts : Bool := false)
    (giftTreasure : Bool := false)
    (foodAlsoCreatesTreasure : Bool := false)
    (othersEnterWithPlusOneEqualToughness : Bool := false)
    (powerPerMountain : Nat := 0)
    (extraLandIfOtherSubtype : Option String := none)
    (tapAddColorlessPerSubtype : Option String := none)
    (cascade : Nat := 0)
    (kicker : Option ManaCost := none)
    (tokenDoubling : Bool := false)
    (drawTwoExceptFirstDrawStep : Bool := false)
    (staticAbilities : Array StaticAbility := #[])
    (triggeredAbilities : Array TriggeredAbility := #[])
    (activatedAbilities : Array ActivatedAbility := #[])
    (adventure : Option AdventureFace := none)
    (teamwork : Option Nat := none)
    (chooseBothIfTeamwork : Bool := false)
    (entersWithShield : Nat := 0)
    (otherFace : Option CardDef := none)
    (mayLookAtTopAnytime : Bool := false)
    (mayPlayLandsFromTop : Bool := false) : CardDef := {
  name, manaCost, types, subtypes, oracleText, power, toughness, keywords,
  supertypes, spellEffect, spellModes, additionalCostSacrificeArtifactOrCreature,
  additionalCostOrPayGeneric, costReductionIfCreatureDied, costReductionIfTargetDamaged,
  costReductionIfTargetTapped, costReductionIfTargetAttackingNontoken,
  tapAddMana, tapAddManaForEach, tapAddAnyColorEqualToPower,
  tapAddAnyColorForInstantOrSorcery, entersWithHopePerCreature, entersTapped,
  tapAddOneOf, tapAddOneOfIfEnteredOrBasic, tapAddAnyColor, tapSacrificeAddAnyColor, isToken, cantBeCountered,
  flashIfYouControlSubtype, ward, flashback, colorIndicator,
  entersTappedUnlessLegendary, entersTappedUnlessEquipment,
  tapAddAnyColorForLegendary, costReductionEqualFlyingPower, crew,
  tapAddTwoAmong, chooseOneOrBoth, chooseTwoIfYouControlSubtype,
  tapAddAnyColorAmongLegendaries, tapAddRestricted, tapPayLifeAddOneOf,
  entersTappedUnlessPayLife, tapAddCommanderIdentity,
  additionalCostSacrificeCreature, asEntersChooseCreatureType,
  saga, affinityForSubtype, costReductionEqualOppArtifacts, giftTreasure,
  foodAlsoCreatesTreasure, othersEnterWithPlusOneEqualToughness, powerPerMountain,
  extraLandIfOtherSubtype, tapAddColorlessPerSubtype, cascade, kicker,
  tokenDoubling, drawTwoExceptFirstDrawStep,
  staticAbilities, triggeredAbilities, activatedAbilities, adventure,
  teamwork, chooseBothIfTeamwork, entersWithShield, otherFace,
  mayLookAtTopAnytime, mayPlayLandsFromTop
}

/-- A basic land whose name is also its land type (CR 305.6). -/
def basicLand (landName : String) (color : Color) : CardDef :=
  card landName #[.land] (subtypes := #[landName]) (supertypes := #[.basic])
    (oracleText := s!"(\{T}: Add \{{color.letter}}.)")

def plains : CardDef := basicLand "Plains" .white
def island : CardDef := basicLand "Island" .blue
def swamp : CardDef := basicLand "Swamp" .black
def mountain : CardDef := basicLand "Mountain" .red
def forest : CardDef := basicLand "Forest" .green

/-- A creature used by engine tests and the Hobbit catalog. -/
def creature (name : String) (manaCost : ManaCost) (subtypes : Array Subtype)
    (power toughness : Int) (oracleText : String := "")
    (keywords : Keywords := Keywords.none)
    (tapAddMana : Array ManaType := #[])
    (supertypes : Array Supertype := #[])
    (staticAbilities : Array StaticAbility := #[])
    (triggeredAbilities : Array TriggeredAbility := #[])
    (activatedAbilities : Array ActivatedAbility := #[])
    (tapAddManaForEach : Array TapAddForEach := #[])
    (tapAddAnyColorEqualToPower : Bool := false)
    (tapAddAnyColorForInstantOrSorcery : Bool := false)
    (tapAddAnyColor : Bool := false)
    (adventure : Option AdventureFace := none)
    (costReductionIfCreatureDied : Nat := 0)
    (colorIndicator : Option ColorSet := none)
    (isToken : Bool := false)
    (cantBeCountered : Bool := false)
    (flashIfYouControlSubtype : Option String := none)
    (ward : Option Nat := none)
    (tapAddAnyColorForLegendary : Bool := false)
    (costReductionEqualFlyingPower : Bool := false)
    (tapAddRestricted : Option (Array ManaType × String) := none)
    (foodAlsoCreatesTreasure : Bool := false)
    (othersEnterWithPlusOneEqualToughness : Bool := false)
    (powerPerMountain : Nat := 0)
    (extraLandIfOtherSubtype : Option String := none)
    (tapAddColorlessPerSubtype : Option String := none)
    (affinityForSubtype : Option String := none)
    (costReductionEqualOppArtifacts : Bool := false)
    (cascade : Nat := 0)
    (tokenDoubling : Bool := false)
    (drawTwoExceptFirstDrawStep : Bool := false)
    (teamwork : Option Nat := none)
    (entersWithShield : Nat := 0)
    (otherFace : Option CardDef := none)
    (legendary := false) : CardDef :=
  card name #[.creature] manaCost subtypes oracleText (some power) (some toughness)
    keywords ((if legendary then #[.legendary] else #[]) ++ supertypes)
    (tapAddMana := tapAddMana)
    (tapAddManaForEach := tapAddManaForEach)
    (tapAddAnyColorEqualToPower := tapAddAnyColorEqualToPower)
    (tapAddAnyColorForInstantOrSorcery := tapAddAnyColorForInstantOrSorcery)
    (tapAddAnyColor := tapAddAnyColor)
    (staticAbilities := staticAbilities) (triggeredAbilities := triggeredAbilities)
    (activatedAbilities := activatedAbilities) (adventure := adventure)
    (costReductionIfCreatureDied := costReductionIfCreatureDied)
    (colorIndicator := colorIndicator) (isToken := isToken)
    (cantBeCountered := cantBeCountered)
    (flashIfYouControlSubtype := flashIfYouControlSubtype)
    (ward := ward)
    (tapAddAnyColorForLegendary := tapAddAnyColorForLegendary)
    (costReductionEqualFlyingPower := costReductionEqualFlyingPower)
    (tapAddRestricted := tapAddRestricted)
    (foodAlsoCreatesTreasure := foodAlsoCreatesTreasure)
    (othersEnterWithPlusOneEqualToughness := othersEnterWithPlusOneEqualToughness)
    (powerPerMountain := powerPerMountain)
    (extraLandIfOtherSubtype := extraLandIfOtherSubtype)
    (tapAddColorlessPerSubtype := tapAddColorlessPerSubtype)
    (affinityForSubtype := affinityForSubtype)
    (costReductionEqualOppArtifacts := costReductionEqualOppArtifacts)
    (cascade := cascade)
    (tokenDoubling := tokenDoubling)
    (drawTwoExceptFirstDrawStep := drawTwoExceptFirstDrawStep)
    (teamwork := teamwork)
    (entersWithShield := entersWithShield)
    (otherFace := otherFace)

/-- A legendary creature (CR 205.4 / 704.5j). -/
def legendaryCreature (name : String) (manaCost : ManaCost) (subtypes : Array Subtype)
    (power toughness : Int) (oracleText : String := "")
    (keywords : Keywords := Keywords.none)
    (tapAddMana : Array ManaType := #[])
    (supertypes : Array Supertype := #[])
    (staticAbilities : Array StaticAbility := #[])
    (triggeredAbilities : Array TriggeredAbility := #[])
    (activatedAbilities : Array ActivatedAbility := #[])
    (tapAddManaForEach : Array TapAddForEach := #[])
    (tapAddAnyColorEqualToPower : Bool := false)
    (tapAddAnyColorForInstantOrSorcery : Bool := false)
    (adventure : Option AdventureFace := none)
    (costReductionIfCreatureDied : Nat := 0)
    (ward : Option Nat := none)
    (costReductionEqualFlyingPower : Bool := false)
    (tapAddRestricted : Option (Array ManaType × String) := none)
    (foodAlsoCreatesTreasure : Bool := false)
    (othersEnterWithPlusOneEqualToughness : Bool := false)
    (powerPerMountain : Nat := 0)
    (extraLandIfOtherSubtype : Option String := none)
    (tapAddColorlessPerSubtype : Option String := none)
    (affinityForSubtype : Option String := none)
    (costReductionEqualOppArtifacts : Bool := false)
    (cascade : Nat := 0)
    (tokenDoubling : Bool := false)
    (drawTwoExceptFirstDrawStep : Bool := false)
    (teamwork : Option Nat := none)
    (entersWithShield : Nat := 0)
    (otherFace : Option CardDef := none) : CardDef :=
  creature name manaCost subtypes power toughness oracleText (legendary := true)
    (keywords := keywords) (tapAddMana := tapAddMana) (supertypes := supertypes)
    (staticAbilities := staticAbilities) (triggeredAbilities := triggeredAbilities)
    (activatedAbilities := activatedAbilities)
    (tapAddManaForEach := tapAddManaForEach)
    (tapAddAnyColorEqualToPower := tapAddAnyColorEqualToPower)
    (tapAddAnyColorForInstantOrSorcery := tapAddAnyColorForInstantOrSorcery)
    (adventure := adventure)
    (costReductionIfCreatureDied := costReductionIfCreatureDied)
    (ward := ward)
    (costReductionEqualFlyingPower := costReductionEqualFlyingPower)
    (tapAddRestricted := tapAddRestricted)
    (foodAlsoCreatesTreasure := foodAlsoCreatesTreasure)
    (othersEnterWithPlusOneEqualToughness := othersEnterWithPlusOneEqualToughness)
    (powerPerMountain := powerPerMountain)
    (extraLandIfOtherSubtype := extraLandIfOtherSubtype)
    (tapAddColorlessPerSubtype := tapAddColorlessPerSubtype)
    (affinityForSubtype := affinityForSubtype)
    (costReductionEqualOppArtifacts := costReductionEqualOppArtifacts)
    (cascade := cascade)
    (tokenDoubling := tokenDoubling)
    (drawTwoExceptFirstDrawStep := drawTwoExceptFirstDrawStep)
    (teamwork := teamwork)
    (entersWithShield := entersWithShield)
    (otherFace := otherFace)

/-- Instant or sorcery with an optional one-shot effect or modal modes. -/
def spellCard (cardType : CardType) (name : String) (manaCost : ManaCost)
    (oracleText : String) (spellEffect : Option SpellEffect := none)
    (spellModes : Array SpellEffect := #[])
    (additionalCostSacrificeArtifactOrCreature : Bool := false)
    (additionalCostOrPayGeneric : Option Nat := none)
    (costReductionIfCreatureDied : Nat := 0)
    (costReductionIfTargetDamaged : Nat := 0)
    (costReductionIfTargetTapped : Nat := 0)
    (costReductionIfTargetAttackingNontoken : Nat := 0)
    (activatedAbilities : Array ActivatedAbility := #[])
    (flashback : Option ManaCost := none)
    (cantBeCountered : Bool := false)
    (chooseOneOrBoth : Bool := false)
    (chooseTwoIfYouControlSubtype : Option String := none)
    (additionalCostSacrificeCreature : Bool := false)
    (affinityForSubtype : Option String := none)
    (costReductionEqualOppArtifacts : Bool := false)
    (giftTreasure : Bool := false)
    (cascade : Nat := 0)
    (kicker : Option ManaCost := none)
    (staticAbilities : Array StaticAbility := #[])
    (teamwork : Option Nat := none)
    (chooseBothIfTeamwork : Bool := false) : CardDef :=
  card name #[cardType] manaCost (oracleText := oracleText)
    (spellEffect := spellEffect) (spellModes := spellModes)
    (additionalCostSacrificeArtifactOrCreature :=
      additionalCostSacrificeArtifactOrCreature)
    (additionalCostOrPayGeneric := additionalCostOrPayGeneric)
    (costReductionIfCreatureDied := costReductionIfCreatureDied)
    (costReductionIfTargetDamaged := costReductionIfTargetDamaged)
    (costReductionIfTargetTapped := costReductionIfTargetTapped)
    (costReductionIfTargetAttackingNontoken := costReductionIfTargetAttackingNontoken)
    (activatedAbilities := activatedAbilities)
    (flashback := flashback)
    (cantBeCountered := cantBeCountered)
    (chooseOneOrBoth := chooseOneOrBoth)
    (chooseTwoIfYouControlSubtype := chooseTwoIfYouControlSubtype)
    (additionalCostSacrificeCreature := additionalCostSacrificeCreature)
    (affinityForSubtype := affinityForSubtype)
    (costReductionEqualOppArtifacts := costReductionEqualOppArtifacts)
    (giftTreasure := giftTreasure)
    (cascade := cascade)
    (kicker := kicker)
    (staticAbilities := staticAbilities)
    (teamwork := teamwork)
    (chooseBothIfTeamwork := chooseBothIfTeamwork)

/-- An instant, optionally with a one-shot effect or modal modes. -/
def instant (name : String) (manaCost : ManaCost) (oracleText : String)
    (spellEffect : Option SpellEffect := none)
    (spellModes : Array SpellEffect := #[])
    (additionalCostSacrificeArtifactOrCreature : Bool := false)
    (additionalCostOrPayGeneric : Option Nat := none)
    (costReductionIfCreatureDied : Nat := 0)
    (costReductionIfTargetDamaged : Nat := 0)
    (costReductionIfTargetTapped : Nat := 0)
    (costReductionIfTargetAttackingNontoken : Nat := 0)
    (activatedAbilities : Array ActivatedAbility := #[])
    (flashback : Option ManaCost := none)
    (cantBeCountered : Bool := false)
    (chooseOneOrBoth : Bool := false)
    (chooseTwoIfYouControlSubtype : Option String := none)
    (additionalCostSacrificeCreature : Bool := false)
    (affinityForSubtype : Option String := none)
    (costReductionEqualOppArtifacts : Bool := false)
    (giftTreasure : Bool := false)
    (cascade : Nat := 0)
    (kicker : Option ManaCost := none)
    (staticAbilities : Array StaticAbility := #[])
    (teamwork : Option Nat := none)
    (chooseBothIfTeamwork : Bool := false) : CardDef :=
  spellCard .instant name manaCost oracleText spellEffect
    (spellModes := spellModes)
    (additionalCostSacrificeArtifactOrCreature :=
      additionalCostSacrificeArtifactOrCreature)
    (additionalCostOrPayGeneric := additionalCostOrPayGeneric)
    (costReductionIfCreatureDied := costReductionIfCreatureDied)
    (costReductionIfTargetDamaged := costReductionIfTargetDamaged)
    (costReductionIfTargetTapped := costReductionIfTargetTapped)
    (costReductionIfTargetAttackingNontoken :=
      costReductionIfTargetAttackingNontoken)
    (activatedAbilities := activatedAbilities)
    (flashback := flashback)
    (cantBeCountered := cantBeCountered)
    (chooseOneOrBoth := chooseOneOrBoth)
    (chooseTwoIfYouControlSubtype := chooseTwoIfYouControlSubtype)
    (additionalCostSacrificeCreature := additionalCostSacrificeCreature)
    (affinityForSubtype := affinityForSubtype)
    (costReductionEqualOppArtifacts := costReductionEqualOppArtifacts)
    (giftTreasure := giftTreasure)
    (cascade := cascade)
    (kicker := kicker)
    (staticAbilities := staticAbilities)
    (teamwork := teamwork)
    (chooseBothIfTeamwork := chooseBothIfTeamwork)

/-- A sorcery, optionally with a one-shot effect or modal modes. -/
def sorcery (name : String) (manaCost : ManaCost) (oracleText : String)
    (spellEffect : Option SpellEffect := none)
    (spellModes : Array SpellEffect := #[])
    (additionalCostSacrificeArtifactOrCreature : Bool := false)
    (additionalCostOrPayGeneric : Option Nat := none)
    (costReductionIfCreatureDied : Nat := 0)
    (costReductionIfTargetDamaged : Nat := 0)
    (costReductionIfTargetTapped : Nat := 0)
    (costReductionIfTargetAttackingNontoken : Nat := 0)
    (activatedAbilities : Array ActivatedAbility := #[])
    (flashback : Option ManaCost := none)
    (cantBeCountered : Bool := false)
    (chooseOneOrBoth : Bool := false)
    (chooseTwoIfYouControlSubtype : Option String := none)
    (additionalCostSacrificeCreature : Bool := false)
    (affinityForSubtype : Option String := none)
    (costReductionEqualOppArtifacts : Bool := false)
    (giftTreasure : Bool := false)
    (cascade : Nat := 0)
    (kicker : Option ManaCost := none)
    (staticAbilities : Array StaticAbility := #[])
    (teamwork : Option Nat := none)
    (chooseBothIfTeamwork : Bool := false) : CardDef :=
  spellCard .sorcery name manaCost oracleText spellEffect
    (spellModes := spellModes)
    (additionalCostSacrificeArtifactOrCreature :=
      additionalCostSacrificeArtifactOrCreature)
    (additionalCostOrPayGeneric := additionalCostOrPayGeneric)
    (costReductionIfCreatureDied := costReductionIfCreatureDied)
    (costReductionIfTargetDamaged := costReductionIfTargetDamaged)
    (costReductionIfTargetTapped := costReductionIfTargetTapped)
    (costReductionIfTargetAttackingNontoken :=
      costReductionIfTargetAttackingNontoken)
    (activatedAbilities := activatedAbilities)
    (flashback := flashback)
    (cantBeCountered := cantBeCountered)
    (chooseOneOrBoth := chooseOneOrBoth)
    (chooseTwoIfYouControlSubtype := chooseTwoIfYouControlSubtype)
    (additionalCostSacrificeCreature := additionalCostSacrificeCreature)
    (affinityForSubtype := affinityForSubtype)
    (costReductionEqualOppArtifacts := costReductionEqualOppArtifacts)
    (giftTreasure := giftTreasure)
    (cascade := cascade)
    (kicker := kicker)
    (staticAbilities := staticAbilities)
    (teamwork := teamwork)
    (chooseBothIfTeamwork := chooseBothIfTeamwork)

/-- A non-Aura enchantment. -/
def enchantment (name : String) (manaCost : ManaCost) (oracleText : String)
    (keywords : Keywords := Keywords.none)
    (staticAbilities : Array StaticAbility := #[])
    (triggeredAbilities : Array TriggeredAbility := #[])
    (activatedAbilities : Array ActivatedAbility := #[])
    (subtypes : Array Subtype := #[])
    (entersWithHopePerCreature : Bool := false)
    (entersTapped : Bool := false)
    (supertypes : Array Supertype := #[])
    (ward : Option Nat := none)
    (asEntersChooseCreatureType : Bool := false)
    (adventure : Option AdventureFace := none)
    (saga : Option SagaDef := none) : CardDef :=
  card name #[.enchantment] manaCost subtypes oracleText (keywords := keywords)
    (supertypes := supertypes)
    (staticAbilities := staticAbilities) (triggeredAbilities := triggeredAbilities)
    (activatedAbilities := activatedAbilities)
    (entersWithHopePerCreature := entersWithHopePerCreature)
    (entersTapped := entersTapped)
    (ward := ward)
    (asEntersChooseCreatureType := asEntersChooseCreatureType)
    (adventure := adventure)
    (saga := saga)

/-- A catalog Saga chapter with parsed numerals and a real effect. -/
def chapter (roman effect : String) (ce : ChapterEffect) : SagaChapter :=
  SagaChapter.of roman effect ce

/-- A Saga enchantment (CR 714). -/
def saga (name : String) (manaCost : ManaCost) (oracleText : String)
    (sacrificeAfter : String) (chapters : Array SagaChapter) : CardDef :=
  enchantment name manaCost oracleText
    (subtypes := #["Saga"])
    (saga := some { sacrificeAfter, chapters })

/-- An Aura enchantment (CR 303.4). -/
def aura (name : String) (manaCost : ManaCost) (oracleText : String)
    (keywords : Keywords := Keywords.none)
    (staticAbilities : Array StaticAbility := #[])
    (triggeredAbilities : Array TriggeredAbility := #[]) : CardDef :=
  enchantment name manaCost oracleText keywords staticAbilities triggeredAbilities
    (subtypes := #["Aura"])

/-- An artifact, including Equipment. -/
def artifact (name : String) (manaCost : ManaCost) (oracleText : String)
    (subtypes : Array Subtype := #[])
    (staticAbilities : Array StaticAbility := #[])
    (triggeredAbilities : Array TriggeredAbility := #[])
    (activatedAbilities : Array ActivatedAbility := #[])
    (tapAddMana : Array ManaType := #[])
    (tapAddManaForEach : Array TapAddForEach := #[])
    (tapAddAnyColor : Bool := false)
    (tapSacrificeAddAnyColor : Bool := false)
    (isToken : Bool := false)
    (keywords : Keywords := Keywords.none)
    (supertypes : Array Supertype := #[])
    (crew : Option Nat := none)
    (tapAddTwoAmong : Array ManaType := #[])
    (power : Option Int := none)
    (toughness : Option Int := none)
    (tapAddAnyColorAmongLegendaries : Bool := false)
    (tapAddCommanderIdentity : Bool := false)
    (adventure : Option AdventureFace := none)
    (legendary := false)
    (entersTapped := false)
    (ward : Option Nat := none) : CardDef :=
  card name #[.artifact] manaCost subtypes oracleText
    (power := power) (toughness := toughness)
    (keywords := keywords)
    (supertypes := (if legendary then #[.legendary] else #[]) ++ supertypes)
    (staticAbilities := staticAbilities) (triggeredAbilities := triggeredAbilities)
    (activatedAbilities := activatedAbilities) (tapAddMana := tapAddMana)
    (tapAddManaForEach := tapAddManaForEach)
    (tapAddAnyColor := tapAddAnyColor)
    (tapSacrificeAddAnyColor := tapSacrificeAddAnyColor)
    (isToken := isToken)
    (crew := crew)
    (tapAddTwoAmong := tapAddTwoAmong)
    (tapAddAnyColorAmongLegendaries := tapAddAnyColorAmongLegendaries)
    (tapAddCommanderIdentity := tapAddCommanderIdentity)
    (adventure := adventure)
    (entersTapped := entersTapped)
    (ward := ward)

/-- An artifact creature, optionally legendary. -/
def artifactCreature (name : String) (manaCost : ManaCost) (subtypes : Array Subtype)
    (power toughness : Int) (oracleText : String := "")
    (keywords : Keywords := Keywords.none)
    (staticAbilities : Array StaticAbility := #[])
    (triggeredAbilities : Array TriggeredAbility := #[])
    (activatedAbilities : Array ActivatedAbility := #[])
    (legendary := false)
    (ward : Option Nat := none)
    (otherFace : Option CardDef := none)
    (entersWithShield : Nat := 0) : CardDef :=
  card name #[.artifact, .creature] manaCost subtypes oracleText
    (some power) (some toughness) keywords
    ((if legendary then #[.legendary] else #[]) )
    (staticAbilities := staticAbilities)
    (triggeredAbilities := triggeredAbilities)
    (activatedAbilities := activatedAbilities)
    (ward := ward)
    (otherFace := otherFace)
    (entersWithShield := entersWithShield)

/-- A nonbasic land. -/
def land (name : String) (oracleText : String)
    (tapAddMana : Array ManaType := #[])
    (tapAddOneOf : Array ManaType := #[])
    (tapAddOneOfIfEnteredOrBasic : Array ManaType := #[])
    (activatedAbilities : Array ActivatedAbility := #[])
    (subtypes : Array Subtype := #[])
    (supertypes : Array Supertype := #[])
    (entersTapped : Bool := false)
    (triggeredAbilities : Array TriggeredAbility := #[])
    (staticAbilities : Array StaticAbility := #[])
    (entersTappedUnlessLegendary : Bool := false)
    (entersTappedUnlessEquipment : Bool := false)
    (tapPayLifeAddOneOf : Option (Nat × Array ManaType) := none)
    (entersTappedUnlessPayLife : Option Nat := none)
    (legendary := false) : CardDef :=
  card name #[.land] (subtypes := subtypes) (oracleText := oracleText)
    (supertypes := (if legendary then #[.legendary] else #[]) ++ supertypes)
    (tapAddMana := tapAddMana)
    (tapAddOneOf := tapAddOneOf)
    (tapAddOneOfIfEnteredOrBasic := tapAddOneOfIfEnteredOrBasic)
    (activatedAbilities := activatedAbilities)
    (entersTapped := entersTapped) (triggeredAbilities := triggeredAbilities)
    (staticAbilities := staticAbilities)
    (entersTappedUnlessLegendary := entersTappedUnlessLegendary)
    (entersTappedUnlessEquipment := entersTappedUnlessEquipment)
    (tapPayLifeAddOneOf := tapPayLifeAddOneOf)
    (entersTappedUnlessPayLife := entersTappedUnlessPayLife)

/-- A legendary land. -/
def legendaryLand (name : String) (oracleText : String)
    (tapAddMana : Array ManaType := #[])
    (tapAddOneOf : Array ManaType := #[])
    (activatedAbilities : Array ActivatedAbility := #[])
    (subtypes : Array Subtype := #[])
    (entersTapped : Bool := false)
    (entersTappedUnlessLegendary : Bool := false)
    (tapPayLifeAddOneOf : Option (Nat × Array ManaType) := none)
    (entersTappedUnlessPayLife : Option Nat := none)
    (staticAbilities : Array StaticAbility := #[]) : CardDef :=
  land name oracleText (legendary := true)
    (tapAddMana := tapAddMana) (tapAddOneOf := tapAddOneOf)
    (activatedAbilities := activatedAbilities) (subtypes := subtypes)
    (entersTapped := entersTapped)
    (entersTappedUnlessLegendary := entersTappedUnlessLegendary)
    (tapPayLifeAddOneOf := tapPayLifeAddOneOf)
    (entersTappedUnlessPayLife := entersTappedUnlessPayLife)
    (staticAbilities := staticAbilities)

/-- A Treasure token (CR 111 / 701.42). -/
def treasureToken : CardDef :=
  artifact "Treasure" ManaCost.empty
    "{T}, Sacrifice this artifact: Add one mana of any color."
    (subtypes := #["Treasure"])
    (tapSacrificeAddAnyColor := true)
    (isToken := true)

/-- A creature token with a color indicator (CR 202.2e). -/
def tokenCreature (name : String) (subtypes : Array Subtype)
    (power toughness : Int) (color : Color)
    (keywords : Keywords := Keywords.none) : CardDef :=
  creature name ManaCost.empty subtypes power toughness
    (colorIndicator := some (ColorSet.singleton color))
    (keywords := keywords)
    (isToken := true)

/-- A 1/1 white Human Soldier creature token. -/
def humanSoldierToken : CardDef :=
  tokenCreature "Human Soldier" #["Human", "Soldier"] 1 1 .white

/-- A Food token. -/
def foodToken : CardDef :=
  artifact "Food" ManaCost.empty
    "{2}, {T}, Sacrifice this artifact: You gain 3 life."
    (subtypes := #["Food"])
    (activatedAbilities := #[{
      cost := { mana := ManaCost.ofGeneric 2, tap := true, sacrificeSource := true }
      effect := .gainLife 3
    }])
    (isToken := true)

def wolfToken : CardDef :=
  tokenCreature "Wolf" #["Wolf"] 2 2 .green

def dwarfToken : CardDef :=
  tokenCreature "Dwarf" #["Dwarf"] 2 2 .red

def bearToken : CardDef :=
  tokenCreature "Bear" #["Bear"] 2 2 .green

def elfToken : CardDef :=
  tokenCreature "Elf" #["Elf"] 1 1 .green

/-- An activated ability (CR 602.1). -/
def activated (effect : AbilityEffect) (mana : ManaCost := ManaCost.empty)
    (tap : Bool := false) (sacrificeSource : Bool := false)
    (sacrificeAnotherCreatureOrArtifact : Bool := false)
    (onlyAsSorcery : Bool := false) (onlyDuringYourTurn : Bool := false)
    (onceEachTurn : Bool := false)
    (otherModes : Array AbilityEffect := #[]) (payLife : Nat := 0)
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
    (removeIndestructibleCounter : Bool := false)
    (sacrificeLegendaryArtifact : Bool := false)
    (discardLegendarySameName : Bool := false)
    (sacrificeArtifact : Bool := false)
    (powerUp : Bool := false)
    (equipWorthy : Bool := false) :
    ActivatedAbility := {
  cost := {
    mana := mana
    tap := tap
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
  }
  effect, otherModes, onlyAsSorcery, onlyDuringYourTurn, onceEachTurn
  activateFromGraveyard, activateFromHand, onlyIfYouControlLegendary
  costReductionIfYouControlLegendary, equipSubtype, costReductionPerEquipment
  onlyIfYouAttackedWithTwoOrMore, powerUp, equipWorthy
}

/-- Equip `mana`: attach to target creature you control, only as a sorcery.
`subtype` restricts Equip to that creature type (e.g. Equip Human). -/
def equipAbility (mana : ManaCost) (subtype : Option String := none) : ActivatedAbility :=
  activated .attachToTargetCreatureYouControl mana (onlyAsSorcery := true)
    (equipSubtype := subtype)

/-- Equip worthy `mana` (MSH): attach only to a worthy creature. -/
def equipWorthyAbility (mana : ManaCost) : ActivatedAbility :=
  activated .attachToTargetCreatureYouControl mana (onlyAsSorcery := true)
    (equipWorthy := true)

/-- Equipment with a standard Equip cost (CR 301.5 / 702.6). -/
def equipment (name : String) (manaCost : ManaCost) (oracleText : String)
    (equip : ManaCost)
    (staticAbilities : Array StaticAbility := #[])
    (triggeredAbilities : Array TriggeredAbility := #[])
    (keywords : Keywords := Keywords.none)
    (equipSubtype : Option String := none)
    (moreEquips : Array ActivatedAbility := #[])
    (legendary := false)
    (adventure : Option AdventureFace := none) : CardDef :=
  artifact name manaCost oracleText
    (subtypes := #["Equipment"])
    (keywords := keywords)
    (legendary := legendary)
    (staticAbilities := staticAbilities)
    (triggeredAbilities := triggeredAbilities)
    (activatedAbilities :=
      #[equipAbility equip (subtype := equipSubtype)] ++ moreEquips)
    (adventure := adventure)

/-- Typecycling `{cost}`: discard this card from hand, search for a `landType`
card, put it into your hand, then shuffle (CR 702.29). -/
def typecyclingAbility (landType : String) (mana : ManaCost := ManaCost.ofGeneric 1) :
    ActivatedAbility :=
  activated (.searchLandTypeToHand landType) mana
    (discardSource := true) (activateFromHand := true)

/-- Adventure characteristics used while the card is a spell (CR 715.2). -/
def adventure (name : String) (manaCost : ManaCost) (oracleText : String)
    (spellEffect : SpellEffect) (cardType : CardType := .sorcery)
    (additionalCostSacrificeCreature : Bool := false) : AdventureFace := {
  name, manaCost, types := #[cardType], subtypes := #["Adventure"],
  oracleText, spellEffect := some spellEffect,
  additionalCostSacrificeCreature
}

/-- A red instant that deals `amount` damage to any target. -/
def damageInstant (name : String) (amount : Nat) : CardDef :=
  instant name (ManaCost.ofColor .red)
    s!"{name} deals {amount} damage to any target."
    (some (.dealDamage amount))

def grizzlyBears : CardDef :=
  creature "Grizzly Bears" (ManaCost.ofGenericAndColor 1 .green) #["Bear"] 2 2

def grayOgre : CardDef :=
  creature "Gray Ogre" (ManaCost.ofGenericAndColor 2 .red) #["Ogre"] 2 2

def hillGiant : CardDef :=
  creature "Hill Giant" (ManaCost.ofGenericAndColor 3 .red) #["Giant"] 3 3

def canyonMinotaur : CardDef :=
  creature "Canyon Minotaur" (ManaCost.ofGenericAndColor 3 .red) #["Minotaur"] 3 3

def ragingGoblin : CardDef :=
  creature "Raging Goblin" (ManaCost.ofColor .red) #["Goblin"] 1 1
    (oracleText := "Haste (This creature can attack and {T} as soon as it comes under your control.)")
    (keywords := Keyword.haste)

def llanowarElves : CardDef :=
  creature "Llanowar Elves" (ManaCost.ofColor .green) #["Elf", "Druid"] 1 1
    (oracleText := "{T}: Add {G}.") (tapAddMana := #[.colored .green])

def crawWurm : CardDef :=
  creature "Craw Wurm" (ManaCost.ofGenericAndColor 4 .green) #["Wurm"] 6 4

def centaurCourser : CardDef :=
  creature "Centaur Courser" (ManaCost.ofGenericAndColor 2 .green) #["Centaur"] 3 3

def rumblingBaloth : CardDef :=
  creature "Rumbling Baloth" (ManaCost.ofGenericAndColors 2 [.green, .green])
    #["Beast"] 4 4

def giantSpider : CardDef :=
  creature "Giant Spider" (ManaCost.ofGenericAndColor 3 .green) #["Spider"] 2 4
    (oracleText := "Reach (This creature can block creatures with flying.)")
    (keywords := Keyword.reach)

def lightningBolt : CardDef := damageInstant "Lightning Bolt" 3

def shock : CardDef := damageInstant "Shock" 2

def giantGrowth : CardDef :=
  instant "Giant Growth" (ManaCost.ofColor .green)
    "Target creature gets +3/+3 until end of turn."
    (some (.pump 3 3))

/-- Repeat a card `n` times. -/
def copies (n : Nat) (c : CardDef) : Array CardDef :=
  Array.replicate n c

/-- Leftover modeled static. -/
def leftoverStatic (t : ModeledStatic) : StaticAbility :=
  .msh t

/-- Leftover modeled activation. -/
def leftoverAct (t : ModeledAbility) (mana : ManaCost := ManaCost.empty)
    (tap : Bool := false) (powerUp : Bool := false)
    (onlyAsSorcery : Bool := false) : ActivatedAbility :=
  activated (.msh t) mana (tap := tap) (powerUp := powerUp)
    (onlyAsSorcery := onlyAsSorcery)

/-- Activated ability that is a power-up (activate only once; reduced if
the source entered this turn). -/
def powerUpAbility (effect : AbilityEffect) (mana : ManaCost)
    (tap : Bool := false) : ActivatedAbility :=
  activated effect mana (tap := tap) (powerUp := true)

/-- Dual land: enters tapped, gains 1 life, `{T}: Add` one of these colors. -/
def gainLifeDualLand (name : String) (oracleText : String)
    (colors : Array ManaType) : CardDef :=
  land name oracleText
    (entersTapped := true)
    (triggeredAbilities := #[.onEnterGainLife 1])
    (tapAddOneOf := colors)

/-- Dual land: `{T}: Add {C}` plus a two-color tap that requires this land
entered this turn or a basic land you control. -/
def conditionalDualLand (name : String) (oracleText : String)
    (colors : Array ManaType) : CardDef :=
  land name oracleText
    (tapAddMana := #[.colorless])
    (tapAddOneOfIfEnteredOrBasic := colors)

/-- MSH dual land: enters tapped, gains 1 life, `{T}: Add` two colors. -/
def mshGainLifeDualLand (name : String) (oracleText : String)
    (addColors : ModeledAbility) : CardDef :=
  gainLifeDualLand name oracleText addColors.addManaTypes

/-- MSH dual land: `{T}: Add {C}` plus a two-color tap that requires this
land entered this turn or a basic land. -/
def mshConditionalDualLand (name : String) (oracleText : String)
    (addConditional : ModeledAbility) : CardDef :=
  conditionalDualLand name oracleText addConditional.addManaTypes

#guard (gainLifeDualLand "Silent Plaza" ""
  #[.colored .blue, .colored .black]).tapAddOneOf ==
  #[.colored .blue, .colored .black]
#guard (gainLifeDualLand "Silent Plaza" ""
  #[.colored .blue, .colored .black]).triggeredAbilities == #[.onEnterGainLife 1]
#guard (conditionalDualLand "Silent Lair" ""
  #[.colored .blue, .colored .black]).tapAddOneOfIfEnteredOrBasic ==
  #[.colored .blue, .colored .black]
#guard (conditionalDualLand "Silent Lair" ""
  #[.colored .blue, .colored .black]).requiresEnteredOrBasicAdd
#guard (legendaryCreature "Silent Legend" ManaCost.empty #[] 1 1).hasSupertype .legendary
#guard (creature "Silent Legend" ManaCost.empty #[] 1 1 (legendary := true)).hasSupertype .legendary
#guard (legendaryLand "Silent Keep" "").hasSupertype .legendary
#guard (instant "Silent Bolt" (ManaCost.ofColor .red) "" (some (.dealDamage 1))).isInstant
#guard (sorcery "Silent Flame" (ManaCost.ofColor .red) "" (some (.dealDamage 1))).isSorcery
#guard mountain.colors.isColorless
#guard grizzlyBears.colors.isMonocolored
#guard grizzlyBears.hasSorcerySpeed
#guard !lightningBolt.hasSorcerySpeed
#guard !mountain.hasSorcerySpeed
#guard (ragingGoblin.summary.splitOn "haste").length > 1
#guard (llanowarElves.summary.splitOn "{T}: Add {G}").length > 1
#guard (lightningBolt.summary.splitOn "deals 3 damage").length > 1
#guard (lightningBolt.summary.splitOn "{R}").length > 1
#guard (mountain.summary.splitOn "{T}: Add {R}").length > 1
#guard (mountain.summary.splitOn "{0}").length == 1
#guard mountain.summary == "Mountain Basic Land — Mountain ({T}: Add {R}.)"
#guard plains.oracleText == "({T}: Add {W}.)"
#guard island.oracleText == "({T}: Add {U}.)"
#guard swamp.oracleText == "({T}: Add {B}.)"
#guard mountain.oracleText == "({T}: Add {R}.)"
#guard forest.oracleText == "({T}: Add {G}.)"
#guard ragingGoblin.oracleText ==
  "Haste (This creature can attack and {T} as soon as it comes under your control.)"
#guard giantSpider.oracleText == "Reach (This creature can block creatures with flying.)"
#guard (giantSpider.summary.splitOn "reach").length > 1
#guard giantGrowth.spellEffect == some (.pump 3 3)
#guard giantGrowth.isInstant
#guard (equipAbility (ManaCost.ofGeneric 3)).onlyAsSorcery
#guard (equipAbility (ManaCost.ofGeneric 3)).effect == .attachToTargetCreatureYouControl
#guard (activated (.sourceGets 2 2) (payLife := 2) (onceEachTurn := true)).cost.payLife == 2
#guard (activated (.sourceGets 2 2) (payLife := 2) (onceEachTurn := true)).onceEachTurn
#guard (adventure "Spew Flame" (ManaCost.ofGenericAndColor 4 .red) ""
  (.dealDamageToCreature 5)).subtypes.any (· == "Adventure")
#guard lightningBolt.hasType .instant
#guard !grizzlyBears.hasType .instant
#guard lightningBolt.hasCastKind .burn
#guard giantGrowth.hasCastKind .pump
#guard !lightningBolt.hasCastKind .pump
#guard (lightningBolt.spellEffect.map SpellEffect.castKind) == some .burn
#guard (giantGrowth.spellEffect.map SpellEffect.castKind) == some .pump
#guard (land "Silent Passage" "{T}: Add {C}." (tapAddMana := #[.colorless])).isLand
#guard (artifact "Silent Spear" (ManaCost.ofGeneric 1) ""
  (subtypes := #["Equipment"])).isEquipment
#guard (equipment "Silent Blade" (ManaCost.ofGeneric 1) ""
  (ManaCost.ofGeneric 2)).isEquipment
#guard (equipment "Silent Blade" (ManaCost.ofGeneric 1) ""
  (ManaCost.ofGeneric 2)).activatedAbilities ==
  #[equipAbility (ManaCost.ofGeneric 2)]
#guard (artifactCreature "Silent Construct" ManaCost.empty #["Construct"] 1 1
  (legendary := true)).hasSupertype .legendary
#guard (artifactCreature "Silent Construct" ManaCost.empty #["Construct"] 1 1
  (legendary := true)).hasType .artifact
#guard (artifactCreature "Silent Construct" ManaCost.empty #["Construct"] 1 1
  (legendary := true)).hasType .creature
#guard (mshGainLifeDualLand "Silent Plaza" "" (.addOneOf .blue .black)).entersTapped
#guard (mshConditionalDualLand "Silent Keep" ""
  (.addOneOf .blue .black true)).tapAddMana == #[.colorless]
#guard (powerUpAbility (.putPlusOnePlusOneOnSource 1) (ManaCost.ofGeneric 3)).powerUp
#guard (Keywords.mergeAll #[Keyword.flying, Keyword.trample, Keyword.haste]) ==
  (Keyword.flying.merge Keyword.trample |>.merge Keyword.haste)
#guard (aura "Silent Strands" (ManaCost.ofGenericAndColor 3 .green) "").isAura

end Mtg.Engine.Catalog
