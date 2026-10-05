import Mtg.Engine.Mana

/-!
# Reality Fracture static abilities

Static abilities first printed in Reality Fracture (FRA). They are nested
under `StaticAbility.fra`, so `StaticAbility` stays under the constructor
limit of the C runtime. `text` is the printed line the parser matches.
-/

namespace Mtg.Engine

inductive FraStatic where
  /-- As long as you've scried or surveilled this turn, this creature can
  attack as though it didn't have defender. -/
  | attackDespiteDefenderIfScried
  /-- This creature gets +2/+0 for every seven cards in your graveyard. -/
  | powerPerSevenInGraveyard
  /-- Creatures you control have trample. -/
  | creaturesYouControlHaveTrample
  /-- During your turn, this creature has first strike. -/
  | firstStrikeDuringYourTurn
  /-- Equipped creature gets +2/+0 and has an attack trigger granting your
  choice of trample or deathtouch (Hunter's Axe). -/
  | equippedHuntersAxe
  /-- Enchant artifact or non-Aura enchantment. -/
  | enchantArtifactOrNonAuraEnchantment
  /-- Enchanted permanent is a Construct creature with base power and
  toughness 5/5 in addition to its other types. -/
  | enchantedIsConstruct55
  /-- Enchanted creature gets +1/+0 and has deathtouch. -/
  | enchantedGetsOneAndDeathtouch
  /-- This creature has vigilance as long as you control a Jace planeswalker. -/
  | vigilanceIfJace
  /-- This creature gets +1/+0 and has flying as long as there are seven or
  more cards in your graveyard. -/
  | powerAndFlyingIfSevenInGraveyard
  /-- Each creature you control with a +1/+1 counter on it has vigilance. -/
  | plusOneCreaturesHaveVigilance
  /-- As long as an opponent was dealt noncombat damage this turn, this
  creature has flying and haste. -/
  | flyingHasteIfOpponentDealtNoncombat
  /-- Equipped creature gets +1/+0 and has flying and an attack trigger that
  gains you 1 life (Medic's Kitesail). -/
  | equippedMedicsKitesail
  /-- This land enters tapped. As it enters, choose a color. -/
  | entersTappedChooseColor
  /-- `{T}`: Add one mana of the chosen color. -/
  | tapAddChosenColor
  /-- Creatures you control can attack as though they didn't have defender. -/
  | creaturesAttackDespiteDefender
  /-- Creature tokens you control get +1/+0 and have vigilance. -/
  | creatureTokensGetOneAndVigilance
  /-- `{T}`: Add `{C}`. This mana can't be spent to cast spells from your hand. -/
  | tapAddColorlessNotFromHand
  /-- `{T}`: Add one mana of any color. Spend this mana only to cast a
  planeswalker spell. -/
  | tapAddAnyColorPlaneswalkerOnly
  /-- Noncreature spells your opponents cast cost `{1}` more to cast. -/
  | opponentsNoncreatureSpellsCostMore
  /-- Planeswalkers you control have “No more than one creature can attack
  this planeswalker each combat.” -/
  | planeswalkersAttackedByOneAtMost
  /-- If one or more +1/+1 counters would be put on a creature you control,
  that many plus one are put on it instead. -/
  | extraPlusOneCounter
  /-- During combat, players can't cast spells or activate abilities that
  aren't mana abilities. -/
  | noSpellsOrAbilitiesDuringCombat
  /-- Noncreature spells you cast cost `{1}` less to cast. -/
  | noncreatureSpellsCostLess
  /-- This spell costs `{2}` less to cast if you've cast a noncreature spell
  this turn. -/
  | costsLessIfCastNoncreature
  /-- If a creature an opponent controls would die, exile it instead. -/
  | exileOpponentsDyingCreatures
  /-- Ward—Discard a card. -/
  | wardDiscardCard
  /-- Ward—Sacrifice three permanents. -/
  | wardSacrificeThreePermanents
  /-- This gets +1/+0 for each creature and planeswalker card in your
  graveyard. -/
  | powerPerCreatureAndPlaneswalkerCard
  /-- Each other creature you control with a +1/+1 counter on it has haste. -/
  | otherPlusOneCreaturesHaveHaste
  /-- Creatures you control have haste. -/
  | creaturesYouControlHaveHaste
  /-- If a source you control would deal noncombat damage to an opponent or
  a permanent an opponent controls, it deals that much plus 1 instead. -/
  | noncombatDamagePlusOne
  /-- This creature's power is equal to the number of basic land types among
  lands you control (CR 604.3). -/
  | powerEqualsBasicLandTypes
  /-- Other creatures you control have trample. -/
  | otherCreaturesHaveTrample
  /-- Lands you control have hexproof. -/
  | landsHaveHexproof
  /-- This has hexproof as long as it hasn't dealt combat damage yet. -/
  | hexproofUntilCombatDamage
  /-- Thopters you control have haste. -/
  | thoptersHaveHaste
  /-- Artifact creatures you control have vigilance. -/
  | artifactCreaturesHaveVigilance
  /-- This doesn't untap during your untap step. -/
  | doesntUntap
  /-- Creatures you control get +2/+2 (Ajani emblem). -/
  | emblemCreaturesGetTwoTwo
  /-- `{T}`, Sacrifice this token: Add three mana of any one color (Lotus). -/
  | tapSacrificeAddThreeOfOneColor
  /-- As this creature enters, choose a nonland card name. -/
  | entersChooseNonlandCardName
  /-- Spells with the chosen name can't be cast. -/
  | chosenNameSpellsCantBeCast
deriving DecidableEq, Repr, Inhabited, BEq

namespace FraStatic

/-- The printed line. -/
def text : FraStatic → String
  | .attackDespiteDefenderIfScried =>
    "As long as you've scried or surveilled this turn, this creature can attack as though it didn't have defender."
  | .powerPerSevenInGraveyard =>
    "This creature gets +2/+0 for every seven cards in your graveyard."
  | .creaturesYouControlHaveTrample => "Creatures you control have trample."
  | .firstStrikeDuringYourTurn => "During your turn, this creature has first strike."
  | .equippedHuntersAxe =>
    "Equipped creature gets +2/+0 and has \"Whenever this creature attacks, it gains your choice of trample or deathtouch until end of turn.\""
  | .enchantArtifactOrNonAuraEnchantment => "Enchant artifact or non-Aura enchantment"
  | .enchantedIsConstruct55 =>
    "Enchanted permanent is a Construct creature with base power and toughness 5/5 in addition to its other types."
  | .enchantedGetsOneAndDeathtouch => "Enchanted creature gets +1/+0 and has deathtouch."
  | .vigilanceIfJace => "This creature has vigilance as long as you control a Jace planeswalker."
  | .powerAndFlyingIfSevenInGraveyard =>
    "This creature gets +1/+0 and has flying as long as there are seven or more cards in your graveyard."
  | .plusOneCreaturesHaveVigilance =>
    "Each creature you control with a +1/+1 counter on it has vigilance."
  | .flyingHasteIfOpponentDealtNoncombat =>
    "As long as an opponent was dealt noncombat damage this turn, this creature has flying and haste."
  | .equippedMedicsKitesail =>
    "Equipped creature gets +1/+0 and has flying and \"Whenever this creature attacks, you gain 1 life.\""
  | .entersTappedChooseColor => "This land enters tapped. As it enters, choose a color."
  | .tapAddChosenColor => "{T}: Add one mana of the chosen color."
  | .creaturesAttackDespiteDefender =>
    "Creatures you control can attack as though they didn't have defender."
  | .creatureTokensGetOneAndVigilance => "Creature tokens you control get +1/+0 and have vigilance."
  | .tapAddColorlessNotFromHand =>
    "{T}: Add {C}. This mana can't be spent to cast spells from your hand."
  | .tapAddAnyColorPlaneswalkerOnly =>
    "{T}: Add one mana of any color. Spend this mana only to cast a planeswalker spell."
  | .opponentsNoncreatureSpellsCostMore =>
    "Noncreature spells your opponents cast cost {1} more to cast."
  | .planeswalkersAttackedByOneAtMost =>
    "Planeswalkers you control have \"No more than one creature can attack this planeswalker each combat.\""
  | .extraPlusOneCounter =>
    "If one or more +1/+1 counters would be put on a creature you control, that many plus one +1/+1 counters are put on it instead."
  | .noSpellsOrAbilitiesDuringCombat =>
    "During combat, players can't cast spells or activate abilities that aren't mana abilities."
  | .noncreatureSpellsCostLess => "Noncreature spells you cast cost {1} less to cast."
  | .costsLessIfCastNoncreature =>
    "This spell costs {2} less to cast if you've cast a noncreature spell this turn."
  | .exileOpponentsDyingCreatures => "If a creature an opponent controls would die, exile it instead."
  | .wardDiscardCard => "Ward—Discard a card."
  | .wardSacrificeThreePermanents => "Ward—Sacrifice three permanents."
  | .powerPerCreatureAndPlaneswalkerCard =>
    "This creature gets +1/+0 for each creature and planeswalker card in your graveyard."
  | .otherPlusOneCreaturesHaveHaste =>
    "Each other creature you control with a +1/+1 counter on it has haste."
  | .creaturesYouControlHaveHaste => "Creatures you control have haste."
  | .noncombatDamagePlusOne =>
    "If a source you control would deal noncombat damage to an opponent or a permanent an opponent controls, it deals that much damage plus 1 instead."
  | .powerEqualsBasicLandTypes =>
    "This creature's power is equal to the number of basic land types among lands you control."
  | .otherCreaturesHaveTrample => "Other creatures you control have trample."
  | .landsHaveHexproof => "Lands you control have hexproof."
  | .hexproofUntilCombatDamage =>
    "This creature has hexproof as long as they haven't dealt combat damage yet."
  | .thoptersHaveHaste => "Thopters you control have haste."
  | .artifactCreaturesHaveVigilance => "Artifact creatures you control have vigilance."
  | .doesntUntap => "This creature doesn't untap during your untap step."
  | .emblemCreaturesGetTwoTwo => "Creatures you control get +2/+2."
  | .tapSacrificeAddThreeOfOneColor => "{T}, Sacrifice this token: Add three mana of any one color."
  | .entersChooseNonlandCardName => "As this creature enters, choose a nonland card name."
  | .chosenNameSpellsCantBeCast => "Spells with the chosen name can't be cast."

/-- Every FRA static ability the parser recognizes. The emblem's static is
created by Ajani's ultimate and never printed on a card. -/
def all : Array FraStatic := #[
  .attackDespiteDefenderIfScried, .powerPerSevenInGraveyard, .creaturesYouControlHaveTrample,
  .firstStrikeDuringYourTurn, .equippedHuntersAxe, .enchantArtifactOrNonAuraEnchantment,
  .enchantedIsConstruct55, .enchantedGetsOneAndDeathtouch, .vigilanceIfJace,
  .powerAndFlyingIfSevenInGraveyard, .plusOneCreaturesHaveVigilance,
  .flyingHasteIfOpponentDealtNoncombat, .equippedMedicsKitesail, .entersTappedChooseColor,
  .tapAddChosenColor, .creaturesAttackDespiteDefender, .creatureTokensGetOneAndVigilance,
  .tapAddColorlessNotFromHand, .tapAddAnyColorPlaneswalkerOnly,
  .opponentsNoncreatureSpellsCostMore, .planeswalkersAttackedByOneAtMost, .extraPlusOneCounter,
  .noSpellsOrAbilitiesDuringCombat, .noncreatureSpellsCostLess, .costsLessIfCastNoncreature,
  .exileOpponentsDyingCreatures, .wardDiscardCard, .wardSacrificeThreePermanents,
  .powerPerCreatureAndPlaneswalkerCard, .otherPlusOneCreaturesHaveHaste,
  .creaturesYouControlHaveHaste, .noncombatDamagePlusOne, .powerEqualsBasicLandTypes,
  .otherCreaturesHaveTrample, .landsHaveHexproof, .hexproofUntilCombatDamage,
  .thoptersHaveHaste, .artifactCreaturesHaveVigilance, .doesntUntap,
  .entersChooseNonlandCardName, .chosenNameSpellsCantBeCast]

/-- The restricted mana this ability adds, if it is a mana ability. -/
def manaUse? : FraStatic → Option FraManaUse
  | .tapAddColorlessNotFromHand => some .notSpellsFromHand
  | .tapAddAnyColorPlaneswalkerOnly => some .planeswalkerSpell
  | _ => none

end FraStatic

end Mtg.Engine
