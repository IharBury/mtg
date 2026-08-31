/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
Authors: MTG Engine Contributors
-/

import Mtg.Engine.Color
import Mtg.Engine.Mana

/-!
# Leftover modeled ability constructors

Reusable ability shapes live on `TriggeredAbility`, `StaticAbility`,
`SpellEffect`, `AbilityEffect`, and `CardDef` so any set can use them.
Reusable leftover *trigger* wordings now live on event-family effect
inductives (`StepEffect`, `DeathEffect`, `ThisAttackEffect`,
`EnterOrAttackEffect`, `WatchEffect`, `YouAttackEffect`, `CastEffect`,
`ResourceEffect`) with one `TriggeredAbility` constructor each.
Reusable leftover *statics* now live on `StaticAbility`. Reusable leftover
*spells* now live on `SpellEffect`. Leftover activations remain here on
`ModeledAbility`.
-/

namespace Mtg.Engine
/-- How leftover “add one mana of any color; spend only …” restricts the mana. -/
inductive RestrictedManaSpend where
  /-- Hero spells and Hero sources. -/
  | hero
  /-- Villain spells and Villain sources. -/
  | villain
  /-- Artifact spells. -/
  | artifactSpell
deriving Repr, Inhabited, BEq

namespace RestrictedManaSpend

/-- Official Oracle “Spend this mana only …” clause. -/
def spendClause : RestrictedManaSpend → String
  | .hero => "to cast a Hero spell or to activate an ability of a Hero source"
  | .villain => "to cast a Villain spell or to activate an ability of a Villain source"
  | .artifactSpell => "to cast an artifact spell"

end RestrictedManaSpend

/-- A leftover modeled activation that is not yet a shared shape. -/
inductive ModeledAbility where
  /-- Modeled MSH ability. -/
  | mentalOrganismPay3LifeMODOK
  /-- Modeled MSH ability. -/
  | tyrannosaurusRex6UntilEndOfTu
  /-- Modeled MSH ability. -/
  | addXManaOfAnyOneColorWhereXIsDocSams
  /-- Modeled MSH ability. -/
  | addFourManaInAnyCombinationOfColors
  /-- Add one mana of any color, spendable only as `kind` describes. -/
  | addOneManaOfAnyColorSpendOnly (kind : RestrictedManaSpend)
  /-- Modeled MSH ability. -/
  | addTwoManaOfAnyOneColorSpendThisManaO
  /-- `{T}: Add {A} or {B}`, optionally only if this land entered this turn
  or you control a basic land. -/
  | addOneOf (a b : Color) (enteredOrBasic : Bool := false)
  /-- Modeled MSH ability. -/
  | addCCC
  /-- Modeled MSH ability. -/
  | addUThisManaCanTBeSpentToCastANona
  /-- Modeled MSH ability. -/
  | addW
  /-- Modeled MSH ability. -/
  | n1BDiscardThisCard
  /-- Modeled MSH ability. -/
  | n2TDiscardACard
  /-- Modeled MSH ability. -/
  | n2BSacrificeAnArtifactOrCreatur
  /-- Modeled MSH ability. -/
  | n2GTRemoveAnyNumberOf11
  /-- Modeled MSH ability. -/
  | n2RDiscardThisCard
  /-- Modeled MSH ability. -/
  | n3TSacrificeAnArtifactOrDisca
  /-- Modeled MSH ability. -/
  | n3TSacrificeAnArtifact
  /-- Modeled MSH ability. -/
  | n3USacrificeThisArtifact
  /-- Modeled MSH ability. -/
  | tPutAStunCounterOnJessicaJones
  /-- Modeled MSH ability. -/
  | tSacrificeAnEquipmentAttachedTo
  /-- Pay 2 life: add two mana, spendable only on Equipment. -/
  | pay2LifeAddTwoManaOfAnyOneColorSpend
  /-- Pay 2 life: copy an artifact-source ability you control. -/
  | pay2LifeCopyTargetActivatedOrTriggeredA
  /-- Sacrifice this: destroy a noncreature artifact or enchantment. -/
  | sacrificeThisCreatureDestroyTargetNoncreat
  /-- Modeled MSH ability. -/
  | harnessTheMindStone
  /-- Modeled MSH ability. -/
  | targetPlayerDrawsFourCards
  /-- Modeled MSH ability. -/
  | anotherTargetCreatureYouControlGets20A
  /-- Modeled MSH ability. -/
  | copyTargetActivatedOrTriggeredAbilityYouC
  /-- Modeled MSH ability. -/
  | createX11GreenSquirrelCreatureTokensWhe
  /-- Modeled MSH ability. -/
  | createATapped21BlackVillainCreatureToken
  /-- Modeled MSH ability. -/
  | destroyUpToOneTargetArtifactOrEnchantment
  /-- Modeled MSH ability. -/
  | drawACardActivateOnlyIfYouControlACrea
  /-- Modeled MSH ability. -/
  | forEachKindOfCounterOnTargetPermanentOr
  /-- Modeled MSH ability. -/
  | ifThisEquipmentIsnTACreatureItBecomesA
  /-- Modeled MSH ability. -/
  | lookAtTheTopThreeCardsOfYourLibraryYou
  /-- Modeled MSH ability. -/
  | millFourCardsYouMayPutAHeroOrEnchantme
  /-- Modeled MSH ability. -/
  | putA11CounterAndADoubleStrikeCounter
  /-- Modeled MSH ability. -/
  | putA11CounterOnAbominationHeFightsUp
  /-- Modeled MSH ability. -/
  | putA11CounterOnHerculesHeGainsVigila
  /-- Modeled MSH ability. -/
  | putA11CounterOnWhiteTigerAndCreateTh
  /-- Modeled MSH ability. -/
  | putA11CounterOnThisCreatureAndCreate
  /-- Modeled MSH ability. -/
  | putTwo11CountersOnThanosChooseOddOr
  /-- Modeled MSH ability. -/
  | putTwo11CountersOnThisCreatureAndCrea
  /-- Modeled MSH ability. -/
  | returnThisCardFromYourGraveyardToTheBatt
  /-- Modeled MSH ability. -/
  | returnUpToOneTargetCreatureCardFromYour
  /-- Modeled MSH ability. -/
  | revealTheTopCardOfYourLibraryIfItSAn
  /-- Modeled MSH ability. -/
  | tapTargetCreatureThisAbilityCosts1Less
  /-- Modeled MSH ability. -/
  | targetVillainYouControlConnives
  /-- Modeled MSH ability. -/
  | targetArtifactYouControlBecomesACopyOfA
  /-- Modeled MSH ability. -/
  | targetCreatureYouControlThatSAttackingAlo
  /-- Modeled MSH ability. -/
  | untilEndOfTurnReptilBecomesADinosaurHer
  /-- Modeled MSH ability. -/
  | whenYouNextCastAnInstantOrSorcerySpellW
deriving Repr, Inhabited, BEq

namespace ModeledAbility

/-- Official Oracle wording for this ModeledAbility. -/
def toNotation : ModeledAbility → String
  | .mentalOrganismPay3LifeMODOK => "Mental Organism — Pay 3 life: M.O.D.O.K. connives. Activate only during your turn."
  | .tyrannosaurusRex6UntilEndOfTu => "Tyrannosaurus Rex — {6}: Until end of turn, Reptil becomes a Dinosaur Hero with base power and toughness 6/6 and gains trample."
  | .addXManaOfAnyOneColorWhereXIsDocSams => "Add X mana of any one color, where X is Doc Samson's power"
  | .addFourManaInAnyCombinationOfColors => "Add four mana in any combination of colors"
  | .addOneManaOfAnyColorSpendOnly kind =>
    s!"Add one mana of any color. Spend this mana only {kind.spendClause}"
  | .addTwoManaOfAnyOneColorSpendThisManaO => "Add two mana of any one color. Spend this mana only to activate abilities of creature sources"
  | .addOneOf a b enteredOrBasic =>
    let base := s!"Add \{{a.letter}} or \{{b.letter}}"
    if enteredOrBasic then
      s!"{base}. Activate only if this land entered this turn or if you control a basic land"
    else base
  | .addCCC => "Add {C}{C}{C}"
  | .addUThisManaCanTBeSpentToCastANona => "Add {U}. This mana can't be spent to cast a nonartifact spell"
  | .addW => "Add {W}"
  | .n1BDiscardThisCard => "{1}{B}, Discard this card: Search your library for a Plan card, reveal it, put it into your hand, then shuffle."
  | .n2TDiscardACard => "{2}, {T}, Discard a card: Draw a card for each card you've discarded this turn."
  | .n2BSacrificeAnArtifactOrCreatur => "{2}{B}, Sacrifice an artifact or creature: Draw a card."
  | .n2GTRemoveAnyNumberOf11 => "{2}{G}, {T}, Remove any number of +1/+1 counters from The Astonishing Ant-Man: Create that many 1/1 green Insect creature tokens."
  | .n2RDiscardThisCard => "{2}{R}, Discard this card: It deals 2 damage to each creature."
  | .n3TSacrificeAnArtifactOrDisca => "{3}, {T}, Sacrifice an artifact or discard a nonland card: Bullseye deals 2 damage to any target."
  | .n3TSacrificeAnArtifact => "{3}, {T}, Sacrifice an artifact: Create a 3/3 colorless Robot Villain artifact creature token named Doombot. Activate only as a sorcery."
  | .n3USacrificeThisArtifact => "{3}{U}, Sacrifice this artifact: Draw two cards."
  | .tPutAStunCounterOnJessicaJones => "{T}, Put a stun counter on Jessica Jones: Exile the top X cards of your library, where X is Jessica Jones's power. You may play those cards this turn."
  | .tSacrificeAnEquipmentAttachedTo => "{T}, Sacrifice an Equipment attached to Ronin: Target creature gets -4/-4 until end of turn. Activate only as a sorcery."
  | .pay2LifeAddTwoManaOfAnyOneColorSpend =>
      "Pay 2 life: Add two mana of any one color. Spend this mana only to cast Equipment spells or activate equip abilities. Activate only once each turn."
  | .pay2LifeCopyTargetActivatedOrTriggeredA =>
      "Pay 2 life: Copy target activated or triggered ability you control from an artifact source. You may choose new targets for the copy. Activate only during your turn and only once each turn."
  | .sacrificeThisCreatureDestroyTargetNoncreat =>
      "Sacrifice this creature: Destroy target noncreature artifact or noncreature enchantment. Activate only as a sorcery."
  | .harnessTheMindStone => "Harness The Mind Stone"
  | .targetPlayerDrawsFourCards => "Target player draws four cards"
  | .anotherTargetCreatureYouControlGets20A => "Another target creature you control gets +2/+0 and gains hexproof until end of turn"
  | .copyTargetActivatedOrTriggeredAbilityYouC => "Copy target activated or triggered ability you control from a creature source. You may choose new targets for the copy"
  | .createX11GreenSquirrelCreatureTokensWhe => "Create X 1/1 green Squirrel creature tokens, where X is the number of Squirrels you control"
  | .createATapped21BlackVillainCreatureToken => "Create a tapped 2/1 black Villain creature token with menace. Activate only if there are two or more creature cards in your graveyard"
  | .destroyUpToOneTargetArtifactOrEnchantment => "Destroy up to one target artifact or enchantment. Put a +1/+1 counter on She-Hulk"
  | .drawACardActivateOnlyIfYouControlACrea => "Draw a card. Activate only if you control a creature with toughness 4 or greater"
  | .forEachKindOfCounterOnTargetPermanentOr => "For each kind of counter on target permanent or player, give that permanent or player another counter of that kind"
  | .ifThisEquipmentIsnTACreatureItBecomesA => "If this Equipment isn't a creature, it becomes a 0/0 Construct Hero artifact creature with flying and \"This creature gets +1/+1 for each artifact you control\" until end of turn"
  | .lookAtTheTopThreeCardsOfYourLibraryYou => "Look at the top three cards of your library. You may reveal a Hero card from among them and put it into your hand. Put the rest on the bottom of your library in any order"
  | .millFourCardsYouMayPutAHeroOrEnchantme => "Mill four cards. You may put a Hero or enchantment card from among those cards into your hand"
  | .putA11CounterAndADoubleStrikeCounter => "Put a +1/+1 counter and a double strike counter on Quicksilver"
  | .putA11CounterOnAbominationHeFightsUp => "Put a +1/+1 counter on Abomination. He fights up to one target creature an opponent controls"
  | .putA11CounterOnHerculesHeGainsVigila => "Put a +1/+1 counter on Hercules. He gains vigilance, indestructible, and haste until end of turn"
  | .putA11CounterOnWhiteTigerAndCreateTh => "Put a +1/+1 counter on White Tiger and create The Tiger God, a legendary 4/4 green Cat God creature token with \"The Tiger God can't be blocked by more than one creature.\""
  | .putA11CounterOnThisCreatureAndCreate => "Put a +1/+1 counter on this creature and create a 3/2 white Hero creature token with vigilance"
  | .putTwo11CountersOnThanosChooseOddOr => "Put two +1/+1 counters on Thanos. Choose odd or even. Destroy each other creature with mana value of the chosen quality"
  | .putTwo11CountersOnThisCreatureAndCrea => "Put two +1/+1 counters on this creature and create a 2/2 colorless Robot Villain artifact creature token"
  | .returnThisCardFromYourGraveyardToTheBatt => "Return this card from your graveyard to the battlefield with a finality counter on him. Then you may attach an Equipment you control to him"
  | .returnUpToOneTargetCreatureCardFromYour => "Return up to one target creature card from your graveyard to your hand. Put two +1/+1 counters on this creature"
  | .revealTheTopCardOfYourLibraryIfItSAn => "Reveal the top card of your library. If it's an artifact card, draw a card"
  | .tapTargetCreatureThisAbilityCosts1Less => "Tap target creature. This ability costs {1} less to activate if it targets a creature with power 3 or less"
  | .targetVillainYouControlConnives => "Target Villain you control connives"
  | .targetArtifactYouControlBecomesACopyOfA => "Target artifact you control becomes a copy of a second target artifact you control until end of turn, except it isn't legendary"
  | .targetCreatureYouControlThatSAttackingAlo => "Target creature you control that's attacking alone gets +1/+0 until end of turn. You gain 1 life"
  | .untilEndOfTurnReptilBecomesADinosaurHer => "Until end of turn, Reptil becomes a Dinosaur Hero with base power and toughness 3/5 and gains reach and vigilance"
  | .whenYouNextCastAnInstantOrSorcerySpellW => "When you next cast an instant or sorcery spell with mana value less than or equal to Loki's power this turn, copy that spell. You may choose new targets for the copy"

instance : ToString ModeledAbility where
  toString := toNotation

/-- `{T}: Add` types this modeled MSH ability produces for the demo `tap`
command and other mana-ability payment (CR 605.3a). -/
def addManaTypes : ModeledAbility → Array ManaType
  | .addW => #[.colored .white]
  | .addOneOf a b _ => #[.colored a, .colored b]
  | .addCCC => #[.colorless, .colorless, .colorless]
  | .addUThisManaCanTBeSpentToCastANona => #[.colored .blue]
  | _ => #[]

/-- True when the add ability may be activated only if this land entered this
turn or if you control a basic land. -/
def requiresEnteredOrBasic : ModeledAbility → Bool
  | .addOneOf _ _ true => true
  | _ => false

#guard addManaTypes (.addOneOf .blue .black true) ==
  #[.colored .blue, .colored .black]
#guard addManaTypes (.addOneOf .blue .black) == #[.colored .blue, .colored .black]
#guard requiresEnteredOrBasic (.addOneOf .blue .black true)
#guard !(requiresEnteredOrBasic (.addOneOf .blue .black))
#guard toNotation (.addOneOf .blue .black) == "Add {U} or {B}"
#guard toNotation (.addOneOf .blue .black true) ==
  "Add {U} or {B}. Activate only if this land entered this turn or if you control a basic land"
#guard toNotation (.addOneManaOfAnyColorSpendOnly .hero) ==
  "Add one mana of any color. Spend this mana only to cast a Hero spell or to activate an ability of a Hero source"
#guard toNotation (.addOneManaOfAnyColorSpendOnly .villain) ==
  "Add one mana of any color. Spend this mana only to cast a Villain spell or to activate an ability of a Villain source"
#guard toNotation (.addOneManaOfAnyColorSpendOnly .artifactSpell) ==
  "Add one mana of any color. Spend this mana only to cast an artifact spell"

end ModeledAbility
/-- A leftover modeled Saga chapter that is not yet a shared shape. -/
inductive ModeledChapter where
  /-- Modeled MSH ability. -/
  | gainControlOfUpToTwoTargetCreaturesWith
  /-- Modeled MSH ability. -/
  | harnessTheMindStone
  /-- Modeled MSH ability. -/
  | thisSagaDeals2DamageToEachNonVillainCre
  /-- Modeled MSH ability. -/
  | thisSagaDealsXDamageToTargetOpponentWhe
deriving Repr, Inhabited, BEq

namespace ModeledChapter

/-- Official Oracle wording for this ModeledChapter. -/
def toNotation : ModeledChapter → String
  | .gainControlOfUpToTwoTargetCreaturesWith => "Gain control of up to two target creatures with total mana value 6 or less for as long as this Saga remains on the battlefield"
  | .harnessTheMindStone => "Harness The Mind Stone"
  | .thisSagaDeals2DamageToEachNonVillainCre => "This Saga deals 2 damage to each non-Villain creature and each opponent"
  | .thisSagaDealsXDamageToTargetOpponentWhe => "This Saga deals X damage to target opponent, where X is the greatest mana value among artifacts you control"

instance : ToString ModeledChapter where
  toString := toNotation

end ModeledChapter
end Mtg.Engine
