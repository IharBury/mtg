import Mtg.Engine.Card
import Mtg.Engine.Catalog

/-!
# The Hobbit Eternal catalog

Oracle characteristics for cards from Magic: The Gathering | The Hobbit
Eternal (HOC). Oracle text is stored verbatim from Scryfall.
`hobbitEternalCards` lists every unique card in the set, including
reprints that also appear in other sets.

Mentor of the Meek, Minas Tirith Garrison, Olog-hai Crusher, Haunt of the
Dead Marshes, Errand-Rider of Gondor, Mirkwood Elk, Orcish Siegemaster,
Ori, Plate Stacker, Dáin of the Ancient Halls, Dwarven Warriors, Fíli and
Kíli, Joyous, Bolg, Erebor's Reckoning, Elvish Archdruid, Thranduil the
Strategist, Bag End Banquet, Relic of Sauron, Flowering of the White Tree,
Mount Doom, Rivendell, Dragon's Desire, Last March of the Ents, and Raise
the Palisade are written as a `TraditionalCardDefinition`: their printed
characteristics are parts, and `parseOracleParts` reads the Oracle text
into the rest.
-/

namespace Mtg.Engine.Catalog

open Mtg.Engine

/-- Oracle text for Mentor of the Meek. -/
def mentorOfTheMeekOracle : String :=
  "Whenever another creature you control with power 2 or less enters, you may pay {1}. If you do, draw a card."

def mentorOfTheMeekDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Mentor of the Meek",
    .manaCost [.generic 2, .mono .white],
    .type .creature,
    .subtype .human,
    .subtype .soldier,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Mentor of the Meek") mentorOfTheMeekOracle).get!

#guard mentorOfTheMeekDefinition == .card [
  .name "Mentor of the Meek",
  .manaCost [.generic 2, .mono .white],
  .type .creature,
  .subtype .human,
  .subtype .soldier,
  .power 2,
  .toughness 2,
  .ability
    (.triggered
      (.enter
        (.intersection
          [
            .not .this,
            .permanent,
            .cardType .creature,
            .controlled (.controller .this),
            .powerAtMost (.int 2)]))
      (.optionalPayFor (.controller .this) [.mana [.generic 1]] [.draw (.controller .this) (.nat 1)]))]

def mentorOfTheMeek : CardDef :=
  mentorOfTheMeekDefinition.toCardDef (oracleText := mentorOfTheMeekOracle)

#guard mentorOfTheMeek.oracleText == mentorOfTheMeekOracle
#guard mentorOfTheMeek.triggeredAbilities == #[.onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw 2 1]

def fiendHunter : CardDef :=
  creature "Fiend Hunter" (ManaCost.ofGenericAndColors 1 [.white, .white]) #["Human", "Cleric"] 1 3
    (oracleText := "When this creature enters, you may exile another target creature.\nWhen this creature leaves the battlefield, return the exiled card to the battlefield under its owner's control.")
    (triggeredAbilities := #[.onEnterMayExileAnotherCreature, .onLeaveReturnExiled])

/-- Oracle text for Errand-Rider of Gondor. -/
def errandRiderOfGondorOracle : String :=
  "When this creature enters, draw a card. Then if you don't control a legendary creature, put a card from your hand on the bottom of your library."

def errandRiderOfGondorDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Errand-Rider of Gondor",
    .manaCost [.generic 2, .mono .white],
    .type .creature,
    .subtype .human,
    .subtype .soldier,
    .power 3,
    .toughness 2
  ] ++ (parseOracleParts (name := "Errand-Rider of Gondor") errandRiderOfGondorOracle).get!

#guard errandRiderOfGondorDefinition == .card [
  .name "Errand-Rider of Gondor",
  .manaCost [.generic 2, .mono .white],
  .type .creature,
  .subtype .human,
  .subtype .soldier,
  .power 3,
  .toughness 2,
  .ability
    (.triggered
      (.enter .this)
      (.sequence
        [
          .draw (.controller .this) (.nat 1),
          .if
            (.not
              (.any
                (.intersection
                  [
                    .permanent,
                    .cardType .creature,
                    .supertype .legendary,
                    .controlled (.controller .this)])))
            [
              .putOnBottomOfLibrary
                (.selected
                  (.controller .this)
                  (.range (.nat 1) (.nat 1))
                  (.intersection [.inHand, .owner (.controller .this)]))]]))]

def errandRiderOfGondor : CardDef :=
  errandRiderOfGondorDefinition.toCardDef (oracleText := errandRiderOfGondorOracle)

#guard errandRiderOfGondor.oracleText == errandRiderOfGondorOracle
#guard errandRiderOfGondor.triggeredAbilities == #[.onEnterDrawThenBottomIfNoLegendary]

/-- Oracle text for Landroval, Horizon Witness. -/
def landrovalHorizonWitnessOracle : String :=
  "Flying\nWhenever two or more creatures you control attack a player, target attacking creature without flying gains flying until end of turn."

def landrovalHorizonWitnessDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Landroval, Horizon Witness",
    .manaCost [.generic 4, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .bird,
    .subtype .noble,
    .power 3,
    .toughness 4
  ] ++ (parseOracleParts (name := "Landroval, Horizon Witness") landrovalHorizonWitnessOracle).get!

#guard landrovalHorizonWitnessDefinition == .card [
  .name "Landroval, Horizon Witness",
  .manaCost [.generic 4, .mono .white],
  .type .creature,
  .supertype .legendary,
  .subtype .bird,
  .subtype .noble,
  .power 3,
  .toughness 4,
  .ability (.keyword .flying),
  .ability
    (.triggered
      (.attackSimultaneously
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)])
        .player
        [.countAtLeast 2])
      (.continuous
        [
          .gainAbility
            (.target
              1
              (.intersection [
                .permanent,
                .cardType .creature,
                .attacking .all,
                .not (.keyword .flying)]))
            (.keyword .flying)]
        .endOfTurn))]

def landrovalHorizonWitness : CardDef :=
  landrovalHorizonWitnessDefinition.toCardDef (oracleText := landrovalHorizonWitnessOracle)

/-- Oracle text for Rogue's Passage. -/
def roguesPassageOracle : String :=
  "{T}: Add {C}.\n{4}, {T}: Target creature can't be blocked this turn."

def roguesPassageDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Rogue's Passage",
    .type .land
  ] ++ (parseOracleParts (name := "Rogue's Passage") roguesPassageOracle).get!

#guard roguesPassageDefinition == .card [
  .name "Rogue's Passage",
  .type .land,
  .ability
    (.activated [.tapSymbol] (.addMana (.controller .this) [.colorless])),
  .ability
    (.activated
      [.mana [.generic 4], .tapSymbol]
      (.continuous
        [.forbid
          (.block
            .any
            (.target 1 (.intersection [.permanent, .cardType .creature])))]
        .endOfTurn))]

def roguesPassage : CardDef :=
  roguesPassageDefinition.toCardDef (oracleText := roguesPassageOracle)

/-- Oracle text for Soldier of the Grey Host. -/
def soldierOfTheGreyHostOracle : String :=
  "Flash\nFlying\nWhen this creature enters, target creature gets +2/+0 until end of turn."

def soldierOfTheGreyHostDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Soldier of the Grey Host",
    .manaCost [.generic 3, .mono .white],
    .type .creature,
    .subtype .spirit,
    .subtype .soldier,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Soldier of the Grey Host") soldierOfTheGreyHostOracle).get!

#guard soldierOfTheGreyHostDefinition == .card [
  .name "Soldier of the Grey Host",
  .manaCost [.generic 3, .mono .white],
  .type .creature,
  .subtype .spirit,
  .subtype .soldier,
  .power 2,
  .toughness 2,
  .ability (.keyword .flash),
  .ability (.keyword .flying),
  .ability (
    .triggered
      (.enter .this)
      (.continuous
        [.addPower
          (.target 1 (.intersection [.permanent, .cardType .creature])) (Value.int 2)]
        .endOfTurn))]

def soldierOfTheGreyHost : CardDef :=
  soldierOfTheGreyHostDefinition.toCardDef (oracleText := soldierOfTheGreyHostOracle)

/-- Oracle text for Eagles of the North. -/
def eaglesOfTheNorthOracle : String :=
  "Flying\nWhen this creature enters, creatures you control get +1/+0 and gain first strike until end of turn.\nPlainscycling {1} ({1}, Discard this card: Search your library for a Plains card, reveal it, put it into your hand, then shuffle.)"

def eaglesOfTheNorthDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Eagles of the North",
    .manaCost [.generic 5, .mono .white],
    .type .creature,
    .subtype .bird,
    .subtype .soldier,
    .power 3,
    .toughness 3
  ] ++ (parseOracleParts (name := "Eagles of the North") eaglesOfTheNorthOracle).get!

#guard eaglesOfTheNorthDefinition == .card [
  .name "Eagles of the North",
  .manaCost [.generic 5, .mono .white],
  .type .creature,
  .subtype .bird,
  .subtype .soldier,
  .power 3,
  .toughness 3,
  .ability (.keyword .flying),
  .ability (
    .triggered
      (.enter .this)
      (.continuous
        [
          .addPower
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)]) (Value.int 1),
          .gainAbility
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)])
            (.keyword .firstStrike)]
        .endOfTurn)),
  .ability (.keywordWithCost (.typecycling [] [] [.plains]) [.mana [.generic 1]])]

def eaglesOfTheNorth : CardDef :=
  eaglesOfTheNorthDefinition.toCardDef (oracleText := eaglesOfTheNorthOracle)

/-- Oracle text for Dúnedain Blade. -/
def dunedainBladeOracle : String :=
  "Equipped creature gets +2/+1.\nEquip Human {1}\nEquip {3} ({3}: Attach to target creature you control. Equip only as a sorcery.)"

def dunedainBladeDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Dúnedain Blade",
    .manaCost [.generic 1, .mono .white],
    .type .artifact,
    .subtype .equipment
  ] ++ (parseOracleParts (name := "Dúnedain Blade") dunedainBladeOracle).get!

#guard dunedainBladeDefinition == .card [
  .name "Dúnedain Blade",
  .manaCost [.generic 1, .mono .white],
  .type .artifact,
  .subtype .equipment,
  .ability (.static (.addPower (.hostOf .this) (Value.int 2))),
  .ability (.static (.addToughness (.hostOf .this) (Value.int 1))),
  .ability (.keywordWithSubtypeAndCost .equip .human (.mana [.generic 1])),
  .ability (.keywordWithCost .equip [.mana [.generic 3]])]

def dunedainBlade : CardDef :=
  dunedainBladeDefinition.toCardDef (oracleText := dunedainBladeOracle)

def fogOnTheBarrowDowns : CardDef :=
  aura "Fog on the Barrow-Downs" (ManaCost.ofGenericAndColor 2 .white)
    "Enchant creature\nEnchanted creature is a Spirit and can't attack or block. (It loses all other creature types.)"
    (staticAbilities := #[.enchantedIsOnlySubtypeCantAttackOrBlock "Spirit"])

def banishingLight : CardDef :=
  enchantment "Banishing Light" (ManaCost.ofGenericAndColor 2 .white)
    "When this enchantment enters, exile target nonland permanent an opponent controls until this enchantment leaves the battlefield."
    (triggeredAbilities := #[.onEnterExileOppNonlandUntilLeaves])

def dawnOfANewAge : CardDef :=
  enchantment "Dawn of a New Age" (ManaCost.ofGenericAndColor 1 .white)
    "This enchantment enters with a hope counter on it for each creature you control.\nAt the beginning of your end step, remove a hope counter from this enchantment. If you do, draw a card. Then if this enchantment has no hope counters on it, sacrifice it and you gain 4 life."
    (entersWithHopePerCreature := true)
    (triggeredAbilities := #[.onYourEndStepRemoveHopeDrawSac])

/-- Oracle text for Westfold Rider. -/
def westfoldRiderOracle : String :=
  "Sacrifice this creature: Destroy target artifact or enchantment. Activate only as a sorcery."

def westfoldRiderDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Westfold Rider",
    .manaCost [.generic 1, .mono .white],
    .type .creature,
    .subtype .human,
    .subtype .knight,
    .power 3,
    .toughness 1
  ] ++ (parseOracleParts (name := "Westfold Rider") westfoldRiderOracle).get!

#guard westfoldRiderDefinition == .card [
  .name "Westfold Rider",
  .manaCost [.generic 1, .mono .white],
  .type .creature,
  .subtype .human,
  .subtype .knight,
  .power 3,
  .toughness 1,
  .ability (
    .activatedIf
      (.timeToCastSorcery (.controller .this))
      [.sacrifice .this]
      (.destroy
        (.target
          1
          (.intersection [
            .permanent,
            .union [.cardType .artifact, .cardType .enchantment]]))))]

def westfoldRider : CardDef :=
  westfoldRiderDefinition.toCardDef (oracleText := westfoldRiderOracle)

/-- Oracle text for Esquire of the King. -/
def esquireOfTheKingOracle : String :=
  "{4}{W}, {T}: Creatures you control get +1/+1 until end of turn. This ability costs {2} less to activate if you control a legendary creature."

def esquireOfTheKingDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Esquire of the King",
    .manaCost [.mono .white],
    .type .creature,
    .subtype .human,
    .subtype .soldier,
    .power 1,
    .toughness 1
  ] ++ (parseOracleParts (name := "Esquire of the King") esquireOfTheKingOracle).get!

#guard esquireOfTheKingDefinition == .card [
  .name "Esquire of the King",
  .manaCost [.mono .white],
  .type .creature,
  .subtype .human,
  .subtype .soldier,
  .power 1,
  .toughness 1,
  .ability (
    .activated
      [.mana [.generic 4, .mono .white], .tapSymbol]
      (.continuous
        [
          .addPower
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)]) (Value.int 1),
          .addToughness
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)]) (Value.int 1)]
        .endOfTurn)),
  .ability (
    .static
      (.if
        (.any
          (.intersection [
            .permanent,
            .cardType .creature,
            .supertype .legendary,
            .controlled (.controller .this)]))
        [.reduceCost .this [.mana [.generic 2]]]))]

def esquireOfTheKing : CardDef :=
  esquireOfTheKingDefinition.toCardDef (oracleText := esquireOfTheKingOracle)

/-- Oracle text for Pelargir Survivor. -/
def pelargirSurvivorOracle : String :=
  "{T}: Add one mana of any color. Spend this mana only to cast an instant or sorcery spell.\n{5}{U}, {T}: Target player mills three cards. (They put the top three cards of their library into their graveyard.)"

def pelargirSurvivorDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Pelargir Survivor",
    .manaCost [.generic 1, .mono .blue],
    .type .creature,
    .subtype .human,
    .subtype .peasant,
    .power 1,
    .toughness 3
  ] ++ (parseOracleParts (name := "Pelargir Survivor") pelargirSurvivorOracle).get!

#guard pelargirSurvivorDefinition == .card [
  .name "Pelargir Survivor",
  .manaCost [.generic 1, .mono .blue],
  .type .creature,
  .subtype .human,
  .subtype .peasant,
  .power 1,
  .toughness 3,
  .ability
    (.activated
      [.tapSymbol]
      (.sequence [
        .actionId 1
          (.addManaOfOneColor (.controller .this) ManaSymbol.anyColor 1),
        .continuous
          [.forbid
            (.spendManaCreatedByAction 1
              (.not
                (.castSpell
                  (.union [.cardType .instant, .cardType .sorcery]))))]
          .endOfTurn])),
  .ability
    (.activated
      [.mana [.generic 5, .mono .blue], .tapSymbol]
      (.mill (.target 1 .player) 3))]

def pelargirSurvivor : CardDef :=
  pelargirSurvivorDefinition.toCardDef (oracleText := pelargirSurvivorOracle)

/-- Oracle text for Lórien Revealed. -/
def lorienRevealedOracle : String :=
  "Draw three cards.\nIslandcycling {1} ({1}, Discard this card: Search your library for an Island card, reveal it, put it into your hand, then shuffle.)"

def lorienRevealedDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Lórien Revealed",
    .manaCost [.generic 3, .mono .blue, .mono .blue],
    .type .sorcery
  ] ++ (parseOracleParts (name := "Lórien Revealed") lorienRevealedOracle).get!

#guard lorienRevealedDefinition == .card [
  .name "Lórien Revealed",
  .manaCost [.generic 3, .mono .blue, .mono .blue],
  .type .sorcery,
  .actions [.draw (.controller .this) 3],
  .ability (.keywordWithCost (.typecycling [] [] [.island]) [.mana [.generic 1]])]

def lorienRevealed : CardDef :=
  lorienRevealedDefinition.toCardDef (oracleText := lorienRevealedOracle)

/-- Oracle text for Knights of Dol Amroth. -/
def knightsOfDolAmrothOracle : String :=
  "Whenever you draw your second card each turn, put a +1/+1 counter on this creature."

def knightsOfDolAmrothDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Knights of Dol Amroth",
    .manaCost [.generic 3, .mono .blue],
    .type .creature,
    .subtype .human,
    .subtype .knight,
    .power 3,
    .toughness 3
  ] ++ (parseOracleParts (name := "Knights of Dol Amroth") knightsOfDolAmrothOracle).get!

#guard knightsOfDolAmrothDefinition == .card [
  .name "Knights of Dol Amroth",
  .manaCost [.generic 3, .mono .blue],
  .type .creature,
  .subtype .human,
  .subtype .knight,
  .power 3,
  .toughness 3,
  .ability (
    .triggered
      (.ordinal 2 .turnStart (.draw (.controller .this) .all))
      (.putCounter (.source .this) .plusOnePlusOne 1))]

def knightsOfDolAmroth : CardDef :=
  knightsOfDolAmrothDefinition.toCardDef (oracleText := knightsOfDolAmrothOracle)

/-- Oracle text for Grey Havens Navigator. -/
def greyHavensNavigatorOracle : String :=
  "Flash\nWhen this creature enters, scry 1."

def greyHavensNavigatorDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Grey Havens Navigator",
    .manaCost [.generic 2, .mono .blue],
    .type .creature,
    .subtype .elf,
    .subtype .pilot,
    .power 3,
    .toughness 2
  ] ++ (parseOracleParts (name := "Grey Havens Navigator") greyHavensNavigatorOracle).get!

#guard greyHavensNavigatorDefinition == .card [
  .name "Grey Havens Navigator",
  .manaCost [.generic 2, .mono .blue],
  .type .creature,
  .subtype .elf,
  .subtype .pilot,
  .power 3,
  .toughness 2,
  .ability (.keyword .flash),
  .ability (.triggered (.enter .this) (.scry (.controller .this) 1))]

def greyHavensNavigator : CardDef :=
  greyHavensNavigatorDefinition.toCardDef (oracleText := greyHavensNavigatorOracle)

/-- Oracle text for Ithilien Kingfisher. -/
def ithilienKingfisherOracle : String :=
  "Flying\nWhen this creature dies, draw a card."

def ithilienKingfisherDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Ithilien Kingfisher",
    .manaCost [.generic 2, .mono .blue],
    .type .creature,
    .subtype .bird,
    .power 2,
    .toughness 1
  ] ++ (parseOracleParts (name := "Ithilien Kingfisher") ithilienKingfisherOracle).get!

#guard ithilienKingfisherDefinition == .card [
  .name "Ithilien Kingfisher",
  .manaCost [.generic 2, .mono .blue],
  .type .creature,
  .subtype .bird,
  .power 2,
  .toughness 1,
  .ability (.keyword .flying),
  .ability (.triggered (.die .this) (.draw (.controller .this) 1))]

def ithilienKingfisher : CardDef :=
  ithilienKingfisherDefinition.toCardDef (oracleText := ithilienKingfisherOracle)

/-- Oracle text for Hithlain Knots. -/
def hithlainKnotsOracle : String :=
  "Tap target creature. Scry 1.\nDraw a card."

def hithlainKnotsDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Hithlain Knots",
    .manaCost [.generic 1, .mono .blue],
    .type .instant
  ] ++ (parseOracleParts (name := "Hithlain Knots") hithlainKnotsOracle).get!

#guard hithlainKnotsDefinition == .card [
  .name "Hithlain Knots",
  .manaCost [.generic 1, .mono .blue],
  .type .instant,
  .actions [
    .tap (.target 1 (.intersection [.permanent, .cardType .creature])),
    .scry (.controller .this) 1,
    .draw (.controller .this) 1]]

def hithlainKnots : CardDef :=
  hithlainKnotsDefinition.toCardDef (oracleText := hithlainKnotsOracle)

/-- Oracle text for Captain of Umbar. -/
def captainOfUmbarOracle : String :=
  "{1}, {T}: Draw a card, then discard a card."

def captainOfUmbarDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Captain of Umbar",
    .manaCost [.generic 2, .mono .blue],
    .type .creature,
    .subtype .human,
    .subtype .pirate,
    .power 2,
    .toughness 3
  ] ++ (parseOracleParts (name := "Captain of Umbar") captainOfUmbarOracle).get!

#guard captainOfUmbarDefinition == .card [
  .name "Captain of Umbar",
  .manaCost [.generic 2, .mono .blue],
  .type .creature,
  .subtype .human,
  .subtype .pirate,
  .power 2,
  .toughness 3,
  .ability (
    .activated
      [.mana [.generic 1], .tapSymbol]
      (.sequence [.draw (.controller .this) 1, .discard (.controller .this) 1]))]

def captainOfUmbar : CardDef :=
  captainOfUmbarDefinition.toCardDef (oracleText := captainOfUmbarOracle)

/-- Oracle text for Minas Tirith Garrison. -/
def minasTirithGarrisonOracle : String :=
  "Minas Tirith Garrison's power is equal to the number of cards in your hand.\nWhenever this creature attacks, you may tap any number of untapped Humans you control. Draw a card for each Human tapped this way."

def minasTirithGarrisonDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Minas Tirith Garrison",
    .manaCost [.generic 3, .mono .blue],
    .type .creature,
    .subtype .human,
    .subtype .soldier,
    .toughness 5
  ] ++ (parseOracleParts (name := "Minas Tirith Garrison") minasTirithGarrisonOracle).get!

#guard minasTirithGarrisonDefinition == .card [
  .name "Minas Tirith Garrison",
  .manaCost [.generic 3, .mono .blue],
  .type .creature,
  .subtype .human,
  .subtype .soldier,
  .toughness 5,
  .ability
    (.static (.setPower .this (.count (.intersection [.inHand, .owner (.controller .this)])))),
  .ability
    (.triggered
      (.attack .this .all)
      (.sequence
        [
          .actionId
            1
            (.tap
              (.selected
                (.controller .this)
                .any
                (.intersection
                  [.permanent, .subtype .human, .not .tapped, .controlled (.controller .this)]))),
          .draw (.controller .this) (.count (.wasObjectOfAction 1))]))]

def minasTirithGarrison : CardDef :=
  minasTirithGarrisonDefinition.toCardDef (oracleText := minasTirithGarrisonOracle)

#guard minasTirithGarrison.oracleText == minasTirithGarrisonOracle
#guard minasTirithGarrison.toughness == some 5
#guard minasTirithGarrison.staticAbilities == #[.powerEqualCardsInHand]
#guard minasTirithGarrison.triggeredAbilities == #[.onAttackTapHumansDraw]

def colossalWhale : CardDef :=
  creature "Colossal Whale" (ManaCost.ofGenericAndColors 5 [.blue, .blue]) #["Whale"] 5 5
    (oracleText := "Islandwalk (This creature can't be blocked as long as defending player controls an Island.)\nWhenever this creature attacks, you may exile target creature defending player controls until this creature leaves the battlefield. (That creature returns under its owner's control.)")
    (keywords := Keyword.islandwalk)
    (triggeredAbilities := #[.onAttackMayExileDefenderUntilLeaves])

/-- Oracle text for Willow-Wind. -/
def willowWindOracle : String :=
  "Flying\nWhen this creature enters, scry 2."

def willowWindDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Willow-Wind",
    .manaCost [.generic 4, .mono .blue],
    .type .creature,
    .subtype .elemental,
    .power 3,
    .toughness 4
  ] ++ (parseOracleParts (name := "Willow-Wind") willowWindOracle).get!

#guard willowWindDefinition == .card [
  .name "Willow-Wind",
  .manaCost [.generic 4, .mono .blue],
  .type .creature,
  .subtype .elemental,
  .power 3,
  .toughness 4,
  .ability (.keyword .flying),
  .ability (.triggered (.enter .this) (.scry (.controller .this) 2))]

def willowWind : CardDef :=
  willowWindDefinition.toCardDef (oracleText := willowWindOracle)

def nimrodelWatcher : CardDef :=
  creature "Nimrodel Watcher" (ManaCost.ofGenericAndColor 1 .blue) #["Elf", "Scout"] 2 1
    (oracleText := "Whenever you scry, this creature gets +1/+0 until end of turn and can't be blocked this turn. This ability triggers only once each turn.")
    (triggeredAbilities := #[.onScryPumpAndUnblockableOnce])

def sternScolding : CardDef :=
  instant "Stern Scolding" (ManaCost.ofColor .blue)
    "Counter target creature spell with power or toughness 2 or less."
    (some (Effect.counterCreatureSpellPTAtMost 2))

/-- Oracle text for Haunt of the Dead Marshes. -/
def hauntOfTheDeadMarshesOracle : String :=
  "When this creature enters, scry 1.\n{2}{B}: Return this card from your graveyard to the battlefield tapped. Activate only if you control a legendary creature."

def hauntOfTheDeadMarshesDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Haunt of the Dead Marshes",
    .manaCost [.mono .black],
    .type .creature,
    .subtype .nightmare,
    .subtype .elf,
    .power 1,
    .toughness 1
  ] ++ (parseOracleParts (name := "Haunt of the Dead Marshes") hauntOfTheDeadMarshesOracle).get!

#guard hauntOfTheDeadMarshesDefinition == .card [
  .name "Haunt of the Dead Marshes",
  .manaCost [.mono .black],
  .type .creature,
  .subtype .nightmare,
  .subtype .elf,
  .power 1,
  .toughness 1,
  .ability (.triggered (.enter .this) (.scry (.controller .this) (.nat 1))),
  .ability
    (.graveyardActivatedIf
      (.any
        (.intersection
          [.permanent, .cardType .creature, .supertype .legendary, .controlled (.controller .this)]))
      [.mana [.generic 2, .mono .black]]
      (.putOntoBattlefieldInState (.intersection [.inGraveyard, .source .this]) [.tapped]))]

def hauntOfTheDeadMarshes : CardDef :=
  hauntOfTheDeadMarshesDefinition.toCardDef (oracleText := hauntOfTheDeadMarshesOracle)

#guard hauntOfTheDeadMarshes.oracleText == hauntOfTheDeadMarshesOracle
#guard hauntOfTheDeadMarshes.triggeredAbilities == #[.onEnterScry 1]
#guard hauntOfTheDeadMarshes.activatedAbilities == #[
      activated (Effect.returnFromGraveyardTapped) (ManaCost.ofGenericAndColor 2 .black)
        (activateFromGraveyard := true) (onlyIfYouControlLegendary := true)]

/-- Oracle text for Languish. -/
def languishOracle : String :=
  "All creatures get -4/-4 until end of turn."

def languishDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Languish",
    .manaCost [.generic 2, .mono .black, .mono .black],
    .type .sorcery
  ] ++ (parseOracleParts (name := "Languish") languishOracle).get!

#guard languishDefinition == .card [
  .name "Languish",
  .manaCost [.generic 2, .mono .black, .mono .black],
  .type .sorcery,
  .actions [
    .continuous
      [.addPower
        (.intersection [.permanent, .cardType .creature]) (Value.int (-4)),
       .addToughness
        (.intersection [.permanent, .cardType .creature]) (Value.int (-4))]
      .endOfTurn]]

def languish : CardDef :=
  languishDefinition.toCardDef (oracleText := languishOracle)

def shadowOfTheEnemy : CardDef :=
  sorcery "Shadow of the Enemy" (ManaCost.ofGenericAndColors 3 [.black, .black, .black])
    "Exile all creature cards from target player's graveyard. You may cast spells from among those cards for as long as they remain exiled, and mana of any type can be spent to cast them."
    (some (Effect.exileGraveyardCreaturesGrantCast))

def trollOfKhazadDum : CardDef :=
  creature "Troll of Khazad-dûm" (ManaCost.ofGenericAndColor 5 .black) #["Troll"] 6 5
    (oracleText := "This creature can't be blocked except by three or more creatures.\nSwampcycling {1} ({1}, Discard this card: Search your library for a Swamp card, reveal it, put it into your hand, then shuffle.)")
    (staticAbilities := #[.cantBeBlockedExceptBy 3])
    (activatedAbilities := #[typecyclingAbility "Swamp"])

/-- Oracle text for Merciless Executioner. -/
def mercilessExecutionerOracle : String :=
  "When this creature enters, each player sacrifices a creature of their choice."

def mercilessExecutionerDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Merciless Executioner",
    .manaCost [.generic 2, .mono .black],
    .type .creature,
    .subtype .orc,
    .subtype .warrior,
    .power 3,
    .toughness 1
  ] ++ (parseOracleParts (name := "Merciless Executioner") mercilessExecutionerOracle).get!

#guard mercilessExecutionerDefinition == .card [
  .name "Merciless Executioner",
  .manaCost [.generic 2, .mono .black],
  .type .creature,
  .subtype .orc,
  .subtype .warrior,
  .power 3,
  .toughness 1,
  .ability (
    .triggered
      (.enter .this)
      (.forEachVariable 1 .player [
        .sacrifice
          (.selected
            (.variable 1)
            (.range 1 1)
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.variable 1)]))]))]

def mercilessExecutioner : CardDef :=
  mercilessExecutionerDefinition.toCardDef (oracleText := mercilessExecutionerOracle)

def bitterDownfall : CardDef :=
  instant "Bitter Downfall" (ManaCost.ofGenericAndColor 3 .black)
    "This spell costs {3} less to cast if it targets a creature that was dealt damage this turn.\nDestroy target creature. Its controller loses 2 life."
    (some (Effect.destroyTargetCreatureControllerLosesLife 2))
    (costReductionIfTargetDamaged := 3)

/-- Oracle text for Night's Whisper. -/
def nightsWhisperOracle : String :=
  "You draw two cards and lose 2 life."

def nightsWhisperDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Night's Whisper",
    .manaCost [.generic 1, .mono .black],
    .type .sorcery
  ] ++ (parseOracleParts (name := "Night's Whisper") nightsWhisperOracle).get!

#guard nightsWhisperDefinition == .card [
  .name "Night's Whisper",
  .manaCost [.generic 1, .mono .black],
  .type .sorcery,
  .actions [
    .draw (.controller .this) 2,
    .loseLife (.controller .this) 2]]

def nightsWhisper : CardDef :=
  nightsWhisperDefinition.toCardDef (oracleText := nightsWhisperOracle)

/-- Oracle text for Wayfarer's Bauble. -/
def wayfarersBaubleOracle : String :=
  "{2}, {T}, Sacrifice this artifact: Search your library for a basic land card, put that card onto the battlefield tapped, then shuffle."

def wayfarersBaubleDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Wayfarer's Bauble",
    .manaCost [.generic 1],
    .type .artifact
  ] ++ (parseOracleParts (name := "Wayfarer's Bauble") wayfarersBaubleOracle).get!

#guard wayfarersBaubleDefinition == .card [
  .name "Wayfarer's Bauble",
  .manaCost [.generic 1],
  .type .artifact,
  .ability (
    .activated
      [.mana [.generic 2], .tapSymbol, .sacrifice .this]
      (.searchLibraryThenShuffle
        (.controller .this)
        [
          .putOntoBattlefieldInState
            (.selected
              (.controller .this)
              (.range 1 1)
              (.intersection [
                .inLibrary,
                .cardType .land,
                .supertype .basic]))
            [.tapped]]))]

def wayfarersBauble : CardDef :=
  wayfarersBaubleDefinition.toCardDef (oracleText := wayfarersBaubleOracle)

/-- Oracle text for Battle-Scarred Goblin. -/
def battleScarredGoblinOracle : String :=
  "Whenever this creature becomes blocked, it deals 1 damage to each creature blocking it."

def battleScarredGoblinDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Battle-Scarred Goblin",
    .manaCost [.generic 1, .mono .red],
    .type .creature,
    .subtype .goblin,
    .subtype .warrior,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Battle-Scarred Goblin") battleScarredGoblinOracle).get!

#guard battleScarredGoblinDefinition == .card [
  .name "Battle-Scarred Goblin",
  .manaCost [.generic 1, .mono .red],
  .type .creature,
  .subtype .goblin,
  .subtype .warrior,
  .power 2,
  .toughness 2,
  .ability (
    .triggered
      (.block .all .this)
      (.dealDamage .this (.blocking .this) (.nat 1)))]

def battleScarredGoblin : CardDef :=
  battleScarredGoblinDefinition.toCardDef (oracleText := battleScarredGoblinOracle)

/-- Oracle text for Improvised Club. -/
def improvisedClubOracle : String :=
  "As an additional cost to cast this spell, sacrifice an artifact or creature.\nImprovised Club deals 4 damage to any target."

def improvisedClubDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Improvised Club",
    .manaCost [.generic 1, .mono .red],
    .type .instant
  ] ++ (parseOracleParts (name := "Improvised Club") improvisedClubOracle).get!

#guard improvisedClubDefinition == .card [
  .name "Improvised Club",
  .manaCost [.generic 1, .mono .red],
  .type .instant,
  .ability (
    .stackStatic
      (.additionalCost .this
        [.sacrificeCount
          (.intersection [
            .permanent,
            .union [.cardType .artifact, .cardType .creature]])
          1])),
  .actions [.dealDamage .this (.target 1 .all) (.nat 4)]]

def improvisedClub : CardDef :=
  improvisedClubDefinition.toCardDef (oracleText := improvisedClubOracle)

/-- Oracle text for Olog-hai Crusher. -/
def ologHaiCrusherOracle : String :=
  "Trample\nThis creature can't block unless you control a Goblin or Orc."

def ologHaiCrusherDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Olog-hai Crusher",
    .manaCost [.generic 3, .mono .red],
    .type .creature,
    .subtype .troll,
    .subtype .soldier,
    .power 4,
    .toughness 4
  ] ++ (parseOracleParts (name := "Olog-hai Crusher") ologHaiCrusherOracle).get!

#guard ologHaiCrusherDefinition == .card [
  .name "Olog-hai Crusher",
  .manaCost [.generic 3, .mono .red],
  .type .creature,
  .subtype .troll,
  .subtype .soldier,
  .power 4,
  .toughness 4,
  .ability (.keyword .trample),
  .ability
    (.static
      (.if
        (.not
          (.any
            (.intersection
              [
                .permanent,
                .union [.subtype .goblin, .subtype .orc],
                .controlled (.controller .this)])))
        [.forbid (.block .this .all)]))]

def ologHaiCrusher : CardDef :=
  ologHaiCrusherDefinition.toCardDef (oracleText := ologHaiCrusherOracle)

#guard ologHaiCrusher.oracleText == ologHaiCrusherOracle
#guard ologHaiCrusher.keywords == Keyword.trample
#guard ologHaiCrusher.staticAbilities == #[.cantBlockUnlessYouControl #["Goblin", "Orc"]]

def smiteTheDeathless : CardDef :=
  instant "Smite the Deathless" (ManaCost.ofGenericAndColor 1 .red)
    "Smite the Deathless deals 3 damage to target creature. That creature loses indestructible until end of turn. If that creature would die this turn, exile it instead."
    (some (Effect.dealDamageLoseIndestructibleExile 3))

/-- Oracle text for Goblin Fireleaper. -/
def goblinFireleaperOracle : String :=
  "{1}{R}: This creature gets +1/+0 until end of turn.\nWhen this creature dies, it deals damage equal to its power to target creature an opponent controls."

def goblinFireleaperDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Goblin Fireleaper",
    .manaCost [.generic 1, .mono .red],
    .type .creature,
    .subtype .goblin,
    .subtype .warrior,
    .power 1,
    .toughness 1
  ] ++ (parseOracleParts (name := "Goblin Fireleaper") goblinFireleaperOracle).get!

#guard goblinFireleaperDefinition == .card [
  .name "Goblin Fireleaper",
  .manaCost [.generic 1, .mono .red],
  .type .creature,
  .subtype .goblin,
  .subtype .warrior,
  .power 1,
  .toughness 1,
  .ability (
    .activated
      [.mana [.generic 1, .mono .red]]
      (.continuous [.addPower (.source .this) (Value.int 1)] .endOfTurn)),
  .ability (
    .triggered
      (.die .this)
      (.dealDamageEqualToPower
        .this
        (.target
          1
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.opponent (.controller .this))]))))]

def goblinFireleaper : CardDef :=
  goblinFireleaperDefinition.toCardDef (oracleText := goblinFireleaperOracle)

/-- Oracle text for Oliphaunt. -/
def oliphauntOracle : String :=
  "Trample\nWhenever this creature attacks, another target creature you control gets +2/+0 and gains trample until end of turn.\nMountaincycling {1} ({1}, Discard this card: Search your library for a Mountain card, reveal it, put it into your hand, then shuffle.)"

def oliphauntDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Oliphaunt",
    .manaCost [.generic 5, .mono .red],
    .type .creature,
    .subtype .elephant,
    .power 6,
    .toughness 4
  ] ++ (parseOracleParts (name := "Oliphaunt") oliphauntOracle).get!

#guard oliphauntDefinition == .card [
  .name "Oliphaunt",
  .manaCost [.generic 5, .mono .red],
  .type .creature,
  .subtype .elephant,
  .power 6,
  .toughness 4,
  .ability (.keyword .trample),
  .ability (
    .triggered
      (.attack .this .all)
      (.continuous
        [
          .addPower
            (.target
              1
              (.intersection [
                .not .this,
                .permanent,
                .cardType .creature,
                .controlled (.controller .this)])) (Value.int 2),
          .gainAbility (.targetReference 1) (.keyword .trample)]
        .endOfTurn)),
  .ability (.keywordWithCost (.typecycling [] [] [.mountain]) [.mana [.generic 1]])]

def oliphaunt : CardDef :=
  oliphauntDefinition.toCardDef (oracleText := oliphauntOracle)

def goblinCratermaker : CardDef :=
  creature "Goblin Cratermaker" (ManaCost.ofGenericAndColor 1 .red) #["Goblin", "Warrior"] 2 2
    (oracleText := "{1}, Sacrifice this creature: Choose one —\n• This creature deals 2 damage to target creature.\n• Destroy target colorless nonland permanent.")
    (activatedAbilities := #[
      activated (Effect.dealDamageToTargetCreature 2) (ManaCost.ofGeneric 1)
        (sacrificeSource := true)
        (otherModes := #[Effect.destroyTargetColorlessNonland])])

/-- Oracle text for Inferno Titan. -/
def infernoTitanOracle : String :=
  "{R}: This creature gets +1/+0 until end of turn.\nWhenever this creature enters or attacks, it deals 3 damage divided as you choose among one, two, or three targets."

def infernoTitanDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Inferno Titan",
    .manaCost [.generic 4, .mono .red, .mono .red],
    .type .creature,
    .subtype .giant,
    .power 6,
    .toughness 6
  ] ++ (parseOracleParts (name := "Inferno Titan") infernoTitanOracle).get!

#guard infernoTitanDefinition == .card [
  .name "Inferno Titan",
  .manaCost [.generic 4, .mono .red, .mono .red],
  .type .creature,
  .subtype .giant,
  .power 6,
  .toughness 6,
  .ability (
    .activated
      [.mana [.mono .red]]
      (.continuous [.addPower (.source .this) (Value.int 1)] .endOfTurn)),
  .ability (
    .triggered
      (.or (.enter .this) (.attack .this .all))
      (.divideDamage
        (.controller .this)
        .this
        (.targets 1 (.range 1 3) .all)
        3))]

def infernoTitan : CardDef :=
  infernoTitanDefinition.toCardDef (oracleText := infernoTitanOracle)

/-- Oracle text for Guttersnipe. -/
def guttersnipeOracle : String :=
  "Whenever you cast an instant or sorcery spell, this creature deals 2 damage to each opponent."

def guttersnipeDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Guttersnipe",
    .manaCost [.generic 2, .mono .red],
    .type .creature,
    .subtype .goblin,
    .subtype .shaman,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Guttersnipe") guttersnipeOracle).get!

#guard guttersnipeDefinition == .card [
  .name "Guttersnipe",
  .manaCost [.generic 2, .mono .red],
  .type .creature,
  .subtype .goblin,
  .subtype .shaman,
  .power 2,
  .toughness 2,
  .ability (
    .triggered
      (.castSpell
        (.intersection [
          .union [.cardType .instant, .cardType .sorcery],
          .controlled (.controller .this)]))
      (.dealDamage .this (.opponent (.controller .this)) (.nat 2)))]

def guttersnipe : CardDef :=
  guttersnipeDefinition.toCardDef (oracleText := guttersnipeOracle)

/-- Oracle text for Orcish Siegemaster. -/
def orcishSiegemasterOracle : String :=
  "Trample\nOther Orcs and Goblins you control have trample.\nWhenever this creature attacks, it gets +X/+0 until end of turn, where X is the greatest power among creatures you control."

def orcishSiegemasterDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Orcish Siegemaster",
    .manaCost [.generic 2, .mono .red],
    .type .creature,
    .subtype .orc,
    .subtype .soldier,
    .power 0,
    .toughness 5
  ] ++ (parseOracleParts (name := "Orcish Siegemaster") orcishSiegemasterOracle).get!

#guard orcishSiegemasterDefinition == .card [
  .name "Orcish Siegemaster",
  .manaCost [.generic 2, .mono .red],
  .type .creature,
  .subtype .orc,
  .subtype .soldier,
  .power 0,
  .toughness 5,
  .ability (.keyword .trample),
  .ability
    (.static
      (.gainAbility
        (.intersection
          [
            .not .this,
            .permanent,
            .union [.subtype .orc, .subtype .goblin],
            .controlled (.controller .this)])
        (.keyword .trample))),
  .ability
    (.triggered
      (.attack .this .all)
      (.continuous
        [
          .addPower
            (.source .this)
            (.greatestPower
              (.intersection [.permanent, .cardType .creature, .controlled (.controller .this)]))]
        .endOfTurn))]

def orcishSiegemaster : CardDef :=
  orcishSiegemasterDefinition.toCardDef (oracleText := orcishSiegemasterOracle)

#guard orcishSiegemaster.oracleText == orcishSiegemasterOracle
#guard orcishSiegemaster.keywords == Keyword.trample
#guard orcishSiegemaster.staticAbilities == #[.otherCreaturesHaveTrample #["Orc", "Goblin"]]
#guard orcishSiegemaster.triggeredAbilities == #[.onAttackPumpByGreatestPower]

/-- Oracle text for Fire of Orthanc. -/
def fireOfOrthancOracle : String :=
  "Destroy target artifact or land. Creatures without flying can't block this turn."

def fireOfOrthancDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Fire of Orthanc",
    .manaCost [.generic 3, .mono .red],
    .type .sorcery
  ] ++ (parseOracleParts (name := "Fire of Orthanc") fireOfOrthancOracle).get!

#guard fireOfOrthancDefinition == .card [
  .name "Fire of Orthanc",
  .manaCost [.generic 3, .mono .red],
  .type .sorcery,
  .actions [
    .destroy
      (.target
        1
        (.intersection [
          .permanent,
          .union [.cardType .artifact, .cardType .land]])),
    .continuous
      [.forbid (.block (.not (.keyword .flying)) .all)]
      .endOfTurn]]

def fireOfOrthanc : CardDef :=
  fireOfOrthancDefinition.toCardDef (oracleText := fireOfOrthancOracle)

/-- Oracle text for Galadhrim Guide. -/
def galadhrimGuideOracle : String :=
  "When this creature enters, scry 2."

def galadhrimGuideDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Galadhrim Guide",
    .manaCost [.generic 3, .mono .green],
    .type .creature,
    .subtype .elf,
    .subtype .scout,
    .power 3,
    .toughness 4
  ] ++ (parseOracleParts (name := "Galadhrim Guide") galadhrimGuideOracle).get!

#guard galadhrimGuideDefinition == .card [
  .name "Galadhrim Guide",
  .manaCost [.generic 3, .mono .green],
  .type .creature,
  .subtype .elf,
  .subtype .scout,
  .power 3,
  .toughness 4,
  .ability (.triggered (.enter .this) (.scry (.controller .this) 2))]

def galadhrimGuide : CardDef :=
  galadhrimGuideDefinition.toCardDef (oracleText := galadhrimGuideOracle)

/-- Oracle text for Elvish Visionary. -/
def elvishVisionaryOracle : String :=
  "When this creature enters, draw a card."

def elvishVisionaryDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Elvish Visionary",
    .manaCost [.generic 1, .mono .green],
    .type .creature,
    .subtype .elf,
    .subtype .shaman,
    .power 1,
    .toughness 1
  ] ++ (parseOracleParts (name := "Elvish Visionary") elvishVisionaryOracle).get!

#guard elvishVisionaryDefinition == .card [
  .name "Elvish Visionary",
  .manaCost [.generic 1, .mono .green],
  .type .creature,
  .subtype .elf,
  .subtype .shaman,
  .power 1,
  .toughness 1,
  .ability (.triggered (.enter .this) (.draw (.controller .this) 1))]

def elvishVisionary : CardDef :=
  elvishVisionaryDefinition.toCardDef (oracleText := elvishVisionaryOracle)

/-- Oracle text for Mirkwood Elk. -/
def mirkwoodElkOracle : String :=
  "Trample\nWhenever this creature enters or attacks, return target Elf card from your graveyard to your hand. You gain life equal to that card's power."

def mirkwoodElkDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Mirkwood Elk",
    .manaCost [.generic 5, .mono .green],
    .type .creature,
    .subtype .elk,
    .power 6,
    .toughness 6
  ] ++ (parseOracleParts (name := "Mirkwood Elk") mirkwoodElkOracle).get!

#guard mirkwoodElkDefinition == .card [
  .name "Mirkwood Elk",
  .manaCost [.generic 5, .mono .green],
  .type .creature,
  .subtype .elk,
  .power 6,
  .toughness 6,
  .ability (.keyword .trample),
  .ability
    (.triggered
      (.or (.enter .this) (.attack .this .all))
      (.sequence
        [
          .returnToHand
            (.target 1 (.intersection [.inGraveyard, .subtype .elf, .owner (.controller .this)])),
          .gainLife (.controller .this) (.greatestPower (.targetReference 1))]))]

def mirkwoodElk : CardDef :=
  mirkwoodElkDefinition.toCardDef (oracleText := mirkwoodElkOracle)

#guard mirkwoodElk.oracleText == mirkwoodElkOracle
#guard mirkwoodElk.keywords == Keyword.trample
#guard mirkwoodElk.triggeredAbilities == #[.onEnterOrAttackReturnElfGainLife]

def celebornTheWise : CardDef :=
  legendaryCreature "Celeborn the Wise" (ManaCost.ofGenericAndColor 3 .green) #["Elf", "Noble"] 3 3
    (oracleText := "Whenever you attack with one or more Elves, scry 1.\nWhenever you scry, Celeborn gets +1/+1 until end of turn for each card looked at while scrying this way.")
    (triggeredAbilities := #[.onAttackWithElvesScry 1, .onScryPumpSelfForEachLookedAt])

/-- Oracle text for Gift of Strands. -/
def giftOfStrandsOracle : String :=
  "Flash\nEnchant creature\nWhen this Aura enters, scry 2.\nEnchanted creature gets +3/+3."

def giftOfStrandsDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Gift of Strands",
    .manaCost [.generic 3, .mono .green],
    .type .enchantment,
    .subtype .aura
  ] ++ (parseOracleParts (name := "Gift of Strands") giftOfStrandsOracle).get!

#guard giftOfStrandsDefinition == .card [
  .name "Gift of Strands",
  .manaCost [.generic 3, .mono .green],
  .type .enchantment,
  .subtype .aura,
  .ability (.keyword .flash),
  .ability (
    .keywordWithTarget
      .enchant
      1
      (.intersection [.permanent, .cardType .creature])),
  .ability (.triggered (.enter .this) (.scry (.controller .this) 2)),
  .ability (.static (.addPower (.hostOf .this) (Value.int 3))),
  .ability (.static (.addToughness (.hostOf .this) (Value.int 3)))]

def giftOfStrands : CardDef :=
  giftOfStrandsDefinition.toCardDef (oracleText := giftOfStrandsOracle)

/-- Oracle text for Elvish Archdruid. -/
def elvishArchdruidOracle : String :=
  "Other Elf creatures you control get +1/+1.\n{T}: Add {G} for each Elf you control."

def elvishArchdruidDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Elvish Archdruid",
    .manaCost [.generic 1, .mono .green, .mono .green],
    .type .creature,
    .subtype .elf,
    .subtype .druid,
    .power 2,
    .toughness 2
  ] ++ (parseOracleParts (name := "Elvish Archdruid") elvishArchdruidOracle).get!

#guard elvishArchdruidDefinition == .card [
  .name "Elvish Archdruid",
  .manaCost [.generic 1, .mono .green, .mono .green],
  .type .creature,
  .subtype .elf,
  .subtype .druid,
  .power 2,
  .toughness 2,
  .ability
    (.static
      (.addPower
        (.intersection
          [
            .not .this,
            .permanent,
            .cardType .creature,
            .subtype .elf,
            .controlled (.controller .this)])
        (.int 1))),
  .ability
    (.static
      (.addToughness
        (.intersection
          [
            .not .this,
            .permanent,
            .cardType .creature,
            .subtype .elf,
            .controlled (.controller .this)])
        (.int 1))),
  .ability
    (.activated
      [.tapSymbol]
      (.forEachVariable
        1
        (.intersection [.permanent, .subtype .elf, .controlled (.controller .this)])
        [.addMana (.controller .this) [.mono .green]]))]

def elvishArchdruid : CardDef :=
  elvishArchdruidDefinition.toCardDef (oracleText := elvishArchdruidOracle)

#guard elvishArchdruid.oracleText == elvishArchdruidOracle
#guard elvishArchdruid.staticAbilities == #[.otherCreaturesGet #["Elf"] 1 1]
#guard elvishArchdruid.tapAddManaForEach == #[{ mana := .colored .green, subtype := "Elf" }]

/-- Oracle text for Lothlórien Lookout. -/
def lothlorienLookoutOracle : String :=
  "Whenever this creature attacks, scry 1."

def lothlorienLookoutDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Lothlórien Lookout",
    .manaCost [.generic 1, .mono .green],
    .type .creature,
    .subtype .elf,
    .subtype .scout,
    .power 1,
    .toughness 3
  ] ++ (parseOracleParts (name := "Lothlórien Lookout") lothlorienLookoutOracle).get!

#guard lothlorienLookoutDefinition == .card [
  .name "Lothlórien Lookout",
  .manaCost [.generic 1, .mono .green],
  .type .creature,
  .subtype .elf,
  .subtype .scout,
  .power 1,
  .toughness 3,
  .ability (.triggered (.attack .this .all) (.scry (.controller .this) 1))]

def lothlorienLookout : CardDef :=
  lothlorienLookoutDefinition.toCardDef (oracleText := lothlorienLookoutOracle)

/-- Oracle text for Elvish Mystic. -/
def elvishMysticOracle : String :=
  "{T}: Add {G}."

def elvishMysticDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Elvish Mystic",
    .manaCost [.mono .green],
    .type .creature,
    .subtype .elf,
    .subtype .druid,
    .power 1,
    .toughness 1
  ] ++ (parseOracleParts (name := "Elvish Mystic") elvishMysticOracle).get!

#guard elvishMysticDefinition == .card [
  .name "Elvish Mystic",
  .manaCost [.mono .green],
  .type .creature,
  .subtype .elf,
  .subtype .druid,
  .power 1,
  .toughness 1,
  .ability (.activated [.tapSymbol] (.addMana (.controller .this) [.mono .green]))]

def elvishMystic : CardDef :=
  elvishMysticDefinition.toCardDef (oracleText := elvishMysticOracle)

/-- Oracle text for Bard, Heir of Girion. -/
def bardHeirOfGirionOracle : String :=
  "Reach, vigilance\nOther creatures you control get +1/+1.\nWhenever you attack, draw a card."

def bardHeirOfGirionDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Bard, Heir of Girion",
    .manaCost [.generic 2, .mono .white, .mono .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .human,
    .subtype .archer,
    .power 4,
    .toughness 4
  ] ++ (parseOracleParts (name := "Bard, Heir of Girion") bardHeirOfGirionOracle).get!

#guard bardHeirOfGirionDefinition == .card [
  .name "Bard, Heir of Girion",
  .manaCost [.generic 2, .mono .white, .mono .blue],
  .type .creature,
  .supertype .legendary,
  .subtype .human,
  .subtype .archer,
  .power 4,
  .toughness 4,
  .ability (.keyword .reach),
  .ability (.keyword .vigilance),
  .ability (.static (.addPower
        (.intersection [
          .not .this,
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)]) (Value.int 1))),
  .ability (.static (.addToughness
        (.intersection [
          .not .this,
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)]) (Value.int 1))),
  .ability
    (.triggered
      (.attackSimultaneously
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)])
        .all
        [])
      (.draw (.controller .this) 1))]

def bardHeirOfGirion : CardDef :=
  bardHeirOfGirionDefinition.toCardDef (oracleText := bardHeirOfGirionOracle)

/-- Oracle text for Reprieve. -/
def reprieveOracle : String :=
  "Return target spell to its owner's hand.\nDraw a card."

def reprieveDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Reprieve",
    .manaCost [.generic 1, .mono .white],
    .type .instant
  ] ++ (parseOracleParts (name := "Reprieve") reprieveOracle).get!

#guard reprieveDefinition == .card [
  .name "Reprieve",
  .manaCost [.generic 1, .mono .white],
  .type .instant,
  .actions [
    .returnToHand (.target 1 .spell),
    .draw (.controller .this) 1]]

def reprieve : CardDef :=
  reprieveDefinition.toCardDef (oracleText := reprieveOracle)

/-- Oracle text for Great Goblin, Foul-Hearted. -/
def greatGoblinFoulHeartedOracle : String :=
  "Whenever Great Goblin enters or attacks, amass Goblins 3. (Put three +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)\nArmies you control have trample."

def greatGoblinFoulHeartedDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Great Goblin, Foul-Hearted",
    .manaCost [.generic 3, .mono .black, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .goblin,
    .subtype .noble,
    .power 3,
    .toughness 3
  ] ++ (parseOracleParts (name := "Great Goblin, Foul-Hearted") greatGoblinFoulHeartedOracle).get!

#guard greatGoblinFoulHeartedDefinition == .card [
  .name "Great Goblin, Foul-Hearted",
  .manaCost [.generic 3, .mono .black, .mono .red],
  .type .creature,
  .supertype .legendary,
  .subtype .goblin,
  .subtype .noble,
  .power 3,
  .toughness 3,
  .ability (
    .triggered
      (.or (.enter .this) (.attack .this .all))
      (.keyword (.controller .this) (.amass .goblin (.nat 3)))),
  .ability (
    .static
      (.gainAbility
        (.intersection [
          .permanent,
          .subtype .army,
          .controlled (.controller .this)])
        (.keyword .trample)))]

def greatGoblinFoulHearted : CardDef :=
  greatGoblinFoulHeartedDefinition.toCardDef (oracleText := greatGoblinFoulHeartedOracle)

/-- Oracle text for Dwarven Warriors. -/
def dwarvenWarriorsOracle : String :=
  "{T}: Target creature with power 2 or less can't be blocked this turn."

def dwarvenWarriorsDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Dwarven Warriors",
    .manaCost [.generic 2, .mono .red],
    .type .creature,
    .subtype .dwarf,
    .subtype .warrior,
    .power 1,
    .toughness 1
  ] ++ (parseOracleParts (name := "Dwarven Warriors") dwarvenWarriorsOracle).get!

#guard dwarvenWarriorsDefinition == .card [
  .name "Dwarven Warriors",
  .manaCost [.generic 2, .mono .red],
  .type .creature,
  .subtype .dwarf,
  .subtype .warrior,
  .power 1,
  .toughness 1,
  .ability
    (.activated
      [.tapSymbol]
      (.continuous
        [
          .forbid
            (.block
              .all
              (.target 1 (.intersection [.permanent, .cardType .creature, .powerAtMost (.int 2)])))]
        .endOfTurn))]

def dwarvenWarriors : CardDef :=
  dwarvenWarriorsDefinition.toCardDef (oracleText := dwarvenWarriorsOracle)

#guard dwarvenWarriors.oracleText == dwarvenWarriorsOracle
#guard dwarvenWarriors.activatedAbilities == #[
      activated (Effect.targetCantBeBlockedPowerAtMost 2) (tap := true)]

/-- Oracle text for Bag End Banquet. -/
def bagEndBanquetOracle : String :=
  "When this artifact enters, create three Food tokens.\n{T}: Add {C} for each Food you control."

def bagEndBanquetDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Bag End Banquet",
    .manaCost [.generic 6],
    .type .artifact
  ] ++ (parseOracleParts (name := "Bag End Banquet") bagEndBanquetOracle).get!

#guard bagEndBanquetDefinition == .card [
  .name "Bag End Banquet",
  .manaCost [.generic 6],
  .type .artifact,
  .ability
    (.triggered
      (.enter .this)
      (.createTokens
        (.controller .this)
        (.nat 3)
        [
          .type .artifact,
          .subtype .food,
          .ability
            (.activated
              [.mana [.generic 2], .tapSymbol, .sacrifice .this]
              (.gainLife (.controller .this) (.nat 3)))]
        [])),
  .ability
    (.activated
      [.tapSymbol]
      (.forEachVariable
        1
        (.intersection [.permanent, .subtype .food, .controlled (.controller .this)])
        [.addMana (.controller .this) [.colorless]]))]

def bagEndBanquet : CardDef :=
  bagEndBanquetDefinition.toCardDef (oracleText := bagEndBanquetOracle)

#guard bagEndBanquet.oracleText == bagEndBanquetOracle
#guard bagEndBanquet.triggeredAbilities == #[.onEnterCreateTokens .food 3]
#guard bagEndBanquet.tapAddManaForEach == #[⟨.colorless, "Food"⟩]

/-- Oracle text for Flowering of the White Tree. -/
def floweringOfTheWhiteTreeOracle : String :=
  "Legendary creatures you control get +2/+1 and have ward {1}.\nNonlegendary creatures you control get +1/+1."

def floweringOfTheWhiteTreeDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Flowering of the White Tree",
    .manaCost [.mono .white, .mono .white],
    .type .enchantment,
    .supertype .legendary
  ] ++ (parseOracleParts (name := "Flowering of the White Tree") floweringOfTheWhiteTreeOracle).get!

#guard floweringOfTheWhiteTreeDefinition == .card [
  .name "Flowering of the White Tree",
  .manaCost [.mono .white, .mono .white],
  .type .enchantment,
  .supertype .legendary,
  .ability
    (.static
      (.addPower
        (.intersection
          [.permanent, .cardType .creature, .controlled (.controller .this), .supertype .legendary])
        (.int 2))),
  .ability
    (.static
      (.addToughness
        (.intersection
          [.permanent, .cardType .creature, .controlled (.controller .this), .supertype .legendary])
        (.int 1))),
  .ability
    (.static
      (.gainAbility
        (.intersection
          [.permanent, .cardType .creature, .controlled (.controller .this), .supertype .legendary])
        (.keywordWithCost .ward [.mana [.generic 1]]))),
  .ability
    (.static
      (.addPower
        (.intersection
          [
            .permanent,
            .cardType .creature,
            .not (.supertype .legendary),
            .controlled (.controller .this)])
        (.int 1))),
  .ability
    (.static
      (.addToughness
        (.intersection
          [
            .permanent,
            .cardType .creature,
            .not (.supertype .legendary),
            .controlled (.controller .this)])
        (.int 1)))]

def floweringOfTheWhiteTree : CardDef :=
  floweringOfTheWhiteTreeDefinition.toCardDef (oracleText := floweringOfTheWhiteTreeOracle)

#guard floweringOfTheWhiteTree.oracleText == floweringOfTheWhiteTreeOracle
#guard floweringOfTheWhiteTree.supertypes == #[.legendary]
#guard floweringOfTheWhiteTree.staticAbilities == #[
      .legendaryCreaturesGetAndWard 2 1 1,
      .nonlegendaryCreaturesGet 1 1]

/-- Oracle text for Mithril Coat. -/
def mithrilCoatOracle : String :=
  "Flash\nIndestructible\nWhen Mithril Coat enters, attach it to target legendary creature you control.\nEquipped creature has indestructible.\nEquip {3}"

def mithrilCoatDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Mithril Coat",
    .manaCost [.generic 3],
    .type .artifact,
    .subtype .equipment,
    .supertype .legendary
  ] ++ (parseOracleParts (name := "Mithril Coat") mithrilCoatOracle).get!

#guard mithrilCoatDefinition == .card [
  .name "Mithril Coat",
  .manaCost [.generic 3],
  .type .artifact,
  .subtype .equipment,
  .supertype .legendary,
  .ability (.keyword .flash),
  .ability (.keyword .indestructible),
  .ability (
    .triggered
      (.enter .this)
      (.attach
        .this
        (.target
          1
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this),
            .supertype .legendary])))),
  .ability (.static (.gainAbility (.hostOf .this) (.keyword .indestructible))),
  .ability (.keywordWithCost .equip [.mana [.generic 3]])]

def mithrilCoat : CardDef :=
  mithrilCoatDefinition.toCardDef (oracleText := mithrilCoatOracle)

/-- Oracle text for Rivendell. -/
def rivendellOracle : String :=
  "Rivendell enters tapped unless you control a legendary creature.\n{T}: Add {U}.\n{1}{U}, {T}: Scry 2. Activate only if you control a legendary creature."

def rivendellDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Rivendell",
    .type .land,
    .supertype .legendary
  ] ++ (parseOracleParts (name := "Rivendell") rivendellOracle).get!

#guard rivendellDefinition == .card [
  .name "Rivendell",
  .type .land,
  .supertype .legendary,
  .ability
    (.everywhereStatic
      (.if
        (.not
          (.any
            (.intersection
              [
                .permanent,
                .cardType .creature,
                .supertype .legendary,
                .controlled (.controller .this)])))
        [.replace (.enter .this) [.putOntoBattlefieldInState .this [.tapped]]])),
  .ability (.activated [.tapSymbol] (.addMana (.controller .this) [.mono .blue])),
  .ability
    (.activatedIf
      (.any
        (.intersection
          [.permanent, .cardType .creature, .supertype .legendary, .controlled (.controller .this)]))
      [.mana [.generic 1, .mono .blue], .tapSymbol]
      (.scry (.controller .this) (.nat 2)))]

def rivendell : CardDef :=
  rivendellDefinition.toCardDef (oracleText := rivendellOracle)

#guard rivendell.oracleText == rivendellOracle
#guard rivendell.tapAddMana == #[.colored .blue]
#guard rivendell.entersTappedUnlessLegendary == true
#guard rivendell.activatedAbilities == #[
      activated (Effect.abilityScry 2) (ManaCost.ofGenericAndColor 1 .blue) (tap := true)
        (onlyIfYouControlLegendary := true)]

def delightedHalfling : CardDef :=
  creature "Delighted Halfling" (ManaCost.ofColor .green) #["Halfling", "Citizen"] 1 2
    (oracleText := "{T}: Add {C}.\n{T}: Add one mana of any color. Spend this mana only to cast a legendary spell, and that spell can't be countered.")
    (tapAddMana := #[.colorless])
    (tapAddAnyColorForLegendary := true)

/-- Oracle text for Relic of Sauron. -/
def relicOfSauronOracle : String :=
  "{T}: Add two mana in any combination of {U}, {B}, and/or {R}.\n{3}, {T}: Draw two cards, then discard a card."

def relicOfSauronDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Relic of Sauron",
    .manaCost [.generic 4],
    .type .artifact
  ] ++ (parseOracleParts (name := "Relic of Sauron") relicOfSauronOracle).get!

#guard relicOfSauronDefinition == .card [
  .name "Relic of Sauron",
  .manaCost [.generic 4],
  .type .artifact,
  .ability
    (.activated
      [.tapSymbol]
      (.addManaInAnyCombination (.controller .this) [.mono .blue, .mono .black, .mono .red] (.nat 2))),
  .ability
    (.activated
      [.mana [.generic 3], .tapSymbol]
      (.sequence [.draw (.controller .this) (.nat 2), .discard (.controller .this) (.nat 1)]))]

def relicOfSauron : CardDef :=
  relicOfSauronDefinition.toCardDef (oracleText := relicOfSauronOracle)

#guard relicOfSauron.oracleText == relicOfSauronOracle
#guard relicOfSauron.tapAddTwoAmong == #[.colored .blue, .colored .black, .colored .red]
#guard relicOfSauron.activatedAbilities == #[
      activated (Effect.abilityDrawThenDiscard 2) (ManaCost.ofGeneric 3) (tap := true)]

def longLostLances : CardDef :=
  artifact "Long-Lost Lances" (ManaCost.ofGeneric 2)
    "Equipped creature gets +2/+0.\nDuring your turn, creatures you control that are equipped have first strike and vigilance.\nEquip {2}"
    (subtypes := #["Equipment"])
    (staticAbilities := #[
      .equippedCreatureGets 2 0,
      .equippedCreaturesHaveKeywordsDuringYourTurn (Keyword.firstStrike.merge Keyword.vigilance)])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 2)])

/-- Oracle text for Lotho, Corrupt Shirriff. -/
def lothoCorruptShirriffOracle : String :=
  "Whenever a player casts their second spell each turn, you lose 1 life and create a Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")"

def lothoCorruptShirriffDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Lotho, Corrupt Shirriff",
    .manaCost [.mono .white, .mono .black],
    .type .creature,
    .supertype .legendary,
    .subtype .halfling,
    .subtype .rogue,
    .power 2,
    .toughness 1
  ] ++ (parseOracleParts (name := "Lotho, Corrupt Shirriff") lothoCorruptShirriffOracle).get!

#guard lothoCorruptShirriffDefinition == .card [
  .name "Lotho, Corrupt Shirriff",
  .manaCost [.mono .white, .mono .black],
  .type .creature,
  .supertype .legendary,
  .subtype .halfling,
  .subtype .rogue,
  .power 2,
  .toughness 1,
  .ability (
    .triggered
      (.ordinal 2 .turnStart (.castSpell .spell))
      (.sequence [
        .loseLife (.controller .this) 1,
        .createTokens (.controller .this) 1 PredefinedToken.treasureToken]))]

def lothoCorruptShirriff : CardDef :=
  lothoCorruptShirriffDefinition.toCardDef (oracleText := lothoCorruptShirriffOracle)

def flameOfAnor : CardDef :=
  instant "Flame of Anor" (ManaCost.ofGenericAndColors 1 [.blue, .red])
    "Choose one. If you control a Wizard as you cast this spell, you may choose two instead.\n• Target player draws two cards.\n• Destroy target artifact.\n• Flame of Anor deals 5 damage to target creature."
    (spellModes := #[(Effect.targetPlayerDraw 2), (Effect.destroyTargetArtifact), (Effect.dealDamageToCreature 5)])
    (chooseTwoIfYouControlSubtype := some "Wizard")

/-- Oracle text for Last March of the Ents. -/
def lastMarchOfTheEntsOracle : String :=
  "This spell can't be countered.\nDraw cards equal to the greatest toughness among creatures you control, then put any number of creature cards from your hand onto the battlefield."

def lastMarchOfTheEntsDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Last March of the Ents",
    .manaCost [.generic 6, .mono .green, .mono .green],
    .type .sorcery
  ] ++ (parseOracleParts (name := "Last March of the Ents") lastMarchOfTheEntsOracle).get!

#guard lastMarchOfTheEntsDefinition == .card [
  .name "Last March of the Ents",
  .manaCost [.generic 6, .mono .green, .mono .green],
  .type .sorcery,
  .ability (.stackStatic (.forbid (.counter .this))),
  .actions
    [
      .draw
        (.controller .this)
        (.greatestToughness
          (.intersection [.permanent, .cardType .creature, .controlled (.controller .this)])),
      .putOntoBattlefield
        (.selected
          (.controller .this)
          .any
          (.intersection [.inHand, .owner (.controller .this), .cardType .creature]))]]

def lastMarchOfTheEnts : CardDef :=
  lastMarchOfTheEntsDefinition.toCardDef (oracleText := lastMarchOfTheEntsOracle)

#guard lastMarchOfTheEnts.oracleText == lastMarchOfTheEntsOracle
#guard lastMarchOfTheEnts.spellEffect == (some (Effect.drawEqualToughnessThenPutCreatures))
#guard lastMarchOfTheEnts.cantBeCountered == true

/-- Oracle text for Raise the Palisade. -/
def raiseThePalisadeOracle : String :=
  "Choose a creature type. Return all creatures that aren't of the chosen type to their owners' hands."

def raiseThePalisadeDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Raise the Palisade",
    .manaCost [.generic 4, .mono .blue],
    .type .sorcery
  ] ++ (parseOracleParts (name := "Raise the Palisade") raiseThePalisadeOracle).get!

#guard raiseThePalisadeDefinition == .card [
  .name "Raise the Palisade",
  .manaCost [.generic 4, .mono .blue],
  .type .sorcery,
  .actions
    [
      .actionId 1 (.chooseCreatureType (.controller .this)),
      .returnToHand
        (.intersection [.permanent, .cardType .creature, .not (.hasCreatureTypeChosenByAction 1)])]]

def raiseThePalisade : CardDef :=
  raiseThePalisadeDefinition.toCardDef (oracleText := raiseThePalisadeOracle)

#guard raiseThePalisade.oracleText == raiseThePalisadeOracle
#guard raiseThePalisade.spellEffect == (some (Effect.chooseTypeReturnOthers))

/-- Oracle text for Dragon's Desire. -/
def dragonsDesireOracle : String :=
  "Add {R} for each artifact your opponents control."

def dragonsDesireDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Dragon's Desire",
    .manaCost [.generic 2, .mono .red, .mono .red],
    .type .sorcery
  ] ++ (parseOracleParts (name := "Dragon's Desire") dragonsDesireOracle).get!

#guard dragonsDesireDefinition == .card [
  .name "Dragon's Desire",
  .manaCost [.generic 2, .mono .red, .mono .red],
  .type .sorcery,
  .actions
    [
      .forEachVariable
        1
        (.intersection
          [.permanent, .cardType .artifact, .controlled (.opponent (.controller .this))])
        [.addMana (.controller .this) [.mono .red]]]]

def dragonsDesire : CardDef :=
  dragonsDesireDefinition.toCardDef (oracleText := dragonsDesireOracle)

#guard dragonsDesire.oracleText == dragonsDesireOracle
#guard dragonsDesire.spellEffect == (some (Effect.addRedPerOppArtifacts))

/-- Oracle text for Ori, Plate Stacker. -/
def oriPlateStackerOracle : String :=
  "When Ori enters, destroy all artifacts and enchantments your opponents control. You gain 1 life for each permanent destroyed this way."

def oriPlateStackerDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Ori, Plate Stacker",
    .manaCost [.generic 5, .mono .white, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .bard,
    .power 3,
    .toughness 3
  ] ++ (parseOracleParts (name := "Ori, Plate Stacker") oriPlateStackerOracle).get!

#guard oriPlateStackerDefinition == .card [
  .name "Ori, Plate Stacker",
  .manaCost [.generic 5, .mono .white, .mono .white],
  .type .creature,
  .supertype .legendary,
  .subtype .dwarf,
  .subtype .bard,
  .power 3,
  .toughness 3,
  .ability
    (.triggered
      (.enter .this)
      (.sequence
        [
          .actionId
            1
            (.destroy
              (.intersection
                [
                  .permanent,
                  .union [.cardType .artifact, .cardType .enchantment],
                  .controlled (.opponent (.controller .this))])),
          .gainLife (.controller .this) (.count (.wasObjectOfAction 1))]))]

def oriPlateStacker : CardDef :=
  oriPlateStackerDefinition.toCardDef (oracleText := oriPlateStackerOracle)

#guard oriPlateStacker.oracleText == oriPlateStackerOracle
#guard oriPlateStacker.triggeredAbilities == #[.onEnterDestroyOppArtifactsEnchantmentsGainLife]

/-- Oracle text for Dáin of the Ancient Halls. -/
def dainOfTheAncientHallsOracle : String :=
  "Vigilance, haste\nWhenever Dáin attacks, he deals damage equal to the number of Dwarves you control to each opponent."

def dainOfTheAncientHallsDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Dáin of the Ancient Halls",
    .manaCost [.generic 3, .mono .red, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .noble,
    .power 4,
    .toughness 5
  ] ++ (parseOracleParts (name := "Dáin of the Ancient Halls") dainOfTheAncientHallsOracle).get!

#guard dainOfTheAncientHallsDefinition == .card [
  .name "Dáin of the Ancient Halls",
  .manaCost [.generic 3, .mono .red, .mono .white],
  .type .creature,
  .supertype .legendary,
  .subtype .dwarf,
  .subtype .noble,
  .power 4,
  .toughness 5,
  .ability (.keyword .vigilance),
  .ability (.keyword .haste),
  .ability
    (.triggered
      (.attack .this .all)
      (.dealDamage
        .this
        (.opponent (.controller .this))
        (.count (.intersection [.permanent, .subtype .dwarf, .controlled (.controller .this)]))))]

def dainOfTheAncientHalls : CardDef :=
  dainOfTheAncientHallsDefinition.toCardDef (oracleText := dainOfTheAncientHallsOracle)

#guard dainOfTheAncientHalls.oracleText == dainOfTheAncientHallsOracle
#guard dainOfTheAncientHalls.keywords == Keyword.vigilance.merge Keyword.haste
#guard dainOfTheAncientHalls.triggeredAbilities == #[.onAttackDamageEqualSubtypeToEachOpponent "Dwarf"]

/-- Oracle text for Treasure Vault. -/
def treasureVaultOracle : String :=
  "{T}: Add {C}.\n{X}{X}, {T}, Sacrifice this land: Create X Treasure tokens."

def treasureVaultDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Treasure Vault",
    .type .artifact,
    .type .land
  ] ++ (parseOracleParts (name := "Treasure Vault") treasureVaultOracle).get!

#guard treasureVaultDefinition == .card [
  .name "Treasure Vault",
  .type .artifact,
  .type .land,
  .ability (.activated [.tapSymbol] (.addMana (.controller .this) [.colorless])),
  .ability (.activated
    [.mana [.x, .x], .tapSymbol, .sacrifice .this]
    (.createTokens (.controller .this) .x PredefinedToken.treasureToken))]

def treasureVault : CardDef :=
  treasureVaultDefinition.toCardDef (oracleText := treasureVaultOracle)

#guard treasureVault.types == #[.artifact, .land]
#guard treasureVault.manaCost == ManaCost.empty
#guard treasureVault.tapAddMana == #[.colorless]
#guard treasureVault.activatedAbilities == #[
  activated (Effect.abilityCreateTokensX .treasure) { symbols := #[.x, .x] }
    (tap := true) (sacrificeSource := true)]

/-- Oracle text for Aragorn and Arwen, Wed. -/
def aragornAndArwenWedOracle : String :=
  "Vigilance\nWhenever Aragorn and Arwen enters or attacks, put a +1/+1 counter on each other creature you control. You gain 1 life for each other creature you control."

def aragornAndArwenWedDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Aragorn and Arwen, Wed",
    .manaCost [.generic 4, .mono .green, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .human,
    .subtype .elf,
    .subtype .noble,
    .power 3,
    .toughness 6
  ] ++ (parseOracleParts (name := "Aragorn and Arwen, Wed") aragornAndArwenWedOracle).get!

#guard aragornAndArwenWedDefinition == (
  let others : Selector :=
    .intersection [
      .not .this,
      .permanent,
      .cardType .creature,
      .controlled (.controller .this)]

  .card [
    .name "Aragorn and Arwen, Wed",
    .manaCost [.generic 4, .mono .green, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .human,
    .subtype .elf,
    .subtype .noble,
    .power 3,
    .toughness 6,
    .ability (.keyword .vigilance),
    .ability
      (.triggered
        (.or (.enter .this) (.attack .this .all))
        (.sequence [
          .putCounter others .plusOnePlusOne 1,
          .forEachVariable 1 others [.gainLife (.controller .this) 1]]))])

def aragornAndArwenWed : CardDef :=
  aragornAndArwenWedDefinition.toCardDef (oracleText := aragornAndArwenWedOracle)

def minasTirith : CardDef :=
  legendaryLand "Minas Tirith"
    "Minas Tirith enters tapped unless you control a legendary creature.\n{T}: Add {W}.\n{1}{W}, {T}: Draw a card. Activate only if you attacked with two or more creatures this turn."
    (tapAddMana := #[.colored .white])
    (entersTappedUnlessLegendary := true)
    (activatedAbilities := #[
      activated (Effect.abilityDraw 1) (ManaCost.ofGenericAndColor 1 .white) (tap := true)
        (onlyIfYouAttackedWithTwoOrMore := true)])

def theShire : CardDef :=
  legendaryLand "The Shire"
    "The Shire enters tapped unless you control a legendary creature.\n{T}: Add {G}.\n{1}{G}, {T}, Tap an untapped creature you control: Create a Food token."
    (tapAddMana := #[.colored .green])
    (entersTappedUnlessLegendary := true)
    (activatedAbilities := #[
      activated (Effect.abilityCreateTokens .food 1) (ManaCost.ofGenericAndColor 1 .green)
        (tap := true) (tapAnUntappedCreatureYouControl := true)])

/-- Oracle text for Thranduil the Strategist. -/
def thranduilTheStrategistOracle : String :=
  "Other Elves you control have \"{T}: Add {G} or {U}.\"\nLandfall — Whenever a land you control enters, create a 1/1 green Elf creature token."

def thranduilTheStrategistDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Thranduil the Strategist",
    .manaCost [.generic 3, .mono .green, .mono .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .elf,
    .subtype .noble,
    .power 4,
    .toughness 4
  ] ++ (parseOracleParts (name := "Thranduil the Strategist") thranduilTheStrategistOracle).get!

#guard thranduilTheStrategistDefinition == .card [
  .name "Thranduil the Strategist",
  .manaCost [.generic 3, .mono .green, .mono .blue],
  .type .creature,
  .supertype .legendary,
  .subtype .elf,
  .subtype .noble,
  .power 4,
  .toughness 4,
  .ability
    (.static
      (.gainAbility
        (.intersection [.not .this, .permanent, .subtype .elf, .controlled (.controller .this)])
        (.activated
          [.tapSymbol]
          (.playerSelectAction
            (.controller .this)
            (.range (.nat 1) (.nat 1))
            [
              .addMana (.controller .this) [.mono .green],
              .addMana (.controller .this) [.mono .blue]])))),
  .ability
    (.triggered
      (.enter (.intersection [.permanent, .cardType .land, .controlled (.controller .this)]))
      (.createTokens
        (.controller .this)
        (.nat 1)
        [.type .creature, .subtype .elf, .colorIndicator [.green], .power 1, .toughness 1]
        []))]

def thranduilTheStrategist : CardDef :=
  thranduilTheStrategistDefinition.toCardDef (oracleText := thranduilTheStrategistOracle)

#guard thranduilTheStrategist.oracleText == thranduilTheStrategistOracle
#guard thranduilTheStrategist.staticAbilities == #[
      .otherSubtypeHaveTapAddOneOf #["Elf"] #[.colored .green, .colored .blue]]
#guard thranduilTheStrategist.triggeredAbilities == #[.onLandYouControlEntersCreateTokens .elf 1]

def moxAmber : CardDef :=
  artifact "Mox Amber" ManaCost.empty
    "{T}: Add one mana of any color among legendary creatures and planeswalkers you control."
    (supertypes := #[.legendary])
    (tapAddAnyColorAmongLegendaries := true)

/-- Oracle text for Fíli and Kíli, Joyous. -/
def filiAndKiliJoyousOracle : String :=
  "Haste\n{T}: Add {R}{R}. Spend this mana only to cast Dwarf, Equipment, and Saga spells."

def filiAndKiliJoyousDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Fíli and Kíli, Joyous",
    .manaCost [.generic 2, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .bard,
    .power 3,
    .toughness 3
  ] ++ (parseOracleParts (name := "Fíli and Kíli, Joyous") filiAndKiliJoyousOracle).get!

#guard filiAndKiliJoyousDefinition == .card [
  .name "Fíli and Kíli, Joyous",
  .manaCost [.generic 2, .mono .red],
  .type .creature,
  .supertype .legendary,
  .subtype .dwarf,
  .subtype .bard,
  .power 3,
  .toughness 3,
  .ability (.keyword .haste),
  .ability
    (.activated
      [.tapSymbol]
      (.sequence
        [
          .actionId 1 (.addMana (.controller .this) [.mono .red, .mono .red]),
          .continuous
            [
              .forbid
                (.spendManaCreatedByAction
                  1
                  (.not
                    (.castSpell
                      (.intersection
                        [.spell, .union [.subtype .dwarf, .subtype .equipment, .subtype .saga]]))))]
            .endOfTurn]))]

def filiAndKiliJoyous : CardDef :=
  filiAndKiliJoyousDefinition.toCardDef (oracleText := filiAndKiliJoyousOracle)

#guard filiAndKiliJoyous.oracleText == filiAndKiliJoyousOracle
#guard filiAndKiliJoyous.keywords == Keyword.haste
#guard filiAndKiliJoyous.tapAddRestricted == some (#[.colored .red, .colored .red],
      "Dwarf, Equipment, and Saga spells")

def arcaneSignet : CardDef :=
  artifact "Arcane Signet" (ManaCost.ofGeneric 2)
    "{T}: Add one mana of any color in your commander's color identity."
    (tapAddCommanderIdentity := true)

def theGaffer : CardDef :=
  legendaryCreature "The Gaffer" (ManaCost.ofGenericAndColor 2 .white)
    #["Halfling", "Peasant"] 2 3
    (oracleText := "At the beginning of each end step, if you gained 3 or more life this turn, draw a card.")
    (triggeredAbilities := #[.onEachEndStepDrawIfGainedLife 3])

def witchKingBringerOfRuin : CardDef :=
  legendaryCreature "Witch-king, Bringer of Ruin" (ManaCost.ofGenericAndColors 4 [.black, .black])
    #["Wraith", "Noble"] 5 3
    (oracleText := "Flying\nWhenever Witch-king attacks, defending player sacrifices a creature with the least power among creatures they control.")
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onAttackDefenderSacsLeastPower])

def necklaceOfGirion : CardDef :=
  artifact "Necklace of Girion" (ManaCost.ofGenericAndColor 2 .green)
    "Whenever you cast a green spell and whenever a Forest you control enters, put a +1/+1 counter on target creature you control.\n{T}: Add {G}."
    (supertypes := #[.legendary])
    (tapAddMana := #[.colored .green])
    (triggeredAbilities := #[.onCastGreenOrForestEntersPlusOne])

def sauronTheLidlessEye : CardDef :=
  legendaryCreature "Sauron, the Lidless Eye" (ManaCost.ofGenericAndColors 3 [.black, .red])
    #["Avatar", "Horror"] 4 4
    (oracleText := "When Sauron enters, gain control of target creature an opponent controls until end of turn. Untap it. It gains haste until end of turn.\n{1}{B}{R}: Creatures you control get +2/+0 until end of turn. Each opponent loses 2 life.")
    (triggeredAbilities := #[.onEnterGainControlOppUntilEot])
    (activatedAbilities := #[
      activated (Effect.creaturesYouControlGetOppsLoseLife 2 0 2)
        (ManaCost.ofGenericAndColors 1 [.black, .red])])

/-- Oracle text for Bolg, Erebor's Reckoning. -/
def bolgEreborsReckoningOracle : String :=
  "Trample\nAt the beginning of each combat, other Goblins and Orcs you control get +2/+2 until end of turn. Creatures your opponents control get -1/-1 until end of turn."

def bolgEreborsReckoningDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Bolg, Erebor's Reckoning",
    .manaCost [.generic 4, .mono .black, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .goblin,
    .subtype .soldier,
    .power 6,
    .toughness 6
  ] ++ (parseOracleParts (name := "Bolg, Erebor's Reckoning") bolgEreborsReckoningOracle).get!

#guard bolgEreborsReckoningDefinition == .card [
  .name "Bolg, Erebor's Reckoning",
  .manaCost [.generic 4, .mono .black, .mono .red],
  .type .creature,
  .supertype .legendary,
  .subtype .goblin,
  .subtype .soldier,
  .power 6,
  .toughness 6,
  .ability (.keyword .trample),
  .ability
    (.triggered
      (.combatStart .player)
      (.sequence
        [
          .continuous
            [
              .addPower
                (.intersection
                  [
                    .not .this,
                    .permanent,
                    .union [.subtype .goblin, .subtype .orc],
                    .controlled (.controller .this)])
                (.int 2),
              .addToughness
                (.intersection
                  [
                    .not .this,
                    .permanent,
                    .union [.subtype .goblin, .subtype .orc],
                    .controlled (.controller .this)])
                (.int 2)]
            .endOfTurn,
          .continuous
            [
              .addPower
                (.intersection
                  [.permanent, .cardType .creature, .controlled (.opponent (.controller .this))])
                (.int (-1)),
              .addToughness
                (.intersection
                  [.permanent, .cardType .creature, .controlled (.opponent (.controller .this))])
                (.int (-1))]
            .endOfTurn]))]

def bolgEreborsReckoning : CardDef :=
  bolgEreborsReckoningDefinition.toCardDef (oracleText := bolgEreborsReckoningOracle)

#guard bolgEreborsReckoning.oracleText == bolgEreborsReckoningOracle
#guard bolgEreborsReckoning.keywords == Keyword.trample
#guard bolgEreborsReckoning.triggeredAbilities == #[.onEachCombatOthersGetAndOppsGet #["Goblin", "Orc"] 2 2 (-1) (-1)]

/-- Oracle text for Thorin, King of Durin's Folk. -/
def thorinKingOfDurinsFolkOracle : String :=
  "Whenever Thorin or another Dwarf you control enters, create a Treasure token.\nOther Dwarves you control get +1/+0 for each artifact token you control."

def thorinKingOfDurinsFolkDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Thorin, King of Durin's Folk",
    .manaCost [.generic 3, .mono .red, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .noble,
    .power 4,
    .toughness 4
  ] ++ (parseOracleParts (name := "Thorin, King of Durin's Folk") thorinKingOfDurinsFolkOracle).get!

#guard thorinKingOfDurinsFolkDefinition == (
  let otherDwarves : Selector :=
    .intersection [
      .not .this,
      .permanent,
      .cardType .creature,
      .subtype .dwarf,
      .controlled (.controller .this)]
  let artifactTokens : Selector :=
    .intersection [
      .permanent,
      .cardType .artifact,
      .token,
      .controlled (.controller .this)]

  .card [
    .name "Thorin, King of Durin's Folk",
    .manaCost [.generic 3, .mono .red, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .noble,
    .power 4,
    .toughness 4,
    .ability
      (.triggered
        (.or
          (.enter .this)
          (.enter otherDwarves))
        (.createTokens (.controller .this) 1 PredefinedToken.treasureToken)),
    .ability
      (.static
        (.addPower otherDwarves (Value.count artifactTokens)))])

def thorinKingOfDurinsFolk : CardDef :=
  thorinKingOfDurinsFolkDefinition.toCardDef (oracleText := thorinKingOfDurinsFolkOracle)

def bilboUnexpectedAdventurer : CardDef :=
  legendaryCreature "Bilbo, Unexpected Adventurer" (ManaCost.ofGenericAndColor 3 .white)
    #["Halfling", "Rogue"] 2 2
    (oracleText := "Bilbo can't be blocked by creatures with power 3 or greater.\nWhenever Bilbo deals combat damage to a player or battle, put up to one target nonland permanent card with mana value 3 or less from a graveyard onto the battlefield under its owner's control.")
    (staticAbilities := #[.cantBeBlockedByPowerAtLeast 3])
    (triggeredAbilities := #[.onCombatDamagePutNonlandMvAtMost 3])

/-- Oracle text for Andúril, Flame of the West. -/
def andurilFlameOfTheWestOracle : String :=
  "Equipped creature gets +3/+1.\nWhenever equipped creature attacks, create two tapped 1/1 white Spirit creature tokens with flying. If that creature is legendary, instead create two of those tokens that are tapped and attacking.\nEquip {2}"

def andurilFlameOfTheWestDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Andúril, Flame of the West",
    .manaCost [.generic 3],
    .type .artifact,
    .supertype .legendary,
    .subtype .equipment
  ] ++ (parseOracleParts (name := "Andúril, Flame of the West") andurilFlameOfTheWestOracle).get!

#guard andurilFlameOfTheWestDefinition == (
  let spirits : List CardPart := [
    .type .creature, .subtype .spirit, .colorIndicator [.white], .power 1, .toughness 1,
    .ability (.keyword .flying)]

  .card [
    .name "Andúril, Flame of the West",
    .manaCost [.generic 3],
    .type .artifact,
    .supertype .legendary,
    .subtype .equipment,
    .ability (.static (.addPower (.hostOf .this) (Value.int 3))),
    .ability (.static (.addToughness (.hostOf .this) (Value.int 1))),
    .ability (
      .triggered
        (.attack (.hostOf .this) .all)
        (.ifElse
          (.any (.intersection [.hostOf .this, .supertype .legendary]))
          [.createTokens (.controller .this) 2 spirits [.tapped, .attacking]]
          [.createTokens (.controller .this) 2 spirits [.tapped]])),
    .ability (.keywordWithCost .equip [.mana [.generic 2]])])

def andurilFlameOfTheWest : CardDef :=
  andurilFlameOfTheWestDefinition.toCardDef (oracleText := andurilFlameOfTheWestOracle)

def andurilNarsilReforged : CardDef :=
  artifact "Andúril, Narsil Reforged" (ManaCost.ofGeneric 2) "Ascend (If you control ten or more permanents, you get the city's blessing for the rest of the game.)\nWhenever equipped creature attacks, put a +1/+1 counter on each creature you control. If you have the city's blessing, put two +1/+1 counters on each creature you control instead.\nEquip {3}"
    (subtypes := #["Equipment"])
    (supertypes := #[.legendary])
    (keywords := Keyword.ascend)
    (triggeredAbilities := #[.onEquippedAttacksPlusOneEachIfCityBlessing])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 3)])

def aragornTheUniter : CardDef :=
  legendaryCreature "Aragorn, the Uniter" (ManaCost.ofColors [.red, .green, .white, .blue]) #["Human", "Noble"] 5 5 (oracleText := "Whenever you cast a white spell, create a 1/1 white Human Soldier creature token.\nWhenever you cast a blue spell, scry 2.\nWhenever you cast a red spell, Aragorn deals 3 damage to target opponent.\nWhenever you cast a green spell, target creature gets +4/+4 until end of turn.")
    (triggeredAbilities := #[.onCastColorCreateTokens .white .humanSoldier 1,
      .onCastColorScry .blue 2,
      .onCastColorDamageOpponent .red 3,
      .onCastColorPump .green 4 4])

def arwenMortalQueen : CardDef :=
  let c :=
    legendaryCreature "Arwen, Mortal Queen" (ManaCost.ofGenericAndColors 1 [.green, .white]) #["Elf", "Noble"] 2 2 (oracleText := "Arwen enters with an indestructible counter on her.\n{1}, Remove an indestructible counter from Arwen: Another target creature gains indestructible until end of turn. Put a +1/+1 counter and a lifelink counter on that creature and a +1/+1 counter and a lifelink counter on Arwen.")
      (activatedAbilities := #[
        activated (Effect.arwenShare) (ManaCost.ofGeneric 1) (removeIndestructibleCounter := true)])
  { c with entersWithIndestructibleCounter := true }

def arwenWeaverOfHope : CardDef :=
  legendaryCreature "Arwen, Weaver of Hope" (ManaCost.ofGenericAndColors 1 [.green, .green]) #["Elf", "Noble"] 2 1 (oracleText := "Each other creature you control enters with a number of additional +1/+1 counters on it equal to Arwen's toughness.")
    (othersEnterWithPlusOneEqualToughness := true)

def bilboSBurglaring : CardDef :=
  sorcery "Bilbo's Burglaring" (ManaCost.ofGenericAndColors 4 [.blue, .blue]) "For each opponent, gain control of up to one target artifact that player controls." (some (Effect.gainControlOppArtifacts))

def bilboSRing : CardDef :=
  artifact "Bilbo's Ring" (ManaCost.ofGeneric 3) "During your turn, equipped creature has hexproof and can't be blocked.\nWhenever equipped creature attacks alone, you draw a card and you lose 1 life.\nEquip Halfling {1} ({1}: Attach to target Halfling you control. Equip only as a sorcery.)\nEquip {4} ({4}: Attach to target creature you control. Equip only as a sorcery.)"
    (subtypes := #["Equipment"])
    (supertypes := #[.legendary])
    (staticAbilities := #[.equippedHexproofUnblockableDuringYourTurn])
    (triggeredAbilities := #[.onEquippedAttacksAloneDrawLoseLife])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 1) (subtype := some "Halfling"),
      equipAbility (ManaCost.ofGeneric 4)])

def bilboFellowConspirator : CardDef :=
  legendaryCreature "Bilbo, Fellow Conspirator" (ManaCost.ofGenericAndColor 2 .green) #["Halfling", "Citizen"] 2 3 (oracleText := "If you would create a Food token, instead create a Food token and a Treasure token.")
    (foodAlsoCreatesTreasure := true)

def callForthTheTempest : CardDef :=
  sorcery "Call Forth the Tempest" (ManaCost.ofGenericAndColors 5 [.red, .red, .red]) "Cascade, cascade (When you cast this spell, exile cards from the top of your library until you exile a nonland card that costs less. You may cast it without paying its mana cost. Put the exiled cards on the bottom of your library in a random order. Then do it again.)\nCall Forth the Tempest deals damage to each creature your opponents control equal to the total mana value of other spells you've cast this turn." (some (Effect.damageOppCreaturesEqualOtherSpellsMv))
    (cascade := 2)

def cavernHoardDragon : CardDef :=
  creature "Cavern-Hoard Dragon" (ManaCost.ofGenericAndColors 7 [.red, .red]) #["Dragon"] 6 6 (oracleText := "This spell costs {X} less to cast, where X is the greatest number of artifacts an opponent controls.\nFlying, trample, haste\nWhenever this creature deals combat damage to a player, you create a Treasure token for each artifact that player controls.")
    (costReductionEqualOppArtifacts := true)
    (keywords := Keywords.mergeAll #[Keyword.flying, Keyword.trample, Keyword.haste])
    (triggeredAbilities := #[.onCombatDamageCreateTreasuresEqualPlayerArtifacts])

def chiefOfTheWilds : CardDef :=
  legendaryCreature "Chief of the Wilds" (ManaCost.ofGenericAndColors 2 [.black, .green]) #["Wolf"] 4 4 (oracleText := "Menace\nWhenever another Wolf you control enters, put two +1/+1 counters on Chief of the Wilds.\nIf a triggered ability of another Wolf or battle you control triggers, that ability triggers an additional time.")
    (keywords := Keyword.menace)
    (staticAbilities := #[.extraTriggerAnotherYouControl #["Wolf"] true])
    (triggeredAbilities := #[.onAnotherSubtypeEntersPlusOneOnSource "Wolf" 2])

/-- Oracle text for Dragon-Cursed Halls. -/
def dragonCursedHallsOracle : String :=
  "{T}: Add {C}.\n{1}, {T}: Until end of turn, target creature gains \"Whenever this creature deals combat damage to a player, create a Treasure token.\""

def dragonCursedHallsDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Dragon-Cursed Halls",
    .type .land
  ] ++ (parseOracleParts (name := "Dragon-Cursed Halls") dragonCursedHallsOracle).get!

#guard dragonCursedHallsDefinition == .card [
  .name "Dragon-Cursed Halls",
  .type .land,
  .ability
    (.activated
      [.tapSymbol]
      (.addMana (.controller .this) [.colorless])),
  .ability
    (.activated
      [.mana [.generic 1], .tapSymbol]
      (.continuous
        [
          .gainAbility
            (.target 1 (.intersection [.permanent, .cardType .creature]))
            (.triggered
              (.combatDamage .this .player)
              (.createTokens (.controller .this) 1 PredefinedToken.treasureToken))]
        .endOfTurn))]

def dragonCursedHalls : CardDef :=
  dragonCursedHallsDefinition.toCardDef (oracleText := dragonCursedHallsOracle)

def elvenChorus : CardDef :=
  let c :=
    enchantment "Elven Chorus" (ManaCost.ofGenericAndColor 3 .green) "You may look at the top card of your library any time.\nYou may cast creature spells from the top of your library.\nCreatures you control have \"{T}: Add one mana of any color.\""
  { c with
    mayLookAtTopAnytime := true
    mayCastCreaturesFromTop := true
    grantCreaturesTapAddAnyColor := true }

def galadrielSDismissal : CardDef :=
  instant "Galadriel's Dismissal" (ManaCost.ofColor .white) "Kicker {2}{W} (You may pay an additional {2}{W} as you cast this spell.)\nTarget creature phases out. If this spell was kicked, each creature target player controls phases out instead. (Treat phased-out creatures and anything attached to them as though they don't exist until their controller's next turn.)" (some (Effect.phaseOutKicker))
    (kicker := some (ManaCost.ofGenericAndColor 2 .white))

/-- Oracle text for Galadriel, Light of Valinor. -/
def galadrielLightOfValinorOracle : String :=
  "Alliance — Whenever another creature you control enters, choose one that hasn't been chosen this turn —\n• Add {G}{G}{G}.\n• Put a +1/+1 counter on each creature you control.\n• Scry 2, then draw a card."

def galadrielLightOfValinorDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Galadriel, Light of Valinor",
    .manaCost [.generic 2, .mono .green, .mono .white, .mono .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .elf,
    .subtype .noble,
    .power 3,
    .toughness 3
  ] ++ (parseOracleParts (name := "Galadriel, Light of Valinor") galadrielLightOfValinorOracle).get!

#guard galadrielLightOfValinorDefinition == (
  let you : Selector := .controller .this
  let unchosen (id : Nat) : Condition :=
    .didNotHappen (.modeWithIdChosen .player id) .turnStart

  .card [
    .name "Galadriel, Light of Valinor",
    .manaCost [.generic 2, .mono .green, .mono .white, .mono .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .elf,
    .subtype .noble,
    .power 3,
    .toughness 3,
    .ability
      (.triggered
        (.enter
          (.intersection [
            .not .this,
            .permanent,
            .cardType .creature,
            .controlled you]))
        (.chooseModeRestricted you [
          (1, unchosen 1,
            [.addMana you [.mono .green, .mono .green, .mono .green]]),
          (2, unchosen 2,
            [.putCounter
              (.intersection [
                .permanent,
                .cardType .creature,
                .controlled you])
              .plusOnePlusOne
              1]),
          (3, unchosen 3,
            [.sequence [.scry you 2, .draw you 1]])]))])

def galadrielLightOfValinor : CardDef :=
  galadrielLightOfValinorDefinition.toCardDef (oracleText := galadrielLightOfValinorOracle)

def gandalfPartyGuest : CardDef :=
  legendaryCreature "Gandalf, Party Guest" (ManaCost.ofGenericAndColors 1 [.blue, .red, .white]) #["Avatar", "Wizard"] 3 4 (oracleText := "At the beginning of combat on your turn, you may cast an instant or sorcery spell with mana value X or less from your hand without paying its mana cost, where X is twice the number of legendary Wizards you control.")
    (triggeredAbilities := #[.onYourBeginCombatCastInstantSorceryFromHand])

/-- Oracle text for Gandalf, Shadow's Foe. -/
def gandalfShadowSFoeOracle : String :=
  "Vigilance\nWhen Gandalf enters, exile up to three target lands you control, then return them to the battlefield tapped under their owner's control.\nLandfall — Whenever a land you control enters, draw a card and put a +1/+1 counter on Gandalf."

def gandalfShadowSFoeDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Gandalf, Shadow's Foe",
    .manaCost [.generic 5, .mono .blue, .mono .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .avatar,
    .subtype .wizard,
    .power 3,
    .toughness 4
  ] ++ (parseOracleParts (name := "Gandalf, Shadow's Foe") gandalfShadowSFoeOracle).get!

#guard gandalfShadowSFoeDefinition == .card [
  .name "Gandalf, Shadow's Foe",
  .manaCost [.generic 5, .mono .blue, .mono .blue],
  .type .creature,
  .supertype .legendary,
  .subtype .avatar,
  .subtype .wizard,
  .power 3,
  .toughness 4,
  .ability (.keyword .vigilance),
  .ability (
    .triggered
      (.enter .this)
      (.sequence [
        .actionId 1
          (.exile
            (.targets
              1
              (.range 0 3)
              (.intersection [
                .permanent,
                .cardType .land,
                .controlled (.controller .this)]))),
        .putOntoBattlefieldInState
          (.wasCreatedByAction 1)
          [
            .tapped,
            .controlled (.owner (.wasCreatedByAction 1))]])),
  .ability (
    .triggered
      (.enter
        (.intersection [
          .permanent,
          .cardType .land,
          .controlled (.controller .this)]))
      (.sequence [
        .draw (.controller .this) 1,
        .putCounter (.source .this) .plusOnePlusOne 1]))]

def gandalfShadowSFoe : CardDef :=
  gandalfShadowSFoeDefinition.toCardDef (oracleText := gandalfShadowSFoeOracle)

def glamdring : CardDef :=
  artifact "Glamdring" (ManaCost.ofGeneric 2) "Equipped creature has first strike and gets +1/+0 for each instant and sorcery card in your graveyard.\nWhenever equipped creature deals combat damage to a player, you may cast an instant or sorcery spell from your hand with mana value less than or equal to that damage without paying its mana cost.\nEquip {3}"
    (subtypes := #["Equipment"])
    (supertypes := #[.legendary])
    (staticAbilities := #[.equippedFirstStrikePlusPerInstantSorcery])
    (triggeredAbilities := #[.onEquippedCombatDamageCastInstantSorcery])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 3)])

def grimaSarumanSFootman : CardDef :=
  legendaryCreature "Gríma, Saruman's Footman" (ManaCost.ofGenericAndColors 2 [.blue, .black]) #["Human", "Advisor"] 1 4 (oracleText := "Gríma can't be blocked.\nWhenever Gríma deals combat damage to a player, that player exiles cards from the top of their library until they exile an instant or sorcery card. You may cast that card without paying its mana cost. Then that player puts the exiled cards that weren't cast this way on the bottom of their library in a random order.")
    (keywords := { Keywords.none with cantBeBlocked := true })
    (triggeredAbilities := #[.onCombatDamageImpulseInstantSorcery])

def minasMorgulDarkFortress : CardDef :=
  legendaryLand "Minas Morgul, Dark Fortress" "Minas Morgul enters tapped.\n{T}: Add {B}.\n{3}{B}, {T}: Put a shadow counter on target creature. For as long as that creature has a shadow counter on it, it's a Wraith in addition to its other types. (A creature with shadow can block or be blocked by only creatures with shadow.)"
    (entersTapped := true)
    (tapAddMana := #[.colored .black])
    (activatedAbilities := #[
      activated (Effect.putShadowCounter) (ManaCost.ofGenericAndColor 3 .black) (tap := true)])

/-- Oracle text for Mount Doom. -/
def mountDoomOracle : String :=
  "{T}, Pay 1 life: Add {B} or {R}.\n{1}{B}{R}, {T}: Mount Doom deals 1 damage to each opponent.\n{5}{B}{R}, {T}, Sacrifice Mount Doom and a legendary artifact: Choose up to two creatures, then destroy the rest. Activate only as a sorcery."

def mountDoomDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Mount Doom",
    .type .land,
    .supertype .legendary
  ] ++ (parseOracleParts (name := "Mount Doom") mountDoomOracle).get!

#guard mountDoomDefinition == .card [
  .name "Mount Doom",
  .type .land,
  .supertype .legendary,
  .ability
    (.activated
      [.tapSymbol, .life 1]
      (.playerSelectAction
        (.controller .this)
        (.range (.nat 1) (.nat 1))
        [.addMana (.controller .this) [.mono .black], .addMana (.controller .this) [.mono .red]])),
  .ability
    (.activated
      [.mana [.generic 1, .mono .black, .mono .red], .tapSymbol]
      (.dealDamage .this (.opponent (.controller .this)) (.nat 1))),
  .ability
    (.activatedIf
      (.timeToCastSorcery (.controller .this))
      [
        .mana [.generic 5, .mono .black, .mono .red],
        .tapSymbol,
        .sacrifice .this,
        .sacrificeCount (.intersection [.permanent, .cardType .artifact, .supertype .legendary]) 1]
      (.sequence
        [
          .defineSelectorVariable
            1
            (.selected
              (.controller .this)
              (.range (.nat 0) (.nat 2))
              (.intersection [.permanent, .cardType .creature])),
          .destroy (.intersection [.permanent, .cardType .creature, .not (.variable 1)])]))]

def mountDoom : CardDef :=
  mountDoomDefinition.toCardDef (oracleText := mountDoomOracle)

#guard mountDoom.oracleText == mountDoomOracle
#guard mountDoom.tapPayLifeAddOneOf == some (1, #[.colored .black, .colored .red])
#guard mountDoom.activatedAbilities == #[
      activated (Effect.damageEachOpponent 1) (ManaCost.ofGenericAndColors 1 [.black, .red]) (tap := true),
      activated (Effect.chooseTwoDestroyRest) (ManaCost.ofGenericAndColors 5 [.black, .red])
        (tap := true) (sacrificeSource := true) (sacrificeLegendaryArtifact := true)
        (onlyAsSorcery := true)]

def orcishBowmasters : CardDef :=
  creature "Orcish Bowmasters" (ManaCost.ofGenericAndColor 1 .black) #["Orc", "Archer"] 1 1 (oracleText := "Flash\nWhen this creature enters and whenever an opponent draws a card except the first one they draw in each of their draw steps, this creature deals 1 damage to any target. Then amass Orcs 1.")
    (keywords := Keyword.flash)
    (triggeredAbilities := #[.onEnterOrOpponentDrawsDeal1AmassOrcs])

def palantirOfOrthanc : CardDef :=
  artifact "Palantír of Orthanc" (ManaCost.ofGeneric 3) "At the beginning of your end step, put an influence counter on Palantír of Orthanc and scry 2. Then target opponent may have you draw a card. If that player doesn't, you mill X cards, where X is the number of influence counters on Palantír of Orthanc, and that player loses life equal to the total mana value of those cards."
    (supertypes := #[.legendary])
    (triggeredAbilities := #[.onYourEndStepPalantir])

def sarumanOfManyColors : CardDef :=
  legendaryCreature "Saruman of Many Colors" (ManaCost.ofGenericAndColors 3 [.white, .blue, .black]) #["Avatar", "Wizard"] 5 4 (oracleText := "Ward—Discard an enchantment, instant, or sorcery card.\nWhenever you cast your second spell each turn, each opponent mills two cards. When one or more cards are milled this way, exile target enchantment, instant, or sorcery card with equal or lesser mana value than that spell from an opponent's graveyard. Copy the exiled card. You may cast the copy without paying its mana cost.")
    (staticAbilities := #[.wardDiscardEnchantmentInstantOrSorcery])
    (triggeredAbilities := #[.onCastSecondSpellMillThenCopy])

def sauronTheDarkLord : CardDef :=
  legendaryCreature "Sauron, the Dark Lord" (ManaCost.ofGenericAndColors 3 [.blue, .black, .red]) #["Avatar", "Horror"] 7 6 (oracleText := "Ward—Sacrifice a legendary artifact or legendary creature.\nWhenever an opponent casts a spell, amass Orcs 1.\nWhenever an Army you control deals combat damage to a player, the Ring tempts you.\nWhenever the Ring tempts you, you may discard your hand. If you do, draw four cards.")
    (staticAbilities := #[.wardSacrificeLegendary])
    (triggeredAbilities := #[.onOpponentCastsAmassOrcs 1,
      .onArmyCombatDamageRingTempts,
      .onRingTemptsMayDiscardDraw 4])

def smaugTheImpenetrable : CardDef :=
  legendaryCreature "Smaug the Impenetrable" (ManaCost.ofGenericAndColors 5 [.black, .red]) #["Dragon"] 8 7 (oracleText := "Flying, indestructible, haste\nWhenever Smaug is dealt noncombat damage, create that many Treasure tokens.")
    (keywords := Keywords.mergeAll #[Keyword.flying, Keyword.indestructible, Keyword.haste])
    (triggeredAbilities := #[.onDealtNoncombatDamageCreateTreasures])

def theBlackGate : CardDef :=
  legendaryLand "The Black Gate" "As The Black Gate enters, you may pay 3 life. If you don't, it enters tapped.\n{T}: Add {B}.\n{1}{B}, {T}: Choose a player with the most life or tied for most life. Target creature can't be blocked by creatures that player controls this turn."
    (entersTappedUnlessPayLife := some 3)
    (tapAddMana := #[.colored .black])
    (subtypes := #["Gate"])
    (activatedAbilities := #[
      activated (Effect.blackGateUnblockable) (ManaCost.ofGenericAndColor 1 .black) (tap := true)])

def theOneRing : CardDef :=
  artifact "The One Ring" (ManaCost.ofGeneric 4) "Indestructible\nWhen The One Ring enters, if you cast it, you gain protection from everything until your next turn.\nAt the beginning of your upkeep, you lose 1 life for each burden counter on The One Ring.\n{T}: Put a burden counter on The One Ring, then draw a card for each burden counter on The One Ring."
    (supertypes := #[.legendary])
    (keywords := Keyword.indestructible)
    (activatedAbilities := #[activated (Effect.burdenThenDraw) (tap := true)])
    (triggeredAbilities := #[.onEnterIfCastProtectionEverything,
      .onYourUpkeepLoseLifePerBurden])

def theReaverCleaver : CardDef :=
  artifact "The Reaver Cleaver" (ManaCost.ofGenericAndColor 2 .red) "Equipped creature gets +1/+1 and has trample and \"Whenever this creature deals combat damage to a player or planeswalker, create that many Treasure tokens.\"\nEquip {3}"
    (subtypes := #["Equipment"])
    (supertypes := #[.legendary])
    (staticAbilities := #[.equippedGetsTrampleAndCombatTreasures 1 1])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 3)])

/-- Oracle text for Thorin, Company's Leader. -/
def thorinCompanySLeaderOracle : String :=
  "Whenever a Dwarf you control deals combat damage to a player or battle, create two Treasure tokens.\n{10}: Creatures you control gain double strike until end of turn."

def thorinCompanySLeaderDefinition : TraditionalCardDefinition := .card <|
  [
    .name "Thorin, Company's Leader",
    .manaCost [.generic 4, .mono .red],
    .type .creature,
    .supertype .legendary,
    .subtype .dwarf,
    .subtype .warrior,
    .power 4,
    .toughness 5
  ] ++ (parseOracleParts (name := "Thorin, Company's Leader") thorinCompanySLeaderOracle).get!

#guard thorinCompanySLeaderDefinition == .card [
  .name "Thorin, Company's Leader",
  .manaCost [.generic 4, .mono .red],
  .type .creature,
  .supertype .legendary,
  .subtype .dwarf,
  .subtype .warrior,
  .power 4,
  .toughness 5,
  .ability (
    .triggered
      (.combatDamage
        (.intersection [
          .permanent,
          .cardType .creature,
          .subtype .dwarf,
          .controlled (.controller .this)])
        (.union [.player, .cardType .battle]))
      (.createTokens (.controller .this) 2 PredefinedToken.treasureToken)),
  .ability (
    .activated
      [.mana [.generic 10]]
      (.continuous
        [
          .gainAbility
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)])
            (.keyword .doubleStrike)]
        .endOfTurn))]

def thorinCompanySLeader : CardDef :=
  thorinCompanySLeaderDefinition.toCardDef (oracleText := thorinCompanySLeaderOracle)

def tomBombadil : CardDef :=
  let c :=
    legendaryCreature "Tom Bombadil" (ManaCost.ofColors [.white, .blue, .black, .red, .green]) #["God", "Bard"] 4 4 (oracleText := "As long as there are four or more lore counters among Sagas you control, Tom Bombadil has hexproof and indestructible.\nWhenever the final chapter ability of a Saga you control resolves, reveal cards from the top of your library until you reveal a Saga card. Put that card onto the battlefield and the rest on the bottom of your library in a random order. This ability triggers only once each turn.")
      (triggeredAbilities := #[.onFinalSagaChapterRevealSaga])
  { c with hexproofIndestructibleIfLore := some 4 }

def witchKingOfAngmar : CardDef :=
  legendaryCreature "Witch-king of Angmar" (ManaCost.ofGenericAndColors 3 [.black, .black]) #["Wraith", "Noble"] 5 3 (oracleText := "Flying\nWhenever one or more creatures deal combat damage to you, each opponent sacrifices a creature of their choice that dealt combat damage to you this turn. The Ring tempts you.\nDiscard a card: Witch-king of Angmar gains indestructible until end of turn. Tap him.")
    (keywords := Keyword.flying)
    (activatedAbilities := #[
      activated (Effect.sourceGainsIndestructibleTap) (discardACard := true)])
    (triggeredAbilities := #[.onCombatDamageToYouSacRingTempts])

/-- Every unique card in The Hobbit Eternal (HOC), including reprints
that also appear in other sets. -/
def hobbitEternalCards : Array CardDef := #[
  mentorOfTheMeek,
  fiendHunter,
  errandRiderOfGondor,
  landrovalHorizonWitness,
  roguesPassage,
  soldierOfTheGreyHost,
  eaglesOfTheNorth,
  dunedainBlade,
  fogOnTheBarrowDowns,
  banishingLight,
  dawnOfANewAge,
  westfoldRider,
  esquireOfTheKing,
  pelargirSurvivor,
  lorienRevealed,
  knightsOfDolAmroth,
  greyHavensNavigator,
  ithilienKingfisher,
  hithlainKnots,
  captainOfUmbar,
  minasTirithGarrison,
  colossalWhale,
  willowWind,
  nimrodelWatcher,
  sternScolding,
  hauntOfTheDeadMarshes,
  languish,
  shadowOfTheEnemy,
  trollOfKhazadDum,
  mercilessExecutioner,
  bitterDownfall,
  nightsWhisper,
  wayfarersBauble,
  battleScarredGoblin,
  improvisedClub,
  ologHaiCrusher,
  smiteTheDeathless,
  goblinFireleaper,
  oliphaunt,
  goblinCratermaker,
  infernoTitan,
  guttersnipe,
  orcishSiegemaster,
  fireOfOrthanc,
  galadhrimGuide,
  elvishVisionary,
  mirkwoodElk,
  celebornTheWise,
  giftOfStrands,
  elvishArchdruid,
  lothlorienLookout,
  elvishMystic,
  bardHeirOfGirion,
  reprieve,
  greatGoblinFoulHearted,
  dwarvenWarriors,
  bagEndBanquet,
  floweringOfTheWhiteTree,
  mithrilCoat,
  rivendell,
  delightedHalfling,
  relicOfSauron,
  longLostLances,
  lothoCorruptShirriff,
  flameOfAnor,
  lastMarchOfTheEnts,
  raiseThePalisade,
  dragonsDesire,
  oriPlateStacker,
  dainOfTheAncientHalls,
  treasureVault,
  aragornAndArwenWed,
  minasTirith,
  theShire,
  thranduilTheStrategist,
  moxAmber,
  filiAndKiliJoyous,
  arcaneSignet,
  theGaffer,
  witchKingBringerOfRuin,
  necklaceOfGirion,
  sauronTheLidlessEye,
  bolgEreborsReckoning,
  thorinKingOfDurinsFolk,
  bilboUnexpectedAdventurer,
  andurilFlameOfTheWest,
  andurilNarsilReforged,
  aragornTheUniter,
  arwenMortalQueen,
  arwenWeaverOfHope,
  bilboSBurglaring,
  bilboSRing,
  bilboFellowConspirator,
  callForthTheTempest,
  cavernHoardDragon,
  chiefOfTheWilds,
  dragonCursedHalls,
  elvenChorus,
  galadrielSDismissal,
  galadrielLightOfValinor,
  gandalfPartyGuest,
  gandalfShadowSFoe,
  glamdring,
  grimaSarumanSFootman,
  minasMorgulDarkFortress,
  mountDoom,
  orcishBowmasters,
  palantirOfOrthanc,
  sarumanOfManyColors,
  sauronTheDarkLord,
  smaugTheImpenetrable,
  theBlackGate,
  theOneRing,
  theReaverCleaver,
  thorinCompanySLeader,
  tomBombadil,
  witchKingOfAngmar
]

#guard roguesPassage.isLand
#guard roguesPassage.activatedAbilities.size == 1
#guard roguesPassage.activatedAbilities[0]!.effect == Effect.targetCantBeBlockedThisTurn
#guard roguesPassage.activatedAbilities[0]!.cost.tap
#guard roguesPassage.activatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 4)
#guard roguesPassage.tapAddMana == #[.colorless]
#guard elvishMystic.tapAddMana == #[.colored .green]
#guard (wayfarersBauble.summary.splitOn "Search your library").length > 1
#guard wayfarersBauble.activatedAbilities.size == 1
#guard wayfarersBauble.activatedAbilities[0]!.effect == Effect.searchBasicLandTapped
#guard wayfarersBauble.activatedAbilities[0]!.cost.tap
#guard wayfarersBauble.activatedAbilities[0]!.cost.sacrificeSource
#guard wayfarersBauble.activatedAbilities[0]!.cost.mana == ManaCost.ofGeneric 2
#guard (roguesPassage.summary.splitOn "can't be blocked").length > 1
#guard orcishSiegemaster.keywords.trample
#guard orcishSiegemaster.staticAbilities == #[.otherCreaturesHaveTrample #["Orc", "Goblin"]]
#guard orcishSiegemaster.triggeredAbilities == #[.onAttackPumpByGreatestPower]
#guard (orcishSiegemaster.summary.splitOn "Other Orcs and Goblins").length > 1
#guard battleScarredGoblin.triggeredAbilities == #[.onBecomesBlockedDeal1ToBlockers]
#guard (battleScarredGoblin.summary.splitOn "becomes blocked").length > 1
#guard giftOfStrands.isAura
#guard giftOfStrands.keywords.flash
#guard !giftOfStrands.hasSorcerySpeed
#guard giftOfStrands.hasInstantSpeed
#guard giftOfStrands.requiresTarget
#guard giftOfStrands.staticAbilities == #[.enchantedCreatureGets 3 3]
#guard giftOfStrands.triggeredAbilities == #[.onEnterScry 2]
#guard dunedainBlade.activatedAbilities.size == 2
#guard dunedainBlade.activatedAbilities[0]!.equipSubtype == some "Human"
#guard dunedainBlade.activatedAbilities[1]!.equipSubtype == none
#guard dunedainBlade.activatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 1)
#guard dunedainBlade.activatedAbilities[1]!.cost.mana == (ManaCost.ofGeneric 3)
#guard (giftOfStrands.summary.splitOn "flash").length > 1
#guard (giftOfStrands.summary.splitOn "Enchanted creature").length > 1
#guard galadhrimGuide.triggeredAbilities == #[.onEnterScry 2]
#guard (galadhrimGuide.summary.splitOn "scry 2").length > 1
#guard elvishVisionary.triggeredAbilities == #[.onEnterDraw 1]
#guard (elvishVisionary.summary.splitOn "draw a card").length > 1
#guard elvishVisionary.hasSubtype "Elf"
#guard elvishVisionary.hasSubtype "Shaman"
#guard knightsOfDolAmroth.triggeredAbilities == #[.onDrawSecondPlusOne]
#guard knightsOfDolAmroth.hasSubtype "Knight"
#guard elvishArchdruid.staticAbilities == #[.otherCreaturesGet #["Elf"] 1 1]
#guard elvishArchdruid.tapAddManaForEach == #[{ mana := .colored .green, subtype := "Elf" }]
#guard elvishArchdruid.manaAbilities == #[.colored .green]
#guard (elvishArchdruid.summary.splitOn "Other Elf creatures").length > 1
#guard (elvishArchdruid.summary.splitOn "for each Elf").length > 1
#guard mirkwoodElk.keywords.trample
#guard mirkwoodElk.triggeredAbilities == #[.onEnterOrAttackReturnElfGainLife]
#guard mirkwoodElk.power == some 6
#guard mirkwoodElk.toughness == some 6
#guard (mirkwoodElk.summary.splitOn "trample").length > 1
#guard (mirkwoodElk.summary.splitOn "Elf card").length > 1
#guard celebornTheWise.triggeredAbilities ==
  #[.onAttackWithElvesScry 1, .onScryPumpSelfForEachLookedAt]
#guard celebornTheWise.power == some 3
#guard celebornTheWise.toughness == some 3
#guard celebornTheWise.subtypes.any (· == "Elf")
#guard (celebornTheWise.summary.splitOn "one or more Elves").length > 1
#guard (celebornTheWise.summary.splitOn "looked at").length > 1
#guard lothlorienLookout.triggeredAbilities == #[.onAttackScry 1]
#guard (lothlorienLookout.summary.splitOn "scry 1").length > 1
#guard lothlorienLookout.power == some 1
#guard lothlorienLookout.toughness == some 3
#guard galadhrimGuide.power == some 3
#guard galadhrimGuide.toughness == some 4
#guard goblinCratermaker.activatedAbilities.size == 1
#guard goblinCratermaker.activatedAbilities[0]!.cost.sacrificeSource
#guard goblinCratermaker.activatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 1)
#guard goblinCratermaker.activatedAbilities[0]!.isModal
#guard goblinCratermaker.activatedAbilities[0]!.effect == Effect.dealDamageToTargetCreature 2
#guard goblinCratermaker.activatedAbilities[0]!.otherModes ==
  #[Effect.destroyTargetColorlessNonland]
#guard (goblinCratermaker.summary.splitOn "Choose one").length > 1
#guard (goblinCratermaker.summary.splitOn "colorless nonland").length > 1
#guard smiteTheDeathless.isInstant
#guard smiteTheDeathless.requiresTarget
#guard smiteTheDeathless.spellEffect == some (Effect.dealDamageLoseIndestructibleExile 3)
#guard (Effect.dealDamageLoseIndestructibleExile 3).targetCount == 1
#guard (smiteTheDeathless.summary.splitOn "loses indestructible").length > 1
#guard (smiteTheDeathless.summary.splitOn "exile it instead").length > 1
#guard ologHaiCrusher.keywords.trample
#guard ologHaiCrusher.staticAbilities == #[.cantBlockUnlessYouControl #["Goblin", "Orc"]]
#guard (ologHaiCrusher.summary.splitOn "trample").length > 1
#guard (ologHaiCrusher.summary.splitOn "can't block unless").length > 1
#guard oliphaunt.keywords.trample
#guard oliphaunt.triggeredAbilities == #[.onAttackOtherGets2AndTrample]
#guard oliphaunt.activatedAbilities.size == 1
#guard oliphaunt.activatedAbilities[0]!.activateFromHand
#guard oliphaunt.activatedAbilities[0]!.cost.discardSource
#guard oliphaunt.activatedAbilities[0]!.effect == Effect.searchLandTypeToHand "Mountain"
#guard oliphaunt.activatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 1)
#guard oliphaunt.power == some 6
#guard oliphaunt.toughness == some 4
#guard (oliphaunt.summary.splitOn "trample").length > 1
#guard (oliphaunt.summary.splitOn "+2/+0").length > 1
#guard (oliphaunt.summary.splitOn "Mountaincycling").length > 1
#guard goblinFireleaper.activatedAbilities.size == 1
#guard goblinFireleaper.activatedAbilities[0]!.effect == Effect.sourceGets 1 0
#guard goblinFireleaper.activatedAbilities[0]!.cost.mana == (ManaCost.ofGenericAndColor 1 .red)
#guard goblinFireleaper.triggeredAbilities == #[.onDiesDealDamageEqualToPowerToOppCreature]
#guard (goblinFireleaper.summary.splitOn "+1/+0").length > 1
#guard (goblinFireleaper.summary.splitOn "dies").length > 1
#guard infernoTitan.activatedAbilities.size == 1
#guard infernoTitan.activatedAbilities[0]!.effect == Effect.sourceGets 1 0
#guard infernoTitan.activatedAbilities[0]!.cost.mana == (ManaCost.ofColor .red)
#guard infernoTitan.triggeredAbilities == #[.onEnterOrAttackDealDividedDamage 3 3]
#guard infernoTitan.power == some 6
#guard infernoTitan.toughness == some 6
#guard (infernoTitan.summary.splitOn "+1/+0").length > 1
#guard (infernoTitan.summary.splitOn "divided as you choose").length > 1
#guard guttersnipe.triggeredAbilities == #[.onCastInstantOrSorceryDealDamageToEachOpponent 2]
#guard guttersnipe.power == some 2
#guard guttersnipe.toughness == some 2
#guard (guttersnipe.summary.splitOn "instant or sorcery").length > 1
#guard hauntOfTheDeadMarshes.triggeredAbilities == #[.onEnterScry 1]
#guard hauntOfTheDeadMarshes.activatedAbilities.size == 1
#guard hauntOfTheDeadMarshes.activatedAbilities[0]!.activateFromGraveyard
#guard hauntOfTheDeadMarshes.activatedAbilities[0]!.onlyIfYouControlLegendary
#guard hauntOfTheDeadMarshes.activatedAbilities[0]!.effect == Effect.returnFromGraveyardTapped
#guard languish.spellEffect == some (Effect.allCreaturesGet (-4) (-4))
#guard !languish.requiresTarget
#guard shadowOfTheEnemy.spellEffect == some (Effect.exileGraveyardCreaturesGrantCast)
#guard shadowOfTheEnemy.requiresTarget
#guard trollOfKhazadDum.staticAbilities == #[.cantBeBlockedExceptBy 3]
#guard (trollOfKhazadDum.summary.splitOn "three or more").length > 1
#guard trollOfKhazadDum.activatedAbilities.size == 1
#guard trollOfKhazadDum.activatedAbilities[0]!.activateFromHand
#guard trollOfKhazadDum.activatedAbilities[0]!.cost.discardSource
#guard trollOfKhazadDum.activatedAbilities[0]!.effect == Effect.searchLandTypeToHand "Swamp"
#guard trollOfKhazadDum.activatedAbilities[0]!.cost.mana == (ManaCost.ofGeneric 1)
#guard mercilessExecutioner.triggeredAbilities == #[.onEnterEachPlayerSacrificesCreature]
#guard bitterDownfall.spellEffect == some (Effect.destroyTargetCreatureControllerLosesLife 2)
#guard bitterDownfall.costReductionIfTargetDamaged == 3
#guard improvisedClub.isInstant
#guard improvisedClub.spellEffect == some (Effect.dealDamage 4)
#guard improvisedClub.additionalCostSacrificeArtifactOrCreature
#guard improvisedClub.requiresTarget
#guard (improvisedClub.summary.splitOn "additional cost").length > 1
#guard (improvisedClub.summary.splitOn "4 damage").length > 1
#guard fireOfOrthanc.isSorcery
#guard fireOfOrthanc.spellEffect == some (Effect.destroyArtifactOrLandNonflyersCantBlock)
#guard fireOfOrthanc.requiresTarget
#guard (fireOfOrthanc.summary.splitOn "artifact or land").length > 1
#guard (fireOfOrthanc.summary.splitOn "can't block this turn").length > 1
#guard nightsWhisper.isSorcery
#guard nightsWhisper.spellEffect == some (Effect.drawAndLoseLife 2 2)
#guard !nightsWhisper.requiresTarget
#guard nightsWhisper.hasCastKind .draw
#guard (nightsWhisper.summary.splitOn "draw two cards").length > 1
#guard (nightsWhisper.summary.splitOn "lose 2 life").length > 1
#guard theOneRing.activatedAbilities[0]!.effect == Effect.burdenThenDraw
#guard theOneRing.triggeredAbilities ==
  #[.onEnterIfCastProtectionEverything, .onYourUpkeepLoseLifePerBurden]
#guard palantirOfOrthanc.triggeredAbilities == #[.onYourEndStepPalantir]
#guard pelargirSurvivor.tapAddAnyColorForInstantOrSorcery
#guard pelargirSurvivor.activatedAbilities.size == 1
#guard pelargirSurvivor.activatedAbilities[0]!.cost.tap
#guard pelargirSurvivor.activatedAbilities[0]!.cost.mana ==
  ManaCost.ofGenericAndColor 5 .blue
#guard pelargirSurvivor.activatedAbilities[0]!.effect == Effect.millPlayer 3
#guard grimaSarumanSFootman.keywords.cantBeBlocked
#guard grimaSarumanSFootman.triggeredAbilities == #[.onCombatDamageImpulseInstantSorcery]
#guard gandalfShadowSFoe.triggeredAbilities ==
  #[.onEnterExileLandsThenReturnTapped, .onLandYouControlEntersDrawPlusOneSource]
#guard arwenMortalQueen.entersWithIndestructibleCounter
#guard arwenMortalQueen.activatedAbilities[0]!.effect == Effect.arwenShare
#guard callForthTheTempest.spellEffect == some (Effect.damageOppCreaturesEqualOtherSpellsMv)
#guard galadrielSDismissal.spellEffect == some (Effect.phaseOutKicker)
#guard theReaverCleaver.staticAbilities == #[.equippedGetsTrampleAndCombatTreasures 1 1]
#guard mountDoom.activatedAbilities.size == 2
#guard mountDoom.activatedAbilities[1]!.cost.sacrificeLegendaryArtifact

end Mtg.Engine.Catalog
