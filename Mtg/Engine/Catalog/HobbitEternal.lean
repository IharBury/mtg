import Mtg.Engine.Card
import Mtg.Engine.Catalog

/-!
# The Hobbit Eternal catalog

Oracle characteristics for cards from Magic: The Gathering | The Hobbit
Eternal (HOC). Oracle text is stored verbatim from Scryfall; modeled
fields must reconstruct it. `CardDef.matchesOracleText` checks that
mechanically. `hobbitEternalCards` lists every unique card in the set,
including reprints that also appear in other sets.
-/

namespace Mtg.Engine.Catalog

open Mtg.Engine

def mentorOfTheMeek : CardDef :=
  creature "Mentor of the Meek" (ManaCost.ofGenericAndColor 2 .white) #["Human", "Soldier"] 2 2
    (oracleText := "Whenever another creature you control with power 2 or less enters, you may pay {1}. If you do, draw a card.")
    (triggeredAbilities := #[.onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw 2 1])

def fiendHunter : CardDef :=
  creature "Fiend Hunter" (ManaCost.ofGenericAndColors 1 [.white, .white]) #["Human", "Cleric"] 1 3
    (oracleText := "When this creature enters, you may exile another target creature.\nWhen this creature leaves the battlefield, return the exiled card to the battlefield under its owner's control.")
    (triggeredAbilities := #[.onEnterMayExileAnotherCreature, .onLeaveReturnExiled])

def errandRiderOfGondor : CardDef :=
  creature "Errand-Rider of Gondor" (ManaCost.ofGenericAndColor 2 .white) #["Human", "Soldier"] 3 2
    (oracleText := "When this creature enters, draw a card. Then if you don't control a legendary creature, put a card from your hand on the bottom of your library.")
    (triggeredAbilities := #[.onEnterDrawThenBottomIfNoLegendary])

def landrovalHorizonWitness : CardDef :=
  legendaryCreature "Landroval, Horizon Witness" (ManaCost.ofGenericAndColor 4 .white) #["Bird", "Noble"] 3 4
    (oracleText := "Flying\nWhenever two or more creatures you control attack a player, target attacking creature without flying gains flying until end of turn.")
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onAttackWithTwoOrMoreGrantFlying])

def roguesPassage : CardDef :=
  (TraditionalCardDefinition.card [
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
          .endOfTurn))
  ]).toCardDef
    (oracleText := "{T}: Add {C}.\n{4}, {T}: Target creature can't be blocked this turn.")

def soldierOfTheGreyHost : CardDef :=
  (TraditionalCardDefinition.card [
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
          [.addPowerToughness
            (.target 1 (.intersection [.permanent, .cardType .creature]))
            2 0]
          .endOfTurn))
  ]).toCardDef
    (oracleText := "Flash\nFlying\nWhen this creature enters, target creature gets +2/+0 until end of turn.")

def eaglesOfTheNorth : CardDef :=
  (TraditionalCardDefinition.card [
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
            .addPowerToughness
              (.intersection [
                .permanent,
                .cardType .creature,
                .controlled (.controller .this)])
              1 0,
            .gainAbility
              (.intersection [
                .permanent,
                .cardType .creature,
                .controlled (.controller .this)])
              (.keyword .firstStrike)]
          .endOfTurn)),
    .ability (.keywordWithCost (.subtypecycling .plains) [.mana [.generic 1]])
  ]).toCardDef
    (oracleText := "Flying\nWhen this creature enters, creatures you control get +1/+0 and gain first strike until end of turn.\nPlainscycling {1} ({1}, Discard this card: Search your library for a Plains card, reveal it, put it into your hand, then shuffle.)")

def dunedainBlade : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Dúnedain Blade",
    .manaCost [.generic 1, .mono .white],
    .type .artifact,
    .subtype .equipment,
    .ability (.static (.addPowerToughness (.hostOf .this) 2 1)),
    .ability (.keywordWithSubtypeAndCost .equip .human (.mana [.generic 1])),
    .ability (.keywordWithCost .equip [.mana [.generic 3]])
  ]).toCardDef
    (oracleText := "Equipped creature gets +2/+1.\nEquip Human {1}\nEquip {3} ({3}: Attach to target creature you control. Equip only as a sorcery.)")

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

def westfoldRider : CardDef :=
  (TraditionalCardDefinition.card [
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
          (.target 1 (.union [.cardType .artifact, .cardType .enchantment]))))
  ]).toCardDef
    (oracleText := "Sacrifice this creature: Destroy target artifact or enchantment. Activate only as a sorcery.")

def esquireOfTheKing : CardDef :=
  (TraditionalCardDefinition.card [
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
            .addPowerToughness
              (.intersection [
                .permanent,
                .cardType .creature,
                .controlled (.controller .this)])
              1 1]
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
          [.reduceCost .this [.mana [.generic 2]]]))
  ]).toCardDef
    (oracleText := "{4}{W}, {T}: Creatures you control get +1/+1 until end of turn. This ability costs {2} less to activate if you control a legendary creature.")

def pelargirSurvivor : CardDef :=
  creature "Pelargir Survivor" (ManaCost.ofGenericAndColor 1 .blue) #["Human", "Peasant"] 1 3
    (oracleText := "{T}: Add one mana of any color. Spend this mana only to cast an instant or sorcery spell.\n{5}{U}, {T}: Target player mills three cards. (They put the top three cards of their library into their graveyard.)")
    (tapAddAnyColorForInstantOrSorcery := true)
    (activatedAbilities := #[
      activated (Effect.millPlayer 3) (ManaCost.ofGenericAndColor 5 .blue) (tap := true)])

def lorienRevealed : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Lórien Revealed",
    .manaCost [.generic 3, .mono .blue, .mono .blue],
    .type .sorcery,
    .actions [.draw (.controller .this) 3],
    .ability (.keywordWithCost (.subtypecycling .island) [.mana [.generic 1]])
  ]).toCardDef
    (oracleText := "Draw three cards.\nIslandcycling {1} ({1}, Discard this card: Search your library for an Island card, reveal it, put it into your hand, then shuffle.)")

def knightsOfDolAmroth : CardDef :=
  (TraditionalCardDefinition.card [
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
        (.putCounter (.source .this) .plusOnePlusOne 1))
  ]).toCardDef
    (oracleText := "Whenever you draw your second card each turn, put a +1/+1 counter on this creature.")

def greyHavensNavigator : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Grey Havens Navigator",
    .manaCost [.generic 2, .mono .blue],
    .type .creature,
    .subtype .elf,
    .subtype .pilot,
    .power 3,
    .toughness 2,
    .ability (.keyword .flash),
    .ability (.triggered (.enter .this) (.scry (.controller .this) 1))
  ]).toCardDef
    (oracleText := "Flash\nWhen this creature enters, scry 1.")

def ithilienKingfisher : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Ithilien Kingfisher",
    .manaCost [.generic 2, .mono .blue],
    .type .creature,
    .subtype .bird,
    .power 2,
    .toughness 1,
    .ability (.keyword .flying),
    .ability (.triggered (.die .this) (.draw (.controller .this) 1))
  ]).toCardDef
    (oracleText := "Flying\nWhen this creature dies, draw a card.")

def hithlainKnots : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Hithlain Knots",
    .manaCost [.generic 1, .mono .blue],
    .type .instant,
    .actions [
      .tap (.target 1 (.intersection [.permanent, .cardType .creature])),
      .scry (.controller .this) 1,
      .draw (.controller .this) 1]
  ]).toCardDef
    (oracleText := "Tap target creature. Scry 1.\nDraw a card.")

def captainOfUmbar : CardDef :=
  (TraditionalCardDefinition.card [
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
        (.sequence [.draw (.controller .this) 1, .discard (.controller .this) 1]))
  ]).toCardDef
    (oracleText := "{1}, {T}: Draw a card, then discard a card.")

def minasTirithGarrison : CardDef :=
  card "Minas Tirith Garrison" #[.creature] (ManaCost.ofGenericAndColor 3 .blue) #["Human", "Soldier"]
    "Minas Tirith Garrison's power is equal to the number of cards in your hand.\nWhenever this creature attacks, you may tap any number of untapped Humans you control. Draw a card for each Human tapped this way."
    (toughness := some 5)
    (staticAbilities := #[.powerEqualCardsInHand])
    (triggeredAbilities := #[.onAttackTapHumansDraw])

def colossalWhale : CardDef :=
  creature "Colossal Whale" (ManaCost.ofGenericAndColors 5 [.blue, .blue]) #["Whale"] 5 5
    (oracleText := "Islandwalk (This creature can't be blocked as long as defending player controls an Island.)\nWhenever this creature attacks, you may exile target creature defending player controls until this creature leaves the battlefield. (That creature returns under its owner's control.)")
    (keywords := Keyword.islandwalk)
    (triggeredAbilities := #[.onAttackMayExileDefenderUntilLeaves])

def willowWind : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Willow-Wind",
    .manaCost [.generic 4, .mono .blue],
    .type .creature,
    .subtype .elemental,
    .power 3,
    .toughness 4,
    .ability (.keyword .flying),
    .ability (.triggered (.enter .this) (.scry (.controller .this) 2))
  ]).toCardDef
    (oracleText := "Flying\nWhen this creature enters, scry 2.")

def nimrodelWatcher : CardDef :=
  creature "Nimrodel Watcher" (ManaCost.ofGenericAndColor 1 .blue) #["Elf", "Scout"] 2 1
    (oracleText := "Whenever you scry, this creature gets +1/+0 until end of turn and can't be blocked this turn. This ability triggers only once each turn.")
    (triggeredAbilities := #[.onScryPumpAndUnblockableOnce])

def sternScolding : CardDef :=
  instant "Stern Scolding" (ManaCost.ofColor .blue)
    "Counter target creature spell with power or toughness 2 or less."
    (some (Effect.counterCreatureSpellPTAtMost 2))

def hauntOfTheDeadMarshes : CardDef :=
  creature "Haunt of the Dead Marshes" (ManaCost.ofColor .black) #["Nightmare", "Elf"] 1 1
    (oracleText := "When this creature enters, scry 1.\n{2}{B}: Return this card from your graveyard to the battlefield tapped. Activate only if you control a legendary creature.")
    (triggeredAbilities := #[.onEnterScry 1])
    (activatedAbilities := #[
      activated (Effect.returnFromGraveyardTapped) (ManaCost.ofGenericAndColor 2 .black)
        (activateFromGraveyard := true) (onlyIfYouControlLegendary := true)])

def languish : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Languish",
    .manaCost [.generic 2, .mono .black, .mono .black],
    .type .sorcery,
    .actions [
      .continuous
        [.addPowerToughness
          (.intersection [.permanent, .cardType .creature])
          (-4) (-4)]
        .endOfTurn]
  ]).toCardDef
    (oracleText := "All creatures get -4/-4 until end of turn.")

def shadowOfTheEnemy : CardDef :=
  sorcery "Shadow of the Enemy" (ManaCost.ofGenericAndColors 3 [.black, .black, .black])
    "Exile all creature cards from target player's graveyard. You may cast spells from among those cards for as long as they remain exiled, and mana of any type can be spent to cast them."
    (some (Effect.exileGraveyardCreaturesGrantCast))

def trollOfKhazadDum : CardDef :=
  creature "Troll of Khazad-dûm" (ManaCost.ofGenericAndColor 5 .black) #["Troll"] 6 5
    (oracleText := "This creature can't be blocked except by three or more creatures.\nSwampcycling {1} ({1}, Discard this card: Search your library for a Swamp card, reveal it, put it into your hand, then shuffle.)")
    (staticAbilities := #[.cantBeBlockedExceptBy 3])
    (activatedAbilities := #[typecyclingAbility "Swamp"])

def mercilessExecutioner : CardDef :=
  (TraditionalCardDefinition.card [
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
                .controlled (.variable 1)]))]))
  ]).toCardDef
    (oracleText := "When this creature enters, each player sacrifices a creature of their choice.")

def bitterDownfall : CardDef :=
  instant "Bitter Downfall" (ManaCost.ofGenericAndColor 3 .black)
    "This spell costs {3} less to cast if it targets a creature that was dealt damage this turn.\nDestroy target creature. Its controller loses 2 life."
    (some (Effect.destroyTargetCreatureControllerLosesLife 2))
    (costReductionIfTargetDamaged := 3)

def nightsWhisper : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Night's Whisper",
    .manaCost [.generic 1, .mono .black],
    .type .sorcery,
    .actions [
      .draw (.controller .this) 2,
      .loseLife (.controller .this) 2]
  ]).toCardDef
    (oracleText := "You draw two cards and lose 2 life.")

def wayfarersBauble : CardDef :=
  (TraditionalCardDefinition.card [
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
                  .inDeck,
                  .cardType .land,
                  .supertype .basic]))
              [.tapped]]))
  ]).toCardDef
    (oracleText :=
      "{2}, {T}, Sacrifice this artifact: Search your library for a basic land card, put that card onto the battlefield tapped, then shuffle.")

def battleScarredGoblin : CardDef :=
  (TraditionalCardDefinition.card [
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
        (.dealDamage .this (.blocking .this) 1))
  ]).toCardDef
    (oracleText := "Whenever this creature becomes blocked, it deals 1 damage to each creature blocking it.")

def improvisedClub : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Improvised Club",
    .manaCost [.generic 1, .mono .red],
    .type .instant,
    .ability (
      .static
        (.additionalCost .this
          [.sacrificeCount
            (.intersection [
              .permanent,
              .union [.cardType .artifact, .cardType .creature]])
            1])),
    .actions [.dealDamage .this (.target 1 .all) 4]
  ]).toCardDef
    (oracleText := "As an additional cost to cast this spell, sacrifice an artifact or creature.\nImprovised Club deals 4 damage to any target.")

def ologHaiCrusher : CardDef :=
  creature "Olog-hai Crusher" (ManaCost.ofGenericAndColor 3 .red) #["Troll", "Soldier"] 4 4
    (oracleText := "Trample\nThis creature can't block unless you control a Goblin or Orc.")
    (keywords := Keyword.trample)
    (staticAbilities := #[.cantBlockUnlessYouControl #["Goblin", "Orc"]])

def smiteTheDeathless : CardDef :=
  instant "Smite the Deathless" (ManaCost.ofGenericAndColor 1 .red)
    "Smite the Deathless deals 3 damage to target creature. That creature loses indestructible until end of turn. If that creature would die this turn, exile it instead."
    (some (Effect.dealDamageLoseIndestructibleExile 3))

def goblinFireleaper : CardDef :=
  (TraditionalCardDefinition.card [
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
        (.continuous [.addPowerToughness (.source .this) 1 0] .endOfTurn)),
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
              .controlled (.opponent (.controller .this))]))))
  ]).toCardDef
    (oracleText := "{1}{R}: This creature gets +1/+0 until end of turn.\nWhen this creature dies, it deals damage equal to its power to target creature an opponent controls.")

def oliphaunt : CardDef :=
  (TraditionalCardDefinition.card [
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
            .addPowerToughness
              (.target
                1
                (.intersection [
                  .not .this,
                  .permanent,
                  .cardType .creature,
                  .controlled (.controller .this)]))
              2 0,
            .gainAbility (.targetReference 1) (.keyword .trample)]
          .endOfTurn)),
    .ability (.keywordWithCost (.subtypecycling .mountain) [.mana [.generic 1]])
  ]).toCardDef
    (oracleText := "Trample\nWhenever this creature attacks, another target creature you control gets +2/+0 and gains trample until end of turn.\nMountaincycling {1} ({1}, Discard this card: Search your library for a Mountain card, reveal it, put it into your hand, then shuffle.)")

def goblinCratermaker : CardDef :=
  creature "Goblin Cratermaker" (ManaCost.ofGenericAndColor 1 .red) #["Goblin", "Warrior"] 2 2
    (oracleText := "{1}, Sacrifice this creature: Choose one —\n• This creature deals 2 damage to target creature.\n• Destroy target colorless nonland permanent.")
    (activatedAbilities := #[
      activated (Effect.dealDamageToTargetCreature 2) (ManaCost.ofGeneric 1)
        (sacrificeSource := true)
        (otherModes := #[Effect.destroyTargetColorlessNonland])])

def infernoTitan : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Inferno Titan",
    .manaCost [.generic 4, .mono .red, .mono .red],
    .type .creature,
    .subtype .giant,
    .power 6,
    .toughness 6,
    .ability (
      .activated
        [.mana [.mono .red]]
        (.continuous [.addPowerToughness (.source .this) 1 0] .endOfTurn)),
    .ability (
      .triggered
        (.or (.enter .this) (.attack .this .all))
        (.divideDamage
          (.controller .this)
          .this
          (.targets 1 (.range 1 3) .all)
          3))
  ]).toCardDef
    (oracleText := "{R}: This creature gets +1/+0 until end of turn.\nWhenever this creature enters or attacks, it deals 3 damage divided as you choose among one, two, or three targets.")

def guttersnipe : CardDef :=
  (TraditionalCardDefinition.card [
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
        (.dealDamage .this (.opponent (.controller .this)) 2))
  ]).toCardDef
    (oracleText := "Whenever you cast an instant or sorcery spell, this creature deals 2 damage to each opponent.")

def orcishSiegemaster : CardDef :=
  creature "Orcish Siegemaster" (ManaCost.ofGenericAndColor 2 .red) #["Orc", "Soldier"] 0 5
    (oracleText := "Trample\nOther Orcs and Goblins you control have trample.\nWhenever this creature attacks, it gets +X/+0 until end of turn, where X is the greatest power among creatures you control.")
    (keywords := Keyword.trample)
    (staticAbilities := #[.otherCreaturesHaveTrample #["Orc", "Goblin"]])
    (triggeredAbilities := #[.onAttackPumpByGreatestPower])

def fireOfOrthanc : CardDef :=
  (TraditionalCardDefinition.card [
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
        .endOfTurn]
  ]).toCardDef
    (oracleText := "Destroy target artifact or land. Creatures without flying can't block this turn.")

def galadhrimGuide : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Galadhrim Guide",
    .manaCost [.generic 3, .mono .green],
    .type .creature,
    .subtype .elf,
    .subtype .scout,
    .power 3,
    .toughness 4,
    .ability (.triggered (.enter .this) (.scry (.controller .this) 2))
  ]).toCardDef
    (oracleText := "When this creature enters, scry 2.")

def elvishVisionary : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Elvish Visionary",
    .manaCost [.generic 1, .mono .green],
    .type .creature,
    .subtype .elf,
    .subtype .shaman,
    .power 1,
    .toughness 1,
    .ability (.triggered (.enter .this) (.draw (.controller .this) 1))
  ]).toCardDef
    (oracleText := "When this creature enters, draw a card.")

def mirkwoodElk : CardDef :=
  creature "Mirkwood Elk" (ManaCost.ofGenericAndColor 5 .green) #["Elk"] 6 6
    (oracleText := "Trample\nWhenever this creature enters or attacks, return target Elf card from your graveyard to your hand. You gain life equal to that card's power.")
    (keywords := Keyword.trample)
    (triggeredAbilities := #[.onEnterOrAttackReturnElfGainLife])

def celebornTheWise : CardDef :=
  legendaryCreature "Celeborn the Wise" (ManaCost.ofGenericAndColor 3 .green) #["Elf", "Noble"] 3 3
    (oracleText := "Whenever you attack with one or more Elves, scry 1.\nWhenever you scry, Celeborn gets +1/+1 until end of turn for each card looked at while scrying this way.")
    (triggeredAbilities := #[.onAttackWithElvesScry 1, .onScryPumpSelfForEachLookedAt])

def giftOfStrands : CardDef :=
  (TraditionalCardDefinition.card [
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
    .ability (.static (.addPowerToughness (.hostOf .this) 3 3))
  ]).toCardDef
    (oracleText := "Flash\nEnchant creature\nWhen this Aura enters, scry 2.\nEnchanted creature gets +3/+3.")

def elvishArchdruid : CardDef :=
  creature "Elvish Archdruid" (ManaCost.ofGenericAndColors 1 [.green, .green])
    #["Elf", "Druid"] 2 2
    (oracleText := "Other Elf creatures you control get +1/+1.\n{T}: Add {G} for each Elf you control.")
    (staticAbilities := #[.otherCreaturesGet #["Elf"] 1 1])
    (tapAddManaForEach := #[{ mana := .colored .green, subtype := "Elf" }])

def lothlorienLookout : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Lothlórien Lookout",
    .manaCost [.generic 1, .mono .green],
    .type .creature,
    .subtype .elf,
    .subtype .scout,
    .power 1,
    .toughness 3,
    .ability (.triggered (.attack .this .all) (.scry (.controller .this) 1))
  ]).toCardDef
    (oracleText := "Whenever this creature attacks, scry 1.")

def elvishMystic : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Elvish Mystic",
    .manaCost [.mono .green],
    .type .creature,
    .subtype .elf,
    .subtype .druid,
    .power 1,
    .toughness 1,
    .ability (.activated [.tapSymbol] (.addMana (.controller .this) [.mono .green]))
  ]).toCardDef (oracleText := "{T}: Add {G}.")

def bardHeirOfGirion : CardDef :=
  (TraditionalCardDefinition.card [
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
    .ability
      (.static
        (.addPowerToughness
          (.intersection [
            .not .this,
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)])
          1 1)),
    .ability
      (.triggered
        (.attackSimultaneously
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)])
          .all
          [])
        (.draw (.controller .this) 1))
  ]).toCardDef
    (oracleText := "Reach, vigilance\nOther creatures you control get +1/+1.\nWhenever you attack, draw a card.")

def reprieve : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Reprieve",
    .manaCost [.generic 1, .mono .white],
    .type .instant,
    .actions [
      .returnToHand (.target 1 .spell),
      .draw (.controller .this) 1]
  ]).toCardDef
    (oracleText := "Return target spell to its owner's hand.\nDraw a card.")

def greatGoblinFoulHearted : CardDef :=
  (TraditionalCardDefinition.card [
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
        (.keyword (.amass .goblin 3))),
    .ability (
      .static
        (.gainAbility
          (.intersection [
            .permanent,
            .subtype .army,
            .controlled (.controller .this)])
          (.keyword .trample)))
  ]).toCardDef
    (oracleText := "Whenever Great Goblin enters or attacks, amass Goblins 3. (Put three +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)\nArmies you control have trample.")

def dwarvenWarriors : CardDef :=
  creature "Dwarven Warriors" (ManaCost.ofGenericAndColor 2 .red)
    #["Dwarf", "Warrior"] 1 1
    (oracleText := "{T}: Target creature with power 2 or less can't be blocked this turn.")
    (activatedAbilities := #[
      activated (Effect.targetCantBeBlockedPowerAtMost 2) (tap := true)])

def bagEndBanquet : CardDef :=
  artifact "Bag End Banquet" (ManaCost.ofGeneric 6)
    "When this artifact enters, create three Food tokens.\n{T}: Add {C} for each Food you control."
    (triggeredAbilities := #[.onEnterCreateTokens .food 3])
    (tapAddManaForEach := #[⟨.colorless, "Food"⟩])

def floweringOfTheWhiteTree : CardDef :=
  enchantment "Flowering of the White Tree" (ManaCost.ofColors [.white, .white])
    "Legendary creatures you control get +2/+1 and have ward {1}.\nNonlegendary creatures you control get +1/+1."
    (supertypes := #[.legendary])
    (staticAbilities := #[
      .legendaryCreaturesGetAndWard 2 1 1,
      .nonlegendaryCreaturesGet 1 1])

def mithrilCoat : CardDef :=
  (TraditionalCardDefinition.card [
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
    .ability (.keywordWithCost .equip [.mana [.generic 3]])
  ]).toCardDef
    (oracleText := "Flash\nIndestructible\nWhen Mithril Coat enters, attach it to target legendary creature you control.\nEquipped creature has indestructible.\nEquip {3}")

def rivendell : CardDef :=
  legendaryLand "Rivendell"
    "Rivendell enters tapped unless you control a legendary creature.\n{T}: Add {U}.\n{1}{U}, {T}: Scry 2. Activate only if you control a legendary creature."
    (tapAddMana := #[.colored .blue])
    (entersTappedUnlessLegendary := true)
    (activatedAbilities := #[
      activated (Effect.abilityScry 2) (ManaCost.ofGenericAndColor 1 .blue) (tap := true)
        (onlyIfYouControlLegendary := true)])

def delightedHalfling : CardDef :=
  creature "Delighted Halfling" (ManaCost.ofColor .green) #["Halfling", "Citizen"] 1 2
    (oracleText := "{T}: Add {C}.\n{T}: Add one mana of any color. Spend this mana only to cast a legendary spell, and that spell can't be countered.")
    (tapAddMana := #[.colorless])
    (tapAddAnyColorForLegendary := true)

def relicOfSauron : CardDef :=
  artifact "Relic of Sauron" (ManaCost.ofGeneric 4)
    "{T}: Add two mana in any combination of {U}, {B}, and/or {R}.\n{3}, {T}: Draw two cards, then discard a card."
    (tapAddTwoAmong := #[.colored .blue, .colored .black, .colored .red])
    (activatedAbilities := #[
      activated (Effect.abilityDrawThenDiscard 2) (ManaCost.ofGeneric 3) (tap := true)])

def longLostLances : CardDef :=
  artifact "Long-Lost Lances" (ManaCost.ofGeneric 2)
    "Equipped creature gets +2/+0.\nDuring your turn, creatures you control that are equipped have first strike and vigilance.\nEquip {2}"
    (subtypes := #["Equipment"])
    (staticAbilities := #[
      .equippedCreatureGets 2 0,
      .equippedCreaturesHaveKeywordsDuringYourTurn (Keyword.firstStrike.merge Keyword.vigilance)])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 2)])

def lothoCorruptShirriff : CardDef :=
  (TraditionalCardDefinition.card [
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
          .createTokens (.controller .this) 1 PredefinedToken.treasureToken]))
  ]).toCardDef
    (oracleText := "Whenever a player casts their second spell each turn, you lose 1 life and create a Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")")

def flameOfAnor : CardDef :=
  instant "Flame of Anor" (ManaCost.ofGenericAndColors 1 [.blue, .red])
    "Choose one. If you control a Wizard as you cast this spell, you may choose two instead.\n• Target player draws two cards.\n• Destroy target artifact.\n• Flame of Anor deals 5 damage to target creature."
    (spellModes := #[(Effect.targetPlayerDraw 2), (Effect.destroyTargetArtifact), (Effect.dealDamageToCreature 5)])
    (chooseTwoIfYouControlSubtype := some "Wizard")

def lastMarchOfTheEnts : CardDef :=
  sorcery "Last March of the Ents" (ManaCost.ofGenericAndColors 6 [.green, .green])
    "This spell can't be countered.\nDraw cards equal to the greatest toughness among creatures you control, then put any number of creature cards from your hand onto the battlefield."
    (some (Effect.drawEqualToughnessThenPutCreatures))
    (cantBeCountered := true)

def raiseThePalisade : CardDef :=
  sorcery "Raise the Palisade" (ManaCost.ofGenericAndColor 4 .blue)
    "Choose a creature type. Return all creatures that aren't of the chosen type to their owners' hands."
    (some (Effect.chooseTypeReturnOthers))

def dragonsDesire : CardDef :=
  sorcery "Dragon's Desire" (ManaCost.ofGenericAndColors 2 [.red, .red])
    "Add {R} for each artifact your opponents control."
    (some (Effect.addRedPerOppArtifacts))

def oriPlateStacker : CardDef :=
  legendaryCreature "Ori, Plate Stacker" (ManaCost.ofGenericAndColors 5 [.white, .white])
    #["Dwarf", "Bard"] 3 3
    (oracleText := "When Ori enters, destroy all artifacts and enchantments your opponents control. You gain 1 life for each permanent destroyed this way.")
    (triggeredAbilities := #[.onEnterDestroyOppArtifactsEnchantmentsGainLife])

def dainOfTheAncientHalls : CardDef :=
  legendaryCreature "Dáin of the Ancient Halls" (ManaCost.ofGenericAndColors 3 [.red, .white])
    #["Dwarf", "Noble"] 4 5
    (oracleText := "Vigilance, haste\nWhenever Dáin attacks, he deals damage equal to the number of Dwarves you control to each opponent.")
    (keywords := Keyword.vigilance.merge Keyword.haste)
    (triggeredAbilities := #[.onAttackDamageEqualSubtypeToEachOpponent "Dwarf"])

def treasureVault : CardDef :=
  card "Treasure Vault" #[.artifact, .land] ManaCost.empty
    (oracleText := "{T}: Add {C}.\n{X}{X}, {T}, Sacrifice this land: Create X Treasure tokens.")
    (tapAddMana := #[.colorless])
    (activatedAbilities := #[
      activated (Effect.abilityCreateTokensX .treasure) { symbols := #[.x, .x] }
        (tap := true) (sacrificeSource := true)])

def aragornAndArwenWed : CardDef :=
  legendaryCreature "Aragorn and Arwen, Wed" (ManaCost.ofGenericAndColors 4 [.green, .white])
    #["Human", "Elf", "Noble"] 3 6
    (oracleText := "Vigilance\nWhenever Aragorn and Arwen enters or attacks, put a +1/+1 counter on each other creature you control. You gain 1 life for each other creature you control.")
    (keywords := Keyword.vigilance)
    (triggeredAbilities := #[.onEnterOrAttackPlusOneEachOtherGainLife])

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

def thranduilTheStrategist : CardDef :=
  legendaryCreature "Thranduil the Strategist" (ManaCost.ofGenericAndColors 3 [.green, .blue])
    #["Elf", "Noble"] 4 4
    (oracleText := "Other Elves you control have \"{T}: Add {G} or {U}.\"\nLandfall — Whenever a land you control enters, create a 1/1 green Elf creature token.")
    (staticAbilities := #[
      .otherSubtypeHaveTapAddOneOf #["Elf"] #[.colored .green, .colored .blue]])
    (triggeredAbilities := #[.onLandYouControlEntersCreateTokens .elf 1])

def moxAmber : CardDef :=
  artifact "Mox Amber" ManaCost.empty
    "{T}: Add one mana of any color among legendary creatures and planeswalkers you control."
    (supertypes := #[.legendary])
    (tapAddAnyColorAmongLegendaries := true)

def filiAndKiliJoyous : CardDef :=
  legendaryCreature "Fíli and Kíli, Joyous" (ManaCost.ofGenericAndColor 2 .red)
    #["Dwarf", "Bard"] 3 3
    (oracleText := "Haste\n{T}: Add {R}{R}. Spend this mana only to cast Dwarf, Equipment, and Saga spells.")
    (keywords := Keyword.haste)
    (tapAddRestricted := some (#[.colored .red, .colored .red],
      "Dwarf, Equipment, and Saga spells"))

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

def bolgEreborsReckoning : CardDef :=
  legendaryCreature "Bolg, Erebor's Reckoning" (ManaCost.ofGenericAndColors 4 [.black, .red])
    #["Goblin", "Soldier"] 6 6
    (oracleText := "Trample\nAt the beginning of each combat, other Goblins and Orcs you control get +2/+2 until end of turn. Creatures your opponents control get -1/-1 until end of turn.")
    (keywords := Keyword.trample)
    (triggeredAbilities := #[.onEachCombatOthersGetAndOppsGet #["Goblin", "Orc"] 2 2 (-1) (-1)])

def thorinKingOfDurinsFolk : CardDef :=
  legendaryCreature "Thorin, King of Durin's Folk" (ManaCost.ofGenericAndColors 3 [.red, .white])
    #["Dwarf", "Noble"] 4 4
    (oracleText := "Whenever Thorin or another Dwarf you control enters, create a Treasure token.\nOther Dwarves you control get +1/+0 for each artifact token you control.")
    (staticAbilities := #[.otherSubtypeGetPowerPerArtifactToken "Dwarf"])
    (triggeredAbilities := #[.onThisOrAnotherSubtypeEntersCreateTokens "Dwarf" .treasure 1])

def bilboUnexpectedAdventurer : CardDef :=
  legendaryCreature "Bilbo, Unexpected Adventurer" (ManaCost.ofGenericAndColor 3 .white)
    #["Halfling", "Rogue"] 2 2
    (oracleText := "Bilbo can't be blocked by creatures with power 3 or greater.\nWhenever Bilbo deals combat damage to a player or battle, put up to one target nonland permanent card with mana value 3 or less from a graveyard onto the battlefield under its owner's control.")
    (staticAbilities := #[.cantBeBlockedByPowerAtLeast 3])
    (triggeredAbilities := #[.onCombatDamagePutNonlandMvAtMost 3])

def andurilFlameOfTheWest : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Andúril, Flame of the West",
    .manaCost [.generic 3],
    .type .artifact,
    .supertype .legendary,
    .subtype .equipment,
    .ability (.static (.addPowerToughness (.hostOf .this) 3 1)),
    .ability (
      .triggered
        (.attack (.hostOf .this) .all)
        (.createTokensInState (.controller .this) 2
          [.type .creature, .subtype .spirit, .colorIndicator [.white], .power 1, .toughness 1,
            .ability (.keyword .flying)]
          [.tapped])),
    .ability (.keywordWithCost .equip [.mana [.generic 2]])
  ]).toCardDef
    (oracleText := "Equipped creature gets +3/+1.\nWhenever equipped creature attacks, create two tapped 1/1 white Spirit creature tokens with flying. If that creature is legendary, instead create two of those tokens that are tapped and attacking.\nEquip {2}")

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

def dragonCursedHalls : CardDef :=
  (TraditionalCardDefinition.card [
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
          .endOfTurn))
  ]).toCardDef
    (oracleText := "{T}: Add {C}.\n{1}, {T}: Until end of turn, target creature gains \"Whenever this creature deals combat damage to a player, create a Treasure token.\"")

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

def galadrielLightOfValinor : CardDef :=
  legendaryCreature "Galadriel, Light of Valinor" (ManaCost.ofGenericAndColors 2 [.green, .white, .blue]) #["Elf", "Noble"] 3 3 (oracleText := "Alliance — Whenever another creature you control enters, choose one that hasn't been chosen this turn —\n• Add {G}{G}{G}.\n• Put a +1/+1 counter on each creature you control.\n• Scry 2, then draw a card.")
    (triggeredAbilities := #[.onAnotherCreatureYouControlEntersAlliance])

def gandalfPartyGuest : CardDef :=
  legendaryCreature "Gandalf, Party Guest" (ManaCost.ofGenericAndColors 1 [.blue, .red, .white]) #["Avatar", "Wizard"] 3 4 (oracleText := "At the beginning of combat on your turn, you may cast an instant or sorcery spell with mana value X or less from your hand without paying its mana cost, where X is twice the number of legendary Wizards you control.")
    (triggeredAbilities := #[.onYourBeginCombatCastInstantSorceryFromHand])

def gandalfShadowSFoe : CardDef :=
  (TraditionalCardDefinition.card [
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
          .putCounter (.source .this) .plusOnePlusOne 1]))
  ]).toCardDef
    (oracleText := "Vigilance\nWhen Gandalf enters, exile up to three target lands you control, then return them to the battlefield tapped under their owner's control.\nLandfall — Whenever a land you control enters, draw a card and put a +1/+1 counter on Gandalf.")

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

def mountDoom : CardDef :=
  legendaryLand "Mount Doom" "{T}, Pay 1 life: Add {B} or {R}.\n{1}{B}{R}, {T}: Mount Doom deals 1 damage to each opponent.\n{5}{B}{R}, {T}, Sacrifice Mount Doom and a legendary artifact: Choose up to two creatures, then destroy the rest. Activate only as a sorcery."
    (tapPayLifeAddOneOf := some (1, #[.colored .black, .colored .red]))
    (activatedAbilities := #[
      activated (Effect.damageEachOpponent 1) (ManaCost.ofGenericAndColors 1 [.black, .red]) (tap := true),
      activated (Effect.chooseTwoDestroyRest) (ManaCost.ofGenericAndColors 5 [.black, .red])
        (tap := true) (sacrificeSource := true) (sacrificeLegendaryArtifact := true)
        (onlyAsSorcery := true)])

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

def thorinCompanySLeader : CardDef :=
  (TraditionalCardDefinition.card [
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
          .endOfTurn))
  ]).toCardDef
    (oracleText := "Whenever a Dwarf you control deals combat damage to a player or battle, create two Treasure tokens.\n{10}: Creatures you control gain double strike until end of turn.")

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
