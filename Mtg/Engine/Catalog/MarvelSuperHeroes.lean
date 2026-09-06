/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
Authors: MTG Engine Contributors
-/
import Mtg.Engine.Catalog

/-!
# Marvel Super Heroes catalog (MSH, 2026)

Official *Magic: The Gathering | Marvel Super Heroes* set: 276 draft-legal
cards (collector numbers 1–276) plus the five basic lands printed in the set.
Oracle text is taken from Scryfall (`set:msh unique:cards`). Ability words
(Power-up) and reminder text are stripped by `CardDef.reconstructOracle`.
-/

namespace Mtg.Engine.Catalog
open Mtg.Engine

def theSensationalSheHulk : CardDef :=
  legendaryCreature "The Sensational She-Hulk" (ManaCost.ofGenericAndColors 3 [.green, .white, .white]) #["Gamma", "Hero"] 6 6
    (oracleText := "Reach, trample\nYour opponents can't cast spells during your turn.\nWhenever a creature you control is dealt damage, you may have The Sensational She-Hulk deal that much damage to any target. Do this only once each turn.")
    (keywords := (Keyword.reach).merge Keyword.trample)
    (triggeredAbilities := #[.onWatch Effect.watchSheHulkRedirectOnce])
    (staticAbilities := #[StaticAbility.opponentsCantCastOnYourTurn])

def photonLivingLight : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Photon, Living Light",
    .manaCost [.generic 2, .mono .red, .mono .white, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .elemental,
    .subtype .hero,
    .power 4,
    .toughness 4,
    .ability (.keyword .flying),
    .ability (.keyword .hexproof),
    .ability (.keyword .prowess),
    .ability (
      .triggered
        (.castSpell
          (.intersection [
            .spell,
            .not (.cardType .creature),
            .controlled (.controller .this)]))
        (.putCounter
          (.intersection [
            .not .this,
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)])
          .plusOnePlusOne
          1))
  ]).toCardDef
    (oracleText := "Flying, hexproof, prowess\nWhenever you cast a noncreature spell, put a +1/+1 counter on each other creature you control.")

def theIncredibleHulk : CardDef :=
  legendaryCreature "The Incredible Hulk" (ManaCost.ofGenericAndColors 2 [.red, .red, .green, .green]) #["Gamma", "Berserker", "Hero"] 8 8
    (oracleText := "Reach, trample\nEnrage — Whenever The Incredible Hulk is dealt damage, put a +1/+1 counter on him. If he's attacking, untap him and there is an additional combat phase after this phase.")
    (keywords := (Keyword.reach).merge Keyword.trample)
    (triggeredAbilities := #[.onWatch Effect.watchHulk])

def theInvincibleIronMan : CardDef :=
  artifactCreature "The Invincible Iron Man" (ManaCost.ofGenericAndColors 4 [.blue, .red]) #["Human", "Hero"] 5 5
    (oracleText := "Flying, haste\nAt the beginning of combat on your turn, you may put an artifact card from your hand onto the battlefield. If it's an Equipment, attach it to The Invincible Iron Man.")
    (keywords := (Keyword.flying).merge Keyword.haste)
    (triggeredAbilities := #[.onCombatMayPutArtifactAttachEquipment])
    (legendary := true)

def blackPantherHopeEnduring : CardDef :=
  legendaryCreature "Black Panther, Hope Enduring" (ManaCost.ofGenericAndColors 4 [.white, .blue]) #["Human", "Warrior", "Hero"] 3 3
    (oracleText := "Flash\nDouble strike\nPrevent all damage that would be dealt to Black Panther.\nWhenever Black Panther deals combat damage to a player, draw a card.")
    (keywords := (Keyword.flash).merge Keyword.doubleStrike)
    (triggeredAbilities := #[.onCombatDamageDraw 1])
    (staticAbilities := #[StaticAbility.preventAllDamageToThis])

def agent13SharonCarter : CardDef :=
  legendaryCreature "Agent 13, Sharon Carter" (ManaCost.ofGenericAndColor 2 .white) #["Human", "Spy", "Hero"] 3 2
    (oracleText := "Whenever a creature you control attacks alone, investigate. (Create a Clue token. It's an artifact with \"{2}, Sacrifice this token: Draw a card.\")")
    (triggeredAbilities := #[.onCreatureYouControlAttacksAloneInvestigate])

def agentMariaHill : CardDef :=
  legendaryCreature "Agent Maria Hill" (ManaCost.ofColor .white) #["Human", "Spy", "Hero"] 2 1
    (oracleText := "Whenever Agent Maria Hill becomes tapped to pay a teamwork cost, put a +1/+1 counter on her and draw a card.")
    (triggeredAbilities := #[.onTappedForTeamworkPlusOneAndDraw])

def agentOfAtlas : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Agent of Atlas",
    .manaCost [.generic 1, .mono .white],
    .type .creature,
    .subtype .human,
    .subtype .spy,
    .subtype .hero,
    .power 2,
    .toughness 2,
    .ability (.keyword .prowess)
  ]).toCardDef
    (oracleText := "Prowess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn.)")

def agentPhilCoulson : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Agent Phil Coulson",
    .manaCost [.generic 1, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .human,
    .subtype .spy,
    .subtype .hero,
    .power 2,
    .toughness 2,
    .ability (.keyword .vigilance),
    .ability (
      .activated
        [.tapSymbol]
        (.putCounter
          (.intersection [
            .not .this,
            .permanent,
            .subtype .hero,
            .controlled (.controller .this)])
          .plusOnePlusOne
          1))
  ]).toCardDef
    (oracleText := "Vigilance\n{T}: Put a +1/+1 counter on each other Hero you control.")

def agentsOfSHIELD : CardDef :=
  creature "Agents of S.H.I.E.L.D." (ManaCost.ofGenericAndColor 2 .white) #["Human", "Spy", "Hero"] 2 4
    (oracleText := "Whenever a creature you control attacks alone, that creature gets +1/+1 until end of turn.")
    (triggeredAbilities := #[.onCreatureYouControlAttacksAlonePump 1 1])

def avengersAssemble : CardDef :=
  enchantment "Avengers Assemble!" (ManaCost.ofGenericAndColor 4 .white)
    "Flash\nHeroes you control get +2/+2.\nAt the beginning of each end step, if you attacked with a Hero this turn or a Hero entered the battlefield under your control this turn, draw a card."
    (keywords := Keyword.flash)
    (triggeredAbilities := #[.onEachEndStepDrawIfAttackedOrEnteredSubtype "Hero"])
    (staticAbilities := #[StaticAbility.creaturesYouControlOfSubtypeGet "Hero" 2 2])

def boroughBackup : CardDef :=
  sorcery "Borough Backup" (ManaCost.ofGenericAndColor 4 .white)
    "Create two 3/2 white Hero creature tokens with vigilance.\nBasic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)"
    (activatedAbilities := #[typecyclingAbility "Basic land" (ManaCost.ofGeneric 2)])
    (spellEffect := some (Effect.createTokens .hero32vigilance 2))

def braveBrawler : CardDef :=
  creature "Brave Brawler" (ManaCost.ofGenericAndColor 1 .white) #["Human", "Warrior", "Hero"] 2 1
    (oracleText := "Lifelink\nPower-up — {4}{W}: Put two +1/+1 counters on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)")
    (keywords := Keyword.lifelink)
    (activatedAbilities := #[powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColor 4 .white)])

def captainAmericaSuperSoldier : CardDef :=
  legendaryCreature "Captain America, Super-Soldier" (ManaCost.ofGenericAndColors 1 [.white, .white]) #["Human", "Soldier", "Hero"] 3 2
    (oracleText := "First strike\nCaptain America enters with a shield counter on him. (If he would be dealt damage or destroyed, remove a shield counter from him instead.)\nAs long as Captain America has a shield counter on him, you and other Heroes you control have hexproof.")
    (keywords := Keyword.firstStrike)
    (entersWithShield := 1)
    (staticAbilities := #[StaticAbility.youAndOtherSubtypeHaveHexproofIfShield "Hero"])

def captainAmericaWingsOfFreedom : CardDef :=
  legendaryCreature "Captain America, Wings of Freedom" (ManaCost.ofGenericAndColor 2 .white) #["Human", "Soldier", "Hero"] 3 1
    (oracleText := "Flying, first strike, ward {1}\nWhenever Captain America attacks, each other Hero you control gets +X/+X until end of turn, where X is Captain America's toughness.")
    (keywords := (Keyword.flying).merge Keyword.firstStrike)
    (ward := some 1)
    (triggeredAbilities := #[.onAttackOthersOfSubtypeGetEqualToughness "Hero"])

def captainMarvelEarthSProtector : CardDef :=
  legendaryCreature "Captain Marvel, Earth's Protector" (ManaCost.ofGenericAndColors 3 [.white, .white]) #["Human", "Kree", "Hero"] 5 4
    (oracleText := "Flash\nFlying, lifelink\nPower-up — {5}{W}{W}: Put a +1/+1 counter and an indestructible counter on Captain Marvel. (Activate each power-up ability only once. Reduce the cost by her mana cost if she entered this turn.)")
    (keywords := ((Keyword.flash).merge Keyword.flying).merge Keyword.lifelink)
    (activatedAbilities := #[activated (Effect.plusOneAndIndestructibleCounter) (ManaCost.ofGenericAndColors 5 [.white, .white]) (powerUp := true)])

def captainMarVellSpaceBorn : CardDef :=
  legendaryCreature "Captain Mar-Vell, Space-Born" (ManaCost.ofGenericAndColor 4 .white) #["Kree", "Soldier", "Hero"] 4 4
    (oracleText := "Flying, vigilance\nCosmic Awareness — As long as an opponent has cast a spell this turn, you may cast spells as though they had flash.")
    (keywords := (Keyword.flying).merge Keyword.vigilance)
    (staticAbilities := #[StaticAbility.flashIfOpponentCastThisTurn])

def colleenWingStreetSamurai : CardDef :=
  legendaryCreature "Colleen Wing, Street Samurai" (ManaCost.ofGenericAndColor 1 .white) #["Human", "Samurai", "Hero"] 2 2
    (oracleText := "Whenever you cast a spell that targets a creature you control, put a +1/+1 counter on Colleen Wing. Scry 1. (Look at the top card of your library. You may put that card on the bottom.)")
    (triggeredAbilities := #[.onCasting Effect.castingPlusOneScry])

def crowdOfTrueBelievers : CardDef :=
  creature "Crowd of True Believers" (ManaCost.ofColor .white) #["Human", "Citizen"] 1 2
    (oracleText := "{T}: Target creature you control that's attacking alone gets +1/+0 until end of turn. You gain 1 life.")
    (activatedAbilities := #[activated (Effect.pumpAttackingAloneGainLife) (ManaCost.empty) (tap := true)])

def helicarrierStrike : CardDef :=
  instant "Helicarrier Strike" (ManaCost.ofColor .white)
    "Teamwork 2 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 2 or more.)\nHelicarrier Strike deals 2 damage to target attacking or blocking creature. If this spell was cast using teamwork, it deals 4 damage to that creature instead."
    (teamwork := some 2)
    (spellEffect := some (Effect.dealDamageToAttackerOrBlocker 2 4))

def heroInTraining : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Hero in Training",
    .manaCost [.generic 2, .mono .white],
    .type .creature,
    .subtype .human,
    .subtype .hero,
    .power 2,
    .toughness 2,
    .ability (
      .triggered
        (.enter .this)
        (.sequence [
          .draw (.controller .this) 1,
          .if
            (.any
              (.intersection [
                .not .this,
                .permanent,
                .subtype .hero,
                .controlled (.controller .this)]))
            [.gainLife (.controller .this) 2]]))
  ]).toCardDef
    (oracleText := "When this creature enters, draw a card. If you control another Hero, you gain 2 life.")

def invisibleWomanSueStorm : CardDef :=
  legendaryCreature "Invisible Woman, Sue Storm" (ManaCost.ofGenericAndColor 4 .white) #["Human", "Hero"] 2 5
    (oracleText := "Lifelink\nWhenever you put one or more +1/+1 counters on one or more other Heroes you control, you may create a 0/4 colorless Wall creature token with defender.")
    (keywords := Keyword.lifelink)
    (triggeredAbilities := #[.onResource Effect.resourcePlusOneOnHeroesCreateWall])

def jenniferWalters : CardDef :=
  legendaryCreature "Jennifer Walters" (ManaCost.ofGenericAndColor 1 .white) #["Human", "Advisor", "Hero"] 2 3
    (oracleText := "Your opponents can't cast spells during your turn.\n{3}{G}{W}{W}: Transform Jennifer Walters. Activate only as a sorcery.")
    (staticAbilities := #[StaticAbility.opponentsCantCastOnYourTurn])
    (activatedAbilities := #[activated (Effect.transform) (ManaCost.ofGenericAndColors 3 [.green, .white, .white]) (onlyAsSorcery := true)])
    (otherFace := some theSensationalSheHulk)

def kreeCommandos : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Kree Commandos",
    .manaCost [.generic 2, .mono .white],
    .type .creature,
    .subtype .kree,
    .subtype .soldier,
    .subtype .villain,
    .power 2,
    .toughness 1,
    .ability (.keyword .flying),
    .ability (.keyword .vigilance),
    .ability (.keyword .prowess)
  ]).toCardDef
    (oracleText := "Flying, vigilance\nProwess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn.)")

def lukeCagePowerMan : CardDef :=
  legendaryCreature "Luke Cage, Power Man" (ManaCost.ofGenericAndColor 3 .white) #["Human", "Hero"] 2 5
    (oracleText := "Unbreakable Skin — Whenever Luke Cage attacks alone, he gets +2/+0 and gains indestructible until end of turn. (Damage and effects that say \"destroy\" don't destroy him.)")
    (triggeredAbilities := #[.onThisAttack Effect.thisAttackAttacksAlonePlus2Indestructible])

def theMindStone : CardDef :=
  artifact "The Mind Stone" (ManaCost.ofGenericAndColor 1 .white)
    "Indestructible\n{T}: Add {W}.\n{5}{W}, {T}: Harness The Mind Stone. (Once harnessed, its ∞ ability is active.)\n∞ — At the beginning of your end step, exile up to one other target nonland permanent you control, then return that card to the battlefield under its owner's control."
    (subtypes := #["Infinity", "Stone"])
    (keywords := Keyword.indestructible)
    (triggeredAbilities := #[.onStep Effect.stepHarnessedFlicker])
    (tapAddMana := #[.colored .white])
    (activatedAbilities := #[activated (Effect.harnessInfinityStone) (ManaCost.ofGenericAndColor 5 .white) (tap := true)])
    (legendary := true)

def mockingbirdAceAgent : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Mockingbird, Ace Agent",
    .manaCost [.generic 3, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .human,
    .subtype .spy,
    .subtype .hero,
    .power 2,
    .toughness 2,
    .ability (.keyword .doubleStrike),
    .ability (
      .triggered
        (.castSpell
          (.intersection [.spell, .controlled (.controller .this)]))
        (.if
          (.targetsIncludeAny
            .this
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)]))
          [.putCounter (.source .this) .plusOnePlusOne 1]))
  ]).toCardDef
    (oracleText := "Double strike\nWhenever you cast a spell that targets a creature you control, put a +1/+1 counter on Mockingbird.")

def monicaRambeau : CardDef :=
  legendaryCreature "Monica Rambeau" (ManaCost.ofGenericAndColor 2 .white) #["Human", "Hero"] 3 3
    (oracleText := "Flying, prowess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn.)\n{2}{R}{W}{W}: Transform Monica Rambeau. Activate only as a sorcery.")
    (keywords := (Keyword.flying).merge Keyword.prowess)
    (activatedAbilities := #[activated (Effect.transform) (ManaCost.ofGenericAndColors 2 [.red, .white, .white]) (onlyAsSorcery := true)])
    (otherFace := some photonLivingLight)

def murdockSCrusade : CardDef :=
  sorcery "Murdock's Crusade" (ManaCost.ofGenericAndColor 1 .white)
    "Teamwork 4 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 4 or more.)\nChoose one. If this spell was cast using teamwork, choose both instead.\n• Street Justice — Exile target creature with toughness 4 or greater.\n• Legal Justice — Exile target enchantment with mana value 4 or greater."
    (teamwork := some 4)
    (spellModes := #[(Effect.exileCreatureToughnessAtLeast 4), (Effect.exileEnchantmentMvAtLeast 4)])
    (chooseBothIfTeamwork := true)

def nickFuryAgentOfSHIELD : CardDef :=
  legendaryCreature "Nick Fury, Agent of S.H.I.E.L.D." (ManaCost.ofColor .white) #["Human", "Spy", "Hero"] 2 1
    (oracleText := "Power-up — {W}{U}{B}{R}{G}: Put two +1/+1 counters on Nick Fury, then look at the top seven cards of your library. You may put a Hero, Equipment, or Vehicle card from among them onto the battlefield. If it's a double-faced card, you may transform it. Put the rest on the bottom of your library in a random order. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)")
    (activatedAbilities := #[activated (Effect.lookAtTopPutTypes 7 #["Hero", "Equipment", "Vehicle"]) (ManaCost.ofColors [.white, .blue, .black, .red, .green]) (powerUp := true)])

def nightNurseHealerOfHeroes : CardDef :=
  legendaryCreature "Night Nurse, Healer of Heroes" (ManaCost.ofGenericAndColor 1 .white) #["Human", "Doctor", "Hero"] 2 1
    (oracleText := "Flash\nLifelink\nWhen Night Nurse enters, choose target permanent card in your graveyard that was put there from anywhere this turn. Return it to your hand.")
    (keywords := (Keyword.flash).merge Keyword.lifelink)
    (triggeredAbilities := #[.onEnter Effect.enterReturnGyPermanentThisTurn])

def okoyeDoraMilajeLeader : CardDef :=
  legendaryCreature "Okoye, Dora Milaje Leader" (ManaCost.ofGenericAndColor 3 .white) #["Human", "Warrior", "Hero"] 3 2
    (oracleText := "When Okoye enters, create two 1/1 white Soldier creature tokens.\nAttacking creature tokens you control have first strike.")
    (triggeredAbilities := #[.onEnterCreateTokens .soldier11white 2])
    (staticAbilities := #[StaticAbility.attackingTokensHave Keyword.firstStrike])

def originOfTheAvengers : CardDef :=
  enchantment "Origin of the Avengers" (ManaCost.ofGenericAndColor 1 .white)
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)\nI — Scry 2.\nII — You may put a Hero creature card with mana value 3 or less from your hand onto the battlefield. If you don't, draw a card.\nIII — Put a +1/+1 counter on each creature you control."
    (subtypes := #["Saga"])
    (saga := some { sacrificeAfter := "III", chapters := #[chapter "I" "Scry 2." (Effect.scry 2), chapter "II" "You may put a Hero creature card with mana value 3 or less from your hand onto the battlefield. If you don't, draw a card." (Effect.mayPutHeroMvOrDraw 3), chapter "III" "Put a +1/+1 counter on each creature you control." (Effect.plusOneOnEachYouControl)] })

def pantherPounce : CardDef :=
  instant "Panther Pounce" (ManaCost.ofColor .white)
    "Target player investigates. Target creature gets +1/+0 and gains flying until end of turn. Untap it. (To investigate, create a Clue token. It's an artifact with \"{2}, Sacrifice this token: Draw a card.\")"
    (spellEffect := some (Effect.investigatePumpFlyingUntap))

def patriotShieldWielder : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Patriot, Shield Wielder",
    .manaCost [.generic 1, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .human,
    .subtype .hero,
    .power 2,
    .toughness 2,
    .ability
      (.activated
        [.mana [.generic 2], .tapSymbol]
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
            .gainAbility (.targetReference 1) (.keyword .hexproof)]
          .endOfTurn))
  ]).toCardDef
    (oracleText := "{2}, {T}: Another target creature you control gets +2/+0 and gains hexproof until end of turn. (It can't be the target of spells or abilities your opponents control.)")

def politicalTriumph : CardDef :=
  enchantment "Political Triumph" (ManaCost.ofColor .white)
    "Whenever a creature you control enters, scry 1 and put a plan counter on this enchantment.\nWhen the fourth plan counter is put on this enchantment, sacrifice it, draw a card, and put a +1/+1 counter on each creature you control."
    (subtypes := #["Plan"])
    (triggeredAbilities := #[.onCreatureYouControlEntersScryAndPlan 1, .onFourthPlanDrawPlusOneEach])

def quakeAgentOfSHIELD : CardDef :=
  legendaryCreature "Quake, Agent of S.H.I.E.L.D." (ManaCost.ofGenericAndColor 2 .white) #["Inhuman", "Spy", "Hero"] 3 3
    (oracleText := "Seismic Takedown — Whenever you cast a noncreature spell, tap target creature or land.")
    (triggeredAbilities := #[.onCasting Effect.castingTapCreatureOrLand])

def raftSecurityOfficer : CardDef :=
  creature "Raft Security Officer" (ManaCost.ofGenericAndColor 1 .white) #["Human", "Soldier"] 1 3
    (oracleText := "{2}, {T}: Tap target creature. This ability costs {1} less to activate if it targets a creature with power 3 or less.")
    (activatedAbilities := #[activated (Effect.tapTargetCreature) (ManaCost.ofGeneric 2) (tap := true)
      (costReductionIfTargetPowerAtMost := some (1, 3))])

def redGuardianSuperSoldier : CardDef :=
  legendaryCreature "Red Guardian, Super-Soldier" (ManaCost.ofGenericAndColor 2 .white) #["Human", "Soldier", "Villain"] 2 2
    (oracleText := "Flash\nWhen Red Guardian enters, destroy target creature an opponent controls that dealt damage this turn.")
    (keywords := Keyword.flash)
    (triggeredAbilities := #[.onEnter (Effect.enterDestroy .oppCreatureDealtDamageThisTurn)])

def theSentryGoldenGuardian : CardDef :=
  legendaryCreature "The Sentry, Golden Guardian" (ManaCost.ofGenericAndColor 3 .white) #["Human", "Hero"] 5 5
    (oracleText := "Flying, vigilance, indestructible\nWhen The Sentry enters, target opponent creates The Void, a legendary 5/5 black Horror Villain creature token with flying, indestructible, and \"The Void attacks each combat if able.\"")
    (keywords := ((Keyword.flying).merge Keyword.vigilance).merge Keyword.indestructible)
    (triggeredAbilities := #[.onEnter Effect.enterOppCreatesTheVoid])

def sHIELDSpyKit : CardDef :=
  artifact "S.H.I.E.L.D. Spy Kit" (ManaCost.ofColor .white)
    "Equipped creature gets +1/+1.\nWhenever equipped creature attacks alone, untap it and scry 1. (Look at the top card of your library. You may put that card on the bottom.)\nEquip {1} ({1}: Attach to target creature you control. Equip only as a sorcery.)"
    (subtypes := #["Equipment"])
    (triggeredAbilities := #[.onWatch Effect.watchEquippedAttacksAloneUntapScry])
    (staticAbilities := #[StaticAbility.equippedCreatureGets 1 1])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 1)])

def superVillainLockup : CardDef :=
  enchantment "Super Villain Lockup" (ManaCost.ofGenericAndColor 1 .white)
    "Flash\nWhen this enchantment enters, exile target tapped creature an opponent controls until this enchantment leaves the battlefield."
    (keywords := Keyword.flash)
    (triggeredAbilities := #[.onEnterExileOppTappedUntilLeaves])

def superSoldierSerum : CardDef :=
  enchantment "Super-Soldier Serum" (ManaCost.ofGenericAndColor 1 .white)
    "Enchant creature\nEnchanted creature gets +2/+2, has first strike and vigilance, and is a legendary Soldier in addition to its other types.\nWhenever enchanted creature attacks or blocks, attach any number of target Equipment you control to it."
    (subtypes := #["Aura"])
    (triggeredAbilities := #[.onWatch Effect.watchEnchantedAttachEquipment])
    (staticAbilities := #[StaticAbility.enchantedCreatureGetsHasAndTypes 2 2
      (Keyword.firstStrike.merge Keyword.vigilance) #["legendary", "Soldier"]])

def takeUpTheShield : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Take Up the Shield",
    .manaCost [.generic 1, .mono .white],
    .type .instant,
    .actions [
      .putCounter
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        .plusOnePlusOne
        1,
      .continuous
        [
          .gainAbility (.targetReference 1) (.keyword .lifelink),
          .gainAbility (.targetReference 1) (.keyword .indestructible)]
        .endOfTurn]
  ]).toCardDef
    (oracleText := "Put a +1/+1 counter on target creature. It gains lifelink and indestructible until end of turn. (Damage and effects that say \"destroy\" don't destroy it.)")

def wakandanDroneFlock : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Wakandan Drone Flock",
    .manaCost [.generic 3, .mono .white],
    .type .artifact,
    .type .creature,
    .subtype .robot,
    .power 3,
    .toughness 3,
    .ability (.keyword .flying),
    .ability (.triggered (.enter .this) (.scry (.controller .this) 2))
  ]).toCardDef
    (oracleText := "Flying\nWhen this creature enters, scry 2. (Look at the top two cards of your library, then put any number of them on the bottom and the rest on top in any order.)")

def webUp : CardDef :=
  enchantment "Web Up" (ManaCost.ofGenericAndColor 2 .white)
    "When this enchantment enters, exile target nonland permanent an opponent controls until this enchantment leaves the battlefield."
    (triggeredAbilities := #[.onEnterExileOppNonlandUntilLeaves])

def whiteWidowFreeAgent : CardDef :=
  (TraditionalCardDefinition.card [
    .name "White Widow, Free Agent",
    .manaCost [.generic 3, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .human,
    .subtype .hero,
    .subtype .villain,
    .power 2,
    .toughness 3,
    .ability (
      .triggered
        (.enter .this)
        (.chooseMode [
          .putCounter
            (.targets 1 (.range 0 2) (.intersection [.permanent, .cardType .creature]))
            .plusOnePlusOne
            1,
          .returnToHand
            (.target
              1
              (.intersection [
                .inGraveyard,
                .union [.cardType .artifact, .cardType .enchantment],
                .owner (.controller .this)]))]))
  ]).toCardDef
    (oracleText := "When White Widow enters, choose one —\n• Put a +1/+1 counter on each of up to two target creatures.\n• Return target artifact or enchantment card from your graveyard to your hand.")

def aerialDoombot : CardDef :=
  artifactCreature "Aerial Doombot" (ManaCost.ofColor .blue) #["Robot", "Villain"] 1 1
    (oracleText := "Flying\nPower-up — {5}{U}: Put three +1/+1 counters on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)")
    (keywords := Keyword.flying)
    (activatedAbilities := #[powerUpAbility (Effect.putPlusOnePlusOneOnSource 3) (ManaCost.ofGenericAndColor 5 .blue)])

def aIMScientists : CardDef :=
  creature "A.I.M. Scientists" (ManaCost.ofGenericAndColor 3 .blue) #["Human", "Scientist", "Villain"] 3 3
    (oracleText := "When this creature enters, it connives. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on this creature.)\nBasic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)")
    (triggeredAbilities := #[.onEnterConnive])
    (activatedAbilities := #[typecyclingAbility "Basic land" (ManaCost.ofGeneric 2)])

def atlanteanCavalry : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Atlantean Cavalry",
    .manaCost [.generic 2, .mono .blue],
    .type .creature,
    .subtype .merfolk,
    .subtype .soldier,
    .power 3,
    .toughness 2,
    .ability (.keyword .vigilance),
    .ability (
      .triggered
        (.ordinal 2 .turnStart (.draw (.controller .this) .all))
        (.putCounter (.source .this) .plusOnePlusOne 1))
  ]).toCardDef
    (oracleText := "Vigilance\nWhenever you draw your second card each turn, put a +1/+1 counter on this creature.")

def atlantisAttacks : CardDef :=
  sorcery "Atlantis Attacks" (ManaCost.ofGenericAndColors 5 [.blue, .blue])
    "Teamwork 4 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 4 or more.)\nChoose one. If this spell was cast using teamwork, choose both instead.\n• Target player creates a 6/5 blue Leviathan creature token with hexproof.\n• Return one or two target nonland permanents to their owners' hands."
    (teamwork := some 4)
    (spellModes := #[(Effect.targetPlayerCreatesTokens .leviathan65hexproof 1), (Effect.returnOneOrTwoNonlands)])
    (chooseBothIfTeamwork := true)

def attumaAtlanteanWarlord : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Attuma, Atlantean Warlord",
    .manaCost [.generic 2, .mono .blue, .mono .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .merfolk,
    .subtype .warrior,
    .subtype .villain,
    .power 3,
    .toughness 4,
    .ability (
      .static
        (.addPowerToughness
          (.intersection [
            .not .this,
            .permanent,
            .cardType .creature,
            .subtype .merfolk,
            .controlled (.controller .this)])
          1 1)),
    .ability (
      .triggered
        (.attackSimultaneously
          (.intersection [
            .permanent,
            .cardType .creature,
            .subtype .merfolk,
            .controlled (.controller .this)])
          [])
        (.draw (.controller .this) 1))
  ]).toCardDef
    (oracleText := "Other Merfolk you control get +1/+1.\nWhenever one or more Merfolk you control attack a player, draw a card.")

def boldBiochemist : CardDef :=
  creature "Bold Biochemist" (ManaCost.ofGenericAndColor 1 .blue) #["Human", "Scientist"] 1 3
    (oracleText := "Power-up — {5}{U}: Put a +1/+1 counter on this creature and draw two cards. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)")
    (activatedAbilities := #[activated (Effect.plusOneAndDraw 1 2) (ManaCost.ofGenericAndColor 5 .blue) (powerUp := true)])

def bruceBanner : CardDef :=
  legendaryCreature "Bruce Banner" (ManaCost.ofColor .blue) #["Human", "Scientist", "Hero"] 1 1
    (oracleText := "{X}{X}, {T}: Draw X cards. Activate only as a sorcery.\n{2}{R}{R}{G}{G}: Transform Bruce Banner. Activate only as a sorcery.")
    (activatedAbilities := #[activated (Effect.drawX) ({ symbols := #[.x, .x] }) (tap := true) (onlyAsSorcery := true), activated (Effect.transform) (ManaCost.ofGenericAndColors 2 [.red, .red, .green, .green]) (onlyAsSorcery := true)])
    (otherFace := some theIncredibleHulk)

def depower : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Depower",
    .manaCost [.generic 2, .mono .blue],
    .type .instant,
    .ability (
      .static
        (.if
          (.targetsIncludeAny
            .this
            (.intersection [
              .permanent,
              .cardType .creature,
              .attacking .all]))
          [.reduceCost .this [.mana [.generic 2]]])),
    .actions [
      .continuous
        [.addPowerToughness
          (.target 1 (.intersection [.permanent, .cardType .creature]))
          (-4) 0]
        .endOfTurn,
      .draw (.controller .this) 1]
  ]).toCardDef
    (oracleText := "This spell costs {2} less to cast if it targets an attacking creature.\nTarget creature gets -4/-0 until end of turn.\nDraw a card.")

def echoPerceptiveProdigy : CardDef :=
  legendaryCreature "Echo, Perceptive Prodigy" (ManaCost.ofGenericAndColor 2 .blue) #["Human", "Hero"] 1 4
    (oracleText := "Vigilance\n{1}, {T}: Copy target activated or triggered ability you control from a creature source. You may choose new targets for the copy. (Mana abilities can't be targeted.)")
    (keywords := Keyword.vigilance)
    (activatedAbilities := #[activated (Effect.copyControlledAbility true) (ManaCost.ofGeneric 1) (tap := true)])

def falconWingedWonder : CardDef :=
  legendaryCreature "Falcon, Winged Wonder" (ManaCost.ofGenericAndColor 4 .blue) #["Human", "Hero"] 3 4
    (oracleText := "Flying\nAvian Telepathy — When Falcon enters, create Redwing, a legendary 1/1 blue Bird Scout creature token with flying and \"Whenever Redwing attacks, surveil 1.\" (Look at the top card of your library. You may put it into your graveyard.)")
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onEnter Effect.enterCreateRedwing])

def falconSWingHarness : CardDef :=
  artifact "Falcon's Wing Harness" (ManaCost.ofGenericAndColor 1 .blue)
    "When this Equipment enters, attach it to target creature you control.\nEquipped creature gets +1/+1 and has flying and ward {1}. (Whenever equipped creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {1}.)\nEquip {2}{U} ({2}{U}: Attach to target creature you control. Equip only as a sorcery.)"
    (subtypes := #["Equipment"])
    (triggeredAbilities := #[.onEnterAttachToCreatureYouControl])
    (staticAbilities := #[StaticAbility.equippedCreatureGetsHasAndWard 1 1 Keyword.flying 1])
    (activatedAbilities := #[equipAbility (ManaCost.ofGenericAndColor 2 .blue)])

def frozenInIce : CardDef :=
  enchantment "Frozen in Ice" (ManaCost.ofGenericAndColor 2 .blue)
    "Enchant creature\nWhen this Aura enters, tap enchanted creature.\nEnchanted creature loses all abilities and can't become untapped."
    (subtypes := #["Aura"])
    (triggeredAbilities := #[.onEnterEnchanted .tap])
    (staticAbilities := #[StaticAbility.enchantedLosesAbilitiesCantUntap])

def futuristForge : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Futurist Forge",
    .manaCost [.generic 1, .mono .blue],
    .type .artifact,
    .ability (.triggered (.enter .this) (.draw (.controller .this) 1)),
    .ability (
      .activated
        [.mana [.generic 3, .mono .blue], .sacrifice .this]
        (.draw (.controller .this) 2))
  ]).toCardDef
    (oracleText := "When this artifact enters, draw a card.\n{3}{U}, Sacrifice this artifact: Draw two cards.")

def giantSizedFlyingAnt : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Giant-Sized Flying Ant",
    .manaCost [.generic 3, .mono .blue],
    .type .creature,
    .subtype .insect,
    .power 3,
    .toughness 2,
    .ability (.keyword .flash),
    .ability (.keyword .flying),
    .ability (
      .triggered
        (.enter .this)
        (.chooseMode [
          .tap
            (.target
              1
              (.intersection [.permanent, .not (.cardType .land)])),
          .untap
            (.target
              1
              (.intersection [.permanent, .not (.cardType .land)]))]))
  ]).toCardDef
    (oracleText := "Flash\nFlying\nWhen this creature enters, choose one —\n• Tap target nonland permanent.\n• Untap target nonland permanent.")

def hydraulicHelper : CardDef :=
  artifactCreature "Hydraulic Helper" (ManaCost.ofGenericAndColor 1 .blue) #["Robot"] 2 3
    (oracleText := "Defender\n{T}: Add {U}. This mana can't be spent to cast a nonartifact spell.")
    (keywords := Keyword.defender)
    (activatedAbilities := #[activated (Effect.addBlueCantNonartifact) (ManaCost.empty) (tap := true)])

def iAmIronMan : CardDef :=
  instant "I Am Iron Man" (ManaCost.ofGenericAndColor 2 .blue)
    "Until end of turn, target artifact or creature becomes an artifact creature with base power and toughness 4/4 and gains flying.\nDraw a card."
    (spellEffect := some (Effect.becomeArtifactCreature44Flying))

def ironLadDivergingDestiny : CardDef :=
  card "Iron Lad, Diverging Destiny" #[.artifact, .creature] (ManaCost.ofGenericAndColor 2 .blue)
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Flying, vigilance\nYou may look at the top card of your library any time.\n{T}: Reveal the top card of your library. If it's an artifact card, draw a card.")
    (power := some 2)
    (toughness := some 2)
    (keywords := (Keyword.flying).merge Keyword.vigilance)
    (mayLookAtTopAnytime := true)
    (activatedAbilities := #[activated (Effect.revealTopDrawIfArtifact) (ManaCost.empty) (tap := true)])

def ironheartCleverChampion : CardDef :=
  artifactCreature "Ironheart, Clever Champion" (ManaCost.ofGenericAndColor 4 .blue) #["Human", "Hero"] 3 4
    (oracleText := "Improvise (Your artifacts can help cast this spell. Each artifact you tap after you're done activating mana abilities pays for {1}.)\nFlying\nNoncreature spells you cast have improvise.")
    (keywords := Keyword.flying)
    (staticAbilities := #[.improvise, .noncreatureSpellsHaveImprovise])
    (legendary := true)

def justiceVanceAstrovik : CardDef :=
  legendaryCreature "Justice, Vance Astrovik" (ManaCost.ofGenericAndColor 2 .blue) #["Mutant", "Hero"] 2 2
    (oracleText := "Flying\nWhen Justice enters, return up to one target nonland, nontoken permanent to its owner's hand.\nWhenever another nonland permanent you control is returned to its owner's hand, put a +1/+1 counter on Justice.")
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onEnter Effect.enterReturnNonlandNontoken, .onWatch Effect.watchJusticeBounce])

def kangTheConqueror : CardDef :=
  legendaryCreature "Kang the Conqueror" (ManaCost.ofGenericAndColors 2 [.blue, .blue]) #["Human", "Villain"] 4 5
    (oracleText := "Flying\nPower-up — {5}{U}{U}{U}: Put a +1/+1 counter on Kang. Take an extra turn after this one. During that turn, power-up abilities can't be activated. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)")
    (keywords := Keyword.flying)
    (activatedAbilities := #[activated (Effect.plusOneAndExtraTurn) (ManaCost.ofGenericAndColors 5 [.blue, .blue, .blue]) (powerUp := true)])

def kidLoki : CardDef :=
  legendaryCreature "Kid Loki" (ManaCost.ofColor .blue) #["God", "Hero", "Villain"] 1 1
    (oracleText := "Each creature you control that you've put one or more +1/+1 counters on this turn has hexproof.\nWhenever you draw your second card each turn, put a +1/+1 counter on Kid Loki.")
    (triggeredAbilities := #[.onDrawSecondPlusOne])
    (staticAbilities := #[StaticAbility.hexproofIfPlusOneThisTurn])

def leaderSuperGenius : CardDef :=
  legendaryCreature "Leader, Super-Genius" (ManaCost.ofGenericAndColors 2 [.blue, .blue]) #["Gamma", "Scientist", "Villain"] 1 3
    (oracleText := "If a creature you control would connive, instead you draw a card, then that creature connives.\nAt the beginning of combat on your turn, target creature you control connives. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on that creature.)")
    (triggeredAbilities := #[.onCombatTargetYouControlConnives])
    (staticAbilities := #[StaticAbility.extraDrawOnConnive])

def lokiGodOfMischief : CardDef :=
  legendaryCreature "Loki, God of Mischief" (ManaCost.ofGenericAndColor 1 .blue) #["God", "Sorcerer", "Villain"] 2 1
    (oracleText := "Whenever a player or permanent becomes the target of an ability you control, draw a card. This ability triggers only once each turn.")
    (triggeredAbilities := #[.onWatch Effect.watchYouTargetDrawOnce])

def misterFantasticReedRichards : CardDef :=
  legendaryCreature "Mister Fantastic, Reed Richards" (ManaCost.ofGenericAndColor 3 .blue) #["Human", "Scientist", "Hero"] 2 4
    (oracleText := "Reach\nWhenever one or more tokens you control enter, you may draw a card.")
    (keywords := Keyword.reach)
    (triggeredAbilities := #[.onWatch Effect.watchTokensEnterMayDraw])

def msMarvelKamalaKhan : CardDef :=
  legendaryCreature "Ms. Marvel, Kamala Khan" (ManaCost.ofGenericAndColor 2 .blue) #["Mutant", "Inhuman", "Hero"] 1 4
    (oracleText := "Reach, vigilance\nYou have no maximum hand size.\nEmbiggen Fist — Whenever you cast a spell that targets a creature you control, draw a card. Until end of turn, Ms. Marvel gains \"Ms. Marvel's base power is equal to the number of cards in your hand.\"")
    (keywords := (Keyword.reach).merge Keyword.vigilance)
    (triggeredAbilities := #[.onCasting Effect.castingDrawPowerEqualHand])
    (staticAbilities := #[.noMaximumHandSize])

def multiversalIncursion : CardDef :=
  sorcery "Multiversal Incursion" (ManaCost.ofGenericAndColors 5 [.blue, .blue])
    "For each nontoken creature you control, create a token that's a copy of that creature, except it isn't legendary."
    (spellEffect := some (Effect.copyNontokenCreaturesYouControl))

def namorTheSubMariner : CardDef :=
  card "Namor the Sub-Mariner" #[.creature] (ManaCost.ofGenericAndColors 1 [.blue, .blue])
    (supertypes := #[.legendary])
    (subtypes := #["Mutant", "Merfolk", "Villain"])
    (oracleText := "Flying\nNamor's power is equal to the number of Merfolk you control.\nWhenever you cast a noncreature spell with one or more blue mana symbols in its mana cost, create that many 1/1 blue Merfolk creature tokens.")
    (toughness := some 4)
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onCasting Effect.castingMerfolkFromBlue])
    (staticAbilities := #[.powerEqualSubtypeYouControl "Merfolk"])

def pymParticles : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Pym Particles",
    .manaCost [.mono .blue],
    .type .sorcery,
    .actions [
      .continuous
        [
          .gainAbility
            (.target 1 (.intersection [.permanent, .cardType .creature]))
            (.keyword .vigilance),
          .forbid
            (.block
              .any
              (.target 1 (.intersection [.permanent, .cardType .creature])))]
        .endOfTurn,
      .draw (.controller .this) 1]
  ]).toCardDef
    (oracleText := "Target creature gains vigilance until end of turn and can't be blocked this turn.\nDraw a card.")

def rewriteHistory : CardDef :=
  enchantment "Rewrite History" (ManaCost.ofGenericAndColor 2 .blue)
    "Whenever one or more creatures you control become tapped, draw a card, then discard a card and put a plan counter on this enchantment.\nWhen the fourth plan counter is put on this enchantment, sacrifice it. When you do, return up to two target instant and/or sorcery cards from your graveyard to your hand."
    (subtypes := #["Plan"])
    (triggeredAbilities := #[.onCreaturesYouControlBecomeTappedLootAndPlan, .onFourthPlanReturnInstants])

def secretInvasion : CardDef :=
  enchantment "Secret Invasion" (ManaCost.ofGenericAndColors 1 [.blue, .blue])
    "Enchant creature you control\nWhen this Aura enters, exile up to one target creature other than enchanted creature until this Aura leaves the battlefield. Enchanted creature becomes a copy of that creature until this Aura leaves the battlefield.\nEnchanted creature has ward {2}."
    (subtypes := #["Aura"])
    (triggeredAbilities := #[.onEnterExileOtherCopyEnchanted])
    (staticAbilities := #[StaticAbility.enchantedCreatureHasWard 2])

def sHIELDDeploymentDrone : CardDef :=
  artifactCreature "S.H.I.E.L.D. Deployment Drone" (ManaCost.ofGenericAndColor 2 .blue) #["Robot"] 2 2
    (oracleText := "Flying\nWhen this creature enters, create a 1/1 white Soldier creature token.")
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onEnterCreateTokens .soldier11white 1])

def sHIELDFlyingCar : CardDef :=
  artifact "S.H.I.E.L.D. Flying Car" (ManaCost.ofGenericAndColor 2 .blue)
    "Flash\nFlying\nWhen this Vehicle enters, exile up to one target creature you control. Return that card to the battlefield under its owner's control at the beginning of the next end step.\nCrew 1"
    (subtypes := #["Vehicle"])
    (power := some 3)
    (toughness := some 3)
    (keywords := (Keyword.flash).merge Keyword.flying)
    (crew := some 1)
    (triggeredAbilities := #[.onEnterExileCreatureReturnEndStep])

def shuriWakandanInventor : CardDef :=
  legendaryCreature "Shuri, Wakandan Inventor" (ManaCost.ofGenericAndColor 1 .blue) #["Human", "Artificer", "Hero"] 2 1
    (oracleText := "Artifact spells you cast cost {1} less to cast.\n{1}, {T}: Target artifact you control becomes a copy of a second target artifact you control until end of turn, except it isn't legendary. Activate only as a sorcery.")
    (staticAbilities := #[.typeSpellsCostLess .artifact 1])
    (activatedAbilities := #[activated (Effect.copyArtifactYouControlNotLegendary) (ManaCost.ofGeneric 1) (tap := true) (onlyAsSorcery := true)])

def statureSizeShifter : CardDef :=
  legendaryCreature "Stature, Size Shifter" (ManaCost.ofColor .blue) #["Human", "Hero"] 1 1
    (oracleText := "Stature can't be blocked if her power is 1 or less.\nPower-up — {X}{U}{U}: Put X +1/+1 counters on Stature. (Activate each power-up ability only once. Reduce the cost by her mana cost if she entered this turn.)")
    (staticAbilities := #[StaticAbility.cantBeBlockedIfPowerAtMost 1])
    (activatedAbilities := #[activated (Effect.plusOneX) ({ symbols := #[.x, .colored .blue, .colored .blue] }) (powerUp := true)])

def superIntelligence : CardDef :=
  enchantment "Super Intelligence" (ManaCost.ofColor .blue)
    "Enchant creature\nAt the beginning of the upkeep of enchanted creature's controller, that player draws a card."
    (subtypes := #["Aura"])
    (triggeredAbilities := #[.onStep Effect.stepEnchantedControllerDraws])

def superSuit : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Super Suit",
    .manaCost [.generic 1, .mono .blue],
    .type .artifact,
    .subtype .equipment,
    .ability (.keyword .flash),
    .ability (
      .triggered
        (.enter .this)
        (.sequence [
          .attach
            .this
            (.target
              1
              (.intersection [
                .permanent,
                .cardType .creature,
                .controlled (.controller .this)])),
          .untap (.targetReference 1)])),
    .ability (.static (.addPowerToughness (.hostOf .this) 1 2)),
    .ability (.keywordWithCost .equip [.mana [.generic 2]])
  ]).toCardDef
    (oracleText := "Flash\nWhen this Equipment enters, attach it to target creature you control. Untap that creature.\nEquipped creature gets +1/+2.\nEquip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)")

def thirstForKnowledge : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Thirst for Knowledge",
    .manaCost [.generic 2, .mono .blue],
    .type .instant,
    .actions [
      .draw (.controller .this) 3,
      .playerSelectAction
        (.controller .this)
        (.range 1 1)
        [
          .discard (.intersection [.cardType .artifact]) 1,
          .discard (.controller .this) 2]]
  ]).toCardDef
    (oracleText := "Draw three cards. Then discard two cards unless you discard an artifact card.")

def tonyStark : CardDef :=
  legendaryCreature "Tony Stark" (ManaCost.ofGenericAndColor 1 .blue) #["Human", "Artificer", "Hero"] 1 3
    (oracleText := "{1}, {T}: Look at the top four cards of your library. You may reveal an artifact card from among them and put it into your hand. Put the rest on the bottom of your library in a random order.\n{4}{U}{R}: Transform Tony Stark. Activate only as a sorcery.")
    (activatedAbilities := #[activated (Effect.lookAtTopRevealArtifact 4) (ManaCost.ofGeneric 1) (tap := true), activated (Effect.transform) (ManaCost.ofGenericAndColors 4 [.blue, .red]) (onlyAsSorcery := true)])
    (otherFace := some theInvincibleIronMan)

def tricksterSStratagem : CardDef :=
  sorcery "Trickster's Stratagem" (ManaCost.ofGenericAndColor 3 .blue)
    "The owner of target creature an opponent controls puts it into their library second from the top or on the bottom. Then up to one target creature you control connives. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on that creature.)"
    (spellEffect := some (Effect.ownerPutsLibraryThenConnive))

def weSayTheeNay : CardDef :=
  card "We Say Thee Nay!" #[.instant] (ManaCost.ofGenericAndColor 1 .blue)
    (subtypes := #["Arcane"])
    (oracleText := "Teamwork 2 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 2 or more.)\nCounter target spell unless its controller pays {2}. Counter that spell unless its controller pays {4} instead if this spell was cast using teamwork.")
    (teamwork := some 2)
    (spellEffect := some (Effect.counterUnlessPaysTeamwork 2 4))

def wiccanRisingMagician : CardDef :=
  legendaryCreature "Wiccan, Rising Magician" (ManaCost.ofGenericAndColor 4 .blue) #["Mutant", "Warlock", "Hero"] 4 4
    (oracleText := "Flying\nWhenever you cast a noncreature spell, exile another target nonland, nontoken permanent. Return that card to the battlefield under its owner's control at the beginning of the next end step.")
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onCasting Effect.castingExileFlicker])

def theWondrousWasp : CardDef :=
  legendaryCreature "The Wondrous Wasp" (ManaCost.ofGenericAndColor 1 .blue) #["Human", "Hero"] 2 1
    (oracleText := "Flash\nFlying\nWasp's Sting — When The Wondrous Wasp enters, tap up to one target creature. It loses all abilities for as long as The Wondrous Wasp remains on the battlefield.")
    (keywords := (Keyword.flash).merge Keyword.flying)
    (triggeredAbilities := #[.onEnter Effect.enterTapLoseAbilitiesWhileSource])

def agentsOfHYDRA : CardDef :=
  creature "Agents of HYDRA" (ManaCost.ofGenericAndColor 1 .black) #["Human", "Spy", "Villain"] 1 1
    (oracleText := "When this creature dies, create a 2/1 black Villain creature token with menace. (It can't be blocked except by two or more creatures.)")
    (triggeredAbilities := #[.onDiesCreateTokens .villain21menace 1])

def arnimZolaBioFanatic : CardDef :=
  artifactCreature "Arnim Zola, Bio-Fanatic" (ManaCost.ofGenericAndColor 2 .black) #["Scientist", "Villain"] 2 3
    (oracleText := "{3}, {T}: Create a tapped 2/1 black Villain creature token with menace. Activate only if there are two or more creature cards in your graveyard. (It can't be blocked except by two or more creatures.)")
    (activatedAbilities := #[activated (Effect.createTappedTokens .villain21menace 1) (ManaCost.ofGeneric 3) (tap := true)
      (onlyIfGyCreaturesAtLeast := 2)])
    (legendary := true)

def baronHelmutZemo : CardDef :=
  legendaryCreature "Baron Helmut Zemo" (ManaCost.ofColors [.black, .black, .black]) #["Human", "Noble", "Villain"] 3 3
    (oracleText := "Whenever you cast a black spell from your hand, Baron Helmut Zemo connives.\nBoast — Exile any number of black cards from your graveyard with fifteen or more black mana symbols among their mana costs: Copy those exiled cards. You may cast up to three of the copies without paying their mana costs. (Activate only if this creature attacked this turn and only once each turn.)")
    (triggeredAbilities := #[.onYouCastColorFromHandConnive .black])
    (staticAbilities := #[StaticAbility.boast])

def baronStruckerHYDRAOverlord : CardDef :=
  legendaryCreature "Baron Strucker, HYDRA Overlord" (ManaCost.ofGenericAndColor 2 .black) #["Human", "Villain"] 2 2
    (oracleText := "Villain spells you cast cost {1} less to cast.\nWhenever another Villain you control enters, you may have it connive. Do this only once each turn. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on that creature.)")
    (triggeredAbilities := #[.onWatch Effect.watchVillainConniveOnce])
    (staticAbilities := #[StaticAbility.subtypeSpellsCostLess "Villain" 1])

def blackWidowSuperSpy : CardDef :=
  legendaryCreature "Black Widow, Super Spy" (ManaCost.ofGenericAndColor 1 .black) #["Human", "Spy", "Hero"] 2 1
    (oracleText := "Menace\nWhenever Black Widow deals combat damage to a player, that player exiles cards from the top of their library until they exile a nonland card. You may put a +1/+1 counter on Black Widow. If you don't, you may cast the exiled nonland card until end of turn and mana of any type can be spent to cast that spell.")
    (keywords := Keyword.menace)
    (triggeredAbilities := #[.onWatch Effect.watchCombatDamageExileUntilNonland])

def constructACosmicCube : CardDef :=
  enchantment "Construct a Cosmic Cube" (ManaCost.ofGenericAndColor 2 .black)
    "Whenever you draw your second card each turn, create a 2/1 black Villain creature token with menace and put a plan counter on this enchantment.\nWhen the seventh plan counter is put on this enchantment, sacrifice it. When you do, you control target opponent during their next turn. (You see all cards that player could see and make all decisions for them.)"
    (subtypes := #["Plan"])
    (triggeredAbilities := #[.onYouDrawSecondCreateVillainAndPlan, .onSeventhPlanControlOpponent])

def crossbonesMaliciousMercenary : CardDef :=
  legendaryCreature "Crossbones, Malicious Mercenary" (ManaCost.ofGenericAndColor 3 .black) #["Human", "Mercenary", "Villain"] 3 3
    (oracleText := "Deathtouch\nWhenever another Villain you control enters, put a +1/+1 counter on Crossbones. He deals 2 damage to each opponent. This ability triggers only once each turn.")
    (keywords := Keyword.deathtouch)
    (triggeredAbilities := #[.onWatch Effect.watchVillainPlusOneDamageOnce])

def cruelAlliance : CardDef :=
  sorcery "Cruel Alliance" (ManaCost.ofGenericAndColor 2 .black)
    "Teamwork 2 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 2 or more.)\nExile target creature with mana value 3 or less. If this spell was cast using teamwork, instead exile target creature and you gain 3 life."
    (teamwork := some 2)
    (spellEffect := some (Effect.exileCreatureMvAtMostOrAnyIfTeamwork 3 3))

def darkDeed : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Dark Deed",
    .manaCost [.generic 1, .mono .black],
    .type .instant,
    .actions [
      .continuous
        [.addPowerToughness
          (.target 1 (.intersection [.permanent, .cardType .creature]))
          (-4) (-4)]
        .endOfTurn]
  ]).toCardDef
    (oracleText := "Target creature gets -4/-4 until end of turn.")

def decoyPloy : CardDef :=
  instant "Decoy Ploy" (ManaCost.ofGenericAndColor 1 .black)
    "Choose one or both —\n• Return target Villain card from your graveyard to your hand.\n• Return target Hero card from your graveyard to your hand."
    (spellModes := #[(Effect.returnGySubtypeToHand "Villain"), (Effect.returnGySubtypeToHand "Hero")])
    (chooseOneOrBoth := true)

def doctorDoom : CardDef :=
  legendaryCreature "Doctor Doom" (ManaCost.ofGenericAndColors 4 [.black, .black]) #["Human", "Scientist", "Villain"] 3 3
    (oracleText := "When Doctor Doom enters, create two 3/3 colorless Robot Villain artifact creature tokens named Doombot.\nAs long as you control an artifact creature or a Plan, Doctor Doom has indestructible.\nAt the beginning of your end step, you draw a card and lose 1 life.")
    (triggeredAbilities := #[.onEnterCreateTokens .doombot 2, .onYourEndStepDrawLoseLife])
    (staticAbilities := #[StaticAbility.indestructibleIfArtifactCreatureOrPlan])

def doomReignsSupreme : CardDef :=
  enchantment "Doom Reigns Supreme" (ManaCost.ofGenericAndColor 1 .black)
    "Whenever a Villain you control enters, each opponent loses 1 life and you gain 1 life. Put a plan counter on this enchantment.\nWhen the fifth plan counter is put on this enchantment, sacrifice it. When you do, target opponent exiles the top five cards of their library. You may cast up to two spells from among the exiled cards without paying their mana costs."
    (subtypes := #["Plan"])
    (triggeredAbilities := #[.onVillainYouControlEntersDrainAndPlan 1, .onFifthPlanExileTopCast])

def elektraDaughterOfTheHand : CardDef :=
  legendaryCreature "Elektra, Daughter of the Hand" (ManaCost.ofGenericAndColors 2 [.black, .black]) #["Human", "Ninja", "Villain"] 3 3
    (oracleText := "Sneak {1}{B}{B} (You may cast this spell for {1}{B}{B} if you also return an unblocked attacker you control to hand during the declare blockers step. She enters tapped and attacking.)\nWhen Elektra enters, destroy target creature an opponent controls with power 3 or less.")
    (triggeredAbilities := #[.onEnter (Effect.enterDestroy (.oppCreaturePowerAtMost 3))])
    (staticAbilities := #[StaticAbility.sneak (ManaCost.ofGenericAndColors 1 [.black, .black])])

def grimReaperLethalLegionnaire : CardDef :=
  legendaryCreature "Grim Reaper, Lethal Legionnaire" (ManaCost.ofGenericAndColor 3 .black) #["Human", "Villain"] 3 4
    (oracleText := "Whenever Grim Reaper attacks, you may pay {3}{B}. When you do, return target creature card from your graveyard to the battlefield tapped and attacking with a finality counter on it. (If a creature with a finality counter on it would die, exile it instead.)")
    (triggeredAbilities := #[.onThisAttack Effect.thisAttackPayReturnAttacking])

def hourOfDefeat : CardDef :=
  instant "Hour of Defeat" (ManaCost.ofGenericAndColor 3 .black)
    "Destroy target creature. Surveil 1. (Look at the top card of your library. You may put it into your graveyard.)"
    (spellEffect := some (Effect.destroyCreatureSurveil))

def hYDRAInfiltration : CardDef :=
  enchantment "HYDRA Infiltration" (ManaCost.ofGenericAndColor 3 .black)
    "When this enchantment enters, target opponent discards two cards.\nWhenever a creature you control attacks alone, target opponent loses 1 life and you gain 1 life."
    (triggeredAbilities := #[.onEnterTargetOpponentDiscards 2, .onWatch Effect.watchAttacksAloneDrain])

def hYDRATroopers : CardDef :=
  creature "HYDRA Troopers" (ManaCost.ofGenericAndColor 2 .black) #["Human", "Soldier", "Villain"] 3 2
    (oracleText := "When this creature enters, create a tapped 2/1 black Villain creature token with menace if there are two or more creature cards in your graveyard. Otherwise, mill two cards. (Put the top two cards of your library into your graveyard.)")
    (triggeredAbilities := #[.onEnterVillainIfGyElseMill])

def kingpinSEnforcers : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Kingpin's Enforcers",
    .manaCost [.generic 2, .mono .black],
    .type .creature,
    .subtype .human,
    .subtype .villain,
    .power 2,
    .toughness 3,
    .ability (.keyword .lifelink),
    .ability
      (.activated
        [.mana [.generic 2, .mono .black],
          .sacrificeCount
            (.intersection [
              .permanent,
              .union [.cardType .artifact, .cardType .creature]])
            1]
        (.draw (.controller .this) 1))
  ]).toCardDef
    (oracleText := "Lifelink\n{2}{B}, Sacrifice an artifact or creature: Draw a card.")

def klawSonicSubjugator : CardDef :=
  legendaryCreature "Klaw, Sonic Subjugator" (ManaCost.ofGenericAndColor 2 .black) #["Human", "Rogue", "Villain"] 2 2
    (oracleText := "Sonic Attack — When Klaw enters, target player reveals a number of cards from their hand equal to one plus the number of creature cards in your graveyard. You choose one of them. That player discards that card.")
    (triggeredAbilities := #[.onEnter Effect.enterRevealDiscardFromHand])

def madameMasque : CardDef :=
  legendaryCreature "Madame Masque" (ManaCost.ofGenericAndColor 4 .black) #["Human", "Villain"] 3 2
    (oracleText := "When Madame Masque enters, she connives. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on this creature.)\nWhenever you draw your second card each turn, create a 2/1 black Villain creature token with menace. (It can't be blocked except by two or more creatures.)")
    (triggeredAbilities := #[.onEnterConnive, .onYouDrawSecondCreateTokens .villain21menace])

def theMastersOfEvil : CardDef :=
  legendaryCreature "The Masters of Evil" (ManaCost.ofGenericAndColor 5 .black) #["Human", "Villain"] 5 6
    (oracleText := "Other Villains you control get +2/+1.\n{1}{B}, Discard this card: Search your library for a Plan card, reveal it, put it into your hand, then shuffle.")
    (staticAbilities := #[StaticAbility.otherCreaturesGet #["Villain"] 2 1])
    (activatedAbilities := #[activated (Effect.searchLandTypeToHand "Plan") (ManaCost.ofGenericAndColor 1 .black)
      (discardSource := true) (activateFromHand := true)])

def mODOK : CardDef :=
  artifactCreature "M.O.D.O.K." (ManaCost.ofGenericAndColors 3 [.black, .black]) #["Villain"] 2 2
    (oracleText := "Flying, lifelink\nMental Organism — Pay 3 life: M.O.D.O.K. connives. Activate only during your turn. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on this creature.)\nDesigned Only for Killing — Creatures your opponents control get -1/-1.")
    (keywords := (Keyword.flying).merge Keyword.lifelink)
    (staticAbilities := #[StaticAbility.opponentsCreaturesGet (-1) (-1)])
    (activatedAbilities := #[activated (Effect.connive) (payLife := 3) (onlyDuringYourTurn := true)])
    (legendary := true)

def moonstoneHarshMistress : CardDef :=
  legendaryCreature "Moonstone, Harsh Mistress" (ManaCost.ofGenericAndColor 3 .black) #["Human", "Doctor", "Villain"] 2 4
    (oracleText := "Flying\nWhenever you discard a card, you may exile that card from your graveyard. If you do, until the end of your next turn, you may play that card.")
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onResource Effect.resourceDiscardExilePlay])

def ninjaOfTheHand : CardDef :=
  creature "Ninja of the Hand" (ManaCost.ofGenericAndColor 2 .black) #["Human", "Ninja", "Villain"] 2 2
    (oracleText := "Deathtouch\nPower-up — {4}{B}: Each opponent discards a card. Put a +1/+1 counter on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)")
    (keywords := Keyword.deathtouch)
    (activatedAbilities := #[activated (Effect.eachOppDiscardThenPlusOne) (ManaCost.ofGenericAndColor 4 .black) (powerUp := true)])

def projectDeathlokSoldier : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Project Deathlok Soldier",
    .manaCost [.mono .black],
    .type .artifact,
    .type .creature,
    .subtype .zombie,
    .subtype .soldier,
    .power 1,
    .toughness 2,
    .ability (
      .activated
        [.mana [.generic 2, .mono .black]]
        (.returnToHand (.intersection [.inGraveyard, .source .this])))
  ]).toCardDef
    (oracleText := "{2}{B}: Return this card from your graveyard to your hand.")

def redRoomRecruit : CardDef :=
  creature "Red Room Recruit" (ManaCost.ofGenericAndColor 1 .black) #["Human", "Spy", "Villain"] 1 2
    (oracleText := "When this creature enters, it connives. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on this creature.)")
    (triggeredAbilities := #[.onEnterConnive])

def robotDomination : CardDef :=
  enchantment "Robot Domination" (ManaCost.ofGenericAndColor 3 .black)
    "Whenever one or more creature cards are put into your graveyard from anywhere, you draw a card, lose 1 life, and put a plan counter on this enchantment.\nWhen the third plan counter is put on this enchantment, sacrifice it and create three 2/2 colorless Robot Villain artifact creature tokens."
    (subtypes := #["Plan"])
    (triggeredAbilities := #[.onCreatureCardsToGyDrawLoseLifeAndPlan, .onThirdPlanCreateRobots])

def roninShadowStalker : CardDef :=
  legendaryCreature "Ronin, Shadow Stalker" (ManaCost.ofGenericAndColor 2 .black) #["Human", "Rogue", "Hero"] 3 3
    (oracleText := "Pay 2 life: Add two mana of any one color. Spend this mana only to cast Equipment spells or activate equip abilities. Activate only once each turn.\n{T}, Sacrifice an Equipment attached to Ronin: Target creature gets -4/-4 until end of turn. Activate only as a sorcery.")
    (activatedAbilities := #[activated (Effect.addTwoAnyColorEquipment) (payLife := 2) (onceEachTurn := true),
      activated (Effect.targetGets (-4) (-4)) (tap := true) (sacrificeEquipmentAttachedToSource := true)
        (onlyAsSorcery := true)])

def roxxonBrutes : CardDef :=
  creature "Roxxon Brutes" (ManaCost.ofGenericAndColor 4 .black) #["Human", "Berserker", "Villain"] 4 4
    (oracleText := "Menace (This creature can't be blocked except by two or more creatures.)\nWhenever you draw your second card each turn, put a +1/+1 counter on target creature.\nBasic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)")
    (keywords := Keyword.menace)
    (triggeredAbilities := #[.onResource Effect.resourceSecondDrawPlusOneTarget])
    (activatedAbilities := #[typecyclingAbility "Basic land" (ManaCost.ofGeneric 2)])

def stolenStarkTech : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Stolen Stark Tech",
    .manaCost [.generic 1, .mono .black],
    .type .artifact,
    .subtype .equipment,
    .ability (.keyword .flash),
    .ability
      (.triggered
        (.enter .this)
        (.sequence [
          .attach
            .this
            (.target
              1
              (.intersection [
                .permanent,
                .cardType .creature,
                .controlled (.controller .this)])),
          .continuous
            [.gainAbility (.hostOf .this) (.keyword .indestructible)]
            .endOfTurn])),
    .ability (.static (.addPowerToughness (.hostOf .this) 1 0)),
    .ability (.keywordWithCost .equip [.mana [.generic 1]])
  ]).toCardDef
    (oracleText := "Flash\nWhen this Equipment enters, attach it to target creature you control. That creature gains indestructible until end of turn. (Damage and effects that say \"destroy\" don't destroy it.)\nEquipped creature gets +1/+0.\nEquip {1} ({1}: Attach to target creature you control. Equip only as a sorcery.)")

def superSkrull : CardDef :=
  legendaryCreature "Super-Skrull" (ManaCost.ofGenericAndColors 1 [.black, .black, .black]) #["Skrull", "Shapeshifter", "Villain"] 4 5
    (oracleText := "Flying\n{2}{W}: Create a 0/4 colorless Wall creature token with defender.\n{3}{G}: Super-Skrull gets +4/+4 until end of turn.\n{4}{R}: Super-Skrull deals 4 damage to target creature.\n{5}{U}: Target player draws four cards.")
    (keywords := Keyword.flying)
    (activatedAbilities := #[activated (Effect.abilityCreateTokens .wall04defender 1) (ManaCost.ofGenericAndColor 2 .white), activated (Effect.sourceGets 4 4) (ManaCost.ofGenericAndColor 3 .green), activated (Effect.dealDamageToTargetCreature 4) (ManaCost.ofGenericAndColor 4 .red), activated (Effect.abilityTargetPlayerDraw 4) (ManaCost.ofGenericAndColor 5 .blue)])

def swordsmanSharpScoundrel : CardDef :=
  legendaryCreature "Swordsman, Sharp Scoundrel" (ManaCost.ofGenericAndColor 1 .black) #["Human", "Hero", "Villain"] 2 2
    (oracleText := "Whenever another Villain you control enters, attach up to one target Equipment you control to target creature you control.\nWhenever an equipped creature you control attacks, it connives. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on that creature.)")
    (triggeredAbilities := #[.onWatch Effect.watchVillainAttachEquipment, .onEquippedCreatureYouControlAttacksConnive])

def thunderboltsConspiracy : CardDef :=
  enchantment "Thunderbolts Conspiracy" (ManaCost.ofGenericAndColor 3 .black)
    "Flash\nWhenever a Villain you control dies, return it to the battlefield under its owner's control with a finality counter on it. That creature is a Hero in addition to its other types. (If a creature with a finality counter on it would die, exile it instead.)"
    (keywords := Keyword.flash)
    (triggeredAbilities := #[.onDeath Effect.deathVillainReturnAsHero])

def tooEvilToStayDead : CardDef :=
  sorcery "Too Evil to Stay Dead" (ManaCost.ofGenericAndColor 2 .black)
    "Teamwork 4 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 4 or more.)\nChoose target creature card in your graveyard with mana value 4 or less. If this spell was cast using teamwork, instead choose target creature card in your graveyard. Return the chosen card to the battlefield."
    (teamwork := some 4)
    (spellEffect := some (Effect.returnGyCreatureMvAtMostOrAny 4))

def unlivingLegionnaire : CardDef :=
  creature "Unliving Legionnaire" (ManaCost.ofGenericAndColor 3 .black) #["Vampire", "Villain"] 3 2
    (oracleText := "Flying\nPower-up — {5}{B}{B}: Return up to one target creature card from your graveyard to your hand. Put two +1/+1 counters on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)")
    (keywords := Keyword.flying)
    (activatedAbilities := #[activated (Effect.returnGyCreatureThenPlusOne 2) (ManaCost.ofGenericAndColors 5 [.black, .black]) (powerUp := true)])

def visionsOfVillainy : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Visions of Villainy",
    .manaCost [.generic 2, .mono .black],
    .type .instant,
    .ability (
      .static
        (.if
          (.anySubtype (.controlled (.controller .this)) .villain)
          [.reduceCost .this [.mana [.generic 1]]])),
    .actions [
      .draw (.controller .this) 2,
      .loseLife (.controller .this) 2]
  ]).toCardDef
    (oracleText := "This spell costs {1} less to cast if you control a Villain.\nYou draw two cards and lose 2 life.")

def whiplashVengefulEngineer : CardDef :=
  card "Whiplash, Vengeful Engineer" #[.creature] (ManaCost.ofColor .black)
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Artificer", "Villain"])
    (oracleText := "Whiplash enters tapped.\nWhenever Whiplash attacks, if he's equipped, each opponent loses X life and you gain X life, where X is the number of Equipment attached to him.")
    (power := some 2)
    (toughness := some 2)
    (entersTapped := true)
    (triggeredAbilities := #[.onThisAttack Effect.thisAttackEquippedDrain])

def widowSBite : CardDef :=
  instant "Widow's Bite" (ManaCost.ofGenericAndColor 1 .black)
    "Teamwork 3 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 3 or more.)\nChoose one. If this spell was cast using teamwork, choose both instead.\n• Target creature gains deathtouch until end of turn.\n• Target creature gets -2/-2 until end of turn."
    (teamwork := some 3)
    (spellModes := #[(Effect.grantDeathtouch), (Effect.pump (-2) (-2))])
    (chooseBothIfTeamwork := true)

def yellowjacketHeartlessMarauder : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Yellowjacket, Heartless Marauder",
    .manaCost [.generic 1, .mono .black],
    .type .creature,
    .supertype .legendary,
    .subtype .human,
    .subtype .rogue,
    .subtype .villain,
    .power 1,
    .toughness 2,
    .ability (.keyword .flying),
    .ability (
      .triggered
        (.enter
          (.intersection [
            .not .this,
            .permanent,
            .subtype .villain,
            .controlled (.controller .this)]))
        (.continuous
          [
            .addPowerToughness (.source .this) 1 0,
            .gainAbility (.source .this) (.keyword .lifelink)]
          .endOfTurn))
  ]).toCardDef
    (oracleText := "Flying\nWhenever another Villain you control enters, Yellowjacket gets +1/+0 and gains lifelink until end of turn.")

def avengersDisassembled : CardDef :=
  sorcery "Avengers Disassembled" (ManaCost.ofGenericAndColors 1 [.red, .red])
    "Choose one or both —\n• Avengers Disassembled deals 3 damage to each creature.\n• Destroy target land. Its controller may search their library for a basic land card, put it onto the battlefield tapped, then shuffle."
    (spellModes := #[(Effect.dealDamageToEachCreature 3), (Effect.destroyLandSearchBasic)])
    (chooseOneOrBoth := true)

def blazingCrescendo : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Blazing Crescendo",
    .manaCost [.generic 1, .mono .red],
    .type .instant,
    .actions [
      .continuous
        [
          .addPowerToughness
            (.target 1 (.intersection [.permanent, .cardType .creature]))
            3 1]
        .endOfTurn,
      .actionId 1 (.exile (.topOfLibrary (.controller .this))),
      .continuous
        [.canPlay (.controller .this) (.wasCreatedByAction 1)]
        (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])]
  ]).toCardDef
    (oracleText := "Target creature gets +3/+1 until end of turn.\nExile the top card of your library. Until the end of your next turn, you may play that card.")

def crimsonOperative : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Crimson Operative",
    .manaCost [.generic 3, .mono .red],
    .type .artifact,
    .type .creature,
    .subtype .human,
    .subtype .villain,
    .power 3,
    .toughness 2,
    .ability (.keyword .prowess),
    .ability (
      .triggered
        (.enter .this)
        (.sequence [
          .actionId 1 (.exile (.topOfLibrary (.controller .this))),
          .continuous
            [.canPlay (.controller .this) (.wasCreatedByAction 1)]
            (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])]))
  ]).toCardDef
    (oracleText := "Prowess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn.)\nWhen this creature enters, exile the top card of your library. Until the end of your next turn, you may play that card.")

def deathToOurEnemies : CardDef :=
  enchantment "Death to Our Enemies" (ManaCost.ofGenericAndColor 2 .red)
    "Whenever you cast a noncreature spell, create a tapped Treasure token and put a plan counter on this enchantment.\nWhen the fourth plan counter is put on this enchantment, sacrifice it. When you do, it deals 7 damage divided as you choose among one or two targets."
    (subtypes := #["Plan"])
    (triggeredAbilities := #[.onCastNoncreatureTreasureAndPlan, .onFourthPlanDividedDamage])

def evilSThrall : CardDef :=
  sorcery "Evil's Thrall" (ManaCost.ofGenericAndColor 2 .red)
    "Gain control of target creature until end of turn. If you control a Villain with greater mana value than that creature, gain control of that creature until the end of your next turn instead. Untap that creature. It gains haste until end of turn."
    (spellEffect := some (Effect.gainControlUntilEotOrNextIfVillain))

def finFangFoom : CardDef :=
  legendaryCreature "Fin Fang Foom" (ManaCost.ofGenericAndColors 2 [.red, .red]) #["Alien", "Dragon", "Villain"] 3 5
    (oracleText := "Flying\nWhenever you cast an instant or sorcery spell that targets an artifact or land, copy that spell. You may choose new targets for the copy. Put two +1/+1 counters on Fin Fang Foom.")
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onCasting Effect.castingCopyIfArtifactOrLand])

def hawkeyeMasterMarksman : CardDef :=
  legendaryCreature "Hawkeye, Master Marksman" (ManaCost.ofGenericAndColor 1 .red) #["Human", "Archer", "Hero"] 2 2
    (oracleText := "Reach, first strike\nTrick Arrows — Whenever Hawkeye becomes tapped, you may pay {1} up to three times. When you do, choose up to that many —\n• Net — Target creature can't block this turn.\n• Explosive — Hawkeye deals 2 damage to target player.\n• Boomerang — Discard a card, then draw a card.")
    (keywords := (Keyword.reach).merge Keyword.firstStrike)
    (triggeredAbilities := #[.onWatch Effect.watchHawkeyeModes])

def hawkeyeYoungAvenger : CardDef :=
  legendaryCreature "Hawkeye, Young Avenger" (ManaCost.ofGenericAndColor 3 .red) #["Human", "Archer", "Hero"] 2 4
    (oracleText := "Reach\nIf a source you control would deal noncombat damage to an opponent or a permanent an opponent controls, instead it deals that much damage plus X, where X is Hawkeye's power.")
    (keywords := Keyword.reach)
    (staticAbilities := #[StaticAbility.noncombatDamagePlusSourcePower])

def hawkeyeSBow : CardDef :=
  equipment "Hawkeye's Bow" (ManaCost.ofColor .red)
    "Equipped creature gets +1/+0 and has reach.\nWhenever equipped creature becomes tapped, it deals 1 damage to each opponent.\nEquip {1}"
    (ManaCost.ofGeneric 1)
    (triggeredAbilities := #[.onWatch Effect.watchEquippedTappedDamage])
    (staticAbilities := #[StaticAbility.equippedCreatureGetsAndHas 1 0 Keyword.reach])

def hexMagic : CardDef :=
  card "Hex Magic" #[.sorcery] (ManaCost.ofGenericAndColor 2 .red)
    (subtypes := #["Arcane"])
    (oracleText := "Exile all the cards from your hand, then draw that many cards. Until the end of your next turn, you may play cards exiled this way.")
    (spellEffect := some (Effect.exileHandDrawPlayUntilNext))

def hireACrew : CardDef :=
  instant "Hire a Crew" (ManaCost.ofGenericAndColor 2 .red)
    "Create a 2/1 black Villain creature token with menace, then creatures you control get +1/+0 until end of turn. (A creature with menace can't be blocked except by two or more creatures.)"
    (spellEffect := some (Effect.createTokensThenTeamPump .villain21menace 1 1 0))

def hULKSMASH : CardDef :=
  instant "HULK SMASH!" (ManaCost.ofGenericAndColor 1 .red)
    "Teamwork 4 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 4 or more.)\nChoose one. If this spell was cast using teamwork, choose both instead.\n• Destroy target noncreature artifact.\n• Target creature you control deals damage equal to its power to target creature an opponent controls."
    (teamwork := some 4)
    (spellModes := #[(Effect.destroyNoncreatureArtifact), (Effect.creatureYouControlDealsPowerToOppCreature)])
    (chooseBothIfTeamwork := true)

def humanTorchJohnnyStorm : CardDef :=
  legendaryCreature "Human Torch, Johnny Storm" (ManaCost.ofGenericAndColor 2 .red) #["Human", "Hero"] 2 2
    (oracleText := "Flying\nWhenever you draw a card, if you control another Hero, Human Torch deals 1 damage to target opponent.\nPower-up — {6}{R}: Put three +1/+1 counters on Human Torch. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)")
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onResource Effect.resourceDrawIfAnotherHeroDamage])
    (activatedAbilities := #[powerUpAbility (Effect.putPlusOnePlusOneOnSource 3) (ManaCost.ofGenericAndColor 6 .red)])

def hYDRAAssaultRobot : CardDef :=
  (TraditionalCardDefinition.card [
    .name "HYDRA Assault Robot",
    .manaCost [.generic 1, .mono .red],
    .type .artifact,
    .type .creature,
    .subtype .robot,
    .subtype .villain,
    .power 1,
    .toughness 3,
    .ability (
      .triggered
        (.enter
          (.union [
            .intersection [
              .not .this,
              .permanent,
              .subtype .villain,
              .controlled (.controller .this)],
            .intersection [
              .not .this,
              .permanent,
              .cardType .artifact,
              .controlled (.controller .this)]]))
        (.dealDamage .this (.opponent (.controller .this)) 1))
  ]).toCardDef
    (oracleText := "Whenever another Villain and/or artifact you control enters, this creature deals 1 damage to target opponent.")

def ironFistLivingWeapon : CardDef :=
  legendaryCreature "Iron Fist, Living Weapon" (ManaCost.ofGenericAndColor 2 .red) #["Human", "Warrior", "Hero"] 2 3
    (oracleText := "Whenever you cast a spell that targets a creature you control, Iron Fist gains \"{T}: Iron Fist deals damage equal to his power to any other target\" until end of turn.")
    (triggeredAbilities := #[.onCasting Effect.castingIronFistTap])

def jessicaJonesPrivateEye : CardDef :=
  legendaryCreature "Jessica Jones, Private Eye" (ManaCost.ofGenericAndColor 2 .red) #["Human", "Detective", "Hero"] 2 3
    (oracleText := "{T}, Put a stun counter on Jessica Jones: Exile the top X cards of your library, where X is Jessica Jones's power. You may play those cards this turn. (If a permanent with a stun counter would become untapped, remove one from it instead.)")
    (activatedAbilities := #[activated (Effect.exileTopXPlayThisTurn) (tap := true) (putStunCounterOnSource := true)])

def kUnLunWarrior : CardDef :=
  (TraditionalCardDefinition.card [
    .name "K'un-Lun Warrior",
    .manaCost [.generic 1, .mono .red],
    .type .creature,
    .subtype .human,
    .subtype .warrior,
    .subtype .hero,
    .power 2,
    .toughness 2,
    .ability (
      .triggered
        (.enter .this)
        (.sequence [
          .optional
            (.actionId 1
              (.playerSelectAction
                (.controller .this)
                (.range 1 1)
                [
                  .sacrifice
                    (.intersection [
                      .permanent,
                      .cardType .artifact,
                      .controlled (.controller .this)]),
                  .discard (.controller .this) 1])),
          .if (.happened (.actionWithId 1) .gameStart) [.draw (.controller .this) 1]]))
  ]).toCardDef
    (oracleText := "When this creature enters, you may sacrifice an artifact or discard a card. If you do, draw a card.")

def kreeSentinel : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Kree Sentinel",
    .manaCost [.generic 4, .mono .red],
    .type .artifact,
    .type .creature,
    .subtype .kree,
    .subtype .robot,
    .subtype .villain,
    .power 5,
    .toughness 5,
    .ability (.keyword .reach),
    .ability
      (.keywordWithCost
        (.supertypeAndTypeCycling .basic .land)
        [.mana [.generic 2]])
  ]).toCardDef
    (oracleText := "Reach\nBasic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)")

def lightningStrike : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Lightning Strike",
    .manaCost [.generic 1, .mono .red],
    .type .instant,
    .actions [.dealDamage .this (.target 1 .all) 3]
  ]).toCardDef
    (oracleText := "Lightning Strike deals 3 damage to any target.")

def lokiLaufeyson : CardDef :=
  legendaryCreature "Loki Laufeyson" (ManaCost.ofGenericAndColor 1 .red) #["God", "Sorcerer", "Villain"] 2 1
    (oracleText := "{1}, {T}: When you next cast an instant or sorcery spell with mana value less than or equal to Loki's power this turn, copy that spell. You may choose new targets for the copy.\nPower-up — {4}{R}: Put two +1/+1 counters on Loki. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)")
    (activatedAbilities := #[activated (Effect.nextInstantSorceryCopyIfMvAtMostSourcePower) (ManaCost.ofGeneric 1) (tap := true), powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColor 4 .red)])

def machinesmithAutomaton : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Machinesmith Automaton",
    .manaCost [.generic 2, .mono .red],
    .type .artifact,
    .type .creature,
    .subtype .robot,
    .subtype .villain,
    .power 2,
    .toughness 2,
    .ability (.keyword .trample),
    .ability (
      .triggered
        (.enter
          (.intersection [
            .not .this,
            .permanent,
            .cardType .artifact,
            .controlled (.controller .this)]))
        (.putCounter (.source .this) .plusOnePlusOne 1))
  ]).toCardDef
    (oracleText := "Trample\nWhenever another artifact you control enters, put a +1/+1 counter on this creature.")

def mistyKnightHeroForHire : CardDef :=
  legendaryCreature "Misty Knight, Hero for Hire" (ManaCost.ofGenericAndColor 1 .red) #["Human", "Detective", "Hero"] 3 1
    (oracleText := "{2}, {T}, Discard a card: Draw a card for each card you've discarded this turn.")
    (activatedAbilities := #[activated (Effect.drawPerDiscardedThisTurn)
      (ManaCost.ofGeneric 2) (tap := true) (discardACard := true)])

def mjLnirHammerOfThor : CardDef :=
  artifact "Mjölnir, Hammer of Thor" (ManaCost.ofGenericAndColor 3 .red)
    "When Mjölnir enters, it deals 4 damage to up to one target creature.\nDouble all damage equipped creature would deal.\nEquip worthy {1} (A creature is worthy if it's a legendary non-Villain that's red and/or white.)\n{2}{R}, Discard this card: It deals 2 damage to each creature."
    (subtypes := #["Equipment"])
    (triggeredAbilities := #[.onEnter (Effect.enterDealDamageUpToOne 4)])
    (staticAbilities := #[StaticAbility.equippedDealsDoubleDamage])
    (activatedAbilities := #[equipWorthyAbility (ManaCost.ofGeneric 1),
      activated (Effect.abilityDealDamageToEachCreature 2) (ManaCost.ofGenericAndColor 2 .red)
        (discardSource := true) (activateFromHand := true)])
    (legendary := true)

def photonBlastBarrage : CardDef :=
  sorcery "Photon Blast Barrage" ({ symbols := #[.x, .colored .red, .colored .red] })
    "When you cast this spell, copy it X times. You may choose new targets for the copies.\nPhoton Blast Barrage deals 1 damage to target creature."
    (spellEffect := some (Effect.copyThisSpellXTimesThenDamage 1))

def quicksilverBrashBlur : CardDef :=
  legendaryCreature "Quicksilver, Brash Blur" (ManaCost.ofColor .red) #["Mutant", "Hero"] 1 1
    (oracleText := "If Quicksilver, Brash Blur is in your opening hand, you may begin the game with him on the battlefield.\nHaste\nPower-up — {4}{R}: Put a +1/+1 counter and a double strike counter on Quicksilver. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)")
    (keywords := Keyword.haste)
    (staticAbilities := #[StaticAbility.mayBeginOnBattlefield])
    (activatedAbilities := #[activated (Effect.plusOneAndDoubleStrikeCounter) (ManaCost.ofGenericAndColor 4 .red) (powerUp := true)])

def redHulk : CardDef :=
  legendaryCreature "Red Hulk" (ManaCost.ofGenericAndColors 4 [.red, .red]) #["Gamma", "Berserker", "Villain"] 6 7
    (oracleText := "Reach, trample\nEnrage — Whenever Red Hulk is dealt damage, put a +1/+1 counter on him. When you do, he deals damage equal to the number of +1/+1 counters on him to any other target.")
    (keywords := (Keyword.reach).merge Keyword.trample)
    (triggeredAbilities := #[.onWatch Effect.watchRedHulk])

def repulsorBlast : CardDef :=
  sorcery "Repulsor Blast" (ManaCost.ofGenericAndColor 3 .red)
    "Teamwork 2 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 2 or more.)\nRepulsor Blast deals 5 damage to target creature. If this spell was cast using teamwork, it also deals 2 damage to that creature's controller."
    (teamwork := some 2)
    (spellEffect := some (Effect.dealDamageThenControllerIfTeamwork 5 2))

def theScarletWitch : CardDef :=
  legendaryCreature "The Scarlet Witch" (ManaCost.ofGenericAndColor 2 .red) #["Mutant", "Warlock", "Hero"] 2 3
    (oracleText := "Instant and sorcery spells you cast with mana value 4 or greater cost {X} less to cast, where X is The Scarlet Witch's power.")
    (staticAbilities := #[StaticAbility.instantSorceryCostLessEqualPower])

def speedYoungAvenger : CardDef :=
  legendaryCreature "Speed, Young Avenger" (ManaCost.ofGenericAndColor 1 .red) #["Mutant", "Hero"] 2 2
    (oracleText := "Haste\nWhenever you cast a noncreature spell, you may pay {1}. When you do, target creature with haste can't be blocked this turn except by creatures with haste.")
    (keywords := Keyword.haste)
    (triggeredAbilities := #[.onCasting Effect.castingMayPayHasteUnblockable])

def starkIndustriesExecutive : CardDef :=
  creature "Stark Industries Executive" (ManaCost.ofColor .red) #["Human", "Advisor"] 1 2
    (oracleText := "{2}, {T}: Create a Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")")
    (activatedAbilities := #[activated (Effect.abilityCreateTokens .treasure 1) (ManaCost.ofGeneric 2) (tap := true)])

def superSpeed : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Super Speed",
    .manaCost [.mono .red],
    .type .enchantment,
    .subtype .aura,
    .ability (.keyword .flash),
    .ability
      (.keywordWithTarget
        .enchant
        1
        (.intersection [.permanent, .cardType .creature])),
    .ability
      (.triggered
        (.enter .this)
        (.continuous
          [.gainAbility (.hostOf .this) (.keyword .firstStrike)]
          .endOfTurn)),
    .ability (.static (.addPowerToughness (.hostOf .this) 1 0)),
    .ability (.static (.gainAbility (.hostOf .this) (.keyword .haste)))
  ]).toCardDef
    (oracleText := "Flash\nEnchant creature\nWhen this Aura enters, enchanted creature gains first strike until end of turn.\nEnchanted creature gets +1/+0 and has haste.")

def teamTactics : CardDef :=
  instant "Team Tactics" (ManaCost.ofGenericAndColor 1 .red)
    "Teamwork 1 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 1 or more.)\nTarget creature gains double strike until end of turn. If this spell was cast using teamwork, that creature also gains trample until end of turn."
    (teamwork := some 1)
    (spellEffect := some (Effect.grantDoubleStrikeTeamworkTrample))

def thorGodOfThunder : CardDef :=
  legendaryCreature "Thor, God of Thunder" (ManaCost.ofGenericAndColors 3 [.red, .red]) #["God", "Warrior", "Hero"] 5 5
    (oracleText := "Flying\nWhen Thor enters, exile target Equipment, instant, or sorcery card from your graveyard. Until the end of your next turn, you may play that card.\nWhenever you cast a noncreature spell, Thor deals damage equal to that spell's mana value to any target.")
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onEnter Effect.enterExileGyPlayUntilNextTurn, .onCasting Effect.castingDamageEqualMv])

def truckToss : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Truck Toss",
    .manaCost [.generic 2, .mono .red, .mono .red],
    .type .instant,
    .ability (
      .static
        (.if
          (.anySubtype (.controlled (.controller .this)) .vehicle)
          [.reduceCost .this [.mana [.generic 2]]])),
    .actions [.dealDamage .this (.target 1 .all) 4]
  ]).toCardDef
    (oracleText := "This spell costs {2} less to cast if you control a Vehicle.\nTruck Toss deals 4 damage to any target.")

def visionOfLove : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Vision of Love",
    .manaCost [.generic 1, .mono .red],
    .type .instant,
    .actions [
      .optional
        (.actionId 1
          (.playerSelectAction
            (.controller .this)
            (.range 1 1)
            [
              .sacrifice
                (.intersection [
                  .permanent,
                  .cardType .artifact,
                  .controlled (.controller .this)]),
              .discard (.controller .this) 1])),
      .if (.happened (.actionWithId 1) .gameStart) [.draw (.controller .this) 2]]
  ]).toCardDef
    (oracleText := "You may sacrifice an artifact or discard a card. If you do, draw two cards.")

def volcanicVillain : CardDef :=
  creature "Volcanic Villain" (ManaCost.ofGenericAndColor 2 .red) #["Elemental", "Villain"] 3 2
    (oracleText := "Haste\nPower-up — {5}{R}: Put two +1/+1 counters on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)")
    (keywords := Keyword.haste)
    (activatedAbilities := #[powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColor 5 .red)])

def wonderManHollywoodHero : CardDef :=
  legendaryCreature "Wonder Man, Hollywood Hero" (ManaCost.ofGenericAndColors 3 [.red, .red]) #["Human", "Performer", "Hero"] 4 4
    (oracleText := "Flying\nEach power-up ability of permanents you control can be activated an additional time.\nPower-up — {5}{R}{R}: Put two +1/+1 counters on Wonder Man. (Activate each power-up ability only . . . once? Reduce the cost by his mana cost if he entered this turn.)")
    (keywords := Keyword.flying)
    (staticAbilities := #[StaticAbility.extraPowerUpActivation])
    (activatedAbilities := #[powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColors 5 [.red, .red])])

def antManSArmy : CardDef :=
  creature "Ant-Man's Army" (ManaCost.ofGenericAndColor 2 .green) #["Insect"] 3 2
    (oracleText := "When this creature enters, create a Food token or a Treasure token. (A Food token is an artifact with \"{2}, {T}, Sacrifice this token: You gain 3 life.\" A Treasure token is an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")")
    (triggeredAbilities := #[.onEnterCreateFoodOrTreasure])

def callDamageControl : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Call Damage Control",
    .manaCost [.generic 1, .mono .green],
    .type .sorcery,
    .actions [
      .playerSelectAction
        (.controller .this)
        (.range 0 2)
        [
          .returnToHand
            (.target 1 (.intersection [.inGraveyard, .cardType .artifact, .owner (.controller .this)])),
          .returnToHand
            (.target 1 (.intersection [.inGraveyard, .cardType .creature, .owner (.controller .this)])),
          .returnToHand
            (.target 1 (.intersection [.inGraveyard, .cardType .enchantment, .owner (.controller .this)])),
          .returnToHand
            (.target 1 (.intersection [.inGraveyard, .cardType .land, .owner (.controller .this)]))]]
  ]).toCardDef
    (oracleText := "Choose up to two. Return those cards from your graveyard to your hand.\n• Target artifact card.\n• Target creature card.\n• Target enchantment card.\n• Target land card.")

def claimTheKingdom : CardDef :=
  enchantment "Claim the Kingdom" (ManaCost.ofGenericAndColor 1 .green)
    "Landfall — Whenever a land you control enters, put a +1/+1 counter on target creature you control and a plan counter on this enchantment.\nWhen the fourth plan counter is put on this enchantment, sacrifice it. When you do, put an indestructible counter on target creature you control."
    (subtypes := #["Plan"])
    (triggeredAbilities := #[.onLandYouControlEntersPlusOneAndPlan, .onFourthPlanIndestructible])

def docSamsonSuperPsychiatrist : CardDef :=
  legendaryCreature "Doc Samson, Super Psychiatrist" (ManaCost.ofGenericAndColor 4 .green) #["Gamma", "Doctor", "Hero"] 3 6
    (oracleText := "If you would put one or more counters on a permanent you control, put that many plus one of each of those kinds of counters on that permanent instead.\n{T}: Add X mana of any one color, where X is Doc Samson's power.")
    (staticAbilities := #[StaticAbility.extraCounterOnPermanents])
    (activatedAbilities := #[activated (Effect.addAnyColorEqualToSourcePower) (ManaCost.empty) (tap := true)])

def earthSMightiestHeroes : CardDef :=
  sorcery "Earth's Mightiest Heroes" (ManaCost.ofGenericAndColors 4 [.green, .green])
    "Teamwork 5 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 5 or more.)\nReveal the top eight cards of your library. You may put a creature card from among them onto the battlefield. If this spell was cast using teamwork, put any number of creature cards from among them onto the battlefield instead. Put the rest into your graveyard."
    (teamwork := some 5)
    (spellEffect := some (Effect.revealTopPutCreatures 8))

def epicFight : CardDef :=
  sorcery "Epic Fight" (ManaCost.ofGenericAndColor 2 .green)
    "Choose one or both —\n• Double target creature's power and toughness until end of turn.\n• Target creature you control fights target creature an opponent controls."
    (spellModes := #[(Effect.doublePowerAndToughness), (Effect.fight)])
    (chooseOneOrBoth := true)

def goNuts : CardDef :=
  sorcery "Go Nuts!" (ManaCost.ofColor .green)
    "Teamwork 3 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 3 or more.)\nChoose one. If this spell was cast using teamwork, choose both instead.\n• Put a +1/+1 counter on target creature.\n• Target creature you control fights target creature an opponent controls."
    (teamwork := some 3)
    (spellModes := #[(Effect.plusOneOnCreature), (Effect.fight)])
    (chooseBothIfTeamwork := true)

def guerrillaGorilla : CardDef :=
  creature "Guerrilla Gorilla" (ManaCost.ofGenericAndColor 1 .green) #["Ape", "Soldier", "Hero"] 2 2
    (oracleText := "Reach\nSacrifice this creature: Destroy target noncreature artifact or noncreature enchantment. Activate only as a sorcery.")
    (keywords := Keyword.reach)
    (activatedAbilities := #[activated (Effect.destroyTargetNoncreatureArtOrEnch)
      (sacrificeSource := true) (onlyAsSorcery := true)])

def hellcatUndyingVigilante : CardDef :=
  legendaryCreature "Hellcat, Undying Vigilante" (ManaCost.ofColors [.green, .green]) #["Human", "Hero"] 2 2
    (oracleText := "Haste\nWhen Hellcat dies, return her to the battlefield under her owner's control with a +1/+1 counter on her. She loses all abilities and gains haste.")
    (keywords := Keyword.haste)
    (triggeredAbilities := #[.onDeath Effect.deathHellcatReturn])

def herculesPrinceOfPower : CardDef :=
  legendaryCreature "Hercules, Prince of Power" (ManaCost.ofGenericAndColor 2 .green) #["Demigod", "Warrior", "Hero"] 3 3
    (oracleText := "Power-up — {4}{G}: Put a +1/+1 counter on Hercules. He gains vigilance, indestructible, and haste until end of turn. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)")
    (activatedAbilities := #[activated (Effect.plusOneAndGrant ((Keyword.vigilance.merge Keyword.indestructible).merge Keyword.haste)) (ManaCost.ofGenericAndColor 4 .green) (powerUp := true)])

def heroicFeast : CardDef :=
  enchantment "Heroic Feast" (ManaCost.ofGenericAndColor 2 .green)
    "When this enchantment enters, create a Food token. (It's an artifact with \"{2}, {T}, Sacrifice this token: You gain 3 life.\")\nWhenever you gain life, choose up to that many target creatures you control. Put a +1/+1 counter on each of them."
    (triggeredAbilities := #[.onEnterCreateTokens .food 1, .onResource Effect.resourceGainLifePlusOnes])

def hulklingBurgeoningBruiser : CardDef :=
  legendaryCreature "Hulkling, Burgeoning Bruiser" (ManaCost.ofGenericAndColor 2 .green) #["Kree", "Skrull", "Hero"] 2 3
    (oracleText := "Vigilance\nWhenever another creature you control enters, if it has greater power or toughness than Hulkling, put a +1/+1 counter on Hulkling.")
    (keywords := Keyword.vigilance)
    (triggeredAbilities := #[.onWatch Effect.watchHulklingCompare])

def kaZarOfTheSavageLand : CardDef :=
  card "Ka-Zar of the Savage Land" #[.creature] (ManaCost.ofGenericAndColor 4 .green)
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Barbarian", "Hero"])
    (oracleText := "You may look at the top card of your library any time.\nYou may play lands from the top of your library.\nWhen Ka-Zar enters, create Zabu, a legendary 2/2 green Cat creature token with \"Landfall — Whenever a land you control enters, put a +1/+1 counter on Zabu.\"")
    (power := some 3)
    (toughness := some 2)
    (mayLookAtTopAnytime := true)
    (mayPlayLandsFromTop := true)
    (triggeredAbilities := #[.onEnter Effect.enterCreateZabu])

def knightOfWundagore : CardDef :=
  creature "Knight of Wundagore" (ManaCost.ofGenericAndColor 1 .green) #["Cat", "Knight", "Villain"] 2 1
    (oracleText := "Trample\nWhenever you put a +1/+1 counter on another creature, put a +1/+1 counter on this creature. This ability triggers only once each turn.")
    (keywords := Keyword.trample)
    (triggeredAbilities := #[.onResource Effect.resourcePlusOneOnThisOnce])

def misterHydeMonsterWithin : CardDef :=
  legendaryCreature "Mister Hyde, Monster Within" (ManaCost.ofGenericAndColor 2 .green) #["Human", "Villain"] 2 2
    (oracleText := "At the beginning of your upkeep, choose one —\n• Put a +1/+1 counter on Mister Hyde.\n• Remove a counter from a creature you control. If you do, draw a card.")
    (triggeredAbilities := #[.onStep Effect.stepHydeChoose])

def moleManMoloidMaster : CardDef :=
  legendaryCreature "Mole Man, Moloid Master" (ManaCost.ofGenericAndColor 2 .green) #["Human", "Villain"] 1 1
    (oracleText := "You may play lands from your graveyard.\nLandfall — Whenever a land you control enters, create a 1/1 green Minion creature token named Moloid with \"Whenever this token attacks, you may mill a card.\"")
    (staticAbilities := #[StaticAbility.mayPlayLandsFromGraveyard])
    (triggeredAbilities := #[.onLandYouControlEntersCreateTokens .moloid 1])

def petAvengers : CardDef :=
  creature "Pet Avengers" (ManaCost.ofGenericAndColor 3 .green) #["Dragon", "Cat", "Dog", "Bird", "Frog", "Hero"] 4 4
    (oracleText := "Reach\nPower-up — {6}{G}: Put a +1/+1 counter on this creature and create a 3/2 white Hero creature token with vigilance. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)")
    (keywords := Keyword.reach)
    (activatedAbilities := #[activated (Effect.plusOneAndCreateTokens 1 .hero32vigilance) (ManaCost.ofGenericAndColor 6 .green) (powerUp := true)])

def powerfulBroker : CardDef :=
  creature "Powerful Broker" (ManaCost.ofGenericAndColor 2 .green) #["Human", "Villain"] 3 3
    (oracleText := "{T}: For each kind of counter on target permanent or player, give that permanent or player another counter of that kind. Activate only as a sorcery.")
    (activatedAbilities := #[activated (Effect.proliferateEachKind) (ManaCost.empty) (tap := true) (onlyAsSorcery := true)])

def punishingPunch : CardDef :=
  card "Punishing Punch" #[.instant] (ManaCost.ofGenericAndColor 2 .green)
    (oracleText := "This spell costs {2} less to cast if there are two or more creature cards in your graveyard.\nTarget creature you control deals damage equal to twice its power to target creature an opponent controls.")
    (costReductionIfGyCreaturesAtLeast := some (2, 2))
    (spellEffect := some (Effect.creatureYouControlDealsTwicePower))

def rapidRescue : CardDef :=
  instant "Rapid Rescue" (ManaCost.ofColor .green)
    "Mill two cards. You may put a permanent card from among the milled cards into your hand. You gain 2 life. (To mill two cards, put the top two cards of your library into your graveyard.)"
    (spellEffect := some (Effect.millThenPutPermanentGainLife 2 2))

def reptilDinomorpher : CardDef :=
  legendaryCreature "Reptil, Dinomorpher" (ManaCost.ofColor .green) #["Human", "Hero"] 1 2
    (oracleText := "Brontosaurus — {3}: Until end of turn, Reptil becomes a Dinosaur Hero with base power and toughness 3/5 and gains reach and vigilance.\nTyrannosaurus Rex — {6}: Until end of turn, Reptil becomes a Dinosaur Hero with base power and toughness 6/6 and gains trample.")
    (activatedAbilities := #[activated (Effect.becomeTypes #["Dinosaur", "Hero"] 3 5 (Keyword.reach.merge Keyword.vigilance)) (ManaCost.ofGeneric 3),
      activated (Effect.becomeTypes #["Dinosaur", "Hero"] 6 6 Keyword.trample) (ManaCost.ofGeneric 6)])

def restorativeTechnique : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Restorative Technique",
    .manaCost [.generic 2, .mono .green],
    .type .sorcery,
    .actions [
      .gainLife (.target 1 .player) 2,
      .searchLibraryThenShuffle
        (.targetReference 1)
        [
          .putOntoBattlefieldInState
            (.selected
              (.targetReference 1)
              (.range 1 1)
              (.intersection [
                .inDeck,
                .cardType .land,
                .supertype .basic]))
            .tapped],
      .putCounter
        (.targets 1 (.range 0 1) (.intersection [.permanent, .cardType .creature]))
        .plusOnePlusOne
        1]
  ]).toCardDef
    (oracleText := "Target player gains 2 life, then searches their library for a basic land card, puts it onto the battlefield tapped, then shuffles. Put a +1/+1 counter on up to one target creature.")

def rickJonesDestinedSidekick : CardDef :=
  legendaryCreature "Rick Jones, Destined Sidekick" (ManaCost.ofColor .green) #["Human", "Advisor"] 0 3
    (oracleText := "{3}, {T}: Mill four cards. You may put a Hero or enchantment card from among those cards into your hand. (To mill four cards, put the top four cards of your library into your graveyard.)")
    (activatedAbilities := #[activated (Effect.millThenPutSubtypeOrEnchantment 4 "Hero") (ManaCost.ofGeneric 3) (tap := true)])

def savageLandDinosaur : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Savage Land Dinosaur",
    .manaCost [.generic 4, .mono .green, .mono .green],
    .type .creature,
    .subtype .dinosaur,
    .power 7,
    .toughness 6,
    .ability (.keyword .trample),
    .ability
      (.keywordWithCost
        (.supertypeAndTypeCycling .basic .land)
        [.mana [.generic 2]])
  ]).toCardDef
    (oracleText := "Trample\nBasic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)")

def serpentSpecialist : CardDef :=
  creature "Serpent Specialist" (ManaCost.ofColor .green) #["Human", "Snake", "Villain"] 1 1
    (oracleText := "Deathtouch\nPower-up — {3}{G}: Put two +1/+1 counters on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)")
    (keywords := Keyword.deathtouch)
    (activatedAbilities := #[powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColor 3 .green)])

def shangChiMasterOfKungFu : CardDef :=
  legendaryCreature "Shang-Chi, Master of Kung Fu" (ManaCost.ofGenericAndColor 1 .green) #["Human", "Warrior", "Hero"] 2 2
    (oracleText := "You may activate abilities of creatures you control as though those creatures had haste.\n{T}: Add two mana of any one color. Spend this mana only to activate abilities of creature sources.")
    (staticAbilities := #[StaticAbility.activateCreaturesAsThoughHaste])
    (activatedAbilities := #[activated (Effect.addTwoAnyColorCreatureSources) (ManaCost.empty) (tap := true)])

def sheHulkJadeDefender : CardDef :=
  legendaryCreature "She-Hulk, Jade Defender" (ManaCost.ofGenericAndColor 3 .green) #["Gamma", "Hero"] 4 4
    (oracleText := "Reach, trample\nPower-up — {4}{G}{G}: Destroy up to one target artifact or enchantment. Put a +1/+1 counter on She-Hulk. (Activate each power-up ability only once. Reduce the cost by her mana cost if she entered this turn.)")
    (keywords := (Keyword.reach).merge Keyword.trample)
    (activatedAbilities := #[activated (Effect.destroyUpToOneThenPlusOne) (ManaCost.ofGenericAndColors 4 [.green, .green]) (powerUp := true)])

def superStrength : CardDef :=
  enchantment "Super Strength" (ManaCost.ofGenericAndColor 4 .green)
    "Enchant creature\nEnchanted creature gets +4/+4 and has trample and ward {1}. (Whenever enchanted creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {1}.)"
    (subtypes := #["Aura"])
    (staticAbilities := #[StaticAbility.enchantedCreatureGetsHasAndWard 4 4
      Keyword.trample 1])

def theThingBenGrimm : CardDef :=
  (TraditionalCardDefinition.card [
    .name "The Thing, Ben Grimm",
    .manaCost [.generic 5, .mono .green],
    .type .creature,
    .supertype .legendary,
    .subtype .human,
    .subtype .hero,
    .power 7,
    .toughness 7,
    .ability (.keyword .trample),
    .ability (
      .triggered
        (.combatDamage
          (.intersection [
            .permanent,
            .cardType .creature,
            .subtype .hero,
            .controlled (.controller .this)])
          .player)
        (.putCounter (.source .this) .plusOnePlusOne 2))
  ]).toCardDef
    (oracleText := "Trample\nWhenever one or more Heroes you control deal damage to a player, put two +1/+1 counters on The Thing.")

def tigraFelineFury : CardDef :=
  legendaryCreature "Tigra, Feline Fury" (ManaCost.ofGenericAndColor 1 .green) #["Cat", "Human", "Hero"] 2 1
    (oracleText := "Flash\nTrample\nWhenever you gain life, put a +1/+1 counter on Tigra.")
    (keywords := (Keyword.flash).merge Keyword.trample)
    (triggeredAbilities := #[.onGainLifePlusOne])

def trainingRegimen : CardDef :=
  enchantment "Training Regimen" (ManaCost.ofGenericAndColor 3 .green)
    "Creatures you control with +1/+1 counters on them have trample.\nAt the beginning of combat on your turn, put a +1/+1 counter on target creature you control."
    (triggeredAbilities := #[.onCombatPlusOneOnCreatureYouControl])
    (staticAbilities := #[StaticAbility.creaturesWithPlusOneHave Keyword.trample])

def theUnbeatableSquirrelGirl : CardDef :=
  legendaryCreature "The Unbeatable Squirrel Girl" (ManaCost.ofGenericAndColors 1 [.green, .green, .green]) #["Squirrel", "Human", "Hero"] 4 4
    (oracleText := "Do You Like Squirrels? — Whenever The Unbeatable Squirrel Girl enters or attacks, create a 1/1 green Squirrel creature token.\nI LOVE Squirrels! — {1}{G}{G}{G}: Create X 1/1 green Squirrel creature tokens, where X is the number of Squirrels you control.")
    (triggeredAbilities := #[.onEnterOrAttack Effect.enterOrAttackCreateSquirrel])
    (activatedAbilities := #[activated (Effect.createTokensEqualSubtype .squirrel11green "Squirrel") (ManaCost.ofGenericAndColors 1 [.green, .green, .green])])

def undercoverSkrull : CardDef :=
  creature "Undercover Skrull" (ManaCost.ofGenericAndColor 1 .green) #["Skrull", "Shapeshifter", "Villain"] 1 1
    (oracleText := "As long as there are two or more creature cards in your graveyard, this creature gets +2/+2 and is all creature types.\n{T}: Add one mana of any color.")
    (staticAbilities := #[StaticAbility.getsAndAllTypesIfGyCreatureCards 2 2 2])
    (activatedAbilities := #[activated (Effect.addAnyColor) (ManaCost.empty) (tap := true)])

def wakandanRoyalGuard : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Wakandan Royal Guard",
    .manaCost [.generic 4, .mono .green],
    .type .creature,
    .subtype .human,
    .subtype .soldier,
    .subtype .hero,
    .power 4,
    .toughness 4,
    .ability (.keyword .vigilance),
    .ability (
      .triggered
        (.enter .this)
        (.sequence [
          .putCounter
            (.target 1 (.intersection [.permanent, .cardType .creature]))
            .plusOnePlusOne
            1,
          .if
            (.anySubtype (.targetReference 1) .hero)
            [.putCounter (.targetReference 1) .plusOnePlusOne 1]]))
  ]).toCardDef
    (oracleText := "Vigilance\nWhen this creature enters, put a +1/+1 counter on target creature. If that creature is another Hero, put two +1/+1 counters on it instead.")

def whiteTigerAvaAyala : CardDef :=
  legendaryCreature "White Tiger, Ava Ayala" (ManaCost.ofGenericAndColor 1 .green) #["Human", "Hero"] 2 2
    (oracleText := "Power-up — {5}{G}: Put a +1/+1 counter on White Tiger and create The Tiger God, a legendary 4/4 green Cat God creature token with \"The Tiger God can't be blocked by more than one creature.\" (Activate each power-up ability only once. Reduce the cost by her mana cost if she entered this turn.)")
    (activatedAbilities := #[activated (Effect.plusOneAndCreateTigerGod) (ManaCost.ofGenericAndColor 5 .green) (powerUp := true)])

def worldWarHulk : CardDef :=
  enchantment "World War Hulk" (ManaCost.ofGenericAndColors 3 [.green, .green])
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)\nI — The next red or green creature spell you cast this turn can be cast without paying its mana cost.\nII — Put three +1/+1 counters on target creature you control.\nIII — Choose target creature you control. Until end of turn, double its power and toughness and it gains trample."
    (subtypes := #["Saga"])
    (saga := some { sacrificeAfter := "III", chapters := #[chapter "I" "The next red or green creature spell you cast this turn can be cast without paying its mana cost." (Effect.nextFreeRGCreature), chapter "II" "Put three +1/+1 counters on target creature you control." (Effect.plusOneOnCreatureN 3), chapter "III" "Choose target creature you control. Until end of turn, double its power and toughness and it gains trample." (Effect.chooseTargetDoubleAndTrample)] })

def abominationTerrifyingTitan : CardDef :=
  legendaryCreature "Abomination, Terrifying Titan" (ManaCost.ofGenericAndHybrids 3 .red .green) #["Gamma", "Villain"] 4 4
    (oracleText := "Trample\nPower-up — {5}{R/G}{R/G}: Put a +1/+1 counter on Abomination. He fights up to one target creature an opponent controls. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)")
    (keywords := Keyword.trample)
    (activatedAbilities := #[activated (Effect.plusOneThenFightUpToOne) (ManaCost.ofGenericAndHybrids 5 .red .green 2) (powerUp := true)])

def absorbingMan : CardDef :=
  legendaryCreature "Absorbing Man" (ManaCost.ofGenericAndColors 1 [.green, .blue]) #["Human", "Villain"] 4 4
    (oracleText := "Vigilance\nAt the beginning of your first main phase, until your next turn, Absorbing Man becomes a copy of up to one target artifact, non-Aura enchantment, or land, except his name is Absorbing Man, he's a legendary 4/4 Human Villain creature in addition to his other types, and he has vigilance.")
    (keywords := Keyword.vigilance)
    (triggeredAbilities := #[.onStep Effect.stepCopyAbsorbingMan])

def alienInvasion : CardDef :=
  enchantment "Alien Invasion" (ManaCost.ofGenericAndColors 1 [.red, .red, .green])
    "At the beginning of combat on your turn, create a 1/1 red Alien creature token with haste and \"This token attacks each combat if able.\" Put a +1/+1 counter on it for each invasion counter on this enchantment, then put an invasion counter on this enchantment."
    (triggeredAbilities := #[.onCombatCreateAlienPerInvasion])

def antManColonyCommander : CardDef :=
  legendaryCreature "Ant-Man, Colony Commander" (ManaCost.ofGenericAndColors 1 [.green, .blue]) #["Human", "Rogue", "Hero"] 2 2
    (oracleText := "Whenever Ant-Man attacks, you may pay {1}. When you do, put a +1/+1 counter on target creature.\nWhenever you put a +1/+1 counter on a creature, create a 1/1 green Insect creature token. This ability triggers only once each turn.")
    (triggeredAbilities := #[.onThisAttack Effect.thisAttackMayPayPlusOne, .onResource Effect.resourcePlusOneCreateInsectOnce])

def aresGodOfWar : CardDef :=
  legendaryCreature "Ares, God of War" (ManaCost.ofGenericAndColors 1 [.black, .red]) #["God", "Warrior", "Villain"] 4 3
    (oracleText := "Ares attacks each combat if able.\nWhenever an attacking creature you control dies, return that card to its owner's hand.")
    (triggeredAbilities := #[.onDeath Effect.deathAttackingReturnHand])
    (staticAbilities := #[StaticAbility.attacksEachCombatIfAble])

def armorWars : CardDef :=
  enchantment "Armor Wars" (ManaCost.ofGenericAndColors 2 [.blue, .red])
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)\nI — You may draw a card for each artifact you control. If you do, each opponent draws a card.\nII — Artifact spells you cast this turn cost {1} less to cast.\nIII — This Saga deals X damage to target opponent, where X is the greatest mana value among artifacts you control."
    (subtypes := #["Saga"])
    (saga := some { sacrificeAfter := "III", chapters := #[chapter "I" "You may draw a card for each artifact you control. If you do, each opponent draws a card." (Effect.mayDrawPerArtifactOppsDraw), chapter "II" "Artifact spells you cast this turn cost {1} less to cast." (Effect.artifactSpellsCostLessThisTurn 1), chapter "III" "This Saga deals X damage to target opponent, where X is the greatest mana value among artifacts you control." (Effect.chapterDealXDamageToTargetOpponentGreatestArtifactMv)] })

def theAstonishingAntMan : CardDef :=
  legendaryCreature "The Astonishing Ant-Man" (ManaCost.ofColors [.green, .blue]) #["Human", "Scientist", "Hero"] 1 1
    (oracleText := "Whenever you draw a card, put a +1/+1 counter on The Astonishing Ant-Man.\n{2}{G}, {T}, Remove any number of +1/+1 counters from The Astonishing Ant-Man: Create that many 1/1 green Insect creature tokens.")
    (triggeredAbilities := #[.onDrawPlusOne])
    (activatedAbilities := #[activated (Effect.createTokensEqualRemovedPlusOnes .insect11green)
      (ManaCost.ofGenericAndColor 2 .green) (tap := true) (removeAnyNumberPlusOne := true)])

def avengersUnderSiege : CardDef :=
  enchantment "Avengers: Under Siege" (ManaCost.ofGenericAndColors 2 [.black, .red])
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)\nI — Create two 2/1 black Villain creature tokens with menace.\nII — This Saga deals 2 damage to each non-Villain creature and each opponent.\nIII — Create a Treasure token for each Villain you control."
    (subtypes := #["Saga"])
    (saga := some { sacrificeAfter := "III", chapters := #[chapter "I" "Create two 2/1 black Villain creature tokens with menace." (Effect.createTokens .villain21menace 2), chapter "II" "This Saga deals 2 damage to each non-Villain creature and each opponent." (Effect.chapterDealDamageToEachNonSubtypeAndOpponents 2 "Villain"), chapter "III" "Create a Treasure token for each Villain you control." (Effect.createTokensPerSubtype .treasure "Villain")] })

def beastEruditeAerialist : CardDef :=
  legendaryCreature "Beast, Erudite Aerialist" (ManaCost.ofGenericAndHybrids 3 .green .blue) #["Mutant", "Scientist", "Hero"] 3 3
    (oracleText := "As long as you've put one or more +1/+1 counters on Beast this turn, he has flying.\nWhenever Beast deals combat damage to a player, draw a card.")
    (triggeredAbilities := #[.onCombatDamageDraw 1])
    (staticAbilities := #[StaticAbility.flyingIfPlusOneThisTurn])

def blackPantherVanguard : CardDef :=
  legendaryCreature "Black Panther, Vanguard" (ManaCost.ofGenericAndColors 2 [.green, .white]) #["Human", "Warrior", "Hero"] 4 4
    (oracleText := "Whenever another nontoken Hero you control enters, choose one —\n• Create a 1/1 white Soldier creature token.\n• Creatures you control get +1/+1 until end of turn.")
    (triggeredAbilities := #[.onWatch Effect.watchNontokenHeroModal])

def blackWidowDoubleAgent : CardDef :=
  legendaryCreature "Black Widow, Double Agent" (ManaCost.ofGenericAndColors 1 [.white, .black]) #["Human", "Hero", "Villain"] 3 2
    (oracleText := "Deathtouch\nWhenever a creature you control attacks alone, it gains first strike and menace until end of turn. (It can't be blocked except by two or more creatures.)")
    (keywords := Keyword.deathtouch)
    (triggeredAbilities := #[.onWatch Effect.watchAttacksAloneFirstStrikeMenace])

def bullseyeDeathDealer : CardDef :=
  legendaryCreature "Bullseye, Death Dealer" (ManaCost.ofGenericAndHybrids 2 .black .red) #["Human", "Assassin", "Villain"] 2 3
    (oracleText := "When Bullseye enters, you may sacrifice an artifact or discard a nonland card. When you do, Bullseye deals 2 damage to any target.\n{3}, {T}, Sacrifice an artifact or discard a nonland card: Bullseye deals 2 damage to any target.")
    (triggeredAbilities := #[.onEnter Effect.enterMaySacOrDiscardNonlandThenDamage])
    (activatedAbilities := #[activated (Effect.dealDamageToAny 2) (ManaCost.ofGeneric 3)
      (tap := true) (sacrificeArtifactOrDiscardNonland := true)])

def captainAmericaLivingLegend : CardDef :=
  legendaryCreature "Captain America, Living Legend" (ManaCost.ofGenericAndColors 1 [.white, .blue]) #["Human", "Soldier", "Hero"] 3 4
    (oracleText := "Vigilance\nWhenever a creature you control becomes tapped during your turn, if it's the first time that creature has become tapped this turn, untap it.")
    (keywords := Keyword.vigilance)
    (triggeredAbilities := #[.onWatch Effect.watchFirstTapUntap])

def cloakAndDaggerEntwined : CardDef :=
  legendaryCreature "Cloak and Dagger, Entwined" (ManaCost.ofGenericAndColors 1 [.white, .black]) #["Human", "Hero"] 2 2
    (oracleText := "Deathtouch, lifelink\nWhen Cloak and Dagger enter, choose target opponent and up to one target creature they control. They reveal their hand. You may exile a nonland card from their hand or the chosen creature until Cloak and Dagger leave the battlefield.")
    (keywords := (Keyword.deathtouch).merge Keyword.lifelink)
    (triggeredAbilities := #[.onEnter Effect.enterRevealHandExileUntilLeaves])

def theComingOfGalactus : CardDef :=
  enchantment "The Coming of Galactus" (ManaCost.ofGenericAndColors 2 [.black, .black, .green])
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI — Destroy up to one target nonland permanent.\nII, III — Each opponent loses 2 life.\nIV — Create Galactus, a legendary 16/16 black Elder Alien creature token with flying, trample, and \"Whenever Galactus attacks, destroy target land.\""
    (subtypes := #["Saga"])
    (saga := some { sacrificeAfter := "IV", chapters := #[chapter "I" "Destroy up to one target nonland permanent." (Effect.destroyUpToOneNonland), chapter "II, III" "Each opponent loses 2 life." (Effect.eachOpponentLosesLife 2), chapter "IV" "Create Galactus, a legendary 16/16 black Elder Alien creature token with flying, trample, and \"Whenever Galactus attacks, destroy target land.\"." (Effect.createGalactus)] })

def daredevilManWithoutFear : CardDef :=
  card "Daredevil, Man Without Fear" #[.creature] (ManaCost.ofGenericAndColors 2 [.red, .white])
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Vigilance, haste\nRadar Sense — You may look at the top card of your library any time.\nWhenever you attack, you may exile the top card of your library. If that card is a Hero card, Daredevil gets +2/+1 until end of turn. You may play that card this turn.")
    (power := some 3)
    (toughness := some 4)
    (keywords := (Keyword.vigilance).merge Keyword.haste)
    (mayLookAtTopAnytime := true)
    (triggeredAbilities := #[.onYouAttacking Effect.youAttackingExileTopHeroPump])

def ghostSpectralSaboteur : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Ghost, Spectral Saboteur",
    .manaCost [.generic 2, .hybrid .blue .black],
    .type .creature,
    .supertype .legendary,
    .subtype .human,
    .subtype .rogue,
    .subtype .villain,
    .power 2,
    .toughness 2,
    .ability (.keyword .flash),
    .ability (.static (.forbid (.block .any .this)))
  ]).toCardDef
    (oracleText := "Flash\nIntangibility — Ghost can't be blocked.")

def hulkGammaGoliath : CardDef :=
  legendaryCreature "Hulk, Gamma Goliath" (ManaCost.ofGenericAndColors 3 [.red, .green]) #["Gamma", "Berserker", "Hero"] 6 5
    (oracleText := "Reach, trample\nPower-up abilities of other creatures you control cost {3} less to activate.\nPower-up — {6}{R}{G}: Put five +1/+1 counters on Hulk. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)")
    (keywords := (Keyword.reach).merge Keyword.trample)
    (staticAbilities := #[StaticAbility.otherPowerUpCostsLess 3])
    (activatedAbilities := #[powerUpAbility (Effect.putPlusOnePlusOneOnSource 5) (ManaCost.ofGenericAndColors 6 [.red, .green])])

def ironManMasterOfMachines : CardDef :=
  artifactCreature "Iron Man, Master of Machines" (ManaCost.ofGenericAndColors 2 [.blue, .red]) #["Human", "Hero"] 1 4
    (oracleText := "Flying, vigilance\nIron Man gets +1/+0 for each other artifact you control.\nWhenever Iron Man attacks, if an artifact entered the battlefield under your control this turn, draw a card.")
    (keywords := (Keyword.flying).merge Keyword.vigilance)
    (triggeredAbilities := #[.onThisAttack Effect.thisAttackIfArtifactEnteredDraw])
    (staticAbilities := #[StaticAbility.getsPowerPerOtherArtifact 1])
    (legendary := true)

def kangTemporalTyrant : CardDef :=
  legendaryCreature "Kang, Temporal Tyrant" (ManaCost.ofGenericAndColors 2 [.blue, .black]) #["Human", "Villain"] 3 4
    (oracleText := "Whenever Kang attacks, he connives. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on this creature.)\nWhenever you draw your second card each turn, each opponent loses 1 life and you gain 1 life.")
    (triggeredAbilities := #[.onAttackConnive, .onResource Effect.resourceSecondDrawDrain])

def killmongerScourgeOfWakanda : CardDef :=
  legendaryCreature "Killmonger, Scourge of Wakanda" (ManaCost.ofGenericAndColors 2 [.black, .green]) #["Human", "Mercenary", "Villain"] 3 3
    (oracleText := "When Killmonger enters, you may sacrifice another creature. When you do, destroy target nonland permanent an opponent controls.\nAs long as there are two or more creature cards in your graveyard, Killmonger gets +2/+1.")
    (triggeredAbilities := #[.onEnter Effect.enterMaySacAnotherThenDestroyOppNonland])
    (staticAbilities := #[StaticAbility.getsIfGyCreatureCards 2 2 1])

def kingTChalla : CardDef :=
  legendaryCreature "King T'Challa" (ManaCost.ofGenericAndColors 1 [.white, .blue]) #["Human", "Noble", "Hero"] 3 2
    (oracleText := "Flash\nWhenever a player draws their second card each turn, you draw a card.\n{4}{W}{U}: Transform King T'Challa. Activate only as a sorcery.")
    (keywords := Keyword.flash)
    (triggeredAbilities := #[.onWatch Effect.watchAnyPlayerSecondDraw])
    (activatedAbilities := #[activated (Effect.transform) (ManaCost.ofGenericAndColors 4 [.white, .blue]) (onlyAsSorcery := true)])
    (otherFace := some blackPantherHopeEnduring)

def theKingpinOfCrime : CardDef :=
  legendaryCreature "The Kingpin of Crime" (ManaCost.ofGenericAndColors 1 [.white, .black]) #["Human", "Villain"] 1 5
    (oracleText := "Extort (Whenever you cast a spell, you may pay {W/B}. If you do, each opponent loses 1 life and you gain that much life.)\nWhenever you attack, you may pay 2 life. If you do, until end of turn, creatures you control with toughness greater than their power assign combat damage equal to their toughness rather than their power.")
    (triggeredAbilities := #[.onYouAttacking Effect.youAttackingPay2LifeToughness])
    (staticAbilities := #[.extort])

def madameHydra : CardDef :=
  legendaryCreature "Madame Hydra" (ManaCost.ofGenericAndColors 2 [.black, .red]) #["Human", "Villain"] 2 3
    (oracleText := "Whenever you cast a Villain spell, create a 2/1 black Villain creature token with menace. (It can't be blocked except by two or more creatures.)")
    (triggeredAbilities := #[.onCasting Effect.castingVillainToken])

def theMightyThorJaneFoster : CardDef :=
  (TraditionalCardDefinition.card [
    .name "The Mighty Thor, Jane Foster",
    .manaCost [.generic 1, .mono .white, .mono .blue],
    .type .creature,
    .supertype .legendary,
    .subtype .human,
    .subtype .god,
    .subtype .hero,
    .power 3,
    .toughness 3,
    .ability (.keyword .flying),
    .ability (
      .triggered
        (.attack .this .all)
        (.sequence [
          .actionId 1
            (.exile
              (.targets
                1
                (.range 0 1)
                (.intersection [
                  .not .token,
                  .permanent,
                  .union [.cardType .artifact, .cardType .creature]]))),
          .putOntoBattlefieldInState (.wasCreatedByAction 1) .tapped])),
    .ability (
      .triggered
        (.enter
          (.intersection [
            .permanent,
            .subtype .equipment,
            .controlled (.controller .this)]))
        (.draw (.controller .this) 1))
  ]).toCardDef
    (oracleText := "Flying\nWhenever The Mighty Thor attacks, exile up to one target nontoken artifact or creature, then return that card to the battlefield tapped under its owner's control.\nWhenever an Equipment you control enters, draw a card.")

def moonGirlAndDevilDinosaur : CardDef :=
  legendaryCreature "Moon Girl and Devil Dinosaur" (ManaCost.ofGenericAndColors 1 [.green, .blue]) #["Human", "Dinosaur", "Hero"] 2 2
    (oracleText := "Whenever you draw your second card each turn, until end of turn, Moon Girl and Devil Dinosaur's base power and toughness become 6/6 and they gain trample.\nWhenever an artifact you control enters, draw a card. This ability triggers only once each turn.")
    (triggeredAbilities := #[.onResource Effect.resourceSecondDrawBecome66, .onArtifactYouControlEntersDrawOnce])

def theRuinousWreckingCrew : CardDef :=
  legendaryCreature "The Ruinous Wrecking Crew" ({ symbols := #[.x, .colored .black, .colored .red] }) #["Human", "Villain"] 2 2
    (oracleText := "The Ruinous Wrecking Crew enters with X +1/+1 counters on it.\nWhen The Ruinous Wrecking Crew enters, choose up to X —\n• Discard a card, then draw a card.\n• Target opponent loses 2 life.\n• Destroy target token.\n• Each player sacrifices a creature of their choice.")
    (triggeredAbilities := #[.onEnter Effect.enterChooseUpToXModes])
    (staticAbilities := #[StaticAbility.entersWithXPlusOne])

def scientistSupremeOfAIM : CardDef :=
  legendaryCreature "Scientist Supreme of A.I.M." (ManaCost.ofColors [.blue, .black]) #["Human", "Scientist", "Villain"] 2 2
    (oracleText := "Pay 2 life: Copy target activated or triggered ability you control from an artifact source. You may choose new targets for the copy. Activate only during your turn and only once each turn. (Mana abilities can't be targeted.)")
    (activatedAbilities := #[activated (Effect.copyControlledAbility false)
      (payLife := 2) (onlyDuringYourTurn := true) (onceEachTurn := true)])

def theSerpentSociety : CardDef :=
  legendaryCreature "The Serpent Society" (ManaCost.ofGenericAndColors 1 [.black, .green]) #["Human", "Snake", "Villain"] 3 4
    (oracleText := "Deathtouch\nWard—Get five poison counters. (A player with ten or more poison counters loses the game.)\nWhenever another creature you control with deathtouch dies, each opponent sacrifices a nontoken creature of their choice.")
    (keywords := Keyword.deathtouch)
    (triggeredAbilities := #[.onDeath Effect.deathDeathtouchOppSac])
    (staticAbilities := #[StaticAbility.wardPoisonCounters 5])

def speedballNewWarrior : CardDef :=
  legendaryCreature "Speedball, New Warrior" (ManaCost.ofGenericAndHybrids 2 .blue .red) #["Human", "Hero"] 2 2
    (oracleText := "Whenever a player casts a spell that targets Speedball, he gets +2/+2 until end of turn. You may choose new targets for that spell.")
    (triggeredAbilities := #[.onWatch Effect.watchSpeedballTargeted])

def spiderManToTheRescue : CardDef :=
  legendaryCreature "Spider-Man, To the Rescue" (ManaCost.ofGenericAndHybrids 2 .green .white) #["Spider", "Human", "Hero"] 3 2
    (oracleText := "Flash\nReach, vigilance\nNo One Dies! — When Spider-Man enters, you may tap him. When you do, another target nonattacking creature you control gains indestructible until end of turn. (Damage and effects that say \"destroy\" don't destroy it.)")
    (keywords := ((Keyword.flash).merge Keyword.reach).merge Keyword.vigilance)
    (triggeredAbilities := #[.onEnter Effect.enterMayTapThenGrantIndestructible])

def spiderWomanSecretAgent : CardDef :=
  legendaryCreature "Spider-Woman, Secret Agent" (ManaCost.ofGenericAndHybrids 3 .white .blue) #["Spider", "Human", "Spy", "Hero"] 1 4
    (oracleText := "Flash\nWhen Spider-Woman enters, tap target creature an opponent controls. That creature can't become untapped for as long as you control Spider-Woman.")
    (keywords := Keyword.flash)
    (triggeredAbilities := #[.onEnter Effect.enterTapOppCantUntapWhileControl])

def stormWindrider : CardDef :=
  legendaryCreature "Storm, Windrider" (ManaCost.ofGenericAndColors 1 [.green, .white, .white]) #["Mutant", "Hero"] 4 4
    (oracleText := "Flying\nCreatures with flying can't attack you or block creatures you control.\nWhenever you cast a spell that targets one or more creatures, those creatures gain flying until end of turn.")
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onCasting Effect.castingTargetsGainFlying])
    (staticAbilities := #[StaticAbility.flyingCantAttackYouOrBlockYours])

def theSuperHeroCivilWar : CardDef :=
  enchantment "The Super Hero Civil War" (ManaCost.ofGenericAndColors 3 [.red, .white])
    "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)\nI — Gain control of up to two target creatures with total mana value 6 or less for as long as this Saga remains on the battlefield.\nII — Creatures you control get +1/+1 and gain vigilance until end of turn.\nIII — Target creature you control fights up to one other target creature."
    (subtypes := #["Saga"])
    (saga := some { sacrificeAfter := "III", chapters := #[chapter "I" "Gain control of up to two target creatures with total mana value 6 or less for as long as this Saga remains on the battlefield." (Effect.chapterGainControlOfUpToTwoCreaturesTotalMvAtMost 6), chapter "II" "Creatures you control get +1/+1 and gain vigilance until end of turn." (Effect.creaturesYouControlGetAndGrant 1 1 Keyword.vigilance), chapter "III" "Target creature you control fights up to one other target creature." (Effect.fightUpToOne)] })

def taskmasterMercenaryMimic : CardDef :=
  legendaryCreature "Taskmaster, Mercenary Mimic" (ManaCost.ofGenericAndColors 2 [.blue, .black]) #["Human", "Mercenary", "Villain"] 3 5
    (oracleText := "Photographic Reflexes — At the beginning of your first main phase, until your next turn, Taskmaster becomes a copy of up to one target creature on the battlefield or creature card in a graveyard, except his name is Taskmaster, Mercenary Mimic and he's a legendary Human Mercenary Villain creature.")
    (triggeredAbilities := #[.onStep Effect.stepCopyTaskmaster])

def thanosTheMadTitan : CardDef :=
  legendaryCreature "Thanos, the Mad Titan" (ManaCost.ofColors [.red, .white, .black]) #["Eternal", "Villain"] 4 4
    (oracleText := "Deathtouch, lifelink\nPower-up — {C}{W}{U}{B}{R}{G}: Put two +1/+1 counters on Thanos. Choose odd or even. Destroy each other creature with mana value of the chosen quality. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn. Zero is even.)")
    (keywords := (Keyword.deathtouch).merge Keyword.lifelink)
    (activatedAbilities := #[activated (Effect.plusTwoThenOddEvenDestroy) ({ symbols := #[.colorless, .colored .white, .colored .blue, .colored .black, .colored .red, .colored .green] }) (powerUp := true)])

def thorOdinson : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Thor Odinson",
    .manaCost [.generic 3, .mono .red, .mono .white],
    .type .creature,
    .supertype .legendary,
    .subtype .god,
    .subtype .warrior,
    .subtype .hero,
    .power 4,
    .toughness 4,
    .ability (.keyword .flying),
    .ability (.keyword .vigilance),
    .ability (.keyword .prowess),
    .ability (.keyword .prowess)
  ]).toCardDef
    (oracleText := "Flying, vigilance, prowess, prowess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn twice.)")

def titaniaRuggedRumbler : CardDef :=
  card "Titania, Rugged Rumbler" #[.creature] (ManaCost.ofGenericAndHybrids 2 .black .green)
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Villain"])
    (oracleText := "As an additional cost to cast this spell, discard a card or pay {2}.\nWard—Discard a card or pay {2}. (Whenever this creature becomes the target of a spell or ability an opponent controls, counter it unless that player discards a card or pays {2}.)")
    (power := some 5)
    (toughness := some 5)
    (additionalCostDiscardOrPayGeneric := some 2)
    (staticAbilities := #[StaticAbility.wardDiscardOrPay 2])

#guard titaniaRuggedRumbler.additionalCostDiscardOrPayGeneric == some 2
#guard titaniaRuggedRumbler.announcesAdditionalCost

def uSAgentJohnWalker : CardDef :=
  legendaryCreature "U.S.Agent, John Walker" (ManaCost.ofGenericAndHybrids 3 .white .black) #["Human", "Soldier", "Hero"] 3 2
    (oracleText := "When U.S.Agent enters, create a colorless Equipment artifact token named Sturdy Shield with \"Equipped creature gets +1/+2\" and equip {2}. Attach it to U.S.Agent.")
    (triggeredAbilities := #[.onEnter Effect.enterCreateSturdyShieldAttach])

def visionQuest : CardDef :=
  sorcery "Vision Quest" ({ symbols := #[.x, .colored .blue, .colored .red] })
    "Search your library and/or graveyard for an artifact creature card with mana value X or less and put it onto the battlefield with X additional +1/+1 counters on it. If X is 4 or greater, it gains haste until end of turn. If you search your library this way, shuffle."
    (spellEffect := some (Effect.searchLibraryOrGyArtifactCreatureX))

def warMachineLegacyOfIron : CardDef :=
  artifactCreature "War Machine, Legacy of Iron" (ManaCost.ofGenericAndHybrids 2 .red .white) #["Human", "Hero"] 1 3
    (oracleText := "Flying\nAt the beginning of combat on your turn, another target creature you control gets +X/+0 until end of turn, where X is War Machine's power.")
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onCombatAnotherGetsSourcePower])
    (legendary := true)

def winterSoldierIcyAssassin : CardDef :=
  legendaryCreature "Winter Soldier, Icy Assassin" (ManaCost.ofColors [.white, .black]) #["Human", "Assassin", "Villain"] 2 2
    (oracleText := "Vigilance, menace\nWinter Soldier gets +2/+0 for each Equipment attached to him.\n{3}{W}{B}: Return this card from your graveyard to the battlefield with a finality counter on him. Then you may attach an Equipment you control to him. (If a creature with a finality counter on it would die, exile it instead.)")
    (keywords := (Keyword.vigilance).merge Keyword.menace)
    (staticAbilities := #[StaticAbility.getsPowerPerAttachedEquipment 2])
    (activatedAbilities := #[activated (Effect.returnFromGyFinalityAttach) (ManaCost.ofGenericAndColors 3 [.white, .black])
      (activateFromGraveyard := true)])

def wolverineFierceFighter : CardDef :=
  legendaryCreature "Wolverine, Fierce Fighter" (ManaCost.ofGenericAndColors 2 [.red, .green]) #["Mutant", "Berserker", "Hero"] 3 5
    (oracleText := "Haste\nWhen Wolverine enters, he fights up to one other target creature.\nIf damage would be dealt to Wolverine, instead that damage is dealt, but all other damage already dealt to him is healed.")
    (keywords := Keyword.haste)
    (triggeredAbilities := #[.onEnter Effect.enterFightUpToOne])
    (staticAbilities := #[StaticAbility.healOtherDamageWhenDealt])

def worldsWithinWorlds : CardDef :=
  sorcery "Worlds Within Worlds" (ManaCost.ofGenericAndColors 5 [.green, .blue])
    "Exile all creatures. Each player may put any number of creature cards from their hand onto the battlefield. Then put all cards exiled this way into their owners' hands. Exile Worlds Within Worlds."
    (spellEffect := some (Effect.worldsWithinWorlds))

def aIMSynthoids : CardDef :=
  artifactCreature "A.I.M. Synthoids" (ManaCost.ofGeneric 2)
    #["Robot", "Villain"] 1 3
    "When this creature enters, surveil 2. (Look at the top two cards of your library, then put any number of them into your graveyard and the rest on top of your library in any order.)"
    (triggeredAbilities := #[.onEnterSurveil 2])

def arcReactor : CardDef :=
  artifact "Arc Reactor" (ManaCost.ofGeneric 5)
    "Improvise (Your artifacts can help cast this spell. Each artifact you tap after you're done activating mana abilities pays for {1}.)\nThis artifact enters tapped.\n{T}: Add {C}{C}{C}."
    (entersTapped := true)
    (staticAbilities := #[.improvise])
    (activatedAbilities := #[activated (Effect.addMana #[.colorless, .colorless, .colorless]) (ManaCost.empty) (tap := true)])

def captainAmericaSShield : CardDef :=
  equipment "Captain America's Shield" (ManaCost.ofGeneric 2)
    "Indestructible\nEquipped creature gets +0/+8 and has vigilance.\nWhenever equipped creature attacks, tap target creature defending player controls.\nEquip {2}"
    (ManaCost.ofGeneric 2)
    (legendary := true)
    (keywords := Keyword.indestructible)
    (triggeredAbilities := #[.onWatch Effect.watchEquippedAttacksTap])
    (staticAbilities := #[StaticAbility.equippedCreatureGetsAndHas 0 8 Keyword.vigilance])

def cosmicCube : CardDef :=
  artifact "Cosmic Cube" (ManaCost.ofGeneric 5)
    "Ward {2}\nWhenever you attack, look at the top six cards of your library. You may cast a spell from among them with mana value less than or equal to the greatest power among attacking creatures you control without paying its mana cost. Put the rest on the bottom of your library in a random order."
    (ward := some 2)
    (triggeredAbilities := #[.onYouAttacking Effect.youAttackingLookSixCast])

def dependableQuinjet : CardDef :=
  artifact "Dependable Quinjet" (ManaCost.ofGeneric 3)
    "Flying\n{T}: Add one mana of any color.\nCrew 4 (Tap any number of creatures you control with total power 4 or more: This Vehicle becomes an artifact creature until end of turn.)"
    (subtypes := #["Vehicle"])
    (power := some 3)
    (toughness := some 3)
    (keywords := Keyword.flying)
    (crew := some 4)
    (activatedAbilities := #[activated (Effect.addAnyColor) (ManaCost.empty) (tap := true)])

def hERBIEScoutUnit : CardDef :=
  artifactCreature "H.E.R.B.I.E. Scout Unit" (ManaCost.ofGeneric 4) #["Robot", "Scout"] 2 1
    (oracleText := "Flying\nWhen this creature enters, draw a card, then you may put a land card from your hand onto the battlefield tapped.")
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onEnterDrawMayPutLandTapped])

def ironManArmor : CardDef :=
  artifact "Iron Man Armor" (ManaCost.ofGeneric 3)
    "When this Equipment enters, attach it to target creature you control.\nEquipped creature gets +2/+1 and has flying.\n{2}: If this Equipment isn't a creature, it becomes a 0/0 Construct Hero artifact creature with flying and \"This creature gets +1/+1 for each artifact you control\" until end of turn.\nEquip {2}"
    (subtypes := #["Equipment"])
    (triggeredAbilities := #[.onEnterAttachToCreatureYouControl])
    (staticAbilities := #[StaticAbility.equippedCreatureGetsAndHas 2 1 Keyword.flying])
    (activatedAbilities := #[activated (Effect.equipmentBecomesConstructHero) (ManaCost.ofGeneric 2), equipAbility (ManaCost.ofGeneric 2)])

def sHIELDHelicarrier : CardDef :=
  artifact "S.H.I.E.L.D. Helicarrier" (ManaCost.ofGeneric 4)
    "Flying\nWhen this Vehicle enters, create two 1/1 white Soldier creature tokens.\nCrew 6 (Tap any number of creatures you control with total power 6 or more: This Vehicle becomes an artifact creature until end of turn.)"
    (subtypes := #["Vehicle"])
    (power := some 4)
    (toughness := some 5)
    (keywords := Keyword.flying)
    (crew := some 6)
    (triggeredAbilities := #[.onEnterCreateTokens .soldier11white 2])

def superAdaptoid : CardDef :=
  card "Super-Adaptoid" #[.artifact, .creature] (ManaCost.ofGeneric 2)
    (supertypes := #[.legendary])
    (subtypes := #["Robot", "Villain"])
    (oracleText := "Super-Adaptoid's power is equal to the number of legendary creatures you control.\nWhenever Super-Adaptoid enters or attacks, choose another target creature. If that creature has haste and Super-Adaptoid doesn't, put a haste counter on Super-Adaptoid. Do the same for flying, first strike, double strike, deathtouch, indestructible, lifelink, menace, reach, trample, and vigilance.")
    (toughness := some 2)
    (triggeredAbilities := #[.onEnterOrAttack Effect.enterOrAttackCopyKeywords])
    (staticAbilities := #[.powerEqualLegendaryCreaturesYouControl])

def theTenRings : CardDef :=
  artifact "The Ten Rings" (ManaCost.ofGeneric 8)
    "Your maximum hand size is ten.\nAt the beginning of your end step, if you have fewer than ten cards in hand, draw cards equal to the difference."
    (triggeredAbilities := #[.onStep Effect.stepDrawToTen])
    (staticAbilities := #[.maximumHandSize 10])
    (legendary := true)

def ultronArtificialMalevolence : CardDef :=
  artifactCreature "Ultron, Artificial Malevolence" (ManaCost.ofGeneric 3) #["Robot", "Villain"] 2 4
    (oracleText := "Whenever another nontoken artifact you control enters, you may pay {2}. If you do, create a token that's a copy of it. If the token isn't a creature, it becomes a 2/2 Robot Villain creature in addition to its other types.")
    (triggeredAbilities := #[.onWatch Effect.watchUltronCopy])
    (legendary := true)

def ultronDrone : CardDef :=
  artifactCreature "Ultron Drone" (ManaCost.ofGeneric 3) #["Robot", "Villain"] 2 3
    (oracleText := "Power-up — {6}: Put two +1/+1 counters on this creature and create a 2/2 colorless Robot Villain artifact creature token. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)")
    (activatedAbilities := #[activated (Effect.plusOneAndCreateTokens 2 .robotVillain22) (ManaCost.ofGeneric 6) (powerUp := true)])

def vibraniumEnergyDaggers : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Vibranium Energy Daggers",
    .manaCost [.generic 1],
    .type .artifact,
    .subtype .equipment,
    .ability (.keyword .indestructible),
    .ability (.static (.addPowerToughness (.hostOf .this) 2 2)),
    .ability (.keywordWithCost .equip [.mana [.generic 3]])
  ]).toCardDef
    (oracleText := "Indestructible (Effects that say \"destroy\" don't destroy this Equipment.)\nEquipped creature gets +2/+2.\nEquip {3} ({3}: Attach to target creature you control. Equip only as a sorcery.)")

def theVision : CardDef :=
  artifactCreature "The Vision" (ManaCost.ofGeneric 4) #["Robot", "Hero"] 2 5
    (oracleText := "Flying, vigilance\nWhenever you cast a noncreature spell, choose one that hasn't been chosen this turn —\n• Solar Beam — The Vision gains double strike until end of turn.\n• Density Control — The Vision gains indestructible until end of turn.\n• Technopathy — Draw a card.")
    (keywords := (Keyword.flying).merge Keyword.vigilance)
    (triggeredAbilities := #[.onCasting Effect.castingVisionModes])
    (legendary := true)

def vivVisionTeenSynthezoid : CardDef :=
  artifactCreature "Viv Vision, Teen Synthezoid" (ManaCost.ofGeneric 3) #["Robot", "Hero"] 2 2
    (oracleText := "Flying\nCybernetic Senses — Whenever Viv Vision attacks, draw a card if her power is 4 or greater.\nPower-up — {7}: Put two +1/+1 counters on Viv Vision. (Activate each power-up ability only once. Reduce the cost by her mana cost if she entered this turn.)")
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onThisAttack Effect.thisAttackDrawIfPower4])
    (activatedAbilities := #[powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGeneric 7)])
    (legendary := true)

def aIMLabs : CardDef :=
  (TraditionalCardDefinition.card [
    .name "A.I.M. Labs",
    .type .land,
    .ability (
      .static
        (.replace
          (.enter .this)
          [.putOntoBattlefieldInState .this .tapped])),
    .ability (.triggered (.enter .this) (.gainLife (.controller .this) 1)),
    .ability (
      .activated
        [.tapSymbol]
        (.playerSelectAction
          (.controller .this)
          (.range 1 1)
          [
            .addMana (.controller .this) [.mono .blue],
            .addMana (.controller .this) [.mono .black]]))
  ]).toCardDef
    (oracleText :=
      "This land enters tapped.\nWhen this land enters, you gain 1 life.\n{T}: Add {U} or {B}.")

#guard aIMLabs.tapAddOneOf == #[.colored .blue, .colored .black]
#guard aIMLabs.triggeredAbilities == #[.onEnterGainLife 1]
#guard aIMLabs.oracleText ==
  "This land enters tapped.\nWhen this land enters, you gain 1 life.\n{T}: Add {U} or {B}."
#guard aIMLabs.entersTapped

def asgardianCitadel : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Asgardian Citadel",
    .type .land,
    .ability (
      .static
        (.replace
          (.enter .this)
          [.putOntoBattlefieldInState .this .tapped])),
    .ability (.triggered (.enter .this) (.gainLife (.controller .this) 1)),
    .ability (
      .activated
        [.tapSymbol]
        (.playerSelectAction
          (.controller .this)
          (.range 1 1)
          [
            .addMana (.controller .this) [.mono .red],
            .addMana (.controller .this) [.mono .white]]))
  ]).toCardDef
    (oracleText :=
      "This land enters tapped.\nWhen this land enters, you gain 1 life.\n{T}: Add {R} or {W}.")

def avengersHangar : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Avengers Hangar",
    .type .land,
    .ability (
      .static
        (.replace
          (.enter .this)
          [.putOntoBattlefieldInState .this .tapped])),
    .ability (.triggered (.enter .this) (.gainLife (.controller .this) 1)),
    .ability (
      .activated
        [.tapSymbol]
        (.playerSelectAction
          (.controller .this)
          (.range 1 1)
          [
            .addMana (.controller .this) [.mono .white],
            .addMana (.controller .this) [.mono .blue]]))
  ]).toCardDef
    (oracleText :=
      "This land enters tapped.\nWhen this land enters, you gain 1 life.\n{T}: Add {W} or {U}.")

def avengersTower : CardDef :=
  land "Avengers Tower"
    "{T}: Add {C}.\n{T}: Add one mana of any color. Spend this mana only to cast a Hero spell or to activate an ability of a Hero source.\n{4}, {T}: Look at the top three cards of your library. You may reveal a Hero card from among them and put it into your hand. Put the rest on the bottom of your library in any order."
    (tapAddMana := #[.colorless])
    (activatedAbilities := #[activated (Effect.addAnyColorSpendOnlySubtype "Hero") (ManaCost.empty) (tap := true),
      activated (Effect.lookAtTopRevealSubtype 3 "Hero") (ManaCost.ofGeneric 4) (tap := true)])

def baxterBuilding : CardDef :=
  land "Baxter Building"
    "{T}: Add {C}.\n{4}, {T}: Add four mana in any combination of colors.\n{4}, {T}: Draw a card. Activate only if you control a creature with toughness 4 or greater."
    (tapAddMana := #[.colorless])
    (activatedAbilities := #[activated (Effect.addFourAnyCombination) (ManaCost.ofGeneric 4) (tap := true),
      activated (Effect.abilityDraw 1) (ManaCost.ofGeneric 4) (tap := true)
        (onlyIfYouControlCreatureToughnessAtLeast := 4)])

def birninZanaPlaza : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Birnin Zana Plaza",
    .type .land,
    .ability (
      .static
        (.replace
          (.enter .this)
          [.putOntoBattlefieldInState .this .tapped])),
    .ability (.triggered (.enter .this) (.gainLife (.controller .this) 1)),
    .ability (
      .activated
        [.tapSymbol]
        (.playerSelectAction
          (.controller .this)
          (.range 1 1)
          [
            .addMana (.controller .this) [.mono .green],
            .addMana (.controller .this) [.mono .white]]))
  ]).toCardDef
    (oracleText :=
      "This land enters tapped.\nWhen this land enters, you gain 1 life.\n{T}: Add {G} or {W}.")

def castleDoom : CardDef :=
  land "Castle Doom"
    "{T}: Add {C}.\n{T}: Add one mana of any color. Spend this mana only to cast an artifact spell.\n{3}, {T}, Sacrifice an artifact: Create a 3/3 colorless Robot Villain artifact creature token named Doombot. Activate only as a sorcery."
    (tapAddMana := #[.colorless])
    (activatedAbilities := #[activated (Effect.addAnyColorSpendOnlyArtifactSpell) (ManaCost.empty) (tap := true),
      activated (Effect.abilityCreateTokens .doombot 1) (ManaCost.ofGeneric 3) (tap := true)
        (sacrificeArtifact := true) (onlyAsSorcery := true)])

def darkFortress : CardDef :=
  conditionalDualLand "Dark Fortress" .black .red

def fiskTower : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Fisk Tower",
    .type .land,
    .ability (
      .static
        (.replace
          (.enter .this)
          [.putOntoBattlefieldInState .this .tapped])),
    .ability (.triggered (.enter .this) (.gainLife (.controller .this) 1)),
    .ability (
      .activated
        [.tapSymbol]
        (.playerSelectAction
          (.controller .this)
          (.range 1 1)
          [
            .addMana (.controller .this) [.mono .white],
            .addMana (.controller .this) [.mono .black]]))
  ]).toCardDef
    (oracleText :=
      "This land enters tapped.\nWhen this land enters, you gain 1 life.\n{T}: Add {W} or {B}.")

def gatheringPlace : CardDef :=
  conditionalDualLand "Gathering Place" .green .white

def gleamingBastion : CardDef :=
  conditionalDualLand "Gleaming Bastion" .white .blue

def hellSKitchen : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Hell's Kitchen",
    .type .land,
    .ability (
      .static
        (.replace
          (.enter .this)
          [.putOntoBattlefieldInState .this .tapped])),
    .ability (.triggered (.enter .this) (.gainLife (.controller .this) 1)),
    .ability (
      .activated
        [.tapSymbol]
        (.playerSelectAction
          (.controller .this)
          (.range 1 1)
          [
            .addMana (.controller .this) [.mono .black],
            .addMana (.controller .this) [.mono .red]]))
  ]).toCardDef
    (oracleText :=
      "This land enters tapped.\nWhen this land enters, you gain 1 life.\n{T}: Add {B} or {R}.")

def hiddenLair : CardDef :=
  conditionalDualLand "Hidden Lair" .blue .black

def losDiablosMissileBase : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Los Diablos Missile Base",
    .type .land,
    .ability (
      .static
        (.replace
          (.enter .this)
          [.putOntoBattlefieldInState .this .tapped])),
    .ability (.triggered (.enter .this) (.gainLife (.controller .this) 1)),
    .ability (
      .activated
        [.tapSymbol]
        (.playerSelectAction
          (.controller .this)
          (.range 1 1)
          [
            .addMana (.controller .this) [.mono .red],
            .addMana (.controller .this) [.mono .green]]))
  ]).toCardDef
    (oracleText :=
      "This land enters tapped.\nWhen this land enters, you gain 1 life.\n{T}: Add {R} or {G}.")

def pymTechnologies : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Pym Technologies",
    .type .land,
    .ability (
      .static
        (.replace
          (.enter .this)
          [.putOntoBattlefieldInState .this .tapped])),
    .ability (.triggered (.enter .this) (.gainLife (.controller .this) 1)),
    .ability (
      .activated
        [.tapSymbol]
        (.playerSelectAction
          (.controller .this)
          (.range 1 1)
          [
            .addMana (.controller .this) [.mono .green],
            .addMana (.controller .this) [.mono .blue]]))
  ]).toCardDef
    (oracleText :=
      "This land enters tapped.\nWhen this land enters, you gain 1 life.\n{T}: Add {G} or {U}.")

def starkIndustries : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Stark Industries",
    .type .land,
    .ability (
      .static
        (.replace
          (.enter .this)
          [.putOntoBattlefieldInState .this .tapped])),
    .ability (.triggered (.enter .this) (.gainLife (.controller .this) 1)),
    .ability (
      .activated
        [.tapSymbol]
        (.playerSelectAction
          (.controller .this)
          (.range 1 1)
          [
            .addMana (.controller .this) [.mono .blue],
            .addMana (.controller .this) [.mono .red]]))
  ]).toCardDef
    (oracleText :=
      "This land enters tapped.\nWhen this land enters, you gain 1 life.\n{T}: Add {U} or {R}.")

def subterraneanCavern : CardDef :=
  (TraditionalCardDefinition.card [
    .name "Subterranean Cavern",
    .type .land,
    .ability (
      .static
        (.replace
          (.enter .this)
          [.putOntoBattlefieldInState .this .tapped])),
    .ability (.triggered (.enter .this) (.gainLife (.controller .this) 1)),
    .ability (
      .activated
        [.tapSymbol]
        (.playerSelectAction
          (.controller .this)
          (.range 1 1)
          [
            .addMana (.controller .this) [.mono .black],
            .addMana (.controller .this) [.mono .green]]))
  ]).toCardDef
    (oracleText :=
      "This land enters tapped.\nWhen this land enters, you gain 1 life.\n{T}: Add {B} or {G}.")

def surveillanceRoom : CardDef :=
  land "Surveillance Room"
    "When this land enters, surveil 1. (Look at the top card of your library. You may put it into your graveyard.)\n{T}: Add {C}.\n{1}, {T}: Add one mana of any color."
    (tapAddMana := #[.colorless])
    (triggeredAbilities := #[.onEnterSurveil 1])
    (activatedAbilities := #[activated (Effect.addAnyColor) (ManaCost.ofGeneric 1) (tap := true)])

def trainingCompound : CardDef :=
  conditionalDualLand "Training Compound" .red .green

def villainousHideout : CardDef :=
  land "Villainous Hideout"
    "{T}: Add {C}.\n{T}: Add one mana of any color. Spend this mana only to cast a Villain spell or to activate an ability of a Villain source.\n{3}, {T}: Target Villain you control connives. Activate only as a sorcery. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on that creature.)"
    (tapAddMana := #[.colorless])
    (activatedAbilities := #[activated (Effect.addAnyColorSpendOnlySubtype "Villain") (ManaCost.empty) (tap := true),
      activated (Effect.targetSubtypeConnives "Villain") (ManaCost.ofGeneric 3) (tap := true) (onlyAsSorcery := true)])

/-- All unique MSH card names, including both faces of transforming cards
and the five basic lands printed in the set. -/
def mshCards : Array CardDef :=
  #[
    theSensationalSheHulk,
    photonLivingLight,
    theIncredibleHulk,
    theInvincibleIronMan,
    blackPantherHopeEnduring,
    agent13SharonCarter,
    agentMariaHill,
    agentOfAtlas,
    agentPhilCoulson,
    agentsOfSHIELD,
    avengersAssemble,
    boroughBackup,
    braveBrawler,
    captainAmericaSuperSoldier,
    captainAmericaWingsOfFreedom,
    captainMarvelEarthSProtector,
    captainMarVellSpaceBorn,
    colleenWingStreetSamurai,
    crowdOfTrueBelievers,
    helicarrierStrike,
    heroInTraining,
    invisibleWomanSueStorm,
    jenniferWalters,
    kreeCommandos,
    lukeCagePowerMan,
    theMindStone,
    mockingbirdAceAgent,
    monicaRambeau,
    murdockSCrusade,
    nickFuryAgentOfSHIELD,
    nightNurseHealerOfHeroes,
    okoyeDoraMilajeLeader,
    originOfTheAvengers,
    pantherPounce,
    patriotShieldWielder,
    politicalTriumph,
    quakeAgentOfSHIELD,
    raftSecurityOfficer,
    redGuardianSuperSoldier,
    theSentryGoldenGuardian,
    sHIELDSpyKit,
    superVillainLockup,
    superSoldierSerum,
    takeUpTheShield,
    wakandanDroneFlock,
    webUp,
    whiteWidowFreeAgent,
    aerialDoombot,
    aIMScientists,
    atlanteanCavalry,
    atlantisAttacks,
    attumaAtlanteanWarlord,
    boldBiochemist,
    bruceBanner,
    depower,
    echoPerceptiveProdigy,
    falconWingedWonder,
    falconSWingHarness,
    frozenInIce,
    futuristForge,
    giantSizedFlyingAnt,
    hydraulicHelper,
    iAmIronMan,
    ironLadDivergingDestiny,
    ironheartCleverChampion,
    justiceVanceAstrovik,
    kangTheConqueror,
    kidLoki,
    leaderSuperGenius,
    lokiGodOfMischief,
    misterFantasticReedRichards,
    msMarvelKamalaKhan,
    multiversalIncursion,
    namorTheSubMariner,
    pymParticles,
    rewriteHistory,
    secretInvasion,
    sHIELDDeploymentDrone,
    sHIELDFlyingCar,
    shuriWakandanInventor,
    statureSizeShifter,
    superIntelligence,
    superSuit,
    thirstForKnowledge,
    tonyStark,
    tricksterSStratagem,
    weSayTheeNay,
    wiccanRisingMagician,
    theWondrousWasp,
    agentsOfHYDRA,
    arnimZolaBioFanatic,
    baronHelmutZemo,
    baronStruckerHYDRAOverlord,
    blackWidowSuperSpy,
    constructACosmicCube,
    crossbonesMaliciousMercenary,
    cruelAlliance,
    darkDeed,
    decoyPloy,
    doctorDoom,
    doomReignsSupreme,
    elektraDaughterOfTheHand,
    grimReaperLethalLegionnaire,
    hourOfDefeat,
    hYDRAInfiltration,
    hYDRATroopers,
    kingpinSEnforcers,
    klawSonicSubjugator,
    madameMasque,
    theMastersOfEvil,
    mODOK,
    moonstoneHarshMistress,
    ninjaOfTheHand,
    projectDeathlokSoldier,
    redRoomRecruit,
    robotDomination,
    roninShadowStalker,
    roxxonBrutes,
    stolenStarkTech,
    superSkrull,
    swordsmanSharpScoundrel,
    thunderboltsConspiracy,
    tooEvilToStayDead,
    unlivingLegionnaire,
    visionsOfVillainy,
    whiplashVengefulEngineer,
    widowSBite,
    yellowjacketHeartlessMarauder,
    avengersDisassembled,
    blazingCrescendo,
    crimsonOperative,
    deathToOurEnemies,
    evilSThrall,
    finFangFoom,
    hawkeyeMasterMarksman,
    hawkeyeYoungAvenger,
    hawkeyeSBow,
    hexMagic,
    hireACrew,
    hULKSMASH,
    humanTorchJohnnyStorm,
    hYDRAAssaultRobot,
    ironFistLivingWeapon,
    jessicaJonesPrivateEye,
    kUnLunWarrior,
    kreeSentinel,
    lightningStrike,
    lokiLaufeyson,
    machinesmithAutomaton,
    mistyKnightHeroForHire,
    mjLnirHammerOfThor,
    photonBlastBarrage,
    quicksilverBrashBlur,
    redHulk,
    repulsorBlast,
    theScarletWitch,
    speedYoungAvenger,
    starkIndustriesExecutive,
    superSpeed,
    teamTactics,
    thorGodOfThunder,
    truckToss,
    visionOfLove,
    volcanicVillain,
    wonderManHollywoodHero,
    antManSArmy,
    callDamageControl,
    claimTheKingdom,
    docSamsonSuperPsychiatrist,
    earthSMightiestHeroes,
    epicFight,
    giantGrowth,
    goNuts,
    guerrillaGorilla,
    hellcatUndyingVigilante,
    herculesPrinceOfPower,
    heroicFeast,
    hulklingBurgeoningBruiser,
    kaZarOfTheSavageLand,
    knightOfWundagore,
    misterHydeMonsterWithin,
    moleManMoloidMaster,
    petAvengers,
    powerfulBroker,
    punishingPunch,
    rapidRescue,
    reptilDinomorpher,
    restorativeTechnique,
    rickJonesDestinedSidekick,
    savageLandDinosaur,
    serpentSpecialist,
    shangChiMasterOfKungFu,
    sheHulkJadeDefender,
    superStrength,
    theThingBenGrimm,
    tigraFelineFury,
    trainingRegimen,
    theUnbeatableSquirrelGirl,
    undercoverSkrull,
    wakandanRoyalGuard,
    whiteTigerAvaAyala,
    worldWarHulk,
    abominationTerrifyingTitan,
    absorbingMan,
    alienInvasion,
    antManColonyCommander,
    aresGodOfWar,
    armorWars,
    theAstonishingAntMan,
    avengersUnderSiege,
    beastEruditeAerialist,
    blackPantherVanguard,
    blackWidowDoubleAgent,
    bullseyeDeathDealer,
    captainAmericaLivingLegend,
    cloakAndDaggerEntwined,
    theComingOfGalactus,
    daredevilManWithoutFear,
    ghostSpectralSaboteur,
    hulkGammaGoliath,
    ironManMasterOfMachines,
    kangTemporalTyrant,
    killmongerScourgeOfWakanda,
    kingTChalla,
    theKingpinOfCrime,
    madameHydra,
    theMightyThorJaneFoster,
    moonGirlAndDevilDinosaur,
    theRuinousWreckingCrew,
    scientistSupremeOfAIM,
    theSerpentSociety,
    speedballNewWarrior,
    spiderManToTheRescue,
    spiderWomanSecretAgent,
    stormWindrider,
    theSuperHeroCivilWar,
    taskmasterMercenaryMimic,
    thanosTheMadTitan,
    thorOdinson,
    titaniaRuggedRumbler,
    uSAgentJohnWalker,
    visionQuest,
    warMachineLegacyOfIron,
    winterSoldierIcyAssassin,
    wolverineFierceFighter,
    worldsWithinWorlds,
    aIMSynthoids,
    arcReactor,
    captainAmericaSShield,
    cosmicCube,
    dependableQuinjet,
    hERBIEScoutUnit,
    ironManArmor,
    sHIELDHelicarrier,
    superAdaptoid,
    theTenRings,
    ultronArtificialMalevolence,
    ultronDrone,
    vibraniumEnergyDaggers,
    theVision,
    vivVisionTeenSynthezoid,
    aIMLabs,
    asgardianCitadel,
    avengersHangar,
    avengersTower,
    baxterBuilding,
    birninZanaPlaza,
    castleDoom,
    darkFortress,
    fiskTower,
    gatheringPlace,
    gleamingBastion,
    hellSKitchen,
    hiddenLair,
    losDiablosMissileBase,
    pymTechnologies,
    starkIndustries,
    subterraneanCavern,
    surveillanceRoom,
    trainingCompound,
    villainousHideout,
    plains,
    island,
    swamp,
    mountain,
    forest
  ]

#guard kingpinSEnforcers.keywords.lifelink
#guard kingpinSEnforcers.activatedAbilities.size == 1
#guard kingpinSEnforcers.activatedAbilities[0]!.cost.sacrificeAnotherCreatureOrArtifact
#guard kingpinSEnforcers.activatedAbilities[0]!.effect == Effect.abilityDraw 1
#guard kreeSentinel.keywords.reach
#guard kreeSentinel.activatedAbilities.size == 1
#guard kreeSentinel.activatedAbilities[0]!.activateFromHand
#guard kreeSentinel.activatedAbilities[0]!.cost.discardSource
#guard kreeSentinel.activatedAbilities[0]!.effect ==
  Effect.searchLandTypeToHand "Basic land"
#guard savageLandDinosaur.keywords.trample
#guard savageLandDinosaur.activatedAbilities.size == 1
#guard savageLandDinosaur.activatedAbilities[0]!.activateFromHand
#guard savageLandDinosaur.activatedAbilities[0]!.cost.discardSource
#guard savageLandDinosaur.activatedAbilities[0]!.effect ==
  Effect.searchLandTypeToHand "Basic land"
#guard mshCards.size >= 281
#guard mshCards.all (fun c => c.name != "")
#guard agentOfAtlas.keywords.prowess
#guard agentOfAtlas.hasSubtype "Spy"
#guard kreeCommandos.keywords.flying
#guard kreeCommandos.keywords.vigilance
#guard kreeCommandos.keywords.prowess
#guard crimsonOperative.keywords.prowess
#guard crimsonOperative.triggeredAbilities == #[.onEnterExileTop]
#guard atlanteanCavalry.keywords.vigilance
#guard atlanteanCavalry.triggeredAbilities == #[.onDrawSecondPlusOne]
#guard ghostSpectralSaboteur.keywords.flash
#guard ghostSpectralSaboteur.keywords.cantBeBlocked
#guard ghostSpectralSaboteur.hasSupertype .legendary
#guard thorOdinson.keywords.flying
#guard thorOdinson.keywords.vigilance
#guard thorOdinson.keywords.prowess

end Mtg.Engine.Catalog
