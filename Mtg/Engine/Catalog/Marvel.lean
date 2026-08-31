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
  card "The Sensational She-Hulk" #[.creature] ({ symbols := #[.generic 3, .colored .green, .colored .white, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Gamma", "Hero"])
    (oracleText := "Reach, trample\nYour opponents can't cast spells during your turn.\nWhenever a creature you control is dealt damage, you may have The Sensational She-Hulk deal that much damage to any target. Do this only once each turn.")
    (power := some 6)
    (toughness := some 6)
    (keywords := (Keyword.reach).merge Keyword.trample)
    (triggeredAbilities := #[.onWatch .sheHulkRedirectOnce])
    (staticAbilities := #[StaticAbility.opponentsCantCastOnYourTurn])

def photonLivingLight : CardDef :=
  card "Photon, Living Light" #[.creature] ({ symbols := #[.generic 2, .colored .red, .colored .white, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Elemental", "Hero"])
    (oracleText := "Flying, hexproof, prowess\nWhenever you cast a noncreature spell, put a +1/+1 counter on each other creature you control.")
    (power := some 4)
    (toughness := some 4)
    (keywords := ((Keyword.flying).merge Keyword.hexproof).merge Keyword.prowess)
    (triggeredAbilities := #[.onCasting .plusOneEachOther])

def theIncredibleHulk : CardDef :=
  card "The Incredible Hulk" #[.creature] ({ symbols := #[.generic 2, .colored .red, .colored .red, .colored .green, .colored .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Gamma", "Berserker", "Hero"])
    (oracleText := "Reach, trample\nEnrage — Whenever The Incredible Hulk is dealt damage, put a +1/+1 counter on him. If he's attacking, untap him and there is an additional combat phase after this phase.")
    (power := some 8)
    (toughness := some 8)
    (keywords := (Keyword.reach).merge Keyword.trample)
    (triggeredAbilities := #[.onWatch .hulk])

def theInvincibleIronMan : CardDef :=
  card "The Invincible Iron Man" #[.artifact, .creature] ({ symbols := #[.generic 4, .colored .blue, .colored .red] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Flying, haste\nAt the beginning of combat on your turn, you may put an artifact card from your hand onto the battlefield. If it's an Equipment, attach it to The Invincible Iron Man.")
    (power := some 5)
    (toughness := some 5)
    (keywords := (Keyword.flying).merge Keyword.haste)
    (triggeredAbilities := #[.onCombatMayPutArtifactAttachEquipment])

def blackPantherHopeEnduring : CardDef :=
  card "Black Panther, Hope Enduring" #[.creature] ({ symbols := #[.generic 4, .colored .white, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Warrior", "Hero"])
    (oracleText := "Flash\nDouble strike\nPrevent all damage that would be dealt to Black Panther.\nWhenever Black Panther deals combat damage to a player, draw a card.")
    (power := some 3)
    (toughness := some 3)
    (keywords := (Keyword.flash).merge Keyword.doubleStrike)
    (triggeredAbilities := #[.onCombatDamageDraw 1])
    (staticAbilities := #[StaticAbility.preventAllDamageToThis])

def agent13SharonCarter : CardDef :=
  card "Agent 13, Sharon Carter" #[.creature] ({ symbols := #[.generic 2, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Spy", "Hero"])
    (oracleText := "Whenever a creature you control attacks alone, investigate. (Create a Clue token. It's an artifact with \"{2}, Sacrifice this token: Draw a card.\")")
    (power := some 3)
    (toughness := some 2)
    (triggeredAbilities := #[.onCreatureYouControlAttacksAloneInvestigate])

def agentMariaHill : CardDef :=
  card "Agent Maria Hill" #[.creature] ({ symbols := #[.colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Spy", "Hero"])
    (oracleText := "Whenever Agent Maria Hill becomes tapped to pay a teamwork cost, put a +1/+1 counter on her and draw a card.")
    (power := some 2)
    (toughness := some 1)
    (triggeredAbilities := #[.onTappedForTeamworkPlusOneAndDraw])

def agentOfAtlas : CardDef :=
  card "Agent of Atlas" #[.creature] ({ symbols := #[.generic 1, .colored .white] })
    (subtypes := #["Human", "Spy", "Hero"])
    (oracleText := "Prowess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn.)")
    (power := some 2)
    (toughness := some 2)
    (keywords := Keyword.prowess)

def agentPhilCoulson : CardDef :=
  card "Agent Phil Coulson" #[.creature] ({ symbols := #[.generic 1, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Spy", "Hero"])
    (oracleText := "Vigilance\n{T}: Put a +1/+1 counter on each other Hero you control.")
    (power := some 2)
    (toughness := some 2)
    (keywords := Keyword.vigilance)
    (activatedAbilities := #[activated (Effect.ofAbility (.plusOneOnEachOtherSubtype "Hero" 1)) (ManaCost.empty) (tap := true)])

def agentsOfSHIELD : CardDef :=
  card "Agents of S.H.I.E.L.D." #[.creature] ({ symbols := #[.generic 2, .colored .white] })
    (subtypes := #["Human", "Spy", "Hero"])
    (oracleText := "Whenever a creature you control attacks alone, that creature gets +1/+1 until end of turn.")
    (power := some 2)
    (toughness := some 4)
    (triggeredAbilities := #[.onCreatureYouControlAttacksAlonePump 1 1])

def avengersAssemble : CardDef :=
  card "Avengers Assemble!" #[.enchantment] ({ symbols := #[.generic 4, .colored .white] })
    (oracleText := "Flash\nHeroes you control get +2/+2.\nAt the beginning of each end step, if you attacked with a Hero this turn or a Hero entered the battlefield under your control this turn, draw a card.")
    (keywords := Keyword.flash)
    (triggeredAbilities := #[.onEachEndStepDrawIfAttackedOrEnteredSubtype "Hero"])
    (staticAbilities := #[StaticAbility.creaturesYouControlOfSubtypeGet "Hero" 2 2])

def boroughBackup : CardDef :=
  card "Borough Backup" #[.sorcery] ({ symbols := #[.generic 4, .colored .white] })
    (oracleText := "Create two 3/2 white Hero creature tokens with vigilance.\nBasic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)")
    (activatedAbilities := #[typecyclingAbility "Basic land" (ManaCost.ofGeneric 2)])
    (spellEffect := some (Effect.ofSpell (.createTokens .hero32vigilance 2)))

def braveBrawler : CardDef :=
  card "Brave Brawler" #[.creature] ({ symbols := #[.generic 1, .colored .white] })
    (subtypes := #["Human", "Warrior", "Hero"])
    (oracleText := "Lifelink\nPower-up — {4}{W}: Put two +1/+1 counters on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)")
    (power := some 2)
    (toughness := some 1)
    (keywords := Keyword.lifelink)
    (activatedAbilities := #[powerUpAbility (Effect.ofAbility (.putPlusOnePlusOneOnSource 2)) ({ symbols := #[.generic 4, .colored .white] })])

def captainAmericaSuperSoldier : CardDef :=
  card "Captain America, Super-Soldier" #[.creature] ({ symbols := #[.generic 1, .colored .white, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Soldier", "Hero"])
    (oracleText := "First strike\nCaptain America enters with a shield counter on him. (If he would be dealt damage or destroyed, remove a shield counter from him instead.)\nAs long as Captain America has a shield counter on him, you and other Heroes you control have hexproof.")
    (power := some 3)
    (toughness := some 2)
    (keywords := Keyword.firstStrike)
    (entersWithShield := 1)
    (staticAbilities := #[StaticAbility.youAndOtherSubtypeHaveHexproofIfShield "Hero"])

def captainAmericaWingsOfFreedom : CardDef :=
  card "Captain America, Wings of Freedom" #[.creature] ({ symbols := #[.generic 2, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Soldier", "Hero"])
    (oracleText := "Flying, first strike, ward {1}\nWhenever Captain America attacks, each other Hero you control gets +X/+X until end of turn, where X is Captain America's toughness.")
    (power := some 3)
    (toughness := some 1)
    (keywords := (Keyword.flying).merge Keyword.firstStrike)
    (ward := some 1)
    (triggeredAbilities := #[.onAttackOthersOfSubtypeGetEqualToughness "Hero"])

def captainMarvelEarthSProtector : CardDef :=
  card "Captain Marvel, Earth's Protector" #[.creature] ({ symbols := #[.generic 3, .colored .white, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Kree", "Hero"])
    (oracleText := "Flash\nFlying, lifelink\nPower-up — {5}{W}{W}: Put a +1/+1 counter and an indestructible counter on Captain Marvel. (Activate each power-up ability only once. Reduce the cost by her mana cost if she entered this turn.)")
    (power := some 5)
    (toughness := some 4)
    (keywords := ((Keyword.flash).merge Keyword.flying).merge Keyword.lifelink)
    (activatedAbilities := #[activated (Effect.ofAbility (.plusOneAndIndestructibleCounter)) ({ symbols := #[.generic 5, .colored .white, .colored .white] }) (powerUp := true)])

def captainMarVellSpaceBorn : CardDef :=
  card "Captain Mar-Vell, Space-Born" #[.creature] ({ symbols := #[.generic 4, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Kree", "Soldier", "Hero"])
    (oracleText := "Flying, vigilance\nCosmic Awareness — As long as an opponent has cast a spell this turn, you may cast spells as though they had flash.")
    (power := some 4)
    (toughness := some 4)
    (keywords := (Keyword.flying).merge Keyword.vigilance)
    (staticAbilities := #[StaticAbility.flashIfOpponentCastThisTurn])

def colleenWingStreetSamurai : CardDef :=
  card "Colleen Wing, Street Samurai" #[.creature] ({ symbols := #[.generic 1, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Samurai", "Hero"])
    (oracleText := "Whenever you cast a spell that targets a creature you control, put a +1/+1 counter on Colleen Wing. Scry 1. (Look at the top card of your library. You may put that card on the bottom.)")
    (power := some 2)
    (toughness := some 2)
    (triggeredAbilities := #[.onCasting .plusOneScry])

def crowdOfTrueBelievers : CardDef :=
  card "Crowd of True Believers" #[.creature] ({ symbols := #[.colored .white] })
    (subtypes := #["Human", "Citizen"])
    (oracleText := "{T}: Target creature you control that's attacking alone gets +1/+0 until end of turn. You gain 1 life.")
    (power := some 1)
    (toughness := some 2)
    (activatedAbilities := #[activated (Effect.ofAbility .pumpAttackingAloneGainLife) (ManaCost.empty) (tap := true)])

def helicarrierStrike : CardDef :=
  card "Helicarrier Strike" #[.instant] ({ symbols := #[.colored .white] })
    (oracleText := "Teamwork 2 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 2 or more.)\nHelicarrier Strike deals 2 damage to target attacking or blocking creature. If this spell was cast using teamwork, it deals 4 damage to that creature instead.")
    (teamwork := some 2)
    (spellEffect := some (Effect.ofSpell (.dealDamageToAttackerOrBlocker 2 4)))

def heroInTraining : CardDef :=
  card "Hero in Training" #[.creature] ({ symbols := #[.generic 2, .colored .white] })
    (subtypes := #["Human", "Hero"])
    (oracleText := "When this creature enters, draw a card. If you control another Hero, you gain 2 life.")
    (power := some 2)
    (toughness := some 2)
    (triggeredAbilities := #[.onEnterDrawGainLifeIfAnotherHero])

def invisibleWomanSueStorm : CardDef :=
  card "Invisible Woman, Sue Storm" #[.creature] ({ symbols := #[.generic 4, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Lifelink\nWhenever you put one or more +1/+1 counters on one or more other Heroes you control, you may create a 0/4 colorless Wall creature token with defender.")
    (power := some 2)
    (toughness := some 5)
    (keywords := Keyword.lifelink)
    (triggeredAbilities := #[.onResource .plusOneOnHeroesCreateWall])

def jenniferWalters : CardDef :=
  card "Jennifer Walters" #[.creature] ({ symbols := #[.generic 1, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Advisor", "Hero"])
    (oracleText := "Your opponents can't cast spells during your turn.\n{3}{G}{W}{W}: Transform Jennifer Walters. Activate only as a sorcery.")
    (power := some 2)
    (toughness := some 3)
    (staticAbilities := #[StaticAbility.opponentsCantCastOnYourTurn])
    (activatedAbilities := #[activated (Effect.ofAbility (.transform)) ({ symbols := #[.generic 3, .colored .green, .colored .white, .colored .white] }) (onlyAsSorcery := true)])
    (otherFace := some theSensationalSheHulk)

def kreeCommandos : CardDef :=
  card "Kree Commandos" #[.creature] ({ symbols := #[.generic 2, .colored .white] })
    (subtypes := #["Kree", "Soldier", "Villain"])
    (oracleText := "Flying, vigilance\nProwess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn.)")
    (power := some 2)
    (toughness := some 1)
    (keywords := ((Keyword.flying).merge Keyword.vigilance).merge Keyword.prowess)

def lukeCagePowerMan : CardDef :=
  card "Luke Cage, Power Man" #[.creature] ({ symbols := #[.generic 3, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Unbreakable Skin — Whenever Luke Cage attacks alone, he gets +2/+0 and gains indestructible until end of turn. (Damage and effects that say \"destroy\" don't destroy him.)")
    (power := some 2)
    (toughness := some 5)
    (triggeredAbilities := #[.onThisAttack .attacksAlonePlus2Indestructible])

def theMindStone : CardDef :=
  card "The Mind Stone" #[.artifact] ({ symbols := #[.generic 1, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Infinity", "Stone"])
    (oracleText := "Indestructible\n{T}: Add {W}.\n{5}{W}, {T}: Harness The Mind Stone. (Once harnessed, its ∞ ability is active.)\n∞ — At the beginning of your end step, exile up to one other target nonland permanent you control, then return that card to the battlefield under its owner's control.")
    (keywords := Keyword.indestructible)
    (triggeredAbilities := #[.onStep .harnessedFlicker])
    (tapAddMana := #[.colored .white])
    (activatedAbilities := #[activated (Effect.ofAbility .harnessInfinityStone) ({ symbols := #[.generic 5, .colored .white] }) (tap := true)])

def mockingbirdAceAgent : CardDef :=
  card "Mockingbird, Ace Agent" #[.creature] ({ symbols := #[.generic 3, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Spy", "Hero"])
    (oracleText := "Double strike\nWhenever you cast a spell that targets a creature you control, put a +1/+1 counter on Mockingbird.")
    (power := some 2)
    (toughness := some 2)
    (keywords := Keyword.doubleStrike)
    (triggeredAbilities := #[.onCasting .plusOneThis])

def monicaRambeau : CardDef :=
  card "Monica Rambeau" #[.creature] ({ symbols := #[.generic 2, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Flying, prowess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn.)\n{2}{R}{W}{W}: Transform Monica Rambeau. Activate only as a sorcery.")
    (power := some 3)
    (toughness := some 3)
    (keywords := (Keyword.flying).merge Keyword.prowess)
    (activatedAbilities := #[activated (Effect.ofAbility (.transform)) ({ symbols := #[.generic 2, .colored .red, .colored .white, .colored .white] }) (onlyAsSorcery := true)])
    (otherFace := some photonLivingLight)

def murdockSCrusade : CardDef :=
  card "Murdock's Crusade" #[.sorcery] ({ symbols := #[.generic 1, .colored .white] })
    (oracleText := "Teamwork 4 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 4 or more.)\nChoose one. If this spell was cast using teamwork, choose both instead.\n• Street Justice — Exile target creature with toughness 4 or greater.\n• Legal Justice — Exile target enchantment with mana value 4 or greater.")
    (teamwork := some 4)
    (spellModes := #[(Effect.ofSpell (.exileCreatureToughnessAtLeast 4)), (Effect.ofSpell (.exileEnchantmentMvAtLeast 4))])
    (chooseBothIfTeamwork := true)

def nickFuryAgentOfSHIELD : CardDef :=
  card "Nick Fury, Agent of S.H.I.E.L.D." #[.creature] ({ symbols := #[.colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Spy", "Hero"])
    (oracleText := "Power-up — {W}{U}{B}{R}{G}: Put two +1/+1 counters on Nick Fury, then look at the top seven cards of your library. You may put a Hero, Equipment, or Vehicle card from among them onto the battlefield. If it's a double-faced card, you may transform it. Put the rest on the bottom of your library in a random order. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)")
    (power := some 2)
    (toughness := some 1)
    (activatedAbilities := #[activated (Effect.ofAbility (.lookAtTopPutHeroEquipVehicle 7)) ({ symbols := #[.colored .white, .colored .blue, .colored .black, .colored .red, .colored .green] }) (powerUp := true)])

def nightNurseHealerOfHeroes : CardDef :=
  card "Night Nurse, Healer of Heroes" #[.creature] ({ symbols := #[.generic 1, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Doctor", "Hero"])
    (oracleText := "Flash\nLifelink\nWhen Night Nurse enters, choose target permanent card in your graveyard that was put there from anywhere this turn. Return it to your hand.")
    (power := some 2)
    (toughness := some 1)
    (keywords := (Keyword.flash).merge Keyword.lifelink)
    (triggeredAbilities := #[.onEnter .returnGyPermanentThisTurn])

def okoyeDoraMilajeLeader : CardDef :=
  card "Okoye, Dora Milaje Leader" #[.creature] ({ symbols := #[.generic 3, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Warrior", "Hero"])
    (oracleText := "When Okoye enters, create two 1/1 white Soldier creature tokens.\nAttacking creature tokens you control have first strike.")
    (power := some 3)
    (toughness := some 2)
    (triggeredAbilities := #[.onEnterCreateTokens .soldier11white 2])
    (staticAbilities := #[StaticAbility.attackingTokensHave Keyword.firstStrike])

def originOfTheAvengers : CardDef :=
  card "Origin of the Avengers" #[.enchantment] ({ symbols := #[.generic 1, .colored .white] })
    (subtypes := #["Saga"])
    (oracleText := "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)\nI — Scry 2.\nII — You may put a Hero creature card with mana value 3 or less from your hand onto the battlefield. If you don't, draw a card.\nIII — Put a +1/+1 counter on each creature you control.")
    (saga := some { sacrificeAfter := "III", chapters := #[chapter "I" "Scry 2." (.spell (.scry 2)), chapter "II" "You may put a Hero creature card with mana value 3 or less from your hand onto the battlefield. If you don't, draw a card." (.spell (.mayPutHeroMvOrDraw 3)), chapter "III" "Put a +1/+1 counter on each creature you control." (.spell (.plusOneOnEachYouControl))] })

def pantherPounce : CardDef :=
  card "Panther Pounce" #[.instant] ({ symbols := #[.colored .white] })
    (oracleText := "Target player investigates. Target creature gets +1/+0 and gains flying until end of turn. Untap it. (To investigate, create a Clue token. It's an artifact with \"{2}, Sacrifice this token: Draw a card.\")")
    (spellEffect := some (Effect.ofSpell (.investigatePumpFlyingUntap)))

def patriotShieldWielder : CardDef :=
  card "Patriot, Shield Wielder" #[.creature] ({ symbols := #[.generic 1, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "{2}, {T}: Another target creature you control gets +2/+0 and gains hexproof until end of turn. (It can't be the target of spells or abilities your opponents control.)")
    (power := some 2)
    (toughness := some 2)
    (activatedAbilities := #[activated (Effect.ofAbility (.anotherYouControlGetsAndGrant 2 0 Keyword.hexproof)) ({ symbols := #[.generic 2] }) (tap := true)])

def politicalTriumph : CardDef :=
  card "Political Triumph" #[.enchantment] ({ symbols := #[.colored .white] })
    (subtypes := #["Plan"])
    (oracleText := "Whenever a creature you control enters, scry 1 and put a plan counter on this enchantment.\nWhen the fourth plan counter is put on this enchantment, sacrifice it, draw a card, and put a +1/+1 counter on each creature you control.")
    (triggeredAbilities := #[.onCreatureYouControlEntersScryAndPlan 1, .onFourthPlanDrawPlusOneEach])

def quakeAgentOfSHIELD : CardDef :=
  card "Quake, Agent of S.H.I.E.L.D." #[.creature] ({ symbols := #[.generic 2, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Inhuman", "Spy", "Hero"])
    (oracleText := "Seismic Takedown — Whenever you cast a noncreature spell, tap target creature or land.")
    (power := some 3)
    (toughness := some 3)
    (triggeredAbilities := #[.onCasting .tapCreatureOrLand])

def raftSecurityOfficer : CardDef :=
  card "Raft Security Officer" #[.creature] ({ symbols := #[.generic 1, .colored .white] })
    (subtypes := #["Human", "Soldier"])
    (oracleText := "{2}, {T}: Tap target creature. This ability costs {1} less to activate if it targets a creature with power 3 or less.")
    (power := some 1)
    (toughness := some 3)
    (activatedAbilities := #[activated (Effect.ofAbility .tapTargetCreature) ({ symbols := #[.generic 2] }) (tap := true)
      (costReductionIfTargetPowerAtMost := some (1, 3))])

def redGuardianSuperSoldier : CardDef :=
  card "Red Guardian, Super-Soldier" #[.creature] ({ symbols := #[.generic 2, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Soldier", "Villain"])
    (oracleText := "Flash\nWhen Red Guardian enters, destroy target creature an opponent controls that dealt damage this turn.")
    (power := some 2)
    (toughness := some 2)
    (keywords := Keyword.flash)
    (triggeredAbilities := #[.onEnter (.destroy .oppCreatureDealtDamageThisTurn)])

def theSentryGoldenGuardian : CardDef :=
  card "The Sentry, Golden Guardian" #[.creature] ({ symbols := #[.generic 3, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Flying, vigilance, indestructible\nWhen The Sentry enters, target opponent creates The Void, a legendary 5/5 black Horror Villain creature token with flying, indestructible, and \"The Void attacks each combat if able.\"")
    (power := some 5)
    (toughness := some 5)
    (keywords := ((Keyword.flying).merge Keyword.vigilance).merge Keyword.indestructible)
    (triggeredAbilities := #[.onEnter .oppCreatesTheVoid])

def sHIELDSpyKit : CardDef :=
  card "S.H.I.E.L.D. Spy Kit" #[.artifact] ({ symbols := #[.colored .white] })
    (subtypes := #["Equipment"])
    (oracleText := "Equipped creature gets +1/+1.\nWhenever equipped creature attacks alone, untap it and scry 1. (Look at the top card of your library. You may put that card on the bottom.)\nEquip {1} ({1}: Attach to target creature you control. Equip only as a sorcery.)")
    (triggeredAbilities := #[.onWatch .equippedAttacksAloneUntapScry])
    (staticAbilities := #[StaticAbility.equippedCreatureGets 1 1])
    (activatedAbilities := #[equipAbility ({ symbols := #[.generic 1] })])

def superVillainLockup : CardDef :=
  card "Super Villain Lockup" #[.enchantment] ({ symbols := #[.generic 1, .colored .white] })
    (oracleText := "Flash\nWhen this enchantment enters, exile target tapped creature an opponent controls until this enchantment leaves the battlefield.")
    (keywords := Keyword.flash)
    (triggeredAbilities := #[.onEnterExileOppTappedUntilLeaves])

def superSoldierSerum : CardDef :=
  card "Super-Soldier Serum" #[.enchantment] ({ symbols := #[.generic 1, .colored .white] })
    (subtypes := #["Aura"])
    (oracleText := "Enchant creature\nEnchanted creature gets +2/+2, has first strike and vigilance, and is a legendary Soldier in addition to its other types.\nWhenever enchanted creature attacks or blocks, attach any number of target Equipment you control to it.")
    (triggeredAbilities := #[.onWatch .enchantedAttachEquipment])
    (staticAbilities := #[StaticAbility.enchantedCreatureGetsHasAndTypes 2 2
      (Keyword.firstStrike.merge Keyword.vigilance) #["legendary", "Soldier"]])

def takeUpTheShield : CardDef :=
  card "Take Up the Shield" #[.instant] ({ symbols := #[.generic 1, .colored .white] })
    (oracleText := "Put a +1/+1 counter on target creature. It gains lifelink and indestructible until end of turn. (Damage and effects that say \"destroy\" don't destroy it.)")
    (spellEffect := some (Effect.ofSpell (.plusOneLifelinkIndestructible)))

def wakandanDroneFlock : CardDef :=
  card "Wakandan Drone Flock" #[.artifact, .creature] ({ symbols := #[.generic 3, .colored .white] })
    (subtypes := #["Robot"])
    (oracleText := "Flying\nWhen this creature enters, scry 2. (Look at the top two cards of your library, then put any number of them on the bottom and the rest on top in any order.)")
    (power := some 3)
    (toughness := some 3)
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onEnterScry 2])

def webUp : CardDef :=
  card "Web Up" #[.enchantment] ({ symbols := #[.generic 2, .colored .white] })
    (oracleText := "When this enchantment enters, exile target nonland permanent an opponent controls until this enchantment leaves the battlefield.")
    (triggeredAbilities := #[.onEnterExileOppNonlandUntilLeaves])

def whiteWidowFreeAgent : CardDef :=
  card "White Widow, Free Agent" #[.creature] ({ symbols := #[.generic 3, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero", "Villain"])
    (oracleText := "When White Widow enters, choose one —\n• Put a +1/+1 counter on each of up to two target creatures.\n• Return target artifact or enchantment card from your graveyard to your hand.")
    (power := some 2)
    (toughness := some 3)
    (triggeredAbilities := #[.onEnter .plusOnesOrReturnArtEnch])

def aerialDoombot : CardDef :=
  card "Aerial Doombot" #[.artifact, .creature] ({ symbols := #[.colored .blue] })
    (subtypes := #["Robot", "Villain"])
    (oracleText := "Flying\nPower-up — {5}{U}: Put three +1/+1 counters on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)")
    (power := some 1)
    (toughness := some 1)
    (keywords := Keyword.flying)
    (activatedAbilities := #[powerUpAbility (Effect.ofAbility (.putPlusOnePlusOneOnSource 3)) ({ symbols := #[.generic 5, .colored .blue] })])

def aIMScientists : CardDef :=
  card "A.I.M. Scientists" #[.creature] ({ symbols := #[.generic 3, .colored .blue] })
    (subtypes := #["Human", "Scientist", "Villain"])
    (oracleText := "When this creature enters, it connives. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on this creature.)\nBasic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)")
    (power := some 3)
    (toughness := some 3)
    (triggeredAbilities := #[.onEnterConnive])
    (activatedAbilities := #[typecyclingAbility "Basic land" (ManaCost.ofGeneric 2)])

def atlanteanCavalry : CardDef :=
  card "Atlantean Cavalry" #[.creature] ({ symbols := #[.generic 2, .colored .blue] })
    (subtypes := #["Merfolk", "Soldier"])
    (oracleText := "Vigilance\nWhenever you draw your second card each turn, put a +1/+1 counter on this creature.")
    (power := some 3)
    (toughness := some 2)
    (keywords := Keyword.vigilance)
    (triggeredAbilities := #[.onDrawSecondPlusOne])

def atlantisAttacks : CardDef :=
  card "Atlantis Attacks" #[.sorcery] ({ symbols := #[.generic 5, .colored .blue, .colored .blue] })
    (oracleText := "Teamwork 4 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 4 or more.)\nChoose one. If this spell was cast using teamwork, choose both instead.\n• Target player creates a 6/5 blue Leviathan creature token with hexproof.\n• Return one or two target nonland permanents to their owners' hands.")
    (teamwork := some 4)
    (spellModes := #[(Effect.ofSpell (.targetPlayerCreatesTokens .leviathan65hexproof 1)), (Effect.ofSpell .returnOneOrTwoNonlands)])
    (chooseBothIfTeamwork := true)

def attumaAtlanteanWarlord : CardDef :=
  card "Attuma, Atlantean Warlord" #[.creature] ({ symbols := #[.generic 2, .colored .blue, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Merfolk", "Warrior", "Villain"])
    (oracleText := "Other Merfolk you control get +1/+1.\nWhenever one or more Merfolk you control attack a player, draw a card.")
    (power := some 3)
    (toughness := some 4)
    (triggeredAbilities := #[.onWatch .merfolkAttackDraw])
    (staticAbilities := #[StaticAbility.otherCreaturesGet #["Merfolk"] 1 1])

def boldBiochemist : CardDef :=
  card "Bold Biochemist" #[.creature] ({ symbols := #[.generic 1, .colored .blue] })
    (subtypes := #["Human", "Scientist"])
    (oracleText := "Power-up — {5}{U}: Put a +1/+1 counter on this creature and draw two cards. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)")
    (power := some 1)
    (toughness := some 3)
    (activatedAbilities := #[activated (Effect.ofAbility (.plusOneAndDraw 1 2)) ({ symbols := #[.generic 5, .colored .blue] }) (powerUp := true)])

def bruceBanner : CardDef :=
  card "Bruce Banner" #[.creature] ({ symbols := #[.colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Scientist", "Hero"])
    (oracleText := "{X}{X}, {T}: Draw X cards. Activate only as a sorcery.\n{2}{R}{R}{G}{G}: Transform Bruce Banner. Activate only as a sorcery.")
    (power := some 1)
    (toughness := some 1)
    (activatedAbilities := #[activated (Effect.ofAbility (.drawX)) ({ symbols := #[.x, .x] }) (tap := true) (onlyAsSorcery := true), activated (Effect.ofAbility (.transform)) ({ symbols := #[.generic 2, .colored .red, .colored .red, .colored .green, .colored .green] }) (onlyAsSorcery := true)])
    (otherFace := some theIncredibleHulk)

def depower : CardDef :=
  card "Depower" #[.instant] ({ symbols := #[.generic 2, .colored .blue] })
    (oracleText := "This spell costs {2} less to cast if it targets an attacking creature.\nTarget creature gets -4/-0 until end of turn.\nDraw a card.")
    (costReductionIfTargetAttacking := 2)
    (spellEffect := some (Effect.ofSpell (.pumpThenDraw (-4) 0)))

def echoPerceptiveProdigy : CardDef :=
  card "Echo, Perceptive Prodigy" #[.creature] ({ symbols := #[.generic 2, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Vigilance\n{1}, {T}: Copy target activated or triggered ability you control from a creature source. You may choose new targets for the copy. (Mana abilities can't be targeted.)")
    (power := some 1)
    (toughness := some 4)
    (keywords := Keyword.vigilance)
    (activatedAbilities := #[activated (Effect.ofAbility (.copyControlledAbility true)) ({ symbols := #[.generic 1] }) (tap := true)])

def falconWingedWonder : CardDef :=
  card "Falcon, Winged Wonder" #[.creature] ({ symbols := #[.generic 4, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Flying\nAvian Telepathy — When Falcon enters, create Redwing, a legendary 1/1 blue Bird Scout creature token with flying and \"Whenever Redwing attacks, surveil 1.\" (Look at the top card of your library. You may put it into your graveyard.)")
    (power := some 3)
    (toughness := some 4)
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onEnter .createRedwing])

def falconSWingHarness : CardDef :=
  card "Falcon's Wing Harness" #[.artifact] ({ symbols := #[.generic 1, .colored .blue] })
    (subtypes := #["Equipment"])
    (oracleText := "When this Equipment enters, attach it to target creature you control.\nEquipped creature gets +1/+1 and has flying and ward {1}. (Whenever equipped creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {1}.)\nEquip {2}{U} ({2}{U}: Attach to target creature you control. Equip only as a sorcery.)")
    (triggeredAbilities := #[.onEnterAttachToCreatureYouControl])
    (staticAbilities := #[StaticAbility.equippedCreatureGetsHasAndWard 1 1 Keyword.flying 1])
    (activatedAbilities := #[equipAbility ({ symbols := #[.generic 2, .colored .blue] })])

def frozenInIce : CardDef :=
  card "Frozen in Ice" #[.enchantment] ({ symbols := #[.generic 2, .colored .blue] })
    (subtypes := #["Aura"])
    (oracleText := "Enchant creature\nWhen this Aura enters, tap enchanted creature.\nEnchanted creature loses all abilities and can't become untapped.")
    (triggeredAbilities := #[.onEnterEnchanted .tap])
    (staticAbilities := #[StaticAbility.enchantedLosesAbilitiesCantUntap])

def futuristForge : CardDef :=
  card "Futurist Forge" #[.artifact] ({ symbols := #[.generic 1, .colored .blue] })
    (oracleText := "When this artifact enters, draw a card.\n{3}{U}, Sacrifice this artifact: Draw two cards.")
    (triggeredAbilities := #[.onEnterDraw 1])
    (activatedAbilities := #[activated (Effect.ofAbility (.draw 2)) ({ symbols := #[.generic 3, .colored .blue] }) (sacrificeSource := true)])

def giantSizedFlyingAnt : CardDef :=
  card "Giant-Sized Flying Ant" #[.creature] ({ symbols := #[.generic 3, .colored .blue] })
    (subtypes := #["Insect"])
    (oracleText := "Flash\nFlying\nWhen this creature enters, choose one —\n• Tap target nonland permanent.\n• Untap target nonland permanent.")
    (power := some 3)
    (toughness := some 2)
    (keywords := (Keyword.flash).merge Keyword.flying)
    (triggeredAbilities := #[.onEnterTapOrUntapNonland])

def hydraulicHelper : CardDef :=
  card "Hydraulic Helper" #[.artifact, .creature] ({ symbols := #[.generic 1, .colored .blue] })
    (subtypes := #["Robot"])
    (oracleText := "Defender\n{T}: Add {U}. This mana can't be spent to cast a nonartifact spell.")
    (power := some 2)
    (toughness := some 3)
    (keywords := Keyword.defender)
    (activatedAbilities := #[activated (Effect.ofAbility .addBlueCantNonartifact) (ManaCost.empty) (tap := true)])

def iAmIronMan : CardDef :=
  card "I Am Iron Man" #[.instant] ({ symbols := #[.generic 2, .colored .blue] })
    (oracleText := "Until end of turn, target artifact or creature becomes an artifact creature with base power and toughness 4/4 and gains flying.\nDraw a card.")
    (spellEffect := some (Effect.ofSpell (.becomeArtifactCreature44Flying)))

def ironLadDivergingDestiny : CardDef :=
  card "Iron Lad, Diverging Destiny" #[.artifact, .creature] ({ symbols := #[.generic 2, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Flying, vigilance\nYou may look at the top card of your library any time.\n{T}: Reveal the top card of your library. If it's an artifact card, draw a card.")
    (power := some 2)
    (toughness := some 2)
    (keywords := (Keyword.flying).merge Keyword.vigilance)
    (mayLookAtTopAnytime := true)
    (activatedAbilities := #[activated (Effect.ofAbility .revealTopDrawIfArtifact) (ManaCost.empty) (tap := true)])

def ironheartCleverChampion : CardDef :=
  card "Ironheart, Clever Champion" #[.artifact, .creature] ({ symbols := #[.generic 4, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Improvise (Your artifacts can help cast this spell. Each artifact you tap after you're done activating mana abilities pays for {1}.)\nFlying\nNoncreature spells you cast have improvise.")
    (power := some 3)
    (toughness := some 4)
    (keywords := Keyword.flying)
    (staticAbilities := #[.improvise, .noncreatureSpellsHaveImprovise])

def justiceVanceAstrovik : CardDef :=
  card "Justice, Vance Astrovik" #[.creature] ({ symbols := #[.generic 2, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Mutant", "Hero"])
    (oracleText := "Flying\nWhen Justice enters, return up to one target nonland, nontoken permanent to its owner's hand.\nWhenever another nonland permanent you control is returned to its owner's hand, put a +1/+1 counter on Justice.")
    (power := some 2)
    (toughness := some 2)
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onEnter .returnNonlandNontoken, .onWatch .justiceBounce])

def kangTheConqueror : CardDef :=
  card "Kang the Conqueror" #[.creature] ({ symbols := #[.generic 2, .colored .blue, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Villain"])
    (oracleText := "Flying\nPower-up — {5}{U}{U}{U}: Put a +1/+1 counter on Kang. Take an extra turn after this one. During that turn, power-up abilities can't be activated(Effect.ofAbility .) (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)")
    (power := some 4)
    (toughness := some 5)
    (keywords := Keyword.flying)
    (activatedAbilities := #[activated (Effect.ofAbility (.plusOneAndExtraTurn)) ({ symbols := #[.generic 5, .colored .blue, .colored .blue, .colored .blue] }) (powerUp := true)])

def kidLoki : CardDef :=
  card "Kid Loki" #[.creature] ({ symbols := #[.colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["God", "Hero", "Villain"])
    (oracleText := "Each creature you control that you've put one or more +1/+1 counters on this turn has hexproof.\nWhenever you draw your second card each turn, put a +1/+1 counter on Kid Loki.")
    (power := some 1)
    (toughness := some 1)
    (triggeredAbilities := #[.onDrawSecondPlusOne])
    (staticAbilities := #[StaticAbility.hexproofIfPlusOneThisTurn])

def leaderSuperGenius : CardDef :=
  card "Leader, Super-Genius" #[.creature] ({ symbols := #[.generic 2, .colored .blue, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Gamma", "Scientist", "Villain"])
    (oracleText := "If a creature you control would connive, instead you draw a card, then that creature connives.\nAt the beginning of combat on your turn, target creature you control connives. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on that creature.)")
    (power := some 1)
    (toughness := some 3)
    (triggeredAbilities := #[.onCombatTargetYouControlConnives])
    (staticAbilities := #[StaticAbility.extraDrawOnConnive])

def lokiGodOfMischief : CardDef :=
  card "Loki, God of Mischief" #[.creature] ({ symbols := #[.generic 1, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["God", "Sorcerer", "Villain"])
    (oracleText := "Whenever a player or permanent becomes the target of an ability you control, draw a card. This ability triggers only once each turn.")
    (power := some 2)
    (toughness := some 1)
    (triggeredAbilities := #[.onWatch .youTargetDrawOnce])

def misterFantasticReedRichards : CardDef :=
  card "Mister Fantastic, Reed Richards" #[.creature] ({ symbols := #[.generic 3, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Scientist", "Hero"])
    (oracleText := "Reach\nWhenever one or more tokens you control enter, you may draw a card.")
    (power := some 2)
    (toughness := some 4)
    (keywords := Keyword.reach)
    (triggeredAbilities := #[.onWatch .tokensEnterMayDraw])

def msMarvelKamalaKhan : CardDef :=
  card "Ms. Marvel, Kamala Khan" #[.creature] ({ symbols := #[.generic 2, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Mutant", "Inhuman", "Hero"])
    (oracleText := "Reach, vigilance\nYou have no maximum hand size.\nEmbiggen Fist — Whenever you cast a spell that targets a creature you control, draw a card. Until end of turn, Ms. Marvel gains \"Ms. Marvel's base power is equal to the number of cards in your hand.\"")
    (power := some 1)
    (toughness := some 4)
    (keywords := (Keyword.reach).merge Keyword.vigilance)
    (triggeredAbilities := #[.onCasting .drawPowerEqualHand])
    (staticAbilities := #[.noMaximumHandSize])

def multiversalIncursion : CardDef :=
  card "Multiversal Incursion" #[.sorcery] ({ symbols := #[.generic 5, .colored .blue, .colored .blue] })
    (oracleText := "For each nontoken creature you control, create a token that's a copy of that creature, except it isn't legendary.")
    (spellEffect := some (Effect.ofSpell .copyNontokenCreaturesYouControl))

def namorTheSubMariner : CardDef :=
  card "Namor the Sub-Mariner" #[.creature] ({ symbols := #[.generic 1, .colored .blue, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Mutant", "Merfolk", "Villain"])
    (oracleText := "Flying\nNamor's power is equal to the number of Merfolk you control.\nWhenever you cast a noncreature spell with one or more blue mana symbols in its mana cost, create that many 1/1 blue Merfolk creature tokens.")
    (toughness := some 4)
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onCasting .merfolkFromBlue])
    (staticAbilities := #[.powerEqualSubtypeYouControl "Merfolk"])

def pymParticles : CardDef :=
  card "Pym Particles" #[.sorcery] ({ symbols := #[.colored .blue] })
    (oracleText := "Target creature gains vigilance until end of turn and can't be blocked this turn.\nDraw a card.")
    (spellEffect := some (Effect.ofSpell (.grantVigilanceUnblockable)))

def rewriteHistory : CardDef :=
  card "Rewrite History" #[.enchantment] ({ symbols := #[.generic 2, .colored .blue] })
    (subtypes := #["Plan"])
    (oracleText := "Whenever one or more creatures you control become tapped, draw a card, then discard a card and put a plan counter on this enchantment.\nWhen the fourth plan counter is put on this enchantment, sacrifice it. When you do, return up to two target instant and/or sorcery cards from your graveyard to your hand.")
    (triggeredAbilities := #[.onCreaturesYouControlBecomeTappedLootAndPlan, .onFourthPlanReturnInstants])

def secretInvasion : CardDef :=
  card "Secret Invasion" #[.enchantment] ({ symbols := #[.generic 1, .colored .blue, .colored .blue] })
    (subtypes := #["Aura"])
    (oracleText := "Enchant creature you control\nWhen this Aura enters, exile up to one target creature other than enchanted creature until this Aura leaves the battlefield. Enchanted creature becomes a copy of that creature until this Aura leaves the battlefield.\nEnchanted creature has ward {2}.")
    (triggeredAbilities := #[.onEnterExileOtherCopyEnchanted])
    (staticAbilities := #[StaticAbility.enchantedCreatureHasWard 2])

def sHIELDDeploymentDrone : CardDef :=
  card "S.H.I.E.L.D. Deployment Drone" #[.artifact, .creature] ({ symbols := #[.generic 2, .colored .blue] })
    (subtypes := #["Robot"])
    (oracleText := "Flying\nWhen this creature enters, create a 1/1 white Soldier creature token.")
    (power := some 2)
    (toughness := some 2)
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onEnterCreateTokens .soldier11white 1])

def sHIELDFlyingCar : CardDef :=
  card "S.H.I.E.L.D. Flying Car" #[.artifact] ({ symbols := #[.generic 2, .colored .blue] })
    (subtypes := #["Vehicle"])
    (oracleText := "Flash\nFlying\nWhen this Vehicle enters, exile up to one target creature you control. Return that card to the battlefield under its owner's control at the beginning of the next end step.\nCrew 1")
    (power := some 3)
    (toughness := some 3)
    (keywords := (Keyword.flash).merge Keyword.flying)
    (crew := some 1)
    (triggeredAbilities := #[.onEnterExileCreatureReturnEndStep])

def shuriWakandanInventor : CardDef :=
  card "Shuri, Wakandan Inventor" #[.creature] ({ symbols := #[.generic 1, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Artificer", "Hero"])
    (oracleText := "Artifact spells you cast cost {1} less to cast.\n{1}, {T}: Target artifact you control becomes a copy of a second target artifact you control until end of turn, except it isn't legendary. Activate only as a sorcery.")
    (power := some 2)
    (toughness := some 1)
    (staticAbilities := #[.typeSpellsCostLess .artifact 1])
    (activatedAbilities := #[activated (Effect.ofAbility .copyArtifactYouControlNotLegendary) ({ symbols := #[.generic 1] }) (tap := true) (onlyAsSorcery := true)])

def statureSizeShifter : CardDef :=
  card "Stature, Size Shifter" #[.creature] ({ symbols := #[.colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Stature can't be blocked if her power is 1 or less.\nPower-up — {X}{U}{U}: Put X +1/+1 counters on Stature. (Activate each power-up ability only once. Reduce the cost by her mana cost if she entered this turn.)")
    (power := some 1)
    (toughness := some 1)
    (staticAbilities := #[StaticAbility.cantBeBlockedIfPowerAtMost 1])
    (activatedAbilities := #[activated (Effect.ofAbility (.plusOneX)) ({ symbols := #[.x, .colored .blue, .colored .blue] }) (powerUp := true)])

def superIntelligence : CardDef :=
  card "Super Intelligence" #[.enchantment] ({ symbols := #[.colored .blue] })
    (subtypes := #["Aura"])
    (oracleText := "Enchant creature\nAt the beginning of the upkeep of enchanted creature's controller, that player draws a card.")
    (triggeredAbilities := #[.onStep .enchantedControllerDraws])

def superSuit : CardDef :=
  card "Super Suit" #[.artifact] ({ symbols := #[.generic 1, .colored .blue] })
    (subtypes := #["Equipment"])
    (oracleText := "Flash\nWhen this Equipment enters, attach it to target creature you control. Untap that creature.\nEquipped creature gets +1/+2.\nEquip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)")
    (keywords := Keyword.flash)
    (triggeredAbilities := #[.onEnterAttachThen .untap])
    (staticAbilities := #[StaticAbility.equippedCreatureGets 1 2])
    (activatedAbilities := #[equipAbility ({ symbols := #[.generic 2] })])

def thirstForKnowledge : CardDef :=
  card "Thirst for Knowledge" #[.instant] ({ symbols := #[.generic 2, .colored .blue] })
    (oracleText := "Draw three cards. Then discard two cards unless you discard an artifact card.")
    (spellEffect := some (Effect.ofSpell (.drawThreeDiscardUnlessArtifact)))

def tonyStark : CardDef :=
  card "Tony Stark" #[.creature] ({ symbols := #[.generic 1, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Artificer", "Hero"])
    (oracleText := "{1}, {T}: Look at the top four cards of your library. You may reveal an artifact card from among them and put it into your hand. Put the rest on the bottom of your library in a random order.\n{4}{U}{R}: Transform Tony Stark. Activate only as a sorcery.")
    (power := some 1)
    (toughness := some 3)
    (activatedAbilities := #[activated (Effect.ofAbility (.lookAtTopRevealArtifact 4)) ({ symbols := #[.generic 1] }) (tap := true), activated (Effect.ofAbility (.transform)) ({ symbols := #[.generic 4, .colored .blue, .colored .red] }) (onlyAsSorcery := true)])
    (otherFace := some theInvincibleIronMan)

def tricksterSStratagem : CardDef :=
  card "Trickster's Stratagem" #[.sorcery] ({ symbols := #[.generic 3, .colored .blue] })
    (oracleText := "The owner of target creature an opponent controls puts it into their library second from the top or on the bottom. Then up to one target creature you control connives. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on that creature.)")
    (spellEffect := some (Effect.ofSpell .ownerPutsLibraryThenConnive))

def weSayTheeNay : CardDef :=
  card "We Say Thee Nay!" #[.instant] ({ symbols := #[.generic 1, .colored .blue] })
    (subtypes := #["Arcane"])
    (oracleText := "Teamwork 2 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 2 or more.)\nCounter target spell unless its controller pays {2}. Counter that spell unless its controller pays {4} instead if this spell was cast using teamwork.")
    (teamwork := some 2)
    (spellEffect := some (Effect.ofSpell (.counterUnlessPaysTeamwork 2 4)))

def wiccanRisingMagician : CardDef :=
  card "Wiccan, Rising Magician" #[.creature] ({ symbols := #[.generic 4, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Mutant", "Warlock", "Hero"])
    (oracleText := "Flying\nWhenever you cast a noncreature spell, exile another target nonland, nontoken permanent. Return that card to the battlefield under its owner's control at the beginning of the next end step.")
    (power := some 4)
    (toughness := some 4)
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onCasting .exileFlicker])

def theWondrousWasp : CardDef :=
  card "The Wondrous Wasp" #[.creature] ({ symbols := #[.generic 1, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Flash\nFlying\nWasp's Sting — When The Wondrous Wasp enters, tap up to one target creature. It loses all abilities for as long as The Wondrous Wasp remains on the battlefield.")
    (power := some 2)
    (toughness := some 1)
    (keywords := (Keyword.flash).merge Keyword.flying)
    (triggeredAbilities := #[.onEnter .tapLoseAbilitiesWhileSource])

def agentsOfHYDRA : CardDef :=
  card "Agents of HYDRA" #[.creature] ({ symbols := #[.generic 1, .colored .black] })
    (subtypes := #["Human", "Spy", "Villain"])
    (oracleText := "When this creature dies, create a 2/1 black Villain creature token with menace. (It can't be blocked except by two or more creatures.)")
    (power := some 1)
    (toughness := some 1)
    (triggeredAbilities := #[.onDiesCreateTokens .villain21menace 1])

def arnimZolaBioFanatic : CardDef :=
  card "Arnim Zola, Bio-Fanatic" #[.artifact, .creature] ({ symbols := #[.generic 2, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Scientist", "Villain"])
    (oracleText := "{3}, {T}: Create a tapped 2/1 black Villain creature token with menace. Activate only if there are two or more creature cards in your graveyard. (It can't be blocked except by two or more creatures.)")
    (power := some 2)
    (toughness := some 3)
    (activatedAbilities := #[activated (Effect.ofAbility (.createTappedTokens .villain21menace 1)) ({ symbols := #[.generic 3] }) (tap := true)
      (onlyIfGyCreaturesAtLeast := 2)])

def baronHelmutZemo : CardDef :=
  card "Baron Helmut Zemo" #[.creature] ({ symbols := #[.colored .black, .colored .black, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Noble", "Villain"])
    (oracleText := "Whenever you cast a black spell from your hand, Baron Helmut Zemo connives.\nBoast — Exile any number of black cards from your graveyard with fifteen or more black mana symbols among their mana costs: Copy those exiled cards. You may cast up to three of the copies without paying their mana costs. (Activate only if this creature attacked this turn and only once each turn.)")
    (power := some 3)
    (toughness := some 3)
    (triggeredAbilities := #[.onYouCastColorFromHandConnive .black])
    (staticAbilities := #[StaticAbility.boast])

def baronStruckerHYDRAOverlord : CardDef :=
  card "Baron Strucker, HYDRA Overlord" #[.creature] ({ symbols := #[.generic 2, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Villain"])
    (oracleText := "Villain spells you cast cost {1} less to cast.\nWhenever another Villain you control enters, you may have it connive. Do this only once each turn. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on that creature.)")
    (power := some 2)
    (toughness := some 2)
    (triggeredAbilities := #[.onWatch .villainConniveOnce])
    (staticAbilities := #[StaticAbility.subtypeSpellsCostLess "Villain" 1])

def blackWidowSuperSpy : CardDef :=
  card "Black Widow, Super Spy" #[.creature] ({ symbols := #[.generic 1, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Spy", "Hero"])
    (oracleText := "Menace\nWhenever Black Widow deals combat damage to a player, that player exiles cards from the top of their library until they exile a nonland card. You may put a +1/+1 counter on Black Widow. If you don't, you may cast the exiled nonland card until end of turn and mana of any type can be spent to cast that spell.")
    (power := some 2)
    (toughness := some 1)
    (keywords := Keyword.menace)
    (triggeredAbilities := #[.onWatch .combatDamageExileUntilNonland])

def constructACosmicCube : CardDef :=
  card "Construct a Cosmic Cube" #[.enchantment] ({ symbols := #[.generic 2, .colored .black] })
    (subtypes := #["Plan"])
    (oracleText := "Whenever you draw your second card each turn, create a 2/1 black Villain creature token with menace and put a plan counter on this enchantment.\nWhen the seventh plan counter is put on this enchantment, sacrifice it. When you do, you control target opponent during their next turn. (You see all cards that player could see and make all decisions for them.)")
    (triggeredAbilities := #[.onYouDrawSecondCreateVillainAndPlan, .onSeventhPlanControlOpponent])

def crossbonesMaliciousMercenary : CardDef :=
  card "Crossbones, Malicious Mercenary" #[.creature] ({ symbols := #[.generic 3, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Mercenary", "Villain"])
    (oracleText := "Deathtouch\nWhenever another Villain you control enters, put a +1/+1 counter on Crossbones. He deals 2 damage to each opponent. This ability triggers only once each turn.")
    (power := some 3)
    (toughness := some 3)
    (keywords := Keyword.deathtouch)
    (triggeredAbilities := #[.onWatch .villainPlusOneDamageOnce])

def cruelAlliance : CardDef :=
  card "Cruel Alliance" #[.sorcery] ({ symbols := #[.generic 2, .colored .black] })
    (oracleText := "Teamwork 2 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 2 or more.)\nExile target creature with mana value 3 or less. If this spell was cast using teamwork, instead exile target creature and you gain 3 life.")
    (teamwork := some 2)
    (spellEffect := some (Effect.ofSpell (.exileCreatureMvAtMostOrAnyIfTeamwork 3 3)))

def darkDeed : CardDef :=
  card "Dark Deed" #[.instant] ({ symbols := #[.generic 1, .colored .black] })
    (oracleText := "Target creature gets -4/-4 until end of turn.")
    (spellEffect := some (Effect.ofSpell (.pump (-4) (-4))))

def decoyPloy : CardDef :=
  card "Decoy Ploy" #[.instant] ({ symbols := #[.generic 1, .colored .black] })
    (oracleText := "Choose one or both —\n• Return target Villain card from your graveyard to your hand.\n• Return target Hero card from your graveyard to your hand.")
    (spellModes := #[(Effect.ofSpell (.returnGySubtypeToHand "Villain")), (Effect.ofSpell (.returnGySubtypeToHand "Hero"))])
    (chooseOneOrBoth := true)

def doctorDoom : CardDef :=
  card "Doctor Doom" #[.creature] ({ symbols := #[.generic 4, .colored .black, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Scientist", "Villain"])
    (oracleText := "When Doctor Doom enters, create two 3/3 colorless Robot Villain artifact creature tokens named Doombot.\nAs long as you control an artifact creature or a Plan, Doctor Doom has indestructible.\nAt the beginning of your end step, you draw a card and lose 1 life.")
    (power := some 3)
    (toughness := some 3)
    (triggeredAbilities := #[.onEnterCreateTokens .doombot 2, .onYourEndStepDrawLoseLife])
    (staticAbilities := #[StaticAbility.indestructibleIfArtifactCreatureOrPlan])

def doomReignsSupreme : CardDef :=
  card "Doom Reigns Supreme" #[.enchantment] ({ symbols := #[.generic 1, .colored .black] })
    (subtypes := #["Plan"])
    (oracleText := "Whenever a Villain you control enters, each opponent loses 1 life and you gain 1 life. Put a plan counter on this enchantment.\nWhen the fifth plan counter is put on this enchantment, sacrifice it. When you do, target opponent exiles the top five cards of their library. You may cast up to two spells from among the exiled cards without paying their mana costs.")
    (triggeredAbilities := #[.onVillainYouControlEntersDrainAndPlan 1, .onFifthPlanExileTopCast])

def elektraDaughterOfTheHand : CardDef :=
  card "Elektra, Daughter of the Hand" #[.creature] ({ symbols := #[.generic 2, .colored .black, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Ninja", "Villain"])
    (oracleText := "Sneak {1}{B}{B} (You may cast this spell for {1}{B}{B} if you also return an unblocked attacker you control to hand during the declare blockers step. She enters tapped and attacking.)\nWhen Elektra enters, destroy target creature an opponent controls with power 3 or less.")
    (power := some 3)
    (toughness := some 3)
    (triggeredAbilities := #[.onEnter (.destroy (.oppCreaturePowerAtMost 3))])
    (staticAbilities := #[StaticAbility.sneak (ManaCost.ofGenericAndColors 1 [.black, .black])])

def grimReaperLethalLegionnaire : CardDef :=
  card "Grim Reaper, Lethal Legionnaire" #[.creature] ({ symbols := #[.generic 3, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Villain"])
    (oracleText := "Whenever Grim Reaper attacks, you may pay {3}{B}. When you do, return target creature card from your graveyard to the battlefield tapped and attacking with a finality counter on it. (If a creature with a finality counter on it would die, exile it instead.)")
    (power := some 3)
    (toughness := some 4)
    (triggeredAbilities := #[.onThisAttack .payReturnAttacking])

def hourOfDefeat : CardDef :=
  card "Hour of Defeat" #[.instant] ({ symbols := #[.generic 3, .colored .black] })
    (oracleText := "Destroy target creature. Surveil 1. (Look at the top card of your library. You may put it into your graveyard.)")
    (spellEffect := some (Effect.ofSpell (.destroyCreatureSurveil)))

def hYDRAInfiltration : CardDef :=
  card "HYDRA Infiltration" #[.enchantment] ({ symbols := #[.generic 3, .colored .black] })
    (oracleText := "When this enchantment enters, target opponent discards two cards.\nWhenever a creature you control attacks alone, target opponent loses 1 life and you gain 1 life.")
    (triggeredAbilities := #[.onEnterTargetOpponentDiscards 2, .onWatch .attacksAloneDrain])

def hYDRATroopers : CardDef :=
  card "HYDRA Troopers" #[.creature] ({ symbols := #[.generic 2, .colored .black] })
    (subtypes := #["Human", "Soldier", "Villain"])
    (oracleText := "When this creature enters, create a tapped 2/1 black Villain creature token with menace if there are two or more creature cards in your graveyard. Otherwise, mill two cards. (Put the top two cards of your library into your graveyard.)")
    (power := some 3)
    (toughness := some 2)
    (triggeredAbilities := #[.onEnterVillainIfGyElseMill])

def kingpinSEnforcers : CardDef :=
  card "Kingpin's Enforcers" #[.creature] ({ symbols := #[.generic 2, .colored .black] })
    (subtypes := #["Human", "Villain"])
    (oracleText := "Lifelink\n{2}{B}, Sacrifice an artifact or creature: Draw a card.")
    (power := some 2)
    (toughness := some 3)
    (keywords := Keyword.lifelink)
    (activatedAbilities := #[activated (Effect.ofAbility (.draw 1)) ({ symbols := #[.generic 2, .colored .black] })
      (sacrificeArtifactOrCreature := true)])

def klawSonicSubjugator : CardDef :=
  card "Klaw, Sonic Subjugator" #[.creature] ({ symbols := #[.generic 2, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Rogue", "Villain"])
    (oracleText := "Sonic Attack — When Klaw enters, target player reveals a number of cards from their hand equal to one plus the number of creature cards in your graveyard. You choose one of them. That player discards that card.")
    (power := some 2)
    (toughness := some 2)
    (triggeredAbilities := #[.onEnter .revealDiscardFromHand])

def madameMasque : CardDef :=
  card "Madame Masque" #[.creature] ({ symbols := #[.generic 4, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Villain"])
    (oracleText := "When Madame Masque enters, she connives. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on this creature.)\nWhenever you draw your second card each turn, create a 2/1 black Villain creature token with menace. (It can't be blocked except by two or more creatures.)")
    (power := some 3)
    (toughness := some 2)
    (triggeredAbilities := #[.onEnterConnive, .onYouDrawSecondCreateTokens .villain21menace])

def theMastersOfEvil : CardDef :=
  card "The Masters of Evil" #[.creature] ({ symbols := #[.generic 5, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Villain"])
    (oracleText := "Other Villains you control get +2/+1.\n{1}{B}, Discard this card: Search your library for a Plan card, reveal it, put it into your hand, then shuffle.")
    (power := some 5)
    (toughness := some 6)
    (staticAbilities := #[StaticAbility.otherCreaturesGet #["Villain"] 2 1])
    (activatedAbilities := #[activated (Effect.ofAbility (.searchLandTypeToHand "Plan")) ({ symbols := #[.generic 1, .colored .black] })
      (discardSource := true) (activateFromHand := true)])

def mODOK : CardDef :=
  card "M.O.D.O.K." #[.artifact, .creature] ({ symbols := #[.generic 3, .colored .black, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Villain"])
    (oracleText := "Flying, lifelink\nMental Organism — Pay 3 life: M.O.D.O.K. connives. Activate only during your turn. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on this creature.)\nDesigned Only for Killing — Creatures your opponents control get -1/-1.")
    (power := some 2)
    (toughness := some 2)
    (keywords := (Keyword.flying).merge Keyword.lifelink)
    (staticAbilities := #[StaticAbility.opponentsCreaturesGet (-1) (-1)])
    (activatedAbilities := #[activated (Effect.ofAbility .connive) (payLife := 3) (onlyDuringYourTurn := true)])

def moonstoneHarshMistress : CardDef :=
  card "Moonstone, Harsh Mistress" #[.creature] ({ symbols := #[.generic 3, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Doctor", "Villain"])
    (oracleText := "Flying\nWhenever you discard a card, you may exile that card from your graveyard. If you do, until the end of your next turn, you may play that card.")
    (power := some 2)
    (toughness := some 4)
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onResource .discardExilePlay])

def ninjaOfTheHand : CardDef :=
  card "Ninja of the Hand" #[.creature] ({ symbols := #[.generic 2, .colored .black] })
    (subtypes := #["Human", "Ninja", "Villain"])
    (oracleText := "Deathtouch\nPower-up — {4}{B}: Each opponent discards a card. Put a +1/+1 counter on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)")
    (power := some 2)
    (toughness := some 2)
    (keywords := Keyword.deathtouch)
    (activatedAbilities := #[activated (Effect.ofAbility (.eachOppDiscardThenPlusOne)) ({ symbols := #[.generic 4, .colored .black] }) (powerUp := true)])

def projectDeathlokSoldier : CardDef :=
  card "Project Deathlok Soldier" #[.artifact, .creature] ({ symbols := #[.colored .black] })
    (subtypes := #["Zombie", "Soldier"])
    (oracleText := "{2}{B}: Return this card from your graveyard to your hand.")
    (power := some 1)
    (toughness := some 2)
    (activatedAbilities := #[activated (Effect.ofAbility (.returnFromGraveyardToHand)) ({ symbols := #[.generic 2, .colored .black] })])

def redRoomRecruit : CardDef :=
  card "Red Room Recruit" #[.creature] ({ symbols := #[.generic 1, .colored .black] })
    (subtypes := #["Human", "Spy", "Villain"])
    (oracleText := "When this creature enters, it connives. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on this creature.)")
    (power := some 1)
    (toughness := some 2)
    (triggeredAbilities := #[.onEnterConnive])

def robotDomination : CardDef :=
  card "Robot Domination" #[.enchantment] ({ symbols := #[.generic 3, .colored .black] })
    (subtypes := #["Plan"])
    (oracleText := "Whenever one or more creature cards are put into your graveyard from anywhere, you draw a card, lose 1 life, and put a plan counter on this enchantment.\nWhen the third plan counter is put on this enchantment, sacrifice it and create three 2/2 colorless Robot Villain artifact creature tokens.")
    (triggeredAbilities := #[.onCreatureCardsToGyDrawLoseLifeAndPlan, .onThirdPlanCreateRobots])

def roninShadowStalker : CardDef :=
  card "Ronin, Shadow Stalker" #[.creature] ({ symbols := #[.generic 2, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Rogue", "Hero"])
    (oracleText := "Pay 2 life: Add two mana of any one color. Spend this mana only to cast Equipment spells or activate equip abilities. Activate only once each turn.\n{T}, Sacrifice an Equipment attached to Ronin: Target creature gets -4/-4 until end of turn. Activate only as a sorcery.")
    (power := some 3)
    (toughness := some 3)
    (activatedAbilities := #[activated (Effect.ofAbility .addTwoAnyColorEquipment) (payLife := 2) (onceEachTurn := true),
      activated (Effect.ofAbility (.targetGets (-4) (-4))) (tap := true) (sacrificeEquipmentAttachedToSource := true)
        (onlyAsSorcery := true)])

def roxxonBrutes : CardDef :=
  card "Roxxon Brutes" #[.creature] ({ symbols := #[.generic 4, .colored .black] })
    (subtypes := #["Human", "Berserker", "Villain"])
    (oracleText := "Menace (This creature can't be blocked except by two or more creatures.)\nWhenever you draw your second card each turn, put a +1/+1 counter on target creature.\nBasic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)")
    (power := some 4)
    (toughness := some 4)
    (keywords := Keyword.menace)
    (triggeredAbilities := #[.onResource .secondDrawPlusOneTarget])
    (activatedAbilities := #[typecyclingAbility "Basic land" (ManaCost.ofGeneric 2)])

def stolenStarkTech : CardDef :=
  card "Stolen Stark Tech" #[.artifact] ({ symbols := #[.generic 1, .colored .black] })
    (subtypes := #["Equipment"])
    (oracleText := "Flash\nWhen this Equipment enters, attach it to target creature you control. That creature gains indestructible until end of turn. (Damage and effects that say \"destroy\" don't destroy it.)\nEquipped creature gets +1/+0.\nEquip {1} ({1}: Attach to target creature you control. Equip only as a sorcery.)")
    (keywords := Keyword.flash)
    (triggeredAbilities := #[.onEnterAttachThen (.grantKeywords Keyword.indestructible)])
    (staticAbilities := #[StaticAbility.equippedCreatureGets 1 0])
    (activatedAbilities := #[equipAbility ({ symbols := #[.generic 1] })])

def superSkrull : CardDef :=
  card "Super-Skrull" #[.creature] ({ symbols := #[.generic 1, .colored .black, .colored .black, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Skrull", "Shapeshifter", "Villain"])
    (oracleText := "Flying\n{2}{W}: Create a 0/4 colorless Wall creature token with defender.\n{3}{G}: Super-Skrull gets +4/+4 until end of turn.\n{4}{R}: Super-Skrull deals 4 damage to target creature.\n{5}{U}: Target player draws four cards.")
    (power := some 4)
    (toughness := some 5)
    (keywords := Keyword.flying)
    (activatedAbilities := #[activated (Effect.ofAbility (.createTokens .wall04defender 1)) ({ symbols := #[.generic 2, .colored .white] }), activated (Effect.ofAbility (.sourceGets 4 4)) ({ symbols := #[.generic 3, .colored .green] }), activated (Effect.ofAbility (.dealDamageToTargetCreature 4)) ({ symbols := #[.generic 4, .colored .red] }), activated (Effect.ofAbility (.targetPlayerDraw 4)) ({ symbols := #[.generic 5, .colored .blue] })])

def swordsmanSharpScoundrel : CardDef :=
  card "Swordsman, Sharp Scoundrel" #[.creature] ({ symbols := #[.generic 1, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero", "Villain"])
    (oracleText := "Whenever another Villain you control enters, attach up to one target Equipment you control to target creature you control.\nWhenever an equipped creature you control attacks, it connives. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on that creature.)")
    (power := some 2)
    (toughness := some 2)
    (triggeredAbilities := #[.onWatch .villainAttachEquipment, .onEquippedCreatureYouControlAttacksConnive])

def thunderboltsConspiracy : CardDef :=
  card "Thunderbolts Conspiracy" #[.enchantment] ({ symbols := #[.generic 3, .colored .black] })
    (oracleText := "Flash\nWhenever a Villain you control dies, return it to the battlefield under its owner's control with a finality counter on it. That creature is a Hero in addition to its other types. (If a creature with a finality counter on it would die, exile it instead.)")
    (keywords := Keyword.flash)
    (triggeredAbilities := #[.onDeath .villainReturnAsHero])

def tooEvilToStayDead : CardDef :=
  card "Too Evil to Stay Dead" #[.sorcery] ({ symbols := #[.generic 2, .colored .black] })
    (oracleText := "Teamwork 4 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 4 or more.)\nChoose target creature card in your graveyard with mana value 4 or less. If this spell was cast using teamwork, instead choose target creature card in your graveyard. Return the chosen card to the battlefield.")
    (teamwork := some 4)
    (spellEffect := some (Effect.ofSpell (.returnGyCreatureMvAtMostOrAny 4)))

def unlivingLegionnaire : CardDef :=
  card "Unliving Legionnaire" #[.creature] ({ symbols := #[.generic 3, .colored .black] })
    (subtypes := #["Vampire", "Villain"])
    (oracleText := "Flying\nPower-up — {5}{B}{B}: Return up to one target creature card from your graveyard to your hand. Put two +1/+1 counters on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)")
    (power := some 3)
    (toughness := some 2)
    (keywords := Keyword.flying)
    (activatedAbilities := #[activated (Effect.ofAbility (.returnGyCreatureThenPlusOne 2)) ({ symbols := #[.generic 5, .colored .black, .colored .black] }) (powerUp := true)])

def visionsOfVillainy : CardDef :=
  card "Visions of Villainy" #[.instant] ({ symbols := #[.generic 2, .colored .black] })
    (oracleText := "This spell costs {1} less to cast if you control a Villain.\nYou draw two cards and lose 2 life.")
    (costReductionIfYouControl := some (1, "Villain"))
    (spellEffect := some (Effect.ofSpell (.drawAndLoseLife 2 2)))

def whiplashVengefulEngineer : CardDef :=
  card "Whiplash, Vengeful Engineer" #[.creature] ({ symbols := #[.colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Artificer", "Villain"])
    (oracleText := "Whiplash enters tapped.\nWhenever Whiplash attacks, if he's equipped, each opponent loses X life and you gain X life, where X is the number of Equipment attached to him.")
    (power := some 2)
    (toughness := some 2)
    (entersTapped := true)
    (triggeredAbilities := #[.onThisAttack .equippedDrain])

def widowSBite : CardDef :=
  card "Widow's Bite" #[.instant] ({ symbols := #[.generic 1, .colored .black] })
    (oracleText := "Teamwork 3 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 3 or more.)\nChoose one. If this spell was cast using teamwork, choose both instead.\n• Target creature gains deathtouch until end of turn.\n• Target creature gets -2/-2 until end of turn.")
    (teamwork := some 3)
    (spellModes := #[(Effect.ofSpell .grantDeathtouch), (Effect.ofSpell (.pump (-2) (-2)))])
    (chooseBothIfTeamwork := true)

def yellowjacketHeartlessMarauder : CardDef :=
  card "Yellowjacket, Heartless Marauder" #[.creature] ({ symbols := #[.generic 1, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Rogue", "Villain"])
    (oracleText := "Flying\nWhenever another Villain you control enters, Yellowjacket gets +1/+0 and gains lifelink until end of turn.")
    (power := some 1)
    (toughness := some 2)
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onWatch .villainPlusOneLifelink])

def avengersDisassembled : CardDef :=
  card "Avengers Disassembled" #[.sorcery] ({ symbols := #[.generic 1, .colored .red, .colored .red] })
    (oracleText := "Choose one or both —\n• Avengers Disassembled deals 3 damage to each creature.\n• Destroy target land. Its controller may search their library for a basic land card, put it onto the battlefield tapped, then shuffle.")
    (spellModes := #[(Effect.ofSpell (.dealDamageToEachCreature 3)), (Effect.ofSpell .destroyLandSearchBasic)])
    (chooseOneOrBoth := true)

def blazingCrescendo : CardDef :=
  card "Blazing Crescendo" #[.instant] ({ symbols := #[.generic 1, .colored .red] })
    (oracleText := "Target creature gets +3/+1 until end of turn.\nExile the top card of your library. Until the end of your next turn, you may play that card.")
    (spellEffect := some (Effect.ofSpell (.pumpThenExileTopPlay 3 1)))

def crimsonOperative : CardDef :=
  card "Crimson Operative" #[.artifact, .creature] ({ symbols := #[.generic 3, .colored .red] })
    (subtypes := #["Human", "Villain"])
    (oracleText := "Prowess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn.)\nWhen this creature enters, exile the top card of your library. Until the end of your next turn, you may play that card.")
    (power := some 3)
    (toughness := some 2)
    (keywords := Keyword.prowess)
    (triggeredAbilities := #[.onEnterExileTop])

def deathToOurEnemies : CardDef :=
  card "Death to Our Enemies" #[.enchantment] ({ symbols := #[.generic 2, .colored .red] })
    (subtypes := #["Plan"])
    (oracleText := "Whenever you cast a noncreature spell, create a tapped Treasure token and put a plan counter on this enchantment.\nWhen the fourth plan counter is put on this enchantment, sacrifice it. When you do, it deals 7 damage divided as you choose among one or two targets.")
    (triggeredAbilities := #[.onCastNoncreatureTreasureAndPlan, .onFourthPlanDividedDamage])

def evilSThrall : CardDef :=
  card "Evil's Thrall" #[.sorcery] ({ symbols := #[.generic 2, .colored .red] })
    (oracleText := "Gain control of target creature until end of turn. If you control a Villain with greater mana value than that creature, gain control of that creature until the end of your next turn instead. Untap that creature. It gains haste until end of turn.")
    (spellEffect := some (Effect.ofSpell .gainControlUntilEotOrNextIfVillain))

def finFangFoom : CardDef :=
  card "Fin Fang Foom" #[.creature] ({ symbols := #[.generic 2, .colored .red, .colored .red] })
    (supertypes := #[.legendary])
    (subtypes := #["Alien", "Dragon", "Villain"])
    (oracleText := "Flying\nWhenever you cast an instant or sorcery spell that targets an artifact or land, copy that spell. You may choose new targets for the copy. Put two +1/+1 counters on Fin Fang Foom.")
    (power := some 3)
    (toughness := some 5)
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onCasting .copyIfArtifactOrLand])

def hawkeyeMasterMarksman : CardDef :=
  card "Hawkeye, Master Marksman" #[.creature] ({ symbols := #[.generic 1, .colored .red] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Archer", "Hero"])
    (oracleText := "Reach, first strike\nTrick Arrows — Whenever Hawkeye becomes tapped, you may pay {1} up to three times. When you do, choose up to that many —\n• Net — Target creature can't block this turn.\n• Explosive — Hawkeye deals 2 damage to target player.\n• Boomerang — Discard a card, then draw a card.")
    (power := some 2)
    (toughness := some 2)
    (keywords := (Keyword.reach).merge Keyword.firstStrike)
    (triggeredAbilities := #[.onWatch .hawkeyeModes])

def hawkeyeYoungAvenger : CardDef :=
  card "Hawkeye, Young Avenger" #[.creature] ({ symbols := #[.generic 3, .colored .red] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Archer", "Hero"])
    (oracleText := "Reach\nIf a source you control would deal noncombat damage to an opponent or a permanent an opponent controls, instead it deals that much damage plus X, where X is Hawkeye's power.")
    (power := some 2)
    (toughness := some 4)
    (keywords := Keyword.reach)
    (staticAbilities := #[StaticAbility.noncombatDamagePlusSourcePower])

def hawkeyeSBow : CardDef :=
  card "Hawkeye's Bow" #[.artifact] ({ symbols := #[.colored .red] })
    (subtypes := #["Equipment"])
    (oracleText := "Equipped creature gets +1/+0 and has reach.\nWhenever equipped creature becomes tapped, it deals 1 damage to each opponent.\nEquip {1} ({1}: Attach to target creature you control. Equip only as a sorcery.)")
    (triggeredAbilities := #[.onWatch .equippedTappedDamage])
    (staticAbilities := #[StaticAbility.equippedCreatureGetsAndHas 1 0 Keyword.reach])
    (activatedAbilities := #[equipAbility ({ symbols := #[.generic 1] })])

def hexMagic : CardDef :=
  card "Hex Magic" #[.sorcery] ({ symbols := #[.generic 2, .colored .red] })
    (subtypes := #["Arcane"])
    (oracleText := "Exile all the cards from your hand, then draw that many cards. Until the end of your next turn, you may play cards exiled this way.")
    (spellEffect := some (Effect.ofSpell .exileHandDrawPlayUntilNext))

def hireACrew : CardDef :=
  card "Hire a Crew" #[.instant] ({ symbols := #[.generic 2, .colored .red] })
    (oracleText := "Create a 2/1 black Villain creature token with menace, then creatures you control get +1/+0 until end of turn. (A creature with menace can't be blocked except by two or more creatures.)")
    (spellEffect := some (Effect.ofSpell (.createTokensThenTeamPump .villain21menace 1 1 0)))

def hULKSMASH : CardDef :=
  card "HULK SMASH!" #[.instant] ({ symbols := #[.generic 1, .colored .red] })
    (oracleText := "Teamwork 4 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 4 or more.)\nChoose one. If this spell was cast using teamwork, choose both instead.\n• Destroy target noncreature artifact.\n• Target creature you control deals damage equal to its power to target creature an opponent controls.")
    (teamwork := some 4)
    (spellModes := #[(Effect.ofSpell .destroyNoncreatureArtifact), (Effect.ofSpell .creatureYouControlDealsPowerToOppCreature)])
    (chooseBothIfTeamwork := true)

def humanTorchJohnnyStorm : CardDef :=
  card "Human Torch, Johnny Storm" #[.creature] ({ symbols := #[.generic 2, .colored .red] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Flying\nWhenever you draw a card, if you control another Hero, Human Torch deals 1 damage to target opponent.\nPower-up — {6}{R}: Put three +1/+1 counters on Human Torch. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)")
    (power := some 2)
    (toughness := some 2)
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onResource .drawIfAnotherHeroDamage])
    (activatedAbilities := #[powerUpAbility (Effect.ofAbility (.putPlusOnePlusOneOnSource 3)) ({ symbols := #[.generic 6, .colored .red] })])

def hYDRAAssaultRobot : CardDef :=
  card "HYDRA Assault Robot" #[.artifact, .creature] ({ symbols := #[.generic 1, .colored .red] })
    (subtypes := #["Robot", "Villain"])
    (oracleText := "Whenever another Villain and/or artifact you control enters, this creature deals 1 damage to target opponent.")
    (power := some 1)
    (toughness := some 3)
    (triggeredAbilities := #[.onWatch .villainOrArtifactDamage])

def ironFistLivingWeapon : CardDef :=
  card "Iron Fist, Living Weapon" #[.creature] ({ symbols := #[.generic 2, .colored .red] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Warrior", "Hero"])
    (oracleText := "Whenever you cast a spell that targets a creature you control, Iron Fist gains \"{T}: Iron Fist deals damage equal to his power to any other target\" until end of turn.")
    (power := some 2)
    (toughness := some 3)
    (triggeredAbilities := #[.onCasting .ironFistTap])

def jessicaJonesPrivateEye : CardDef :=
  card "Jessica Jones, Private Eye" #[.creature] ({ symbols := #[.generic 2, .colored .red] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Detective", "Hero"])
    (oracleText := "{T}, Put a stun counter on Jessica Jones: Exile the top X cards of your library, where X is Jessica Jones's power. You may play those cards this turn. (If a permanent with a stun counter would become untapped, remove one from it instead.)")
    (power := some 2)
    (toughness := some 3)
    (activatedAbilities := #[activated (Effect.ofAbility .exileTopXPlayThisTurn) (tap := true) (putStunCounterOnSource := true)])

def kUnLunWarrior : CardDef :=
  card "K'un-Lun Warrior" #[.creature] ({ symbols := #[.generic 1, .colored .red] })
    (subtypes := #["Human", "Warrior", "Hero"])
    (oracleText := "When this creature enters, you may sacrifice an artifact or discard a card. If you do, draw a card.")
    (power := some 2)
    (toughness := some 2)
    (triggeredAbilities := #[.onEnterMaySacArtifactOrDiscardDraw])

def kreeSentinel : CardDef :=
  card "Kree Sentinel" #[.artifact, .creature] ({ symbols := #[.generic 4, .colored .red] })
    (subtypes := #["Kree", "Robot", "Villain"])
    (oracleText := "Reach\nBasic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)")
    (power := some 5)
    (toughness := some 5)
    (keywords := Keyword.reach)
    (activatedAbilities := #[typecyclingAbility "Basic land" (ManaCost.ofGeneric 2)])

def lightningStrike : CardDef :=
  card "Lightning Strike" #[.instant] ({ symbols := #[.generic 1, .colored .red] })
    (oracleText := "Lightning Strike deals 3 damage to any target.")
    (spellEffect := some (Effect.ofSpell (.dealDamage 3)))

def lokiLaufeyson : CardDef :=
  card "Loki Laufeyson" #[.creature] ({ symbols := #[.generic 1, .colored .red] })
    (supertypes := #[.legendary])
    (subtypes := #["God", "Sorcerer", "Villain"])
    (oracleText := "{1}, {T}: When you next cast an instant or sorcery spell with mana value less than or equal to Loki's power this turn, copy that spell. You may choose new targets for the copy.\nPower-up — {4}{R}: Put two +1/+1 counters on Loki. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)")
    (power := some 2)
    (toughness := some 1)
    (activatedAbilities := #[activated (Effect.ofAbility .nextInstantSorceryCopyIfMvAtMostSourcePower) ({ symbols := #[.generic 1] }) (tap := true), powerUpAbility (Effect.ofAbility (.putPlusOnePlusOneOnSource 2)) ({ symbols := #[.generic 4, .colored .red] })])

def machinesmithAutomaton : CardDef :=
  card "Machinesmith Automaton" #[.artifact, .creature] ({ symbols := #[.generic 2, .colored .red] })
    (subtypes := #["Robot", "Villain"])
    (oracleText := "Trample\nWhenever another artifact you control enters, put a +1/+1 counter on this creature.")
    (power := some 2)
    (toughness := some 2)
    (keywords := Keyword.trample)
    (triggeredAbilities := #[.onAnotherArtifactEntersPlusOne])

def mistyKnightHeroForHire : CardDef :=
  card "Misty Knight, Hero for Hire" #[.creature] ({ symbols := #[.generic 1, .colored .red] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Detective", "Hero"])
    (oracleText := "{2}, {T}, Discard a card: Draw a card for each card you've discarded this turn.")
    (power := some 3)
    (toughness := some 1)
    (activatedAbilities := #[activated (Effect.ofAbility .drawPerDiscardedThisTurn)
      ({ symbols := #[.generic 2] }) (tap := true) (discardACard := true)])

def mjLnirHammerOfThor : CardDef :=
  card "Mjölnir, Hammer of Thor" #[.artifact] ({ symbols := #[.generic 3, .colored .red] })
    (supertypes := #[.legendary])
    (subtypes := #["Equipment"])
    (oracleText := "When Mjölnir enters, it deals 4 damage to up to one target creature.\nDouble all damage equipped creature would deal.\nEquip worthy {1} (A creature is worthy if it's a legendary non-Villain that's red and/or white.)\n{2}{R}, Discard this card: It deals 2 damage to each creature.")
    (triggeredAbilities := #[.onEnter (.dealDamageUpToOne 4)])
    (staticAbilities := #[StaticAbility.equippedDealsDoubleDamage])
    (activatedAbilities := #[equipWorthyAbility (ManaCost.ofGeneric 1),
      activated (Effect.ofAbility (.dealDamageToEachCreature 2)) ({ symbols := #[.generic 2, .colored .red] })
        (discardSource := true) (activateFromHand := true)])

def photonBlastBarrage : CardDef :=
  card "Photon Blast Barrage" #[.sorcery] ({ symbols := #[.x, .colored .red, .colored .red] })
    (oracleText := "When you cast this spell, copy it X times. You may choose new targets for the copies.\nPhoton Blast Barrage deals 1 damage to target creature.")
    (spellEffect := some (Effect.ofSpell (.copyThisSpellXTimesThenDamage 1)))

def quicksilverBrashBlur : CardDef :=
  card "Quicksilver, Brash Blur" #[.creature] ({ symbols := #[.colored .red] })
    (supertypes := #[.legendary])
    (subtypes := #["Mutant", "Hero"])
    (oracleText := "If Quicksilver, Brash Blur is in your opening hand, you may begin the game with him on the battlefield.\nHaste\nPower-up — {4}{R}: Put a +1/+1 counter and a double strike counter on Quicksilver. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)")
    (power := some 1)
    (toughness := some 1)
    (keywords := Keyword.haste)
    (staticAbilities := #[StaticAbility.mayBeginOnBattlefield])
    (activatedAbilities := #[activated (Effect.ofAbility .plusOneAndDoubleStrikeCounter) ({ symbols := #[.generic 4, .colored .red] }) (powerUp := true)])

def redHulk : CardDef :=
  card "Red Hulk" #[.creature] ({ symbols := #[.generic 4, .colored .red, .colored .red] })
    (supertypes := #[.legendary])
    (subtypes := #["Gamma", "Berserker", "Villain"])
    (oracleText := "Reach, trample\nEnrage — Whenever Red Hulk is dealt damage, put a +1/+1 counter on him. When you do, he deals damage equal to the number of +1/+1 counters on him to any other target.")
    (power := some 6)
    (toughness := some 7)
    (keywords := (Keyword.reach).merge Keyword.trample)
    (triggeredAbilities := #[.onWatch .redHulk])

def repulsorBlast : CardDef :=
  card "Repulsor Blast" #[.sorcery] ({ symbols := #[.generic 3, .colored .red] })
    (oracleText := "Teamwork 2 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 2 or more.)\nRepulsor Blast deals 5 damage to target creature. If this spell was cast using teamwork, it also deals 2 damage to that creature's controller.")
    (teamwork := some 2)
    (spellEffect := some (Effect.ofSpell (.dealDamageThenControllerIfTeamwork 5 2)))

def theScarletWitch : CardDef :=
  card "The Scarlet Witch" #[.creature] ({ symbols := #[.generic 2, .colored .red] })
    (supertypes := #[.legendary])
    (subtypes := #["Mutant", "Warlock", "Hero"])
    (oracleText := "Instant and sorcery spells you cast with mana value 4 or greater cost {X} less to cast, where X is The Scarlet Witch's power.")
    (power := some 2)
    (toughness := some 3)
    (staticAbilities := #[StaticAbility.instantSorceryCostLessEqualPower])

def speedYoungAvenger : CardDef :=
  card "Speed, Young Avenger" #[.creature] ({ symbols := #[.generic 1, .colored .red] })
    (supertypes := #[.legendary])
    (subtypes := #["Mutant", "Hero"])
    (oracleText := "Haste\nWhenever you cast a noncreature spell, you may pay {1}. When you do, target creature with haste can't be blocked this turn except by creatures with haste.")
    (power := some 2)
    (toughness := some 2)
    (keywords := Keyword.haste)
    (triggeredAbilities := #[.onCasting .mayPayHasteUnblockable])

def starkIndustriesExecutive : CardDef :=
  card "Stark Industries Executive" #[.creature] ({ symbols := #[.colored .red] })
    (subtypes := #["Human", "Advisor"])
    (oracleText := "{2}, {T}: Create a Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")")
    (power := some 1)
    (toughness := some 2)
    (activatedAbilities := #[activated (Effect.ofAbility (.createTokens .treasure 1)) ({ symbols := #[.generic 2] }) (tap := true)])

def superSpeed : CardDef :=
  card "Super Speed" #[.enchantment] ({ symbols := #[.colored .red] })
    (subtypes := #["Aura"])
    (oracleText := "Flash\nEnchant creature\nWhen this Aura enters, enchanted creature gains first strike until end of turn.\nEnchanted creature gets +1/+0 and has haste.")
    (keywords := Keyword.flash)
    (triggeredAbilities := #[.onEnterEnchanted (.grantKeywords Keyword.firstStrike)])
    (staticAbilities := #[StaticAbility.enchantedCreatureGetsAndHas 1 0 Keyword.haste])

def teamTactics : CardDef :=
  card "Team Tactics" #[.instant] ({ symbols := #[.generic 1, .colored .red] })
    (oracleText := "Teamwork 1 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 1 or more.)\nTarget creature gains double strike until end of turn. If this spell was cast using teamwork, that creature also gains trample until end of turn.")
    (teamwork := some 1)
    (spellEffect := some (Effect.ofSpell (.grantDoubleStrikeTeamworkTrample)))

def thorGodOfThunder : CardDef :=
  card "Thor, God of Thunder" #[.creature] ({ symbols := #[.generic 3, .colored .red, .colored .red] })
    (supertypes := #[.legendary])
    (subtypes := #["God", "Warrior", "Hero"])
    (oracleText := "Flying\nWhen Thor enters, exile target Equipment, instant, or sorcery card from your graveyard. Until the end of your next turn, you may play that card.\nWhenever you cast a noncreature spell, Thor deals damage equal to that spell's mana value to any target.")
    (power := some 5)
    (toughness := some 5)
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onEnter .exileGyPlayUntilNextTurn, .onCasting .damageEqualMv])

def truckToss : CardDef :=
  card "Truck Toss" #[.instant] ({ symbols := #[.generic 2, .colored .red, .colored .red] })
    (oracleText := "This spell costs {2} less to cast if you control a Vehicle.\nTruck Toss deals 4 damage to any target.")
    (costReductionIfYouControl := some (2, "Vehicle"))
    (spellEffect := some (Effect.ofSpell (.dealDamage 4)))

def visionOfLove : CardDef :=
  card "Vision of Love" #[.instant] ({ symbols := #[.generic 1, .colored .red] })
    (oracleText := "You may sacrifice an artifact or discard a card. If you do, draw two cards.")
    (spellEffect := some (Effect.ofSpell (.maySacArtifactOrDiscardDraw 2)))

def volcanicVillain : CardDef :=
  card "Volcanic Villain" #[.creature] ({ symbols := #[.generic 2, .colored .red] })
    (subtypes := #["Elemental", "Villain"])
    (oracleText := "Haste\nPower-up — {5}{R}: Put two +1/+1 counters on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)")
    (power := some 3)
    (toughness := some 2)
    (keywords := Keyword.haste)
    (activatedAbilities := #[powerUpAbility (Effect.ofAbility (.putPlusOnePlusOneOnSource 2)) ({ symbols := #[.generic 5, .colored .red] })])

def wonderManHollywoodHero : CardDef :=
  card "Wonder Man, Hollywood Hero" #[.creature] ({ symbols := #[.generic 3, .colored .red, .colored .red] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Performer", "Hero"])
    (oracleText := "Flying\nEach power-up ability of permanents you control can be activated an additional time.\nPower-up — {5}{R}{R}: Put two +1/+1 counters on Wonder Man. (Activate each power-up ability only . . . once? Reduce the cost by his mana cost if he entered this turn.)")
    (power := some 4)
    (toughness := some 4)
    (keywords := Keyword.flying)
    (staticAbilities := #[StaticAbility.extraPowerUpActivation])
    (activatedAbilities := #[powerUpAbility (Effect.ofAbility (.putPlusOnePlusOneOnSource 2)) ({ symbols := #[.generic 5, .colored .red, .colored .red] })])

def antManSArmy : CardDef :=
  card "Ant-Man's Army" #[.creature] ({ symbols := #[.generic 2, .colored .green] })
    (subtypes := #["Insect"])
    (oracleText := "When this creature enters, create a Food token or a Treasure token. (A Food token is an artifact with \"{2}, {T}, Sacrifice this token: You gain 3 life.\" A Treasure token is an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")")
    (power := some 3)
    (toughness := some 2)
    (triggeredAbilities := #[.onEnterCreateFoodOrTreasure])

def callDamageControl : CardDef :=
  card "Call Damage Control" #[.sorcery] ({ symbols := #[.generic 1, .colored .green] })
    (oracleText := "Choose up to two. Return those cards from your graveyard to your hand.\n• Target artifact card.\n• Target creature card.\n• Target enchantment card.\n• Target land card.")
    (spellEffect := some (Effect.ofSpell .returnUpToTwoGyModal))

def claimTheKingdom : CardDef :=
  card "Claim the Kingdom" #[.enchantment] ({ symbols := #[.generic 1, .colored .green] })
    (subtypes := #["Plan"])
    (oracleText := "Landfall — Whenever a land you control enters, put a +1/+1 counter on target creature you control and a plan counter on this enchantment.\nWhen the fourth plan counter is put on this enchantment, sacrifice it. When you do, put an indestructible counter on target creature you control.")
    (triggeredAbilities := #[.onLandYouControlEntersPlusOneAndPlan, .onFourthPlanIndestructible])

def docSamsonSuperPsychiatrist : CardDef :=
  card "Doc Samson, Super Psychiatrist" #[.creature] ({ symbols := #[.generic 4, .colored .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Gamma", "Doctor", "Hero"])
    (oracleText := "If you would put one or more counters on a permanent you control, put that many plus one of each of those kinds of counters on that permanent instead.\n{T}: Add X mana of any one color, where X is Doc Samson's power.")
    (power := some 3)
    (toughness := some 6)
    (staticAbilities := #[StaticAbility.extraCounterOnPermanents])
    (activatedAbilities := #[activated (Effect.ofAbility .addAnyColorEqualToSourcePower) (ManaCost.empty) (tap := true)])

def earthSMightiestHeroes : CardDef :=
  card "Earth's Mightiest Heroes" #[.sorcery] ({ symbols := #[.generic 4, .colored .green, .colored .green] })
    (oracleText := "Teamwork 5 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 5 or more.)\nReveal the top eight cards of your library. You may put a creature card from among them onto the battlefield. If this spell was cast using teamwork, put any number of creature cards from among them onto the battlefield instead. Put the rest into your graveyard.")
    (teamwork := some 5)
    (spellEffect := some (Effect.ofSpell (.revealTopPutCreatures 8)))

def epicFight : CardDef :=
  card "Epic Fight" #[.sorcery] ({ symbols := #[.generic 2, .colored .green] })
    (oracleText := "Choose one or both —\n• Double target creature's power and toughness until end of turn.\n• Target creature you control fights target creature an opponent controls.")
    (spellModes := #[(Effect.ofSpell .doublePowerAndToughness), (Effect.ofSpell .fight)])
    (chooseOneOrBoth := true)

def goNuts : CardDef :=
  card "Go Nuts!" #[.sorcery] ({ symbols := #[.colored .green] })
    (oracleText := "Teamwork 3 (As an additional cost to cast this spell, you may tap any number of creatures you control with total power 3 or more.)\nChoose one. If this spell was cast using teamwork, choose both instead.\n• Put a +1/+1 counter on target creature.\n• Target creature you control fights target creature an opponent controls.")
    (teamwork := some 3)
    (spellModes := #[(Effect.ofSpell .plusOneOnCreature), (Effect.ofSpell .fight)])
    (chooseBothIfTeamwork := true)

def guerrillaGorilla : CardDef :=
  card "Guerrilla Gorilla" #[.creature] ({ symbols := #[.generic 1, .colored .green] })
    (subtypes := #["Ape", "Soldier", "Hero"])
    (oracleText := "Reach\nSacrifice this creature: Destroy target noncreature artifact or noncreature enchantment. Activate only as a sorcery.")
    (power := some 2)
    (toughness := some 2)
    (keywords := Keyword.reach)
    (activatedAbilities := #[activated (Effect.ofAbility .destroyTargetNoncreatureArtOrEnch)
      (sacrificeSource := true) (onlyAsSorcery := true)])

def hellcatUndyingVigilante : CardDef :=
  card "Hellcat, Undying Vigilante" #[.creature] ({ symbols := #[.colored .green, .colored .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Haste\nWhen Hellcat dies, return her to the battlefield under her owner's control with a +1/+1 counter on her. She loses all abilities and gains haste.")
    (power := some 2)
    (toughness := some 2)
    (keywords := Keyword.haste)
    (triggeredAbilities := #[.onDeath .hellcatReturn])

def herculesPrinceOfPower : CardDef :=
  card "Hercules, Prince of Power" #[.creature] ({ symbols := #[.generic 2, .colored .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Demigod", "Warrior", "Hero"])
    (oracleText := "Power-up — {4}{G}: Put a +1/+1 counter on Hercules. He gains vigilance, indestructible, and haste until end of turn. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)")
    (power := some 3)
    (toughness := some 3)
    (activatedAbilities := #[activated (Effect.ofAbility (.plusOneAndGrant ((Keyword.vigilance.merge Keyword.indestructible).merge Keyword.haste))) ({ symbols := #[.generic 4, .colored .green] }) (powerUp := true)])

def heroicFeast : CardDef :=
  card "Heroic Feast" #[.enchantment] ({ symbols := #[.generic 2, .colored .green] })
    (oracleText := "When this enchantment enters, create a Food token. (It's an artifact with \"{2}, {T}, Sacrifice this token: You gain 3 life.\")\nWhenever you gain life, choose up to that many target creatures you control. Put a +1/+1 counter on each of them.")
    (triggeredAbilities := #[.onEnterCreateTokens .food 1, .onResource .gainLifePlusOnes])

def hulklingBurgeoningBruiser : CardDef :=
  card "Hulkling, Burgeoning Bruiser" #[.creature] ({ symbols := #[.generic 2, .colored .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Kree", "Skrull", "Hero"])
    (oracleText := "Vigilance\nWhenever another creature you control enters, if it has greater power or toughness than Hulkling, put a +1/+1 counter on Hulkling.")
    (power := some 2)
    (toughness := some 3)
    (keywords := Keyword.vigilance)
    (triggeredAbilities := #[.onWatch .hulklingCompare])

def kaZarOfTheSavageLand : CardDef :=
  card "Ka-Zar of the Savage Land" #[.creature] ({ symbols := #[.generic 4, .colored .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Barbarian", "Hero"])
    (oracleText := "You may look at the top card of your library any time.\nYou may play lands from the top of your library.\nWhen Ka-Zar enters, create Zabu, a legendary 2/2 green Cat creature token with \"Landfall — Whenever a land you control enters, put a +1/+1 counter on Zabu.\"")
    (power := some 3)
    (toughness := some 2)
    (mayLookAtTopAnytime := true)
    (mayPlayLandsFromTop := true)
    (triggeredAbilities := #[.onEnter .createZabu])

def knightOfWundagore : CardDef :=
  card "Knight of Wundagore" #[.creature] ({ symbols := #[.generic 1, .colored .green] })
    (subtypes := #["Cat", "Knight", "Villain"])
    (oracleText := "Trample\nWhenever you put a +1/+1 counter on another creature, put a +1/+1 counter on this creature. This ability triggers only once each turn.")
    (power := some 2)
    (toughness := some 1)
    (keywords := Keyword.trample)
    (triggeredAbilities := #[.onResource .plusOneOnThisOnce])

def misterHydeMonsterWithin : CardDef :=
  card "Mister Hyde, Monster Within" #[.creature] ({ symbols := #[.generic 2, .colored .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Villain"])
    (oracleText := "At the beginning of your upkeep, choose one —\n• Put a +1/+1 counter on Mister Hyde.\n• Remove a counter from a creature you control. If you do, draw a card.")
    (power := some 2)
    (toughness := some 2)
    (triggeredAbilities := #[.onStep .hydeChoose])

def moleManMoloidMaster : CardDef :=
  card "Mole Man, Moloid Master" #[.creature] ({ symbols := #[.generic 2, .colored .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Villain"])
    (oracleText := "You may play lands from your graveyard.\nLandfall — Whenever a land you control enters, create a 1/1 green Minion creature token named Moloid with \"Whenever this token attacks, you may mill a card.\"")
    (power := some 1)
    (toughness := some 1)
    (staticAbilities := #[StaticAbility.mayPlayLandsFromGraveyard])
    (triggeredAbilities := #[.onLandYouControlEntersCreateTokens .moloid 1])

def petAvengers : CardDef :=
  card "Pet Avengers" #[.creature] ({ symbols := #[.generic 3, .colored .green] })
    (subtypes := #["Dragon", "Cat", "Dog", "Bird", "Frog", "Hero"])
    (oracleText := "Reach\nPower-up — {6}{G}: Put a +1/+1 counter on this creature and create a 3/2 white Hero creature token with vigilance. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)")
    (power := some 4)
    (toughness := some 4)
    (keywords := Keyword.reach)
    (activatedAbilities := #[activated (Effect.ofAbility (.plusOneAndCreateTokens 1 .hero32vigilance)) ({ symbols := #[.generic 6, .colored .green] }) (powerUp := true)])

def powerfulBroker : CardDef :=
  card "Powerful Broker" #[.creature] ({ symbols := #[.generic 2, .colored .green] })
    (subtypes := #["Human", "Villain"])
    (oracleText := "{T}: For each kind of counter on target permanent or player, give that permanent or player another counter of that kind. Activate only as a sorcery.")
    (power := some 3)
    (toughness := some 3)
    (activatedAbilities := #[activated (Effect.ofAbility .proliferateEachKind) (ManaCost.empty) (tap := true) (onlyAsSorcery := true)])

def punishingPunch : CardDef :=
  card "Punishing Punch" #[.instant] ({ symbols := #[.generic 2, .colored .green] })
    (oracleText := "This spell costs {2} less to cast if there are two or more creature cards in your graveyard.\nTarget creature you control deals damage equal to twice its power to target creature an opponent controls.")
    (costReductionIfGyCreaturesAtLeast := some (2, 2))
    (spellEffect := some (Effect.ofSpell .creatureYouControlDealsTwicePower))

def rapidRescue : CardDef :=
  card "Rapid Rescue" #[.instant] ({ symbols := #[.colored .green] })
    (oracleText := "Mill two cards. You may put a permanent card from among the milled cards into your hand. You gain 2 life. (To mill two cards, put the top two cards of your library into your graveyard.)")
    (spellEffect := some (Effect.ofSpell (.millThenPutPermanentGainLife 2 2)))

def reptilDinomorpher : CardDef :=
  card "Reptil, Dinomorpher" #[.creature] ({ symbols := #[.colored .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Brontosaurus — {3}: Until end of turn, Reptil becomes a Dinosaur Hero with base power and toughness 3/5 and gains reach and vigilance.\nTyrannosaurus Rex — {6}: Until end of turn, Reptil becomes a Dinosaur Hero with base power and toughness 6/6 and gains trample.")
    (power := some 1)
    (toughness := some 2)
    (activatedAbilities := #[activated (Effect.ofAbility (.becomeDinosaurHero 3 5 (Keyword.reach.merge Keyword.vigilance))) ({ symbols := #[.generic 3] }),
      activated (Effect.ofAbility (.becomeDinosaurHero 6 6 Keyword.trample)) ({ symbols := #[.generic 6] })])

def restorativeTechnique : CardDef :=
  card "Restorative Technique" #[.sorcery] ({ symbols := #[.generic 2, .colored .green] })
    (oracleText := "Target player gains 2 life, then searches their library for a basic land card, puts it onto the battlefield tapped, then shuffles. Put a +1/+1 counter on up to one target creature.")
    (spellEffect := some (Effect.ofSpell (.gainLifeSearchBasicPlusOne 2)))

def rickJonesDestinedSidekick : CardDef :=
  card "Rick Jones, Destined Sidekick" #[.creature] ({ symbols := #[.colored .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Advisor"])
    (oracleText := "{3}, {T}: Mill four cards. You may put a Hero or enchantment card from among those cards into your hand. (To mill four cards, put the top four cards of your library into your graveyard.)")
    (power := some 0)
    (toughness := some 3)
    (activatedAbilities := #[activated (Effect.ofAbility (.millThenPutHeroOrEnchantment 4)) ({ symbols := #[.generic 3] }) (tap := true)])

def savageLandDinosaur : CardDef :=
  card "Savage Land Dinosaur" #[.creature] ({ symbols := #[.generic 4, .colored .green, .colored .green] })
    (subtypes := #["Dinosaur"])
    (oracleText := "Trample\nBasic landcycling {2} ({2}, Discard this card: Search your library for a basic land card, reveal it, put it into your hand, then shuffle.)")
    (power := some 7)
    (toughness := some 6)
    (keywords := Keyword.trample)
    (activatedAbilities := #[typecyclingAbility "Basic land" (ManaCost.ofGeneric 2)])

def serpentSpecialist : CardDef :=
  card "Serpent Specialist" #[.creature] ({ symbols := #[.colored .green] })
    (subtypes := #["Human", "Snake", "Villain"])
    (oracleText := "Deathtouch\nPower-up — {3}{G}: Put two +1/+1 counters on this creature. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)")
    (power := some 1)
    (toughness := some 1)
    (keywords := Keyword.deathtouch)
    (activatedAbilities := #[powerUpAbility (Effect.ofAbility (.putPlusOnePlusOneOnSource 2)) ({ symbols := #[.generic 3, .colored .green] })])

def shangChiMasterOfKungFu : CardDef :=
  card "Shang-Chi, Master of Kung Fu" #[.creature] ({ symbols := #[.generic 1, .colored .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Warrior", "Hero"])
    (oracleText := "You may activate abilities of creatures you control as though those creatures had haste.\n{T}: Add two mana of any one color. Spend this mana only to activate abilities of creature sources.")
    (power := some 2)
    (toughness := some 2)
    (staticAbilities := #[StaticAbility.activateCreaturesAsThoughHaste])
    (activatedAbilities := #[activated (Effect.ofAbility .addTwoAnyColorCreatureSources) (ManaCost.empty) (tap := true)])

def sheHulkJadeDefender : CardDef :=
  card "She-Hulk, Jade Defender" #[.creature] ({ symbols := #[.generic 3, .colored .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Gamma", "Hero"])
    (oracleText := "Reach, trample\nPower-up — {4}{G}{G}: Destroy up to one target artifact or enchantment. Put a +1/+1 counter on She-Hulk. (Activate each power-up ability only once. Reduce the cost by her mana cost if she entered this turn.)")
    (power := some 4)
    (toughness := some 4)
    (keywords := (Keyword.reach).merge Keyword.trample)
    (activatedAbilities := #[activated (Effect.ofAbility .destroyUpToOneThenPlusOne) ({ symbols := #[.generic 4, .colored .green, .colored .green] }) (powerUp := true)])

def superStrength : CardDef :=
  card "Super Strength" #[.enchantment] ({ symbols := #[.generic 4, .colored .green] })
    (subtypes := #["Aura"])
    (oracleText := "Enchant creature\nEnchanted creature gets +4/+4 and has trample and ward {1}. (Whenever enchanted creature becomes the target of a spell or ability an opponent controls, counter it unless that player pays {1}.)")
    (staticAbilities := #[StaticAbility.enchantedCreatureGetsHasAndWard 4 4
      Keyword.trample 1])

def theThingBenGrimm : CardDef :=
  card "The Thing, Ben Grimm" #[.creature] ({ symbols := #[.generic 5, .colored .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Trample\nWhenever one or more Heroes you control deal damage to a player, put two +1/+1 counters on The Thing.")
    (power := some 7)
    (toughness := some 7)
    (keywords := Keyword.trample)
    (triggeredAbilities := #[.onWatch .heroesDamagePlusTwo])

def tigraFelineFury : CardDef :=
  card "Tigra, Feline Fury" #[.creature] ({ symbols := #[.generic 1, .colored .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Cat", "Human", "Hero"])
    (oracleText := "Flash\nTrample\nWhenever you gain life, put a +1/+1 counter on Tigra.")
    (power := some 2)
    (toughness := some 1)
    (keywords := (Keyword.flash).merge Keyword.trample)
    (triggeredAbilities := #[.onGainLifePlusOne])

def trainingRegimen : CardDef :=
  card "Training Regimen" #[.enchantment] ({ symbols := #[.generic 3, .colored .green] })
    (oracleText := "Creatures you control with +1/+1 counters on them have trample.\nAt the beginning of combat on your turn, put a +1/+1 counter on target creature you control.")
    (triggeredAbilities := #[.onCombatPlusOneOnCreatureYouControl])
    (staticAbilities := #[StaticAbility.creaturesWithPlusOneHave Keyword.trample])

def theUnbeatableSquirrelGirl : CardDef :=
  card "The Unbeatable Squirrel Girl" #[.creature] ({ symbols := #[.generic 1, .colored .green, .colored .green, .colored .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Squirrel", "Human", "Hero"])
    (oracleText := "Do You Like Squirrels? — Whenever The Unbeatable Squirrel Girl enters or attacks, create a 1/1 green Squirrel creature token.\nI LOVE Squirrels! — {1}{G}{G}{G}: Create X 1/1 green Squirrel creature tokens, where X is the number of Squirrels you control.")
    (power := some 4)
    (toughness := some 4)
    (triggeredAbilities := #[.onEnterOrAttack .createSquirrel])
    (activatedAbilities := #[activated (Effect.ofAbility (.createTokensEqualSubtype .squirrel11green "Squirrel")) ({ symbols := #[.generic 1, .colored .green, .colored .green, .colored .green] })])

def undercoverSkrull : CardDef :=
  card "Undercover Skrull" #[.creature] ({ symbols := #[.generic 1, .colored .green] })
    (subtypes := #["Skrull", "Shapeshifter", "Villain"])
    (oracleText := "As long as there are two or more creature cards in your graveyard, this creature gets +2/+2 and is all creature types.\n{T}: Add one mana of any color.")
    (power := some 1)
    (toughness := some 1)
    (staticAbilities := #[StaticAbility.getsAndAllTypesIfGyCreatureCards 2 2 2])
    (activatedAbilities := #[activated (Effect.ofAbility (.addAnyColor)) (ManaCost.empty) (tap := true)])

def wakandanRoyalGuard : CardDef :=
  card "Wakandan Royal Guard" #[.creature] ({ symbols := #[.generic 4, .colored .green] })
    (subtypes := #["Human", "Soldier", "Hero"])
    (oracleText := "Vigilance\nWhen this creature enters, put a +1/+1 counter on target creature. If that creature is another Hero, put two +1/+1 counters on it instead.")
    (power := some 4)
    (toughness := some 4)
    (keywords := Keyword.vigilance)
    (triggeredAbilities := #[.onEnterPlusOneOrTwoIfAnotherHero])

def whiteTigerAvaAyala : CardDef :=
  card "White Tiger, Ava Ayala" #[.creature] ({ symbols := #[.generic 1, .colored .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Power-up — {5}{G}: Put a +1/+1 counter on White Tiger and create The Tiger God, a legendary 4/4 green Cat God creature token with \"The Tiger God can't be blocked by more than one creature.\" (Activate each power-up ability only once. Reduce the cost by her mana cost if she entered this turn.)")
    (power := some 2)
    (toughness := some 2)
    (activatedAbilities := #[activated (Effect.ofAbility .plusOneAndCreateTigerGod) ({ symbols := #[.generic 5, .colored .green] }) (powerUp := true)])

def worldWarHulk : CardDef :=
  card "World War Hulk" #[.enchantment] ({ symbols := #[.generic 3, .colored .green, .colored .green] })
    (subtypes := #["Saga"])
    (oracleText := "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)\nI — The next red or green creature spell you cast this turn can be cast without paying its mana cost.\nII — Put three +1/+1 counters on target creature you control.\nIII — Choose target creature you control. Until end of turn, double its power and toughness and it gains trample.")
    (saga := some { sacrificeAfter := "III", chapters := #[chapter "I" "The next red or green creature spell you cast this turn can be cast without paying its mana cost." (.spell .nextFreeRGCreature), chapter "II" "Put three +1/+1 counters on target creature you control." (.spell (.plusOneOnCreatureN 3)), chapter "III" "Choose target creature you control. Until end of turn, double its power and toughness and it gains trample." (.spell .chooseTargetDoubleAndTrample)] })

def abominationTerrifyingTitan : CardDef :=
  card "Abomination, Terrifying Titan" #[.creature] ({ symbols := #[.generic 3, .hybrid .red .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Gamma", "Villain"])
    (oracleText := "Trample\nPower-up — {5}{R/G}{R/G}: Put a +1/+1 counter on Abomination. He fights up to one target creature an opponent controls. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)")
    (power := some 4)
    (toughness := some 4)
    (keywords := Keyword.trample)
    (activatedAbilities := #[activated (Effect.ofAbility .plusOneThenFightUpToOne) ({ symbols := #[.generic 5, .hybrid .red .green, .hybrid .red .green] }) (powerUp := true)])

def absorbingMan : CardDef :=
  card "Absorbing Man" #[.creature] ({ symbols := #[.generic 1, .colored .green, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Villain"])
    (oracleText := "Vigilance\nAt the beginning of your first main phase, until your next turn, Absorbing Man becomes a copy of up to one target artifact, non-Aura enchantment, or land, except his name is Absorbing Man, he's a legendary 4/4 Human Villain creature in addition to his other types, and he has vigilance.")
    (power := some 4)
    (toughness := some 4)
    (keywords := Keyword.vigilance)
    (triggeredAbilities := #[.onStep .copyAbsorbingMan])

def alienInvasion : CardDef :=
  card "Alien Invasion" #[.enchantment] ({ symbols := #[.generic 1, .colored .red, .colored .red, .colored .green] })
    (oracleText := "At the beginning of combat on your turn, create a 1/1 red Alien creature token with haste and \"This token attacks each combat if able.\" Put a +1/+1 counter on it for each invasion counter on this enchantment, then put an invasion counter on this enchantment.")
    (triggeredAbilities := #[.onCombatCreateAlienPerInvasion])

def antManColonyCommander : CardDef :=
  card "Ant-Man, Colony Commander" #[.creature] ({ symbols := #[.generic 1, .colored .green, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Rogue", "Hero"])
    (oracleText := "Whenever Ant-Man attacks, you may pay {1}. When you do, put a +1/+1 counter on target creature.\nWhenever you put a +1/+1 counter on a creature, create a 1/1 green Insect creature token. This ability triggers only once each turn.")
    (power := some 2)
    (toughness := some 2)
    (triggeredAbilities := #[.onThisAttack .mayPayPlusOne, .onResource .plusOneCreateInsectOnce])

def aresGodOfWar : CardDef :=
  card "Ares, God of War" #[.creature] ({ symbols := #[.generic 1, .colored .black, .colored .red] })
    (supertypes := #[.legendary])
    (subtypes := #["God", "Warrior", "Villain"])
    (oracleText := "Ares attacks each combat if able.\nWhenever an attacking creature you control dies, return that card to its owner's hand.")
    (power := some 4)
    (toughness := some 3)
    (triggeredAbilities := #[.onDeath .attackingReturnHand])
    (staticAbilities := #[StaticAbility.attacksEachCombatIfAble])

def armorWars : CardDef :=
  card "Armor Wars" #[.enchantment] ({ symbols := #[.generic 2, .colored .blue, .colored .red] })
    (subtypes := #["Saga"])
    (oracleText := "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)\nI — You may draw a card for each artifact you control. If you do, each opponent draws a card.\nII — Artifact spells you cast this turn cost {1} less to cast.\nIII — This Saga deals X damage to target opponent, where X is the greatest mana value among artifacts you control.")
    (saga := some { sacrificeAfter := "III", chapters := #[chapter "I" "You may draw a card for each artifact you control. If you do, each opponent draws a card." (.spell .mayDrawPerArtifactOppsDraw), chapter "II" "Artifact spells you cast this turn cost {1} less to cast." (.spell (.artifactSpellsCostLessThisTurn 1)), chapter "III" "This Saga deals X damage to target opponent, where X is the greatest mana value among artifacts you control." .dealXDamageToTargetOpponentGreatestArtifactMv] })

def theAstonishingAntMan : CardDef :=
  card "The Astonishing Ant-Man" #[.creature] ({ symbols := #[.colored .green, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Scientist", "Hero"])
    (oracleText := "Whenever you draw a card, put a +1/+1 counter on The Astonishing Ant-Man.\n{2}{G}, {T}, Remove any number of +1/+1 counters from The Astonishing Ant-Man: Create that many 1/1 green Insect creature tokens.")
    (power := some 1)
    (toughness := some 1)
    (triggeredAbilities := #[.onDrawPlusOne])
    (activatedAbilities := #[activated (Effect.ofAbility (.createTokensEqualRemovedPlusOnes .insect11green))
      ({ symbols := #[.generic 2, .colored .green] }) (tap := true) (removeAnyNumberPlusOne := true)])

def avengersUnderSiege : CardDef :=
  card "Avengers: Under Siege" #[.enchantment] ({ symbols := #[.generic 2, .colored .black, .colored .red] })
    (subtypes := #["Saga"])
    (oracleText := "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)\nI — Create two 2/1 black Villain creature tokens with menace.\nII — This Saga deals 2 damage to each non-Villain creature and each opponent.\nIII — Create a Treasure token for each Villain you control.")
    (saga := some { sacrificeAfter := "III", chapters := #[chapter "I" "Create two 2/1 black Villain creature tokens with menace." (.spell (.createTokens .villain21menace 2)), chapter "II" "This Saga deals 2 damage to each non-Villain creature and each opponent." (.dealDamageToEachNonSubtypeAndOpponents 2 "Villain"), chapter "III" "Create a Treasure token for each Villain you control." (.spell (.createTokensPerSubtype .treasure "Villain"))] })

def beastEruditeAerialist : CardDef :=
  card "Beast, Erudite Aerialist" #[.creature] ({ symbols := #[.generic 3, .hybrid .green .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Mutant", "Scientist", "Hero"])
    (oracleText := "As long as you've put one or more +1/+1 counters on Beast this turn, he has flying.\nWhenever Beast deals combat damage to a player, draw a card.")
    (power := some 3)
    (toughness := some 3)
    (triggeredAbilities := #[.onCombatDamageDraw 1])
    (staticAbilities := #[StaticAbility.flyingIfPlusOneThisTurn])

def blackPantherVanguard : CardDef :=
  card "Black Panther, Vanguard" #[.creature] ({ symbols := #[.generic 2, .colored .green, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Warrior", "Hero"])
    (oracleText := "Whenever another nontoken Hero you control enters, choose one —\n• Create a 1/1 white Soldier creature token.\n• Creatures you control get +1/+1 until end of turn.")
    (power := some 4)
    (toughness := some 4)
    (triggeredAbilities := #[.onWatch .nontokenHeroModal])

def blackWidowDoubleAgent : CardDef :=
  card "Black Widow, Double Agent" #[.creature] ({ symbols := #[.generic 1, .colored .white, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero", "Villain"])
    (oracleText := "Deathtouch\nWhenever a creature you control attacks alone, it gains first strike and menace until end of turn. (It can't be blocked except by two or more creatures.)")
    (power := some 3)
    (toughness := some 2)
    (keywords := Keyword.deathtouch)
    (triggeredAbilities := #[.onWatch .attacksAloneFirstStrikeMenace])

def bullseyeDeathDealer : CardDef :=
  card "Bullseye, Death Dealer" #[.creature] ({ symbols := #[.generic 2, .hybrid .black .red] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Assassin", "Villain"])
    (oracleText := "When Bullseye enters, you may sacrifice an artifact or discard a nonland card. When you do, Bullseye deals 2 damage to any target.\n{3}, {T}, Sacrifice an artifact or discard a nonland card: Bullseye deals 2 damage to any target.")
    (power := some 2)
    (toughness := some 3)
    (triggeredAbilities := #[.onEnter .maySacOrDiscardNonlandThenDamage])
    (activatedAbilities := #[activated (Effect.ofAbility (.dealDamageToAny 2)) ({ symbols := #[.generic 3] })
      (tap := true) (sacrificeArtifactOrDiscardNonland := true)])

def captainAmericaLivingLegend : CardDef :=
  card "Captain America, Living Legend" #[.creature] ({ symbols := #[.generic 1, .colored .white, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Soldier", "Hero"])
    (oracleText := "Vigilance\nWhenever a creature you control becomes tapped during your turn, if it's the first time that creature has become tapped this turn, untap it.")
    (power := some 3)
    (toughness := some 4)
    (keywords := Keyword.vigilance)
    (triggeredAbilities := #[.onWatch .firstTapUntap])

def cloakAndDaggerEntwined : CardDef :=
  card "Cloak and Dagger, Entwined" #[.creature] ({ symbols := #[.generic 1, .colored .white, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Deathtouch, lifelink\nWhen Cloak and Dagger enter, choose target opponent and up to one target creature they control. They reveal their hand. You may exile a nonland card from their hand or the chosen creature until Cloak and Dagger leave the battlefield.")
    (power := some 2)
    (toughness := some 2)
    (keywords := (Keyword.deathtouch).merge Keyword.lifelink)
    (triggeredAbilities := #[.onEnter .revealHandExileUntilLeaves])

def theComingOfGalactus : CardDef :=
  card "The Coming of Galactus" #[.enchantment] ({ symbols := #[.generic 2, .colored .black, .colored .black, .colored .green] })
    (subtypes := #["Saga"])
    (oracleText := "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after IV.)\nI — Destroy up to one target nonland permanent.\nII, III — Each opponent loses 2 life.\nIV — Create Galactus, a legendary 16/16 black Elder Alien creature token with flying, trample, and \"Whenever Galactus attacks, destroy target land.\"")
    (saga := some { sacrificeAfter := "IV", chapters := #[chapter "I" "Destroy up to one target nonland permanent." (.spell .destroyUpToOneNonland), chapter "II, III" "Each opponent loses 2 life." (.spell (.eachOpponentLosesLife 2)), chapter "IV" "Create Galactus, a legendary 16/16 black Elder Alien creature token with flying, trample, and \"Whenever Galactus attacks, destroy target land.\"." (.spell .createGalactus)] })

def daredevilManWithoutFear : CardDef :=
  card "Daredevil, Man Without Fear" #[.creature] ({ symbols := #[.generic 2, .colored .red, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Vigilance, haste\nRadar Sense — You may look at the top card of your library any time.\nWhenever you attack, you may exile the top card of your library. If that card is a Hero card, Daredevil gets +2/+1 until end of turn. You may play that card this turn.")
    (power := some 3)
    (toughness := some 4)
    (keywords := (Keyword.vigilance).merge Keyword.haste)
    (mayLookAtTopAnytime := true)
    (triggeredAbilities := #[.onYouAttacking .exileTopHeroPump])

def ghostSpectralSaboteur : CardDef :=
  card "Ghost, Spectral Saboteur" #[.creature] ({ symbols := #[.generic 2, .hybrid .blue .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Rogue", "Villain"])
    (oracleText := "Flash\nIntangibility — Ghost can't be blocked.")
    (power := some 2)
    (toughness := some 2)
    (keywords := (Keyword.flash).merge Keyword.cantBeBlocked)

def hulkGammaGoliath : CardDef :=
  card "Hulk, Gamma Goliath" #[.creature] ({ symbols := #[.generic 3, .colored .red, .colored .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Gamma", "Berserker", "Hero"])
    (oracleText := "Reach, trample\nPower-up abilities of other creatures you control cost {3} less to activate.\nPower-up — {6}{R}{G}: Put five +1/+1 counters on Hulk. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn.)")
    (power := some 6)
    (toughness := some 5)
    (keywords := (Keyword.reach).merge Keyword.trample)
    (staticAbilities := #[StaticAbility.otherPowerUpCostsLess 3])
    (activatedAbilities := #[powerUpAbility (Effect.ofAbility (.putPlusOnePlusOneOnSource 5)) ({ symbols := #[.generic 6, .colored .red, .colored .green] })])

def ironManMasterOfMachines : CardDef :=
  card "Iron Man, Master of Machines" #[.artifact, .creature] ({ symbols := #[.generic 2, .colored .blue, .colored .red] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Flying, vigilance\nIron Man gets +1/+0 for each other artifact you control.\nWhenever Iron Man attacks, if an artifact entered the battlefield under your control this turn, draw a card.")
    (power := some 1)
    (toughness := some 4)
    (keywords := (Keyword.flying).merge Keyword.vigilance)
    (triggeredAbilities := #[.onThisAttack .ifArtifactEnteredDraw])
    (staticAbilities := #[StaticAbility.getsPowerPerOtherArtifact 1])

def kangTemporalTyrant : CardDef :=
  card "Kang, Temporal Tyrant" #[.creature] ({ symbols := #[.generic 2, .colored .blue, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Villain"])
    (oracleText := "Whenever Kang attacks, he connives. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on this creature.)\nWhenever you draw your second card each turn, each opponent loses 1 life and you gain 1 life.")
    (power := some 3)
    (toughness := some 4)
    (triggeredAbilities := #[.onAttackConnive, .onResource .secondDrawDrain])

def killmongerScourgeOfWakanda : CardDef :=
  card "Killmonger, Scourge of Wakanda" #[.creature] ({ symbols := #[.generic 2, .colored .black, .colored .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Mercenary", "Villain"])
    (oracleText := "When Killmonger enters, you may sacrifice another creature. When you do, destroy target nonland permanent an opponent controls.\nAs long as there are two or more creature cards in your graveyard, Killmonger gets +2/+1.")
    (power := some 3)
    (toughness := some 3)
    (triggeredAbilities := #[.onEnter .maySacAnotherThenDestroyOppNonland])
    (staticAbilities := #[StaticAbility.getsIfGyCreatureCards 2 2 1])

def kingTChalla : CardDef :=
  card "King T'Challa" #[.creature] ({ symbols := #[.generic 1, .colored .white, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Noble", "Hero"])
    (oracleText := "Flash\nWhenever a player draws their second card each turn, you draw a card.\n{4}{W}{U}: Transform King T'Challa. Activate only as a sorcery.")
    (power := some 3)
    (toughness := some 2)
    (keywords := Keyword.flash)
    (triggeredAbilities := #[.onWatch .anyPlayerSecondDraw])
    (activatedAbilities := #[activated (Effect.ofAbility (.transform)) ({ symbols := #[.generic 4, .colored .white, .colored .blue] }) (onlyAsSorcery := true)])
    (otherFace := some blackPantherHopeEnduring)

def theKingpinOfCrime : CardDef :=
  card "The Kingpin of Crime" #[.creature] ({ symbols := #[.generic 1, .colored .white, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Villain"])
    (oracleText := "Extort (Whenever you cast a spell, you may pay {W/B}. If you do, each opponent loses 1 life and you gain that much life.)\nWhenever you attack, you may pay 2 life. If you do, until end of turn, creatures you control with toughness greater than their power assign combat damage equal to their toughness rather than their power.")
    (power := some 1)
    (toughness := some 5)
    (triggeredAbilities := #[.onYouAttacking .pay2LifeToughness])
    (staticAbilities := #[.extort])

def madameHydra : CardDef :=
  card "Madame Hydra" #[.creature] ({ symbols := #[.generic 2, .colored .black, .colored .red] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Villain"])
    (oracleText := "Whenever you cast a Villain spell, create a 2/1 black Villain creature token with menace. (It can't be blocked except by two or more creatures.)")
    (power := some 2)
    (toughness := some 3)
    (triggeredAbilities := #[.onCasting .villainToken])

def theMightyThorJaneFoster : CardDef :=
  card "The Mighty Thor, Jane Foster" #[.creature] ({ symbols := #[.generic 1, .colored .white, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "God", "Hero"])
    (oracleText := "Flying\nWhenever The Mighty Thor attacks, exile up to one target nontoken artifact or creature, then return that card to the battlefield tapped under its owner's control.\nWhenever an Equipment you control enters, draw a card.")
    (power := some 3)
    (toughness := some 3)
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onThisAttack .blinkNontoken, .onEquipmentYouControlEntersDraw])

def moonGirlAndDevilDinosaur : CardDef :=
  card "Moon Girl and Devil Dinosaur" #[.creature] ({ symbols := #[.generic 1, .colored .green, .colored .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Dinosaur", "Hero"])
    (oracleText := "Whenever you draw your second card each turn, until end of turn, Moon Girl and Devil Dinosaur's base power and toughness become 6/6 and they gain trample.\nWhenever an artifact you control enters, draw a card. This ability triggers only once each turn.")
    (power := some 2)
    (toughness := some 2)
    (triggeredAbilities := #[.onResource .secondDrawBecome66, .onArtifactYouControlEntersDrawOnce])

def theRuinousWreckingCrew : CardDef :=
  card "The Ruinous Wrecking Crew" #[.creature] ({ symbols := #[.x, .colored .black, .colored .red] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Villain"])
    (oracleText := "The Ruinous Wrecking Crew enters with X +1/+1 counters on it.\nWhen The Ruinous Wrecking Crew enters, choose up to X —\n• Discard a card, then draw a card.\n• Target opponent loses 2 life.\n• Destroy target token.\n• Each player sacrifices a creature of their choice.")
    (power := some 2)
    (toughness := some 2)
    (triggeredAbilities := #[.onEnter .chooseUpToXModes])
    (staticAbilities := #[StaticAbility.entersWithXPlusOne])

def scientistSupremeOfAIM : CardDef :=
  card "Scientist Supreme of A.I.M." #[.creature] ({ symbols := #[.colored .blue, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Scientist", "Villain"])
    (oracleText := "Pay 2 life: Copy target activated or triggered ability you control from an artifact source. You may choose new targets for the copy. Activate only during your turn and only once each turn. (Mana abilities can't be targeted.)")
    (power := some 2)
    (toughness := some 2)
    (activatedAbilities := #[activated (Effect.ofAbility (.copyControlledAbility false))
      (payLife := 2) (onlyDuringYourTurn := true) (onceEachTurn := true)])

def theSerpentSociety : CardDef :=
  card "The Serpent Society" #[.creature] ({ symbols := #[.generic 1, .colored .black, .colored .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Snake", "Villain"])
    (oracleText := "Deathtouch\nWard—Get five poison counters. (A player with ten or more poison counters loses the game.)\nWhenever another creature you control with deathtouch dies, each opponent sacrifices a nontoken creature of their choice.")
    (power := some 3)
    (toughness := some 4)
    (keywords := Keyword.deathtouch)
    (triggeredAbilities := #[.onDeath .deathtouchOppSac])
    (staticAbilities := #[StaticAbility.wardPoisonCounters 5])

def speedballNewWarrior : CardDef :=
  card "Speedball, New Warrior" #[.creature] ({ symbols := #[.generic 2, .hybrid .blue .red] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Whenever a player casts a spell that targets Speedball, he gets +2/+2 until end of turn. You may choose new targets for that spell.")
    (power := some 2)
    (toughness := some 2)
    (triggeredAbilities := #[.onWatch .speedballTargeted])

def spiderManToTheRescue : CardDef :=
  card "Spider-Man, To the Rescue" #[.creature] ({ symbols := #[.generic 2, .hybrid .green .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Spider", "Human", "Hero"])
    (oracleText := "Flash\nReach, vigilance\nNo One Dies! — When Spider-Man enters, you may tap him. When you do, another target nonattacking creature you control gains indestructible until end of turn. (Damage and effects that say \"destroy\" don't destroy it.)")
    (power := some 3)
    (toughness := some 2)
    (keywords := ((Keyword.flash).merge Keyword.reach).merge Keyword.vigilance)
    (triggeredAbilities := #[.onEnter .mayTapThenGrantIndestructible])

def spiderWomanSecretAgent : CardDef :=
  card "Spider-Woman, Secret Agent" #[.creature] ({ symbols := #[.generic 3, .hybrid .white .blue] })
    (supertypes := #[.legendary])
    (subtypes := #["Spider", "Human", "Spy", "Hero"])
    (oracleText := "Flash\nWhen Spider-Woman enters, tap target creature an opponent controls. That creature can't become untapped for as long as you control Spider-Woman.")
    (power := some 1)
    (toughness := some 4)
    (keywords := Keyword.flash)
    (triggeredAbilities := #[.onEnter .tapOppCantUntapWhileControl])

def stormWindrider : CardDef :=
  card "Storm, Windrider" #[.creature] ({ symbols := #[.generic 1, .colored .green, .colored .white, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Mutant", "Hero"])
    (oracleText := "Flying\nCreatures with flying can't attack you or block creatures you control.\nWhenever you cast a spell that targets one or more creatures, those creatures gain flying until end of turn.")
    (power := some 4)
    (toughness := some 4)
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onCasting .targetsGainFlying])
    (staticAbilities := #[StaticAbility.flyingCantAttackYouOrBlockYours])

def theSuperHeroCivilWar : CardDef :=
  card "The Super Hero Civil War" #[.enchantment] ({ symbols := #[.generic 3, .colored .red, .colored .white] })
    (subtypes := #["Saga"])
    (oracleText := "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)\nI — Gain control of up to two target creatures with total mana value 6 or less for as long as this Saga remains on the battlefield.\nII — Creatures you control get +1/+1 and gain vigilance until end of turn.\nIII — Target creature you control fights up to one other target creature.")
    (saga := some { sacrificeAfter := "III", chapters := #[chapter "I" "Gain control of up to two target creatures with total mana value 6 or less for as long as this Saga remains on the battlefield." (.gainControlOfUpToTwoCreaturesTotalMvAtMost 6), chapter "II" "Creatures you control get +1/+1 and gain vigilance until end of turn." (.spell (.creaturesYouControlGetAndGrant 1 1 Keyword.vigilance)), chapter "III" "Target creature you control fights up to one other target creature." (.spell (.fightUpToOne))] })

def taskmasterMercenaryMimic : CardDef :=
  card "Taskmaster, Mercenary Mimic" #[.creature] ({ symbols := #[.generic 2, .colored .blue, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Mercenary", "Villain"])
    (oracleText := "Photographic Reflexes — At the beginning of your first main phase, until your next turn, Taskmaster becomes a copy of up to one target creature on the battlefield or creature card in a graveyard, except his name is Taskmaster, Mercenary Mimic and he's a legendary Human Mercenary Villain creature.")
    (power := some 3)
    (toughness := some 5)
    (triggeredAbilities := #[.onStep .copyTaskmaster])

def thanosTheMadTitan : CardDef :=
  card "Thanos, the Mad Titan" #[.creature] ({ symbols := #[.colored .red, .colored .white, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Eternal", "Villain"])
    (oracleText := "Deathtouch, lifelink\nPower-up — {C}{W}{U}{B}{R}{G}: Put two +1/+1 counters on Thanos. Choose odd or even. Destroy each other creature with mana value of the chosen quality. (Activate each power-up ability only once. Reduce the cost by his mana cost if he entered this turn. Zero is even.)")
    (power := some 4)
    (toughness := some 4)
    (keywords := (Keyword.deathtouch).merge Keyword.lifelink)
    (activatedAbilities := #[activated (Effect.ofAbility .plusTwoThenOddEvenDestroy) ({ symbols := #[.colorless, .colored .white, .colored .blue, .colored .black, .colored .red, .colored .green] }) (powerUp := true)])

def thorOdinson : CardDef :=
  card "Thor Odinson" #[.creature] ({ symbols := #[.generic 3, .colored .red, .colored .white] })
    (supertypes := #[.legendary])
    (subtypes := #["God", "Warrior", "Hero"])
    (oracleText := "Flying, vigilance, prowess, prowess (Whenever you cast a noncreature spell, this creature gets +1/+1 until end of turn twice.)")
    (power := some 4)
    (toughness := some 4)
    (keywords := (((Keyword.flying).merge Keyword.vigilance).merge Keyword.prowess).merge Keyword.prowess)

def titaniaRuggedRumbler : CardDef :=
  card "Titania, Rugged Rumbler" #[.creature] ({ symbols := #[.generic 2, .hybrid .black .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Villain"])
    (oracleText := "As an additional cost to cast this spell, discard a card or pay {2}.\nWard—Discard a card or pay {2}. (Whenever this creature becomes the target of a spell or ability an opponent controls, counter it unless that player discards a card or pays {2}.)")
    (power := some 5)
    (toughness := some 5)
    (additionalCostDiscardOrPayGeneric := some 2)
    (staticAbilities := #[StaticAbility.wardDiscardOrPay 2])

def uSAgentJohnWalker : CardDef :=
  card "U.S.Agent, John Walker" #[.creature] ({ symbols := #[.generic 3, .hybrid .white .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Soldier", "Hero"])
    (oracleText := "When U.S.Agent enters, create a colorless Equipment artifact token named Sturdy Shield with \"Equipped creature gets +1/+2\" and equip {2}. Attach it to U.S.Agent.")
    (power := some 3)
    (toughness := some 2)
    (triggeredAbilities := #[.onEnter .createSturdyShieldAttach])

def visionQuest : CardDef :=
  card "Vision Quest" #[.sorcery] ({ symbols := #[.x, .colored .blue, .colored .red] })
    (oracleText := "Search your library and/or graveyard for an artifact creature card with mana value X or less and put it onto the battlefield with X additional +1/+1 counters on it. If X is 4 or greater, it gains haste until end of turn. If you search your library this way, shuffle.")
    (spellEffect := some (Effect.ofSpell .searchLibraryOrGyArtifactCreatureX))

def warMachineLegacyOfIron : CardDef :=
  card "War Machine, Legacy of Iron" #[.artifact, .creature] ({ symbols := #[.generic 2, .hybrid .red .white] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Hero"])
    (oracleText := "Flying\nAt the beginning of combat on your turn, another target creature you control gets +X/+0 until end of turn, where X is War Machine's power.")
    (power := some 1)
    (toughness := some 3)
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onCombatAnotherGetsSourcePower])

def winterSoldierIcyAssassin : CardDef :=
  card "Winter Soldier, Icy Assassin" #[.creature] ({ symbols := #[.colored .white, .colored .black] })
    (supertypes := #[.legendary])
    (subtypes := #["Human", "Assassin", "Villain"])
    (oracleText := "Vigilance, menace\nWinter Soldier gets +2/+0 for each Equipment attached to him.\n{3}{W}{B}: Return this card from your graveyard to the battlefield with a finality counter on him. Then you may attach an Equipment you control to him. (If a creature with a finality counter on it would die, exile it instead.)")
    (power := some 2)
    (toughness := some 2)
    (keywords := (Keyword.vigilance).merge Keyword.menace)
    (staticAbilities := #[StaticAbility.getsPowerPerAttachedEquipment 2])
    (activatedAbilities := #[activated (Effect.ofAbility .returnFromGyFinalityAttach) ({ symbols := #[.generic 3, .colored .white, .colored .black] })
      (activateFromGraveyard := true)])

def wolverineFierceFighter : CardDef :=
  card "Wolverine, Fierce Fighter" #[.creature] ({ symbols := #[.generic 2, .colored .red, .colored .green] })
    (supertypes := #[.legendary])
    (subtypes := #["Mutant", "Berserker", "Hero"])
    (oracleText := "Haste\nWhen Wolverine enters, he fights up to one other target creature.\nIf damage would be dealt to Wolverine, instead that damage is dealt, but all other damage already dealt to him is healed.")
    (power := some 3)
    (toughness := some 5)
    (keywords := Keyword.haste)
    (triggeredAbilities := #[.onEnter .fightUpToOne])
    (staticAbilities := #[StaticAbility.healOtherDamageWhenDealt])

def worldsWithinWorlds : CardDef :=
  card "Worlds Within Worlds" #[.sorcery] ({ symbols := #[.generic 5, .colored .green, .colored .blue] })
    (oracleText := "Exile all creatures. Each player may put any number of creature cards from their hand onto the battlefield. Then put all cards exiled this way into their owners' hands. Exile Worlds Within Worlds.")
    (spellEffect := some (Effect.ofSpell .worldsWithinWorlds))

def aIMSynthoids : CardDef :=
  artifactCreature "A.I.M. Synthoids" ({ symbols := #[.generic 2] })
    #["Robot", "Villain"] 1 3
    "When this creature enters, surveil 2. (Look at the top two cards of your library, then put any number of them into your graveyard and the rest on top of your library in any order.)"
    (triggeredAbilities := #[.onEnterSurveil 2])

def arcReactor : CardDef :=
  card "Arc Reactor" #[.artifact] ({ symbols := #[.generic 5] })
    (oracleText := "Improvise (Your artifacts can help cast this spell. Each artifact you tap after you're done activating mana abilities pays for {1}.)\nThis artifact enters tapped.\n{T}: Add {C}{C}{C}.")
    (entersTapped := true)
    (staticAbilities := #[.improvise])
    (activatedAbilities := #[activated (Effect.ofAbility (.addMana #[.colorless, .colorless, .colorless])) (ManaCost.empty) (tap := true)])

def captainAmericaSShield : CardDef :=
  equipment "Captain America's Shield" ({ symbols := #[.generic 2] })
    "Indestructible\nEquipped creature gets +0/+8 and has vigilance.\nWhenever equipped creature attacks, tap target creature defending player controls.\nEquip {2}"
    ({ symbols := #[.generic 2] })
    (legendary := true)
    (keywords := Keyword.indestructible)
    (triggeredAbilities := #[.onWatch .equippedAttacksTap])
    (staticAbilities := #[StaticAbility.equippedCreatureGetsAndHas 0 8 Keyword.vigilance])

def cosmicCube : CardDef :=
  card "Cosmic Cube" #[.artifact] ({ symbols := #[.generic 5] })
    (oracleText := "Ward {2}\nWhenever you attack, look at the top six cards of your library. You may cast a spell from among them with mana value less than or equal to the greatest power among attacking creatures you control without paying its mana cost. Put the rest on the bottom of your library in a random order.")
    (ward := some 2)
    (triggeredAbilities := #[.onYouAttacking .lookSixCast])

def dependableQuinjet : CardDef :=
  card "Dependable Quinjet" #[.artifact] ({ symbols := #[.generic 3] })
    (subtypes := #["Vehicle"])
    (oracleText := "Flying\n{T}: Add one mana of any color.\nCrew 4 (Tap any number of creatures you control with total power 4 or more: This Vehicle becomes an artifact creature until end of turn.)")
    (power := some 3)
    (toughness := some 3)
    (keywords := Keyword.flying)
    (crew := some 4)
    (activatedAbilities := #[activated (Effect.ofAbility (.addAnyColor)) (ManaCost.empty) (tap := true)])

def hERBIEScoutUnit : CardDef :=
  card "H.E.R.B.I.E. Scout Unit" #[.artifact, .creature] ({ symbols := #[.generic 4] })
    (subtypes := #["Robot", "Scout"])
    (oracleText := "Flying\nWhen this creature enters, draw a card, then you may put a land card from your hand onto the battlefield tapped.")
    (power := some 2)
    (toughness := some 1)
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onEnterDrawMayPutLandTapped])

def ironManArmor : CardDef :=
  card "Iron Man Armor" #[.artifact] ({ symbols := #[.generic 3] })
    (subtypes := #["Equipment"])
    (oracleText := "When this Equipment enters, attach it to target creature you control.\nEquipped creature gets +2/+1 and has flying.\n{2}: If this Equipment isn't a creature, it becomes a 0/0 Construct Hero artifact creature with flying and \"This creature gets +1/+1 for each artifact you control\" until end of turn.\nEquip {2}")
    (triggeredAbilities := #[.onEnterAttachToCreatureYouControl])
    (staticAbilities := #[StaticAbility.equippedCreatureGetsAndHas 2 1 Keyword.flying])
    (activatedAbilities := #[activated (Effect.ofAbility .equipmentBecomesConstructHero) ({ symbols := #[.generic 2] }), equipAbility ({ symbols := #[.generic 2] })])

def sHIELDHelicarrier : CardDef :=
  card "S.H.I.E.L.D. Helicarrier" #[.artifact] ({ symbols := #[.generic 4] })
    (subtypes := #["Vehicle"])
    (oracleText := "Flying\nWhen this Vehicle enters, create two 1/1 white Soldier creature tokens.\nCrew 6 (Tap any number of creatures you control with total power 6 or more: This Vehicle becomes an artifact creature until end of turn.)")
    (power := some 4)
    (toughness := some 5)
    (keywords := Keyword.flying)
    (crew := some 6)
    (triggeredAbilities := #[.onEnterCreateTokens .soldier11white 2])

def superAdaptoid : CardDef :=
  card "Super-Adaptoid" #[.artifact, .creature] ({ symbols := #[.generic 2] })
    (supertypes := #[.legendary])
    (subtypes := #["Robot", "Villain"])
    (oracleText := "Super-Adaptoid's power is equal to the number of legendary creatures you control.\nWhenever Super-Adaptoid enters or attacks, choose another target creature. If that creature has haste and Super-Adaptoid doesn't, put a haste counter on Super-Adaptoid. Do the same for flying, first strike, double strike, deathtouch, indestructible, lifelink, menace, reach, trample, and vigilance.")
    (toughness := some 2)
    (triggeredAbilities := #[.onEnterOrAttack .copyKeywords])
    (staticAbilities := #[.powerEqualLegendaryCreaturesYouControl])

def theTenRings : CardDef :=
  card "The Ten Rings" #[.artifact] ({ symbols := #[.generic 8] })
    (supertypes := #[.legendary])
    (oracleText := "Your maximum hand size is ten.\nAt the beginning of your end step, if you have fewer than ten cards in hand, draw cards equal to the difference.")
    (triggeredAbilities := #[.onStep .drawToTen])
    (staticAbilities := #[.maximumHandSize 10])

def ultronArtificialMalevolence : CardDef :=
  card "Ultron, Artificial Malevolence" #[.artifact, .creature] ({ symbols := #[.generic 3] })
    (supertypes := #[.legendary])
    (subtypes := #["Robot", "Villain"])
    (oracleText := "Whenever another nontoken artifact you control enters, you may pay {2}. If you do, create a token that's a copy of it. If the token isn't a creature, it becomes a 2/2 Robot Villain creature in addition to its other types.")
    (power := some 2)
    (toughness := some 4)
    (triggeredAbilities := #[.onWatch .ultronCopy])

def ultronDrone : CardDef :=
  card "Ultron Drone" #[.artifact, .creature] ({ symbols := #[.generic 3] })
    (subtypes := #["Robot", "Villain"])
    (oracleText := "Power-up — {6}: Put two +1/+1 counters on this creature and create a 2/2 colorless Robot Villain artifact creature token. (Activate each power-up ability only once. Reduce the cost by its mana cost if it entered this turn.)")
    (power := some 2)
    (toughness := some 3)
    (activatedAbilities := #[activated (Effect.ofAbility (.plusOneAndCreateTokens 2 .robotVillain22)) ({ symbols := #[.generic 6] }) (powerUp := true)])

def vibraniumEnergyDaggers : CardDef :=
  card "Vibranium Energy Daggers" #[.artifact] ({ symbols := #[.generic 1] })
    (subtypes := #["Equipment"])
    (oracleText := "Indestructible (Effects that say \"destroy\" don't destroy this Equipment.)\nEquipped creature gets +2/+2.\nEquip {3} ({3}: Attach to target creature you control. Equip only as a sorcery.)")
    (keywords := Keyword.indestructible)
    (staticAbilities := #[StaticAbility.equippedCreatureGets 2 2])
    (activatedAbilities := #[equipAbility ({ symbols := #[.generic 3] })])

def theVision : CardDef :=
  card "The Vision" #[.artifact, .creature] ({ symbols := #[.generic 4] })
    (supertypes := #[.legendary])
    (subtypes := #["Robot", "Hero"])
    (oracleText := "Flying, vigilance\nWhenever you cast a noncreature spell, choose one that hasn't been chosen this turn —\n• Solar Beam — The Vision gains double strike until end of turn.\n• Density Control — The Vision gains indestructible until end of turn.\n• Technopathy — Draw a card.")
    (power := some 2)
    (toughness := some 5)
    (keywords := (Keyword.flying).merge Keyword.vigilance)
    (triggeredAbilities := #[.onCasting .visionModes])

def vivVisionTeenSynthezoid : CardDef :=
  card "Viv Vision, Teen Synthezoid" #[.artifact, .creature] ({ symbols := #[.generic 3] })
    (supertypes := #[.legendary])
    (subtypes := #["Robot", "Hero"])
    (oracleText := "Flying\nCybernetic Senses — Whenever Viv Vision attacks, draw a card if her power is 4 or greater.\nPower-up — {7}: Put two +1/+1 counters on Viv Vision. (Activate each power-up ability only once. Reduce the cost by her mana cost if she entered this turn.)")
    (power := some 2)
    (toughness := some 2)
    (keywords := Keyword.flying)
    (triggeredAbilities := #[.onThisAttack .drawIfPower4])
    (activatedAbilities := #[powerUpAbility (Effect.ofAbility (.putPlusOnePlusOneOnSource 2)) ({ symbols := #[.generic 7] })])

def aIMLabs : CardDef :=
  gainLifeDualLand "A.I.M. Labs"
    "This land enters tapped.\nWhen this land enters, you gain 1 life.\n{T}: Add {U} or {B}."
    #[.colored .blue, .colored .black]

def asgardianCitadel : CardDef :=
  gainLifeDualLand "Asgardian Citadel"
    "This land enters tapped.\nWhen this land enters, you gain 1 life.\n{T}: Add {R} or {W}."
    #[.colored .red, .colored .white]

def avengersHangar : CardDef :=
  gainLifeDualLand "Avengers Hangar"
    "This land enters tapped.\nWhen this land enters, you gain 1 life.\n{T}: Add {W} or {U}."
    #[.colored .white, .colored .blue]

def avengersTower : CardDef :=
  card "Avengers Tower" #[.land] (ManaCost.empty)
    (oracleText := "{T}: Add {C}.\n{T}: Add one mana of any color. Spend this mana only to cast a Hero spell or to activate an ability of a Hero source.\n{4}, {T}: Look at the top three cards of your library. You may reveal a Hero card from among them and put it into your hand. Put the rest on the bottom of your library in any order.")
    (tapAddMana := #[.colorless])
    (activatedAbilities := #[activated (Effect.ofAbility .addAnyColorSpendOnlyHero) (ManaCost.empty) (tap := true),
      activated (Effect.ofAbility (.lookAtTopRevealSubtype 3 "Hero")) ({ symbols := #[.generic 4] }) (tap := true)])

def baxterBuilding : CardDef :=
  card "Baxter Building" #[.land] (ManaCost.empty)
    (oracleText := "{T}: Add {C}.\n{4}, {T}: Add four mana in any combination of colors.\n{4}, {T}: Draw a card. Activate only if you control a creature with toughness 4 or greater.")
    (tapAddMana := #[.colorless])
    (activatedAbilities := #[activated (Effect.ofAbility .addFourAnyCombination) ({ symbols := #[.generic 4] }) (tap := true),
      activated (Effect.ofAbility (.draw 1)) ({ symbols := #[.generic 4] }) (tap := true)
        (onlyIfYouControlCreatureToughnessAtLeast := 4)])

def birninZanaPlaza : CardDef :=
  gainLifeDualLand "Birnin Zana Plaza"
    "This land enters tapped.\nWhen this land enters, you gain 1 life.\n{T}: Add {G} or {W}."
    #[.colored .green, .colored .white]

def castleDoom : CardDef :=
  card "Castle Doom" #[.land] (ManaCost.empty)
    (oracleText := "{T}: Add {C}.\n{T}: Add one mana of any color. Spend this mana only to cast an artifact spell.\n{3}, {T}, Sacrifice an artifact: Create a 3/3 colorless Robot Villain artifact creature token named Doombot. Activate only as a sorcery.")
    (tapAddMana := #[.colorless])
    (activatedAbilities := #[activated (Effect.ofAbility .addAnyColorSpendOnlyArtifactSpell) (ManaCost.empty) (tap := true),
      activated (Effect.ofAbility (.createTokens .doombot 1)) ({ symbols := #[.generic 3] }) (tap := true)
        (sacrificeArtifact := true) (onlyAsSorcery := true)])

def darkFortress : CardDef :=
  conditionalDualLand "Dark Fortress"
    "{T}: Add {C}.\n{T}: Add {B} or {R}. Activate only if this land entered this turn or if you control a basic land."
    #[.colored .black, .colored .red]

def fiskTower : CardDef :=
  gainLifeDualLand "Fisk Tower"
    "This land enters tapped.\nWhen this land enters, you gain 1 life.\n{T}: Add {W} or {B}."
    #[.colored .white, .colored .black]

def gatheringPlace : CardDef :=
  conditionalDualLand "Gathering Place"
    "{T}: Add {C}.\n{T}: Add {G} or {W}. Activate only if this land entered this turn or if you control a basic land."
    #[.colored .green, .colored .white]

def gleamingBastion : CardDef :=
  conditionalDualLand "Gleaming Bastion"
    "{T}: Add {C}.\n{T}: Add {W} or {U}. Activate only if this land entered this turn or if you control a basic land."
    #[.colored .white, .colored .blue]

def hellSKitchen : CardDef :=
  gainLifeDualLand "Hell's Kitchen"
    "This land enters tapped.\nWhen this land enters, you gain 1 life.\n{T}: Add {B} or {R}."
    #[.colored .black, .colored .red]

def hiddenLair : CardDef :=
  conditionalDualLand "Hidden Lair"
    "{T}: Add {C}.\n{T}: Add {U} or {B}. Activate only if this land entered this turn or if you control a basic land."
    #[.colored .blue, .colored .black]

def losDiablosMissileBase : CardDef :=
  gainLifeDualLand "Los Diablos Missile Base"
    "This land enters tapped.\nWhen this land enters, you gain 1 life.\n{T}: Add {R} or {G}."
    #[.colored .red, .colored .green]

def pymTechnologies : CardDef :=
  gainLifeDualLand "Pym Technologies"
    "This land enters tapped.\nWhen this land enters, you gain 1 life.\n{T}: Add {G} or {U}."
    #[.colored .green, .colored .blue]

def starkIndustries : CardDef :=
  gainLifeDualLand "Stark Industries"
    "This land enters tapped.\nWhen this land enters, you gain 1 life.\n{T}: Add {U} or {R}."
    #[.colored .blue, .colored .red]

def subterraneanCavern : CardDef :=
  gainLifeDualLand "Subterranean Cavern"
    "This land enters tapped.\nWhen this land enters, you gain 1 life.\n{T}: Add {B} or {G}."
    #[.colored .black, .colored .green]

def surveillanceRoom : CardDef :=
  card "Surveillance Room" #[.land] (ManaCost.empty)
    (oracleText := "When this land enters, surveil 1. (Look at the top card of your library. You may put it into your graveyard.)\n{T}: Add {C}.\n{1}, {T}: Add one mana of any color.")
    (tapAddMana := #[.colorless])
    (triggeredAbilities := #[.onEnterSurveil 1])
    (activatedAbilities := #[activated (Effect.ofAbility (.addAnyColor)) ({ symbols := #[.generic 1] }) (tap := true)])

def trainingCompound : CardDef :=
  conditionalDualLand "Training Compound"
    "{T}: Add {C}.\n{T}: Add {R} or {G}. Activate only if this land entered this turn or if you control a basic land."
    #[.colored .red, .colored .green]

def villainousHideout : CardDef :=
  card "Villainous Hideout" #[.land] (ManaCost.empty)
    (oracleText := "{T}: Add {C}.\n{T}: Add one mana of any color. Spend this mana only to cast a Villain spell or to activate an ability of a Villain source.\n{3}, {T}: Target Villain you control connives. Activate only as a sorcery. (Draw a card, then discard a card. If you discarded a nonland card, put a +1/+1 counter on that creature.)")
    (tapAddMana := #[.colorless])
    (activatedAbilities := #[activated (Effect.ofAbility .addAnyColorSpendOnlyVillain) (ManaCost.empty) (tap := true),
      activated (Effect.ofAbility (.targetSubtypeConnives "Villain")) ({ symbols := #[.generic 3] }) (tap := true) (onlyAsSorcery := true)])

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

#guard mshCards.size >= 281
#guard mshCards.all (fun c => c.name != "")

end Mtg.Engine.Catalog
