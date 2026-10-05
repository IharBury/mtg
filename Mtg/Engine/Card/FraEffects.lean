import Mtg.Engine.Card.OracleActivate

/-!
# Reality Fracture effects

Spell and ability effects first printed in Reality Fracture (FRA), each with
the Oracle wording the parser matches, and the candidate list the parser
reads them from.
-/

namespace Mtg.Engine


namespace Effect

/-- An FRA spell effect with its printed wording. -/
def fraSpell (kind : EffectTargetKind) (r : Resolution) (phrase : String)
    (castKind : SpellCastKind := .extraLand) (maxTargets : Nat := 0)
    (allowsZeroTargets := false) : Effect :=
  { targeting := .of kind, resolution := r, phrase, spellCastKind := castKind
    maxTargets, allowsZeroTargets }

def fraSpellOn (f : TargetFilter) (r : FraResolution) (phrase : String)
    (castKind : SpellCastKind := .extraLand) : Effect :=
  fraSpell (.filtered f) (.fra r) phrase castKind

def fraUntargeted (r : Resolution) (phrase : String)
    (castKind : SpellCastKind := .extraLand) : Effect :=
  fraSpell .none r phrase castKind

/-! ## White -/

def generousRevival : Effect :=
  fraSpellOn { noun := "target creature card with mana value 3 or less from your graveyard", zone := .yourGraveyard, types := #[.creature], mvAtMost := some 3 }
    (.returnFromGyToBattlefield 1)
    "Return target creature card with mana value 3 or less from your graveyard to the battlefield with an additional +1/+1 counter on it"
    (castKind := .draw)

def hexhavenBattalion : Effect :=
  fraUntargeted (.createTokens .cadet 3)
    "Create three 2/2 colorless Wizard Soldier creature tokens named Cadet"
    (castKind := .draw)

def kindredJudgment : Effect :=
  fraUntargeted (.fra .destroyAllNotChosenType)
    "Choose a creature type. Destroy all creatures that aren't of the chosen type"
    (castKind := .destroyCreature)

def loyalTutor : Effect :=
  fraUntargeted (.fra .searchPlaneswalkerToTop)
    "Search your library for a planeswalker card, reveal it, then shuffle and put that card on top"
    (castKind := .draw)

def predictivePreparations : Effect :=
  fraSpell (.filtered TargetFilter.creature) (.fra (.plusOneOnEachTarget 1))
    "Put a +1/+1 counter on each of one or two target creatures"
    (castKind := .pump) (maxTargets := 2)

def prophesiedEnd : Effect :=
  fraSpellOn TargetFilter.creature .destroyDrawIfNotAttacking
    "Destroy target creature. If it wasn't attacking, its controller draws a card"
    (castKind := .destroyCreature)

def refuteDestiny : Effect :=
  fraSpell (.filtered { TargetFilter.creatureOrPlaneswalker with
      noun := "target creature or planeswalker that's green or blue"
      colors := #[.green, .blue] })
    (.sequence [.fra .exile, .surveil 1])
    "Exile target creature or planeswalker that's green or blue. Surveil 1"
    (castKind := .destroyCreature)

def returnToTheLightRealms : Effect :=
  fraUntargeted (.fra .returnAllNonlandPermanentsFromGy)
    "Return all nonland permanent cards from your graveyard to the battlefield"
    (castKind := .draw)

def surgicalPrecisionDestroy : Effect :=
  fraSpell (.filtered { TargetFilter.creature with
      noun := "target creature with toughness 4 or greater", toughnessAtLeast := some 4 })
    (.sequence [.fra .destroy, .gainLife 1])
    "Destroy target creature with toughness 4 or greater. You gain 1 life"
    (castKind := .destroyCreature)

def drawAndGainLife (cards life : Nat) : Effect :=
  fraUntargeted (.fra (.drawAndGainLife cards life))
    s!"You draw {cardPhrase cards} and gain {life} life"
    (castKind := .draw)

def yourFateEndsHere : Effect :=
  fraSpell (.filtered { TargetFilter.creatureOrPlaneswalker with
      noun := "target creature or planeswalker with mana value 3 or greater"
      mvAtLeast := some 3 })
    (.sequence [.fra .destroy, .surveil 1])
    "Destroy target creature or planeswalker with mana value 3 or greater. Surveil 1"
    (castKind := .destroyCreature)

/-! ## Blue -/

def counterTargetSpell : Effect :=
  fraSpellOn TargetFilter.spell .counter "Counter target spell" (castKind := .counter)

def cruelCalculations : Effect :=
  fraSpell .player (.fra .drawMilledThisTurn)
    "Draw X cards, where X is the number of cards that were put into target player's graveyard from their library this turn"
    (castKind := .draw)

def icyReceptionCounter : Effect :=
  fraSpellOn { noun := "target creature or legendary spell", zone := .stack
               types := #[.creature], orLegendary := true }
    (.counterUnlessPays 3)
    "Counter target creature or legendary spell unless its controller pays {3}"
    (castKind := .counter)

def targetCreatureGets (p t : Int) : Effect :=
  fraSpell (.filtered TargetFilter.creature) (.onPermanent (.pump p t))
    s!"Target creature gets {signedStat p}/{signedStat t} until end of turn"
    (castKind := .pump)

def preciseRedaction : Effect :=
  fraSpellOn { noun := "target white or black spell", zone := .stack
               colors := #[.white, .black] }
    .counter "Counter target white or black spell" (castKind := .counter)

def sphinxsApproach : Effect :=
  fraUntargeted (.fra .sphinxsApproach)
    "Draw two cards. Then you may exile this spell and four cards named Sphinx's Approach from your graveyard. If you do, search your library for a Sphinx creature card, put it onto the battlefield, then shuffle"
    (castKind := .draw)

def unsummon : Effect :=
  fraSpellOn TargetFilter.creature .bounce "Return target creature to its owner's hand"
    (castKind := .destroyCreature)

def unwindHistory : Effect :=
  fraSpell (.filtered { TargetFilter.creature with
      noun := "target creature an opponent controls with mana value 3 or less"
      controller := .opponent, mvAtMost := some 3 })
    (.sequence [.fra .bounce, .surveil 1])
    "Return target creature an opponent controls with mana value 3 or less to its owner's hand. Surveil 1"
    (castKind := .destroyCreature)

def arcOfFortune : Effect :=
  fraUntargeted (.fra (.eachPlayerMayWheel 7))
    "Each player may discard their hand and draw seven cards"
    (castKind := .draw)

/-! ## Black -/

def castAwayDoubt : Effect :=
  fraUntargeted (.sequence [.draw 2, .fra (.damageEachPlayer 2)])
    "Draw two cards. This spell deals 2 damage to each player"
    (castKind := .draw)

def extendedAbsence : Effect :=
  fraSpell (.filtered TargetFilter.creatureOrPlaneswalker)
    (.sequence [.fra .exile, .fra (.damageEachOpponentGainLife 1)])
    "Exile target creature or planeswalker. This spell deals 1 damage to each opponent and you gain 1 life"
    (castKind := .destroyCreature)

def extrapolateTheImpossible : Effect :=
  fraUntargeted (.fra .extrapolate)
    "You may reveal exactly two cards you own with different names from outside the game. An opponent chooses one of them. You put that card into your hand"
    (castKind := .draw)

def overwriteTheMultiverse : Effect :=
  fraUntargeted (.fra .exileAllCreaturesEmpower)
    "Exile all creatures. Empower Jace X, where X is the number of creatures exiled this way"
    (castKind := .destroyCreature)

def rewriteRegrets : Effect :=
  fraSpellOn { noun := "target creature or planeswalker card with mana value 6 or less from your graveyard", zone := .yourGraveyard, types := #[.creature, .planeswalker], mvAtMost := some 6 }
    (.returnFromGyToBattlefield 0)
    "Return target creature or planeswalker card with mana value 6 or less from your graveyard to the battlefield"
    (castKind := .draw)

def riseDraw : Effect :=
  fraUntargeted (.fra .drawGreatestPowerLoseLife)
    "Draw cards equal to the greatest power among creatures you control. You lose life equal to the number of cards drawn this way"
    (castKind := .draw)

def destroyTargetCreatureOrPlaneswalker : Effect :=
  fraSpellOn TargetFilter.creatureOrPlaneswalker .destroy
    "Destroy target creature or planeswalker" (castKind := .destroyCreature)

def solveForDisappointment : Effect :=
  fraSpell .opponent (.fra (.revealHandDiscardNonland true))
    "Target opponent reveals their hand. You choose a nonland permanent card from it. That player discards that card"
    (castKind := .draw)

def terminalCriticism : Effect :=
  fraSpell (.filtered { TargetFilter.creatureOrPlaneswalker with
      noun := "target creature or planeswalker that's blue or red"
      colors := #[.blue, .red] })
    (.sequence [.fra .destroy, .gainLife 1])
    "Destroy target creature or planeswalker that's blue or red. You gain 1 life"
    (castKind := .destroyCreature)

def vraskasMercyDestroy : Effect :=
  fraSpell (.filtered TargetFilter.creatureOrPlaneswalker)
    (.sequence [.fra (.loseLife 2), .fra .destroy])
    "You lose 2 life. Destroy target creature or planeswalker"
    (castKind := .destroyCreature)

def vraskasMercyEmpower : Effect :=
  fraUntargeted (.sequence [.fra (.loseLife 2), .empowerJace 6])
    "You lose 2 life. Empower Jace 6"
    (castKind := .draw)

/-! ## Red -/

def artifistAcumen : Effect :=
  fraUntargeted (.sequence [.teamGain Keyword.firstStrike, .draw 1])
    "Creatures you control gain first strike until end of turn.\nDraw a card"
    (castKind := .pump)

def awakenTheInferno : Effect :=
  fraSpell (.multi #[TargetFilter.oppCreatureOrPlaneswalker,
      { TargetFilter.creatureYouControl with noun := "up to one target creature you control" }] #[1])
    (.fra (.damageThenPlusOneOnSecond 6))
    "This spell deals 6 damage to target creature or planeswalker an opponent controls. Put a +1/+1 counter on up to one target creature you control"
    (castKind := .creatureDamage)

def commandTheStage : Effect :=
  fraUntargeted (.fra .cadetThenPlusOneOtherWizardTokens)
    "Create a 2/2 colorless Wizard Soldier creature token named Cadet, then put a +1/+1 counter on each other Wizard token you control"
    (castKind := .draw)

def essenceBurn : Effect :=
  fraSpellOn { TargetFilter.creatureOrPlaneswalker with
      noun := "target black or green creature or planeswalker", colors := #[.black, .green] }
    (.damageExileIfDies 5)
    "This spell deals 5 damage to target black or green creature or planeswalker. If that permanent would die this turn, exile it instead"
    (castKind := .creatureDamage)

def fulminousForteSweep : Effect :=
  fraUntargeted (.fra (.damageEachOppCreatureAndPlaneswalker 1))
    "This spell deals 1 damage to each creature and planeswalker your opponents control"
    (castKind := .creatureDamage)

def damageToCreatureOrPlaneswalker (n : Nat) : Effect :=
  fraSpell (.filtered TargetFilter.creatureOrPlaneswalker) (.onPermanent (.dealDamage n))
    s!"This spell deals {n} damage to target creature or planeswalker"
    (castKind := .creatureDamage)

def moltenTide : Effect :=
  fraUntargeted (.fra .mountainsAddExtraRed)
    "Until end of turn, whenever you tap a Mountain for mana, add an additional {R}"
    (castKind := .draw)

/-! ## Green -/

def enroot : Effect :=
  fraUntargeted (.fra .searchLandToGraveyard)
    "Search your library for a land card, put it into your graveyard, then shuffle"
    (castKind := .draw)

def flourishingGrapple : Effect :=
  fraSpell (.multi #[{ TargetFilter.oppCreatureOrPlaneswalker with
        noun := "target creature or planeswalker an opponent controls that's red or white"
        colors := #[.red, .white] }, TargetFilter.creatureYouControl] #[])
    (.fra .loseAbilitiesThenFight)
    "Target creature or planeswalker an opponent controls that's red or white loses all abilities until end of turn. Target creature you control deals damage equal to its power to that permanent"
    (castKind := .fight)

def restoreWithEmpathy : Effect :=
  fraSpell (.filtered { noun := "target permanent card from your graveyard", zone := .yourGraveyard, permanentCard := true })
    (.sequence [.fra .returnFromGyToHand, .gainLife 4])
    "Return target permanent card from your graveyard to your hand. You gain 4 life"
    (castKind := .draw)

def somethingWorthSaving : Effect :=
  fraUntargeted (.fra (.millMayPutPermanentGainLife 4 1))
    "Mill four cards. You may put a permanent card from among them into your hand. You gain 1 life"
    (castKind := .draw)

def tethermagesAdvantage : Effect :=
  fraSpellOn TargetFilter.creature (.pumpGrantUntap 2 2 Keyword.reach)
    "Target creature gets +2/+2 and gains reach until end of turn. Untap it"
    (castKind := .pump)

/-! ## Multicolor -/

def creaturesYouControlGetUntilEot (p t : Int) : Effect :=
  fraUntargeted (.creaturesYouControlPump p t)
    s!"Creatures you control get {signedStat p}/{signedStat t} until end of turn"
    (castKind := .pump)

def chargeTheSanctumPump : Effect :=
  fraSpellOn TargetFilter.creature (.pumpGrantPlusOne 2 0 Keyword.firstStrike 1)
    "Target creature gets +2/+0 and gains first strike until end of turn. Put a +1/+1 counter on it"
    (castKind := .pump)

def clashOfElements : Effect :=
  fraSpellOn { noun := "target nonland permanent", nonland := true } .clashOfElements
    "Choose target nonland permanent. Its owner may put it on top of their library. If they do, this spell deals 2 damage to them. If they didn't put the card on top of their library, they put it on the bottom"
    (castKind := .destroyCreature)

def entrustTheSpark : Effect :=
  fraUntargeted (.fra .entrustTheSpark)
    "You may sacrifice a planeswalker. If you do, search your library for a planeswalker card, put it onto the battlefield, then shuffle"
    (castKind := .draw)

def drawThenEmpower (cards n : Nat) : Effect :=
  fraUntargeted (.sequence [.draw cards, .empowerJace n])
    s!"Draw {cardPhrase cards}. Empower Jace {n}"
    (castKind := .draw)

def bounceSpellOrCreature : Effect :=
  fraSpellOn { noun := "target spell or creature", zone := .spellOrCreature } .bounce
    "Return target spell or creature to its owner's hand"
    (castKind := .counter)

def damageToCreatureWithFlying (n : Nat) : Effect :=
  fraSpell (.filtered { TargetFilter.creature with
      noun := "target creature with flying", withFlying := true })
    (.onPermanent (.dealDamage n))
    s!"This spell deals {n} damage to target creature with flying"
    (castKind := .destroyFlying)

def plusOneThenGrant (n : Nat) (k : Keywords) (upToOne := false) : Effect :=
  let noun := if upToOne then "up to one target creature" else "target creature"
  fraSpell (.filtered { TargetFilter.creature with noun }) (.fra (.plusOneThenGrant n k))
    s!"Put {plusOnePlusOneCountersPhrase n} on {noun}. It gains {k.joinedAnd} until end of turn"
    (castKind := .pump) (allowsZeroTargets := upToOne)

def addColorless (n : Nat) : Effect :=
  fraUntargeted (.addMana (Array.replicate n .colorless))
    s!"Add {String.join (List.replicate n "{C}")}"
    (castKind := .draw)

def recursiveRecruitment : Effect :=
  fraUntargeted (.fra (.cadetsPlusOnePerThreeIfFromGy 2))
    "Create two 2/2 colorless Wizard Soldier creature tokens named Cadet. If this spell was cast from a graveyard, put a +1/+1 counter on each of them for every three cards in your graveyard"
    (castKind := .draw)

def targetCreatureGains (k : Keywords) (words : String := k.joinedAnd) : Effect :=
  fraSpell (.filtered TargetFilter.creature) (.onPermanent (.grantKeywords k))
    s!"Target creature gains {words} until end of turn"
    (castKind := .pump)

def cadetWithHaste : Effect :=
  fraUntargeted (.fra .cadetWithHaste)
    "Create a 2/2 colorless Wizard Soldier creature token named Cadet. It gains haste until end of turn"
    (castKind := .draw)

def stingingVitriol : Effect :=
  fraSpell .opponent (.fra (.damageThenRevealDiscardNonland 2))
    "This spell deals 2 damage to target opponent. That player reveals their hand. You choose a nonland card from it. They discard that card"
    (castKind := .burn)

def theorixCounter : Effect :=
  fraSpellOn { noun := "target noncreature spell", zone := .stack, noncreature := true }
    (.counterUnlessPays 2)
    "Counter target noncreature spell unless its controller pays {2}"
    (castKind := .counter)

def millThenDraw (m d : Nat) : Effect :=
  fraUntargeted (.fra (.millThenDraw m d))
    s!"Mill {englishNumber m} cards, then draw {cardPhrase d}"
    (castKind := .draw)

def twinnedVision : Effect :=
  fraUntargeted (.fra .drawOneOrTwoIfNotFromHand)
    "Draw a card. If this spell wasn't cast from your hand, draw two cards instead"
    (castKind := .draw)

def twistedFates : Effect :=
  fraSpell (.multi #[{ noun := "target nonland permanent", nonland := true },
      { noun := "target player", zone := .player }] #[])
    (.fra .destroyThenPlusOneEachOfPlayer)
    "Destroy target nonland permanent. Put a +1/+1 counter on each creature target player controls"
    (castKind := .destroyCreature)

def permanentYouControlGains (k : Keywords) : Effect :=
  fraSpell (.filtered { noun := "target permanent you control", controller := .you })
    (.onPermanent (.grantKeywords k))
    s!"Target permanent you control gains {k.joinedAnd} until end of turn"
    (castKind := .pump)

def vindictiveTriumph : Effect :=
  fraSpellOn TargetFilter.creatureOrPlaneswalker (.exileReturnBrieflyIfMvAtMost 3)
    "Exile target creature or planeswalker. If that permanent's mana value was 3 or less, return it to the battlefield tapped under your control. Exile it at the beginning of the next end step"
    (castKind := .destroyCreature)

def tamsResistance : Effect := plusOneThenGrant 1 Keyword.vigilance (upToOne := true)


/-! ## Modes of modal triggered abilities -/

def returnLegendaryCardToHand : Effect :=
  fraSpellOn { noun := "target legendary card from your graveyard", zone := .yourGraveyard, legendary := true }
    .returnFromGyToHand "Return target legendary card from your graveyard to your hand"

def plusOneVigilanceIndestructible : Effect :=
  fraSpell (.filtered TargetFilter.creature)
    (.fra (.plusOneThenGrant 1 (Keyword.vigilance.merge Keyword.indestructible)))
    "Put a +1/+1 counter on target creature. It gains vigilance and indestructible until end of turn"
    (castKind := .pump)

def fraTapTargetCreature : Effect :=
  fraSpell (.filtered TargetFilter.creature) (.onPermanent .tap) "Tap target creature"

def untapTargetCreature : Effect :=
  fraSpell (.filtered TargetFilter.creature) (.onPermanent .untap) "Untap target creature"

def drawThenDiscardOne : Effect :=
  fraUntargeted (.sequence [.draw 1, .discard 1]) "Draw a card, then discard a card"

def destroyNoncreatureNonland : Effect :=
  fraSpellOn { noun := "target noncreature, nonland permanent", noncreature := true, nonland := true }
    .destroy "Destroy target noncreature, nonland permanent"

def gainLifeMode (n : Nat) : Effect :=
  fraUntargeted (.gainLife n) s!"You gain {n} life"

def minusPowerPerGraveyard : Effect :=
  fraSpellOn TargetFilter.creature .minusPowerPerGraveyard
    "Target creature gets -X/-0 until end of turn, where X is the number of cards in your graveyard"

def surveilMode (n : Nat) : Effect :=
  fraUntargeted (.surveil n) s!"Surveil {n}"

def sourceDealsDamageToCreatureOrPlaneswalker (n : Nat) : Effect :=
  fraSpell (.filtered TargetFilter.creatureOrPlaneswalker) (.onPermanent (.dealDamage n))
    s!"This creature deals {n} damage to target creature or planeswalker"

def createCadetMode : Effect :=
  fraUntargeted (.createTokens .cadet 1)
    "Create a 2/2 colorless Wizard Soldier creature token named Cadet"

def drawMode : Effect := fraUntargeted (.draw 1) "Draw a card"

end Effect


namespace ActivatedAbility

/-- An FRA activated ability with its printed line. -/
def fra (printed : String) (effect : Effect) (cost : ActivationCost)
    (onlyAsSorcery := false) (onlyDuringYourTurn := false)
    (activateFromGraveyard := false) (activateFromHand := false) (exhaust := false)
    (cond : FraActivationCondition := .none) : ActivatedAbility :=
  { cost, effect, printed, onlyAsSorcery, onlyDuringYourTurn, activateFromGraveyard,
    activateFromHand, exhaust, fraCondition := cond }

end ActivatedAbility

namespace FraCandidates

/-- Shorthand for an FRA ability effect. -/
def ab (r : Resolution) (phrase : String) (kind : EffectTargetKind := .none)
    (allowsZeroTargets := false) (maxTargets := 0) : Effect :=
  { targeting := .of kind, resolution := r, phrase, allowsZeroTargets, maxTargets }

/-- FRA activated abilities the parser recognizes. -/
def activatedAbilities : Array ActivatedAbility :=
  let creatureF : EffectTargetKind := .filtered TargetFilter.creature
  #[
  ActivatedAbility.fra
    "{3}, Exile this card from your hand: Target land gains \"{T}: Add {C}{C}\" until this card is cast from exile. You may cast this card for as long as it remains exiled."
    (ab (.fra .emrakulGrantMana) "Target land gains \"{T}: Add {C}{C}\" until this card is cast from exile. You may cast this card for as long as it remains exiled"
      (.filtered { noun := "target land", types := #[.land] }))
    { mana := ManaCost.ofGeneric 3, fra := .exileSourceFromHand } (activateFromHand := true),
  ActivatedAbility.fra "{4}{W}: Creatures you control get +1/+1 until end of turn."
    (ab (.creaturesYouControlPump 1 1) "Creatures you control get +1/+1 until end of turn")
    { mana := ⟨#[.generic 4, .colored .white]⟩ },
  ActivatedAbility.fra "{3}{U}{U}, Exile this card from your graveyard: Draw two cards."
    (ab (.draw 2) "Draw two cards")
    { mana := ⟨#[.generic 3, .colored .blue, .colored .blue]⟩, exileSourceFromGraveyard := true }
    (activateFromGraveyard := true),
  ActivatedAbility.fra "{3}{U}: Surveil 1." (ab (.surveil 1) "Surveil 1")
    { mana := ⟨#[.generic 3, .colored .blue]⟩ },
  ActivatedAbility.fra "{U}, Sacrifice this creature: The next spell you cast this turn can't be countered."
    (ab (.fra .nextSpellCantBeCountered) "The next spell you cast this turn can't be countered")
    { mana := ⟨#[.colored .blue]⟩, sacrificeSource := true },
  ActivatedAbility.fra "{2}: This creature gets +1/-1 until end of turn."
    (ab (.onSource (.pump 1 (-1))) "This creature gets +1/-1 until end of turn")
    { mana := ManaCost.ofGeneric 2 },
  ActivatedAbility.fra "{3}{B}, Exile this card from your graveyard: Return another target creature card from your graveyard to your hand."
    (ab (.fra .returnFromGyToHand) "Return another target creature card from your graveyard to your hand"
      (.filtered { noun := "another target creature card from your graveyard", zone := .yourGraveyard
                   types := #[.creature], another := true }))
    { mana := ⟨#[.generic 3, .colored .black]⟩, exileSourceFromGraveyard := true }
    (activateFromGraveyard := true),
  ActivatedAbility.fra "{T}, Discard a card: Draw a card." (ab (.draw 1) "Draw a card")
    { tap := true, discardACard := true },
  ActivatedAbility.fra
    "{3}{R}: Exile target creature or planeswalker you control. Reveal cards from the top of your library until you reveal a creature or planeswalker card. Put that card onto the battlefield and the rest on the bottom of your library in a random order. Activate only as a sorcery."
    (ab (.fra .identityEcho) "Exile target creature or planeswalker you control"
      (.filtered { TargetFilter.creatureOrPlaneswalker with
        noun := "target creature or planeswalker you control", controller := .you }))
    { mana := ⟨#[.generic 3, .colored .red]⟩ } (onlyAsSorcery := true),
  ActivatedAbility.fra
    "Sacrifice this creature: Destroy target artifact or enchantment. If that permanent was a legendary enchantment, draw a card. Activate only as a sorcery."
    (ab (.fra .destroyDrawIfLegendaryEnchantment) "Destroy target artifact or enchantment"
      (.filtered { noun := "target artifact or enchantment", types := #[.artifact, .enchantment] }))
    { sacrificeSource := true } (onlyAsSorcery := true),
  ActivatedAbility.fra
    "{1}, Sacrifice another artifact: Put a +1/+1 counter on this creature. It gains your choice of trample, hexproof, or haste until end of turn."
    (ab (.fra (.plusOneThenChooseKeyword [0, 1, 2])) "Put a +1/+1 counter on this creature")
    { mana := ManaCost.ofGeneric 1, fra := .sacrificeAnotherArtifact },
  ActivatedAbility.fra "{4}{G}: Return this card from your graveyard to your hand."
    (ab .returnFromGraveyardToHand "Return this card from your graveyard to your hand")
    { mana := ⟨#[.generic 4, .colored .green]⟩ } (activateFromGraveyard := true),
  ActivatedAbility.fra "{3}{G}, Discard this card: Destroy target creature with flying."
    (ab (.fra .destroy) "Destroy target creature with flying"
      (.filtered { TargetFilter.creature with noun := "target creature with flying", withFlying := true }))
    { mana := ⟨#[.generic 3, .colored .green]⟩, discardSource := true } (activateFromHand := true),
  ActivatedAbility.fra "{6}{G}{G}: This creature gets +4/+4 and gains trample until end of turn."
    (ab (.onSource (.pumpAndTrample 4 4)) "This creature gets +4/+4 and gains trample until end of turn")
    { mana := ⟨#[.generic 6, .colored .green, .colored .green]⟩ },
  ActivatedAbility.fra
    "{6}: Create a Heartwood token. Then this creature gets +X/+0 until end of turn, where X is the number of artifacts you control."
    (ab (.fra .heartwoodThenPowerPerArtifact) "Create a Heartwood token")
    { mana := ManaCost.ofGeneric 6 },
  ActivatedAbility.fra "{2}{W/B}: Return this card from your graveyard to your hand."
    (ab .returnFromGraveyardToHand "Return this card from your graveyard to your hand")
    { mana := ⟨#[.generic 2, .hybrid .white .black]⟩ } (activateFromGraveyard := true),
  ActivatedAbility.fra "{4}{G}{W}: Target creature gains trample and lifelink until end of turn."
    (ab (.onPermanent (.grantKeywords (Keyword.trample.merge Keyword.lifelink)))
      "Target creature gains trample and lifelink until end of turn" creatureF)
    { mana := ⟨#[.generic 4, .colored .green, .colored .white]⟩ },
  ActivatedAbility.fra
    "{4}: Create a 2/2 colorless Wizard Soldier creature token named Cadet. Then creatures you control gain haste until end of turn."
    (ab (.fra .cadetThenTeamHaste) "Create a Cadet") { mana := ManaCost.ofGeneric 4 },
  ActivatedAbility.fra "{2}: Put target card from your graveyard on the bottom of your library."
    (ab (.fra .graveyardCardToLibraryBottom) "Put target card from your graveyard on the bottom of your library"
      (.filtered { noun := "target card from your graveyard", zone := .yourGraveyard }))
    { mana := ManaCost.ofGeneric 2 },
  ActivatedAbility.fra
    "{W}{U}: Return this card from your graveyard to the battlefield with a finality counter on it. Activate only if you've scried or surveilled this turn."
    (ab .returnFromGyWithFinality "Return this card from your graveyard to the battlefield with a finality counter on it")
    { mana := ⟨#[.colored .white, .colored .blue]⟩ } (activateFromGraveyard := true)
    (cond := .scriedOrSurveilledThisTurn),
  ActivatedAbility.fra "{1}, {T}, Discard a legendary card: Draw a card." (ab (.draw 1) "Draw a card")
    { mana := ManaCost.ofGeneric 1, tap := true, fra := .discardLegendaryCard },
  ActivatedAbility.fra "Tap two untapped artifacts you control: Put two +1/+1 counters on this creature."
    (ab (.onSource (.plusOne 2)) "Put two +1/+1 counters on this creature")
    { fra := .tapTwoUntappedArtifacts },
  { ActivatedAbility.fra
      "Equip {3}. This ability costs {1} less to activate for each +1/+1 counter on the creature it targets."
      Effect.attachToTargetCreatureYouControl { mana := ManaCost.ofGeneric 3 } (onlyAsSorcery := true)
    with costLessPerPlusOneOnTarget := true },
  ActivatedAbility.fra "{2}: This creature gains flying until end of turn."
    (ab (.onSource (.grantKeywords Keyword.flying)) "This creature gains flying until end of turn")
    { mana := ManaCost.ofGeneric 2 },
  ActivatedAbility.fra "{5}, {T}, Exile this artifact: Destroy all creatures. Activate only as a sorcery."
    (ab (.fra .destroyAllCreatures) "Destroy all creatures")
    { mana := ManaCost.ofGeneric 5, tap := true, fra := .exileSource } (onlyAsSorcery := true),
  ActivatedAbility.fra
    "{6}, Sacrifice this creature: Choose target creature or planeswalker an opponent controls. Its owner shuffles it into their library."
    (ab (.fra .ownerShufflesIntoLibrary) "Its owner shuffles it into their library"
      (.filtered TargetFilter.oppCreatureOrPlaneswalker))
    { mana := ManaCost.ofGeneric 6, sacrificeSource := true },
  ActivatedAbility.fra "{2}, {T}, Discard a card: Draw a card." (ab (.draw 1) "Draw a card")
    { mana := ManaCost.ofGeneric 2, tap := true, discardACard := true },
  ActivatedAbility.fra
    "{2}, {T}: Target creature that attacked this turn becomes prepared. Activate only as a sorcery."
    (ab (.onPermanent .becomePrepared) "Target creature that attacked this turn becomes prepared"
      (.filtered { TargetFilter.creature with noun := "target creature that attacked this turn", attackedThisTurn := true }))
    { mana := ManaCost.ofGeneric 2, tap := true } (onlyAsSorcery := true),
  ActivatedAbility.fra "{1}{W}, Discard this card: It deals 4 damage to target attacking or blocking creature."
    (ab (.onPermanent (.dealDamage 4)) "It deals 4 damage to target attacking or blocking creature"
      (.filtered { TargetFilter.creature with noun := "target attacking or blocking creature", attackingOrBlocking := true }))
    { mana := ⟨#[.generic 1, .colored .white]⟩, discardSource := true } (activateFromHand := true),
  ActivatedAbility.fra
    "{1}, {T}, Discard a card: Another target creature or planeswalker you control gains hexproof until end of turn."
    (ab (.onPermanent (.grantKeywords Keyword.hexproof)) "Another target creature or planeswalker you control gains hexproof until end of turn"
      (.filtered { TargetFilter.creatureOrPlaneswalker with
        noun := "another target creature or planeswalker you control", controller := .you, another := true }))
    { mana := ManaCost.ofGeneric 1, tap := true, discardACard := true },
  ActivatedAbility.fra "{T}: Return another target permanent you control to its owner's hand. Activate only during your turn."
    (ab (.fra .bounce) "Return another target permanent you control to its owner's hand"
      (.filtered { noun := "another target permanent you control", controller := .you, another := true }))
    { tap := true } (onlyDuringYourTurn := true),
  ActivatedAbility.fra "{T}: Target creature with a +1/+1 counter on it gains flying until end of turn."
    (ab (.onPermanent (.grantKeywords Keyword.flying)) "Target creature with a +1/+1 counter on it gains flying until end of turn"
      (.filtered { TargetFilter.creature with noun := "target creature with a +1/+1 counter on it", withPlusOneCounter := true }))
    { tap := true },
  ActivatedAbility.fra "{6}: Put a +1/+1 counter on target legendary creature."
    (ab (.onPermanent (.plusOne 1)) "Put a +1/+1 counter on target legendary creature"
      (.filtered { TargetFilter.creature with noun := "target legendary creature", legendary := true }))
    { mana := ManaCost.ofGeneric 6 },
  ActivatedAbility.fra "{6}: Put a +1/+1 counter on target nonlegendary creature."
    (ab (.onPermanent (.plusOne 1)) "Put a +1/+1 counter on target nonlegendary creature"
      (.filtered { TargetFilter.creature with noun := "target nonlegendary creature", nonlegendary := true }))
    { mana := ManaCost.ofGeneric 6 },
  ActivatedAbility.fra "{T}: Draw a card, then discard a card."
    (ab (.sequence [.draw 1, .discard 1]) "Draw a card, then discard a card") { tap := true },
  ActivatedAbility.fra "{2}{U}: Untap target creature."
    (ab (.onPermanent .untap) "Untap target creature" creatureF)
    { mana := ⟨#[.generic 2, .colored .blue]⟩ },
  ActivatedAbility.fra
    "{3}{U}{U}: Until end of turn, whenever this creature deals combat damage to a player, draw two cards."
    (ab (.fra .grantCombatDamageDrawTwo) "Until end of turn, whenever this creature deals combat damage to a player, draw two cards")
    { mana := ⟨#[.generic 3, .colored .blue, .colored .blue]⟩ },
  ActivatedAbility.fra
    "{4}{B}, Exile another creature card from your graveyard: Return this card from your graveyard to the battlefield tapped with a +1/+1 counter on her."
    (ab (.fra (.returnSourceFromGy false true 1)) "Return this card from your graveyard to the battlefield tapped")
    { mana := ⟨#[.generic 4, .colored .black]⟩, fra := .exileAnotherCreatureCardFromGraveyard }
    (activateFromGraveyard := true),
  ActivatedAbility.fra
    "{5}{B}: Return target creature or planeswalker card from your graveyard to the battlefield. Put a +1/+1 counter on this creature. Activate only as a sorcery."
    (ab (.fra .returnTargetThenPlusOneSource) "Return target creature or planeswalker card from your graveyard to the battlefield"
      (.filtered { noun := "target creature or planeswalker card from your graveyard", zone := .yourGraveyard
                   types := #[.creature, .planeswalker] }))
    { mana := ⟨#[.generic 5, .colored .black]⟩ } (onlyAsSorcery := true) (exhaust := true),
  ActivatedAbility.fra
    "Sacrifice another creature or planeswalker: This creature gets -2/-0 until end of turn. Activate only if there are seven or more cards in your graveyard."
    (ab (.onSource (.pump (-2) 0)) "This creature gets -2/-0 until end of turn")
    { fra := .sacrificeAnotherCreatureOrPlaneswalker } (cond := .graveyardAtLeast 7),
  ActivatedAbility.fra "{B}, Discard this card: Target creature gets -3/-1 until end of turn."
    (ab (.onPermanent (.pump (-3) (-1))) "Target creature gets -3/-1 until end of turn" creatureF)
    { mana := ⟨#[.colored .black]⟩, discardSource := true } (activateFromHand := true),
  ActivatedAbility.fra "{1}{R}, {T}: Put a +1/+1 counter on target creature that entered this turn."
    (ab (.onPermanent (.plusOne 1)) "Put a +1/+1 counter on target creature that entered this turn"
      (.filtered { TargetFilter.creature with noun := "target creature that entered this turn", enteredThisTurn := true }))
    { mana := ⟨#[.generic 1, .colored .red]⟩, tap := true },
  ActivatedAbility.fra "{8}: Create a 5/5 red Dragon creature token with flying."
    (ab (.createTokens .dragon55flying 1) "Create a 5/5 red Dragon creature token with flying")
    { mana := ManaCost.ofGeneric 8 },
  ActivatedAbility.fra "{2}, {T}, Sacrifice an artifact or land: Draw a card." (ab (.draw 1) "Draw a card")
    { mana := ManaCost.ofGeneric 2, tap := true, fra := .sacrificeArtifactOrLand },
  ActivatedAbility.fra
    "{5}{R}: Target creature gets +X/+0 until end of turn, where X is the number of artifacts you control."
    (ab (.fra .pumpPerArtifact) "Target creature gets +X/+0 until end of turn" creatureF)
    { mana := ⟨#[.generic 5, .colored .red]⟩ },
  ActivatedAbility.fra "{4}{G}: Put a +1/+1 counter on each creature you control with a +1/+1 counter on it."
    (ab (.fra .plusOneOnEachWithPlusOne) "Put a +1/+1 counter on each creature you control with a +1/+1 counter on it")
    { mana := ⟨#[.generic 4, .colored .green]⟩ },
  ActivatedAbility.fra "{2}: Return target land card from your graveyard to your hand."
    (ab (.fra .returnFromGyToHand) "Return target land card from your graveyard to your hand"
      (.filtered { noun := "target land card from your graveyard", zone := .yourGraveyard, types := #[.land] }))
    { mana := ManaCost.ofGeneric 2 },
  ActivatedAbility.fra
    "{2}, Sacrifice another creature or planeswalker: Put a +1/+1 counter on this creature. He gains menace until end of turn."
    (ab (.sequence [.onSource (.plusOne 1), .onSource (.grantKeywords Keyword.menace)]) "Put a +1/+1 counter on this creature")
    { mana := ManaCost.ofGeneric 2, fra := .sacrificeAnotherCreatureOrPlaneswalker }
  ]

/-- FRA loyalty abilities and abilities granted to planeswalkers, as effects
the parser reads after the loyalty cost. -/
def loyaltyEffects : Array Effect :=
  let perOpp (noun : String) (types : Array CardType) : EffectTargetKind :=
    .filtered { noun, types, controller := .eachOpponent }
  #[
  ab (.createTokens .illusion11blue 1) "Create a 1/1 blue Illusion creature token",
  ab (.fra .bounceEachTarget)
    "For each opponent, return up to one target artifact or creature that player controls to its owner's hand"
    (perOpp "up to one target artifact or creature that player controls" #[.artifact, .creature])
    (allowsZeroTargets := true),
  ab (.fra .drawThreeThenCountersPerHand)
    "Draw three cards. Then put X +1/+1 counters on each creature you control, where X is the number of cards in your hand",
  ab (.fra .surveilReturnNoncreatureNonland)
    "Surveil 1. If you put a noncreature, nonland card into your graveyard this way, put that card into your hand",
  ab (.fra .addBlueNoncreatureOnly) "Add {U}. Spend this mana only to cast a noncreature spell",
  ab (.fra .tapAndStunX) "Tap target artifact or creature. Put X stun counters on it"
    (.filtered { noun := "target artifact or creature", types := #[.artifact, .creature] }),
  ab (.fra .emblemDrawOnCast) "You get an emblem with \"Whenever you cast a spell, draw a card.\"",
  ab (.fra .empowerJacePerIsland) "Empower Jace X, where X is the number of Islands you control",
  ab (.fra .attackersGetMinusFiveUntilYourTurn)
    "Until your next turn, whenever a creature attacks you or a planeswalker you control, it gets -5/-0 until end of turn",
  ab (.fra .exileOpponentLibrariesButBottom) "Exile all but the bottom card of each opponent's library",
  ab (.fra .minusFourMinusOneUntilYourTurn) "Up to one target creature gets -4/-1 until your next turn"
    (.filtered { TargetFilter.creature with noun := "up to one target creature" }) (allowsZeroTargets := true),
  ab (.fra .eachPlayerSacrificesThenBeast)
    "Each player sacrifices a creature of their choice. If you sacrificed a creature this way, create a 4/4 green Beast creature token with trample",
  ab (.fra .eachOpponentDiscardsTwoDrawPerShort)
    "Each opponent discards two cards. For each opponent who didn't discard two nonland cards this way, you draw a card",
  ab (.fra .discardHandDrawPerCreature) "Discard your hand, then draw a card for each creature you control",
  ab (.fra (.damageEachCreatureExceptYourTokens 4)) "This deals 4 damage to each creature except for tokens you control",
  ab (.fra .emblemCreaturesGetTwoTwo) "You get an emblem with \"Creatures you control get +2/+2.\"",
  ab (.fra .untapTargets) "Untap up to two target lands"
    (.filtered { noun := "up to two target lands", types := #[.land] }) (allowsZeroTargets := true) (maxTargets := 2),
  ab (.fra .attackersGetTwoTwoTrampleUntilYourTurn)
    "Until your next turn, whenever one or more creatures attack one of your opponents, those creatures get +2/+2 and gain trample until end of turn",
  ab (.fra (.damageEachOpponentGainLife 1))
    "This planeswalker deals 1 damage to each opponent and you gain 1 life",
  ab (.fra .plusOnePerLand) "Put a +1/+1 counter on target creature for each land you control"
    (.filtered TargetFilter.creature),
  ab (.fra .maySacrificeCreatureForBeast)
    "You may sacrifice a creature. If you do, create a 4/4 green Beast creature token with trample",
  ab (.fra (.damageUpToOneAndPlayer 2))
    "This planeswalker deals 2 damage to up to one target creature or planeswalker and 2 damage to target player"
    (.multi #[{ TargetFilter.creatureOrPlaneswalker with noun := "up to one target creature or planeswalker" },
      { noun := "target player", zone := .player }] #[0]),
  ab (.createTokens .leviathan88hexproof 1) "Create an 8/8 blue Leviathan creature token with hexproof"
  ]


open TriggeredAbility in
/-- FRA triggered abilities the parser recognizes. -/
def triggeredAbilities : Array TriggeredAbility :=
  let anyTarget : EffectTargetKind := .playerOrCreature
  let perOpponent (noun : String) : EffectTargetKind :=
    .filtered { noun, types := #[.creature], controller := .eachOpponent }
  #[
  fra (.fra .castThis) "When you cast this spell, untap all lands you control."
    (.fra .untapAllLandsYouControl),
  fra .youCastCreature
    "Whenever you cast a creature spell, exile up to one other target creature you control, then return that card to the battlefield under its owner's control."
    (.fra .blink)
    (.filtered { noun := "up to one other target creature you control", types := #[.creature], controller := .you, another := true })
    (allowsZeroTargets := true),
  fra .yourBeginCombat
    "At the beginning of combat on your turn, you may remove a +1/+1 counter from this creature. If you do, put a +1/+1 counter on each other creature you control."
    (.fra .mayMovePlusOneToEachOther),
  fra .attack
    "Whenever this creature attacks, empower Jace X, where X is the number of creatures you control."
    (.fra .empowerJacePerCreature),
  fra .enter "When this Aura enters, tap enchanted creature. It becomes unprepared."
    (.fra .tapEnchantedUnprepare),
  fra .enter
    "When this enchantment enters, the owner of up to one other target nonland permanent puts it on their choice of the top or bottom of their library."
    (.fra .ownerPutsOnTopOrBottom)
    (.filtered { noun := "up to one other target nonland permanent", nonland := true, another := true })
    (allowsZeroTargets := true),
  fra .enter
    "When this creature enters, draw two cards, then discard two cards. When you discard one or more nonland cards this way, tap up to that many target creatures and put a stun counter on each of them."
    (.fra .drawTwoDiscardTwoStun),
  fra .attack "Whenever this creature attacks, draw a card, then discard a card."
    (.sequence [.draw 1, .discard 1]),
  fra .dies "When this creature dies, if it isn't a token, create a token that's a copy of it."
    (.fra .copyTokenOfSourceIfNotToken) (cond := .sourceNotToken),
  fra (.or .enter .dies) "When this creature enters or dies, you gain 2 life." (.gainLife 2),
  fra .enter "When this creature enters, mill three cards." (.millSelf 3),
  fra (.fra .yourBeginCombatFromGraveyard)
    "At the beginning of combat on your turn, if two or more creatures died this turn, return this card from your graveyard to the battlefield."
    (.fra (.returnSourceFromGy false false 0)) (cond := .twoCreaturesDiedThisTurn),
  fra .enter
    "When this Equipment enters, you may pay {2}. When you do, for each opponent, destroy up to one target creature or planeswalker that player controls."
    (.fra (.mayPayThenDestroyPerOpponent 2)),
  fra .enter "When this creature enters, target creature gets +2/+2 and gains deathtouch until end of turn."
    (.onPermanent (.pumpAndGrant 2 2 Keyword.deathtouch)) (.filtered TargetFilter.creature),
  fra .attack "Whenever this creature attacks, it deals 1 damage to each opponent and you gain 1 life."
    (.fra (.damageEachOpponentGainLife 1)),
  fra .enter "When this enchantment enters, it deals X damage to any target." (.fra .damageX) anyTarget,
  fra .youCastNoncreature "Whenever you cast a noncreature spell, put a +1/+1 counter on this creature."
    (.fra (.plusOneOnSource 1)),
  fra (.fra .eachUpkeepFromGraveyard)
    "At the beginning of each upkeep, if an opponent was dealt noncombat damage last turn, return this card from your graveyard to your hand."
    (.fra (.returnSourceFromGy true false 0)) (cond := .opponentDealtNoncombatDamageLastTurn),
  fra .enter
    "When this creature enters, creatures you control gain trample and get +X/+0 until end of turn, where X is the number of artifacts you control."
    (.fra .trampleAndPowerPerArtifact),
  fra .enter
    "When this creature enters, search your library for a card, put it into your hand, shuffle, then discard a card at random."
    (.fra .searchCardThenDiscardRandom),
  fra .enter "When this creature enters, create a 2/2 colorless Wizard Soldier creature token named Cadet."
    (.createTokens .cadet 1),
  fra (.fra .opponentsDealtNoncombatDamage)
    "Whenever one or more opponents are dealt noncombat damage, creatures you control get +1/+0 until end of turn."
    (.creaturesYouControlPump 1 0),
  fra .enter
    "When this creature enters, target instant or sorcery card in your graveyard gains flashback until end of turn. The flashback cost is equal to its mana cost."
    (.fra .grantFlashbackUntilEot)
    (.filtered { noun := "target instant or sorcery card in your graveyard", zone := .yourGraveyard, types := #[.instant, .sorcery] }),
  fra .enter "When this creature enters, you may discard a card. When you do, this creature deals 2 damage to any target."
    (.fra (.mayDiscardThenDamage 2)),
  fra .combatDamageToPlayer
    "Whenever this creature deals combat damage to a player, return target land card from your graveyard to your hand."
    (.fra .returnFromGyToHand)
    (.filtered { noun := "target land card from your graveyard", zone := .yourGraveyard, types := #[.land] }),
  fra .anotherCreatureYouControlEnters "Whenever another creature you control enters, you gain 1 life."
    (.gainLife 1),
  fra .sourceDealtDamage
    "Whenever this creature is dealt damage, you may search your library for up to that many land cards, put them onto the battlefield tapped, then shuffle."
    (.fra .maySearchLandsEqualDamage),
  fra .enter "When this creature enters, create a Heartwood token." (.createTokens .heartwood 1),
  fra (.fra .youPutLoyaltyCounters)
    "Whenever you put one or more loyalty counters on a planeswalker, put a +1/+1 counter on this creature."
    (.fra (.plusOneOnSource 1)),
  fra .enter
    "When this creature enters, you may search your library for a basic land card, put that card onto the battlefield tapped, then shuffle."
    (.fra .maySearchBasicLandTapped),
  fra .enter "When this creature enters, put three +1/+1 counters on target creature."
    (.onPermanent (.plusOne 3)) (.filtered TargetFilter.creature),
  fra (.or .enter .dies) "When this creature enters or dies, create a Heartwood token."
    (.createTokens .heartwood 1),
  fra .youGainLife "Whenever you gain life, draw a card. This ability triggers only once each turn."
    (.draw 1) (once := true),
  fra .youScryOrSurveil "Whenever you scry or surveil, put a +1/+1 counter on each creature you control."
    (.fra .plusOneOnEachCreatureYouControl),
  fra (.fra .enchantedDies)
    "When enchanted creature dies, return that card to the battlefield tapped under its owner's control."
    (.fra .returnCauseTapped),
  fra .eachEndStep "At the beginning of the end step, sacrifice this creature." (.fra .sacrificeSource),
  fra (.fra .creatureYouControlAttacks)
    "Whenever a creature you control attacks, that creature deals 1 damage to each opponent."
    (.fra (.causeDealsDamageToEachOpponent 1)),
  fra .youGainLife
    "Whenever you gain life, create a colorless artifact token named Lotus with \"{T}, Sacrifice this token: Add three mana of any one color.\" This ability triggers only once each turn."
    (.createTokens .lotus 1) (once := true),
  fra .enter "When this creature enters, it fights up to one target creature an opponent controls."
    (.fra .sourceFightsTarget)
    (.filtered { noun := "up to one target creature an opponent controls", types := #[.creature], controller := .opponent })
    (allowsZeroTargets := true),
  fra .enter
    "When this creature enters, if you cast it, target opponent reveals their hand. You choose a nonland card from it. Exile that card."
    (.fra .exileFromHandUntilLeaves) .opponent (cond := .sourceWasCast),
  fra .enter
    "When this creature enters, mill four cards. When you do, return target land card from your graveyard to the battlefield tapped."
    (.fra (.millThenReturnLandTapped 4)),
  fra (.fra .thisOrAnotherCreatureYouControlEnters)
    "Whenever this creature or another creature you control enters, surveil 1." (.surveil 1),
  fra (.fra (.opponentCastsSpellMvAtMost 2))
    "Whenever an opponent casts a spell with mana value 2 or less, you gain 2 life." (.gainLife 2),
  fra .enter
    "When this artifact enters, exile target nonland permanent an opponent controls with mana value 3 or less until this artifact leaves the battlefield."
    (.fra .exileUntilSourceLeaves)
    (.filtered { noun := "target nonland permanent an opponent controls with mana value 3 or less", nonland := true, controller := .opponent, mvAtMost := some 3 }),
  fra .enter
    "When this creature enters, you may sacrifice a land. If you do, create two tapped Heartwood tokens."
    (.fra .maySacrificeLandForHeartwoods),
  fra .enter
    "When this creature enters, if you cast him, exile up to one target nonland card of each card type from your graveyard. Copy those cards. You may cast any number of spells with total mana value 6 or less from among the copies without paying their mana costs."
    (.fra .uldarosCopies)
    (.filtered { noun := "up to one target nonland card of each card type from your graveyard"
                 zone := .yourGraveyard, nonland := true })
    (allowsZeroTargets := true) (maxTargets := 8) (cond := .sourceWasCast),
  fra .enter "When this Equipment enters, it deals 3 damage to any target and you gain 3 life."
    (.fra (.damageThenGainLife 3)) anyTarget,
  fra .attack "Whenever this creature attacks, exile up to one target card from a graveyard."
    (.fra .exileCardFromGraveyard)
    (.filtered { noun := "up to one target card from a graveyard", zone := .anyGraveyard })
    (allowsZeroTargets := true),
  fra (.fra .youCastPreparedSpell)
    "Whenever you cast a prepared spell, copy it. You may choose new targets for the copy."
    (.fra .copyCauseSpell),
  fra .enter "When this artifact enters, draw a card, then discard a card." (.sequence [.draw 1, .discard 1]),
  fra .yourUpkeep
    "At the beginning of your upkeep, surveil 1. Then if there are seven or more cards in your graveyard, sacrifice this artifact, it deals 2 damage to each opponent, and you gain 2 life."
    (.fra .eyeOfJace),
  fra (.fra .youCastEquipmentOrTargetingCreatureYouControl)
    "Whenever you cast an Equipment spell or a spell that targets a creature you control, draw a card. This ability triggers only once each turn."
    (.draw 1) (once := true),
  fra (.fra .anotherCreatureOrPlaneswalkerYouControlEnters)
    "Whenever another creature or planeswalker you control enters, you gain 1 life." (.gainLife 1),
  fra .youScryOrSurveil
    "Whenever you scry or surveil, create a 1/1 colorless Thopter artifact creature token with flying. This ability triggers only once each turn."
    (.createTokens .thopter 1) (once := true),
  fra .youGainLife "Whenever you gain life, put a loyalty counter on each planeswalker you control."
    (.fra .loyaltyOnEachPlaneswalkerYouControl),
  fra (.fra .creatureYouControlAttacksPlayerAlone)
    "Whenever a creature you control attacks a player alone, it gains double strike until end of turn."
    (.fra (.causeGains Keyword.doubleStrike)),
  fra (.fra .anotherNontokenCreatureYouControlEnters)
    "Whenever another nontoken creature you control enters, untap this creature." (.fra .untapSource),
  fra .enter
    "When this creature enters, for each opponent, tap up to one target creature that player controls. Put a stun counter on each of those creatures."
    (.fra .tapAndStunPerOpponent) (perOpponent "up to one target creature that player controls")
    (allowsZeroTargets := true),
  fra .eachEndStep
    "At the beginning of each end step, if you've drawn three or more cards this turn, create a 3/3 blue Angel creature token with flying."
    (.createTokens .angel33blue 1) (cond := .drewThreeThisTurn),
  fra (.fra .creatureOpponentControlsEnters)
    "Whenever a creature an opponent controls enters, this creature deals 1 damage to that player."
    (.fra (.damageCauseController 1)),
  fra (.fra .opponentActivatesLoyaltyAbility)
    "Whenever an opponent activates a loyalty ability, this creature deals 1 damage to that player."
    (.fra (.damageCauseController 1)),
  fra (.fra .anotherCreatureOrPlaneswalkerYouControlEnters)
    "Whenever another creature or planeswalker you control enters, mill two cards." (.millSelf 2),
  fra .enter "When this creature enters, remove up to three counters from another target creature or planeswalker."
    (.fra (.removeUpToCounters 3))
    (.filtered { TargetFilter.creatureOrPlaneswalker with noun := "another target creature or planeswalker", another := true }),
  fra (.fra .anotherCreatureOrPlaneswalkerYouControlDies)
    "Whenever another creature or planeswalker you control dies, this creature deals 1 damage to target opponent and you gain 1 life."
    (.fra (.damageTargetGainLife 1)) .opponent,
  fra (.fra .opponentDealtNoncombatDamage)
    "Whenever an opponent is dealt noncombat damage, put a +1/+1 counter on this creature."
    (.fra (.plusOneOnSource 1)),
  fra (.fra .playerDiscards)
    "Whenever a player discards one or more cards, this creature deals 1 damage to each opponent."
    (.fra (.damageEachOpponent 1)),
  fra .creatureYouControlDies
    "Whenever a creature you control dies, put a loyalty counter on each planeswalker you control."
    (.fra .loyaltyOnEachPlaneswalkerYouControl),
  fra .enter
    "When this creature enters, you may sacrifice a creature or planeswalker. When you do, each opponent sacrifices a creature of their choice."
    (.fra .maySacrificeThenEdict),
  fra .anotherCreatureYouControlEnters
    "Whenever another creature you control enters, this creature gets +X/+0 until end of turn, where X is that creature's power."
    (.fra .sourceGetsCausePower),
  fra (.fra .creatureYouControlAttacksPlayerAlone)
    "Whenever a creature you control attacks a player alone, discard a card, then draw a card. Then put a +1/+1 counter on that creature for each card you've discarded this turn."
    (.fra .jiangYangguAlone),
  fra .enter "When this creature enters, create a 5/5 red Dragon creature token with flying."
    (.createTokens .dragon55flying 1),
  fra .landYouControlEnters
    "Whenever a land you control enters, this creature deals 1 damage to each opponent. If that land is a Mountain, add {R}."
    (.fra .kothGeomancer),
  fra .enter "When this creature enters, create a 1/1 colorless Thopter artifact creature token with flying."
    (.createTokens .thopter 1),
  fra (.fra .opponentSmallCreatureBlocks)
    "Whenever a creature an opponent controls with power or toughness 1 or less blocks, this creature deals 1 damage to that creature's controller."
    (.fra (.damageCauseController 1)),
  fra .yourEndStep
    "At the beginning of your end step, if you didn't cast a spell this turn, put two +1/+1 counters on this creature."
    (.fra (.plusOneOnSource 2)) (cond := .castNoSpellThisTurn),
  fra .enter
    "When this creature enters, search your library for up to X basic land cards with different names, reveal them, put them into your hand, then shuffle."
    (.fra .fblthpSearch),
  fra (.fra (.creatureYouControlPowerAtLeastEnters 4))
    "Whenever a creature you control with power 4 or greater enters, draw a card." (.draw 1),
  fra .enter "When this creature enters, create Mowu, a legendary 3/3 green Dog creature token."
    (.createTokens .mowu 1),
  fra .yourEndStep "At the beginning of your end step, untap all tokens you control."
    (.fra .untapAllTokensYouControl),
  fra .enter
    "When this creature enters, you may discard a card. If you do, search your library for an enchantment card, reveal it, put it into your hand, then shuffle."
    (.fra .mayDiscardThenSearchEnchantment),
  fra (.fra .youDiscardThis) "When you discard this card, you gain 3 life." (.gainLife 3),
  fra .youActivateLoyaltyAbility
    "Whenever you activate a loyalty ability, you gain 1 life. You may play an additional land this turn."
    (.fra (.gainLifeAndExtraLand 1)),
  fra .enter
    "When this creature enters, another target creature you control fights up to one target creature an opponent controls."
    (.fra .firstFightsSecond)
    (.multi #[{ noun := "another target creature you control", types := #[.creature], controller := .you, another := true },
      { noun := "up to one target creature an opponent controls", types := #[.creature], controller := .opponent }] #[1]),
  fra (.fra .anotherCreatureOrPlaneswalkerYouControlDies)
    "Whenever another creature or planeswalker you control dies, you gain 1 life." (.gainLife 1),
  fra .enter
    "When this creature enters, for each opponent, put X -1/-1 counters on up to one target creature that player controls, where X is the greatest mana value among cards in your graveyard."
    (.fra .minusOnesPerOpponent) (perOpponent "up to one target creature that player controls")
    (allowsZeroTargets := true),
  fra .enter "When this creature enters, draw a card for each color among other artifacts you control."
    (.fra .drawPerColorAmongOtherArtifacts),
  fra .youAttack
    "Whenever you attack, if you've activated a loyalty ability this turn, untap target attacking creature. It can't be blocked this turn."
    (.fra .untapUnblockable)
    (.filtered { noun := "target attacking creature", types := #[.creature], attacking := true })
    (cond := .activatedLoyaltyThisTurn),
  fra (.fra .thisOrAnotherCreatureYouControlEnters)
    "Whenever this creature or another creature you control enters, put a +1/+1 counter on target creature that entered this turn."
    (.onPermanent (.plusOne 1))
    (.filtered { noun := "target creature that entered this turn", types := #[.creature], enteredThisTurn := true }),
  fra .youCastNoncreature
    "Whenever you cast a noncreature spell, create a 1/1 colorless Thopter artifact creature token with flying."
    (.createTokens .thopter 1),
  fra (.fra .youCastArtifactOrCreature) "Whenever you cast an artifact or creature spell, untap this creature."
    (.fra .untapSource)
  ]


/-- FRA spell effects the parser recognizes, including modes of modal spells. -/
def spellEffects : Array Effect := #[
  Effect.generousRevival,
  Effect.hexhavenBattalion,
  Effect.kindredJudgment,
  Effect.loyalTutor,
  Effect.predictivePreparations,
  Effect.prophesiedEnd,
  Effect.refuteDestiny,
  Effect.returnToTheLightRealms,
  Effect.surgicalPrecisionDestroy,
  Effect.drawAndGainLife 1 2,
  Effect.yourFateEndsHere,
  Effect.counterTargetSpell,
  Effect.cruelCalculations,
  Effect.icyReceptionCounter,
  Effect.targetCreatureGets (-5) 0,
  Effect.preciseRedaction,
  Effect.sphinxsApproach,
  Effect.unsummon,
  Effect.unwindHistory,
  Effect.arcOfFortune,
  Effect.castAwayDoubt,
  Effect.extendedAbsence,
  Effect.extrapolateTheImpossible,
  Effect.overwriteTheMultiverse,
  Effect.rewriteRegrets,
  Effect.riseDraw,
  Effect.allCreaturesGet (-3) (-3),
  Effect.destroyTargetCreatureOrPlaneswalker,
  Effect.solveForDisappointment,
  Effect.terminalCriticism,
  Effect.vraskasMercyDestroy,
  Effect.vraskasMercyEmpower,
  Effect.artifistAcumen,
  Effect.awakenTheInferno,
  Effect.commandTheStage,
  Effect.essenceBurn,
  Effect.fulminousForteSweep,
  Effect.damageToCreatureOrPlaneswalker 5,
  Effect.moltenTide,
  Effect.enroot,
  Effect.flourishingGrapple,
  Effect.restoreWithEmpathy,
  Effect.somethingWorthSaving,
  Effect.tethermagesAdvantage,
  Effect.creaturesYouControlGetUntilEot 2 0,
  Effect.chargeTheSanctumPump,
  Effect.clashOfElements,
  Effect.entrustTheSpark,
  Effect.drawThenEmpower 1 2,
  Effect.bounceSpellOrCreature,
  Effect.damageToCreatureWithFlying 6,
  Effect.plusOneThenGrant 2 Keyword.trample,
  Effect.addColorless 3,
  Effect.recursiveRecruitment,
  Effect.targetCreatureGains (Keyword.firstStrike.merge Keyword.deathtouch)
    "first strike and deathtouch",
  Effect.cadetWithHaste,
  Effect.stingingVitriol,
  Effect.theorixCounter,
  Effect.millThenDraw 3 1,
  Effect.twinnedVision,
  Effect.twistedFates,
  Effect.permanentYouControlGains (Keyword.hexproof.merge Keyword.indestructible),
  Effect.drawAndGainLife 1 3,
  Effect.vindictiveTriumph,
  Effect.tamsResistance,
  Effect.returnLegendaryCardToHand,
  Effect.plusOneVigilanceIndestructible,
  Effect.fraTapTargetCreature,
  Effect.untapTargetCreature,
  Effect.drawThenDiscardOne,
  Effect.destroyNoncreatureNonland,
  Effect.gainLifeMode 4,
  Effect.minusPowerPerGraveyard,
  Effect.surveilMode 2,
  Effect.sourceDealsDamageToCreatureOrPlaneswalker 4,
  Effect.createCadetMode,
  Effect.drawMode
] ++ loyaltyEffects

end FraCandidates

end Mtg.Engine
