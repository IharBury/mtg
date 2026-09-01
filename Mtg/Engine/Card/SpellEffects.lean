import Mtg.Engine.Card.Effect

/-!
# Spell and activated-ability effect constructors

`Effect.mkSpell` / `Effect.mkAbility` plus the named constructors for every
printed spell and activated-ability effect the engine models.
-/

namespace Mtg.Engine

namespace Effect

/-- Build a spell-shaped `Effect` from targeting and resolution.
Phrase comes from `SpellResolution.toPhrase` unless overridden. -/
def mkSpell (targeting : EffectTargeting) (resolution : SpellResolution)
    (castKind : SpellCastKind := .extraLand)
    (preferAsDefaultMode := false)
    (maxTargets := 0)
    (allowsZeroTargets := false)
    (phraseOverride : Option String := none) : Effect :=
  { targeting
    allowsZeroTargets
    maxTargets
    spellCastKind := castKind
    preferAsDefaultMode
    resolution := Resolution.ofSpell resolution
    phrase := phraseOverride.getD (SpellResolution.toPhrase resolution targeting.kind.noun) }

/-- Build an activated-ability `Effect` from targeting and resolution.
Phrase comes from `AbilityResolution.toPhrase` unless overridden. -/
def mkAbility (targeting : EffectTargeting) (resolution : AbilityResolution)
    (castKind : AbilityCastKind := .other)
    (allowsZeroTargets := false)
    (phraseOverride : Option String := none) : Effect :=
  { targeting
    allowsZeroTargets
    abilityCastKind := castKind
    resolution := Resolution.ofAbility resolution
    phrase := phraseOverride.getD (AbilityResolution.toPhrase resolution targeting.kind.noun) }

/-- Printed leftover constructors as unified `Effect` values.
Call sites should use these instead of leftover inductives. -/

def dealDamage (amount : Nat) : Effect :=
  mkSpell (.of .playerOrCreature) (.onPermanent (.dealDamage amount))
    (castKind := .burn)

def pump (power toughness : Int) : Effect :=
  mkSpell (.of .creature .own) (.onPermanent (.pump power toughness))
    (castKind := .pump)

def destroyCreatureWithFlying : Effect :=
  mkSpell (.of .creatureWithFlying) (.onPermanent .destroy)
    (castKind := .destroyFlying)
    (preferAsDefaultMode := true)

def destroyCreature : Effect :=
  mkSpell (.of .creature) (.onPermanent .destroy)
    (castKind := .destroyCreature)

def plusOnePlusOneTrampleHexproof : Effect :=
  mkSpell (.of .creatureYouControl) (.onPermanent .plusOnePlusOneTrampleHexproof)
    (castKind := .pump)

def dealDamageToCreature (amount : Nat) : Effect :=
  mkSpell (.of .creature) (.onPermanent (.dealDamage amount))
    (castKind := .creatureDamage)

def dealDamageLoseIndestructibleExile (amount : Nat) : Effect :=
  mkSpell (.of .creature) (.onPermanent (.dealDamageLoseIndestructibleExile amount))
    (castKind := .creatureDamage)

def creatureYouControlDealsPowerToOppCreature : Effect :=
  mkSpell (.of .creatureYouControlThenOppCreature) (.fight)
    (castKind := .fight)

def playAdditionalLandThisTurn : Effect :=
  mkSpell (.of .none) (.extraLand)
    (castKind := .extraLand)

def destroyArtifactOrLandNonflyersCantBlock : Effect :=
  mkSpell (.of .artifactOrLand) (.onPermanent .destroyThenNonflyersCantBlock)
    (castKind := .destroyArtifactOrLand)

def destroyTargetCreatureControllerLosesLife (life : Nat) : Effect :=
  mkSpell (.of .creature) (.destroyAndControllerLosesLife life)
    (castKind := .destroyCreature)
    (preferAsDefaultMode := true)

def allCreaturesGet (power toughness : Int) : Effect :=
  mkSpell (.of .none) (.allCreaturesPump power toughness)
    (castKind := .massPump)

def drawAndLoseLife (cards life : Nat) : Effect :=
  mkSpell (.of .none) (.drawAndLoseLife cards life)
    (castKind := .draw)

def targetPlayerDrawLoseLife (cards life : Nat) : Effect :=
  mkSpell (.of .player .selfPlayer) (.playerDrawLoseLife cards life)
    (castKind := .draw)

def creaturesTargetPlayerGet (power toughness : Int) : Effect :=
  mkSpell (.of .player) (.creaturesOfPlayerPump power toughness)
    (castKind := .massPump)

def pumpAndLifelink (power toughness : Int) : Effect :=
  mkSpell (.of .creature .own) (.onPermanent (.pumpAndLifelink power toughness))
    (castKind := .pump)

def pumpAndExileIfDies (power toughness : Int) : Effect :=
  mkSpell (.of .creature) (.onPermanent (.pumpAndExileIfDies power toughness))
    (castKind := .pump)
    (preferAsDefaultMode := true)

def exileGraveyardCreaturesGrantCast : Effect :=
  mkSpell (.of .player) (.exileGraveyardCreaturesGrantCast)
    (castKind := .draw)

def draw (n : Nat) : Effect :=
  mkSpell (.of .none) (.draw n)
    (castKind := .draw)

def drawThenDiscard (n : Nat) : Effect :=
  mkSpell (.of .none) (.drawThenDiscard n)
    (castKind := .draw)

def scry (n : Nat) : Effect :=
  mkSpell (.of .none) (.scry n)
    (castKind := .draw)

def tapScryDraw (scryN drawN : Nat) : Effect :=
  mkSpell (.of .creature) (.tapScryDraw scryN drawN)
    (castKind := .draw)

def tapOneOrTwoCreatures : Effect :=
  mkSpell (.of .creature) (.tapTargets)
    (castKind := .pump)
    (maxTargets := 2)

def grantHexproofIndestructible : Effect :=
  mkSpell (.of .artifactOrCreatureYouControl) (.onPermanent (.grantKeywords (Keyword.hexproof.merge Keyword.indestructible)))
    (castKind := .pump)

def plusOneUpToOneAndPlayerGainsLife (life : Nat) : Effect :=
  mkSpell (.of .upToOneCreatureThenPlayer) (.plusOneAndPlayerGainsLife life)
    (castKind := .pump)

def counterSpell : Effect :=
  mkSpell (.of .spell) (.counter)
    (castKind := .counter)

def counterUnlessPays (n : Nat) : Effect :=
  mkSpell (.of .spell) (.counterUnlessPays n)
    (castKind := .counter)

def counterCreatureSpellPTAtMost (n : Nat) : Effect :=
  mkSpell (.of (.creatureSpellPTAtMost n)) (.counter)
    (castKind := .counter)

def counterExilePermanentMayCast : Effect :=
  mkSpell (.of .spell) (.counterExilePermanentMayCast)
    (castKind := .counter)

def putOnTopOrBottom : Effect :=
  mkSpell (.of .creature) (.putOnTopOrBottom)
    (castKind := .counter)

def untapPumpMaybeAttach (power toughness : Int) : Effect :=
  mkSpell (.of .creatureYouControl) (.untapPumpMaybeAttach power toughness)
    (castKind := .pump)

def exchangeControlSharingType : Effect :=
  mkSpell (.of .twoNonlandsSharingType) (.exchangeControl)
    (castKind := .counter)

def returnSpellDraw : Effect :=
  mkSpell (.of .spell) (.returnSpellDraw)
    (castKind := .counter)

def creaturesYouControlGet (power toughness : Int) : Effect :=
  mkSpell (.of .none) (.creaturesYouControlPump power toughness)
    (castKind := .massPump)

def destroyArtifactOrEnchantmentGainLife (life : Nat) : Effect :=
  mkSpell (.of .artifactOrEnchantment) (.destroyArtifactOrEnchantmentGainLife life)
    (castKind := .destroyArtifactOrLand)

def destroyCreaturePowerAtLeast (n : Int) : Effect :=
  mkSpell (.of (.creaturePowerAtLeast n)) (.onPermanent .destroy)
    (castKind := .destroyCreature)
    (preferAsDefaultMode := true)

def becomeArtifactGainIndestructible : Effect :=
  mkSpell (.of .creature) (.onPermanent .becomeArtifactIndestructible)
    (castKind := .pump)

def pumpAndGrantKeywords (power toughness : Int) (k : Keywords) : Effect :=
  mkSpell (.of .creature .own) (.onPermanent (.pumpAndGrant power toughness k))
    (castKind := .pump)

def amassGoblins (n : Nat) : Effect :=
  mkSpell (.of .none) (.amassGoblins n)
    (castKind := .pump)

def drawLoseLifeThenAmass (n : Nat) : Effect :=
  mkSpell (.of .none) (.drawLoseLifeThenAmass n)
    (castKind := .draw)

def returnCreatureFromGyThenAmass (n : Nat) : Effect :=
  mkSpell (.of .creatureCardInYourGraveyard) (.returnCreatureFromGyThenAmass n)
    (castKind := .draw)
    (allowsZeroTargets := true)

def counterThenRecruitIfMvAtMost (n : Nat) : Effect :=
  mkSpell (.of .spell) (.counterThenRecruitIfMvAtMost n)
    (castKind := .counter)

def plusOneThenFight (n : Nat) : Effect :=
  mkSpell (.of .creatureYouControlThenOppCreature) (.plusOneThenFight n)
    (castKind := .fight)

def plusOneThenEachOtherIfFromGy : Effect :=
  mkSpell (.of .creatureYouControl) (.plusOneThenEachOtherIfFromGy)
    (castKind := .pump)

def drawIfFromGy (n fromGy : Nat) : Effect :=
  mkSpell (.of .none) (.drawIfFromGy n fromGy)
    (castKind := .draw)

def amassGoblinsOrFromGy (n fromGy : Nat) : Effect :=
  mkSpell (.of .none) (.amassGoblinsOrFromGy n fromGy)
    (castKind := .pump)

def searchLegendaryCreatureToHand : Effect :=
  mkSpell (.of .none) (.searchLegendaryCreatureToHand)
    (castKind := .draw)

def dealDamageToEachOppCreature (n : Nat) : Effect :=
  mkSpell (.of .none) (.dealDamageToEachOppCreature n)
    (castKind := .creatureDamage)

def destroyTargetArtifact : Effect :=
  mkSpell (.of .artifact) (.onPermanent .destroy)
    (castKind := .destroyArtifactOrLand)

def targetPlayerDraw (n : Nat) : Effect :=
  mkSpell (.of .player .selfPlayer) (.targetPlayerDraw n)
    (castKind := .draw)

def dealDamageToCreatureExileIfDies (n : Nat) : Effect :=
  mkSpell (.of .creature) (.dealDamageToCreatureExileIfDies n)
    (castKind := .creatureDamage)

def destroyArtifactToken : Effect :=
  mkSpell (.of .artifactToken) (.onPermanent .destroy)
    (castKind := .destroyArtifactOrLand)

def addRedPerOppArtifacts : Effect :=
  mkSpell (.of .none) (.addRedPerOppArtifacts)
    (castKind := .draw)

def dealDamageToEachNonDragon (n : Nat) : Effect :=
  mkSpell (.of .none) (.dealDamageToEachNonDragon n)
    (castKind := .creatureDamage)

def chooseTypeReturnOthers : Effect :=
  mkSpell (.of .none) (.chooseTypeReturnOthers)
    (castKind := .counter)

def drawEqualToughnessThenPutCreatures : Effect :=
  mkSpell (.of .none) (.drawEqualToughnessThenPutCreatures)
    (castKind := .draw)

def millThenPutInstantOrSorcery (n : Nat) : Effect :=
  mkSpell (.of .none) (.millThenPutInstantOrSorcery n)
    (castKind := .draw)

def millThenPutLands (n max : Nat) : Effect :=
  mkSpell (.of .none) (.millThenPutLands n max)
    (castKind := .draw)

def exileThenReturnYouControl : Effect :=
  mkSpell (.of .twoCreaturesOrLandsYouControl) (.exileThenReturnYouControl)
    (castKind := .counter)

def dealDamageToEachNonDragonThenAddDragonMana (n : Nat) : Effect :=
  mkSpell (.of .none) (.dealDamageToEachNonDragonThenAddDragonMana n)
    (castKind := .creatureDamage)

def millThenPutAllInstantsOrSorceries (n : Nat) : Effect :=
  mkSpell (.of .none) (.millThenPutAllInstantsOrSorceries n)
    (castKind := .draw)

def exileAttackersSearchBasics : Effect :=
  mkSpell (.of .player) (.exileAttackersSearchBasics)
    (castKind := .destroyCreature)

def createTokensX (kind : TokenKind) : Effect :=
  mkSpell (.of .none) (.createTokensX kind)
    (castKind := .extraLand)

def exileTopPlayIfYouControlSubtype (n : Nat) (subtype : String) : Effect :=
  mkSpell (.of .none) (.exileTopPlayIfYouControlSubtype n subtype)
    (castKind := .draw)

def returnSpellCantCastIfGift : Effect :=
  mkSpell (.of .spell) (.returnSpellCantCastIfGift)
    (castKind := .counter)

def exileTopXOppPlayForLife : Effect :=
  mkSpell (.of .opponent) (.exileTopXOppPlayForLife)
    (castKind := .draw)

def riddlesInTheDark : Effect :=
  mkSpell (.of .none) (.riddlesInTheDark)
    (castKind := .draw)

def supperForSpiders : Effect :=
  mkSpell (.of .none) (.supperForSpiders)
    (castKind := .draw)

def eaglesAreComing : Effect :=
  mkSpell (.of .creatureYouControl) (.eaglesAreComing)
    (castKind := .draw)

def lookAtTopLandsGainLife (n life : Nat) : Effect :=
  mkSpell (.of .none) (.lookAtTopLandsGainLife n life)
    (castKind := .draw)

def gainControlOppArtifacts : Effect :=
  mkSpell (.of .artifact) (.gainControlOppArtifacts)
    (castKind := .counter)
    (allowsZeroTargets := true)

def damageOppCreaturesEqualOtherSpellsMv : Effect :=
  mkSpell (.of .none) (.damageOppCreaturesEqualOtherSpellsMv)
    (castKind := .creatureDamage)

def phaseOutKicker : Effect :=
  mkSpell (.of .creature) (.phaseOutKicker)
    (castKind := .counter)

def dealDamageToAttackerOrBlocker (n teamworkN : Nat) : Effect :=
  mkSpell (.of .attackingOrBlockingCreature) (.dealDamageTeamwork n teamworkN)
    (castKind := .creatureDamage)

def dealDamageThenControllerIfTeamwork (n extra : Nat) : Effect :=
  mkSpell (.of .creature) (.dealDamageThenControllerIfTeamwork n extra)
    (castKind := .creatureDamage)

def grantDoubleStrikeTeamworkTrample : Effect :=
  mkSpell (.of .creature) (.grantDoubleStrikeTeamworkTrample)
    (castKind := .pump)

def counterUnlessPaysTeamwork (n teamworkN : Nat) : Effect :=
  mkSpell (.of .spell) (.counterUnlessPaysTeamwork n teamworkN)
    (castKind := .counter)

def exileCreatureMvAtMostOrAnyIfTeamwork (n life : Nat) : Effect :=
  mkSpell (.of (.creatureMvAtMost n)) (.exileCreatureMvAtMostOrAnyIfTeamwork n life)
    (castKind := .destroyCreature)

def returnGyCreatureMvAtMostOrAny (n : Nat) : Effect :=
  mkSpell (.of (.creatureCardInYourGraveyardMvAtMost n)) (.returnGyCreatureMvAtMostOrAny n)
    (castKind := .draw)

def revealTopPutCreatures (n : Nat) : Effect :=
  mkSpell (.of .none) (.revealTopPutCreatures n)
    (castKind := .extraLand)

def createTokens (kind : TokenKind) (n : Nat) : Effect :=
  mkSpell (.of .none) (.createTokens kind n)
    (castKind := .extraLand)

def exileCreatureToughnessAtLeast (n : Int) : Effect :=
  mkSpell (.of (.creatureToughnessAtLeast n)) (.exileTarget)
    (castKind := .destroyCreature)

def exileEnchantmentMvAtLeast (n : Nat) : Effect :=
  mkSpell (.of (.enchantmentMvAtLeast n)) (.exileTarget)
    (castKind := .destroyArtifactOrLand)

def returnOneOrTwoNonlands : Effect :=
  mkSpell (.of .nonland) (.returnOneOrTwoNonlands)
    (castKind := .counter)
    (maxTargets := 2)

def grantDeathtouch : Effect :=
  mkSpell (.of .creature) (.onPermanent (.grantKeywords Keyword.deathtouch))
    (castKind := .pump)

def destroyNoncreatureArtifact : Effect :=
  mkSpell (.of .noncreatureArtifact) (.onPermanent .destroy)
    (castKind := .destroyArtifactOrLand)

def plusOneOnCreature : Effect :=
  mkSpell (.of .creature) (.onPermanent (.plusOne 1))
    (castKind := .pump)

def targetPlayerCreatesTokens (kind : TokenKind) (n : Nat) : Effect :=
  mkSpell (.of .player) (.targetPlayerCreatesTokens kind n)
    (castKind := .extraLand)

def destroyCreatureSurveil : Effect :=
  mkSpell (.of .creature) (.destroyCreatureSurveil)
    (castKind := .destroyCreature)

def investigatePumpFlyingUntap : Effect :=
  mkSpell (.of .playerOrCreature) (.investigatePumpFlyingUntap)
    (castKind := .pump)

def plusOneLifelinkIndestructible : Effect :=
  mkSpell (.of .creature) (.plusOneLifelinkIndestructible)
    (castKind := .pump)

def dealDamageToEachCreature (n : Nat) : Effect :=
  mkSpell (.of .none) (.dealDamageToEachCreature n)
    (castKind := .creatureDamage)

def destroyLandSearchBasic : Effect :=
  mkSpell (.of .artifactOrLand) (.destroyLandSearchBasic)
    (castKind := .destroyArtifactOrLand)

def doublePowerAndToughness : Effect :=
  mkSpell (.of .creature) (.doublePowerAndToughness)
    (castKind := .pump)

def returnGySubtypeToHand (subtype : String) : Effect :=
  mkSpell (.of .creatureCardInYourGraveyard) (.returnGySubtypeToHand subtype)
    (castKind := .draw)

def grantVigilanceUnblockable : Effect :=
  mkSpell (.of .creature) (.grantVigilanceUnblockable)
    (castKind := .pump)

def becomeArtifactCreature44Flying : Effect :=
  mkSpell (.of .artifactOrCreatureYouControl) (.becomeArtifactCreature44Flying)
    (castKind := .pump)

def drawThreeDiscardUnlessArtifact : Effect :=
  mkSpell (.of .none) (.drawThreeDiscardUnlessArtifact)
    (castKind := .draw)

def eachOpponentLosesLife (n : Nat) : Effect :=
  mkSpell (.of .none) (.eachOpponentLosesLife n)
    (castKind := .burn)

def fight : Effect :=
  mkSpell (.of .creatureYouControlThenOppCreature) (.fight)
    (castKind := .fight)
    (phraseOverride := some "target creature you control fights target creature an opponent controls")

def fightUpToOne : Effect :=
  mkSpell (.of .creatureYouControlThenOppCreature) (.fightUpToOne)
    (castKind := .fight)
    (allowsZeroTargets := true)

def plusOneOnEachYouControl : Effect :=
  mkSpell (.of .none) (.plusOneOnEachYouControl)
    (castKind := .pump)

def plusOneOnCreatureN (n : Nat) : Effect :=
  mkSpell (.of .creatureYouControl) (.plusOneOnCreatureN n)
    (castKind := .pump)

def pumpThenDraw (power toughness : Int) : Effect :=
  mkSpell (.of .creature) (.pumpThenDraw power toughness)
    (castKind := .pump)

def pumpThenExileTopPlay (power toughness : Int) : Effect :=
  mkSpell (.of .creature) (.pumpThenExileTopPlay power toughness)
    (castKind := .pump)

def creatureYouControlDealsTwicePower : Effect :=
  mkSpell (.of .creatureYouControlThenOppCreature) (.creatureYouControlDealsTwicePower)
    (castKind := .fight)

def createTokensThenTeamPump (kind : TokenKind) (n : Nat) (power toughness : Int) : Effect :=
  mkSpell (.of .none) (.createTokensThenTeamPump kind n power toughness)
    (castKind := .pump)

def createTokensPerSubtype (kind : TokenKind) (subtype : String) : Effect :=
  mkSpell (.of .none) (.createTokensPerSubtype kind subtype)
    (castKind := .extraLand)

def creaturesYouControlGetAndGrant (power toughness : Int) (k : Keywords) : Effect :=
  mkSpell (.of .none) (.creaturesYouControlGetAndGrant power toughness k)
    (castKind := .massPump)

def destroyUpToOneNonland : Effect :=
  mkSpell (.of .nonland) (.destroyUpToOneNonland)
    (castKind := .destroyArtifactOrLand)
    (allowsZeroTargets := true)

def createGalactus : Effect :=
  mkSpell (.of .none) (.createGalactus)
    (castKind := .extraLand)

def worldsWithinWorlds : Effect :=
  mkSpell (.of .none) (.worldsWithinWorlds)
    (castKind := .extraLand)

def exileHandDrawPlayUntilNext : Effect :=
  mkSpell (.of .none) (.exileHandDrawPlayUntilNext)
    (castKind := .draw)

def copyNontokenCreaturesYouControl : Effect :=
  mkSpell (.of .none) (.copyNontokenCreaturesYouControl)
    (castKind := .extraLand)

def gainControlUntilEotOrNextIfVillain : Effect :=
  mkSpell (.of .creature) (.gainControlUntilEotOrNextIfVillain)
    (castKind := .pump)

def millThenPutPermanentGainLife (n life : Nat) : Effect :=
  mkSpell (.of .none) (.millThenPutPermanentGainLife n life)
    (castKind := .draw)

def searchLibraryOrGyArtifactCreatureX : Effect :=
  mkSpell (.of .none) (.searchLibraryOrGyArtifactCreatureX)
    (castKind := .extraLand)

def gainLifeSearchBasicPlusOne (life : Nat) : Effect :=
  mkSpell (.of .upToOneCreatureThenPlayer) (.gainLifeSearchBasicPlusOne life)
    (castKind := .draw)

def nextFreeRGCreature : Effect :=
  mkSpell (.of .none) (.nextFreeRGCreature)
    (castKind := .extraLand)

def ownerPutsLibraryThenConnive : Effect :=
  mkSpell (.of .oppCreature) (.ownerPutsLibraryThenConnive)
    (castKind := .counter)

def copyThisSpellXTimesThenDamage (n : Nat) : Effect :=
  mkSpell (.of .creature) (.copyThisSpellXTimesThenDamage n)
    (castKind := .creatureDamage)

def mayDrawPerArtifactOppsDraw : Effect :=
  mkSpell (.of .none) (.mayDrawPerArtifactOppsDraw)
    (castKind := .draw)

def mayPutHeroMvOrDraw (n : Nat) : Effect :=
  mkSpell (.of .none) (.mayPutHeroMvOrDraw n)
    (castKind := .draw)

def maySacArtifactOrDiscardDraw (cards : Nat) : Effect :=
  mkSpell (.of .none) (.maySacArtifactOrDiscardDraw cards)
    (castKind := .draw)

def chooseTargetDoubleAndTrample : Effect :=
  mkSpell (.of .creatureYouControl) (.chooseTargetDoubleAndTrample)
    (castKind := .pump)

def returnUpToTwoGyModal : Effect :=
  mkSpell (.of .none) (.returnUpToTwoGyModal)
    (castKind := .draw)

def artifactSpellsCostLessThisTurn (n : Nat) : Effect :=
  mkSpell (.of .none) (.artifactSpellsCostLessThisTurn n)
    (castKind := .extraLand)

def searchBasicLandTapped : Effect :=
  mkAbility ({}) (.searchBasicLand)

def searchLandTypeToHand (landType : String) : Effect :=
  mkAbility ({}) (.searchLandTypeToHand landType)

def exileTopPlayUntilEndOfNextTurn : Effect :=
  mkAbility ({}) (.exileTop)

def dealDamageToTargetCreature (amount : Nat) : Effect :=
  mkAbility (.of .creature) (.onPermanent (.dealDamage amount))
    (castKind := .creatureDamage)

def destroyTargetColorlessNonland : Effect :=
  mkAbility (.of .colorlessNonland) (.onPermanent .destroy)
    (castKind := .destroyColorless)

def attachToTargetCreatureYouControl : Effect :=
  mkAbility (.of .creatureYouControl) (.attach)

def becomeBearCreatureWithLandsPT : Effect :=
  mkAbility ({}) (.becomeBear)

def sourceGets (power toughness : Int) : Effect :=
  mkAbility ({}) (.onSource (.pump power toughness))

def putPlusOnePlusOneOnSource (n : Nat) : Effect :=
  mkAbility ({}) (.onSource (.plusOne n))

def targetCantBeBlockedThisTurn : Effect :=
  mkAbility (.of .creature .own) (.onPermanent .cantBeBlocked)

def returnFromGraveyardTapped : Effect :=
  mkAbility ({}) (.returnFromGraveyardTapped)

def returnFromGraveyardToHand : Effect :=
  mkAbility ({}) (.returnFromGraveyardToHand)

def destroyTargetArtifactOrEnchantment : Effect :=
  mkAbility (.of .artifactOrEnchantment) (.onPermanent .destroy)
    (castKind := .destroyColorless)

def millPlayer (n : Nat) : Effect :=
  mkAbility (.of .player) (.mill n)

def addAnyColor : Effect :=
  mkAbility ({}) (.addAnyColor)

def destroyTargetPermanent : Effect :=
  mkAbility (.of .permanent) (.onPermanent .destroy)
    (castKind := .destroyColorless)

def plusOneOnTarget (n : Nat) (subtypes : Array String := #[]) : Effect :=
  mkAbility (.of (if subtypes.isEmpty then .creatureYouControl
             else .creatureYouControlAnySubtype subtypes)) (.onPermanent (.plusOne n))

def targetCantBeBlockedPowerAtMost (n : Int) : Effect :=
  mkAbility (.of (.creaturePowerAtMost n)) (.onPermanent .cantBeBlocked)

def recruit : Effect :=
  mkAbility ({}) (.recruit)

def gainLife (n : Nat) : Effect :=
  mkAbility ({}) (.gainLife n)

def ownerShuffleSourceDraw (n : Nat) : Effect :=
  mkAbility ({}) (.ownerShuffleSourceDraw n)

def returnFromGyAttachPowerAtMost (n : Int) : Effect :=
  mkAbility (.of (.creatureYouControlPowerAtMost n)) (.returnFromGyAttach)

def addMana (types : Array ManaType) : Effect :=
  mkAbility ({}) (.addMana types)

def searchBasicLandToHand : Effect :=
  mkAbility ({}) (.searchBasicLandToHand)

def searchTwoBasicsSplit : Effect :=
  mkAbility ({}) (.searchTwoBasicsSplit)

def creaturesYouControlGetOppsLoseLife (power toughness : Int) (life : Nat) : Effect :=
  mkAbility ({}) (.creaturesYouControlGetOppsLoseLife power toughness life)

def goblinsAndOrcsGainMenace : Effect :=
  mkAbility ({}) (.goblinsAndOrcsGainMenace)

def exileThenReturnNextEnd : Effect :=
  mkAbility (.of .twoCreaturesOrLandsYouControl) (.exileThenReturnNextEnd)

def searchBasicBeholdElfUntap : Effect :=
  mkAbility ({}) (.searchBasicBeholdElfUntap)

def twoPlayersDraw : Effect :=
  mkAbility (.of .twoPlayers) (.twoPlayersDraw)

def discardLegendarySameNameDraw : Effect :=
  mkAbility ({}) (.discardLegendarySameNameDraw)

def dealDamageToAny (n : Nat) : Effect :=
  mkAbility (.of .playerOrCreature) (.dealDamageToAny n)
    (castKind := .creatureDamage)

def drawEqualSacrificedPowerThenDiscard : Effect :=
  mkAbility ({}) (.drawEqualSacrificedPowerThenDiscard)

def arwenShare : Effect :=
  mkAbility (.of .anotherCreature) (.arwenShare)

def grantCombatDamageCreateTreasure : Effect :=
  mkAbility (.of .creature) (.grantCombatDamageCreateTreasure)

def putShadowCounter : Effect :=
  mkAbility (.of .creature) (.putShadowCounter)

def damageEachOpponent (n : Nat) : Effect :=
  mkAbility ({}) (.damageEachOpponent n)

def chooseTwoDestroyRest : Effect :=
  mkAbility (.of .creature) (.chooseTwoDestroyRest)

def blackGateUnblockable : Effect :=
  mkAbility (.of .creature) (.blackGateUnblockable)

def burdenThenDraw : Effect :=
  mkAbility ({}) (.burdenThenDraw)

def teamGainDoubleStrike : Effect :=
  mkAbility ({}) (.teamGainDoubleStrike)

def sourceGainsIndestructibleTap : Effect :=
  mkAbility ({}) (.sourceGainsIndestructibleTap)

def plusOneOnEachOtherSubtype (subtype : String) (n : Nat) : Effect :=
  mkAbility ({}) (.plusOneOnEachOtherSubtype subtype n)

def plusOneAndIndestructibleCounter : Effect :=
  mkAbility ({}) (.plusOneAndIndestructibleCounter)

def plusOneAndDraw (plus cards : Nat) : Effect :=
  mkAbility ({}) (.plusOneAndDraw plus cards)

def plusOneAndExtraTurn : Effect :=
  mkAbility ({}) (.plusOneAndExtraTurn)

def plusOneX : Effect :=
  mkAbility ({}) (.plusOneX)

def eachOppDiscardThenPlusOne : Effect :=
  mkAbility ({}) (.eachOppDiscardThenPlusOne)

def lookAtTopPutHeroEquipVehicle (n : Nat) : Effect :=
  mkAbility ({}) (.lookAtTopPutHeroEquipVehicle n)

def transform : Effect :=
  mkAbility ({}) (.transform)

def drawX : Effect :=
  mkAbility ({}) (.drawX)

def lookAtTopRevealArtifact (n : Nat) : Effect :=
  mkAbility ({}) (.lookAtTopRevealArtifact n)

def connive : Effect :=
  mkAbility ({}) (.connive)

def addAnyColorSpendOnlyHero : Effect :=
  mkAbility ({}) (.addAnyColorSpendOnlyHero)

def addAnyColorSpendOnlyVillain : Effect :=
  mkAbility ({}) (.addAnyColorSpendOnlyVillain)

def addAnyColorSpendOnlyArtifactSpell : Effect :=
  mkAbility ({}) (.addAnyColorSpendOnlyArtifactSpell)

def addTwoAnyColorCreatureSources : Effect :=
  mkAbility ({}) (.addTwoAnyColorCreatureSources)

def addBlueCantNonartifact : Effect :=
  mkAbility ({}) (.addBlueCantNonartifact)

def addAnyColorEqualToSourcePower : Effect :=
  mkAbility ({}) (.addAnyColorEqualToSourcePower)

def addFourAnyCombination : Effect :=
  mkAbility ({}) (.addFourAnyCombination)

def addTwoAnyColorEquipment : Effect :=
  mkAbility ({}) (.addTwoAnyColorEquipment)

def drawPerDiscardedThisTurn : Effect :=
  mkAbility ({}) (.drawPerDiscardedThisTurn)

def createTokensEqualRemovedPlusOnes (kind : TokenKind) : Effect :=
  mkAbility ({}) (.createTokensEqualRemovedPlusOnes kind)

def exileTopXPlayThisTurn : Effect :=
  mkAbility ({}) (.exileTopXPlayThisTurn)

def copyControlledAbility (fromCreature : Bool) : Effect :=
  mkAbility (.of (if fromCreature then .stackAbilityFromCreatureSource
             else .stackAbilityFromArtifactSource)) (.copyControlledAbility fromCreature)

def createTokensEqualSubtype (kind : TokenKind) (subtype : String) : Effect :=
  mkAbility ({}) (.createTokensEqualSubtype kind subtype)

def createTappedTokens (kind : TokenKind) (n : Nat) : Effect :=
  mkAbility ({}) (.createTappedTokens kind n)

def destroyUpToOneThenPlusOne : Effect :=
  mkAbility (.of .artifactOrEnchantment) (.destroyUpToOneThenPlusOne)
    (castKind := .destroyColorless)
    (allowsZeroTargets := true)

def proliferateEachKind : Effect :=
  mkAbility (.of .permanentOrPlayer) (.proliferateEachKind)

def equipmentBecomesConstructHero : Effect :=
  mkAbility ({}) (.equipmentBecomesConstructHero)

def lookAtTopRevealSubtype (n : Nat) (subtype : String) : Effect :=
  mkAbility ({}) (.lookAtTopRevealSubtype n subtype)

def millThenPutHeroOrEnchantment (n : Nat) : Effect :=
  mkAbility ({}) (.millThenPutHeroOrEnchantment n)

def plusOneAndDoubleStrikeCounter : Effect :=
  mkAbility ({}) (.plusOneAndDoubleStrikeCounter)

def plusOneThenFightUpToOne : Effect :=
  mkAbility (.of .oppCreature) (.plusOneThenFightUpToOne)
    (allowsZeroTargets := true)

def plusOneAndGrant (k : Keywords) : Effect :=
  mkAbility ({}) (.plusOneAndGrant k)

def plusOneAndCreateTigerGod : Effect :=
  mkAbility ({}) (.plusOneAndCreateTigerGod)

def plusOneAndCreateTokens (n : Nat) (kind : TokenKind) : Effect :=
  mkAbility ({}) (.plusOneAndCreateTokens n kind)

def plusTwoThenOddEvenDestroy : Effect :=
  mkAbility ({}) (.plusTwoThenOddEvenDestroy)

def returnFromGyFinalityAttach : Effect :=
  mkAbility ({}) (.returnFromGyFinalityAttach)

def returnGyCreatureThenPlusOne (n : Nat) : Effect :=
  mkAbility (.of .creatureCardInYourGraveyard) (.returnGyCreatureThenPlusOne n)
    (allowsZeroTargets := true)

def revealTopDrawIfArtifact : Effect :=
  mkAbility ({}) (.revealTopDrawIfArtifact)

def copyArtifactYouControlNotLegendary : Effect :=
  mkAbility (.of .twoArtifactsYouControl) (.copyArtifactYouControlNotLegendary)

def pumpAttackingAloneGainLife : Effect :=
  mkAbility (.of .attackingAloneCreatureYouControl) (.pumpAttackingAloneGainLife)

def becomeDinosaurHero (power toughness : Int) (k : Keywords) : Effect :=
  mkAbility ({}) (.becomeDinosaurHero power toughness k)

def nextInstantSorceryCopyIfMvAtMostSourcePower : Effect :=
  mkAbility ({}) (.nextInstantSorceryCopyIfMvAtMostSourcePower)

def harnessInfinityStone : Effect :=
  mkAbility ({}) (.harnessInfinityStone)

def destroyTargetNoncreatureArtOrEnch : Effect :=
  mkAbility (.of .noncreatureArtifactOrEnchantment) (.destroyTargetNoncreatureArtOrEnch)
    (castKind := .destroyColorless)

def targetSubtypeConnives (subtype : String) : Effect :=
  mkAbility (.of (.creatureYouControlSubtype subtype)) (.targetSubtypeConnives subtype)

def anotherYouControlGetsAndGrant (p t : Int) (k : Keywords) : Effect :=
  mkAbility (.of .anotherCreatureYouControl) (.onPermanent (.pumpAndGrant p t k))

def tapTargetCreature : Effect :=
  mkAbility (.of .creature) (.onPermanent .tap)

def targetGets (p t : Int) : Effect :=
  mkAbility (.of .creature) (.onPermanent (.pump p t))

/-- Ability-phrased factories for leftover names that overlap spells. -/

def abilityCreateTokens (kind : TokenKind) (n : Nat) : Effect :=
  mkAbility ({}) (.createTokens kind n)

def abilityCreateTokensX (kind : TokenKind) : Effect :=
  mkAbility ({}) (.createTokensX kind)

def abilityCreaturesYouControlGet (power toughness : Int) : Effect :=
  mkAbility ({}) (.creaturesYouControlPump power toughness)

def abilityDealDamageToEachCreature (n : Nat) : Effect :=
  mkAbility ({}) (.dealDamageToEachCreature n)
    (castKind := .creatureDamage)

def abilityDraw (n : Nat) : Effect :=
  mkAbility ({}) (.draw n)

def abilityDrawThenDiscard (n : Nat) : Effect :=
  { resolution := .sequence [.draw n, .discard 1]
    phrase := s!"Draw {cardPhrase n}, then discard a card" }

def abilityScry (n : Nat) : Effect :=
  mkAbility ({}) (.scry n)

def abilityTargetPlayerDraw (n : Nat) : Effect :=
  mkAbility (.of .player) (.targetPlayerDraw n)

end Effect

end Mtg.Engine
