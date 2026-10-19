import Mtg.Engine.Card.ActivatedAbility
import Mtg.Engine.Card.Counter
import Mtg.Engine.Card.Effect

/-!
# Spell and activated-ability effect constructors

`Effect.mkSpell` / `Effect.mkAbility` plus the named constructors for every
printed spell and activated-ability effect the engine models, including
effects that resolve through the former Reality Fracture steps of `Resolution`.
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
Phrase comes from `Resolution.toPhrase` unless overridden. -/
def mkAbility (targeting : EffectTargeting) (resolution : Resolution)
    (castKind : AbilityCastKind := .other)
    (allowsZeroTargets := false)
    (phraseOverride : Option String := none) : Effect :=
  { targeting
    allowsZeroTargets
    abilityCastKind := castKind
    resolution
    phrase := phraseOverride.getD (Resolution.toPhrase resolution targeting.kind.noun) }

/-- Destroy one target of `kind`.
Pass `spellKind` for a spell (lowercase phrase, `SpellCastKind`).
Otherwise this is an activated ability. -/
def destroyTarget (kind : EffectTargetKind)
    (spellKind : Option SpellCastKind := none)
    (abilityKind : AbilityCastKind := .destroyColorless)
    (preferAsDefaultMode := false) : Effect :=
  match spellKind with
  | some castKind =>
    mkSpell (.of kind) (.onPermanent .destroy)
      (castKind := castKind)
      (preferAsDefaultMode := preferAsDefaultMode)
  | none =>
    mkAbility (.of kind) (.onPermanent .destroy)
      (castKind := abilityKind)

/-- The printed destroy-one-target effect for `kind`, including the cast
category used by the named constructors. The Oracle matcher refills a single
prototype to this so lines that differ only by the target noun stay one shape. -/
def canonicalDestroy (kind : EffectTargetKind) : Effect :=
  match kind with
  | .creatureWithFlying =>
    destroyTarget kind (spellKind := some .destroyFlying) (preferAsDefaultMode := true)
  | .creaturePowerAtLeast _ =>
    destroyTarget kind (spellKind := some .destroyCreature) (preferAsDefaultMode := true)
  | .artifact | .artifactToken | .noncreatureArtifact =>
    destroyTarget kind (spellKind := some .destroyArtifactOrLand)
  | .colorlessNonland | .artifactOrEnchantment | .permanent
  | .noncreatureArtifactOrEnchantment =>
    destroyTarget kind
  | _ =>
    destroyTarget kind (spellKind := some .destroyCreature)

/-- Printed leftover constructors as unified `Effect` values.
Call sites should use these instead of leftover inductives. -/

def dealDamage (amount : Nat) : Effect :=
  mkSpell (.of .playerOrCreature) (.onPermanent (.dealDamage amount))
    (castKind := .burn)

def pump (power toughness : Int) : Effect :=
  mkSpell (.of .creature .own) (.onPermanent (.pump power toughness))
    (castKind := .pump)

def destroyCreatureWithFlying : Effect :=
  destroyTarget .creatureWithFlying (spellKind := some .destroyFlying)
    (preferAsDefaultMode := true)

def destroyCreature : Effect :=
  destroyTarget .creature (spellKind := some .destroyCreature)

def plusOnePlusOneTrampleHexproof : Effect :=
  mkSpell (.of .creatureYouControl)
    (.sequence [
      .onPermanent (.plusOne 1),
      .onPermanent (.grantKeywords (Keyword.trample.merge Keyword.hexproof))])
    (castKind := .pump)
    (phraseOverride := some
      "put a +1/+1 counter on target creature you control. It gains trample and hexproof until end of turn")

def dealDamageToCreature (amount : Nat) : Effect :=
  mkSpell (.of .creature) (.onPermanent (.dealDamage amount))
    (castKind := .creatureDamage)

/-- Deal `amount` damage. The creature loses indestructible until end of turn.
If it would die this turn, exile it instead. -/
def dealDamageLoseIndestructibleExile (amount : Nat) : Effect :=
  mkSpell (.of .creature)
    (.sequence [
      .onPermanent (.dealDamage amount),
      .onPermanent .loseIndestructible,
      .replace .diesThisTurn .exile])
    (castKind := .creatureDamage)

def creatureYouControlDealsPowerToOppCreature : Effect :=
  mkSpell (.of .creatureYouControlThenOppCreature) (.fight .announced (.timesPower 1))
    (castKind := .fight)

def playAdditionalLandThisTurn : Effect :=
  mkSpell (.of .none) (.grant .extraLand .youIfCast)
    (castKind := .extraLand)

def destroyArtifactOrLandNonflyersCantBlock : Effect :=
  { targeting := .of .artifactOrLand
    spellCastKind := .destroyArtifactOrLand
    resolution := .sequence [.onPermanent .destroy, .cant (.block .creaturesWithoutFlying)]
    phrase := "destroy target artifact or land. Creatures without flying can't block this turn" }

def destroyTargetCreatureControllerLosesLife (life : Nat) : Effect :=
  mkSpell (.of .creature) (.sequence [.onPermanent .destroy, .loseLife life (.controller .target)])
    (castKind := .destroyCreature)
    (preferAsDefaultMode := true)

def allCreaturesGet (power toughness : Int) : Effect :=
  mkSpell (.of .none) (.pump (.fixed power) (.fixed toughness) .allCreatures)
    (castKind := .massPump)

def drawAndLoseLife (cards life : Nat) : Effect :=
  mkSpell (.of .none) (.sequence [.draw cards, .loseLife life])
    (castKind := .draw)

def targetPlayerDrawLoseLife (cards life : Nat) : Effect :=
  mkSpell (.of .player .selfPlayer)
    (.sequence [.draw cards .player, .loseLife life .player])
    (castKind := .draw)

def creaturesTargetPlayerGet (power toughness : Int) : Effect :=
  mkSpell (.of .player) (.pump (.fixed power) (.fixed toughness) .creaturesOfTargetPlayer)
    (castKind := .massPump)

def pumpAndLifelink (power toughness : Int) : Effect :=
  { targeting := .of .creature .own
    spellCastKind := .pump
    resolution := .sequence
      [.onPermanent (.pump power toughness),
       .onPermanent (.grantKeywords Keyword.lifelink)]
    phrase :=
      s!"target creature gets {signedStat power}/{signedStat toughness} and gains lifelink until end of turn" }

/-- Until-end-of-turn +P/+T. If the creature would die this turn, exile it instead. -/
def pumpAndExileIfDies (power toughness : Int) : Effect :=
  mkSpell (.of .creature)
    (.sequence [
      .onPermanent (.pump power toughness),
      .replace .diesThisTurn .exile])
    (castKind := .pump)
    (preferAsDefaultMode := true)

def exileGraveyardCreaturesGrantCast : Effect :=
  mkSpell (.of .player) (.exile (.graveyardCardsOfType .creature (.target .player)) .anyManaWhileExiled)
    (castKind := .draw)

def draw (n : Nat) : Effect :=
  mkSpell (.of .none) (.draw n)
    (castKind := .draw)

/-- Discard `n` cards. The Oracle parser joins this with `draw` on “, then”,
so “draw N cards, then discard a card” is not its own prototype. -/
def discardCards (n : Nat) : Effect :=
  { resolution := .discard (.cards n)
    phrase := s!"discard {cardPhrase n}" }

def drawThenDiscard (n : Nat) : Effect :=
  mkSpell (.of .none) (.sequence [.draw n, .discard (.cards 1)])
    (castKind := .draw)

def scry (n : Nat) : Effect :=
  mkSpell (.of .none) (.scry n)
    (castKind := .draw)

/-- Tap the target, then scry `scryN` and draw `drawN` (Hithlain Knots).
The draw waits until the scry finishes. An illegal target means none of
the steps happen. -/
def tapScryDraw (scryN drawN : Nat) : Effect :=
  mkSpell (.of .creature)
    (.sequence [.onPermanent .tap, .scry scryN, .draw drawN])
    (castKind := .draw)

def tapOneOrTwoCreatures : Effect :=
  mkSpell (.of .creature) (.tap (.target .eachPermanent))
    (castKind := .pump)
    (maxTargets := 2)

def grantHexproofIndestructible : Effect :=
  mkSpell (.of .artifactOrCreatureYouControl) (.onPermanent (.grantKeywords (Keyword.hexproof.merge Keyword.indestructible)))
    (castKind := .pump)

/-- Put `counters` of `kind` on up to one target creature, then the targeted
player gains `life`. Defaults are one +1/+1 counter (Meager Meal). -/
def plusOneUpToOneAndPlayerGainsLife (life : Nat)
    (kind : CounterKind := .plusOnePlusOne) (counters : Nat := 1) : Effect :=
  mkSpell (.of .upToOneCreatureThenPlayer)
    (.sequence [.putCounters (.ofKind kind counters) .creatureTargets, .gainLife life .player])
    (castKind := .pump)

def counterSpell : Effect :=
  mkSpell (.of .spell) (.counter)
    (castKind := .counter)

/-- Counter the targeted spell unless its controller pays `{n}`. -/
def counterUnlessPays (n : Nat) : Effect :=
  mkSpell (.of .spell) (.unlessPays .counter n)
    (castKind := .counter)

def counterCreatureSpellPTAtMost (n : Nat) : Effect :=
  mkSpell (.of (.creatureSpellPTAtMost n)) (.counter)
    (castKind := .counter)

def counterExilePermanentMayCast : Effect :=
  mkSpell (.of .spell) (.exile .targetSpell .forLater .counteredPermanentMayCast)
    (castKind := .counter)

/-- The owner puts the targeted creature on the top or bottom of their library. -/
def putOnTopOrBottom : Effect :=
  mkSpell (.of .creature)
    (.or [.onPermanent .putOnTopOfLibrary, .onPermanent .putOnBottomOfLibrary])
    (castKind := .counter)

def untapPumpMaybeAttach (power toughness : Int) : Effect :=
  mkSpell (.of .creatureYouControl)
    (.sequence [
      .onPermanent .untap,
      .onPermanent (.pump power toughness),
      .«if» (.subtype "Dwarf") (.may (.attach .equipmentYouControl .target) (.sequence []))])
    (castKind := .pump)

def exchangeControlSharingType : Effect :=
  mkSpell (.of .twoNonlandsSharingType) (.gainControl .exchangeTargets)
    (castKind := .counter)

def returnSpellDraw : Effect :=
  mkSpell (.of .spell) (.sequence [.returnToHand .targetSpell, .draw 1])
    (castKind := .counter)

def creaturesYouControlGet (power toughness : Int) : Effect :=
  mkSpell (.of .none) (.pump (.fixed power) (.fixed toughness) .creaturesYouControl)
    (castKind := .massPump)

def destroyArtifactOrEnchantmentGainLife (life : Nat) : Effect :=
  mkSpell (.of .artifactOrEnchantment) (.sequence [.onPermanent .destroy, .gainLife life])
    (castKind := .destroyArtifactOrLand)

def destroyCreaturePowerAtLeast (n : Int) : Effect :=
  destroyTarget (.creaturePowerAtLeast n) (spellKind := some .destroyCreature)
    (preferAsDefaultMode := true)

def becomeArtifactGainIndestructible : Effect :=
  mkSpell (.of .creature) (.onPermanent .becomeArtifactIndestructible)
    (castKind := .pump)

def pumpAndGrantKeywords (power toughness : Int) (k : Keywords) : Effect :=
  { targeting := .of .creature .own
    spellCastKind := .pump
    resolution := .sequence
      [.onPermanent (.pump power toughness), .onPermanent (.grantKeywords k)]
    phrase :=
      s!"target creature gets {signedStat power}/{signedStat toughness} and gains {k.joinedAnd} until end of turn" }

def amassGoblins (n : Nat) : Effect :=
  mkSpell (.of .none) (.amass n)
    (castKind := .pump)

def drawLoseLifeThenAmass (n : Nat) : Effect :=
  mkSpell (.of .none) (.sequence [.draw 1, .loseLife 1, .amass n])
    (castKind := .draw)

def returnCreatureFromGyThenAmass (n : Nat) : Effect :=
  mkSpell (.of .creatureCardInYourGraveyard)
    (.sequence [.returnToHand (.target .graveyardCard), .amass n])
    (castKind := .draw)
    (allowsZeroTargets := true)

/-- Counter the targeted spell. If its mana value was `n` or less, recruit.
The mana value includes `{X}` from when the spell was on the stack. -/
def counterThenRecruitIfMvAtMost (n : Nat) : Effect :=
  mkSpell (.of .spell)
    (.sequence [.counter, .«if» (.mvAtMost n) .recruit])
    (castKind := .counter)

def plusOneThenFight (n : Nat) : Effect :=
  mkSpell (.of .creatureYouControlThenOppCreature)
    (.sequence [.putCounters (.ofKind .plusOnePlusOne n) .firstTargetCreatureYouControl,
      .fight .announced .mutual])
    (castKind := .fight)

/-- Put a +1/+1 counter on the targeted creature you control. If this spell
was cast from a graveyard, also put one on each other creature you control. -/
def plusOneThenEachOtherIfFromGy : Effect :=
  mkSpell (.of .creatureYouControl)
    (.sequence [
      .putCounters (.ofKind .plusOnePlusOne 1) .firstTargetCreatureYouControl,
      .«if» .castFromGraveyard (.putCounters (.ofKind .plusOnePlusOne 1) .eachOther)])
    (castKind := .pump)

/-- Draw `n` cards, or `fromGy` cards if this spell was cast from a graveyard. -/
def drawIfFromGy (n fromGy : Nat) : Effect :=
  mkSpell (.of .none) (.ifElse .castFromGraveyard (.draw fromGy) (.draw n))
    (castKind := .draw)

/-- Amass Goblins `n`, or `fromGy` if this spell was cast from a graveyard. -/
def amassGoblinsOrFromGy (n fromGy : Nat) : Effect :=
  mkSpell (.of .none)
    (.ifElse .castFromGraveyard (.amass fromGy) (.amass n))
    (castKind := .pump)

def searchLegendaryCreatureToHand : Effect :=
  mkSpell (.of .none) (.searchLibrary (.returnToHand (.supertypeCard .legendary .creature)))
    (castKind := .draw)

def dealDamageToEachOppCreature (n : Nat) : Effect :=
  mkSpell (.of .none) (.dealDamage (.fixed n) .opponentsCreatures)
    (castKind := .creatureDamage)

def destroyTargetArtifact : Effect :=
  destroyTarget .artifact (spellKind := some .destroyArtifactOrLand)

def targetPlayerDraw (n : Nat) : Effect :=
  mkSpell (.of .player .selfPlayer) (.draw n .player)
    (castKind := .draw)

def dealDamageToCreatureExileIfDies (n : Nat) : Effect :=
  mkSpell (.of .creature)
    (.sequence [.replace .diesThisTurn .exile, .onPermanent (.dealDamage n)])
    (castKind := .creatureDamage)

def destroyArtifactToken : Effect :=
  destroyTarget .artifactToken (spellKind := some .destroyArtifactOrLand)

def addRedPerOppArtifacts : Effect :=
  mkSpell (.of .none) (.addMana #[.colored .red] (.count (.oppPermanents .artifact)))
    (castKind := .draw)

def dealDamageToEachNonDragon (n : Nat) : Effect :=
  mkSpell (.of .none) (.dealDamage (.fixed n) (.nonSubtypeCreatures "Dragon"))
    (castKind := .creatureDamage)

def chooseTypeReturnOthers : Effect :=
  mkSpell (.of .none) (.returnToHand .creaturesNotChosenType)
    (castKind := .counter)

def drawEqualToughnessThenPutCreatures : Effect :=
  mkSpell (.of .none) (.draw .greatestToughnessThenPutCreatures)
    (castKind := .draw)

def millThenPutInstantOrSorcery (n : Nat) : Effect :=
  mkSpell (.of .none) (.mill (.fixed n) .you (.toHand (.oneOf .instant .sorcery)))
    (castKind := .draw)

def millThenPutLands (n max : Nat) : Effect :=
  mkSpell (.of .none) (.mill (.fixed n) .you (.toHand (.upTo max .land)))
    (castKind := .draw)

def exileThenReturnYouControl : Effect :=
  mkSpell (.of .twoCreaturesOrLandsYouControl) (.exile .eachPermanent .returnImmediately)
    (castKind := .counter)

def dealDamageToEachNonDragonThenAddDragonMana (n : Nat) : Effect :=
  mkSpell (.of .none)
    (.sequence [.dealDamage (.fixed n) (.nonSubtypeCreatures "Dragon"), .addMana #[] (.fixed 4) (.subtypeSpells "Dragon")])
    (castKind := .creatureDamage)

def millThenPutAllInstantsOrSorceries (n : Nat) : Effect :=
  mkSpell (.of .none) (.mill (.fixed n) .you (.toHand (.allOf .instant .sorcery)))
    (castKind := .draw)

def exileAttackersSearchBasics : Effect :=
  mkSpell (.of .player) (.exile .attackingCreatures .forLater .controllerMaySearchBasic)
    (castKind := .destroyCreature)

def createTokensX (kind : TokenKind) : Effect :=
  mkSpell (.of .none) (.createTokens kind .chosenX)
    (castKind := .extraLand)

def exileTopPlayIfYouControlSubtype (n : Nat) (subtype : String) : Effect :=
  mkSpell (.of .none) (.exile (.topN n) (.playIfYouControlSubtype subtype))
    (castKind := .draw)

def returnSpellCantCastIfGift : Effect :=
  mkSpell (.of .spell)
    (.sequence [.returnToHand .targetSpell, .«if» .giftPromised (.cant (.castSpellsThisTurn .any))])
    (castKind := .counter)

def exileTopXOppPlayForLife : Effect :=
  mkSpell (.of .opponent) (.exile .opponentTopX .playForLifeThisTurn)
    (castKind := .draw)

def riddlesInTheDark : Effect :=
  mkSpell (.of .none) (.revealLibrary (.top 4) (.returnToHand .twoPiles))
    (castKind := .draw)

def supperForSpiders : Effect :=
  mkSpell (.of .none) (.put .creaturesDiedThisTurn .tapped .asFood)
    (castKind := .draw)

def eaglesAreComing : Effect :=
  mkSpell (.of (.filtered { noun := "target creature you own", types := #[.creature], ownedByYou := true }))
    (.returnToHand .ownedCreaturesKicker .delayedBirds)
    (castKind := .draw)

def lookAtTopLandsGainLife (n life : Nat) : Effect :=
  mkSpell (.of .none) (.revealLibrary (.top n) (.sequence [.put .landsYouControl .tapped, .gainLife (.fixed life)]))
    (castKind := .draw)

def gainControlOppArtifacts : Effect :=
  mkSpell (.of .artifact) (.gainControl .oppArtifacts)
    (castKind := .counter)
    (allowsZeroTargets := true)

def damageOppCreaturesEqualOtherSpellsMv : Effect :=
  mkSpell (.of .none)
    (.dealDamage .otherSpellsManaValue .opponentsCreatures)
    (castKind := .creatureDamage)

def phaseOutKicker : Effect :=
  mkSpell (.of .creature) (.grant .phaseOutKicker .target)
    (castKind := .counter)

def dealDamageToAttackerOrBlocker (n teamworkN : Nat) : Effect :=
  mkSpell (.of .attackingOrBlockingCreature)
    (.ifElse .teamwork (.onPermanent (.dealDamage teamworkN)) (.onPermanent (.dealDamage n)))
    (castKind := .creatureDamage)

def dealDamageThenControllerIfTeamwork (n extra : Nat) : Effect :=
  mkSpell (.of .creature)
    (.sequence [
      .onPermanent (.dealDamage n),
      .«if» .teamwork (.dealDamage (.fixed extra) (.player (.controller .target)))])
    (castKind := .creatureDamage)

def grantDoubleStrikeTeamworkTrample : Effect :=
  mkSpell (.of .creature)
    (.sequence [
      .onPermanent (.grantKeywords Keyword.doubleStrike),
      .«if» .teamwork (.onPermanent (.grantKeywords Keyword.trample))])
    (castKind := .pump)

def counterUnlessPaysTeamwork (n teamworkN : Nat) : Effect :=
  mkSpell (.of .spell)
    (.ifElse .teamwork (.unlessPays .counter teamworkN) (.unlessPays .counter n))
    (castKind := .counter)

def exileCreatureMvAtMostOrAnyIfTeamwork (n life : Nat) : Effect :=
  mkSpell (.of (.creatureMvAtMost n)) (.exile (.creatureMvAtMostOrTeamwork n) .forLater (.gainLifeIfTeamwork life))
    (castKind := .destroyCreature)

def returnGyCreatureMvAtMostOrAny (n : Nat) : Effect :=
  mkSpell (.of (.creatureCardInYourGraveyardMvAtMost n)) (.put (.creatureMvAtMostOrTeamwork n) .asPrinted)
    (castKind := .draw)

def revealTopPutCreatures (n : Nat) : Effect :=
  mkSpell (.of .none) (.revealLibrary (.top n) (.put .creaturesYouControl))
    (castKind := .extraLand)

def createTokens (kind : TokenKind) (n : Nat) : Effect :=
  mkSpell (.of .none) (.createTokens kind n)
    (castKind := .extraLand)

def exileCreatureToughnessAtLeast (n : Int) : Effect :=
  mkSpell (.of (.creatureToughnessAtLeast n)) (.onPermanent .exile)
    (castKind := .destroyCreature)

def exileEnchantmentMvAtLeast (n : Nat) : Effect :=
  mkSpell (.of (.enchantmentMvAtLeast n)) (.onPermanent .exile)
    (castKind := .destroyArtifactOrLand)

def returnOneOrTwoNonlands : Effect :=
  mkSpell (.of .nonland) (.returnToHand .eachPermanent)
    (castKind := .counter)
    (maxTargets := 2)

def grantDeathtouch : Effect :=
  mkSpell (.of .creature) (.onPermanent (.grantKeywords Keyword.deathtouch))
    (castKind := .pump)

def destroyNoncreatureArtifact : Effect :=
  destroyTarget .noncreatureArtifact (spellKind := some .destroyArtifactOrLand)

def plusOneOnCreature : Effect :=
  mkSpell (.of .creature) (.onPermanent (.plusOne 1))
    (castKind := .pump)

def targetPlayerCreatesTokens (kind : TokenKind) (n : Nat) : Effect :=
  mkSpell (.of .player) (.createTokens kind n (who := .player))
    (castKind := .extraLand)

def destroyCreatureSurveil : Effect :=
  mkSpell (.of .creature) (.sequence [.onPermanent .destroy, .surveil 1])
    (castKind := .destroyCreature)

def investigatePumpFlyingUntap : Effect :=
  mkSpell (.of .playerThenCreature)
    (.sequence [
      .investigate (.target .player),
      .grant (.keywords Keyword.flying) .creatureTargets,
      .untap .creatureTargets,
      .pump (.fixed 1) (.fixed 0) .creatureTargets])
    (castKind := .pump)

def plusOneLifelinkIndestructible : Effect :=
  mkSpell (.of .creature) (.sequence [.onPermanent (.plusOne 1),
    .onPermanent (.grantKeywords (Keyword.lifelink.merge Keyword.indestructible))])
    (castKind := .pump)

def dealDamageToEachCreature (n : Nat) : Effect :=
  mkSpell (.of .none) (.dealDamage (.fixed n) .allCreatures)
    (castKind := .creatureDamage)

def destroyLandSearchBasic : Effect :=
  mkSpell (.of .artifactOrLand)
    (.sequence [.onPermanent .destroy, .searchLibrary (.put (.supertypeCard .basic .land) .tapped)])
    (castKind := .destroyArtifactOrLand)

def doublePowerAndToughness : Effect :=
  mkSpell (.of .creature) (.onPermanent .doublePowerAndToughness)
    (castKind := .pump)

def returnGySubtypeToHand (subtype : String) : Effect :=
  mkSpell (.of (.filtered {
      noun := s!"target {subtype} card in your graveyard"
      zone := .yourGraveyard
      controller := .you
      subtypes := #[subtype] }))
    (.returnToHand (.graveyardSubtype subtype))
    (castKind := .draw)

def grantVigilanceUnblockable : Effect :=
  mkSpell (.of .creature) (.sequence [
    .onPermanent (.grantKeywords (Keyword.vigilance.merge Keyword.cantBeBlocked)),
    .draw 1])
    (castKind := .pump)

def becomeArtifactCreature44Flying : Effect :=
  mkSpell (.of .artifactOrCreatureYouControl) (.grant (.artifactCreature 4 4 "flying") .target)
    (castKind := .pump)

def drawThreeDiscardUnlessArtifact : Effect :=
  mkSpell (.of .none) (.sequence [.draw 3, .discard (.cardsUnlessType 2 .artifact)])
    (castKind := .draw)

def eachOpponentLosesLife (n : Nat) : Effect :=
  mkSpell (.of .none) (.loseLife n .eachOpponent)
    (castKind := .burn)

def fight : Effect :=
  mkSpell (.of .creatureYouControlThenOppCreature) (.fight .announced .mutual)
    (castKind := .fight)

def fightUpToOne : Effect :=
  mkSpell (.of .creatureYouControlThenOppCreature) (.fight .announced .upToOneOther)
    (castKind := .fight)
    (allowsZeroTargets := true)

def plusOneOnEachYouControl : Effect :=
  mkSpell (.of .none) (.putCounters (.ofKind .plusOnePlusOne) .youControl)
    (castKind := .pump)

def plusOneOnCreatureN (n : Nat) : Effect :=
  mkSpell (.of .creatureYouControl) (.putCounters (.ofKind .plusOnePlusOne n) .permanent)
    (castKind := .pump)

def pumpThenDraw (power toughness : Int) : Effect :=
  mkSpell (.of .creature) (.sequence [.onPermanent (.pump power toughness), .draw 1])
    (castKind := .pump)

def pumpThenExileTopPlay (power toughness : Int) : Effect :=
  mkSpell (.of .creature)
    (.sequence [.onPermanent (.pump power toughness), .exile (.topN 1) .playUntilNextTurn])
    (castKind := .pump)

def creatureYouControlDealsTwicePower (k : Nat := 2) : Effect :=
  mkSpell (.of .creatureYouControlThenOppCreature) (.fight .announced (.timesPower k))
    (castKind := .fight)

def createTokensThenTeamPump (kind : TokenKind) (n : Nat) (power toughness : Int) : Effect :=
  mkSpell (.of .none) (.sequence [.createTokens kind n, .pump (.fixed power) (.fixed toughness) .creaturesYouControl])
    (castKind := .pump)

def createTokensPerSubtype (kind : TokenKind) (subtype : String) : Effect :=
  mkSpell (.of .none) (.createTokens kind (.perSubtype subtype))
    (castKind := .extraLand)

def creaturesYouControlGetAndGrant (power toughness : Int) (k : Keywords) : Effect :=
  mkSpell (.of .none) (.sequence [.pump (.fixed power) (.fixed toughness) .creaturesYouControl, .grant (.keywords k) .creaturesYouControl])
    (castKind := .massPump)

def destroyUpToOneNonland : Effect :=
  mkSpell (.of .nonland) (.destroy .target)
    (castKind := .destroyArtifactOrLand)
    (allowsZeroTargets := true)

def createGalactus : Effect :=
  mkSpell (.of .none) (.createTokens .treasure (.fixed 1) false .galactus)
    (castKind := .extraLand)

def worldsWithinWorlds : Effect :=
  mkSpell (.of .none) (.exile .allCreatures .forLater .worldsWithinWorlds)
    (castKind := .extraLand)

def exileHandDrawPlayUntilNext : Effect :=
  mkSpell (.of .none) (.exile .hand .playUntilNextTurn .thenDrawThree)
    (castKind := .draw)

def copyNontokenCreaturesYouControl : Effect :=
  mkSpell (.of .none) (.becomeCopy .nontokenCreaturesYouControl)
    (castKind := .extraLand)

def gainControlUntilEotOrNextIfVillain : Effect :=
  mkSpell (.of .creature) (.gainControl .untilEotOrNextIfVillain)
    (castKind := .pump)

def millThenPutPermanentGainLife (n life : Nat) : Effect :=
  mkSpell (.of .none) (.mill (.fixed n) .you (.permanentAndGainLife life))
    (castKind := .draw)

def searchLibraryOrGyArtifactCreatureX : Effect :=
  mkSpell (.of .none) (.searchLibrary (.put .artifactCreatureX))
    (castKind := .extraLand)

def gainLifeSearchBasicPlusOne (life : Nat) : Effect :=
  mkSpell (.of .upToOneCreatureThenPlayer)
    (.sequence [.gainLife (.fixed life) .player, .searchLibrary (.put .basicLand .asPrinted), .putCounters (.ofKind .plusOnePlusOne 1) .target])
    (castKind := .draw)

def nextFreeRGCreature : Effect :=
  mkSpell (.of .none) (.mayCast .nextRedOrGreenCreature .unlimited .withoutPaying)
    (castKind := .extraLand)

def ownerPutsLibraryThenConnive : Effect :=
  mkSpell (.of .oppCreatureThenUpToOneCreatureYouControl) (.putOnLibrary .secondOrBottomThenConnive .target)
    (castKind := .counter)

def copyThisSpellXTimesThenDamage (n : Nat) : Effect :=
  mkSpell (.of .creature) (.sequence [.becomeCopy .sourceSpellXTimes, .onPermanent (.dealDamage n)])
    (castKind := .creatureDamage)

def mayDrawPerArtifactOppsDraw : Effect :=
  mkSpell (.of .none) (.may (.draw (.perControlled .artifact)) (.draw (.fixed 1) (who := .eachOpponent)) .ifYouDo)
    (castKind := .draw)

def mayPutHeroMvOrDraw (n : Nat) : Effect :=
  mkSpell (.of .none) (.may (.put (.creatureFromHand "Hero" n)) (.draw (.fixed 1)))
    (castKind := .draw)

def maySacArtifactOrDiscardDraw (cards : Nat) : Effect :=
  mkSpell (.of .none) (.may (.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .card])) (.draw (.fixed cards)) .ifYouDo)
    (castKind := .draw)

def chooseTargetDoubleAndTrample : Effect :=
  mkSpell (.of .creatureYouControl)
    (.sequence [
      .onPermanent .doublePowerAndToughness,
      .onPermanent (.grantKeywords Keyword.trample)])
    (castKind := .pump)

def returnUpToTwoGyModal : Effect :=
  mkSpell (.of (.filtered {
      noun := "up to two target artifact, creature, enchantment, and/or land cards in your graveyard"
      zone := .yourGraveyard
      types := #[.artifact, .creature, .enchantment, .land]
      controller := .you }))
    (.returnToHand .upToTwoGyModal) (allowsZeroTargets := true) (maxTargets := 2)
    (castKind := .draw)

def artifactSpellsCostLessThisTurn (n : Nat) : Effect :=
  mkSpell (.of .none) (.spellsCostLess (.cardType .artifact) (.fixed n))
    (castKind := .extraLand)

def supertypeSpellsCostLessThisTurn (n : Nat) : Effect :=
  mkSpell (.of .none) (.spellsCostLess (.supertype .legendary) (.fixed n))
    (castKind := .extraLand)

def searchBasicLandTapped : Effect :=
  mkAbility ({}) (.searchLibrary (.put .basicLand .tapped))

def searchLandTypeToHand (landType : String) : Effect :=
  mkAbility ({}) (.searchLibrary (.returnToHand (.landSubtype landType)))

def exileTopPlayUntilEndOfNextTurn : Effect :=
  mkAbility ({}) (.exile .top .playUntilNextTurn)

def dealDamageToTargetCreature (amount : Nat) : Effect :=
  mkAbility (.of .creature) (.onPermanent (.dealDamage amount))
    (castKind := .creatureDamage)

def destroyTargetColorlessNonland : Effect :=
  destroyTarget .colorlessNonland

def attachToTargetCreatureYouControl : Effect :=
  mkAbility (.of .creatureYouControl) (.attach .source .target)

def becomeSubtypeWithLandsPT (subtype : String) : Effect :=
  mkAbility ({}) (.grant (.subtypeWithLandsPT subtype) .source)

def becomeBearCreatureWithLandsPT : Effect :=
  becomeSubtypeWithLandsPT "Bear"

def sourceGets (power toughness : Int) : Effect :=
  mkAbility ({}) (.onSource (.pump power toughness))

def putPlusOnePlusOneOnSource (n : Nat) : Effect :=
  mkAbility ({}) (.onSource (.plusOne n))

def targetCantBeBlockedThisTurn : Effect :=
  mkAbility (.of .creature .own) (.onPermanent .cantBeBlocked)

def returnFromGraveyardTapped : Effect :=
  mkAbility ({}) (.put .source .tapped)

def returnFromGraveyardToHand : Effect :=
  mkAbility ({}) (.returnToHand .source)

def destroyTargetArtifactOrEnchantment : Effect :=
  destroyTarget .artifactOrEnchantment

def millPlayer (n : Nat) : Effect :=
  mkAbility (.of .player) (.mill n .player)

def addAnyColor : Effect :=
  mkAbility ({}) (.addMana #[] (.fixed 1) .anyColor)

def destroyTargetPermanent : Effect :=
  destroyTarget .permanent

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
  { resolution := .sequence [.putOnLibrary .shuffled .source, .draw n]
    phrase := s!"This owner shuffles him into their library and draws {cardPhrase n}" }

def returnFromGyAttachPowerAtMost (n : Int) : Effect :=
  mkAbility (.of (.creatureYouControlPowerAtMost n)) (.put .source .asPrinted .forAttach)

def addMana (types : Array ManaType) : Effect :=
  mkAbility ({}) (.addMana types)

def searchBasicLandToHand : Effect :=
  mkAbility ({}) (.searchLibrary (.returnToHand .basicLand))

def searchTwoBasicsSplit : Effect :=
  mkAbility ({}) (.searchLibrary (.sequence [.put .basicLand .tapped, .returnToHand .basicLand]))

def creaturesYouControlGetOppsLoseLife (power toughness : Int) (life : Nat) : Effect :=
  { resolution := .sequence
      [.pump (.fixed power) (.fixed toughness) .creaturesYouControl,
       .loseLife life .eachOpponent]
    phrase :=
      s!"Creatures you control get {signedStat power}/{signedStat toughness} until end of turn. Each opponent loses {life} life" }

def subtypesGainMenace (subtypes : Array String) : Effect :=
  mkAbility ({}) (.grant (.keywords Keyword.menace) (.intersection [.creaturesYouControl, .union (subtypes.toList.map (fun s => .youControl (.subtype s)))]))

def exileThenReturnNextEnd : Effect :=
  mkAbility (.of .twoCreaturesOrLandsYouControl) (.exile (.target .eachPermanent) .nextEndStep)

def searchBasicBeholdSubtypeUntap (subtype : String) : Effect :=
  mkAbility ({}) (.searchLibrary (.put (.basicBeholdUntap subtype) .tapped))

def searchBasicBeholdElfUntap : Effect :=
  searchBasicBeholdSubtypeUntap "Elf"

def twoPlayersDraw : Effect :=
  mkAbility (.of .twoPlayers) (.draw (.fixed 1) .targetPlayers)

def discardLegendarySameNameDraw : Effect :=
  mkAbility ({}) (.draw (.fixed 2))

def dealDamageToAny (n : Nat) : Effect :=
  mkAbility (.of .playerOrCreature) (.dealDamage n .target)
    (castKind := .creatureDamage)

def drawEqualSacrificedPowerThenDiscard : Effect :=
  mkAbility ({})
    (.sequence [.draw .lastKnownPower, .discard (.cards 1)])
    (phraseOverride := some
      "Draw cards equal to the sacrificed creature's power, then discard a card")

def arwenShare : Effect :=
  mkAbility (.of .anotherCreature) (.grant .arwenShare .target)

def grantCombatDamageCreateTreasure : Effect :=
  mkAbility (.of .creature) (.grant .combatDamageCreateTreasure .target)

def putShadowCounter : Effect :=
  mkAbility (.of .creature) (.putCounters (.ofKind .shadow 1) .target)

def damageEachOpponent (n : Nat) : Effect :=
  mkAbility ({}) (.dealDamage n (.player .eachOpponent))

def chooseTwoDestroyRest : Effect :=
  mkAbility (.of .none) (.destroy .allCreaturesExceptTwoChosen)

def blackGateUnblockable : Effect :=
  mkAbility (.of .creature) (.cant (.beBlockedByMostLifePlayer .target))

def burdenThenDraw : Effect :=
  mkAbility ({})
    (.sequence [.onSource .burdenCounter, .draw .perBurden])
    (phraseOverride := some
      "Put a burden counter on The One Ring, then draw a card for each burden counter on The One Ring")

def teamGain (k : Keywords) : Effect :=
  mkAbility ({}) (.grant (.keywords k) .creaturesYouControl)

def teamGainDoubleStrike : Effect :=
  teamGain Keyword.doubleStrike

def sourceGainsIndestructibleTap : Effect :=
  mkAbility ({})
    (.sequence [.onSource (.grantKeywords Keyword.indestructible), .onSource .tap])
    (phraseOverride := some
      "Witch-king of Angmar gains indestructible until end of turn. Tap him")

def plusOneOnEachOtherSubtype (subtype : String) (n : Nat) : Effect :=
  mkAbility ({}) (.putCounters (.ofKind .plusOnePlusOne n) (.othersOfSubtype subtype))

def plusOneAndIndestructibleCounter : Effect :=
  mkAbility ({})
    (.sequence [.onSource (.plusOne 1), .onSource .indestructibleCounter])
    (phraseOverride := some
      "Put a +1/+1 counter and an indestructible counter on this")

def plusOneAndDraw (plus cards : Nat) : Effect :=
  { resolution := .sequence [.onSource (.plusOne plus), .draw cards]
    phrase :=
      s!"Put {plusOnePlusOneCountersPhrase plus} on this and draw {cardPhrase cards}" }

def plusOneAndExtraTurn : Effect :=
  mkAbility ({})
    (.sequence [.onSource (.plusOne 1), .grant .extraTurn .youIfCast])
    (phraseOverride := some
      "Put a +1/+1 counter on this. Take an extra turn after this one. During that turn, power-up abilities can't be activated")

def plusOneX : Effect :=
  mkAbility ({}) (.putCounters .plusOneChosenX .source)

def eachOppDiscardThenPlusOne : Effect :=
  mkAbility ({}) (.sequence [.discard (.cards 1 .eachOpponent), .putCounters (.ofKind .plusOnePlusOne 1) .source])

def lookAtTopPutTypes (n : Nat) (types : Array String) : Effect :=
  let listed := orJoin types.toList
  let art := indefinite (types[0]?.getD "")
  mkAbility ({})
    (.sequence [.onSource (.plusOne 2), .revealLibrary (.top n) (.put (.lookedTypes types))])
    (phraseOverride := some
      s!"Put two +1/+1 counters on this, then look at the top {n} cards of your library. You may put {art} {listed} card from among them onto the battlefield. If it's a double-faced card, you may transform it. {restOnBottomRandomPhrase}")

def lookAtTopPutHeroEquipVehicle (n : Nat) : Effect :=
  lookAtTopPutTypes n #["Hero", "Equipment", "Vehicle"]

def transform : Effect :=
  mkAbility ({}) (.grant .transformed .source)

def drawX : Effect :=
  mkAbility ({}) (.draw .chosenX)

def lookAtTopRevealArtifact (n : Nat) : Effect :=
  mkAbility ({}) (.revealLibrary (.top n) (.returnToHand .artifact))

def connive : Effect :=
  mkAbility ({}) (.connive)

def addAnyColorSpendOnlySubtype (subtype : String) : Effect :=
  mkAbility ({}) (.addMana #[] (.fixed 1) (.subtypeSpellsOrAbilities subtype))

def addAnyColorSpendOnlyHero : Effect :=
  addAnyColorSpendOnlySubtype "Hero"

def addAnyColorSpendOnlyVillain : Effect :=
  addAnyColorSpendOnlySubtype "Villain"

def addAnyColorSpendOnlyArtifactSpell : Effect :=
  mkAbility ({}) (.addMana #[] (.fixed 1) .artifactSpell)

def addTwoAnyColorCreatureSources : Effect :=
  mkAbility ({}) (.addMana #[] (.fixed 2) .creatureSources)

def addBlueCantNonartifact : Effect :=
  mkAbility ({}) (.addMana #[.colored .blue] (.fixed 1) .cantNonartifact)

def addAnyColorEqualToSourcePower : Effect :=
  mkAbility ({}) (.addMana #[] .equalSourcePower .anyColor)

def addFourAnyCombination : Effect :=
  mkAbility ({}) (.addMana #[] (.fixed 4) .anyCombination)

def addTwoAnyColorEquipment : Effect :=
  mkAbility ({}) (.addMana #[] (.fixed 2) .equipment)

def drawPerDiscardedThisTurn : Effect :=
  mkAbility ({}) (.draw .cardsDiscardedThisTurn)

def createTokensEqualRemovedPlusOnes (kind : TokenKind) : Effect :=
  mkAbility ({}) (.createTokens kind .removedPlusOnes)

def exileTopXPlayThisTurn : Effect :=
  mkAbility ({}) (.exile .topPower .playThisTurn)

def copyControlledAbility (fromCreature : Bool) : Effect :=
  mkAbility (.of (if fromCreature then .stackAbilityFromCreatureSource
             else .stackAbilityFromArtifactSource)) (.becomeCopy (.stackAbility fromCreature))

def createTokensEqualSubtype (kind : TokenKind) (subtype : String) : Effect :=
  mkAbility ({}) (.createTokens kind (.perSubtype subtype))

def createTappedTokens (kind : TokenKind) (n : Nat) : Effect :=
  mkAbility ({}) (.createTokens kind n (tapped := true))

def destroyUpToOneThenPlusOne : Effect :=
  { targeting := .of .artifactOrEnchantment
    allowsZeroTargets := true
    abilityCastKind := .destroyColorless
    resolution := .sequence [.onPermanent .destroy, .onSource (.plusOne 1)]
    phrase :=
      "Destroy up to one target artifact or enchantment. Put a +1/+1 counter on this" }

def proliferateEachKind : Effect :=
  mkAbility (.of .permanentOrPlayer) (.proliferate (.fixed 1) .target)

def equipmentBecomesConstructHero : Effect :=
  mkAbility ({}) (.grant .constructHero .source)

def lookAtTopRevealSubtype (n : Nat) (subtype : String) : Effect :=
  mkAbility ({}) (.revealLibrary (.top n) (.returnToHand (.milledSubtype subtype)))

def millThenPutSubtypeOrEnchantment (n : Nat) (subtype : String) : Effect :=
  mkAbility ({}) (.mill (.fixed n) .you (.subtypeOrEnchantmentToHand subtype))

def millThenPutHeroOrEnchantment (n : Nat) : Effect :=
  millThenPutSubtypeOrEnchantment n "Hero"

def plusOneAndDoubleStrikeCounter : Effect :=
  mkAbility ({})
    (.sequence [.onSource (.plusOne 1), .onSource .doubleStrikeCounter])
    (phraseOverride := some
      "Put a +1/+1 counter and a double strike counter on this")

def plusOneThenFightUpToOne : Effect :=
  mkAbility (.of .oppCreature)
    (.sequence [.onSource (.plusOne 1), .fight .source .mutual])
    (allowsZeroTargets := true)
    (phraseOverride := some
      "Put a +1/+1 counter on this. This fights up to one target creature an opponent controls")

def plusOneAndGrant (k : Keywords) : Effect :=
  let joined :=
    if k.vigilance && k.indestructible && k.haste then
      "vigilance, indestructible, and haste"
    else k.joinedAnd
  { resolution := .sequence [.onSource (.plusOne 1), .onSource (.grantKeywords k)]
    phrase := s!"Put a +1/+1 counter on this. He gains {joined} until end of turn" }

def plusOneAndCreateTigerGod : Effect :=
  mkAbility ({})
    (.sequence [.onSource (.plusOne 1), .createTokens .treasure (.fixed 1) false .tigerGod])
    (phraseOverride := some
      "Put a +1/+1 counter on this and create The Tiger God, a legendary 4/4 green Cat God creature token with \"The Tiger God can't be blocked by more than one creature.\"")

def plusOneAndCreateTokens (n : Nat) (kind : TokenKind) : Effect :=
  { resolution := .sequence [.onSource (.plusOne n), .createTokens kind 1]
    phrase :=
      s!"Put {plusOnePlusOneCountersPhrase n} on this creature and {TokenKind.createPhrase kind 1}" }

def plusTwoThenOddEvenDestroy : Effect :=
  mkAbility ({})
    (.sequence [.onSource (.plusOne 2), .destroy .otherCreaturesOddOrEvenMv])
    (phraseOverride := some
      "Put two +1/+1 counters on this. Choose odd or even. Destroy each other creature with mana value of the chosen quality")

def returnFromGyFinalityAttach : Effect :=
  mkAbility ({}) (.put .source .asPrinted (.entering [.counter .finality 1 true]))

def returnGyCreatureThenPlusOne (n : Nat) : Effect :=
  mkAbility (.of .creatureCardInYourGraveyard)
    (.sequence [.returnToHand (.target .graveyardCard), .onSource (.plusOne n)])
    (allowsZeroTargets := true)
    (phraseOverride := some
      s!"Return up to one target creature card from your graveyard to your hand. Put {plusOnePlusOneCountersPhrase n} on this creature")

def revealTopDrawIfArtifact : Effect :=
  mkAbility ({}) (.revealLibrary (.top 1) (.draw (.fixed 1)))

def copyArtifactYouControlNotLegendary : Effect :=
  mkAbility (.of .twoArtifactsYouControl) (.becomeCopy .secondArtifactTargetNotLegendary)

def pumpAttackingAloneGainLife : Effect :=
  mkAbility (.of .attackingAloneCreatureYouControl)
    (.sequence [.onPermanent (.pump 1 0), .gainLife 1])

def becomeTypes (types : Array String) (power toughness : Int) (k : Keywords) : Effect :=
  mkAbility ({}) (.grant (.typesPTAndKeywords types power toughness k) .source)

def becomeDinosaurHero (power toughness : Int) (k : Keywords) : Effect :=
  becomeTypes #["Dinosaur", "Hero"] power toughness k

def nextInstantSorceryCopyIfMvAtMostSourcePower : Effect :=
  mkAbility ({}) (.grant (.nextSpellCopy true) .source)

def harnessInfinityStone : Effect :=
  mkAbility ({}) (.grant .harnessed .source)

def destroyTargetNoncreatureArtOrEnch : Effect :=
  destroyTarget .noncreatureArtifactOrEnchantment

def targetSubtypeConnives (subtype : String) : Effect :=
  mkAbility (.of (.creatureYouControlSubtype subtype)) (.connive (.target (.youControl (.subtype subtype))))

def anotherYouControlGetsAndGrant (p t : Int) (k : Keywords) : Effect :=
  mkAbility (.of .anotherCreatureYouControl)
    (.sequence [.onPermanent (.pump p t), .onPermanent (.grantKeywords k)])
    (phraseOverride := some
      s!"Another target creature you control gets {signedStat p}/{signedStat t} and gains {k.joinedAnd} until end of turn")

def tapTargetCreature : Effect :=
  mkAbility (.of .creature) (.onPermanent .tap)

def targetGets (p t : Int) : Effect :=
  mkAbility (.of .creature) (.onPermanent (.pump p t))

/-- Ability-phrased factories for leftover names that overlap spells. -/

def abilityCreateTokens (kind : TokenKind) (n : Nat) : Effect :=
  mkAbility ({}) (.createTokens kind n)

def abilityCreateTokensX (kind : TokenKind) : Effect :=
  mkAbility ({}) (.createTokens kind .chosenX)

def abilityCreaturesYouControlGet (power toughness : Int) : Effect :=
  mkAbility ({}) (.pump (.fixed power) (.fixed toughness) .creaturesYouControl)

def abilityDealDamageToEachCreature (n : Nat) : Effect :=
  mkAbility ({}) (.dealDamage (.fixed n) .allCreatures)
    (castKind := .creatureDamage)

def abilityDraw (n : Nat) : Effect :=
  mkAbility ({}) (.draw n)

def abilityDrawThenDiscard (n : Nat) : Effect :=
  { resolution := .sequence [.draw n, .discard (.cards 1)]
    phrase := s!"Draw {cardPhrase n}, then discard a card" }

def abilityScry (n : Nat) : Effect :=
  mkAbility ({}) (.scry n)

def abilityTargetPlayerDraw (n : Nat) : Effect :=
  mkAbility (.of .player) (.draw n .player)

/-- Reality Fracture effects. -/

def abilityEmpowerJace (n : Nat) : Effect :=
  mkAbility ({}) (.empowerJace n)

def abilitySurveil (n : Nat) : Effect :=
  mkAbility ({}) (.surveil n)

def targetCreatureBecomesPrepared : Effect :=
  mkAbility (.of .creature) (.onPermanent .becomePrepared)

def eachCreatureYouControlBecomesPrepared : Effect :=
  mkAbility ({}) (.becomePrepared .creaturesYouControl)

def plusOneThenGainLife (n life : Nat) : Effect :=
  { mkAbility (.of .creature) (.sequence [.onPermanent (.plusOne n), .gainLife life])
      with spellCastKind := .pump }

def damageTargetOpponent (n : Nat) : Effect :=
  { mkAbility (.of .opponent) (.onPermanent (.dealDamage n))
      (phraseOverride := some s!"This deals {n} damage to target opponent")
      with spellCastKind := .burn }

def millSelf (n : Nat) : Effect :=
  mkAbility ({}) (.mill n)

def mayDiscardDraw (n : Nat) : Effect :=
  { mkAbility ({}) (.may (.discard (.cards 1)) (.draw n) .ifYouDo) with spellCastKind := .draw }

def createTokensThenSurveil (kind : TokenKind) (n s : Nat) : Effect :=
  mkAbility ({}) (.sequence [.createTokens kind n, .surveil s])

def createTokensLifeGained (kind : TokenKind) : Effect :=
  mkAbility ({}) (.createTokens kind .lifeGainedThisTurn)

def setBasePT (power toughness : Int) : Effect :=
  { mkAbility (.of .creature) (.onPermanent (.setBasePT power toughness))
      with spellCastKind := .creatureDamage }

def oppSacrificesGreatestMvGainLife (life : Nat) : Effect :=
  { mkAbility (.of .opponent)
      (.sequence [.sacrifice .oppGreatestMvCreatureOrPlaneswalker, .gainLife life])
      (phraseOverride := some
        s!"Target opponent sacrifices a creature or planeswalker with the greatest mana value among creatures and planeswalkers they control. You gain {life} life")
      with spellCastKind := .destroyCreature }

def damageThenEmpowerExcess (n : Nat) : Effect :=
  { mkAbility (.of .creatureOrPlaneswalker) (.sequence [.dealDamage (.fixed n) .target .excess, .empowerJace .notedExcess])
      with spellCastKind := .creatureDamage }

def jaceLoyaltyAtInstantSpeed : Effect :=
  mkAbility ({}) (.grant .jaceLoyaltyAtInstantSpeed .youIfCast)

def exileTopMayCastElseDamageOpponents (n : Nat) : Effect :=
  mkAbility ({}) (.exile .top (.mayCastElseDamageOpponents n))

def emblemCastSpellDamage (n : Nat) : Effect :=
  mkAbility ({}) (.grant (.emblemCastSpellDamage n) .youIfCast)

def returnFromGyWithFinality : Effect :=
  mkAbility ({}) (.put .source .asPrinted (.entering [.counter .finality 1]))

def firstDealsStatDamageToSecond (useLoyalty : Bool) : Effect :=
  { mkAbility (.of (if useLoyalty then .planeswalkerYouControlThenOppCreatureOrPlaneswalker
        else .creatureYouControlThenOppCreatureOrPlaneswalker))
      (.dealDamage (if useLoyalty then .loyalty (.targetAt 0) else .power (.targetAt 0)) (.targetAt 1))
      with spellCastKind := .fight }

def tapAndStunTargetCreature : Effect :=
  mkAbility (.of .creature) (.onPermanent .tapAndStun)

def copyNextInstantSorceryThisTurn : Effect :=
  mkAbility ({}) (.grant (.nextSpellCopy false) .source)

def proliferatePlaneswalkerTypesTimes : Effect :=
  mkAbility ({}) (.proliferate .planeswalkerTypes .youControl)

def copyEachCreatureOfTargetPlayer : Effect :=
  { mkAbility (.of .player) (.becomeCopy (.creaturesControlledBy (.target .player)))
      with spellCastKind := .extraLand }

def cantBeBlockedAnotherPowerAtMost (n : Int) : Effect :=
  mkAbility (.of (.anotherCreatureYouControlPowerAtMost n)) (.onPermanent .cantBeBlocked)

/-- The printed “put N +1/+1 counters on” effect for `kind`.
`creature` is the pump spell; a creature you control, including a subtype
list, is the activated ability. -/
def canonicalPlusOne (n : Nat) (kind : EffectTargetKind) : Option Effect :=
  match kind with
  | .creature =>
    some (mkSpell (.of .creature) (.onPermanent (.plusOne n)) (castKind := .pump))
  | .creatureYouControl => some (plusOneOnTarget n)
  | .creatureYouControlAnySubtype ss =>
    some (if ss.isEmpty then plusOneOnTarget n else plusOneOnTarget n ss)
  | _ => none

def becomeCopyLegendRuleOff : Effect :=
  mkAbility (.of .creatureYouControl) (.becomeCopy .targetLegendRuleOff)

/-! Effects that resolve through former Reality Fracture steps of `Resolution`. -/

/-- A spell effect with its printed wording. -/
def fraSpell (kind : EffectTargetKind) (r : Resolution) (phrase : String)
    (castKind : SpellCastKind := .extraLand) (maxTargets : Nat := 0)
    (allowsZeroTargets := false) : Effect :=
  { targeting := .of kind, resolution := r, phrase, spellCastKind := castKind
    maxTargets, allowsZeroTargets }

def fraSpellOn (f : TargetFilter) (r : Resolution) (phrase : String)
    (castKind : SpellCastKind := .extraLand) : Effect :=
  fraSpell (.filtered f) r phrase castKind

def fraUntargeted (r : Resolution) (phrase : String)
    (castKind : SpellCastKind := .extraLand) : Effect :=
  fraSpell .none r phrase castKind

/-! ## White -/

def generousRevival : Effect :=
  fraSpellOn { noun := "target creature card with mana value 3 or less from your graveyard", zone := .yourGraveyard, types := #[.creature], mvAtMost := some 3 }
    (.put .graveyardCard .asPrinted (.entering [.counter .plusOnePlusOne 1 true]))
    "Return target creature card with mana value 3 or less from your graveyard to the battlefield with an additional +1/+1 counter on it"
    (castKind := .draw)

def hexhavenBattalion : Effect :=
  fraUntargeted (.createTokens .cadet 3)
    "Create three 2/2 colorless Wizard Soldier creature tokens named Cadet"
    (castKind := .draw)

def kindredJudgment : Effect :=
  fraUntargeted (.destroy .creaturesNotChosenType)
    "Choose a creature type. Destroy all creatures that aren't of the chosen type"
    (castKind := .destroyCreature)

def loyalTutor : Effect :=
  fraUntargeted (.searchLibrary (.putOnLibrary .top .planeswalkerCard))
    "Search your library for a planeswalker card, reveal it, then shuffle and put that card on top"
    (castKind := .draw)

def predictivePreparations : Effect :=
  fraSpell (.filtered TargetFilter.creature) (.putCounters (.ofKind .plusOnePlusOne 1) (.target .eachPermanent))
    "Put a +1/+1 counter on each of one or two target creatures"
    (castKind := .pump) (maxTargets := 2)

def prophesiedEnd : Effect :=
  fraSpellOn TargetFilter.creature (.destroy .target .drawIfNotAttacking)
    "Destroy target creature. If it wasn't attacking, its controller draws a card"
    (castKind := .destroyCreature)

def refuteDestiny : Effect :=
  fraSpell (.filtered { TargetFilter.creatureOrPlaneswalker with
      noun := "target creature or planeswalker that's green or blue"
      colors := #[.green, .blue] })
    (.sequence [.exile .target .forLater, .surveil 1])
    "Exile target creature or planeswalker that's green or blue. Surveil 1"
    (castKind := .destroyCreature)

def returnToTheLightRealms : Effect :=
  fraUntargeted (.put .allNonlandPermanentsInGraveyard)
    "Return all nonland permanent cards from your graveyard to the battlefield"
    (castKind := .draw)

def surgicalPrecisionDestroy : Effect :=
  fraSpell (.filtered { TargetFilter.creature with
      noun := "target creature with toughness 4 or greater", toughnessAtLeast := some 4 })
    (.sequence [.destroy .target, .gainLife 1])
    "Destroy target creature with toughness 4 or greater. You gain 1 life"
    (castKind := .destroyCreature)

def drawAndGainLife (cards life : Nat) : Effect :=
  fraUntargeted (.sequence [.draw cards, .gainLife life])
    s!"You draw {cardPhrase cards} and gain {life} life"
    (castKind := .draw)

def yourFateEndsHere : Effect :=
  fraSpell (.filtered { TargetFilter.creatureOrPlaneswalker with
      noun := "target creature or planeswalker with mana value 3 or greater"
      mvAtLeast := some 3 })
    (.sequence [.destroy .target, .surveil 1])
    "Destroy target creature or planeswalker with mana value 3 or greater. Surveil 1"
    (castKind := .destroyCreature)

/-! ## Blue -/

def counterTargetSpell : Effect :=
  fraSpellOn TargetFilter.spell .counter "Counter target spell" (castKind := .counter)

def cruelCalculations : Effect :=
  fraSpell .player (.draw .milledByTargetPlayerThisTurn)
    "Draw X cards, where X is the number of cards that were put into target player's graveyard from their library this turn"
    (castKind := .draw)

def icyReceptionCounter : Effect :=
  fraSpellOn { noun := "target creature or legendary spell", zone := .stack
               types := #[.creature], orLegendary := true }
    (.unlessPays .counter 3)
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
  fraUntargeted (.sequence [.draw 2, .exile .sphinxsApproach .forLater])
    "Draw two cards. Then you may exile this spell and four cards named Sphinx's Approach from your graveyard. If you do, search your library for a Sphinx creature card, put it onto the battlefield, then shuffle"
    (castKind := .draw)

def unsummon : Effect :=
  fraSpellOn TargetFilter.creature (.returnToHand .target) "Return target creature to its owner's hand"
    (castKind := .destroyCreature)

def unwindHistory : Effect :=
  fraSpell (.filtered { TargetFilter.creature with
      noun := "target creature an opponent controls with mana value 3 or less"
      controller := .opponent, mvAtMost := some 3 })
    (.sequence [.returnToHand .target, .surveil 1])
    "Return target creature an opponent controls with mana value 3 or less to its owner's hand. Surveil 1"
    (castKind := .destroyCreature)

def arcOfFortune : Effect :=
  fraUntargeted (.discard (.mayWheel 7 .eachPlayer))
    "Each player may discard their hand and draw seven cards"
    (castKind := .draw)

/-! ## Black -/

def castAwayDoubt : Effect :=
  fraUntargeted (.sequence [.draw 2, .dealDamage (.fixed 2) (.player .eachPlayer)])
    "Draw two cards. This spell deals 2 damage to each player"
    (castKind := .draw)

def extendedAbsence : Effect :=
  fraSpell (.filtered TargetFilter.creatureOrPlaneswalker)
    (.sequence [.exile .target .forLater, .dealDamage 1 (.player .eachOpponent), .gainLife 1])
    "Exile target creature or planeswalker. This spell deals 1 damage to each opponent and you gain 1 life"
    (castKind := .destroyCreature)

def extrapolateTheImpossible : Effect :=
  fraUntargeted (.returnToHand .outsideGameOpponentChoice)
    "You may reveal exactly two cards you own with different names from outside the game. An opponent chooses one of them. You put that card into your hand"
    (castKind := .draw)

def overwriteTheMultiverse : Effect :=
  fraUntargeted (.exile .allCreatures .forLater .empowerJace)
    "Exile all creatures. Empower Jace X, where X is the number of creatures exiled this way"
    (castKind := .destroyCreature)

def rewriteRegrets : Effect :=
  fraSpellOn { noun := "target creature or planeswalker card with mana value 6 or less from your graveyard", zone := .yourGraveyard, types := #[.creature, .planeswalker], mvAtMost := some 6 }
    (.put .graveyardCard)
    "Return target creature or planeswalker card with mana value 6 or less from your graveyard to the battlefield"
    (castKind := .draw)

def riseDraw : Effect :=
  fraUntargeted (.draw .greatestPowerAndLoseLife .you)
    "Draw cards equal to the greatest power among creatures you control. You lose life equal to the number of cards drawn this way"
    (castKind := .draw)

def destroyTargetCreatureOrPlaneswalker : Effect :=
  fraSpellOn TargetFilter.creatureOrPlaneswalker (.destroy .target)
    "Destroy target creature or planeswalker" (castKind := .destroyCreature)

def solveForDisappointment : Effect :=
  fraSpell .opponent (.discard .chosenNonlandPermanent)
    "Target opponent reveals their hand. You choose a nonland permanent card from it. That player discards that card"
    (castKind := .draw)

def terminalCriticism : Effect :=
  fraSpell (.filtered { TargetFilter.creatureOrPlaneswalker with
      noun := "target creature or planeswalker that's blue or red"
      colors := #[.blue, .red] })
    (.sequence [.destroy .target, .gainLife 1])
    "Destroy target creature or planeswalker that's blue or red. You gain 1 life"
    (castKind := .destroyCreature)

def vraskasMercyDestroy : Effect :=
  fraSpell (.filtered TargetFilter.creatureOrPlaneswalker)
    (.sequence [.loseLife 2, .destroy .target])
    "You lose 2 life. Destroy target creature or planeswalker"
    (castKind := .destroyCreature)

def vraskasMercyEmpower : Effect :=
  fraUntargeted (.sequence [.loseLife 2, .empowerJace 6])
    "You lose 2 life. Empower Jace 6"
    (castKind := .draw)

/-! ## Red -/

def artifistAcumen : Effect :=
  fraUntargeted (.sequence [.grant (.keywords Keyword.firstStrike) .creaturesYouControl, .draw 1])
    "Creatures you control gain first strike until end of turn.\nDraw a card"
    (castKind := .pump)

def awakenTheInferno : Effect :=
  fraSpell (.multi #[TargetFilter.oppCreatureOrPlaneswalker,
      { TargetFilter.creatureYouControl with noun := "up to one target creature you control" }] #[1])
    (.sequence [.dealDamage (.fixed 6) (.targetAt 0), .putCounters (.ofKind .plusOnePlusOne 1) (.targetAt 1)])
    "This spell deals 6 damage to target creature or planeswalker an opponent controls. Put a +1/+1 counter on up to one target creature you control"
    (castKind := .creatureDamage)

def commandTheStage : Effect :=
  fraUntargeted (.sequence [.createTokens .cadet 1, .putCounters (.ofKind .plusOnePlusOne) .wizardTokensExceptRecent])
    "Create a 2/2 colorless Wizard Soldier creature token named Cadet, then put a +1/+1 counter on each other Wizard token you control"
    (castKind := .draw)

def essenceBurn : Effect :=
  fraSpellOn { TargetFilter.creatureOrPlaneswalker with
      noun := "target black or green creature or planeswalker", colors := #[.black, .green] }
    (.sequence [.replace .diesThisTurn .exile, .onPermanent (.dealDamage 5)])
    "This spell deals 5 damage to target black or green creature or planeswalker. If that permanent would die this turn, exile it instead"
    (castKind := .creatureDamage)

def fulminousForteSweep : Effect :=
  fraUntargeted (.dealDamage (.fixed 1) .oppCreaturesAndPlaneswalkers)
    "This spell deals 1 damage to each creature and planeswalker your opponents control"
    (castKind := .creatureDamage)

def damageToCreatureOrPlaneswalker (n : Nat) : Effect :=
  fraSpell (.filtered TargetFilter.creatureOrPlaneswalker) (.onPermanent (.dealDamage n))
    s!"This spell deals {n} damage to target creature or planeswalker"
    (castKind := .creatureDamage)

def moltenTide : Effect :=
  fraUntargeted (.grant .mountainsAddExtraRed .landsYouControl)
    "Until end of turn, whenever you tap a Mountain for mana, add an additional {R}"
    (castKind := .draw)

/-! ## Green -/

def enroot : Effect :=
  fraUntargeted (.searchLibrary (.mill (.fixed 1)))
    "Search your library for a land card, put it into your graveyard, then shuffle"
    (castKind := .draw)

def flourishingGrapple : Effect :=
  fraSpell (.multi #[{ TargetFilter.oppCreatureOrPlaneswalker with
        noun := "target creature or planeswalker an opponent controls that's red or white"
        colors := #[.red, .white] }, TargetFilter.creatureYouControl] #[])
    (.sequence [.lose .allAbilities (.targetAt 0), .dealDamage (.power (.targetAt 1)) (.targetAt 0)])
    "Target creature or planeswalker an opponent controls that's red or white loses all abilities until end of turn. Target creature you control deals damage equal to its power to that permanent"
    (castKind := .fight)

def restoreWithEmpathy : Effect :=
  fraSpell (.filtered { noun := "target permanent card from your graveyard", zone := .yourGraveyard, permanentCard := true })
    (.sequence [.returnToHand (.target .graveyardCard), .gainLife 4])
    "Return target permanent card from your graveyard to your hand. You gain 4 life"
    (castKind := .draw)

def somethingWorthSaving : Effect :=
  fraUntargeted (.mill (.fixed 4) .you (.permanentAndGainLife 1))
    "Mill four cards. You may put a permanent card from among them into your hand. You gain 1 life"
    (castKind := .draw)

def tethermagesAdvantage : Effect :=
  fraSpell (.filtered TargetFilter.creature)
    (.sequence [.onPermanent (.pump 2 2), .onPermanent (.grantKeywords Keyword.reach),
      .onPermanent .untap])
    "Target creature gets +2/+2 and gains reach until end of turn. Untap it"
    (castKind := .pump)

/-! ## Multicolor -/

def creaturesYouControlGetUntilEot (p t : Int) : Effect :=
  fraUntargeted (.pump (.fixed p) (.fixed t) .creaturesYouControl)
    s!"Creatures you control get {signedStat p}/{signedStat t} until end of turn"
    (castKind := .pump)

def chargeTheSanctumPump : Effect :=
  fraSpell (.filtered TargetFilter.creature)
    (.sequence [.onPermanent (.pump 2 0), .onPermanent (.grantKeywords Keyword.firstStrike),
      .onPermanent (.plusOne 1)])
    "Target creature gets +2/+0 and gains first strike until end of turn. Put a +1/+1 counter on it"
    (castKind := .pump)

def clashOfElements : Effect :=
  fraSpellOn { noun := "target nonland permanent", nonland := true } (.putOnLibrary .topOrBottomDamage2 .target)
    "Choose target nonland permanent. Its owner may put it on top of their library. If they do, this spell deals 2 damage to them. If they didn't put the card on top of their library, they put it on the bottom"
    (castKind := .destroyCreature)

def entrustTheSpark : Effect :=
  fraUntargeted (.may (.sacrifice .planeswalker) (.searchLibrary (.put .planeswalkerCard)) .ifYouDo)
    "You may sacrifice a planeswalker. If you do, search your library for a planeswalker card, put it onto the battlefield, then shuffle"
    (castKind := .draw)

def drawThenEmpower (cards n : Nat) : Effect :=
  fraUntargeted (.sequence [.draw cards, .empowerJace n])
    s!"Draw {cardPhrase cards}. Empower Jace {n}"
    (castKind := .draw)

def bounceSpellOrCreature : Effect :=
  fraSpellOn { noun := "target spell or creature", zone := .spellOrCreature } (.returnToHand .target)
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
  fraSpell (.filtered { TargetFilter.creature with noun })
    (.sequence [.onPermanent (.plusOne n), .onPermanent (.grantKeywords k)])
    s!"Put {plusOnePlusOneCountersPhrase n} on {noun}. It gains {k.joinedAnd} until end of turn"
    (castKind := .pump) (allowsZeroTargets := upToOne)

def addColorless (n : Nat) : Effect :=
  fraUntargeted (.addMana (Array.replicate n .colorless))
    s!"Add {String.join (List.replicate n "{C}")}"
    (castKind := .draw)

def recursiveRecruitment : Effect :=
  fraUntargeted
    (.sequence [.createTokens .cadet 2, .putCounters .plusOnePerThreeGraveyardIfFromGy .createdToken])
    "Create two 2/2 colorless Wizard Soldier creature tokens named Cadet. If this spell was cast from a graveyard, put a +1/+1 counter on each of them for every three cards in your graveyard"
    (castKind := .draw)

def targetCreatureGains (k : Keywords) (words : String := k.joinedAnd) : Effect :=
  fraSpell (.filtered TargetFilter.creature) (.onPermanent (.grantKeywords k))
    s!"Target creature gains {words} until end of turn"
    (castKind := .pump)

def cadetWithHaste : Effect :=
  fraUntargeted (.sequence [.createTokens .cadet 1, .grant (.keywords Keyword.haste) .createdToken])
    "Create a 2/2 colorless Wizard Soldier creature token named Cadet. It gains haste until end of turn"
    (castKind := .draw)

def stingingVitriol : Effect :=
  fraSpell .opponent
    (.sequence [.dealDamage (.fixed 2) .target, .discard .chosenNonland])
    "This spell deals 2 damage to target opponent. That player reveals their hand. You choose a nonland card from it. They discard that card"
    (castKind := .burn)

def theorixCounter : Effect :=
  fraSpellOn { noun := "target noncreature spell", zone := .stack, noncreature := true }
    (.unlessPays .counter 2)
    "Counter target noncreature spell unless its controller pays {2}"
    (castKind := .counter)

def millThenDraw (m d : Nat) : Effect :=
  fraUntargeted (.sequence [.mill m, .draw d])
    s!"Mill {englishNumber m} cards, then draw {cardPhrase d}"
    (castKind := .draw)

def twinnedVision : Effect :=
  fraUntargeted (.ifElse .notFromHand (.draw (.fixed 2)) (.draw (.fixed 1)))
    "Draw a card. If this spell wasn't cast from your hand, draw two cards instead"
    (castKind := .draw)

def twistedFates : Effect :=
  fraSpell (.multi #[{ noun := "target nonland permanent", nonland := true },
      { noun := "target player", zone := .player }] #[])
    (.sequence [.destroy (.targetAt 0), .putCounters (.ofKind .plusOnePlusOne 1) (.creaturesControlledBy (.targetAt 1))])
    "Destroy target nonland permanent. Put a +1/+1 counter on each creature target player controls"
    (castKind := .destroyCreature)

def permanentYouControlGains (k : Keywords) : Effect :=
  fraSpell (.filtered { noun := "target permanent you control", controller := .you })
    (.onPermanent (.grantKeywords k))
    s!"Target permanent you control gains {k.joinedAnd} until end of turn"
    (castKind := .pump)

def vindictiveTriumph : Effect :=
  fraSpellOn TargetFilter.creatureOrPlaneswalker (.exile .target (.returnBrieflyIfMvAtMost 3))
    "Exile target creature or planeswalker. If that permanent's mana value was 3 or less, return it to the battlefield tapped under your control. Exile it at the beginning of the next end step"
    (castKind := .destroyCreature)

def tamsResistance : Effect := plusOneThenGrant 1 Keyword.vigilance (upToOne := true)


/-! ## Modes of modal triggered abilities -/

def returnLegendaryCardToHand : Effect :=
  fraSpellOn { noun := "target legendary card from your graveyard", zone := .yourGraveyard, legendary := true }
    (.returnToHand (.target .graveyardCard)) "Return target legendary card from your graveyard to your hand"

def plusOneVigilanceIndestructible : Effect :=
  fraSpell (.filtered TargetFilter.creature)
    (.sequence [.onPermanent (.plusOne 1),
      .onPermanent (.grantKeywords (Keyword.vigilance.merge Keyword.indestructible))])
    "Put a +1/+1 counter on target creature. It gains vigilance and indestructible until end of turn"
    (castKind := .pump)

def fraTapTargetCreature : Effect :=
  fraSpell (.filtered TargetFilter.creature) (.onPermanent .tap) "Tap target creature"

def untapTargetCreature : Effect :=
  fraSpell (.filtered TargetFilter.creature) (.onPermanent .untap) "Untap target creature"

def drawThenDiscardOne : Effect :=
  fraUntargeted (.sequence [.draw 1, .discard (.cards 1)]) "Draw a card, then discard a card"

def destroyNoncreatureNonland : Effect :=
  fraSpellOn { noun := "target noncreature, nonland permanent", noncreature := true, nonland := true }
    (.destroy .target) "Destroy target noncreature, nonland permanent"

def gainLifeMode (n : Nat) : Effect :=
  fraUntargeted (.gainLife n) s!"You gain {n} life"

def minusPowerPerGraveyard : Effect :=
  fraSpellOn TargetFilter.creature (.pump .minusGraveyardCards (.fixed 0) .target)
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

/-- An activated ability with its printed line. -/
def fra (printed : String) (effect : Effect) (cost : ActivationCost)
    (onlyAsSorcery := false) (onlyDuringYourTurn := false)
    (activateFromGraveyard := false) (activateFromHand := false) (exhaust := false)
    (cond : FraActivationCondition := .none) : ActivatedAbility :=
  { cost, effect, printed, onlyAsSorcery, onlyDuringYourTurn, activateFromGraveyard,
    activateFromHand, exhaust, fraCondition := cond }

end ActivatedAbility

namespace FraCandidates

/-- Shorthand for an ability effect. -/
def ab (r : Resolution) (phrase : String) (kind : EffectTargetKind := .none)
    (allowsZeroTargets := false) (maxTargets := 0) : Effect :=
  { targeting := .of kind, resolution := r, phrase, allowsZeroTargets, maxTargets }

end FraCandidates

end Mtg.Engine
