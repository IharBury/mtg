import Mtg.Engine.Card.PermanentAction
import Mtg.Engine.Card.Targeting
import Mtg.Engine.Card.Token

/-!
# Spell resolutions (CR 608)

How a spell resolves, the demonstration agent's spell classification, and
the Oracle wording of each shape.
-/

namespace Mtg.Engine

/-- How the demonstration agent classifies a spell when choosing what to cast.
Adding a constructor is a compile error in `SpellResolution.toPhrase` rather than
silently skipping the new effect. -/
inductive SpellCastKind where
  /-- Damage to any target (player or creature). -/
  | burn
  /-- Damage to a creature only (including Smite-style follow-ups). -/
  | creatureDamage
  /-- A creature you control deals its power to an opposing creature. -/
  | fight
  /-- Destroy target creature with flying. -/
  | destroyFlying
  /-- Destroy target creature. -/
  | destroyCreature
  /-- Destroy target artifact or land. -/
  | destroyArtifactOrLand
  /-- Until-end-of-turn pump or +1/+1 with keyword grants. -/
  | pump
  /-- You may play an additional land this turn. -/
  | extraLand
  /-- Mass until-end-of-turn P/T change. -/
  | massPump
  /-- Draw cards, optionally losing life (e.g. Night's Whisper). -/
  | draw
  /-- Counter a spell. -/
  | counter
deriving Repr, Inhabited, BEq, DecidableEq

/-- How a spell resolves (CR 608). Grouped so `Game.applyEffect` matches a
handful of shapes instead of every printed spell factory. Burn and
creature-only damage both use `onPermanent (.dealDamage n)`; Game applies
that action to a player or a creature when the targeting shape allows it. -/
inductive SpellResolution where
  /-- You may play an additional land this turn. -/
  | extraLand
  /-- A creature you control deals its power to an opposing creature. -/
  | fight
  /-- Affect a still-legal target. Damage can hit a player or a creature;
  other actions require a permanent. -/
  | onPermanent (action : PermanentAction)
  /-- All creatures get +P/+T until end of turn. -/
  | allCreaturesPump (power toughness : Int)
  /-- You draw `cards` cards and lose `life` life. Loss of life is not
  damage (CR 118.3a / 120.3). -/
  | drawAndLoseLife (cards life : Nat)
  /-- The targeted player draws `cards` and loses `life` life. -/
  | playerDrawLoseLife (cards life : Nat)
  /-- Creatures the targeted player controls get +P/+T until end of turn. -/
  | creaturesOfPlayerPump (power toughness : Int)
  /-- Destroy the targeted creature; its controller loses `life` life. -/
  | destroyAndControllerLosesLife (life : Nat)
  /-- Exile creature cards from the targeted player's graveyard and grant
  permission to cast them, spending mana as though it were any type. -/
  | exileGraveyardCreaturesGrantCast
  /-- Draw `n` cards. -/
  | draw (n : Nat)
  /-- Draw `n` cards, then discard a card. -/
  | drawThenDiscard (n : Nat)
  /-- Scry `n`. -/
  | scry (n : Nat)
  /-- Tap the target, then scry and draw. -/
  | tapScryDraw (scryN drawN : Nat)
  /-- Tap each targeted creature (one or two). -/
  | tapTargets
  /-- Counter the targeted spell. -/
  | counter
  /-- Counter unless the controller pays `{n}`. -/
  | counterUnlessPays (n : Nat)
  /-- Counter; exile a permanent spell and grant a free cast. -/
  | counterExilePermanentMayCast
  /-- Owner puts the targeted creature on top or bottom of their library. -/
  | putOnTopOrBottom
  /-- Untap, pump, and maybe attach Equipment if the target is a Dwarf. -/
  | untapPumpMaybeAttach (power toughness : Int)
  /-- Exchange control of the two targeted permanents. -/
  | exchangeControl
  /-- Put a +1/+1 counter on an optional creature target; a player gains life. -/
  | plusOneAndPlayerGainsLife (life : Nat)
  /-- Return the targeted spell to its owner's hand, then draw a card. -/
  | returnSpellDraw
  /-- Creatures you control get +P/+T until end of turn. -/
  | creaturesYouControlPump (power toughness : Int)
  /-- Destroy the targeted artifact or enchantment; you gain life. -/
  | destroyArtifactOrEnchantmentGainLife (life : Nat)
  /-- Amass Goblins `n`. -/
  | amassGoblins (n : Nat)
  /-- Draw a card, lose 1 life, then amass Goblins `n`. -/
  | drawLoseLifeThenAmass (n : Nat)
  /-- Return an optional graveyard creature card, then amass Goblins `n`. -/
  | returnCreatureFromGyThenAmass (n : Nat)
  /-- Counter the targeted spell; recruit if its mana value was `n` or less. -/
  | counterThenRecruitIfMvAtMost (n : Nat)
  /-- +1/+1 counters on the first target, then it fights the second. -/
  | plusOneThenFight (n : Nat)
  /-- +1/+1 on the target; if from the graveyard, also each other. -/
  | plusOneThenEachOtherIfFromGy
  /-- Draw `n`, or `fromGy` if cast from a graveyard. -/
  | drawIfFromGy (n fromGy : Nat)
  /-- Amass Goblins `n`, or `fromGy` if cast from a graveyard. -/
  | amassGoblinsOrFromGy (n fromGy : Nat)
  /-- Search the library for a legendary creature and put it into hand. -/
  | searchLegendaryCreatureToHand
  /-- Deal `n` damage to each creature opponents control. -/
  | dealDamageToEachOppCreature (n : Nat)
  /-- Target player draws `n` cards. -/
  | targetPlayerDraw (n : Nat)
  /-- Deal `n` damage; if the creature would die this turn, exile it. -/
  | dealDamageToCreatureExileIfDies (n : Nat)
  /-- Add {R} for each artifact opponents control. -/
  | addRedPerOppArtifacts
  /-- Deal `n` damage to each non-Dragon creature. -/
  | dealDamageToEachNonDragon (n : Nat)
  /-- Choose a creature type and bounce the rest. -/
  | chooseTypeReturnOthers
  /-- Draw equal to greatest toughness, then put creatures onto the battlefield. -/
  | drawEqualToughnessThenPutCreatures
  /-- Mill `n`, then put an instant or sorcery into hand. -/
  | millThenPutInstantOrSorcery (n : Nat)
  /-- Mill `n`, then put up to `max` lands into hand. -/
  | millThenPutLands (n max : Nat)
  /-- Exile targeted permanents you control, then return them. -/
  | exileThenReturnYouControl
  /-- Deal `n` to each non-Dragon, then add Dragon-restricted mana. -/
  | dealDamageToEachNonDragonThenAddDragonMana (n : Nat)
  /-- Mill `n`, then put all instants and sorceries into hand. -/
  | millThenPutAllInstantsOrSorceries (n : Nat)
  /-- Exile attacking creatures; that player may search basics. -/
  | exileAttackersSearchBasics
  /-- Create X tokens of this kind. -/
  | createTokensX (kind : TokenKind)
  /-- Exile the top `n`; play them if you control this subtype. -/
  | exileTopPlayIfYouControlSubtype (n : Nat) (subtype : String)
  /-- Return the targeted spell; if a gift was promised, lock casts. -/
  | returnSpellCantCastIfGift
  /-- Exile the top X of the targeted opponent; play them for life. -/
  | exileTopXOppPlayForLife
  /-- Riddles in the Dark piles. -/
  | riddlesInTheDark
  /-- Return this-turn battlefield-to-gy creatures as Food. -/
  | supperForSpiders
  /-- Bounce owned creatures; delayed Bird Soldiers. -/
  | eaglesAreComing
  /-- Look at the top `n`; put lands onto the battlefield tapped; gain life. -/
  | lookAtTopLandsGainLife (n life : Nat)
  /-- Gain control of targeted opposing artifacts. -/
  | gainControlOppArtifacts
  /-- Damage opposing creatures equal to other spells cast this turn. -/
  | damageOppCreaturesEqualOtherSpellsMv
  /-- Phase out the target, or each of a player's creatures if kicked. -/
  | phaseOutKicker
  /-- Deal `n` to the target; `teamworkN` if the spell was cast using teamwork. -/
  | dealDamageTeamwork (n teamworkN : Nat)
  /-- Deal `n` to the target; if teamwork, `extra` to its controller. -/
  | dealDamageThenControllerIfTeamwork (n extra : Nat)
  /-- Grant double strike; also trample if teamwork. -/
  | grantDoubleStrikeTeamworkTrample
  /-- Counter unless `n`; `teamworkN` if teamwork. -/
  | counterUnlessPaysTeamwork (n teamworkN : Nat)
  /-- Exile MV-limited creature, or any plus gain life if teamwork. -/
  | exileCreatureMvAtMostOrAnyIfTeamwork (n life : Nat)
  /-- Return a gy creature, MV-limited unless teamwork. -/
  | returnGyCreatureMvAtMostOrAny (n : Nat)
  /-- Reveal the top `n` and put creatures onto the battlefield. -/
  | revealTopPutCreatures (n : Nat)
  /-- Create `n` tokens of this kind. -/
  | createTokens (kind : TokenKind) (n : Nat)
  /-- Exile the targeted creature. -/
  | exileTarget
  /-- Return one or two targeted nonlands to hand. -/
  | returnOneOrTwoNonlands
  /-- Target player creates tokens. -/
  | targetPlayerCreatesTokens (kind : TokenKind) (n : Nat)
  /-- Destroy the targeted creature, then surveil 1. -/
  | destroyCreatureSurveil
  /-- Investigate, pump +1/+0 and flying, untap. -/
  | investigatePumpFlyingUntap
  /-- +1/+1, lifelink, and indestructible on the target. -/
  | plusOneLifelinkIndestructible
  /-- Deal `n` damage to each creature. -/
  | dealDamageToEachCreature (n : Nat)
  /-- Destroy the targeted land; its controller may search a basic. -/
  | destroyLandSearchBasic
  /-- Double the targeted creature's power and toughness. -/
  | doublePowerAndToughness
  /-- Return a graveyard card of this subtype to hand. -/
  | returnGySubtypeToHand (subtype : String)
  /-- Grant vigilance and unblockable. -/
  | grantVigilanceUnblockable
  /-- Become a 4/4 artifact creature with flying. -/
  | becomeArtifactCreature44Flying
  /-- Draw three, then discard two unless an artifact. -/
  | drawThreeDiscardUnlessArtifact
  /-- Each opponent loses `n` life. -/
  | eachOpponentLosesLife (n : Nat)
  /-- Fight up to one other creature. -/
  | fightUpToOne
  /-- +1/+1 on each creature you control. -/
  | plusOneOnEachYouControl
  /-- `n` +1/+1 counters on a creature you control. -/
  | plusOneOnCreatureN (n : Nat)
  /-- Pump then draw. -/
  | pumpThenDraw (power toughness : Int)
  /-- Pump then exile the top card to play. -/
  | pumpThenExileTopPlay (power toughness : Int)
  /-- Controlled creature deals twice its power. -/
  | creatureYouControlDealsTwicePower
  /-- Create tokens, then pump the team. -/
  | createTokensThenTeamPump (kind : TokenKind) (n : Nat) (power toughness : Int)
  /-- Create a token per controlled subtype. -/
  | createTokensPerSubtype (kind : TokenKind) (subtype : String)
  /-- Team pump and grant keywords. -/
  | creaturesYouControlGetAndGrant (power toughness : Int) (k : Keywords)
  /-- Destroy up to one nonland. -/
  | destroyUpToOneNonland
  /-- Create Galactus. -/
  | createGalactus
  /-- Worlds Within Worlds. -/
  | worldsWithinWorlds
  /-- Exile hand, draw, play exiled cards. -/
  | exileHandDrawPlayUntilNext
  /-- Copy nontoken creatures you control. -/
  | copyNontokenCreaturesYouControl
  /-- Gain control until EOT or next turn if a bigger Villain. -/
  | gainControlUntilEotOrNextIfVillain
  /-- Mill, maybe take a permanent, gain life. -/
  | millThenPutPermanentGainLife (n life : Nat)
  /-- Search library or graveyard for an artifact creature. -/
  | searchLibraryOrGyArtifactCreatureX
  /-- Gain life, search a basic, +1/+1 on up to one. -/
  | gainLifeSearchBasicPlusOne (life : Nat)
  /-- Next red or green creature is free. -/
  | nextFreeRGCreature
  /-- Owner puts the creature into their library; you may connive. -/
  | ownerPutsLibraryThenConnive
  /-- Copy this spell X times, then deal damage. -/
  | copyThisSpellXTimesThenDamage (n : Nat)
  /-- Maybe draw per artifact; opponents draw if you do. -/
  | mayDrawPerArtifactOppsDraw
  /-- Maybe put a Hero from hand; otherwise draw. -/
  | mayPutHeroMvOrDraw (n : Nat)
  /-- Maybe sacrifice or discard, then draw. -/
  | maySacArtifactOrDiscardDraw (cards : Nat)
  /-- Double P/T and grant trample. -/
  | chooseTargetDoubleAndTrample
  /-- Return up to two modal graveyard cards. -/
  | returnUpToTwoGyModal
  /-- Artifact spells cost less this turn. -/
  | artifactSpellsCostLessThisTurn (n : Nat)
deriving Repr, Inhabited, BEq


namespace SpellResolution

/-- Oracle-style reminder from targeting and resolution. `fight` here is the
Quarrel wording; `Effect.fight` overrides the phrase for the actual fight spell. -/
def toPhrase (r : SpellResolution) (noun : String) : String :=
  match r with
  | .fight =>
    "target creature you control deals damage equal to its power to target creature an opponent controls"
  | .extraLand => "you may play an additional land this turn"
  | .drawAndLoseLife cards life =>
    s!"you draw {cardPhrase cards} and lose {life} life"
  | .onPermanent action => PermanentAction.toNotation action noun
  | .allCreaturesPump p t =>
    s!"all creatures get {signedStat p}/{signedStat t} until end of turn"
  | .playerDrawLoseLife cards life =>
    s!"{noun} draws {cardPhrase cards} and loses {life} life"
  | .creaturesOfPlayerPump p t =>
    s!"creatures {noun} controls get {signedStat p}/{signedStat t} until end of turn"
  | .destroyAndControllerLosesLife n =>
    s!"destroy {noun}. Its controller loses {n} life"
  | .exileGraveyardCreaturesGrantCast =>
    "exile all creature cards from target player's graveyard. You may cast spells from among those cards for as long as they remain exiled, and mana of any type can be spent to cast them"
  | .draw n => s!"draw {cardPhrase n}"
  | .drawThenDiscard n => s!"draw {cardPhrase n}, then discard a card"
  | .scry n => s!"scry {n}"
  | .tapScryDraw scryN drawN =>
    s!"tap {noun}. Scry {scryN}. Draw {cardPhrase drawN}"
  | .tapTargets => "tap one or two target creatures"
  | .counter => s!"counter {noun}"
  | .counterUnlessPays n =>
    s!"counter {noun} unless its controller pays \{{n}}"
  | .counterExilePermanentMayCast =>
    s!"counter {noun}. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled"
  | .putOnTopOrBottom =>
    s!"{noun}'s owner puts it on their choice of the top or bottom of their library"
  | .untapPumpMaybeAttach p t =>
    s!"untap {noun}. It gets {signedStat p}/{signedStat t} until end of turn. If it's a Dwarf, you may attach an Equipment you control to it"
  | .exchangeControl =>
    "exchange control of two target nonland permanents that share a card type"
  | .plusOneAndPlayerGainsLife n =>
    s!"put a +1/+1 counter on up to one target creature. Target player gains {n} life"
  | .returnSpellDraw =>
    s!"return {noun} to its owner's hand. Draw a card"
  | .creaturesYouControlPump p t =>
    s!"creatures you control get {signedStat p}/{signedStat t} until end of turn"
  | .destroyArtifactOrEnchantmentGainLife n =>
    s!"destroy {noun}. You gain {n} life"
  | .amassGoblins n =>
    s!"amass Goblins {n}"
  | .drawLoseLifeThenAmass n =>
    s!"you draw a card and lose 1 life. Amass Goblins {n}"
  | .returnCreatureFromGyThenAmass n =>
    s!"return up to one {noun} to your hand. Amass Goblins {n}"
  | .counterThenRecruitIfMvAtMost n =>
    s!"counter {noun}. If that spell's mana value was {n} or less, recruit"
  | .plusOneThenFight n =>
    s!"put {plusOnePlusOneCountersPhrase n} on target creature you control. Then it fights target creature an opponent controls"
  | .plusOneThenEachOtherIfFromGy =>
    "put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control"
  | .drawIfFromGy n fromGy =>
    s!"draw {cardPhrase n}. If this spell was cast from a graveyard, draw {cardPhrase fromGy} instead"
  | .amassGoblinsOrFromGy n fromGy =>
    s!"amass Goblins {n}. If this spell was cast from a graveyard, amass Goblins {fromGy} instead"
  | .searchLegendaryCreatureToHand =>
    searchLibraryToHandPhrase "a legendary creature card"
  | .dealDamageToEachOppCreature n =>
    s!"deals {n} damage to each creature your opponents control"
  | .targetPlayerDraw n =>
    s!"{noun} draws {cardPhrase n}"
  | .dealDamageToCreatureExileIfDies n =>
    s!"deals {n} damage to {noun}. If that creature would die this turn, exile it instead"
  | .addRedPerOppArtifacts =>
    "add {R} for each artifact your opponents control"
  | .dealDamageToEachNonDragon n =>
    s!"deals {n} damage to each non-Dragon creature"
  | .chooseTypeReturnOthers =>
    "choose a creature type. Return all creatures that aren't of the chosen type to their owners' hands"
  | .drawEqualToughnessThenPutCreatures =>
    "draw cards equal to the greatest toughness among creatures you control, then put any number of creature cards from your hand onto the battlefield"
  | .millThenPutInstantOrSorcery n =>
    s!"mill {n} cards, then put an instant or sorcery card from among them into your hand"
  | .millThenPutLands n max =>
    s!"mill {n} cards, then put up to {englishNumber max} land cards from among them into your hand"
  | .exileThenReturnYouControl =>
    "exile two target creatures and/or lands you control, then return them to the battlefield under their owner's control"
  | .dealDamageToEachNonDragonThenAddDragonMana n =>
    s!"deals {n} damage to each non-Dragon creature. Add four mana in any combination of colors. Spend this mana only to cast Dragon spells"
  | .millThenPutAllInstantsOrSorceries n =>
    s!"mill {n} cards, then put all instant and sorcery cards from among them into your hand"
  | .exileAttackersSearchBasics =>
    s!"exile all attacking creatures {noun} controls. That player may search their library for that many basic land cards, put those cards onto the battlefield tapped, then shuffle"
  | .createTokensX kind =>
    s!"create X {kind.pluralNoun}"
  | .exileTopPlayIfYouControlSubtype n subtype =>
    s!"look at the top {n} cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a {subtype}"
  | .returnSpellCantCastIfGift =>
    "return target spell to its owner's hand. If the gift was promised, players can't cast spells this turn"
  | .exileTopXOppPlayForLife =>
    "exile the top X cards of target opponent's library. You may play those cards this turn. If you cast a spell this way, pay life equal to its mana value rather than pay its mana cost"
  | .riddlesInTheDark =>
    "look at the top four cards of your library and separate them into a face-down pile and a face-up pile. An opponent chooses one of the piles. Put that pile into your hand and the other into your graveyard"
  | .supperForSpiders =>
    "put onto the battlefield under your control all creature cards in your opponents' graveyards that were put there from the battlefield this turn. They are Food artifacts with \"{2}, {T}, Sacrifice this artifact: You gain 3 life.\""
  | .eaglesAreComing =>
    "choose target creature you own. If this spell was kicked, instead choose any number of target creatures you own. Return each chosen creature to your hand. At the beginning of the next upkeep, create a 4/4 white Bird Soldier creature token with flying for each creature returned to your hand this way"
  | .lookAtTopLandsGainLife n life =>
    s!"look at the top {n} cards of your library, put any number of land cards from among them onto the battlefield tapped, then shuffle. You gain {life} life"
  | .gainControlOppArtifacts =>
    "for each opponent, gain control of up to one target artifact that player controls"
  | .damageOppCreaturesEqualOtherSpellsMv =>
    "deals damage to each creature your opponents control equal to the total mana value of other spells you've cast this turn"
  | .phaseOutKicker =>
    "target creature phases out. If this spell was kicked, each creature target player controls phases out instead"
  | .dealDamageTeamwork n teamworkN =>
    s!"deals {n} damage to target attacking or blocking creature. If this spell was cast using teamwork, it deals {teamworkN} damage to that creature instead"
  | .dealDamageThenControllerIfTeamwork n extra =>
    s!"deals {n} damage to target creature. If this spell was cast using teamwork, it also deals {extra} damage to that creature's controller"
  | .grantDoubleStrikeTeamworkTrample =>
    "target creature gains double strike until end of turn. If this spell was cast using teamwork, that creature also gains trample until end of turn"
  | .counterUnlessPaysTeamwork n teamworkN =>
    s!"counter target spell unless its controller pays \{{n}}. Counter that spell unless its controller pays \{{teamworkN}} instead if this spell was cast using teamwork"
  | .exileCreatureMvAtMostOrAnyIfTeamwork n life =>
    s!"exile target creature with mana value {n} or less. If this spell was cast using teamwork, instead exile target creature and you gain {life} life"
  | .returnGyCreatureMvAtMostOrAny n =>
    s!"choose target creature card in your graveyard with mana value {n} or less. If this spell was cast using teamwork, instead choose target creature card in your graveyard. Return the chosen card to the battlefield"
  | .revealTopPutCreatures n =>
    s!"reveal the top {n} cards of your library. You may put a creature card from among them onto the battlefield. If this spell was cast using teamwork, put any number of creature cards from among them onto the battlefield instead. Put the rest into your graveyard"
  | .createTokens kind n =>
    TokenKind.createPhrase kind n
  | .exileTarget =>
    s!"exile {noun}"
  | .returnOneOrTwoNonlands =>
    "return one or two target nonland permanents to their owners' hands"
  | .targetPlayerCreatesTokens kind n =>
    s!"{noun} creates {TokenKind.createdTokensPhrase kind n}"
  | .destroyCreatureSurveil =>
    s!"destroy {noun}. Surveil 1"
  | .investigatePumpFlyingUntap =>
    "target player investigates. Target creature gets +1/+0 and gains flying until end of turn. Untap it"
  | .plusOneLifelinkIndestructible =>
    "put a +1/+1 counter on target creature. It gains lifelink and indestructible until end of turn"
  | .dealDamageToEachCreature n =>
    s!"deals {n} damage to each creature"
  | .destroyLandSearchBasic =>
    s!"destroy {noun}. Its controller may {searchBasicLandTappedPhrase "their"}"
  | .doublePowerAndToughness =>
    s!"double {noun}'s power and toughness until end of turn"
  | .returnGySubtypeToHand subtype =>
    s!"return target {subtype} card from your graveyard to your hand"
  | .grantVigilanceUnblockable =>
    s!"{noun} gains vigilance until end of turn and can't be blocked this turn"
  | .becomeArtifactCreature44Flying =>
    s!"until end of turn, {noun} becomes an artifact creature with base power and toughness 4/4 and gains flying"
  | .drawThreeDiscardUnlessArtifact =>
    "draw three cards. Then discard two cards unless you discard an artifact card"
  | .eachOpponentLosesLife n =>
    s!"each opponent loses {n} life"
  | .fightUpToOne =>
    "target creature you control fights up to one other target creature"
  | .plusOneOnEachYouControl =>
    "put a +1/+1 counter on each creature you control"
  | .plusOneOnCreatureN n =>
    s!"put {plusOnePlusOneCountersPhrase n} on {noun}"
  | .pumpThenDraw p t =>
    let tStr := if t == 0 && p < 0 then "-0" else signedStat t
    s!"Target creature gets {signedStat p}/{tStr} until end of turn.\nDraw a card."
  | .pumpThenExileTopPlay p t =>
    s!"Target creature gets {signedStat p}/{signedStat t} until end of turn.\nExile the top card of your library. {playThatCardUntilNextTurnPhrase}."
  | .creatureYouControlDealsTwicePower =>
    "Target creature you control deals damage equal to twice its power to target creature an opponent controls."
  | .createTokensThenTeamPump kind n p t =>
    let tokens := capitalizeAscii (TokenKind.createPhrase kind n)
    s!"{tokens}, then creatures you control get {signedStat p}/{signedStat t} until end of turn."
  | .createTokensPerSubtype kind subtype =>
    s!"Create a {kind.oracleNoun} for each {subtype} you control"
  | .creaturesYouControlGetAndGrant p t k =>
    s!"Creatures you control get {signedStat p}/{signedStat t} and gain {k.joinedAnd} until end of turn"
  | .destroyUpToOneNonland =>
    "Destroy up to one target nonland permanent"
  | .createGalactus =>
    "Create Galactus, a legendary 16/16 black Elder Alien creature token with flying, trample, and \"Whenever Galactus attacks, destroy target land.\""
  | .worldsWithinWorlds =>
    "Exile all creatures. Each player may put any number of creature cards from their hand onto the battlefield. Then put all cards exiled this way into their owners' hands. Exile Worlds Within Worlds."
  | .exileHandDrawPlayUntilNext =>
    "Exile all the cards from your hand, then draw that many cards. Until the end of your next turn, you may play cards exiled this way."
  | .copyNontokenCreaturesYouControl =>
    "For each nontoken creature you control, create a token that's a copy of that creature, except it isn't legendary."
  | .gainControlUntilEotOrNextIfVillain =>
    "Gain control of target creature until end of turn. If you control a Villain with greater mana value than that creature, gain control of that creature until the end of your next turn instead. Untap that creature. It gains haste until end of turn."
  | .millThenPutPermanentGainLife n life =>
    s!"Mill {n} cards. You may put a permanent card from among the milled cards into your hand. You gain {life} life."
  | .searchLibraryOrGyArtifactCreatureX =>
    "Search your library and/or graveyard for an artifact creature card with mana value X or less and put it onto the battlefield with X additional +1/+1 counters on it. If X is 4 or greater, it gains haste until end of turn. If you search your library this way, shuffle."
  | .gainLifeSearchBasicPlusOne life =>
    s!"Target player gains {life} life, then searches their library for a basic land card, puts it onto the battlefield tapped, then shuffles. Put a +1/+1 counter on up to one target creature."
  | .nextFreeRGCreature =>
    "The next red or green creature spell you cast this turn can be cast without paying its mana cost"
  | .ownerPutsLibraryThenConnive =>
    "The owner of target creature an opponent controls puts it into their library second from the top or on the bottom. Then up to one target creature you control connives."
  | .copyThisSpellXTimesThenDamage n =>
    s!"When you cast this spell, copy it X times. You may choose new targets for the copies.\ndeals {n} damage to target creature."
  | .mayDrawPerArtifactOppsDraw =>
    "You may draw a card for each artifact you control. If you do, each opponent draws a card"
  | .mayPutHeroMvOrDraw n =>
    s!"You may put a Hero creature card with mana value {n} or less from your hand onto the battlefield. If you don't, draw a card"
  | .maySacArtifactOrDiscardDraw cards =>
    s!"You may sacrifice an artifact or discard a card. If you do, draw {cardPhrase cards}."
  | .chooseTargetDoubleAndTrample =>
    "Choose target creature you control. Until end of turn, double its power and toughness and it gains trample"
  | .returnUpToTwoGyModal =>
    "Choose up to two. Return those cards from your graveyard to your hand. • Target artifact card. • Target creature card. • Target enchantment card. • Target land card."
  | .artifactSpellsCostLessThisTurn n =>
    s!"Artifact spells you cast this turn cost \{{n}} less to cast"

end SpellResolution

end Mtg.Engine
