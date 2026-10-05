import Mtg.Engine.Card.Token
import Mtg.Engine.Card.Targeting

/-!
# Reality Fracture one-shot effects

Resolutions first printed in Reality Fracture (FRA). They are nested under
`Resolution.fra`, so spells, activated abilities, and triggered abilities
resolve them through one interpreter, and `Resolution` stays under the
constructor limit of the C runtime.
-/

namespace Mtg.Engine

inductive FraResolution where
  /-- Return the target permanent (or spell) to its owner's hand. -/
  | bounce
  /-- Exile the target permanent. -/
  | exile
  /-- Destroy the target creature. If it wasn't attacking, its controller
  draws a card (Prophesied End). -/
  | destroyDrawIfNotAttacking
  /-- You lose `n` life. -/
  | loseLife (n : Nat)
  /-- This deals `n` damage to each opponent and you gain `n` life. -/
  | damageEachOpponentGainLife (n : Nat)
  /-- This deals `n` damage to each player. -/
  | damageEachPlayer (n : Nat)
  /-- You draw `cards` cards and gain `life` life. -/
  | drawAndGainLife (cards life : Nat)
  /-- Deal `n` damage to the first target. Put a +1/+1 counter on the
  second target, if any (Awaken the Inferno). -/
  | damageThenPlusOneOnSecond (n : Nat)
  /-- Return the target card from your graveyard to the battlefield with
  `plusOnes` additional +1/+1 counters. -/
  | returnFromGyToBattlefield (plusOnes : Nat)
  /-- Return the target card from your graveyard to your hand. -/
  | returnFromGyToHand
  /-- Choose a creature type. Destroy all creatures that aren't of it. -/
  | destroyAllNotChosenType
  /-- Search for a planeswalker card, reveal it, shuffle, and put it on top. -/
  | searchPlaneswalkerToTop
  /-- Put `n` +1/+1 counters on each target. -/
  | plusOneOnEachTarget (n : Nat)
  /-- Return all nonland permanent cards from your graveyard to the battlefield. -/
  | returnAllNonlandPermanentsFromGy
  /-- Draw a card for each card put into the target player's graveyard from
  their library this turn. -/
  | drawMilledThisTurn
  /-- Exile all creatures. Empower Jace that many. -/
  | exileAllCreaturesEmpower
  /-- Draw cards equal to the greatest power among creatures you control,
  then lose that much life. -/
  | drawGreatestPowerLoseLife
  /-- The target player reveals their hand; you choose a card from it
  (nonland permanent card if `permanentOnly`, else nonland card). They
  discard it. -/
  | revealHandDiscardNonland (permanentOnly : Bool)
  /-- Deal `n` damage to the target opponent, then they reveal their hand and
  discard a nonland card you choose (Stinging Vitriol). -/
  | damageThenRevealDiscardNonland (n : Nat)
  /-- Reveal two cards from outside the game; an opponent chooses one to put
  into your hand (Extrapolate the Impossible). -/
  | extrapolate
  /-- Draw two cards, then you may exile this spell and four cards named
  Sphinx's Approach from your graveyard to search for a Sphinx creature card
  and put it onto the battlefield. -/
  | sphinxsApproach
  /-- Create a Cadet, then put a +1/+1 counter on each other Wizard token you
  control (Command the Stage). -/
  | cadetThenPlusOneOtherWizardTokens
  /-- This deals `n` damage to each creature and planeswalker your opponents
  control. -/
  | damageEachOppCreatureAndPlaneswalker (n : Nat)
  /-- The first target loses all abilities until end of turn; the second
  deals damage equal to its power to it (Flourishing Grapple). -/
  | loseAbilitiesThenFight
  /-- The target gets +P/+T and gains `k` until end of turn. Untap it. -/
  | pumpGrantUntap (power toughness : Int) (k : Keywords)
  /-- The target gets +P/+T and gains `k` until end of turn. Put `n` +1/+1
  counters on it. -/
  | pumpGrantPlusOne (power toughness : Int) (k : Keywords) (n : Nat)
  /-- Put `n` +1/+1 counters on the target. It gains `k` until end of turn. -/
  | plusOneThenGrant (n : Nat) (k : Keywords)
  /-- The owner of the target may put it on top of their library; if they do,
  this deals 2 damage to them. Otherwise they put it on the bottom. -/
  | clashOfElements
  /-- You may sacrifice a planeswalker. If you do, search for a planeswalker
  card and put it onto the battlefield (Entrust the Spark). -/
  | entrustTheSpark
  /-- Create `n` Cadets. If cast from a graveyard, put a +1/+1 counter on each
  for every three cards in your graveyard. -/
  | cadetsPlusOnePerThreeIfFromGy (n : Nat)
  /-- Create a Cadet. It gains haste until end of turn. -/
  | cadetWithHaste
  /-- Draw a card, or two if this spell wasn't cast from your hand. -/
  | drawOneOrTwoIfNotFromHand
  /-- Destroy the first target. Put a +1/+1 counter on each creature the
  second target (a player) controls. -/
  | destroyThenPlusOneEachOfPlayer
  /-- Exile the target. If its mana value was `n` or less, return it tapped
  under your control and exile it at the next end step. -/
  | exileReturnBrieflyIfMvAtMost (n : Nat)
  /-- Each player may discard their hand and draw `n` cards. -/
  | eachPlayerMayWheel (n : Nat)
  /-- Until end of turn, whenever you tap a Mountain for mana, add an
  additional {R}. -/
  | mountainsAddExtraRed
  /-- Search for a land card, put it into your graveyard, then shuffle. -/
  | searchLandToGraveyard
  /-- Counter the target spell. -/
  | counter
  /-- Counter the target spell unless its controller pays `{n}`. -/
  | counterUnlessPays (n : Nat)
  /-- Mill `m` cards, then draw `d` cards. -/
  | millThenDraw (m d : Nat)
  /-- Destroy the target permanent. -/
  | destroy
  /-- Deal `n` damage to the target. If that permanent would die this turn,
  exile it instead. -/
  | damageExileIfDies (n : Nat)
  /-- Mill `n` cards. You may put a permanent card from among them into your
  hand. You gain `life` life. -/
  | millMayPutPermanentGainLife (n life : Nat)
  /-- Untap all lands you control. -/
  | untapAllLandsYouControl
  /-- Exile the target, then return that card to the battlefield under its
  owner's control. -/
  | blink
  /-- You may remove a +1/+1 counter from the source. If you do, put a +1/+1
  counter on each other creature you control. -/
  | mayMovePlusOneToEachOther
  /-- Empower Jace X, where X is the number of creatures you control. -/
  | empowerJacePerCreature
  /-- Tap enchanted creature. It becomes unprepared. -/
  | tapEnchantedUnprepare
  /-- The owner of the target puts it on their choice of the top or bottom of
  their library. -/
  | ownerPutsOnTopOrBottom
  /-- Draw two cards, then discard two. Tap up to that many target creatures
  as nonland cards were discarded and stun them (Seasoned Cryomancer). -/
  | drawTwoDiscardTwoStun
  /-- If the source wasn't a token, create a token that's a copy of it. -/
  | copyTokenOfSourceIfNotToken
  /-- Return the source card from your graveyard to your hand, or to the
  battlefield (tapped if `tapped`, with `plusOnes` +1/+1 counters). -/
  | returnSourceFromGy (toHand : Bool) (tapped : Bool) (plusOnes : Nat)
  /-- You may pay `{n}`. When you do, for each opponent, destroy up to one
  target creature or planeswalker that player controls (Lich's Relic). -/
  | mayPayThenDestroyPerOpponent (n : Nat)
  /-- This deals X damage to the target, where X is the source's X. -/
  | damageX
  /-- Creatures you control gain trample and get +X/+0 until end of turn,
  where X is the number of artifacts you control. -/
  | trampleAndPowerPerArtifact
  /-- Search for a card, put it into your hand, shuffle, then discard a card
  at random. -/
  | searchCardThenDiscardRandom
  /-- The target instant or sorcery card in your graveyard gains flashback
  until end of turn; the flashback cost is its mana cost. -/
  | grantFlashbackUntilEot
  /-- You may discard a card. When you do, this deals `n` damage to any target. -/
  | mayDiscardThenDamage (n : Nat)
  /-- You may search for up to that many land cards (the damage dealt) and put
  them onto the battlefield tapped. -/
  | maySearchLandsEqualDamage
  /-- You may search for a basic land card and put it onto the battlefield
  tapped. -/
  | maySearchBasicLandTapped
  /-- Return the card that triggered this (an enchanted creature that died)
  to the battlefield tapped under its owner's control. -/
  | returnCauseTapped
  /-- Sacrifice the source. -/
  | sacrificeSource
  /-- The creature that triggered this deals `n` damage to each opponent. -/
  | causeDealsDamageToEachOpponent (n : Nat)
  /-- The target opponent reveals their hand; you exile a nonland card from it
  until the source leaves the battlefield (Null Summoner). -/
  | exileFromHandUntilLeaves
  /-- Mill `n` cards. When you do, return target land card from your
  graveyard to the battlefield tapped. -/
  | millThenReturnLandTapped (n : Nat)
  /-- You may sacrifice a land. If you do, create two tapped Heartwood tokens. -/
  | maySacrificeLandForHeartwoods
  /-- Exile up to one target nonland card of each card type from your
  graveyard, copy them, and cast copies with total mana value 6 or less
  free (Uldaros Theorix). -/
  | uldarosCopies
  /-- This deals `n` damage to the target and you gain `n` life. -/
  | damageThenGainLife (n : Nat)
  /-- Exile up to one target card from a graveyard. -/
  | exileCardFromGraveyard
  /-- Copy the spell that triggered this. You may choose new targets. -/
  | copyCauseSpell
  /-- Surveil 1. Then if seven or more cards are in your graveyard, sacrifice
  the source, deal 2 damage to each opponent, and gain 2 life. -/
  | eyeOfJace
  /-- Put a loyalty counter on each planeswalker you control. -/
  | loyaltyOnEachPlaneswalkerYouControl
  /-- The creature that triggered this gains `k` until end of turn. -/
  | causeGains (k : Keywords)
  /-- Untap the source. -/
  | untapSource
  /-- For each opponent, tap up to one target creature that player controls;
  put a stun counter on each. -/
  | tapAndStunPerOpponent
  /-- This deals `n` damage to the controller of the object that triggered it. -/
  | damageCauseController (n : Nat)
  /-- Remove up to `n` counters from the target. -/
  | removeUpToCounters (n : Nat)
  /-- This deals `n` damage to the target and you gain `n` life. -/
  | damageTargetGainLife (n : Nat)
  /-- You may sacrifice a creature or planeswalker. When you do, each opponent
  sacrifices a creature of their choice. -/
  | maySacrificeThenEdict
  /-- The source gets +X/+0 until end of turn, where X is the power of the
  creature that triggered this. -/
  | sourceGetsCausePower
  /-- Discard a card, then draw a card; then put a +1/+1 counter on the
  attacking creature for each card you've discarded this turn. -/
  | jiangYangguAlone
  /-- This deals 1 damage to each opponent. If the land is a Mountain, add {R}. -/
  | kothGeomancer
  /-- Search for up to X basic land cards with different names, where X is
  the value paid for the source's X, reveal them, and put them into your hand. -/
  | fblthpSearch
  /-- Untap all tokens you control. -/
  | untapAllTokensYouControl
  /-- You may discard a card. If you do, search for an enchantment card and put
  it into your hand. -/
  | mayDiscardThenSearchEnchantment
  /-- You gain `n` life. You may play an additional land this turn. -/
  | gainLifeAndExtraLand (n : Nat)
  /-- The first target fights up to one second target. -/
  | firstFightsSecond
  /-- For each opponent, put X minus-one counters on up to one target creature
  that player controls, where X is the greatest mana value among cards in
  your graveyard. -/
  | minusOnesPerOpponent
  /-- Draw a card for each color among other artifacts you control. -/
  | drawPerColorAmongOtherArtifacts
  /-- Untap the target attacking creature. It can't be blocked this turn. -/
  | untapUnblockable
  /-- The target creature gets minus X power until end of turn, where X is
  the number of cards in your graveyard. -/
  | minusPowerPerGraveyard
  /-- Put a +1/+1 counter on each creature you control. -/
  | plusOneOnEachCreatureYouControl
  /-- Put `n` +1/+1 counters on the source. -/
  | plusOneOnSource (n : Nat)
  /-- The source fights up to one target creature. -/
  | sourceFightsTarget
  /-- Exile the target until the source leaves the battlefield. -/
  | exileUntilSourceLeaves
  /-- Destroy each legal target. -/
  | destroyEachTarget
  /-- This deals `n` damage to each opponent. -/
  | damageEachOpponent (n : Nat)
  /-- This deals `n` damage to any target. -/
  | damageAny (n : Nat)
  /-- Return the target card from your graveyard to the battlefield tapped. -/
  | returnFromGyToBattlefieldTapped
  /-- Search for a basic land card and put it onto the battlefield tapped. -/
  | searchBasicLandTapped
  /-- Search for up to `n` land cards and put them onto the battlefield
  tapped. -/
  | searchLandsTapped (n : Nat)
  /-- Search for an enchantment card, reveal it, and put it into your hand. -/
  | searchEnchantmentToHand
  /-- Create `n` tapped Heartwood tokens. -/
  | tappedHeartwoods (n : Nat)
  /-- Each opponent sacrifices a creature of their choice. -/
  | eachOpponentSacrificesCreature
  /-- Draw a card; then put a +1/+1 counter on the creature that triggered
  this for each card you've discarded this turn (Jiang Yanggu, Alone). -/
  | drawThenCountersPerDiscard
  /-- If seven or more cards are in your graveyard, sacrifice the source, deal
  2 damage to each opponent, and gain 2 life (Eye of Jace). -/
  | eyeOfJaceCheck
  /-- Put a reflexive “deal `n` damage to any target” ability on the stack. -/
  | reflexiveDamageAnyTarget (n : Nat)
  /-- Put a reflexive “for each opponent, destroy up to one target creature or
  planeswalker that player controls” ability on the stack. -/
  | reflexiveDestroyPerOpponent
  /-- Put a reflexive “return target land card from your graveyard to the
  battlefield tapped” ability on the stack. -/
  | reflexiveReturnLandTapped
  /-- Choose `count` modes of this triggered ability as it is put on the
  stack; the modes are `CardDef.fraTriggerModes`. -/
  | chooseTriggerModes (count : Nat)
deriving Repr, Inhabited, BEq

namespace FraResolution

/-- Oracle-style wording, with `noun` for the first target. -/
def toPhrase (r : FraResolution) (noun : String) : String :=
  match r with
  | .bounce => s!"Return {noun} to its owner's hand"
  | .exile => s!"Exile {noun}"
  | .destroyDrawIfNotAttacking =>
    s!"Destroy {noun}. If it wasn't attacking, its controller draws a card"
  | .loseLife n => s!"You lose {n} life"
  | .damageEachOpponentGainLife n =>
    s!"This deals {n} damage to each opponent and you gain {n} life"
  | .damageEachPlayer n => s!"This deals {n} damage to each player"
  | .drawAndGainLife c l => s!"You draw {cardPhrase c} and gain {l} life"
  | .damageThenPlusOneOnSecond n =>
    s!"This deals {n} damage to {noun}. Put a +1/+1 counter on up to one target creature you control"
  | .returnFromGyToBattlefield n =>
    if n == 0 then s!"Return {noun} to the battlefield"
    else s!"Return {noun} to the battlefield with an additional +1/+1 counter on it"
  | .returnFromGyToHand => s!"Return {noun} to your hand"
  | .destroyAllNotChosenType =>
    "Choose a creature type. Destroy all creatures that aren't of the chosen type"
  | .searchPlaneswalkerToTop =>
    "Search your library for a planeswalker card, reveal it, then shuffle and put that card on top"
  | .plusOneOnEachTarget n =>
    s!"Put {plusOnePlusOneCountersPhrase n} on each of {noun}"
  | .returnAllNonlandPermanentsFromGy =>
    "Return all nonland permanent cards from your graveyard to the battlefield"
  | .drawMilledThisTurn =>
    "Draw X cards, where X is the number of cards that were put into target player's graveyard from their library this turn"
  | .exileAllCreaturesEmpower =>
    "Exile all creatures. Empower Jace X, where X is the number of creatures exiled this way"
  | .drawGreatestPowerLoseLife =>
    "Draw cards equal to the greatest power among creatures you control. You lose life equal to the number of cards drawn this way"
  | .revealHandDiscardNonland permanentOnly =>
    let what := if permanentOnly then "nonland permanent card" else "nonland card"
    s!"{capitalizeAscii noun} reveals their hand. You choose a {what} from it. That player discards that card"
  | .damageThenRevealDiscardNonland n =>
    s!"This deals {n} damage to {noun}. That player reveals their hand. You choose a nonland card from it. They discard that card"
  | .extrapolate =>
    "You may reveal exactly two cards you own with different names from outside the game. An opponent chooses one of them. You put that card into your hand"
  | .sphinxsApproach =>
    "Draw two cards. Then you may exile this spell and four cards named Sphinx's Approach from your graveyard. If you do, search your library for a Sphinx creature card, put it onto the battlefield, then shuffle"
  | .cadetThenPlusOneOtherWizardTokens =>
    "Create a 2/2 colorless Wizard Soldier creature token named Cadet, then put a +1/+1 counter on each other Wizard token you control"
  | .damageEachOppCreatureAndPlaneswalker n =>
    s!"This deals {n} damage to each creature and planeswalker your opponents control"
  | .loseAbilitiesThenFight =>
    s!"{capitalizeAscii noun} loses all abilities until end of turn. Target creature you control deals damage equal to its power to that permanent"
  | .pumpGrantUntap p t k =>
    s!"{capitalizeAscii noun} gets {signedStat p}/{signedStat t} and gains {k.joinedAnd} until end of turn. Untap it"
  | .pumpGrantPlusOne p t k n =>
    s!"{capitalizeAscii noun} gets {signedStat p}/{signedStat t} and gains {k.joinedAnd} until end of turn. Put {plusOnePlusOneCountersPhrase n} on it"
  | .plusOneThenGrant n k =>
    s!"Put {plusOnePlusOneCountersPhrase n} on {noun}. It gains {k.joinedAnd} until end of turn"
  | .clashOfElements =>
    "Choose target nonland permanent. Its owner may put it on top of their library. If they do, this deals 2 damage to them. If they didn't put the card on top of their library, they put it on the bottom"
  | .entrustTheSpark =>
    "You may sacrifice a planeswalker. If you do, search your library for a planeswalker card, put it onto the battlefield, then shuffle"
  | .cadetsPlusOnePerThreeIfFromGy n =>
    s!"Create {englishNumber n} 2/2 colorless Wizard Soldier creature tokens named Cadet. If this spell was cast from a graveyard, put a +1/+1 counter on each of them for every three cards in your graveyard"
  | .cadetWithHaste =>
    "Create a 2/2 colorless Wizard Soldier creature token named Cadet. It gains haste until end of turn"
  | .drawOneOrTwoIfNotFromHand =>
    "Draw a card. If this spell wasn't cast from your hand, draw two cards instead"
  | .destroyThenPlusOneEachOfPlayer =>
    s!"Destroy {noun}. Put a +1/+1 counter on each creature target player controls"
  | .exileReturnBrieflyIfMvAtMost n =>
    s!"Exile {noun}. If that permanent's mana value was {n} or less, return it to the battlefield tapped under your control. Exile it at the beginning of the next end step"
  | .eachPlayerMayWheel n =>
    s!"Each player may discard their hand and draw {englishNumber n} cards"
  | .mountainsAddExtraRed =>
    "Until end of turn, whenever you tap a Mountain for mana, add an additional {R}"
  | .searchLandToGraveyard =>
    "Search your library for a land card, put it into your graveyard, then shuffle"
  | .counter => s!"Counter {noun}"
  | .counterUnlessPays n => s!"Counter {noun} unless its controller pays \{{n}}"
  | .millThenDraw m d => s!"Mill {englishNumber m} cards, then draw {cardPhrase d}"
  | .destroy => s!"Destroy {noun}"
  | .damageExileIfDies n =>
    s!"This deals {n} damage to {noun}. If that permanent would die this turn, exile it instead"
  | .millMayPutPermanentGainLife n l =>
    s!"Mill {englishNumber n} cards. You may put a permanent card from among them into your hand. You gain {l} life"
  | .chooseTriggerModes n => if n == 2 then "choose two" else "choose one"
  | .minusPowerPerGraveyard =>
    s!"{capitalizeAscii noun} gets -X/-0 until end of turn, where X is the number of cards in your graveyard"
  | _ => ""

end FraResolution

end Mtg.Engine
