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
  /-- This deals `n` damage to each player. -/
  | damageEachPlayer (n : Nat)
  /-- This deals `amount` damage to the permanent target at `index`. -/
  | damageSourceAt (index amount : Nat)
  /-- Put `n` +1/+1 counters on the permanent target at `index`. -/
  | plusOneAt (index n : Nat)
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
  /-- Discard every card in your hand. -/
  | discardHand
  /-- Draw a card for each creature you control. -/
  | drawPerCreatureYouControl
  /-- Reveal two cards from outside the game; an opponent chooses one to put
  into your hand (Extrapolate the Impossible). -/
  | extrapolate
  /-- Draw two cards, then you may exile this spell and four cards named
  Sphinx's Approach from your graveyard to search for a Sphinx creature card
  and put it onto the battlefield. -/
  | sphinxsApproach
  /-- Put a +1/+1 counter on each Wizard token you control except tokens just created. -/
  | plusOneOnWizardTokensExceptRecent
  /-- This deals `n` damage to each creature and planeswalker your opponents
  control. -/
  | damageEachOppCreatureAndPlaneswalker (n : Nat)
  /-- The permanent target at `index` loses all abilities until end of turn. -/
  | loseAbilitiesAt (index : Nat)
  /-- The permanent at `fromIdx` deals damage equal to its power to the permanent at `toIdx`. -/
  | powerDamageFromTo (fromIdx toIdx : Nat)
  /-- The owner of the target may put it on top of their library; if they do,
  this deals 2 damage to them. Otherwise they put it on the bottom. -/
  | clashOfElements
  /-- You may sacrifice a planeswalker. If you do, search for a planeswalker
  card and put it onto the battlefield (Entrust the Spark). -/
  | entrustTheSpark
  /-- If this spell was cast from a graveyard, put a +1/+1 counter on each token
  just created for every three cards in your graveyard. -/
  | plusOnePerThreeGraveyardOnRecentIfFromGy
  /-- Tokens just created gain haste until end of turn. -/
  | grantHasteToRecentTokens
  /-- Draw a card, or two if this spell wasn't cast from your hand. -/
  | drawOneOrTwoIfNotFromHand
  /-- Destroy the permanent target at `index`. -/
  | destroyAt (index : Nat)
  /-- Put a +1/+1 counter on each creature the player target at `index` controls. -/
  | plusOneOnCreaturesOfPlayerAt (index : Nat)
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
  /-- Creatures you control get +X/+0 until end of turn, where X is the number
  of artifacts you control. -/
  | creaturesGetPowerPerArtifact
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
  /-- Create a 4/4 green Beast creature token with trample. -/
  | beastToken
  /-- Put the counters the causing object had as it left the battlefield on
  the source (The Ozolith). -/
  | putCauseCountersOnSource
  /-- You may move all counters from the source onto the target. -/
  | mayMoveSourceCountersToTarget
  /-- You may pay `{pay}`. If you do, proliferate `times` times. -/
  | mayPayThenProliferate (pay times : Nat)
  /-- Proliferate `times` times (CR 701.34). -/
  | proliferate (times : Nat)
  /-- The source Vehicle becomes an artifact creature until end of turn
  (crew, CR 702.122). -/
  | becomeArtifactCreatureUntilEot
  /-- Extort: you may pay {W/B}. If you do, each opponent loses 1 life and
  you gain that much life (CR 702.101). -/
  | extort
  /-- Put the reflexive triggered ability `kind` of an MSH card on the stack
  (“When you do, …”; MSH 359–369). `paid` is how many times its cost was
  paid. -/
  | queueMshReflexive (kind paid : Nat)
  /-- Resolve the reflexive triggered ability `kind` of an MSH card. -/
  | mshReflexive (kind paid : Nat)
  /-- Hawkeye's Trick Arrows: resolve the chosen modes (0 Net, 1 Explosive,
  2 Boomerang) in order. -/
  | hawkeyeArrows (modes : List Nat)
  /-- Copy the cards exiled to pay this boast activation; you may cast up to
  three of the copies without paying their mana costs (Baron Helmut Zemo). -/
  | zemoBoastCopies
  /-- Copy the source spell X times; you may choose new targets for the
  copies (Photon Blast Barrage). -/
  | copySourceSpellXTimes
  /-- You gain `n` life. -/
  | gainLife (n : Nat)
  /-- Put X +1/+1 counters on each creature you control, where X is the number
  of cards in your hand. -/
  | plusOnesEqualToHandOnEachCreature
  /-- The source deals damage equal to its power to the target creature
  (Thorin, Mountain-king). -/
  | damageEqualSourcePower
  /-- Return the source from the graveyard to its owner's hand. -/
  | returnSourceToHand
  /-- Exile the targeted enchantment, instant, or sorcery. Copy it. You may
  cast the copy without paying its mana cost (Saruman of Many Colors). -/
  | sarumanExileCopyMayCast
  /-- The creature that caused this ability gets +P/+T until end of turn. -/
  | causeGetsPump (power toughness : Int)
  /-- Creatures attacking the player recorded as the cause's controller get
  +2/+2 and gain trample until end of turn (Garruk, Curse Breaker). -/
  | attackersOfPlayerGetTwoTwoTrample
  /-- The target land gains “{T}: Add {C}{C}” until the exiled source is cast
  from exile, and you may cast the source while it remains exiled (Emrakul). -/
  | emrakulGrantMana
  /-- The next spell you cast this turn can't be countered. -/
  | nextSpellCantBeCountered
  /-- Exile the target creature or planeswalker you control; reveal until a
  creature or planeswalker card, put it onto the battlefield, and the rest on
  the bottom in a random order (Identity Echo). -/
  | identityEcho
  /-- Destroy the target artifact or enchantment. If it was a legendary
  enchantment, draw a card. -/
  | destroyDrawIfLegendaryEnchantment
  /-- The source gains your choice of the keywords coded in `options` until
  end of turn. -/
  | chooseKeyword (options : List Nat)
  /-- Put the target card from your graveyard on the bottom of your library. -/
  | graveyardCardToLibraryBottom
  /-- Destroy all creatures. -/
  | destroyAllCreatures
  /-- The target's owner shuffles it into their library. -/
  | ownerShufflesIntoLibrary
  /-- Until end of turn, whenever the source deals combat damage to a player,
  draw two cards (Lyra). -/
  | grantCombatDamageDrawTwo
  /-- The source gets +X/+0 until end of turn, where X is the number of
  artifacts you control. -/
  | sourceGetsPowerPerArtifact
  /-- The target gets +X/+0 until end of turn, where X is the number of
  artifacts you control. -/
  | pumpPerArtifact
  /-- Put a +1/+1 counter on each creature you control with a +1/+1 counter. -/
  | plusOneOnEachWithPlusOne
  /-- Return each legal target to its owner's hand. -/
  | bounceEachTarget
  /-- Surveil 1. A noncreature, nonland card put into your graveyard this way
  goes to your hand. -/
  | surveilReturnNoncreatureNonland
  /-- Add {U} that can be spent only to cast a noncreature spell. -/
  | addBlueNoncreatureOnly
  /-- Tap the target. Put X stun counters on it (X of the loyalty cost). -/
  | tapAndStunX
  /-- You get an emblem with “Whenever you cast a spell, draw a card.” -/
  | emblemDrawOnCast
  /-- Empower Jace X, where X is the number of Islands you control. -/
  | empowerJacePerIsland
  /-- Until your next turn, whenever a creature attacks you or a planeswalker
  you control, it gets minus five power until end of turn. -/
  | attackersGetMinusFiveUntilYourTurn
  /-- Exile all but the bottom card of each opponent's library. -/
  | exileOpponentLibrariesButBottom
  /-- Up to one target creature gets minus four power and minus one toughness until your next turn. -/
  | minusFourMinusOneUntilYourTurn
  /-- Each player sacrifices a creature. If you did, create a 4/4 Beast. -/
  | eachPlayerSacrificesThenBeast
  /-- Each opponent discards two cards; draw a card for each opponent who
  didn't discard two nonland cards. -/
  | eachOpponentDiscardsTwoDrawPerShort
  /-- This deals `n` damage to each creature except tokens you control. -/
  | damageEachCreatureExceptYourTokens (n : Nat)
  /-- You get an emblem with “Creatures you control get +2/+2.” -/
  | emblemCreaturesGetTwoTwo
  /-- Untap each legal target land. -/
  | untapTargets
  /-- Until your next turn, whenever one or more creatures attack one of your
  opponents, they get +2/+2 and gain trample until end of turn. -/
  | attackersGetTwoTwoTrampleUntilYourTurn
  /-- Put a +1/+1 counter on the target for each land you control. -/
  | plusOnePerLand
  /-- You may sacrifice a creature. If you do, create a 4/4 Beast. -/
  | maySacrificeCreatureForBeast
  /-- This deals `n` damage to up to one target creature or planeswalker and
  `n` damage to target player. -/
  | damageUpToOneAndPlayer (n : Nat)
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
  | .damageEachPlayer n => s!"This deals {n} damage to each player"
  | .damageSourceAt _ n => s!"This deals {n} damage to {noun}"
  | .plusOneAt _ n => s!"Put {plusOnePlusOneCountersPhrase n} on {noun}"
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
  | .discardHand => "Discard your hand"
  | .drawPerCreatureYouControl => "Draw a card for each creature you control"
  | .extrapolate =>
    "You may reveal exactly two cards you own with different names from outside the game. An opponent chooses one of them. You put that card into your hand"
  | .sphinxsApproach =>
    "You may exile this spell and four cards named Sphinx's Approach from your graveyard. If you do, search your library for a Sphinx creature card, put it onto the battlefield, then shuffle"
  | .plusOneOnWizardTokensExceptRecent =>
    "Put a +1/+1 counter on each other Wizard token you control"
  | .damageEachOppCreatureAndPlaneswalker n =>
    s!"This deals {n} damage to each creature and planeswalker your opponents control"
  | .loseAbilitiesAt _ =>
    s!"{capitalizeAscii noun} loses all abilities until end of turn"
  | .powerDamageFromTo _ _ =>
    "Target creature you control deals damage equal to its power to that permanent"
  | .clashOfElements =>
    "Choose target nonland permanent. Its owner may put it on top of their library. If they do, this deals 2 damage to them. If they didn't put the card on top of their library, they put it on the bottom"
  | .entrustTheSpark =>
    "You may sacrifice a planeswalker. If you do, search your library for a planeswalker card, put it onto the battlefield, then shuffle"
  | .plusOnePerThreeGraveyardOnRecentIfFromGy =>
    "If this spell was cast from a graveyard, put a +1/+1 counter on each of them for every three cards in your graveyard"
  | .grantHasteToRecentTokens =>
    "It gains haste until end of turn"
  | .drawOneOrTwoIfNotFromHand =>
    "Draw a card. If this spell wasn't cast from your hand, draw two cards instead"
  | .destroyAt _ => s!"Destroy {noun}"
  | .plusOneOnCreaturesOfPlayerAt _ =>
    "Put a +1/+1 counter on each creature target player controls"
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
