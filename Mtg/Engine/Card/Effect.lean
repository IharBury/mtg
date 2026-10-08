import Mtg.Engine.Card.AbilityResolution
import Mtg.Engine.Card.FrcEffect
import Mtg.Engine.Card.SharedTrigger
import Mtg.Engine.Card.StaticAbility

/-!
# Unified one-shot effects (CR 608)

The `Effect` structure shared by spells, activated abilities, Saga
chapters, and triggered abilities, plus the shared `Resolution` vocabulary
they resolve through. `FraResolution` lives here so `Resolution` stays under
the C runtime constructor limit.
-/

namespace Mtg.Engine

/-!
Nested resolutions shared across sets. `Resolution.fra` is the single
constructor on `Resolution`, so this inductive stays off that tag and one
interpreter resolves spells, activated abilities, and triggered abilities.
-/

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
  /-- A Reality Fracture Commander resolution. -/
  | frc (e : FrcEffect)
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

/-- How an `Effect` resolves (CR 608). Shared shapes (`draw`, `scry`,
`onPermanent`, …) are used by spells, activated abilities, chapters, and
triggers. Spell-only and trigger leftovers stay nested so the C runtime
tag stays under the limit. Activated-ability leftovers live here so
`Resolution.toPhrase` and `Effect.mkAbility` cover every resolution. -/
inductive Resolution where
  /-- Draw `n` cards. -/
  | draw (n : Nat)
  /-- Scry `n`. -/
  | scry (n : Nat)
  /-- Affect a still-legal permanent target. -/
  | onPermanent (action : PermanentAction)
  /-- Affect the source if it is still on the battlefield. -/
  | onSource (action : PermanentAction)
  /-- You gain `n` life. -/
  | gainLife (n : Nat)
  /-- Recruit. -/
  | recruit
  /-- Amass Goblins `n`. -/
  | amassGoblins (n : Nat)
  /-- Create `n` tokens of this kind. -/
  | createTokens (kind : TokenKind) (n : Nat) (tapped : Bool := false)
  /-- Add these mana types. -/
  | addMana (types : Array ManaType)
  /-- Discard `n` cards. -/
  | discard (n : Nat)
  /-- Owner shuffles the source into their library. -/
  | shuffleSource
  /-- Search for a basic land, put it onto the battlefield tapped, then shuffle. -/
  | searchBasicLand
  /-- Search for a card with this land type, put it into your hand, then shuffle. -/
  | searchLandTypeToHand (landType : String)
  /-- Exile the top card and grant permission to play it. -/
  | exileTop
  /-- Attach this Equipment to the announced creature. -/
  | attach
  /-- Become this subtype with lands-you-control P/T. -/
  | becomeSubtypeWithLandsPT (subtype : String)
  /-- Return the source from the graveyard to the battlefield tapped. -/
  | returnFromGraveyardTapped
  /-- Return the source from the graveyard to its owner's hand. -/
  | returnFromGraveyardToHand
  /-- Creatures you control get +P/+T until end of turn. -/
  | creaturesYouControlPump (power toughness : Int)
  /-- Target player mills `n` cards. -/
  | mill (n : Nat)
  /-- Add one mana of any color. -/
  | addAnyColor
  /-- Return from the graveyard attached to the targeted creature. -/
  | returnFromGyAttach
  /-- Search for a basic land and put it into hand. -/
  | searchBasicLandToHand
  /-- Create X tokens of this kind. -/
  | createTokensX (kind : TokenKind)
  /-- Search two basics; one tapped, one to hand. -/
  | searchTwoBasicsSplit
  /-- These subtypes you control gain menace. -/
  | subtypesGainMenace (subtypes : Array String)
  /-- Exile then return at the next end step. -/
  | exileThenReturnNextEnd
  /-- Search a basic tapped, then behold this subtype to untap it. -/
  | searchBasicBeholdSubtypeUntap (subtype : String)
  /-- Two players each draw. -/
  | twoPlayersDraw
  /-- Discard a same-name legendary; draw two. -/
  | discardLegendarySameNameDraw
  /-- Deal `n` to any target. -/
  | dealDamageToAny (n : Nat)
  /-- Draw cards equal to the ability's recorded power (a sacrificed creature). -/
  | drawEqualToLastKnownPower
  /-- Draw a card for each burden counter on the source. -/
  | drawEqualToBurdenCounters
  /-- Arwen share. -/
  | arwenShare
  /-- Grant a combat-damage Treasure trigger. -/
  | grantCombatDamageCreateTreasure
  /-- Put a shadow counter. -/
  | putShadowCounter
  /-- Damage each opponent. -/
  | damageEachOpponent (n : Nat)
  /-- Choose two, destroy the rest. -/
  | chooseTwoDestroyRest
  /-- Black Gate unblockable. -/
  | blackGateUnblockable
  /-- Creatures you control gain this keyword. -/
  | teamGain (k : Keywords)
  /-- +1/+1 on each other permanent of this subtype. -/
  | plusOneOnEachOtherSubtype (subtype : String) (n : Nat)
  /-- Take an extra turn after this one. Power-up abilities can't be activated during it. -/
  | extraTurn
  /-- X +1/+1 counters on the source. -/
  | plusOneX
  /-- Each opponent discards; +1/+1 on the source. -/
  | eachOppDiscardThenPlusOne
  /-- Look at the top `n`; you may put a card of one of these types onto the battlefield. -/
  | lookAtTopPutTypes (n : Nat) (types : Array String)
  /-- Transform the source. -/
  | transform
  /-- Draw X cards. -/
  | drawX
  /-- Look at the top `n`; reveal an artifact to hand. -/
  | lookAtTopRevealArtifact (n : Nat)
  /-- The source connives. -/
  | connive
  /-- Add one mana of any color, spendable only on this subtype's spells or sources. -/
  | addAnyColorSpendOnlySubtype (subtype : String)
  /-- Add one mana of any color, spendable only to cast an artifact spell. -/
  | addAnyColorSpendOnlyArtifactSpell
  /-- Add two mana of any one color, spendable only on creature-source abilities. -/
  | addTwoAnyColorCreatureSources
  /-- Add {U} that can't be spent to cast a nonartifact spell. -/
  | addBlueCantNonartifact
  /-- Add X mana of any one color, where X is this creature's power. -/
  | addAnyColorEqualToSourcePower
  /-- Add four mana in any combination of colors. -/
  | addFourAnyCombination
  /-- Add two mana of any one color, spendable only on Equipment spells or equip. -/
  | addTwoAnyColorEquipment
  /-- Draw a card for each card you've discarded this turn. -/
  | drawPerDiscardedThisTurn
  /-- This deals `n` damage to each creature. -/
  | dealDamageToEachCreature (n : Nat)
  /-- Create that many tokens of this kind (X = removed +1/+1 counters). -/
  | createTokensEqualRemovedPlusOnes (kind : TokenKind)
  /-- Exile the top X cards; you may play them this turn. -/
  | exileTopXPlayThisTurn
  /-- Target player draws `n` cards. -/
  | targetPlayerDraw (n : Nat)
  /-- Copy target activated or triggered ability you control from this source type. -/
  | copyControlledAbility (fromCreature : Bool)
  /-- Create tokens equal to the number of permanents you control of this subtype. -/
  | createTokensEqualSubtype (kind : TokenKind) (subtype : String)
  /-- For each kind of counter on target permanent or player, give another of that kind. -/
  | proliferateEachKind
  /-- If this Equipment isn't a creature, it becomes a 0/0 Construct Hero with flying. -/
  | equipmentBecomesConstructHero
  /-- Look at the top `n`; you may reveal a card of this subtype and put it into your hand. -/
  | lookAtTopRevealSubtype (n : Nat) (subtype : String)
  /-- Mill `n`. You may put a card of this subtype or an enchantment into your hand. -/
  | millThenPutSubtypeOrEnchantment (n : Nat) (subtype : String)
  /-- Create The Tiger God token. -/
  | createTigerGod
  /-- Choose odd or even. Destroy each other creature with that mana value. -/
  | chooseOddOrEvenDestroy
  /-- Return this from your graveyard with a finality counter. Then you may attach an Equipment. -/
  | returnFromGyFinalityAttach
  /-- Reveal the top card. If it's an artifact, draw a card. -/
  | revealTopDrawIfArtifact
  /-- Target artifact you control becomes a copy of a second until EOT, except it isn't legendary. -/
  | copyArtifactYouControlNotLegendary
  /-- Until end of turn, this becomes these types with base P/T and these keywords. -/
  | becomeTypes (types : Array String) (power toughness : Int) (k : Keywords)
  /-- When you next cast an instant or sorcery with MV ≤ this's power this turn, copy it. -/
  | nextInstantSorceryCopyIfMvAtMostSourcePower
  /-- Harness this Infinity Stone. -/
  | harnessInfinityStone
  /-- Target permanent you control of this subtype connives. -/
  | targetSubtypeConnives (subtype : String)
  /-- Empower Jace `n` (Reality Fracture): put `n` loyalty counters on a Jace
  planeswalker token you control, creating one first if you control none. -/
  | empowerJace (n : Nat)
  /-- Surveil `n` (CR 701.25). -/
  | surveil (n : Nat)
  /-- Mill `n` cards (CR 701.13). -/
  | millSelf (n : Nat)
  /-- You may discard a card. If you do, draw `n` cards. -/
  | mayDiscardDraw (n : Nat)
  /-- Create X tokens, where X is the life you gained this turn. -/
  | createTokensLifeGained (kind : TokenKind)
  /-- The target opponent sacrifices a creature or planeswalker with the
  greatest mana value among those they control. -/
  | oppSacrificesGreatestMv
  /-- Creatures without flying can't block this turn. -/
  | creaturesWithoutFlyingCantBlock
  /-- The targeted player loses `n` life. -/
  | targetPlayerLoseLife (n : Nat)
  /-- The controller of the targeted permanent loses `n` life. -/
  | controllerOfTargetLosesLife (n : Nat)
  /-- Return the targeted spell to its owner's hand. -/
  | returnTargetSpell
  /-- Each creature you control becomes prepared. -/
  | eachCreatureYouControlBecomesPrepared
  /-- Deal `n` damage to the target. If excess damage was dealt, empower Jace
  that much. -/
  | damageThenEmpowerExcess (n : Nat)
  /-- Until end of turn, loyalty abilities of Jace planeswalkers you control
  may be activated any time you could cast an instant. -/
  | jaceLoyaltyAtInstantSpeed
  /-- The source becomes a copy of the target creature until end of turn, and
  the legend rule doesn't apply to permanents you control this turn. -/
  | becomeCopyLegendRuleOff
  /-- For each creature the target player controls, create a token copy with
  haste that is sacrificed at end step unless you control a planeswalker. -/
  | copyEachCreatureOfTargetPlayer
  /-- Proliferate X times, where X is the number of planeswalker types among
  planeswalkers you control (Tam, the Possibility). -/
  | proliferatePlaneswalkerTypesTimes
  /-- When you next cast an instant or sorcery spell this turn, copy it. -/
  | copyNextInstantSorceryThisTurn
  /-- Return this card from your graveyard to the battlefield with a
  finality counter on it. -/
  | returnFromGyWithFinality
  /-- The first target deals damage equal to its power (or loyalty) to the
  second target, checked as the spell resolves (Compel Brutality). -/
  | firstDealsStatDamageToSecond (useLoyalty : Bool)
  /-- Exile the top card of your library. You may cast it. If you don't, this
  deals `n` damage to each opponent (Chandra, Torch of Defiance). -/
  | exileTopMayCastElseDamageOpponents (n : Nat)
  /-- You get an emblem with “Whenever you cast a spell, this emblem deals
  `n` damage to any target.” -/
  | emblemCastSpellDamage (n : Nat)
  /-- Nested resolution kept off this inductive so the C runtime tag stays under the limit. -/
  | fra (r : FraResolution)
  /-- Apply each resolution in the given list, in order. -/
  | sequence (rs : List Resolution)
  /-- Spell-only resolution leftover. -/
  | spell (r : SpellResolution)
  /-- Trigger leftover (timing stays on the shared trigger effect). -/
  | trigger (e : SharedTrigger)
deriving Repr, Inhabited, BEq

/-- Unified one-shot effect for spells, activated abilities, Saga chapters,
and triggered abilities. Targeting, printed wording, and resolution live
here so Game has one apply path. -/
structure Effect where
  targeting : EffectTargeting := .of .none
  allowsZeroTargets : Bool := false
  maxTargets : Nat := 0
  dividedDamage : Option (Nat × Nat) := none
  spellCastKind : SpellCastKind := .extraLand
  abilityCastKind : AbilityCastKind := .other
  preferAsDefaultMode : Bool := false
  resolution : Resolution := .draw 0
  phrase : String := ""
deriving Repr, Inhabited, BEq

namespace Effect

/-- Whom this effect may target (CR 115.1 / 601.2c). -/
def targetKind (e : Effect) : EffectTargetKind :=
  e.targeting.kind

/-- How many targets must be announced (CR 601.2c). -/
def targetCount (e : Effect) : Nat :=
  e.targeting.targetCount

/-- True when announcing this effect requires choosing a target. -/
def requiresTarget (e : Effect) : Bool :=
  e.targeting.requiresTarget

/-- Upper bound on announced targets. `0` on `maxTargets` means `targetCount`. -/
def maxTargetCount (e : Effect) : Nat :=
  if e.maxTargets == 0 then e.targetCount else e.maxTargets

/-- Demonstration-agent category for a spell mode. -/
def castKind (e : Effect) : SpellCastKind :=
  e.spellCastKind

/-- Demonstration-agent category for an activated-ability mode. -/
def abilityKind (e : Effect) : AbilityCastKind :=
  e.abilityCastKind

/-- Recover a Saga chapter stored on this effect, if any. -/
def asChapter? (e : Effect) : Option ChapterResolution :=
  match e.resolution with
  | .trigger (.chapter _ ce) => some ce
  | _ => none

/-- Recover the leftover shared trigger stored on this effect, if any. -/
def asTrigger? (e : Effect) : Option SharedTrigger :=
  match e.resolution with
  | .trigger te => some te
  | _ => none

/-- Oracle-style reminder text. -/
def toNotation (e : Effect) : String :=
  e.phrase

instance : HasTargeting Effect where
  targeting e := e.targeting

instance : ToString Effect where
  toString := toNotation

end Effect

namespace Resolution

/-- Nested `sequence` constructors, left to right. -/
def flatten : Resolution → List Resolution
  | .sequence rs => rs.flatMap flatten
  | r => [r]

/-- `toPhrase` of one resolution, with `sequence` phrasing each step. Adding a
constructor is a compile error here rather than silently skipping the new
effect.

Keep this non-recursive: recursion through `List.map` makes a definition
well-founded, and Lean then compiles a match splitter over every constructor,
which clang takes many seconds to optimize. -/
private def phraseWith (r : Resolution) (noun : String)
    (sequence : List Resolution → String) : String :=
  match r with
  | .draw n =>
    s!"Draw {cardPhrase n}"
  | .scry n =>
    s!"Scry {n}"
  | .onPermanent (.dealDamage n) =>
    s!"This creature deals {n} damage to {noun}"
  | .onPermanent action =>
    PermanentAction.toNotation action noun (sentence := true)
  | .onSource action =>
    PermanentAction.toNotation action "this creature" (sentence := true)
  | .gainLife n =>
    s!"You gain {n} life"
  | .recruit =>
    "Recruit"
  | .amassGoblins n =>
    s!"Amass Goblins {n}"
  | .createTokens kind n tapped =>
    capitalizeAscii (TokenKind.createPhrase kind n (tapped := tapped))
  | .addMana types =>
    s!"Add {manaSymbolsText types}"
  | .discard n =>
    s!"Discard {cardPhrase n}"
  | .shuffleSource =>
    "Shuffle this into its owner's library"
  | .searchBasicLand =>
    capitalizeAscii (searchBasicLandTappedPhrase "your")
  | .searchLandTypeToHand t =>
    capitalizeAscii (searchLibraryToHandPhrase s!"a {t} card")
  | .exileTop =>
    "Exile the top card of your library. You may play it until the end of your next turn"
  | .attach =>
    s!"Attach this Equipment to {noun}"
  | .becomeSubtypeWithLandsPT subtype =>
    s!"This enchantment becomes {indefinite subtype} {subtype} creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\""
  | .returnFromGraveyardTapped =>
    "Return this card from your graveyard to the battlefield tapped"
  | .returnFromGraveyardToHand =>
    "Return this card from your graveyard to your hand"
  | .creaturesYouControlPump p t =>
    s!"Creatures you control get {signedStat p}/{signedStat t} until end of turn"
  | .mill n =>
    s!"{noun} mills {n} cards"
  | .addAnyColor =>
    "Add one mana of any color"
  | .returnFromGyAttach =>
    s!"Return this card from your graveyard to the battlefield attached to {noun}"
  | .searchBasicLandToHand =>
    capitalizeAscii (searchLibraryToHandPhrase "a basic land card")
  | .createTokensX kind =>
    s!"Create X {kind.pluralNoun}"
  | .searchTwoBasicsSplit =>
    "Search your library for up to two basic land cards, reveal them, put one onto the battlefield tapped and the other into your hand, then shuffle"
  | .subtypesGainMenace subtypes =>
    s!"{StaticAbility.joinedSubtypes subtypes StaticAbility.pluralSubtype} you control gain menace until end of turn"
  | .exileThenReturnNextEnd =>
    "Exile up to two other target nonland permanents you control. Return those cards to the battlefield under their owner's control at the beginning of the next end step"
  | .searchBasicBeholdSubtypeUntap subtype =>
    s!"{capitalizeAscii (searchBasicLandTappedPhrase "your")}. You may behold {indefinite subtype} {subtype}. If you do, untap that land"
  | .twoPlayersDraw =>
    "Two target players each draw a card"
  | .discardLegendarySameNameDraw =>
    "Draw two cards"
  | .dealDamageToAny n =>
    s!"This creature deals {n} damage to any target"
  | .drawEqualToLastKnownPower =>
    "Draw cards equal to the sacrificed creature's power"
  | .arwenShare =>
    "Another target creature gains indestructible until end of turn. Put a +1/+1 counter and a lifelink counter on that creature and a +1/+1 counter and a lifelink counter on Arwen"
  | .grantCombatDamageCreateTreasure =>
    "Until end of turn, target creature gains \"Whenever this creature deals combat damage to a player, create a Treasure token.\""
  | .putShadowCounter =>
    "Put a shadow counter on target creature. For as long as that creature has a shadow counter on it, it's a Wraith in addition to its other types"
  | .damageEachOpponent n =>
    s!"This deals {n} damage to each opponent"
  | .chooseTwoDestroyRest =>
    "Choose up to two creatures, then destroy the rest"
  | .blackGateUnblockable =>
    "Choose a player with the most life or tied for most life. Target creature can't be blocked by creatures that player controls this turn"
  | .drawEqualToBurdenCounters =>
    "Draw a card for each burden counter on this"
  | .teamGain k =>
    s!"Creatures you control gain {k.joinedAnd} until end of turn"
  | .plusOneOnEachOtherSubtype subtype n =>
    s!"Put {plusOnePlusOneCountersPhrase n} on each other {subtype} you control"
  | .extraTurn =>
    "Take an extra turn after this one. During that turn, power-up abilities can't be activated"
  | .plusOneX =>
    "Put X +1/+1 counters on this"
  | .eachOppDiscardThenPlusOne =>
    "Each opponent discards a card. Put a +1/+1 counter on this"
  | .lookAtTopPutTypes n types =>
    let listed := orJoin types.toList
    let art := indefinite (types[0]?.getD "")
    s!"Look at the top {n} cards of your library. You may put {art} {listed} card from among them onto the battlefield. If it's a double-faced card, you may transform it. {restOnBottomRandomPhrase}"
  | .transform =>
    "Transform this"
  | .drawX =>
    "Draw X cards"
  | .lookAtTopRevealArtifact n =>
    s!"Look at the top {n} cards of your library. You may reveal an artifact card from among them and put it into your hand. {restOnBottomRandomPhrase}"
  | .connive =>
    "This creature connives"
  | .addAnyColorSpendOnlySubtype subtype =>
    s!"Add one mana of any color. Spend this mana only to cast {indefinite subtype} {subtype} spell or to activate an ability of {indefinite subtype} {subtype} source"
  | .addAnyColorSpendOnlyArtifactSpell =>
    "Add one mana of any color. Spend this mana only to cast an artifact spell"
  | .addTwoAnyColorCreatureSources =>
    "Add two mana of any one color. Spend this mana only to activate abilities of creature sources"
  | .addBlueCantNonartifact =>
    "Add {U}. This mana can't be spent to cast a nonartifact spell"
  | .addAnyColorEqualToSourcePower =>
    "Add X mana of any one color, where X is this creature's power"
  | .addFourAnyCombination =>
    "Add four mana in any combination of colors"
  | .addTwoAnyColorEquipment =>
    "Add two mana of any one color. Spend this mana only to cast Equipment spells or activate equip abilities"
  | .drawPerDiscardedThisTurn =>
    "Draw a card for each card you've discarded this turn"
  | .dealDamageToEachCreature n =>
    s!"This deals {n} damage to each creature"
  | .createTokensEqualRemovedPlusOnes kind =>
    s!"Create that many {kind.pluralNoun}"
  | .exileTopXPlayThisTurn =>
    "Exile the top X cards of your library, where X is this creature's power. You may play those cards this turn"
  | .targetPlayerDraw n =>
    s!"{noun} draws {cardPhrase n}"
  | .copyControlledAbility fromCreature =>
    let src := if fromCreature then "a creature" else "an artifact"
    s!"Copy target activated or triggered ability you control from {src} source. You may choose new targets for the copy"
  | .createTokensEqualSubtype kind subtype =>
    s!"Create X {kind.pluralNoun}, where X is the number of {subtype}s you control"
  | .proliferateEachKind =>
    "For each kind of counter on target permanent or player, give that permanent or player another counter of that kind"
  | .equipmentBecomesConstructHero =>
    "If this Equipment isn't a creature, it becomes a 0/0 Construct Hero artifact creature with flying and \"This creature gets +1/+1 for each artifact you control\" until end of turn"
  | .lookAtTopRevealSubtype n subtype =>
    s!"Look at the top {n} cards of your library. You may reveal a {subtype} card from among them and put it into your hand. Put the rest on the bottom of your library in any order"
  | .millThenPutSubtypeOrEnchantment n subtype =>
    s!"Mill {n} cards. You may put {indefinite subtype} {subtype} or enchantment card from among those cards into your hand"
  | .createTigerGod =>
    "Create The Tiger God, a legendary 4/4 green Cat God creature token with \"The Tiger God can't be blocked by more than one creature.\""
  | .chooseOddOrEvenDestroy =>
    "Choose odd or even. Destroy each other creature with mana value of the chosen quality"
  | .returnFromGyFinalityAttach =>
    "Return this card from your graveyard to the battlefield with a finality counter on him. Then you may attach an Equipment you control to him"
  | .revealTopDrawIfArtifact =>
    "Reveal the top card of your library. If it's an artifact card, draw a card"
  | .copyArtifactYouControlNotLegendary =>
    "Target artifact you control becomes a copy of a second target artifact you control until end of turn, except it isn't legendary"
  | .becomeTypes types p t k =>
    let joined :=
      if k.reach && k.vigilance then "reach and vigilance"
      else k.joinedAnd
    let typeWords := String.intercalate " " types.toList
    let art := indefinite (types[0]?.getD "")
    s!"Until end of turn, this becomes {art} {typeWords} with base power and toughness {p}/{t} and gains {joined}"
  | .nextInstantSorceryCopyIfMvAtMostSourcePower =>
    "When you next cast an instant or sorcery spell with mana value less than or equal to this creature's power this turn, copy that spell. You may choose new targets for the copy"
  | .harnessInfinityStone =>
    "Harness this"
  | .targetSubtypeConnives subtype =>
    s!"Target {subtype} you control connives"
  | .empowerJace n =>
    s!"Empower Jace {n}"
  | .surveil n =>
    s!"Surveil {n}"
  | .millSelf n =>
    s!"Mill {cardPhrase n}"
  | .mayDiscardDraw n =>
    s!"You may discard a card. If you do, draw {cardPhrase n}"
  | .createTokensLifeGained kind =>
    s!"Create X {kind.pluralNoun}, where X is the amount of life you gained this turn"
  | .oppSacrificesGreatestMv =>
    s!"{capitalizeAscii noun} sacrifices a creature or planeswalker with the greatest mana value among creatures and planeswalkers they control"
  | .creaturesWithoutFlyingCantBlock =>
    "Creatures without flying can't block this turn"
  | .targetPlayerLoseLife n =>
    s!"{noun} loses {n} life"
  | .controllerOfTargetLosesLife n =>
    s!"Its controller loses {n} life"
  | .returnTargetSpell =>
    s!"Return {noun} to its owner's hand"
  | .eachCreatureYouControlBecomesPrepared =>
    "Each creature you control becomes prepared"
  | .damageThenEmpowerExcess n =>
    s!"This deals {n} damage to {noun}. If excess damage was dealt to that permanent this way, empower Jace X, where X is that excess damage"
  | .jaceLoyaltyAtInstantSpeed =>
    "Until end of turn, you may activate loyalty abilities of Jace planeswalkers you control on any player's turn any time you could cast an instant"
  | .exileTopMayCastElseDamageOpponents n =>
    s!"Exile the top card of your library. You may cast that card. If you don't, this deals {n} damage to each opponent"
  | .emblemCastSpellDamage n =>
    s!"You get an emblem with \"Whenever you cast a spell, this emblem deals {n} damage to any target.\""
  | .firstDealsStatDamageToSecond useLoyalty =>
    if useLoyalty then
      "Target planeswalker you control deals damage equal to its loyalty to target creature or planeswalker an opponent controls"
    else
      "Target creature you control deals damage equal to its power to target creature or planeswalker an opponent controls"
  | .returnFromGyWithFinality =>
    "Return this card from your graveyard to the battlefield with a finality counter on it"
  | .copyNextInstantSorceryThisTurn =>
    "When you next cast an instant or sorcery spell this turn, copy that spell. You may choose new targets for the copy"
  | .proliferatePlaneswalkerTypesTimes =>
    "Proliferate X times, where X is the number of planeswalker types among planeswalkers you control"
  | .copyEachCreatureOfTargetPlayer =>
    s!"For each creature {noun} controls, create a token that's a copy of that creature, except it has haste and \"At the beginning of the end step, if you don't control a planeswalker, sacrifice this creature.\""
  | .becomeCopyLegendRuleOff =>
    s!"This land becomes a copy of {noun} until end of turn. The \"legend rule\" doesn't apply to permanents you control this turn"
  | .fra r =>
    FraResolution.toPhrase r noun
  | .sequence rs =>
    sequence rs
  | .spell r =>
    SpellResolution.toPhrase r noun
  | .trigger _ =>
    ""

/-- Oracle-style reminder from targeting and resolution. Source-deals-damage
uses the creature as the subject rather than the generic `PermanentAction`
wording. -/
def toPhrase (r : Resolution) (noun : String) : String :=
  match r with
  | .sequence rs => String.intercalate ". " (rs.map (fun step => toPhrase step noun))
  | r => phraseWith r noun fun _ => ""

/-- One spell step as a shared resolution. `sequence` is handled by `ofSpell`. -/
def ofSpellStep : SpellResolution → Resolution
  | .draw n .you => .draw n
  | .draw n .targetPlayer => .targetPlayerDraw n
  | .scry n => .scry n
  | .onPermanent a => .onPermanent a
  | .discard n => .discard n
  | .loseLife n .you => .fra (.loseLife n)
  | .loseLife n .targetPlayer => .targetPlayerLoseLife n
  | .loseLife n .controllerOfTarget => .controllerOfTargetLosesLife n
  | .gainLife n .you => .gainLife n
  | .recruit => .recruit
  | .surveil n => .surveil n
  | .teamGain k => .teamGain k
  | .returnTargetToHand .spell => .returnTargetSpell
  | .returnTargetToHand .graveyard => .fra .returnFromGyToHand
  | .createTokens kind n .you => .createTokens kind n
  | .creaturesPump p t .youControl => .creaturesYouControlPump p t
  | .createTokensX kind => .createTokensX kind
  | .dealDamageToEachCreature n => .dealDamageToEachCreature n
  | .sequence rs => .sequence (rs.map ofSpellStep)
  | r => .spell r

/-- Lift a spell resolution onto the shared `Resolution` vocabulary. -/
def ofSpell (r : SpellResolution) : Resolution :=
  match r with
  | .sequence rs => .sequence ((rs.map ofSpell).flatMap flatten)
  | r => ofSpellStep r

/-- A shared resolution as a spell step, when every part of it is one. -/
def toSpellStep : Resolution → Option SpellResolution
  | .draw n => some (.draw n)
  | .scry n => some (.scry n)
  | .onPermanent a => some (.onPermanent a)
  | .discard n => some (.discard n)
  | .fra (.loseLife n) => some (.loseLife n .you)
  | .fra .returnFromGyToHand => some (.returnTargetToHand .graveyard)
  | .gainLife n => some (.gainLife n)
  | .recruit => some .recruit
  | .surveil n => some (.surveil n)
  | .teamGain k => some (.teamGain k)
  | .targetPlayerLoseLife n => some (.loseLife n .targetPlayer)
  | .controllerOfTargetLosesLife n => some (.loseLife n .controllerOfTarget)
  | .returnTargetSpell => some .returnTargetToHand
  | .amassGoblins n => some (.amassGoblins n)
  | .createTokens kind n false => some (.createTokens kind n)
  | .creaturesYouControlPump p t => some (.creaturesPump p t)
  | .createTokensX kind => some (.createTokensX kind)
  | .dealDamageToEachCreature n => some (.dealDamageToEachCreature n)
  | .targetPlayerDraw n => some (.draw n .targetPlayer)
  | .spell .unrecognized => none
  | .spell (.sequence _) => none
  | .spell r => some r
  | _ => none

/-- The spell view of `r`. A sequence is a spell sequence only when every
step lifts; otherwise it stays unrecognized, as before. -/
def toSpell (r : Resolution) : Option SpellResolution :=
  match r with
  | .sequence rs =>
    match rs.flatMap flatten |>.mapM toSpellStep with
    | some steps => some (.sequence steps)
    | none => none
  | r => toSpellStep r

/-- Recover the leftover spell resolution (common shapes lift back). -/
def _root_.Mtg.Engine.Effect.spellResolution (e : Effect) : SpellResolution :=
  match e.resolution with
  | .onSource a => .onPermanent a
  | .createTokens kind n _ => .createTokens kind n
  | r => r.toSpell.getD .unrecognized

/-- Store a shared trigger on `Resolution`. Timing stays on the nested
effect so leftover family events remain recoverable. -/
def ofSharedTrigger (e : SharedTrigger) : Resolution :=
  .trigger e

/-- True when resolving `r` as a spell or Saga chapter would do nothing.
Chapter payloads are resolved by `applyChapterEffect`. -/
partial def doesNothingAsSpell (r : Resolution) : Bool :=
  match r with
  | .sequence rs => rs.any doesNothingAsSpell
  | .shuffleSource | .gainLife _ | .recruit | .addMana _ | .discard _ | .onSource _ => false
  | .fra _ | .empowerJace _ | .surveil _ | .millSelf _ | .mayDiscardDraw _
  | .createTokensLifeGained _ | .oppSacrificesGreatestMv
  | .createTigerGod | .extraTurn | .drawEqualToBurdenCounters
  | .creaturesWithoutFlyingCantBlock | .targetPlayerLoseLife _
  | .controllerOfTargetLosesLife _ | .returnTargetSpell | .chooseOddOrEvenDestroy
  | .eachCreatureYouControlBecomesPrepared | .damageThenEmpowerExcess _
  | .exileTopMayCastElseDamageOpponents _ | .emblemCastSpellDamage _
  | .firstDealsStatDamageToSecond _ | .returnFromGyWithFinality
  | .copyNextInstantSorceryThisTurn | .proliferatePlaneswalkerTypesTimes
  | .copyEachCreatureOfTargetPlayer | .becomeCopyLegendRuleOff
  | .teamGain _ | .jaceLoyaltyAtInstantSpeed | .drawEqualToLastKnownPower => false
  | .trigger (.chapter _ _) => false
  | .searchBasicLand | .searchLandTypeToHand _ | .searchBasicLandToHand | .exileTop => false
  | .spell .unrecognized => true
  | r => ({ resolution := r } : Effect).spellResolution == .unrecognized

/-- True when resolving `r` as an activated ability would do nothing. -/
partial def doesNothingAsActivated (r : Resolution) : Bool :=
  match r with
  | .spell .unrecognized => true
  | .trigger .exileOppNonlandEachUntilLeaves => false
  | .trigger (.chapter _ _) => false
  | .trigger _ => true
  | .sequence rs => rs.any doesNothingAsActivated
  | _ => false

end Resolution

end Mtg.Engine
