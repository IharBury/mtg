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

end FraResolution

end Mtg.Engine
