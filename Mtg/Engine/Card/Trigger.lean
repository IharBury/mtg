import Mtg.Engine.Card.Counter
import Mtg.Engine.Card.Effect
import Mtg.Engine.Card.TriggerEvent

/-!
# Triggered-ability core (CR 603)

The unified `TriggeredAbility` carrier plus its stack/resolution metadata:
`TriggerResolution`, `TriggerTiming`, the events each shared trigger
watches, and the timing of each shared trigger.
-/

namespace Mtg.Engine

/-- A triggered ability the engine currently understands (CR 603).
One constructor keeps the C runtime tag under the limit; leftover printed
names are aliases of `triggered`. -/
inductive TriggeredAbility where
  /-- Reusable trigger: when it fires, a unified `Effect`, and optional
  intervening conditions / wording filters. -/
  | triggered (when : SharedTriggerWhen) (effect : Effect)
      (opts : SharedTriggerOpts := {})
deriving Repr, Inhabited, BEq

namespace TriggeredAbility

/-- English for “divided as you choose among …” (CR 601.2d). -/
def dividedAmong (maxTargets : Nat) : String :=
  if maxTargets == 3 then "one, two, or three targets"
  else if maxTargets == 1 then "one target"
  else s!"up to {maxTargets} targets"

/-- How a triggered ability selects targets when it is put on the stack
(CR 603.3d / 601.2c). Spell and activated-ability targeting use the same
`EffectTargetKind` constructors. -/
abbrev TriggerTargetKind := EffectTargetKind

/-- How `TriggerResolution.sacrifice` moves the source when `what` is
`.source` or `.sacrificedSource`. -/
inductive SacrificeSourceHow where
  /-- Sacrifice it: “{name} is sacrificed”. -/
  | isSacrificed
  /-- Sacrifice it: “{player} sacrifices {name}”. -/
  | controllerSacrifices
  /-- Move it to the graveyard and log that it is sacrificed, without the
  token-sacrifice trigger `isSacrificed` uses. -/
  | movedAsSacrificed
deriving Repr, Inhabited, BEq

/-- When `TriggerResolution.if` and `TriggerResolution.ifElse` choose a branch. -/
inductive TriggerIf where
  /-- You don't control a legendary creature. -/
  | noLegendaryCreature
  /-- An earlier step removed a hope counter. -/
  | removedHope
  /-- The source is on the battlefield and has no hope counters. -/
  | noHopeOnSource
  /-- You have drawn at least `n` cards this turn. -/
  | drewAtLeast (n : Nat)
  /-- An earlier step dealt damage to a permanent of this subtype. -/
  | dealtDamageToSubtype (subtype : String)
  /-- You attacked with this subtype, or one entered under your control this turn. -/
  | attackedOrEntered (subtype : String)
  /-- At least `n` loyalty counters were removed to activate the ability.
  That count is the ability's last-known power. -/
  | removedLoyaltyAtLeast (n : Nat)
  /-- You control at least `n` lands. -/
  | landsAtLeast (n : Nat)
  /-- You don't control a planeswalker. -/
  | noPlaneswalker
  /-- You control at least `n` Forests other than the one that caused this. -/
  | otherForestsAtLeast (n : Nat)
  /-- An earlier step returned a permanent to its owner's hand. -/
  | returnedPermanent
  /-- `noteResolveThisTurn` recorded ordinal `n`. -/
  | nthResolve (n : Nat)
  /-- You controlled the creature an earlier step destroyed. -/
  | youControlledDestroyed
  /-- You have an enduring story, and an earlier step discarded your hand. -/
  | enduringStoryNoted
  /-- You control at least `n` Bears. -/
  | bearsAtLeast (n : Nat)
  /-- You control at least `n` permanents of this subtype. -/
  | controlsAtLeast (subtype : String) (n : Nat)
  /-- An earlier `.sacrifice .source .noted` sacrificed the source. -/
  | sourceWasSacrificed
  /-- An earlier `.sacrifice .plan .forReflexive` sacrificed the Plan.
  Checking this consumes that note. -/
  | planWasSacrificed
  /-- The source has at least `n` quest counters. -/
  | questAtLeast (n : Nat)
  /-- An earlier step attached Equipment to a creature that is still in play. -/
  | equipmentAttached
  /-- `.mill` noted `.opponentsMilled`: an opponent milled a card. -/
  | opponentsMilled
  /-- You control a Hero other than the source. -/
  | anotherHero
  /-- Your library has no cards. -/
  | libraryEmpty
  /-- Your library still has a card. -/
  | libraryNotEmpty
  /-- This Equipment is attached to a legendary creature you control. -/
  | equippedLegendaryYouControl
  /-- The target is a creature. -/
  | targetIsCreature
  /-- The target is a planeswalker. -/
  | targetIsPlaneswalker
  /-- Your graveyard has at least `n` creature cards. -/
  | creatureCardsInGraveyardAtLeast (n : Nat)
  /-- The targeted permanent has this subtype and is not the source. -/
  | targetIsAnotherSubtype (subtype : String)
  /-- You have scried or surveilled this turn. -/
  | scriedOrSurveilledThisTurn
  /-- The artifact an earlier step put from hand is Equipment. -/
  | putArtifactIsEquipment
  /-- The card `revealLibrary .untilCreature` revealed has mana value at
  most the lands the controller controls. Outside that resolution, the
  condition does not hold. -/
  | revealedManaValueAtMostLands
  /-- The source is on the battlefield and harnessed.
  A missing source does nothing. An unharnessed source is reported. -/
  | sourceHarnessed
  /-- An artifact entered the battlefield under your control this turn.
  None did is reported. -/
  | artifactEnteredThisTurn
  /-- The source's power as this ability resolves is at least `n`.
  A source that has left uses its last-known power.
  Power below 4 is reported as Viv Vision's. -/
  | sourcePowerAtLeast (n : Nat)
  /-- Equipment is attached to the source, or its last-known power is
  positive when the source has left. None is reported. -/
  | attachedEquipment
  /-- The source is on the battlefield and attacking. A missing source
  does not hold. -/
  | sourceAttacking
  /-- An earlier Enrage trigger noted an additional combat phase.
  Checking this consumes that note. -/
  | enrageGrantsCombat
  /-- The creature that caused this has greater power or toughness than
  the source. An announced permanent is used when one was chosen;
  otherwise the recorded cause. A missing source is reported. No cause
  does not hold. The source itself does not hold. -/
  | causeGreaterPowerOrToughness
  /-- Mana was spent to cast the triggering spell.
  Spending none does not hold. -/
  | manaSpent
deriving Repr, Inhabited, BEq

/-- What `TriggerResolution.pay` pays. -/
inductive CostSelector where
  /-- Pay these mana symbols.
  `{n}` is `.mana #[.generic n]`. `{1}{G}{U}` is
  `.mana #[.generic 1, .colored .green, .colored .blue]`. -/
  | mana (symbols : Array ManaSymbol)
  /-- Sacrifice another creature. Its power is noted for
  `TriggerResolution.putCounters .plusOneSacrificedPower`. -/
  | anotherCreature
  /-- Sacrifice another creature or artifact. -/
  | anotherCreatureOrArtifact
  /-- Sacrifice an artifact, or discard a card. -/
  | artifactOrDiscard
  /-- Sacrifice an artifact, or discard a nonland card. -/
  | artifactOrDiscardNonland
deriving Repr, Inhabited, BEq

/-- Which MSH reflexive `TriggerResolution.queueReflexive` queues.
`toNat` is the index `FraResolution.mshReflexive` matches. -/
inductive TriggerReflexiveKind where
  /-- Another target nonattacking creature you control gains indestructible
  until end of turn.
  `.grant (.keywords Keyword.indestructible) .target`. -/
  | grantIndestructible
  /-- Choose up to three Trick Arrows modes.
  `.chooseModes TriggerResolution.trickArrowModes .alreadyChosen`. -/
  | trickArrows
  /-- Put an indestructible counter on target creature you control.
  `.putCounters (.ofKind .indestructible) .permanent`. -/
  | indestructibleCounter
  /-- You control target opponent during their next turn.
  `.gainControl .duringNextTurn`. -/
  | controlOpponent
  /-- Target opponent exiles the top five cards of their library. You may
  cast up to two spells from among the exiled cards without paying their
  mana costs.
  `.exile (.opponentTop 5) (.mayCastUpTo 2)`. -/
  | exileTopFive
  /-- Return target creature card from your graveyard to the battlefield
  tapped and attacking with a finality counter on it.
  `.put .creatureCard .tapped (.entering [.attacking, .counter .finality])`. -/
  | returnAttacking
  /-- Destroy target nonland permanent an opponent controls.
  `.destroy .target`. -/
  | destroyOppNonland
  /-- Deal damage equal to the +1/+1 counters on the source to any other
  target.
  `.dealDamage .plusOneCounters .target`. -/
  | countersDamage
  /-- Target creature with haste can't be blocked this turn except by
  creatures with haste.
  `.cant (.beBlockedExceptByHaste .target)`. -/
  | hasteUnblockable
  /-- Return up to two target instant and/or sorcery cards from your
  graveyard to your hand.
  `.returnToHand (.graveyardInstants 2)`. -/
  | returnInstants
  /-- Put a +1/+1 counter on target creature.
  `.putCounters (.ofKind .plusOnePlusOne) .permanent`. -/
  | plusOne
deriving Repr, Inhabited, BEq

namespace TriggerReflexiveKind

/-- The index `FraResolution.mshReflexive` matches. -/
def toNat : TriggerReflexiveKind → Nat
  | .grantIndestructible => 0
  | .trickArrows => 2
  | .indestructibleCounter => 3
  | .controlOpponent => 4
  | .exileTopFive => 5
  | .returnAttacking => 6
  | .destroyOppNonland => 7
  | .countersDamage => 8
  | .hasteUnblockable => 9
  | .returnInstants => 11
  | .plusOne => 12

end TriggerReflexiveKind

/-- Which player `ObjectSelector.player` names, who
`TriggerResolution.draw` draws for, and who
`TriggerResolution.loseLife` loses life. -/
inductive PlayerSelector where
  /-- Each opponent, or the announced opponent when the ability targets.
  `n` damage to each opponent is `.dealDamage (.fixed n) (.player .eachOpponent)`.
  Each opponent draws `n` is `.draw (.fixed n) .eachOpponent`.
  Each opponent loses `n` life is `.loseLife (.fixed n) .eachOpponent`. -/
  | eachOpponent
  /-- The announced opponent.
  `n` damage to that player is `.dealDamage (.fixed n) (.player .targetOpponent)`.
  That player loses `n` life is `.loseLife (.fixed n) .targetOpponent`. -/
  | targetOpponent
  /-- The controller of the ability.
  That player draws `n` is `.draw (.fixed n)` (`.you`).
  That player loses `n` life is `.loseLife (.fixed n)`. -/
  | you
  /-- The targeted opponent may have the controller draw a card.
  Declining mills X cards, where X is the influence counters on the source,
  and that player loses life equal to the total mana value of those cards.
  An earlier step must have recorded the offer.
  `.draw (.fixed 1) .opponentHasYou`. -/
  | opponentHasYou
  /-- The controller of the creature the source enchants.
  Nothing enchanted draws nothing.
  `.draw (.fixed 1) .enchantedController`. -/
  | enchantedController
deriving Repr, Inhabited, BEq

/-- Who `TriggerResolution.pump` gives +P/+T until end of turn, who
`TriggerResolution.dealDamage` damages, what `TriggerResolution.discard`
discards, which cards `TriggerResolution.returnToHand` returns, which
permanent `TriggerResolution.sacrifice` sacrifices, who
`TriggerResolution.putCounters` puts counters on, who
`TriggerResolution.removeCounters` removes counters from, who
`TriggerResolution.tap` taps, who `TriggerResolution.untap` untaps,
which permanents `TriggerResolution.destroy` destroys, who
`TriggerResolution.grant` grants an ability to, who
`TriggerResolution.fight` uses, who
`TriggerResolution.lose` removes an ability from, who
`TriggerResolution.becomeArtifact` makes an artifact, who
`TriggerResolution.becomePrepared` prepares, who
`TriggerResolution.setBasePT` gives a new base power and toughness,
which card `TriggerResolution.putOnLibrary` puts on a library,
which cards `TriggerResolution.exile` exiles, and
which cards `TriggerResolution.put` puts onto the battlefield.
`.source` is first so a default resolution pumps the source.
A player is `.player`. `n` cards from a hand are `.cards n`.
A returned card names both the card and whose hand.
A sacrifice names both who sacrifices and which permanent.
Counters name who receives them.
Losing an ability names who loses it.
Becoming an artifact names who becomes one.
Becoming prepared names who becomes prepared.
A new base power and toughness names who receives it.
Putting a card on a library names which card.
Exiling names which cards.
Putting cards onto the battlefield names which cards. -/
inductive ObjectSelector where
  /-- The ability's source, if it is still on the battlefield.
  +P/+T is `.pump (.fixed p) (.fixed t) .source`.
  `n` damage is `.dealDamage (.fixed n) .source`.
  Returned from its owner's graveyard to their hand is
  `.returnToHand .source`.
  A loyalty counter is `.putCounters (.ofKind .loyalty) .source`.
  It loses indestructible until end of turn is
  `.lose .indestructible .source`.
  It becomes an artifact until end of turn is `.becomeArtifact .source`.
  It becomes prepared is `.becomePrepared .source`.
  Its base power and toughness become `p`/`t` is
  `.setBasePT (.fixed p) (.fixed t) .source`.
  Its owner puts it on top of their library is `.putOnLibrary .top .source`.
  On the bottom is `.putOnLibrary .bottom .source`.
  Exiling it is `.exile .source .forLater`.
  Returned from its owner's graveyard as an artifact is
  `.put .source (how := .asArtifact)`.
  Returned under its owner's control is `.put .source .underOwner`. -/
  | source
  /-- The announced permanent for a pump. For damage, the announced target,
  a player or a permanent.
  It loses indestructible until end of turn is `.lose .indestructible`
  (`.target`). An illegal target is reported.
  It becomes an artifact until end of turn is `.becomeArtifact`
  (`.target`).
  It becomes prepared is `.becomePrepared` (`.target`).
  Its base power and toughness become `p`/`t` is
  `.setBasePT (.fixed p) (.fixed t)` (`.target`).
  Its owner puts it on top of their library is `.putOnLibrary .top`
  (`.target`). On the bottom is `.putOnLibrary .bottom`.
  Exiling it is `.exile .target .forLater`. -/
  | target
  /-- The creature this Aura enchants. The Aura must still be on the battlefield.
  Nothing enchanted does nothing.
  A counter on it is `.putCounters (.ofKind .plusOnePlusOne) .enchanted`.
  It loses indestructible until end of turn is
  `.lose .indestructible .enchanted`.
  It becomes an artifact until end of turn is `.becomeArtifact .enchanted`.
  It becomes prepared is `.becomePrepared .enchanted`.
  Its base power and toughness become `p`/`t` is
  `.setBasePT (.fixed p) (.fixed t) .enchanted`.
  Its owner puts it on top of their library is `.putOnLibrary .top .enchanted`.
  On the bottom is `.putOnLibrary .bottom .enchanted`.
  Exiling it is `.exile .enchanted .forLater`. -/
  | enchanted
  /-- The announced permanent, while the source is still on the battlefield.
  A source that already left is silent.
  A counter on it is `.putCounters (.ofKind .plusOnePlusOne) .targetWhileSource`.
  It loses indestructible until end of turn is
  `.lose .indestructible .targetWhileSource`.
  It becomes an artifact until end of turn is
  `.becomeArtifact .targetWhileSource`.
  It becomes prepared is `.becomePrepared .targetWhileSource`.
  Its base power and toughness become `p`/`t` is
  `.setBasePT (.fixed p) (.fixed t) .targetWhileSource`.
  Its owner puts it on top of their library is
  `.putOnLibrary .top .targetWhileSource`.
  On the bottom is `.putOnLibrary .bottom .targetWhileSource`.
  Exiling it is `.exile .targetWhileSource .forLater`. -/
  | targetWhileSource
  /-- The creature that caused the trigger.
  Returned to its owner's hand is `.returnToHand .cause`.
  A token ceases to exist.
  `subtype`, when set, requires that subtype.
  The Villain that caused this, under its owner's control, as a Hero with
  a finality counter, is
  `.put (.cause (some "Villain")) .underOwner (.entering [.additionalSubtype "Hero", .counter .finality])`.
  An announced card or permanent is used when one was chosen; otherwise the
  recorded cause. A missing cause, or the wrong subtype, puts nothing. -/
  | cause (subtype : Option String := none)
  /-- Each creature the controller controls. -/
  | creaturesYouControl
  /-- Each other creature the controller controls of these subtypes.
  The source is not included. -/
  | othersOfSubtypes (subtypes : Array String)
  /-- Each other permanent the controller controls of this subtype.
  The source is not included. -/
  | othersOfSubtype (subtype : String)
  /-- Each creature an opponent controls. -/
  | opponentsCreatures
  /-- Each creature the controller controls of this subtype. -/
  | youControlSubtype (subtype : String)
  /-- Each creature blocking the source. -/
  | blockers
  /-- The announced permanent. `byYou` means the controller puts the counters,
  and an illegal target logs that you won't put counters.
  Returned to its owner's hand, noting the return, is
  `.returnToHand .permanent .returnedPermanent`.
  A +1/+1 counter you put on the target is
  `.putCounters (.ofKind .plusOnePlusOne) (.permanent true)`. -/
  | permanent (byYou : Bool := false)
  /-- Each creature that is not this subtype, and each opponent. -/
  | eachNonSubtypeAndOpponents (subtype : String)
  /-- The player `who` names.
  The controller is `.player .you`.
  Each opponent is `.player .eachOpponent`.
  The announced opponent is `.player .targetOpponent`. -/
  | player (who : PlayerSelector)
  /-- `n` cards from the hand of `who`.
  The controller discards `n` is `.cards n` (`.you`).
  Each opponent discards one is `.cards 1 .eachOpponent`.
  The announced opponent discards `n` is `.cards n .targetOpponent`.
  `TriggerResolution.discard` reads this selector. -/
  | cards (n : Nat := 1) (who : PlayerSelector := .you)
  /-- The controller's hand. The number discarded is noted for a later step.
  Declining leaves the note empty.
  `.discard .hand`. -/
  | hand
  /-- A nonland card chosen from the announced player's revealed hand.
  `.discard .chosenNonland`. -/
  | chosenNonland
  /-- The announced graveyard card, returned to the controller's hand.
  A card that has left is reported.
  `.returnToHand .graveyardCard`.
  Exiling it so it can be played is
  `.exile .graveyardCard .forLater .playCard`. -/
  | graveyardCard
  /-- The announced graveyard card, or that card as a permanent target,
  returned to the controller's hand.
  `.returnToHand .graveyardPermanent`. -/
  | graveyardPermanent
  /-- Cards an earlier step milled that have this subtype, put into the
  controller's hand.
  `.returnToHand (.milledSubtype subtype)`. -/
  | milledSubtype (subtype : String)
  /-- The card `revealLibrary .untilCreature` revealed, put into the
  controller's hand on the hand branch.
  Outside that resolution, `.returnToHand .revealed` does nothing.
  Put onto the battlefield is `.put .revealed`. Outside `.untilSaga` and
  the battlefield branch of `.untilCreature`, that put does nothing. -/
  | revealed
  /-- A basic land card `searchLibrary` found, put into the controller's hand.
  Outside that resolution, `.returnToHand .basicLand` does nothing. -/
  | basicLand
  /-- A card the source exiled, returned to its owner's hand.
  A missing source, or nothing exiled, returns nothing.
  `.returnToHand .linkedExile`.
  Put onto the battlefield is `.put .linkedExile`. -/
  | linkedExile
  /-- Up to `n` target instant and/or sorcery cards from the controller's
  graveyard.
  `.returnToHand (.graveyardInstants 2)`.
  Inside `queueReflexive`, those targets are chosen when the reflexive
  ability is put on the stack. Outside it, this returns nothing. -/
  | graveyardInstants (n : Nat)
  /-- The announced opponent sacrifices a creature of their choice.
  `.sacrifice .opponentChosenCreature`. -/
  | opponentChosenCreature
  /-- Each player sacrifices a creature of their choice.
  `.sacrifice .eachPlayersCreature`. -/
  | eachPlayersCreature
  /-- A creature with the least power among creatures the defending player
  controls.
  `.sacrifice .leastPower`. -/
  | leastPower
  /-- A creature that dealt combat damage to you this turn. Each opponent
  sacrifices one of their choice.
  `.sacrifice .combatDamager`. -/
  | combatDamager
  /-- The ability's source, sacrificed as `how` says.
  “{name} is sacrificed” is `.sacrifice .source`, and also
  `.sacrifice (.sacrificedSource .isSacrificed)`.
  The controller sacrifices it with
  `.sacrifice (.sacrificedSource .controllerSacrifices)`.
  It moves as sacrificed, without a token-sacrifice trigger, with
  `.sacrifice (.sacrificedSource .movedAsSacrificed)`. -/
  | sacrificedSource (how : SacrificeSourceHow := .isSacrificed)
  /-- The Plan, if it is still on the battlefield.
  `.sacrifice .plan`.
  Noting whether the sacrifice happened is `.sacrifice .plan .forReflexive`. -/
  | plan
  /-- Another creature the controller controls.
  `.sacrifice .another`. -/
  | another
  /-- A nontoken creature of each opponent's choice. An opponent with none
  sacrifices nothing.
  `.sacrifice .chosenNontokenCreature`. -/
  | chosenNontokenCreature
  /-- Permanents you control.
  Each creature is `.youControl`.
  Each permanent of a subtype is `.youControl (.subtype s)`.
  One counter, or two with the city's blessing, is `.youControl .citysBlessing`.
  `.putCounters (.ofKind .plusOnePlusOne) .youControl`. -/
  | youControl (which : YouControlPlusOne := .eachCreature)
  /-- Each other creature you control.
  `.putCounters (.ofKind .plusOnePlusOne) .eachOther`. -/
  | eachOther
  /-- The token an earlier step created.
  The noted number of +1/+1 counters is
  `.putCounters .plusOneNoted .createdToken`. -/
  | createdToken
  /-- The ability's source, if it is still on the battlefield.
  A source that has left logs that no counter is put. Later steps still run.
  `.putCounters (.ofKind .plusOnePlusOne) .sourceIfPresent`. -/
  | sourceIfPresent
  /-- Each announced permanent, up to the trigger's last-known count.
  None, or zero, puts counters on nothing. An illegal permanent is
  reported and skipped. Announced permanents past that count are ignored.
  `.putCounters (.ofKind .plusOnePlusOne) .eachUpToLastKnown`. -/
  | eachUpToLastKnown
  /-- The announced permanent, while it is still on the battlefield.
  A missing target loses nothing.
  It loses all abilities while the source remains is
  `.lose .allAbilities .targetIfPresent`.
  A source that has left leaves that permanent able. -/
  | targetIfPresent
  /-- A card from the controller's hand.
  An empty hand skips the choice.
  Putting it on the bottom of that player's library is
  `.putOnLibrary .bottom .cardFromHand`.
  Putting it on top puts nothing. -/
  | cardFromHand
  /-- Each announced permanent.
  Each one until the source leaves is
  `.exile .eachTarget .untilSourceLeaves`.
  A source that has left exiles nothing. -/
  | eachTarget
  /-- The top card of the controller's library.
  Playable until the end of your next turn is
  `.exile .top .playUntilNextTurn`.
  Playable this turn, and +2/+1 on the source when it is a Hero, is
  `.exile .top .playThisTurn .ifHero`.
  A missing source still exiles the card. An empty library exiles nothing.
  Inside `revealLibrary`, the top card remembered for `.mayCast .impulse` is
  `.exile .top .forLater .impulse`. Outside that resolution, the exile does
  nothing.
  The nonland from `revealLibrary .untilNonland` is
  `.exile .top .forLater .anyManaThisTurn` inside that resolution.
  Outside it, the exile does nothing. -/
  | top
  /-- Each announced land the controller still controls.
  Remembered so they return tapped is
  `.exile .landsYouControl .forLater .lands`. -/
  | landsYouControl
  /-- Up to `max` basic cards of this subtype from the controller's library.
  Linked to the source is
  `.exile (.basicUpTo subtype max) .forLater .linked`. -/
  | basicUpTo (subtype : String) (max : Nat)
  /-- The card recorded as this trigger's last-known power.
  You may exile it from your graveyard and play it until the end of your
  next turn with
  `.may (.exile .discarded .playUntilNextTurn) (.sequence []) .ifYouDo`.
  A card that has left the graveyard is reported. No recorded card is
  reported. Declining exiles nothing. -/
  | discarded
  /-- The top `n` cards of the announced opponent's library.
  `.exile (.opponentTop 5) (.mayCastUpTo 2)`.
  Inside `queueReflexive`, the opponent is chosen when the reflexive
  ability is put on the stack. Outside it, this exiles nothing. -/
  | opponentTop (n : Nat)
  /-- The announced nonland permanent card from a graveyard.
  Its mana value is at most `mv`.
  `.put (.nonlandMvAtMost mv)`. -/
  | nonlandMvAtMost (mv : Nat)
  /-- Lands an earlier step exiled.
  Returned tapped is `.put .notedLands (how := .tapped)`. -/
  | notedLands
  /-- The card an earlier step discarded, when it is a land.
  Entering tapped is `.put .discardedLand (how := .tapped)`. -/
  | discardedLand
  /-- A land card from the controller's hand.
  Entering tapped is `.put .landFromHand (how := .tapped)`.
  Optional as `.may (.put .landFromHand (how := .tapped)) (.sequence [])`. -/
  | landFromHand
  /-- An artifact card from the controller's hand.
  Remembered for a later attach is
  `.put .artifactFromHand (note := .forAttach)`.
  Optional as `.may (.put .artifactFromHand (note := .forAttach)) (.sequence [])`.
  An empty hand skips that choice. -/
  | artifactFromHand
  /-- A random creature from the cards `revealLibrary (.top n)` revealed.
  `.put .randomCreature`.
  Outside that resolution, this puts nothing. -/
  | randomCreature
  /-- A Forest card `searchLibrary` found.
  `.put .forest`.
  Outside that resolution, this puts nothing. -/
  | forest
  /-- A basic land card `searchLibrary` found, put on top of the library.
  `.put .basicLandOnTop`.
  Outside that resolution, this puts nothing. -/
  | basicLandOnTop
  /-- A Dragon card `searchLibrary` found in the hand and/or library.
  `.put .dragon`.
  Outside that resolution, this puts nothing. -/
  | dragon
  /-- The announced creature card. Its mana value is at most `mv`.
  `.put (.creatureMvAtMost mv)`. -/
  | creatureMvAtMost (mv : Nat)
  /-- A creature card of `subtype` with mana value at most `maxMv` from hand.
  `.may (.put (.creatureFromHand subtype maxMv)) (.draw (.fixed 1))`. -/
  | creatureFromHand (subtype : String) (maxMv : Nat)
  /--   The announced creature card in the controller's graveyard.
  Returned tapped and attacking with a finality counter is
  `.put .creatureCard .tapped (.entering [.attacking, .counter .finality])`.
  Inside `queueReflexive`, that card is chosen when the reflexive ability
  is put on the stack. Outside it, this puts nothing. -/
  | creatureCard
  /-- Any number of untapped Humans the controller controls.
  Choosing none taps nothing.
  `.tap .humans`. -/
  | humans
  /-- The creature this Aura enchants, while the Aura is still on the battlefield.
  Nothing enchanted does nothing. A missing Aura is reported.
  `.tap .enchantedWhileSource`. -/
  | enchantedWhileSource
  /-- Each attacking creature.
  `.untap .attackingCreatures`. -/
  | attackingCreatures
  /-- The creature this Equipment is attached to, while it is on the battlefield.
  A missing creature is reported, and later steps of the sequence do not happen.
  `.untap .equipped`. -/
  | equipped
  /-- The creature that became tapped, while it is still tapped.
  The recorded cause is used when one was chosen. Otherwise the creature
  that became tapped most recently. An untapped creature is left alone.
  `.untap .firstThisTurn`. -/
  | firstThisTurn
  /-- All artifacts and enchantments opponents control.
  `.destroy .oppArtifactsEnchantments`. -/
  | oppArtifactsEnchantments
  /-- The permanent an earlier step dealt damage to.
  `.destroy .permanentDealtDamage`. -/
  | permanentDealtDamage
  /-- Each equipped attacking creature.
  `.grant .doubleStrike .equippedAttackers`. -/
  | equippedAttackers
  /-- The controller, when the source was cast.
  A source that was not cast does nothing.
  `.grant .protectionEverything .youIfCast`. -/
  | youIfCast
  /-- The one creature the controller has attacking alone.
  None is reported. -/
  | attackingAlone
  /-- Each creature the spell that caused this trigger targets.
  A permanent that is not a creature is skipped. No recorded spell grants
  nothing.
  `.grant (.keywords Keyword.flying) .spellTargets`. -/
  | spellTargets
  /-- The announced creature.
  It fights up to one other announced creature with
  `.fight .announced .upToOneOther`.
  It fights another announced creature with `.fight .announced .mutual`. -/
  | announced
  /-- The creature an earlier step attached Equipment to.
  It deals damage equal to its power with `.fight .equipmentHost .reflexive`.
  Nothing is queued when no creature received Equipment. -/
  | equipmentHost
deriving Repr, Inhabited, BEq

/-- Where one statistic of `TriggerResolution.pump` reads its bonus,
where `TriggerResolution.dealDamage` reads its amount, how many cards
`TriggerResolution.scry` looks at, how many cards `TriggerResolution.draw`
draws, where one statistic of `TriggerResolution.setBasePT` reads its
new base, how much life `TriggerResolution.gainLife` gains, and how much
life `TriggerResolution.loseLife` loses.
`.greatestPower` is first so a default resolution uses it.
`.fixed` is a fixed bonus, `n` damage, scry `n`, draw `n`, a base of `n`,
`n` life gained, or `n` life lost. -/
inductive NumberSelector where
  /-- The greatest power among creatures the controller controls. -/
  | greatestPower
  /-- One for each card looked at while scrying. -/
  | perLookedAt
  /-- One for each other creature the controller controls.
  The source is not included.
  +1/+1 is `.pump .perOtherCreature .perOtherCreature .source`.
  1 life is `.gainLife .perOtherCreature`. -/
  | perOtherCreature
  /-- One for each Plains the controller controls. -/
  | perPlains
  /-- A fixed bonus of `n`, `n` damage, scry `n`, draw `n`, a base of `n`,
  `n` life gained, or `n` life lost.
  A base of `p`/`t` is `.setBasePT (.fixed p) (.fixed t)`.
  You gain `n` life is `.gainLife (.fixed n)`.
  You lose `n` life is `.loseLife (.fixed n)`. -/
  | fixed (n : Int)
  /-- The source's toughness.
  Another creature's base toughness becomes this toughness with
  `.setBasePT .equalSourcePower .equalSourceToughness`. -/
  | equalSourceToughness
  /-- The source's power.
  Another creature's base power becomes this power with
  `.setBasePT .equalSourcePower .equalSourceToughness`. -/
  | equalSourcePower
  /-- This statistic's current value, which doubles it.
  Doubling the announced permanent is `.pump .double .double .target`. -/
  | double
  /-- The source's last-known power. -/
  | lastKnownPower
  /-- How many permanents of this subtype the controller controls. -/
  | subtypeCount (subtype : String)
  /-- How many cards an earlier step discarded from the controller's hand.
  Damage to each opponent is `.dealDamage .discardedHand (.player .eachOpponent)`.
  Drawing that many is `.draw .discardedHand`. -/
  | discardedHand
  /-- The greatest mana value among artifacts the controller controls. -/
  | greatestArtifactMv
  /-- The mana value of the spell that caused this, including the chosen
  value of X. A spell that has left the stack uses the trigger's last-known
  power, then the newest spell on the stack, then a mana value recorded
  for this turn. None of those is zero. -/
  | spellManaValue
  /-- One card for each Human tapped by an earlier step.
  `.draw .forEachTappedHuman`. -/
  | forEachTappedHuman
  /-- One card for each graveyard with seven or more cards.
  `.draw .perFatGraveyard`. -/
  | perFatGraveyard
  /-- X cards, where X is the mana spent to cast the triggering spell.
  Spending none skips the later steps of a draw sequence.
  `.draw .equalToManaSpent`. -/
  | equalToManaSpent
  /-- One card for each permanent of this type the controller controls.
  `.draw (.perControlled ty)`. -/
  | perControlled (ty : CardType)
  /-- Enough cards that the controller's hand has `n` cards.
  A hand that already has `n` draws nothing.
  `.draw (.upToHandSize n)`. -/
  | upToHandSize (n : Nat)
  /-- The number of +1/+1 counters on the source.
  A source that has left queues no reflexive damage from this amount.
  `.dealDamage .plusOneCounters .target`. -/
  | plusOneCounters
  /-- The targeted card's power.
  Inside `sequence`, that power is read when the sequence starts, before an
  earlier step moves the card.
  `.gainLife .equalToTargetPower`. -/
  | equalToTargetPower
  /-- One for each permanent an earlier step destroyed.
  Indestructible permanents and shield counters do not count.
  `.gainLife .forEachDestroyedThisWay`. -/
  | forEachDestroyedThisWay
  /-- One for each Equipment attached to the source.
  A source that has left uses its last-known power as that count.
  Zero gains nothing.
  `.gainLife .attachedEquipment`.
  Each opponent loses that much with `.loseLife .attachedEquipment .eachOpponent`. -/
  | attachedEquipment
  /-- One life for each burden counter on the source.
  A source that can no longer be found loses nothing.
  `.loseLife .perBurden`. -/
  | perBurden
deriving Repr, Inhabited, BEq

/-- What `TriggerResolution.dealDamage` records for a later step. -/
inductive TriggerDamageNote where
  /-- The damage only. -/
  | none
  /-- The permanent that was actually marked, for a later destroy. -/
  | markedPermanent
  /-- Excess over the permanent's remaining toughness, for a later amass. -/
  | excess
  /-- The creature this Equipment is attached to deals the damage.
  Nothing equipped still deals it, with no source. -/
  | fromEquipped
  /-- The damage is divided among one or two targets.
  `.dealDamage (.fixed n) .target .divided`.
  Inside `queueReflexive`, that ability is put on the stack and the
  targets are chosen then. Outside it, this deals nothing. -/
  | divided
deriving Repr, Inhabited, BEq

/-- Which permanent an effect uses when several recipients share one constructor.
`.target` is the announced permanent. -/
inductive TriggerAffected where
  /-- The announced permanent, while it is still a legal target. -/
  | target
  /-- The ability's source, if it is still on the battlefield. -/
  | source
  /-- The creature this Aura enchants. The Aura must still be on the battlefield.
  Nothing enchanted does nothing. -/
  | enchanted
  /-- The announced permanent, while the source is still on the battlefield.
  A source that already left is silent. -/
  | targetWhileSource
deriving Repr, Inhabited, BEq

/-- What `TriggerResolution.lose` removes. -/
inductive AbilitySelector where
  /-- Indestructible, until end of turn. -/
  | indestructible
  /-- All abilities, for as long as the source remains on the battlefield. -/
  | allAbilities
deriving Repr, Inhabited, BEq

/-- What `TriggerResolution.putCounters` puts. `ofKind` uses its `n`. -/
inductive CounterSelector where
  /-- `n` counters of this kind. One is `.ofKind kind`. -/
  | ofKind (kind : CounterKind) (n : Nat := 1)
  /-- +1/+1 counters equal to the source's last-known mana value. -/
  | plusOneLastKnownMv
  /-- +1/+1 counters equal to the power noted by sacrificing another creature. -/
  | plusOneSacrificedPower
  /-- Hone counters, one for each creature the targeted opponent controls. -/
  | honePerOpponent
  /-- +1/+1 counters equal to the count an earlier step noted. -/
  | plusOneNoted
  /-- Each kind of counter the source last had, in the same numbers. -/
  | sourceCounters
  /-- One counter on the source for each of haste, flying, first strike,
  double strike, deathtouch, indestructible, lifelink, menace, reach,
  trample, and vigilance that the announced creature has and the source
  does not. An illegal target or a missing source puts nothing. -/
  | missingKeywordsFromTarget
deriving Repr, Inhabited, BEq

/-- Which token `TriggerResolution.createTokens` creates.
`.kind` uses the `kind` argument. -/
inductive TriggerToken where
  /-- The `kind` argument. -/
  | kind
  /-- A colorless Equipment artifact token named Axe. -/
  | axe
  /-- Zabu, a legendary 2/2 green Cat. -/
  | zabu
  /-- The Void, a legendary 5/5 black Horror Villain. -/
  | theVoid
  /-- Redwing, a legendary 1/1 blue Bird Scout. -/
  | redwing
  /-- A 1/1 red Alien creature token with haste. -/
  | alien
  /-- A colorless Equipment artifact token named Sturdy Shield. -/
  | sturdyShield
  /-- Galactus, a legendary 16/16 black Elder Alien with flying and trample. -/
  | galactus
  /-- A 1/1 blue Merfolk creature token. With `qty` `.blueManaSymbols`,
  the count is the blue mana symbols in the spell that caused this.
  No blue symbol creates nothing. -/
  | merfolk
deriving Repr, Inhabited, BEq

/-- Who `TriggerResolution.createTokens` creates the tokens for. -/
inductive TriggerTokenWho where
  /-- The controller of the ability. -/
  | you
  /-- The announced opponent. With no player target, the controller creates it. -/
  | targetOpponent
  /-- The controller the targeted permanent had on the battlefield.
  Destroy may already have moved it. -/
  | targetController
deriving Repr, Inhabited, BEq

/-- How many tokens `TriggerResolution.createTokens` creates.
`.fixed` uses `n`. -/
inductive TriggerTokenQty where
  /-- The `n` argument. -/
  | fixed
  /-- One for each artifact opponents control. -/
  | oppArtifacts
  /-- One for each artifact the damaged player controls. -/
  | damagedPlayerArtifacts
  /-- The last-known count. Bird Soldiers use `kind`; other counts are Treasures. -/
  | lastKnown
  /-- One for each creature the controller controls of a chosen type. -/
  | chosenCreatureType
  /-- One for each permanent of this subtype the controller controls. -/
  | perSubtype (subtype : String)
  /-- One for each blue mana symbol in the mana cost of the spell that
  caused this. No such spell, or no blue symbol, creates nothing. -/
  | blueManaSymbols
deriving Repr, Inhabited, BEq

/-- What `TriggerResolution.createTokens` records or queues after the token exists. -/
inductive TriggerTokenNote where
  /-- The tokens only. -/
  | none
  /-- Queue “attach it to target creature you control.” -/
  | attachReflexive
  /-- Remember the token so a later step can attach it to the source. -/
  | remember
  /-- Remember the token and how many invasion counters the source had. -/
  | invasion
deriving Repr, Inhabited, BEq

/-- How long `TriggerResolution.exile` lasts. -/
inductive TriggerExileHow where
  /-- Link the card for a leave-the-battlefield trigger. It does not return
  when the source leaves. -/
  | leaveTrigger
  /-- Until the source leaves the battlefield. The source must still be there. -/
  | untilSourceLeaves
  /-- Return it at the beginning of the next end step. -/
  | nextEndStep
  /-- You may play it until the end of your next turn. -/
  | playUntilNextTurn
  /-- You may play it this turn. With note `.ifHero`, a Hero card also gives
  the source +2/+1 until end of turn. -/
  | playThisTurn
  /-- Move it to exile. `note` tells the next step which cards moved. -/
  | forLater
  /-- Exile it, then return it under its owner's control.
  A land, the source, a permanent another player controls, or a missing
  target is not exiled. Choosing none does nothing. -/
  | returnImmediately
  /-- Exile the announced nontoken artifact or creature, then return it
  tapped under its owner's control. Choosing none does nothing.
  A token, a permanent that is neither an artifact nor a creature, or a
  missing target is not exiled. -/
  | returnTapped
  /-- You may cast up to `casts` spells from among the exiled cards
  without paying their mana costs.
  `.exile (.opponentTop 5) (.mayCastUpTo 2)`.
  Outside `queueReflexive`, this exiles nothing. -/
  | mayCastUpTo (casts : Nat)
deriving Repr, Inhabited, BEq

/-- What a later step of `TriggerResolution.exile` can read. -/
inductive TriggerExileNote where
  /-- Nothing beyond the exile itself. -/
  | none
  /-- The lands, to return tapped. -/
  | lands
  /-- The creature, and the permanent the source enchants, for a copy. -/
  | copyAndHost
  /-- The graveyard card, so it can be played. -/
  | playCard
  /-- The instant or sorcery, so `.mayCast .impulse` can offer it.
  Outside `revealLibrary .untilInstantOrSorcery`, this note does nothing. -/
  | impulse
  /-- The nonland `revealLibrary .untilNonland` exiled. Declining the
  +1/+1 counter lets you cast it until end of turn, and mana of any type
  can be spent. Outside that resolution, this note does nothing. -/
  | anyManaThisTurn
  /-- Link the exiled cards to the source. Used by a library search. -/
  | linked
  /-- The top card, when it is a Hero, gives the source +2/+1 until end of
  turn. Used with `.exile .top .playThisTurn`. A missing source still exiles
  the card and does not pump. An empty library exiles nothing. -/
  | ifHero
deriving Repr, Inhabited, BEq

/-- What a later step of `TriggerResolution.sacrifice` can read. -/
inductive TriggerSacrificeNote where
  /-- Nothing beyond the sacrifice itself. -/
  | none
  /-- Whether the Plan was actually sacrificed. A following reflexive
  ability triggers only when it was. -/
  | forReflexive
  /-- Whether the source was actually sacrificed. A following
  `«if» .sourceWasSacrificed` sees it. -/
  | noted
deriving Repr, Inhabited, BEq

/-- What `TriggerResolution.attach` attaches. -/
inductive TriggerAttachWhat where
  /-- The source. -/
  | source
  /-- The first announced permanent. -/
  | target
  /-- Any number of Equipment the controller chooses. -/
  | anyYouControl
  /-- The token an earlier step remembered. -/
  | created
  /-- The artifact an earlier step put from hand. -/
  | putArtifact
  /-- The announced Equipment. An illegal Equipment does not move. -/
  | announcedEquipment
  /-- Each announced Equipment. Choosing none attaches nothing. -/
  | eachTargetEquipment
deriving Repr, Inhabited, BEq

/-- What `TriggerResolution.attach` attaches that object to. -/
inductive TriggerAttachTo where
  /-- The token the previous step created. -/
  | created
  /-- The announced permanent. -/
  | target
  /-- Up to one announced creature. A missing creature is reported. -/
  | optionalCreature
  /-- The announced creature. When two targets were announced, the later one. -/
  | creatureTarget
  /-- The source. -/
  | source
  /-- The creature remembered with the artifact put from hand. -/
  | notedHost
  /-- The announced creature. An illegal pair does not move the Equipment. -/
  | announcedCreature
  /-- The creature the source enchants. A missing creature leaves Equipment
  where it is. -/
  | enchantedCreature
deriving Repr, Inhabited, BEq

/-- Who `TriggerResolution.amass` amasses for. -/
inductive AmassWho where
  /-- The ability's controller. -/
  | you
  /-- The controller an earlier step recorded when it destroyed a creature.
  No destruction amasses nothing. -/
  | notedController
deriving Repr, Inhabited, BEq

/-- Where `TriggerResolution.mayCast` finds the spell. -/
inductive TriggerCastFrom where
  /-- An artifact, instant, or sorcery card in your graveyard. -/
  | graveyard
  /-- An instant or sorcery card in your hand. -/
  | hand
  /-- The instant or sorcery an earlier
  `revealLibrary .untilInstantOrSorcery (.exile .top .forLater .impulse) .damagedPlayer`
  stored. -/
  | impulse
  /-- The next red or green creature spell the controller casts this turn. -/
  | nextRedOrGreenCreature
  /-- A spell among the cards `revealLibrary (.top n)` just looked at.
  Outside that resolution, this origin does nothing. -/
  | looked
  /-- An enchantment, instant, or sorcery card in an opponent's graveyard
  with mana value at most the causing spell.
  `.mayCast .milledSpell .causingSpell .withoutPaying`.
  Inside `queueReflexive`, that ability is put on the stack. The mana
  value is the causing spell's, or the trigger's last-known power when
  no spell is recorded. No legal card removes the reflexive ability.
  Outside `queueReflexive`, this casts nothing. -/
  | milledSpell
deriving Repr, Inhabited, BEq

/-- The mana-value limit of `TriggerResolution.mayCast`.
`.unlimited` is no limit. -/
inductive TriggerCastMv where
  /-- No mana-value limit. -/
  | unlimited
  /-- At most twice the number of legendary Wizards you control. -/
  | twiceLegendaryWizards
  /-- At most the last-known power. Combat damage uses that amount. -/
  | lastKnown
  /-- At most the greatest power among attacking creatures the controller
  controls. No attacker is a limit of zero. -/
  | greatestAttackingPower
  /-- At most the mana value of the spell that caused this.
  No recorded spell uses the trigger's last-known power.
  `.mayCast .milledSpell .causingSpell .withoutPaying`. -/
  | causingSpell
deriving Repr, Inhabited, BEq

/-- Whether `TriggerResolution.mayCast` pays the mana cost. -/
inductive TriggerCastCost where
  /-- Pay its mana cost. -/
  | pay
  /-- Without paying its mana cost. -/
  | withoutPaying
deriving Repr, Inhabited, BEq

/-- What happens to an instant or sorcery `TriggerResolution.mayCast` casts. -/
inductive TriggerCastNote where
  /-- The cast only. -/
  | none
  /-- An instant or sorcery cast this way is exiled instead of being put
  into your graveyard. -/
  | exileInstead
deriving Repr, Inhabited, BEq

/-- What a later step of `TriggerResolution.returnToHand` can read. -/
inductive TriggerReturnNote where
  /-- Nothing beyond the return itself. -/
  | none
  /-- Whether a permanent was actually returned. -/
  | returnedPermanent
deriving Repr, Inhabited, BEq

/-- How a card `TriggerResolution.put` changes as it enters. -/
inductive TriggerEnterWith where
  /-- The permanent loses every ability and keyword. -/
  | loseAllAbilities
  /-- The permanent gains these keywords. -/
  | keywords (k : Keywords)
  /-- The permanent gains `subtype` in addition to its other types. -/
  | additionalSubtype (subtype : String)
  /-- Put `n` counters of `kind` on it. `asEnters` reports that it enters
  with them. A finality counter is put by the ability's controller. -/
  | counter (kind : CounterKind) (n : Nat := 1) (asEnters : Bool := false)
  /-- The permanent enters attacking. -/
  | attacking
deriving Repr, Inhabited, BEq

/-- How `TriggerResolution.put` puts those cards onto the battlefield. -/
inductive TriggerPutHow where
  /-- Untapped, as printed. -/
  | asPrinted
  /-- Tapped. -/
  | tapped
  /-- As an artifact. It is not a creature. -/
  | asArtifact
  /-- Under the card's owner's control. -/
  | underOwner
deriving Repr, Inhabited, BEq

/-- What a later step of `TriggerResolution.put` can read, or how the
card enters. -/
inductive TriggerPutNote where
  /-- Nothing beyond putting the cards. -/
  | none
  /-- The artifact put from hand, and the creature it may attach to. -/
  | forAttach
  /-- Apply these changes before the permanent's enters abilities. -/
  | entering (mods : List TriggerEnterWith)
deriving Repr, Inhabited, BEq

namespace TriggerPutNote

/-- Modifications carried by `entering`. Any other note changes nothing. -/
def enterMods : TriggerPutNote → List TriggerEnterWith
  | .entering mods => mods
  | _ => []

end TriggerPutNote

/-- How `TriggerResolution.addMana` chooses the mana it adds. `types` is
the printed mana when this is `.fixed`. -/
inductive TriggerManaAmount where
  /-- The printed mana types, once. -/
  | fixed
  /-- The printed mana types, once for each charge counter on the source.
  A source that has left uses its last-known charge counters. -/
  | perChargeCounter
deriving Repr, Inhabited, BEq

/-- How `TriggerResolution.chooseModes` chooses those modes. -/
inductive TriggerModeHow where
  /-- The controller chooses one mode that has not been chosen this turn.
  The source remembers it until the turn ends. If every mode was already
  chosen, the ability is removed with no effect. -/
  | oneUnusedThisTurn
  /-- The controller chooses one mode that has not been chosen.
  The source remembers it for its lifetime. If every mode was already
  chosen, the ability is removed with no effect. -/
  | oneUnused
  /-- Modes already chosen resolve in printed order. -/
  | alreadyChosen
  /-- The controller chooses one — a +1/+1 counter on the source, or remove
  a counter from a creature you control and draw a card if you do.
  You must remove a counter when a creature you control has one.
  Choosing that mode when none does draws nothing. The modes are
  `TriggerResolution.hydeModes`. This choice does not record a used mode. -/
  | plusOneOrRemoveCounter
  /-- The mode index is this trigger's last-known power. None is mode 0.
  An index past `modes` does nothing. This choice does not record a used mode. -/
  | fromLastKnown
  /-- The controller chooses one Vision mode that has not been chosen this
  turn. The source remembers it until the turn ends. The modes are
  `TriggerResolution.visionModes`. If every mode was already chosen, the
  ability is removed with no effect. A source that has left still draws
  when that mode is chosen, and does not gain a keyword. -/
  | vision
deriving Repr, Inhabited, BEq

/-- What a later step of `TriggerResolution.destroy` can read. -/
inductive TriggerDestroyNote where
  /-- Nothing beyond the destruction. -/
  | none
  /-- How many permanents were actually destroyed. Indestructible
  permanents and shield counters do not count. -/
  | countDestroyed
  /-- The announced creature's controller and power. No legal target
  leaves the note empty, so no player amasses. -/
  | forAmass
  /-- The announced token. A permanent that is not a token stays.
  The ability's own target may be a player; the token is `targets[0]`. -/
  | chosenToken
deriving Repr, Inhabited, BEq

/-- How `TriggerResolution.fight` uses that creature. -/
inductive TriggerFightHow where
  /-- It fights the announced creature. Each deals damage equal to its
  power to the other. Choosing none fights nothing. -/
  | mutual
  /-- It deals damage equal to its power. The target is chosen when a
  reflexive ability is put on the stack. -/
  | reflexive
  /-- The announced creature fights up to one other announced creature. -/
  | upToOneOther
deriving Repr, Inhabited, BEq

/-- What `TriggerResolution.grant` grants. -/
inductive TriggerGrantWhat where
  /-- Double strike until end of turn. -/
  | doubleStrike
  /-- Protection from everything until that player's next turn. -/
  | protectionEverything
  /-- These keywords until end of turn. -/
  | keywords (k : Keywords)
  /-- Hexproof for as long as the source remains on the battlefield. -/
  | hexproofWhileSource
  /-- Prevent all damage this permanent would deal for as long as the
  source remains. Choosing none prevents nothing. -/
  | preventDamageWhileSource
  /-- Landfall: create a 1/1 green Elf whenever a land you control enters. -/
  | landfallCreateElf
  /-- Until end of turn, creatures with toughness greater than their power
  assign combat damage equal to their toughness rather than their power.
  Power is unchanged. -/
  | assignCombatDamageEqualToughness
  /-- Until end of turn, the source's base power is the number of cards in
  its controller's hand. A missing source changes nothing. -/
  | basePowerEqualHand
  /-- Until end of turn, the source gains "{T}: This deals damage equal to
  its power to any other target." Each resolution adds one such ability.
  A missing source gains nothing. -/
  | ironFistTap
deriving Repr, Inhabited, BEq

/-- Who `TriggerResolution.mill` mills. -/
inductive TriggerMillWho where
  /-- The controller. -/
  | you
  /-- The announced player. An illegal target mills nothing. -/
  | target
  /-- The player who lost life. That player's seat is the trigger's
  last-known toughness. A missing seat mills nothing. -/
  | thatPlayer
  /-- Each opponent of the controller. -/
  | eachOpponent
deriving Repr, Inhabited, BEq

/-- Where `TriggerResolution.mill` reads how many cards. The `n` argument
is the count when this is `.fixed`. -/
inductive TriggerMillAmount where
  /-- `n` cards. -/
  | fixed
  /-- The life that player lost. The amount is the trigger's last-known
  power. A missing amount mills nothing. -/
  | thatManyLost
deriving Repr, Inhabited, BEq

/-- What a later step of `TriggerResolution.mill` can read. -/
inductive TriggerMillNote where
  /-- Nothing beyond the mill. -/
  | none
  /-- The cards the controller milled. -/
  | milledCards
  /-- Whether an opponent milled a card. -/
  | opponentsMilled
deriving Repr, Inhabited, BEq

/-- What `TriggerResolution.removeCounters` removes. -/
inductive TriggerRemoveWhat where
  /-- One hope counter. A later `«if» .removedHope` sees whether one was removed. -/
  | hope
  /-- Every counter on that permanent. -/
  | all
deriving Repr, Inhabited, BEq

/-- How far `TriggerResolution.revealLibrary` looks from the top of a library. -/
inductive TriggerLibraryHow where
  /-- The top `n` cards. Looking at zero cards finds nothing. -/
  | top (n : Nat)
  /-- Cards until a creature card. An empty library finds nothing. -/
  | untilCreature
  /-- Cards until a Saga card. An empty library finds nothing. -/
  | untilSaga
  /-- Cards until an instant or sorcery card. An empty library finds nothing. -/
  | untilInstantOrSorcery
  /-- Cards until a nonland card. An empty library finds nothing. -/
  | untilNonland
deriving Repr, Inhabited, BEq

/-- Whose library `TriggerResolution.revealLibrary` looks at. -/
inductive TriggerLibraryWho where
  /-- The controller's library. -/
  | you
  /-- The player who was dealt combat damage. That seat is
  `lastCombatDamagePlayer`. A missing seat is the controller's opponent. -/
  | damagedPlayer
  /-- The announced player. When none was announced, the resolving ability's
  last-known toughness is that player's index. -/
  | announced
deriving Repr, Inhabited, BEq

/-- How many cards `TriggerResolution.revealFromHand` shows (CR 701.16). -/
inductive TriggerRevealCount where
  /-- The whole hand. -/
  | hand
  /-- One card, plus one for each creature card in the controller's
  graveyard. A smaller hand is shown in full. -/
  | onePlusCreatureCards
deriving Repr, Inhabited, BEq

/-- Where `TriggerResolution.putOnLibrary` puts the card. -/
inductive TriggerLibraryPlace where
  /-- On top of the owner's library. -/
  | top
  /-- On the bottom of the owner's library. A card from hand uses the
  controller's library. -/
  | bottom
deriving Repr, Inhabited, BEq

/-- Which outcome of `TriggerResolution.may` resolves `follow`. -/
inductive TriggerMayWhen where
  /-- The player performed `action`. Declining skips `follow`. -/
  | ifYouDo
  /-- The player declined `action`. Performing `action` skips `follow`. -/
  | ifYouDont
deriving Repr, Inhabited, BEq

/-- How long `TriggerResolution.gainControl` lasts. -/
inductive TriggerControlHow where
  /-- Until end of turn. The permanent untaps and gains haste. -/
  | untilEndOfTurn
  /-- For as long as the source remains on the battlefield. -/
  | whileSourceRemains
  /-- You control the announced opponent during their next turn.
  `.gainControl .duringNextTurn`.
  Inside `queueReflexive`, that ability is put on the stack and the
  opponent is chosen then. -/
  | duringNextTurn
deriving Repr, Inhabited, BEq

/-- What `TriggerResolution.becomeCopy` copies, and which exceptions apply.
The source keeps its name when it copies an announced object until the
controller's next turn. Choosing none copies nothing. A missing source
copies nothing. The enchanted creature copies a noted creature until the
source leaves. The controller creates a token copy of the artifact that
caused the trigger. -/
inductive TriggerCopyOf where
  /-- Up to one target artifact, non-Aura enchantment, or land.
  The source is also a legendary 4/4 Human Villain creature with vigilance. -/
  | artifactEnchantmentOrLand
  /-- Up to one target creature, or creature card in a graveyard.
  The source is a legendary Human Mercenary Villain creature. -/
  | creatureOrGraveyardCard
  /-- The creature an earlier step exiled and noted.
  The enchanted creature becomes that copy until the source leaves.
  Nothing noted, or nothing enchanted, copies nothing. -/
  | noted
  /-- The nontoken artifact that caused this trigger.
  An announced permanent is used when one was chosen; otherwise the
  recorded cause. The controller creates a token copy. A noncreature
  token becomes a 2/2 Robot Villain after it enters. -/
  | cause
deriving Repr, Inhabited, BEq

/-- What `TriggerResolution.cant` prevents, and who can't do it.
The announced permanent can't be blocked this turn is `.beBlocked`.
The source is `.beBlocked .source`.
The enchanted creature is `.beBlocked .enchanted`.
The target, while the source remains, is `.beBlocked .targetWhileSource`.
Can't be blocked this turn except by creatures with haste is
`.beBlockedExceptByHaste`.
The announced permanent can't become untapped for as long as you control
the source is `.untapWhileYouControl`. An opponent's creature is the only
recipient. -/
inductive ActionSelector where
  /-- Can't be blocked this turn.
  The announced permanent is `.cant .beBlocked`.
  The source is `.cant (.beBlocked .source)`.
  The enchanted creature is `.cant (.beBlocked .enchanted)`.
  The target, while the source remains, is
  `.cant (.beBlocked .targetWhileSource)`. -/
  | beBlocked (who : TriggerAffected := .target)
  /-- Can't be blocked this turn except by creatures with haste.
  `.cant (.beBlockedExceptByHaste .target)`. -/
  | beBlockedExceptByHaste (who : TriggerAffected := .target)
  /-- Can't become untapped for as long as you control the source.
  The announced permanent is `.cant .untapWhileYouControl`.
  An opponent's creature is the only recipient. A creature you control
  is left alone. Any other `who` does nothing. -/
  | untapWhileYouControl (who : TriggerAffected := .target)
deriving Repr, Inhabited, BEq

/-- What a triggered ability does when it resolves (CR 608). Grouped so
`Game.applyTriggeredAbility` matches resolution shapes instead of every
constructor: scry, drawing, discarding, +1/+1 on the source, divided damage,
putting counters, removing counters, until-end-of-turn pumps, creating tokens,
exile, sacrifice, attach, amass, casting a spell, returning cards to hand,
putting onto the battlefield, adding mana, choosing modes, destroying,
fighting, granting, gaining life, losing life, milling, revealing from
a hand, revealing from a library, searching a library, tapping,
untapping, losing, and putting on a library each cover multiple printed
abilities.
A permanent target uses its own constructor: `pump`, `putCounters`,
`destroy`, `dealDamage`, `grant`, `tap`, `untap`, `exile`, `lose`,
`cant`, `becomeArtifact`, `becomePrepared`, `setBasePT`,
and `putOnLibrary`. Losing indestructible until end of turn, and losing
all abilities while the source remains, are `lose`. What is lost, and who
loses it, are arguments. A permanent that can't be blocked this turn, and
a permanent that can't untap while you control the source, are `cant`.
What it can't do, and who can't, are one `ActionSelector`. Paying mana,
and paying by sacrificing or discarding, are `pay`. What is paid is an
argument. Setting a permanent's base power and toughness to fixed values,
and setting another creature's base power and toughness equal to this
creature's, are `setBasePT`. Each statistic is a `NumberSelector`.
Who receives the new base is an `ObjectSelector`.
Gaining life is `gainLife`. How much is a `NumberSelector`.
Losing life is `loseLife`. How much is a `NumberSelector`.
Who loses it is a `PlayerSelector`.
Putting the announced permanent
on top or on the bottom of its owner's library, and putting a card from your
hand on the bottom, are `putOnLibrary`. Where the card goes is an argument.
Which card is an `ObjectSelector`.
Untapping the announced permanent, and untapping each attacking
creature, are `untap`. Who is untapped is an `ObjectSelector`.
Removing counters is `removeCounters`. Who loses them is an `ObjectSelector`.
Destroying permanents is `destroy`. Which permanents is an `ObjectSelector`.
Tapping permanents is `tap`. Who is tapped is an `ObjectSelector`.
Granting an ability is `grant`. Who receives it is an `ObjectSelector`.
A creature fighting is `fight`. Who fights is an `ObjectSelector`.
+P/+T and trample is
a sequence of `pump` and `grant`. Becoming an artifact and gaining
indestructible is a sequence of `becomeArtifact`
and `grant`. Who becomes an artifact is an `ObjectSelector`.
Who becomes prepared is an `ObjectSelector`.
Who receives a new base power and toughness is an `ObjectSelector`.
Which card is put on a library is an `ObjectSelector`.
Which cards `exile` exiles is an `ObjectSelector`.
Which cards `put` puts onto the battlefield is an `ObjectSelector`.
Tap and a stun counter is a sequence of `tap` and
`putCounters`. The source, the enchanted creature, and a follow-up while
the source remains use those same constructors. `ofSource`, `ofEnchanted`,
and `ofTargetWhileSource` map a `PermanentAction` onto them. +P/+T on the
source is `.pump (.fixed p) (.fixed t) .source`. Tapping the creature this Aura enchants is
`.tap .enchantedWhileSource`. Granting keywords to the target while the
source remains is `.grant (.keywords k) .targetWhileSource`. -/
inductive TriggerResolution where
  /-- Until end of turn, permanents of `who` get +`power`/+`toughness`.
  Each statistic reads its own bonus.
  The source by the greatest power among creatures you control is
  `.pump .greatestPower (.fixed 0) .source`.
  The source +1/+1 per card looked at while scrying is
  `.pump .perLookedAt .perLookedAt .source`.
  The source +1/+1 for each other creature you control is
  `.pump .perOtherCreature .perOtherCreature .source`.
  A target creature you control +1/+1 per Plains is
  `.pump .perPlains .perPlains .target`.
  The creature that caused this +P/+T is `.pump (.fixed p) (.fixed t) .cause`.
  Other permanents of a subtype +X/+X, X = this toughness, is
  `.pump .equalSourceToughness .equalSourceToughness (.othersOfSubtype subtype)`.
  Another target creature +X/+0, X = this power, is
  `.pump .equalSourcePower (.fixed 0) .target`.
  Creatures you control +P/+T is `.pump (.fixed p) (.fixed t) .creaturesYouControl`.
  Other creatures of these subtypes +P/+T is
  `.pump (.fixed p) (.fixed t) (.othersOfSubtypes subtypes)`.
  Creatures opponents control +P/+T is
  `.pump (.fixed p) (.fixed t) .opponentsCreatures`.
  The announced permanent gets +P/+T is `.pump (.fixed p) (.fixed t) .target`.
  Doubling that permanent's power and toughness is `.pump .double .double .target`.
  +P/+T and trample is
  `.sequence [.pump (.fixed p) (.fixed t) .target, .grant (.keywords Keyword.trample) .target]`. -/
  | pump (power toughness : NumberSelector) (who : ObjectSelector)
  /-- Deal damage. `amount` is how much. `.fixed` carries that `n`.
  `who` is who is dealt it, and `note` records a later step.
  Pump and damage share `NumberSelector` and `ObjectSelector`.
  Draw shares `NumberSelector`. Its player is a `PlayerSelector`.
  Each creature blocking the source is `.dealDamage (.fixed n) .blockers`.
  Last-known power to the announced creature is
  `.dealDamage .lastKnownPower .permanent`.
  `n` damage to each opponent is `.dealDamage (.fixed n) (.player .eachOpponent)`.
  When that ability targets, only the announced opponent is dealt damage.
  Damage equal to permanents of `subtype` you control, to each opponent, is
  `.dealDamage (.subtypeCount subtype) (.player .eachOpponent)`.
  Damage equal to Treasures you control, to the target, is
  `.dealDamage (.subtypeCount "Treasure") .target`.
  `n` damage to the target, remembering a marked permanent, is
  `.dealDamage (.fixed n) .target .markedPermanent`.
  Last-known power, noting excess damage, is
  `.dealDamage .lastKnownPower .permanent .excess`.
  Damage to each opponent equal to the hand discarded by an earlier step is
  `.dealDamage .discardedHand (.player .eachOpponent)`.
  `n` damage to the announced opponent is `.dealDamage (.fixed n) (.player .targetOpponent)`.
  `n` damage to the announced target is `.dealDamage (.fixed n) .target`.
  `n` damage to each creature that is not `subtype`, and to each opponent, is
  `.dealDamage (.fixed n) (.eachNonSubtypeAndOpponents subtype)`.
  Damage equal to the greatest mana value among artifacts you control, to
  the announced opponent, is
  `.dealDamage .greatestArtifactMv (.player .targetOpponent)`.
  Damage equal to the mana value of the spell that caused this, to the
  announced player or permanent, is `.dealDamage .spellManaValue .target`.
  The trigger's last-known power to the announced player or permanent, offered
  as a may, is `.may (.dealDamage .lastKnownPower .target) (.sequence []) .ifYouDo`. -/
  | dealDamage (amount : NumberSelector) (who : ObjectSelector)
      (note : TriggerDamageNote := .none)
  /-- Scry, as `n` says. `.fixed` is that many cards.
  Scry 2 is `.scry (.fixed 2)`. Any other amount scries nothing. -/
  | scry (n : NumberSelector)
  /-- `who` draws cards, as `amount` says. `.fixed` is that many cards.
  The controller is `.you`.
  The controller draws `n` is `.draw (.fixed n)`.
  A card for each Human tapped by an earlier step is `.draw .forEachTappedHuman`.
  A card for each graveyard with seven or more cards is `.draw .perFatGraveyard`.
  Cards equal to the hand an earlier step discarded are `.draw .discardedHand`.
  X cards, where X is the mana spent to cast the triggering spell, are
  `.draw .equalToManaSpent`. Spending none skips later steps.
  The targeted opponent may have you draw a card is
  `.draw (.fixed 1) .opponentHasYou`.
  Optional as `.may (.draw (.fixed 1) .opponentHasYou) (.sequence [])`. Declining that
  offer mills and that player loses life; it does not skip.
  The enchanted creature's controller draws a card is
  `.draw (.fixed 1) .enchantedController`. Nothing enchanted draws nothing.
  Cards until the controller has ten in hand are
  `.draw (.upToHandSize 10)`. A hand that already has ten draws nothing.
  One card for each permanent of `ty` the controller controls is
  `.draw (.perControlled ty)`. -/
  | draw (amount : NumberSelector) (who : PlayerSelector := .you)
  /-- Search a library, then resolve `thenDo` for the card that was found.
  A Forest onto the battlefield is `.searchLibrary (.put .forest)`.
  A basic land into your hand is `.searchLibrary (.returnToHand .basicLand)`.
  You may put a basic land on top is `.searchLibrary (.put .basicLandOnTop)`.
  Declining that search does not shuffle.
  A Dragon from your hand and/or library onto the battlefield is
  `.searchLibrary (.put .dragon)`. A card from the library shuffles.
  A card from the hand does not. Choosing not to find does not.
  An empty hand and library still shuffles: nothing was eligible to choose.
  Any other resolution does nothing. `thenDo` does nothing on its own. -/
  | searchLibrary (thenDo : TriggerResolution)
  /-- Discard cards, as `what` says.
  One card from the controller is `.discard` (`.cards`).
  Inside `.may _ _ .ifYouDo`, one card is optional: declining skips the follow-up.
  Each opponent discards one is `.discard (.cards 1 .eachOpponent)`.
  The announced opponent discards `n` is `.discard (.cards n .targetOpponent)`.
  The controller's hand, noting how many cards were discarded, is
  `.discard .hand`.
  Optional as `.may (.discard .hand) (.sequence [])`. Declining leaves the note
  empty so the following draw and damage steps do nothing.
  `n` cards when mana was spent to cast the triggering spell is
  `.«if» .manaSpent (.discard (.cards n))`. Spending none discards nothing.
  The announced opponent reveals their hand and discards a nonland you
  choose with `.discard .chosenNonland`.
  Any other selector discards nothing. -/
  | discard (what : ObjectSelector := .cards)
  /-- Pay `what`. Inside `.may _ _ .ifYouDo`, declining skips the follow-up.
  `{n}` is `.pay (.mana #[.generic n])`. `{1}{G}{U}` is
  `.pay (.mana #[.generic 1, .colored .green, .colored .blue])`.
  Sacrificing another creature is `.pay .anotherCreature`. Its power is noted.
  Sacrificing another creature or artifact is `.pay .anotherCreatureOrArtifact`.
  Sacrificing an artifact, or discarding a card, is `.pay .artifactOrDiscard`.
  Sacrificing an artifact, or discarding a nonland card, is
  `.pay .artifactOrDiscardNonland`. -/
  | pay (what : CostSelector)
  /-- Put counters.
  Each creature you control is `.putCounters (.ofKind .plusOnePlusOne) .youControl`.
  Each permanent of a subtype is
  `.putCounters (.ofKind .plusOnePlusOne) (.youControl (.subtype s))`.
  One counter, or two with the city's blessing, is
  `.putCounters (.ofKind .plusOnePlusOne) (.youControl .citysBlessing)`.
  Each other creature you control is
  `.putCounters (.ofKind .plusOnePlusOne) .eachOther`.
  +1/+1 counters equal to the last-known mana value, on the target, is
  `.putCounters .plusOneLastKnownMv .permanent`.
  A loyalty counter on the source is `.putCounters (.ofKind .loyalty) .source`.
  The source's last-known counters on the target are
  `.putCounters .sourceCounters .permanent`.
  A charge counter on the source is `.putCounters (.ofKind .charge) .source`.
  A quest counter on the source is `.putCounters (.ofKind .quest) .source`.
  Hone counters for each creature the opponent controls are
  `.putCounters .honePerOpponent .source`.
  A plan counter on the source is `.putCounters (.ofKind .plan) .source`.
  Later steps do not run if the source has left.
  A +1/+1 counter you put on the target is
  `.putCounters (.ofKind .plusOnePlusOne) (.permanent true)`.
  The noted number of +1/+1 counters on the created token is
  `.putCounters .plusOneNoted .createdToken`.
  An invasion counter on the source is `.putCounters (.ofKind .invasion) .source`.
  A trample counter on the target is `.putCounters (.ofKind .trample) .permanent`.
  An influence counter on the source, when the opponent is still legal, is
  `.putCounters (.ofKind .influence) .source`. An illegal target skips later steps.
  A loyalty counter on the target is `.putCounters (.ofKind .loyalty) .permanent`.
  +1/+1 counters equal to the sacrificed creature's power are
  `.putCounters .plusOneSacrificedPower .source`.
  `n` +1/+1 counters on the announced permanent are
  `.putCounters (.ofKind .plusOnePlusOne n) .permanent`.
  An indestructible counter on the announced permanent is
  `.putCounters (.ofKind .indestructible) .permanent`.
  A double strike counter is `.putCounters (.ofKind .doubleStrike) .permanent`.
  A burden counter is `.putCounters (.ofKind .burden) .permanent`.
  A stun counter is `.putCounters (.ofKind .stun) .permanent`.
  The keyword counters the announced creature has that the source does not are
  `.putCounters .missingKeywordsFromTarget .source`. An illegal target or a
  missing source puts nothing.
  One +1/+1 counter on each announced creature you control, up to the life
  gained (the trigger's last-known power), is
  `.putCounters (.ofKind .plusOnePlusOne) .eachUpToLastKnown`.
  None, or zero life, puts counters on nothing. An illegal permanent is
  reported and skipped. Extra announced permanents are ignored.
  Any other selector puts nothing. -/
  | putCounters (what : CounterSelector) (who : ObjectSelector)
  /-- Return cards to a hand. `what` says which cards and whose hand.
  `note` says what a later step can read.
  A creature card from your graveyard to your hand is
  `.returnToHand` (`.graveyardCard`).
  The targeted permanent to its owner's hand, noting the return, is
  `.returnToHand .permanent .returnedPermanent`.
  A graveyard permanent card to your hand is
  `.returnToHand .graveyardPermanent`.
  Milled cards of a subtype are `.returnToHand (.milledSubtype subtype)`.
  The source from its owner's graveyard to their hand is
  `.returnToHand .source`.
  The card revealed until a creature, when it does not enter, is
  `.returnToHand .revealed`. Outside that resolution, it does nothing.
  A basic land found by searching is `.returnToHand .basicLand`.
  Outside `searchLibrary`, it does nothing.
  A card the source exiled, to its owner's hand, is
  `.returnToHand .linkedExile`.
  The card that caused this trigger, to its owner's hand, is
  `.returnToHand .cause`. A token ceases to exist.
  Any other selector returns nothing. -/
  | returnToHand (what : ObjectSelector := .graveyardCard)
      (note : TriggerReturnNote := .none)
  /-- Put later ability `followup` on the stack (“When you do”), or arm it
  for a later event. `followup` is that ability.
  Another nonattacking creature gains indestructible is
  `.queueReflexive (.grant (.keywords Keyword.indestructible) .target)`.
  Trick Arrows, paying up to three times, is
  `.queueReflexive (.chooseModes TriggerResolution.trickArrowModes .alreadyChosen)`.
  An indestructible counter is
  `.queueReflexive (.putCounters (.ofKind .indestructible) .permanent)`.
  Controlling an opponent during their next turn is
  `.queueReflexive (.gainControl .duringNextTurn)`.
  An opponent exiling the top five, and casting up to two, is
  `.queueReflexive (.exile (.opponentTop 5) (.mayCastUpTo 2))`.
  A graveyard creature returning tapped and attacking is
  `.queueReflexive (.put .creatureCard .tapped (.entering [.attacking, .counter .finality]))`.
  Destroying an opposing nonland is `.queueReflexive (.destroy .target)`.
  A creature with haste that can't be blocked except by haste is
  `.queueReflexive (.cant (.beBlockedExceptByHaste .target))`.
  Up to two instants or sorceries from the graveyard are
  `.queueReflexive (.returnToHand (.graveyardInstants 2))`.
  A +1/+1 counter on target creature is
  `.queueReflexive (.putCounters (.ofKind .plusOnePlusOne) .permanent)`.
  Damage to any target is `.queueReflexive (.dealDamage (.fixed n) .target)`.
  Damage equal to the source's +1/+1 counters is
  `.queueReflexive (.dealDamage .plusOneCounters .target)`.
  A source that has left queues nothing.
  Exile and copy a milled spell is
  `.queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying)`.
  After opponents mill, that is
  `.«if» .opponentsMilled (.queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying))`.
  Divided damage is
  `.queueReflexive (.dealDamage (.fixed amount) .target .divided)`.
  After the Plan is sacrificed, that is
  `.«if» .planWasSacrificed (.queueReflexive (.dealDamage (.fixed amount) .target .divided))`.
  A Plan that was not sacrificed queues nothing.
  Whenever you attack this turn, +1/+1 for each Plains, is
  `.queueReflexive (.pump .perPlains .perPlains .target)`.
  That arms the attack trigger. It does not put an ability on the stack
  now. Any other resolution queues nothing. -/
  | queueReflexive (followup : TriggerResolution)
  /-- Sacrifice a permanent. `what` says who sacrifices and which permanent.
  `note` says what a later step can read.
  The announced opponent sacrifices a creature of their choice with
  `.sacrifice .opponentChosenCreature`.
  Each player sacrifices a creature of their choice with
  `.sacrifice .eachPlayersCreature`.
  The defending player sacrifices a least-power creature with
  `.sacrifice .leastPower`.
  Each opponent sacrifices a creature that dealt combat damage to you with
  `.sacrifice .combatDamager`.
  The source is sacrificed with `.sacrifice .source`.
  The controller sacrifices the source with
  `.sacrifice (.sacrificedSource .controllerSacrifices)`.
  The source moves as sacrificed, without a token-sacrifice trigger, with
  `.sacrifice (.sacrificedSource .movedAsSacrificed)`.
  `.sacrifice (.sacrificedSource .isSacrificed)` is the same as
  `.sacrifice .source`.
  The Plan, if it is still on the battlefield, is `.sacrifice .plan`.
  The Plan, noting whether the sacrifice happened, is
  `.sacrifice .plan .forReflexive`.
  You may sacrifice another creature with `.may (.sacrifice .another) (.sequence [])`.
  Each opponent sacrifices a nontoken creature of their choice with
  `.sacrifice .chosenNontokenCreature`.
  Any other selector sacrifices nothing. -/
  | sacrifice (what : ObjectSelector) (note : TriggerSacrificeNote := .none)
  /-- A permanent loses `what`, as `who` says.
  The announced permanent loses indestructible until end of turn is
  `.lose .indestructible`.
  The source is `.lose .indestructible .source`.
  The enchanted creature is `.lose .indestructible .enchanted`.
  The target, while the source remains, is
  `.lose .indestructible .targetWhileSource`.
  The announced permanent loses all abilities while the source remains is
  `.lose .allAbilities .targetIfPresent`. A missing target loses nothing.
  A source that has left leaves that permanent able.
  Any other selector loses nothing. -/
  | lose (what : AbilitySelector) (who : ObjectSelector := .target)
  /-- `action` says what can't be done, and who can't do it.
  The announced permanent can't be blocked this turn is `.cant .beBlocked`.
  The source is `.cant (.beBlocked .source)`.
  The enchanted creature is `.cant (.beBlocked .enchanted)`.
  The target, while the source remains, is
  `.cant (.beBlocked .targetWhileSource)`.
  The announced permanent can't become untapped for as long as you control
  the source is `.cant .untapWhileYouControl`. An opponent's creature is
  the only recipient. A creature you control is left alone. A missing
  source still records a stand-in. Any other selector does nothing. -/
  | cant (action : ActionSelector)
  /-- Until end of turn, `who` becomes an artifact in addition to its other
  types. The announced permanent is `.becomeArtifact` (`.target`).
  The source is `.becomeArtifact .source`.
  The enchanted creature is `.becomeArtifact .enchanted`.
  The target, while the source remains, is
  `.becomeArtifact .targetWhileSource`.
  Gaining indestructible as well is
  `.sequence [.becomeArtifact, .grant (.keywords Keyword.indestructible) .target]`.
  Any other selector does nothing. -/
  | becomeArtifact (who : ObjectSelector := .target)
  /-- `who` becomes prepared. A creature that is already prepared, or has no
  prepare spell, does not. The announced permanent is `.becomePrepared`
  (`.target`).
  The source is `.becomePrepared .source`.
  The enchanted creature is `.becomePrepared .enchanted`.
  The target, while the source remains, is
  `.becomePrepared .targetWhileSource`.
  Any other selector does nothing. -/
  | becomePrepared (who : ObjectSelector := .target)
  /-- Until end of turn, `who`'s base power and toughness become `power` and
  `toughness`. Each statistic reads its own value.
  The announced permanent becoming `p`/`t` is `.setBasePT (.fixed p) (.fixed t)`.
  The source is `.setBasePT (.fixed p) (.fixed t) .source`.
  The enchanted creature is `.setBasePT (.fixed p) (.fixed t) .enchanted`.
  The target, while the source remains, is
  `.setBasePT (.fixed p) (.fixed t) .targetWhileSource`.
  Another target creature becoming equal to this creature's power and
  toughness is `.setBasePT .equalSourcePower .equalSourceToughness`.
  A source that has left uses its last-known power and toughness.
  No target logs that none was chosen.
  Any other combination sets nothing. -/
  | setBasePT (power toughness : NumberSelector) (who : ObjectSelector := .target)
  /-- Put a card onto a library. `place` says top or bottom, and `what`
  says which card.
  The announced permanent on top of its owner's library is `.putOnLibrary .top`.
  The announced permanent on the bottom is `.putOnLibrary .bottom`.
  The source is `.putOnLibrary .top .source` or `.putOnLibrary .bottom .source`.
  The enchanted creature is `.putOnLibrary .top .enchanted` or
  `.putOnLibrary .bottom .enchanted`.
  The target, while the source remains, is
  `.putOnLibrary .top .targetWhileSource` or
  `.putOnLibrary .bottom .targetWhileSource`.
  A card from your hand on the bottom of your library is
  `.putOnLibrary .bottom .cardFromHand`. An empty hand skips the choice.
  A card from your hand on top puts nothing.
  Any other selector puts nothing. -/
  | putOnLibrary (place : TriggerLibraryPlace := .top)
      (what : ObjectSelector := .target)
  /-- Deal previously divided damage to the announced targets. -/
  | dividedDamage
  /-- Apply each resolution in order. An illegal required target skips every
  step (CR 608.2b). Return a graveyard card, then gain life equal to its
  power, is `.sequence [.returnToHand .graveyardCard, .gainLife .equalToTargetPower]`.
  Draw, then bottom a card if you control no legendary, is
  `.sequence [.draw (.fixed 1), .«if» .noLegendaryCreature (.putOnLibrary .bottom .cardFromHand)]`.
  Remove a hope counter, draw if one was removed, then sacrifice and gain
  life if none remain, is
  `.sequence [.removeCounters .hope .source, .«if» .removedHope (.draw (.fixed 1)), .«if» .noHopeOnSource (.sequence [.sacrifice .source, .gainLife (.fixed 4)])]`.
  A step that asks a player to choose pauses the later steps until that
  choice finishes; they are still part of this resolution. Tap any number
  of Humans, then draw that many, is
  `.sequence [.may (.tap .humans) (.sequence []), .draw .forEachTappedHuman]`.
  Create one token, then attach the source to it, is
  `.sequence [.createTokens kind 1 false, .attach .source .created]`.
  Gain life, then you may search a basic land onto the top, is
  `.sequence [.gainLife (.fixed n), .searchLibrary (.put .basicLandOnTop)]`.
  Destroy opponents' artifacts and enchantments, then gain 1 life for each
  one actually destroyed, is
  `.sequence [.destroy .oppArtifactsEnchantments (note := .countDestroyed), .gainLife .forEachDestroyedThisWay]`.
  Put a +1/+1 counter on each other creature you control, then gain 1 life
  for each other creature you control, is
  `.sequence [.putCounters (.ofKind .plusOnePlusOne) .eachOther, .gainLife .perOtherCreature]`.
  Deal `n` damage to the target, then destroy it if that damage marked a
  permanent of this subtype, is
  `.sequence [.dealDamage (.fixed n) .target .markedPermanent, .«if» (.dealtDamageToSubtype subtype) (.destroy .permanentDealtDamage)]`.
  Destroy the announced creature, then its controller amasses that power, is
  `.sequence [.destroy .target (note := .forAmass), .amass 0 (amount := .notedPower) (who := .notedController), .«if» .youControlledDestroyed (.draw (.fixed 1))]`.
  Return another permanent to its owner's hand, then put a +1/+1 counter on
  the source if one was actually returned, is
  `.sequence [.returnToHand .permanent .returnedPermanent, .«if» .returnedPermanent (.putCounters (.ofKind .plusOnePlusOne) .source)]`.
  Other creatures you control of these subtypes get +P/+T, and creatures
  your opponents control get +oppP/+oppT, is
  `.sequence [.pump (.fixed p) (.fixed t) (.othersOfSubtypes subtypes), .pump (.fixed oppP) (.fixed oppT) .opponentsCreatures]`.
  Gain 1 life, draw, or put a +1/+1 counter on each creature you control
  when this is the first, second, or third resolve this turn (Belladonna
  Took), is
  `.sequence [.noteResolveThisTurn 3, .«if» (.nthResolve 1) (.gainLife (.fixed 1)), .«if» (.nthResolve 2) (.draw (.fixed 1)), .«if» (.nthResolve 3) (.putCounters (.ofKind .plusOnePlusOne) .youControl)]`.
  Deal the sacrificed creature's power, then amass Goblins for the excess
  (Bolg), is
  `.sequence [.dealDamage .lastKnownPower .permanent .excess, .amass 0 (amount := .notedExcess)]`.
  Put a plan counter, then scry, is
  `.sequence [.putCounters (.ofKind .plan) .source, .scry (.fixed n)]`.
  Put a trample counter on the target, then make it a Bear, is
  `.sequence [.putCounters (.ofKind .trample) .permanent, .becomeBear]`.
  Draw, discard, and a land discarded this way enters tapped, is
  `.sequence [.draw (.fixed 1), .discard (.cards 1), .put .discardedLand (how := .tapped)]`.
  Put an influence counter, scry 2, then offer the opponent's choice
  (Palantír of Orthanc), is
  `.sequence [.putCounters (.ofKind .influence) .source, .scry (.fixed 2), .may (.draw (.fixed 1) (who := .opponentHasYou)) (.sequence [])]`.
  Grant keywords, then a +1/+1 counter if the target is a creature and a
  loyalty counter if it is a planeswalker, is
  `.sequence [.grant (.keywords k) .target, .«if» .targetIsCreature (.putCounters (.ofKind .plusOnePlusOne) .permanent), .«if» .targetIsPlaneswalker (.putCounters (.ofKind .loyalty) .permanent)]`.
  The target gets +3/+0 and gains first strike until end of turn, is
  `.sequence [.pump (.fixed 3) (.fixed 0) .target, .grant (.keywords Keyword.firstStrike) .target]`.
  +P/+T and trample is
  `.sequence [.pump (.fixed p) (.fixed t) .target, .grant (.keywords Keyword.trample) .target]`.
  Becoming an artifact and gaining indestructible is
  `.sequence [.becomeArtifact, .grant (.keywords Keyword.indestructible) .target]`.
  Tap and a stun counter is
  `.sequence [.tap .target, .putCounters (.ofKind .stun) .permanent]`.
  Destroy the target, then its controller creates a Treasure, is
  `.sequence [.destroy .target, .createTokens .treasure 1 false (who := .targetController)]`.
  You may put an artifact from your hand onto the battlefield, then attach
  it to the source if it is Equipment, is
  `.sequence [.may (.put .artifactFromHand (note := .forAttach)) (.sequence []), .«if» .putArtifactIsEquipment (.attach .putArtifact .notedHost)]`. -/
  | sequence (rs : List TriggerResolution)
  /-- The controller may resolve `action`. `when` says which outcome resolves
  `follow`. `.ifYouDont` is the default: declining resolves `follow`, and
  performing `action` skips it. `.ifYouDo` resolves `follow` only when
  `action` is performed. Declining, or being unable to perform `action`,
  skips that follow-up.
  A choice that already includes decline is that choice, so the player
  is not asked twice. You may draw X cards, where X is the mana spent to
  cast the triggering spell, then discard two, is
  `.may (.sequence [.draw .equalToManaSpent, .«if» .manaSpent (.discard (.cards 2))]) (.sequence [])`.
  You may tap any number of untapped Humans is `.may (.tap .humans) (.sequence [])`.
  You may sacrifice another creature is `.may (.sacrifice .another) (.sequence [])`.
  You may put an artifact from your hand onto the battlefield is
  `.may (.put .artifactFromHand (note := .forAttach)) (.sequence [])`.
  You may discard your hand is `.may (.discard .hand) (.sequence [])`.
  The targeted opponent may have you draw a card is
  `.may (.draw (.fixed 1) (who := .opponentHasYou)) (.sequence [])`. Declining that offer mills and
  that player loses life; it does not skip.
  You may put a land card from your hand onto the battlefield tapped is
  `.may (.put .landFromHand (how := .tapped)) (.sequence [])`.
  `SharedTrigger.may a` resolves as `.may` of `a`'s resolution and an empty sequence.
  Declining, or being unable to put a creature of `subtype` with mana value
  at most `maxMv` from your hand, draws a card with
  `.may (.put (.creatureFromHand subtype maxMv)) (.draw (.fixed 1))`.
  Declining with no other effect is `.may action (.sequence [])`.
  You may discard a card to draw `n` is `.may (.discard (.cards 1)) (.draw (.fixed n)) .ifYouDo`.
  `SharedTrigger.mayTo a b` resolves as `.may` of each step's resolution, `.ifYouDo`.
  You may pay `{n}` to draw is `.may (.pay (.mana #[.generic n])) (.draw (.fixed 1)) .ifYouDo`.
  Paying `{n}` to put a +1/+1 counter on the source and draw is
  `.may (.pay (.mana #[.generic n])) (.sequence [.putCounters (.ofKind .plusOnePlusOne) .source, .draw (.fixed 1)]) .ifYouDo`.
  You may sacrifice another creature for +1/+1 counters equal to its power is
  `.may (.pay .anotherCreature) (.putCounters .plusOneSacrificedPower .source) .ifYouDo`.
  You may pay `{1}{G}{U}` to return this from the graveyard is
  `.may (.pay (.mana #[.generic 1, .colored .green, .colored .blue])) (.returnToHand .source) .ifYouDo`.
  You may sacrifice another creature or artifact to draw and create a Treasure is
  `.may (.pay .anotherCreatureOrArtifact) (.sequence [.draw (.fixed 1), .createTokens .treasure 1 false]) .ifYouDo`.
  You may discard your hand to draw `n` is `.may (.discard .hand) (.draw (.fixed n)) .ifYouDo`.
  You may draw for each permanent of a type, and each opponent draws if you do, is
  `.may (.draw (.perControlled ty)) (.draw (.fixed 1) (who := .eachOpponent)) .ifYouDo`.
  You may sacrifice an artifact or discard a card to draw is
  `.may (.pay .artifactOrDiscard) (.draw (.fixed 1)) .ifYouDo`.
  You may sacrifice another creature to destroy an opposing nonland is
  `.may (.pay .anotherCreature) (.queueReflexive (.destroy .target)) .ifYouDo`.
  You may sacrifice an artifact or discard a nonland to deal 2 damage is
  `.may (.pay .artifactOrDiscardNonland) (.queueReflexive (.dealDamage (.fixed 2) .target)) .ifYouDo`.
  You may tap this to grant indestructible is
  `.may (.tap .source) (.queueReflexive (.grant (.keywords Keyword.indestructible) .target)) .ifYouDo`.
  You may pay {1} to put a +1/+1 counter on target creature is
  `.may (.pay (.mana #[.generic 1])) (.queueReflexive (.putCounters (.ofKind .plusOnePlusOne) .permanent)) .ifYouDo`.
  You may pay {1} so a target creature with haste can't be blocked this turn
  except by creatures with haste is
  `.may (.pay (.mana #[.generic 1])) (.queueReflexive (.cant (.beBlockedExceptByHaste .target))) .ifYouDo`.
  You may pay {3}{B} to return a graveyard creature tapped and attacking is
  `.may (.pay (.mana #[.generic 3, .colored .black])) (.queueReflexive (.put .creatureCard .tapped (.entering [.attacking, .counter .finality]))) .ifYouDo`.
  You may have the source deal the damage that caused this to the announced
  target is `.may (.dealDamage .lastKnownPower .target) (.sequence []) .ifYouDo`.
  The amount is the trigger's last-known power. Already used this turn does
  nothing. An illegal target is reported. The source need not still be on
  the battlefield.
  You may choose new targets for the spell that caused this is
  `.may .retargetCause (.sequence []) .ifYouDo`.
  You may pay {1} up to three times, then choose that many modes, is
  `.may (.pay (.mana #[.generic 1])) (.queueReflexive (.chooseModes TriggerResolution.trickArrowModes .alreadyChosen)) .ifYouDo`.
  You may pay {2} to copy the nontoken artifact that caused this is
  `.may (.pay (.mana #[.generic 2])) (.becomeCopy .cause) .ifYouDo`.
  You may exile the discarded card and play it until the end of your next
  turn with
  `.may (.exile .discarded .playUntilNextTurn) (.sequence []) .ifYouDo`.
  You may create a 0/4 Wall creature token with defender with
  `.may (.createTokens .wall04defender 1 false) (.sequence []) .ifYouDo`.
  Declining creates nothing. -/
  | may (action follow : TriggerResolution) (when : TriggerMayWhen := .ifYouDont)
  /-- You gain life (CR 118.2), as `amount` says.
  You gain `n` life is `.gainLife (.fixed n)`.
  Life equal to the targeted card's power is `.gainLife .equalToTargetPower`.
  Inside `sequence`, that power is read when the sequence starts, before an
  earlier step moves the card.
  1 life for each permanent destroyed by an earlier step is
  `.gainLife .forEachDestroyedThisWay`.
  1 life for each other creature you control is `.gainLife .perOtherCreature`.
  Life equal to the Equipment attached to the source is
  `.gainLife .attachedEquipment`. A source that has left uses its last-known
  power. Zero gains nothing.
  Any other selector gains nothing. -/
  | gainLife (amount : NumberSelector)
  /-- Exile cards. `what` says which cards, `how` says for how long, and
  `note` says what a later step can read.
  Which cards is an `ObjectSelector`.
  The targeted permanent, linked for a leave trigger, is
  `.exile .target .leaveTrigger`.
  The targeted permanent until the source leaves is
  `.exile .target .untilSourceLeaves`.
  The top card, playable until the end of your next turn, is
  `.exile .top .playUntilNextTurn`.
  The top card, playable this turn, and +2/+1 on the source when it is a
  Hero, is `.exile .top .playThisTurn .ifHero`. You may do so with
  `.may (.exile .top .playThisTurn .ifHero) (.sequence [])`.
  A missing source still exiles the card. An empty library exiles nothing.
  Each announced permanent until the source leaves is
  `.exile .eachTarget .untilSourceLeaves`.
  The targeted permanent until the next end step is
  `.exile .target .nextEndStep`.
  Targeted lands, remembered so they return tapped, are
  `.exile .landsYouControl .forLater .lands`.
  Another creature until the source leaves, remembered for a copy, is
  `.exile .target .untilSourceLeaves .copyAndHost`.
  A graveyard card, remembered so it can be played, is
  `.exile .graveyardCard .forLater .playCard`.
  Cards from the damaged player's library until an instant or sorcery,
  remembered for `.mayCast .impulse`, are
  `.exile .top .forLater .impulse` inside `revealLibrary`. Outside that
  resolution, the exile does nothing.
  The nonland from `revealLibrary .untilNonland`, cast with mana of any
  type until end of turn when the counter is declined, is
  `.exile .top .forLater .anyManaThisTurn` inside that resolution.
  Outside it, the exile does nothing.
  The announced permanent, with no return, is `.exile .target .forLater`.
  The source is `.exile .source .forLater`.
  The enchanted creature is `.exile .enchanted .forLater`.
  The target, while the source remains, is
  `.exile .targetWhileSource .forLater`.
  The announced nonland the controller still controls, other than the
  source, exiled and returned immediately, is
  `.exile .target .returnImmediately`. Choosing none does nothing.
  While the source is harnessed is
  `.«if» .sourceHarnessed (.exile .target .returnImmediately)`.
  An unharnessed source is reported and exiles nothing.
  The announced nontoken artifact or creature, returned tapped, is
  `.exile .target .returnTapped`. Choosing none does nothing.
  You may exile the card recorded as this trigger's last-known power and
  play it until the end of your next turn with
  `.may (.exile .discarded .playUntilNextTurn) (.sequence []) .ifYouDo`.
  A card that has left your graveyard is reported. No recorded card is
  reported. Declining exiles nothing.
  Any other selector exiles nothing. -/
  | exile (what : ObjectSelector) (how : TriggerExileHow)
      (note : TriggerExileNote := .none)
  /-- Put cards onto the battlefield. `what` says which cards, `how` says
  how they enter, and `note` says what a later step can read.
  Which cards is an `ObjectSelector`.
  Cards the source exiled are `.put .linkedExile`.
  A nonland permanent card with mana value at most `mv` from a graveyard is
  `.put (.nonlandMvAtMost mv)`.
  The source, returned as an artifact, is `.put .source (how := .asArtifact)`.
  Lands an earlier step exiled, returned tapped, are
  `.put .notedLands (how := .tapped)`.
  The land an earlier step discarded, entering tapped, is
  `.put .discardedLand (how := .tapped)`.
  A land card from your hand, entering tapped, is
  `.put .landFromHand (how := .tapped)`.
  Optional as `.may (.put .landFromHand (how := .tapped)) (.sequence [])`.
  An artifact card from your hand, remembered for a later attach, is
  `.put .artifactFromHand (note := .forAttach)`.
  Optional as `.may (.put .artifactFromHand (note := .forAttach)) (.sequence [])`.
  An empty hand skips that choice.
  A random creature from the cards revealed off the top is
  `.put .randomCreature`. The card revealed until a Saga, or the cheap
  creature, is `.put .revealed`. Outside those resolutions, both do nothing.
  A Forest found by searching is `.put .forest`. A basic land put on top
  after that search is `.put .basicLandOnTop`.   A Dragon found in the hand
  and/or library is `.put .dragon`. Outside `searchLibrary`, those do nothing.
  The announced creature card with mana value at most `n` is
  `.put (.creatureMvAtMost n)`.
  The source from its owner's graveyard, under its owner's control,
  losing all abilities, gaining haste, and entering with a +1/+1 counter, is
  `.put .source .underOwner (.entering [.loseAllAbilities, .keywords Keyword.haste, .counter .plusOnePlusOne (asEnters := true)])`.
  A source that has left the graveyard is reported.
  The Villain that caused this, under its owner's control, as a Hero with
  a finality counter, is
  `.put (.cause (some "Villain")) .underOwner (.entering [.additionalSubtype "Hero", .counter .finality])`.
  A missing cause puts nothing.
  Any other selector puts nothing. -/
  | put (what : ObjectSelector) (how : TriggerPutHow := .asPrinted)
      (note : TriggerPutNote := .none)
  /-- Remove counters. `what` says which, and `who` says from whom.
  A hope counter from the source is `.removeCounters .hope .source`.
  Removing none leaves the later draw skipped. A missing source, or a
  source that has left the battlefield, removes nothing.
  All counters from the enchanted creature are
  `.removeCounters .all .enchanted`. Nothing enchanted removes nothing.
  Any other selector removes nothing. -/
  | removeCounters (what : TriggerRemoveWhat) (who : ObjectSelector)
  /-- Tap permanents, as `who` says.
  Any number of untapped Humans you control is `.tap .humans`.
  Choosing none taps nothing. Optional as `.may (.tap .humans) (.sequence [])`.
  The creature the source enchants is `.tap .enchanted`.
  Nothing enchanted taps nothing. A missing source taps nothing.
  The announced permanent, if it is still on the battlefield, is
  `.tap .targetIfPresent`. A missing target taps nothing.
  The announced permanent, while it is still a legal target, is
  `.tap .target`. An illegal target is reported.
  Wrapping one in `may` is that tap.
  The creature this Aura enchants, while the Aura remains, is
  `.tap .enchantedWhileSource`.
  Any other selector taps nothing. -/
  | tap (who : ObjectSelector)
  /-- Untap permanents, as `who` says.
  The announced permanent, while it is still a legal target, is `.untap`.
  An illegal target is reported. A stun counter is removed instead of
  untapping (CR 122.1d).
  The source is `.untap .source`. A missing source untaps nothing.
  The enchanted creature is `.untap .enchanted`. Nothing enchanted untaps
  nothing.
  The announced permanent while the source remains is
  `.untap .targetWhileSource`. A source that already left is silent.
  Each attacking creature is `.untap .attackingCreatures`.
  Tap or untap is `.or [.tap .target, .untap]`.
  Any other selector untaps nothing. -/
  | untap (who : ObjectSelector := .target)
  /-- Destroy permanents. `what` says which, and `note` says what a later
  step can read.
  Opponents' artifacts and enchantments, counted for the next step, are
  `.destroy .oppArtifactsEnchantments (note := .countDestroyed)`.
  Only permanents that actually leave are counted.
  The permanent an earlier step dealt damage to is
  `.destroy .permanentDealtDamage`.
  The announced creature, noting its controller and power, is
  `.destroy .target (note := .forAmass)`. No target means no player amasses.
  The announced permanent is `.destroy .target`.
  The announced token, when this ability's target is a player, is
  `.destroy .target (note := .chosenToken)`.
  The source is `.destroy .source`.
  The enchanted creature is `.destroy .enchanted`.
  The target, while the source remains, is `.destroy .targetWhileSource`.
  Any other selector destroys nothing. -/
  | destroy (what : ObjectSelector) (note : TriggerDestroyNote := .none)
  /-- Recruit. “recruit” is `.recruit`. “you recruit” is `.recruit .you`. -/
  | recruit (who : RecruitSubject := .recruit)
  /-- Amass `subtype` for `who`, as `amount` says. `n` is the count when
  `amount` is `.fixed`. Attach the source when `attachSource` is true.
  Goblins `n` is `.amass n`.
  Orcs `n` is `.amass n "Orc"`.
  Equal to this creature's power is `.amass 0 (amount := .sourcePower)`.
  Then attach this Equipment is `.amass n (attachSource := true)`.
  Equal to the excess an earlier step noted is
  `.amass 0 (amount := .notedExcess)`.
  The noted controller amasses that creature's power is
  `.amass 0 (amount := .notedPower) (who := .notedController)`. -/
  | amass (n : Nat) (subtype : String := "Goblin")
      (amount : AmassAmount := .fixed) (attachSource : Bool := false)
      (who : AmassWho := .you)
  /-- Create tokens. `n` of `kind` is `.createTokens kind n tapped`.
  `kind` and `n` are that token and that count when `token` is `.kind` and
  `qty` is `.fixed`. A last-known count of Bird Soldiers also reads `kind`.
  An Axe is `.createTokens .treasure 1 false .axe`.
  Attaching that Axe is
  `.createTokens .treasure 1 false .axe (note := .attachReflexive)`.
  Tapped Treasures equal to opposing artifacts are
  `.createTokens .treasure 0 true (qty := .oppArtifacts)`.
  A Treasure for each artifact the damaged player controls is
  `.createTokens .treasure 0 false (qty := .damagedPlayerArtifacts)`.
  Bird Soldiers equal to the last-known count are
  `.createTokens .birdSoldier 0 false (qty := .lastKnown)`.
  Treasures equal to that count are
  `.createTokens .treasure 0 false (qty := .lastKnown)`.
  Treasures for each creature of a chosen type are
  `.createTokens .treasure 0 false (qty := .chosenCreatureType)`.
  Zabu is `.createTokens .treasure 1 false .zabu`.
  The announced opponent creates The Void with
  `.createTokens .treasure 1 false .theVoid .targetOpponent`.
  Redwing is `.createTokens .treasure 1 false .redwing`.
  An Alien, remembering invasion counters, is
  `.createTokens .treasure 1 false .alien (note := .invasion)`.
  A Sturdy Shield, remembered for a later attach, is
  `.createTokens .treasure 1 false .sturdyShield (note := .remember)`.
  The target's controller creates a Treasure with
  `.createTokens .treasure 1 false (who := .targetController)`.
  One 1/1 blue Merfolk for each blue mana symbol in the spell that caused
  this is `.createTokens .treasure 0 false .merfolk (qty := .blueManaSymbols)`. -/
  | createTokens (kind : TokenKind) (n : Nat) (tapped : Bool)
      (token : TriggerToken := .kind) (who : TriggerTokenWho := .you)
      (qty : TriggerTokenQty := .fixed) (note : TriggerTokenNote := .none)
  /-- Attach `what` to `host`.
  The source to the token created by the previous step is
  `.attach .source .created`.
  The source to the targeted permanent is `.attach .source .target`.
  Target Equipment to up to one target creature you control is
  `.attach .target .optionalCreature`.
  The source to the creature target is `.attach .source .creatureTarget`.
  Any number of Equipment you control to the target creature is
  `.attach .anyYouControl .target`.
  The token an earlier step remembered, attached to the source, is
  `.attach .created .source`.
  The artifact put from hand, attached to the remembered creature, is
  `.attach .putArtifact .notedHost`. -/
  | attach (what : TriggerAttachWhat) (host : TriggerAttachTo)
  /-- Add mana. `types` is the printed mana when `amount` is `.fixed`.
  Adding those types is `.addMana types`.
  {G} for each charge counter on the source is
  `.addMana #[.colored .green] (amount := .perChargeCounter)`. -/
  | addMana (types : Array ManaType) (amount : TriggerManaAmount := .fixed)
  /-- Set the source's base P/T. -/
  | becomePT (power toughness : Int)
  /-- Look at the top `n` and reveal a listed type. -/
  | lookAtTopRevealTypes (n : Nat) (types : Array String)
  /-- Gain control of the announced permanents, as `how` says.
  Until end of turn, then untap and haste, is `.gainControl .untilEndOfTurn`.
  While the source remains is `.gainControl .whileSourceRemains`.
  A source that has left changes nothing in that case. -/
  | gainControl (how : TriggerControlHow)
  /-- Put a hone counter on each Equipment you control. -/
  | honeEachEquipment
  /-- Cascade: exile until a cheaper nonland, then you may cast it. -/
  | cascade
  /-- Record another resolution of this ability this turn. Later
  `«if» (.nthResolve n)` steps in this sequence see the ordinal. An ordinal
  above `limit` logs that the ability has no effect. -/
  | noteResolveThisTurn (limit : Nat)
  /-- Resolve `thenDo` when `cond` holds.
  Putting a card on the bottom when you control no legendary creature is
  `.«if» .noLegendaryCreature (.putOnLibrary .bottom .cardFromHand)`.
  Drawing when an earlier step removed a hope counter is
  `.«if» .removedHope (.draw (.fixed 1))`.
  Doing `thenDo` on the nth resolution this turn is
  `.«if» (.nthResolve n) thenDo`.
  Attaching the artifact put from hand when it is Equipment is
  `.«if» .putArtifactIsEquipment (.attach .putArtifact .notedHost)`.
  Exiling and returning the announced permanent while the source is
  harnessed is
  `.«if» .sourceHarnessed (.exile .target .returnImmediately)`.
  An unharnessed source is reported. A missing source does nothing.
  Drawing when an artifact entered under your control this turn is
  `.«if» .artifactEnteredThisTurn (.draw (.fixed 1))`. None did is reported.
  Drawing when the source's power is at least 4 is
  `.«if» (.sourcePowerAtLeast 4) (.draw (.fixed 1))`. A source that has left uses
  its last-known power. Power below 4 is reported.
  Draining for the Equipment attached to the source is
  `.«if» .attachedEquipment (.sequence [.loseLife .attachedEquipment .eachOpponent, .gainLife .attachedEquipment])`.
  No Equipment is reported.
  Discarding `n` cards when mana was spent to cast the triggering spell is
  `.«if» .manaSpent (.discard (.cards n))`. Spending none discards nothing. -/
  | «if» (cond : TriggerIf) (thenDo : TriggerResolution)
  /-- Resolve `whenTrue` when `cond` holds, and `whenFalse` otherwise.
  A tapped Villain when your graveyard has two creature cards, and milling
  two otherwise, is
  `.ifElse (.creatureCardsInGraveyardAtLeast 2) (.createTokens .villain21menace 1 true) (.mill 2)`.
  Two +1/+1 counters when the target is another Hero, and one otherwise, is
  `.ifElse (.targetIsAnotherSubtype "Hero") (.putCounters (.ofKind .plusOnePlusOne 2) .permanent) (.putCounters (.ofKind .plusOnePlusOne) .permanent)`.
  A +1/+1 counter when you have scried or surveilled, and +1/+1 until end of
  turn otherwise, is
  `.ifElse .scriedOrSurveilledThisTurn (.putCounters (.ofKind .plusOnePlusOne) .permanent) (.pump (.fixed 1) (.fixed 1) .target)`.
  The revealed creature enters when its mana value is at most the lands
  you control, and goes to your hand otherwise, with
  `.ifElse .revealedManaValueAtMostLands (.put .revealed) (.returnToHand .revealed)`.
  Outside `revealLibrary .untilCreature`, that condition does not hold. -/
  | ifElse (cond : TriggerIf) (whenTrue whenFalse : TriggerResolution)
  /-- The controller chooses one of these resolutions.
  Tap an opposing creature or untap one you control is
  `.or [.tap .target, .untap]`.
  A +1/+1 counter on a Wolf you control, or a Treasure token, is
  `.or [.putCounters (.ofKind .plusOnePlusOne) .permanent, .createTokens .treasure 1 false]`.
  Tap or untap the targeted nonland is
  `.or [.tap .target, .untap]`.
  A Food token or a Treasure token is
  `.or [.createTokens .food 1 false, .createTokens .treasure 1 false]`.
  +1/+1 counters on the creature targets, or returning an artifact or
  enchantment card from the graveyard, is
  `.or [.putCounters (.ofKind .plusOnePlusOne) .permanent, .returnToHand .graveyardCard]`. -/
  | or (rs : List TriggerResolution)
  /-- Resolve these modes, as `how` says.
  Alliance is `.chooseModes TriggerResolution.allianceModes .oneUnusedThisTurn`.
  Gollum is `.chooseModes TriggerResolution.gollumModes .oneUnused`.
  Chosen up to X, in printed order, is
  `.chooseModes TriggerResolution.upToXModes .alreadyChosen`.
  A +1/+1 counter on the source, or removing a counter to draw, is
  `.chooseModes TriggerResolution.hydeModes .plusOneOrRemoveCounter`.
  One unused Vision mode this turn is
  `.chooseModes TriggerResolution.visionModes .vision`. -/
  | chooseModes (modes : List TriggerResolution) (how : TriggerModeHow)
  /-- You may cast a spell. `origin` says where the card is, `maxMv` limits
  its mana value, `cost` says whether that cost is paid, and `note` says
  what happens to an instant or sorcery cast this way.
  An artifact, instant, or sorcery from your graveyard, with instants and
  sorceries exiled instead, is
  `.mayCast .graveyard .unlimited .pay .exileInstead`.
  An instant or sorcery from your hand with mana value at most twice the
  legendary Wizards you control, without paying, is
  `.mayCast .hand .twiceLegendaryWizards .withoutPaying`.
  An instant or sorcery from your hand with mana value at most that damage,
  without paying, is `.mayCast .hand .lastKnown .withoutPaying`.
  The instant or sorcery exiled by the previous step, without paying, is
  `.mayCast .impulse .unlimited .withoutPaying`.
  A spell from the cards `revealLibrary (.top n)` just looked at, with mana
  value at most the greatest power among attacking creatures you control,
  without paying, is
  `.mayCast .looked .greatestAttackingPower .withoutPaying` inside that
  resolution. Outside it, the cast does nothing. -/
  | mayCast (origin : TriggerCastFrom) (maxMv : TriggerCastMv)
      (cost : TriggerCastCost) (note : TriggerCastNote := .none)
  /-- Grant an ability. `what` says which, and `who` says to whom.
  Each equipped attacking creature gains double strike until end of turn
  with `.grant .doubleStrike .equippedAttackers`.
  If the source was cast, the controller gains protection from everything
  until their next turn with `.grant .protectionEverything .youIfCast`.
  A source that was not cast does nothing.
  The announced permanent gains these keywords until end of turn with
  `.grant (.keywords k) .target`.
  The announced permanent gains hexproof while the source remains with
  `.grant .hexproofWhileSource .target`. A missing source grants nothing.
  Damage the announced permanent would deal is prevented while the source
  remains with `.grant .preventDamageWhileSource .target`. Choosing none
  prevents nothing.
  Until end of turn, creatures you control with toughness greater than their
  power assign combat damage equal to their toughness with
  `.grant .assignCombatDamageEqualToughness .creaturesYouControl`.
  You may pay 2 life to do so with
  `.may (.loseLife (.fixed 2)) (.grant .assignCombatDamageEqualToughness .creaturesYouControl) .ifYouDo`.
  Unable to pay is reported. Declining pays nothing. Power is unchanged.
  Until end of turn, the source's base power equals the cards in hand with
  `.grant .basePowerEqualHand .source`. Drawing first is
  `.sequence [.draw (.fixed 1), .grant .basePowerEqualHand .source]`.
  A missing source still draws and does not change a power.
  Iron Fist's tap ability until end of turn is `.grant .ironFistTap .source`.
  Each resolution adds one. A missing source gains nothing.
  Flying on each creature the causing spell targets is
  `.grant (.keywords Keyword.flying) .spellTargets`. A noncreature target
  is skipped. No recorded spell grants nothing.
  Any other selector does nothing. -/
  | grant (what : TriggerGrantWhat) (who : ObjectSelector)
  /-- Look at cards from the top of a library, as `how` and `who` say, then
  resolve `thenDo` for the cards that were found.
  The top `n` cards of your library, a random creature from among them
  onto the battlefield, and the rest on the bottom in a random order, is
  `.revealLibrary (.top n) (.put .randomCreature)`. Looking at zero cards,
  or no creature among them, logs that no creature was revealed. With
  `norandom` and more than one creature, that choice waits.
  Cards from the top of your library until a creature, onto the battlefield
  when its mana value is at most the lands you control and into your hand
  otherwise, is
  `.revealLibrary .untilCreature (.ifElse .revealedManaValueAtMostLands (.put .revealed) (.returnToHand .revealed))`.
  Cards from the top of your library until a Saga, onto the battlefield, is
  `.revealLibrary .untilSaga (.put .revealed)`.
  An empty library for those two cases changes nothing.
  Cards from the top of the damaged player's library until an instant or
  sorcery, exiled face up for `.mayCast .impulse`, is
  `.revealLibrary .untilInstantOrSorcery (.exile .top .forLater .impulse) .damagedPlayer`.
  A missing damaged player is the controller's opponent. An empty library
  still remembers the impulse, with nothing exiled.
  Cards from the announced player's library until a nonland. You may put
  a +1/+1 counter on the source. If you don't, you may cast that nonland
  until end of turn and spend mana of any type. That is
  `.revealLibrary .untilNonland (.may (.putCounters (.ofKind .plusOnePlusOne) .source) (.exile .top .forLater .anyManaThisTurn) .ifYouDont) .announced`.
  A missing player is reported. An empty library exiles nothing. A source
  that has left grants the cast without asking for the counter.
  The top `n` cards. You may cast a spell from among them with mana value at
  most the greatest power among attacking creatures you control, without
  paying its mana cost. The rest go on the bottom in a random order. That is
  `.revealLibrary (.top n) (.mayCast .looked .greatestAttackingPower .withoutPaying)`.
  An empty library is reported. No attacker limits the mana value to zero.
  Any other combination does nothing. -/
  | revealLibrary (how : TriggerLibraryHow) (thenDo : TriggerResolution)
      (who : TriggerLibraryWho := .you)
  /-- Mill cards (CR 701.13). `n` is how many when `amount` is `.fixed`.
  `who` says who mills, and `note` says what a later step can read.
  Milling zero cards changes nothing. A library that runs out logs that
  it is empty and mills nothing further.
  The controller mills `n` with `.mill n`.
  The announced player mills `n` with `.mill n .target`.
  The player who lost life mills that many with
  `.mill 0 .thatPlayer .thatManyLost`.
  The controller mills `n` and remembers those cards with
  `.mill n (note := .milledCards)`.
  Each opponent mills `n`, and a later step sees whether any card was
  milled, with `.mill n .eachOpponent (note := .opponentsMilled)`.
  Any other combination mills nothing. -/
  | mill (n : Nat) (who : TriggerMillWho := .you)
      (amount : TriggerMillAmount := .fixed)
      (note : TriggerMillNote := .none)
  /-- Create two nonlegendary token copies of the source. -/
  | copySelfNonlegendary
  /-- The Ring tempts you. -/
  | ringTempts
  /-- Spells of `which` cost `{n}` less this turn.
  A card type is `.spellsCostLess (.cardType ty) n`.
  A supertype is `.spellsCostLess (.supertype s) n`. -/
  | spellsCostLess (which : SpellCostLess) (n : Nat)
  /-- Investigate (create a Clue). -/
  | investigate
  /-- Connive (CR 701.48). The source is `.connive`. A target is
  `.connive (.target kind)`. -/
  | connive (who : ConniveSubject := .source)
  /-- A creature fights, or deals damage equal to its power. `who` says
  which creature, and `how` says which.
  The source fights up to one other target creature with `.fight`.
  Choosing none fights nothing. A missing source or an illegal target
  fights nothing.
  The creature that received Equipment deals damage equal to its power
  to up to one target creature with `.fight .equipmentHost .reflexive`.
  That target is chosen when the reflexive ability is put on the stack.
  Nothing is queued when no creature received Equipment.
  Any other selector fights nothing. -/
  | fight (who : ObjectSelector := .source) (how : TriggerFightHow := .mutual)
  /-- A player reveals cards from their hand (CR 701.16), as `count` says,
  then resolves `thenDo`.
  The opponent reveals their hand. You may exile a nonland card from it, or
  the chosen creature, until the source leaves, with
  `.revealFromHand .hand (.exile .target .untilSourceLeaves)`.
  A source that has already left still reveals; nothing is exiled.
  The announced player reveals one card plus one for each creature card in
  your graveyard. You choose one of them and that player discards it, with
  `.revealFromHand .onePlusCreatureCards (.discard (.cards 1 .targetOpponent))`.
  A smaller hand is revealed in full.
  Any other combination does nothing. -/
  | revealFromHand (count : TriggerRevealCount) (thenDo : TriggerResolution)
  /-- Surveil `n` (CR 701.25). -/
  | surveil (n : Nat)
  /-- Empower Jace `n` (Reality Fracture). -/
  | empowerJace (n : Nat)
  /-- The source becomes prepared.
  If it isn't prepared is `.prepareSource`.
  If three or more creatures died this turn is
  `.prepareSource .ifThreeCreaturesDied`. -/
  | prepareSource (when : PrepareWhen := .ifNotPrepared)
  /-- Mark tokens from the previous step attacking. -/
  | markRecentTokensAttacking
  /-- There is an additional combat phase after this one. -/
  | additionalCombatPhase
  /-- The target becomes a Bear in addition to its other types. -/
  | becomeBear
  /-- A player loses life (CR 118.3a), as `amount` and `who` say.
  Losing 0 life does nothing.
  You lose `n` life is `.loseLife (.fixed n)`.
  The announced opponent loses `n` life is
  `.loseLife (.fixed n) .targetOpponent`.
  Each opponent loses `n` life is `.loseLife (.fixed n) .eachOpponent`.
  You lose 1 life for each burden counter on the source is
  `.loseLife .perBurden`.
  A missing source loses nothing.
  Each opponent loses life equal to the Equipment attached to the source with
  `.loseLife .attachedEquipment .eachOpponent`.
  A source that has left uses its last-known power. Zero loses nothing.
  Any other selector loses nothing. -/
  | loseLife (amount : NumberSelector) (who : PlayerSelector := .you)
  /-- You may play the exiled card until the end of your next turn. -/
  | grantPlayNotedUntilNextTurn
  /-- You win the game. -/
  | winTheGame
  /-- Shuffle the source into its owner's library. -/
  | shuffleSource
  /-- The following surveil returns a card with mana value at most the life
  you gained this turn. -/
  | armSurveilReturnLifeGained
  /-- The source becomes a copy of the announced object until your next turn,
  as `of` says. It keeps its name.
  An artifact, non-Aura enchantment, or land, also a legendary 4/4 Human
  Villain creature with vigilance, is `.becomeCopy .artifactEnchantmentOrLand`.
  A creature or a creature card in a graveyard, as a legendary Human
  Mercenary Villain creature, is `.becomeCopy .creatureOrGraveyardCard`.
  Choosing none copies nothing. An illegal object is reported.
  A missing source copies nothing.
  The enchanted creature copying the creature an earlier step noted is
  `.becomeCopy .noted`. Nothing noted copies nothing.
  A token copy of the nontoken artifact that caused this is
  `.becomeCopy .cause`. An announced permanent is used when one was chosen;
  otherwise the recorded cause. The source need not still be on the
  battlefield. A noncreature token becomes a 2/2 Robot Villain after it
  enters. -/
  | becomeCopy (of : TriggerCopyOf)
  /-- Choose new targets for the spell that caused this trigger.
  The recorded cause is used when one was chosen. Otherwise the spell on
  the stack that targets the source. A spell that has left changes nothing.
  You may do so with `.may .retargetCause (.sequence []) .ifYouDo`.
  Declining a target leaves it unchanged and asks about the next one. -/
  | retargetCause
  /-- Copy the spell that caused this trigger. You may choose new targets
  for the copy. A spell that has left the stack is reported. No recorded
  spell copies nothing. Two +1/+1 counters on the source, then that copy, is
  `.sequence [.putCounters (.ofKind .plusOnePlusOne 2) .source, .copyCause]`.
  A missing source still copies the spell. -/
  | copyCause
deriving Repr, Inhabited, BEq

namespace TriggerResolution

/-- What `queueReflexive` does with a follow-up resolution.
`.modeled` queues that MSH reflexive. `times` is how many times a mana
cost may be paid. `.counters` reads the source's +1/+1 counters as the
paid count. `.damage` deals that much to any target. `.copy` exiles and
copies a milled spell. `.divided` deals that total among one or two
targets. `.attackPump` arms this turn's attack pump. `.none` queues
nothing. -/
inductive QueuedReflexive where
  | modeled (kind times : Nat)
  | counters (kind : Nat)
  | damage (n : Nat)
  | copy
  | divided (amount : Nat)
  | attackPump
  | none
deriving Repr, Inhabited, BEq

/-- Trick Arrows: Net, Explosive, and Boomerang.
Paying up to three times is
`.chooseModes trickArrowModes .alreadyChosen`. -/
def trickArrowModes : List TriggerResolution :=
  [.cant .beBlocked,
   .dealDamage (.fixed 2) (.player .targetOpponent),
   .sequence [.discard, .draw (.fixed 1)]]

/-- Which reflexive `follow` queues. Any other resolution queues nothing. -/
def queuedReflexive : TriggerResolution → QueuedReflexive
  | .grant (.keywords k) .target =>
    if k == Keyword.indestructible then
      .modeled (TriggerReflexiveKind.toNat .grantIndestructible) 1
    else .none
  | .chooseModes modes .alreadyChosen =>
    if modes == trickArrowModes then
      .modeled (TriggerReflexiveKind.toNat .trickArrows) modes.length
    else .none
  | .putCounters (.ofKind .indestructible _) .permanent =>
    .modeled (TriggerReflexiveKind.toNat .indestructibleCounter) 1
  | .gainControl .duringNextTurn =>
    .modeled (TriggerReflexiveKind.toNat .controlOpponent) 1
  | .exile (.opponentTop 5) (.mayCastUpTo 2) _ =>
    .modeled (TriggerReflexiveKind.toNat .exileTopFive) 1
  | .put .creatureCard .tapped (.entering mods) =>
    if mods == [.attacking, .counter .finality] then
      .modeled (TriggerReflexiveKind.toNat .returnAttacking) 1
    else .none
  | .destroy .target .none =>
    .modeled (TriggerReflexiveKind.toNat .destroyOppNonland) 1
  | .cant (.beBlockedExceptByHaste .target) =>
    .modeled (TriggerReflexiveKind.toNat .hasteUnblockable) 1
  | .returnToHand (.graveyardInstants _) .none =>
    .modeled (TriggerReflexiveKind.toNat .returnInstants) 1
  | .putCounters (.ofKind .plusOnePlusOne _) .permanent =>
    .modeled (TriggerReflexiveKind.toNat .plusOne) 1
  | .dealDamage .plusOneCounters .target .none =>
    .counters (TriggerReflexiveKind.toNat .countersDamage)
  | .dealDamage (.fixed n) .target .divided =>
    .divided n.toNat
  | .dealDamage (.fixed n) .target .none =>
    .damage n.toNat
  | .mayCast .milledSpell .causingSpell .withoutPaying _ =>
    .copy
  | .pump .perPlains .perPlains .target =>
    .attackPump
  | _ => .none

/-- Nested `sequence` constructors, left to right. An `or` stays one step:
flattening it would resolve every alternative. -/
def flatten : TriggerResolution → List TriggerResolution
  | .sequence rs => rs.flatMap flatten
  | r => [r]

/-- Add {G}{G}{G}. Put a +1/+1 counter on each creature you control.
Scry 2, then draw a card. -/
def allianceModes : List TriggerResolution :=
  [.addMana #[.colored .green, .colored .green, .colored .green],
   .putCounters (.ofKind .plusOnePlusOne) .youControl,
   .sequence [.scry (.fixed 2), .draw (.fixed 1)]]

/-- Put a +1/+1 counter on the source. Each opponent loses 2 life and you
gain 2 life. Draw a card. -/
def gollumModes : List TriggerResolution :=
  [.putCounters (.ofKind .plusOnePlusOne) .source,
   .sequence [.loseLife (.fixed 2) .eachOpponent, .gainLife (.fixed 2)],
   .draw (.fixed 1)]

/-- Draw a card, then discard a card. Each opponent loses 2 life.
Destroy the announced token. Each player sacrifices the announced creature,
which is already gone when an earlier mode destroyed it. -/
def upToXModes : List TriggerResolution :=
  [.sequence [.draw (.fixed 1), .discard (.cards 1)],
   .loseLife (.fixed 2) .eachOpponent,
   .destroy .target (note := .chosenToken),
   .sacrifice .eachPlayersCreature]

/-- Put a +1/+1 counter on the source. Draw a card after removing a counter
from a creature you control. `.plusOneOrRemoveCounter` asks for the choice
and removes the counter; the draw is that mode's follow-up. -/
def hydeModes : List TriggerResolution :=
  [.putCounters (.ofKind .plusOnePlusOne) .source, .draw (.fixed 1)]

/-- The Vision gains double strike until end of turn. The Vision gains
indestructible until end of turn. Draw a card. `.vision` asks for one that
has not been chosen this turn. -/
def visionModes : List TriggerResolution :=
  [.grant (.keywords Keyword.doubleStrike) .source,
   .grant (.keywords Keyword.indestructible) .source,
   .draw (.fixed 1)]

/-- What `action` does to the announced permanent. -/
def ofPermanent : PermanentAction → TriggerResolution
  | .plusOne n => .putCounters (.ofKind .plusOnePlusOne n) .permanent
  | .pump p t => .pump (.fixed p) (.fixed t) .target
  | .pumpAndTrample p t =>
    .sequence [.pump (.fixed p) (.fixed t) .target, .grant (.keywords Keyword.trample) .target]
  | .destroy => .destroy .target
  | .dealDamage n => .dealDamage (.fixed n) .target
  | .grantKeywords k => .grant (.keywords k) .target
  | .tap => .tap .target
  | .untap => .untap
  | .loseIndestructible => .lose .indestructible
  | .cantBeBlocked => .cant .beBlocked
  | .indestructibleCounter => .putCounters (.ofKind .indestructible) .permanent
  | .doubleStrikeCounter => .putCounters (.ofKind .doubleStrike) .permanent
  | .burdenCounter => .putCounters (.ofKind .burden) .permanent
  | .becomeArtifactIndestructible =>
    .sequence [.becomeArtifact, .grant (.keywords Keyword.indestructible) .target]
  | .becomePrepared => .becomePrepared
  | .setBasePT p t => .setBasePT (.fixed p) (.fixed t)
  | .tapAndStun =>
    .sequence [.tap .target, .putCounters (.ofKind .stun) .permanent]
  | .putOnTopOfLibrary => .putOnLibrary .top
  | .putOnBottomOfLibrary => .putOnLibrary .bottom
  | .exile => .exile .target .forLater
  | .doublePowerAndToughness => .pump .double .double .target

/-- What `action` does to `who`. `target` is the announced permanent. -/
def ofAffected (who : TriggerAffected) : PermanentAction → TriggerResolution
  | .plusOne n => .putCounters (.ofKind .plusOnePlusOne n) (counterWho who)
  | .pump p t => .pump (.fixed p) (.fixed t) (affectedWho who)
  | .pumpAndTrample p t =>
    .sequence [.pump (.fixed p) (.fixed t) (affectedWho who), .grant (.keywords Keyword.trample) (affectedWho who)]
  | .destroy => .destroy (affectedWho who)
  | .dealDamage n => .dealDamage (.fixed n) (affectedWho who)
  | .grantKeywords k => .grant (.keywords k) (affectedWho who)
  | .tap => .tap (tapWho who)
  | .untap => .untap (affectedWho who)
  | .loseIndestructible => .lose .indestructible (loseWho who)
  | .cantBeBlocked => .cant (.beBlocked who)
  | .indestructibleCounter => .putCounters (.ofKind .indestructible) (counterWho who)
  | .doubleStrikeCounter => .putCounters (.ofKind .doubleStrike) (counterWho who)
  | .burdenCounter => .putCounters (.ofKind .burden) (counterWho who)
  | .becomeArtifactIndestructible =>
    .sequence [.becomeArtifact (affectedWho who), .grant (.keywords Keyword.indestructible) (affectedWho who)]
  | .becomePrepared => .becomePrepared (affectedWho who)
  | .setBasePT p t => .setBasePT (.fixed p) (.fixed t) (affectedWho who)
  | .tapAndStun =>
    .sequence [.tap (tapWho who), .putCounters (.ofKind .stun) (counterWho who)]
  | .putOnTopOfLibrary => .putOnLibrary .top (affectedWho who)
  | .putOnBottomOfLibrary => .putOnLibrary .bottom (affectedWho who)
  | .exile => .exile (affectedWho who) .forLater
  | .doublePowerAndToughness => .pump .double .double (affectedWho who)
where
  counterWho : TriggerAffected → ObjectSelector
    | .target => .permanent
    | .source => .source
    | .enchanted => .enchanted
    | .targetWhileSource => .targetWhileSource
  affectedWho : TriggerAffected → ObjectSelector
    | .target => .target
    | .source => .source
    | .enchanted => .enchanted
    | .targetWhileSource => .targetWhileSource
  tapWho : TriggerAffected → ObjectSelector
    | .target => .target
    | .source => .source
    | .enchanted => .enchantedWhileSource
    | .targetWhileSource => .targetWhileSource
  loseWho : TriggerAffected → ObjectSelector
    | .target => .target
    | .source => .source
    | .enchanted => .enchanted
    | .targetWhileSource => .targetWhileSource

/-- What `action` does to the source if it is still on the battlefield. -/
def ofSource : PermanentAction → TriggerResolution :=
  ofAffected .source

/-- What `action` does to the creature this Aura enchants. -/
def ofEnchanted : PermanentAction → TriggerResolution :=
  ofAffected .enchanted

/-- What `action` does to the target while the source is still on the battlefield.
A source that already left is silent. -/
def ofTargetWhileSource : PermanentAction → TriggerResolution :=
  ofAffected .targetWhileSource

/-- A spell step as trigger steps. A shape this does not name does nothing. -/
def ofSpell : SpellResolution → TriggerResolution
  | .sequence rs => .sequence (rs.map ofSpell)
  | .scry n => .scry (.fixed n)
  | .draw n .you => .draw (.fixed n)
  | .discard n => .discard (.cards n)
  | .loseLife n .you => .loseLife (.fixed n)
  | .loseLife n .eachOpponent => .loseLife (.fixed n) .eachOpponent
  | .gainLife n .you => .gainLife (.fixed n)
  | .amass n subtype => .amass n subtype
  | .recruit => .recruit
  | .surveil n => .surveil n
  | .onPermanent a => ofPermanent a
  | .creaturesPump p t .youControl => .pump (.fixed p) (.fixed t) .creaturesYouControl
  | .teamGain k => .grant (.keywords k) .creaturesYouControl
  | .createTokens kind n .you .fixed => .createTokens kind n false
  | .createTokens kind _ .you (.perSubtype subtype) =>
    .createTokens kind 0 false (qty := .perSubtype subtype)
  | .plusOneOnEachYouControl n .each =>
    .putCounters (.ofKind .plusOnePlusOne n) .youControl
  | .plusOneOnEachYouControl n .eachOther =>
    .putCounters (.ofKind .plusOnePlusOne n) .eachOther
  | .plusOneOnCreatureN n =>
    .putCounters (.ofKind .plusOnePlusOne n) .permanent
  | .destroyUpToOneNonland => .destroy .target
  | .mutualFight .upToOne => .fight .announced .upToOneOther
  | .mutualFight .both => .fight .announced .mutual
  | .createGalactus => .createTokens .treasure 1 false .galactus
  | .nextFreeRGCreature =>
    .mayCast .nextRedOrGreenCreature .unlimited .withoutPaying
  | .mayDrawPerArtifactOppsDraw ty =>
    .may (.draw (.perControlled ty)) (.draw (.fixed 1) (who := .eachOpponent)) .ifYouDo
  | .mayPutHeroMvOrDraw n subtype =>
    .may (.put (.creatureFromHand subtype n)) (.draw (.fixed 1))
  | .spellsCostLessThisTurn which n => .spellsCostLess which n
  | _ => .sequence []

end TriggerResolution

/-- When a triggered ability fires, how it targets, optional divided-damage
parameters, and how it resolves (CR 603 / 601.2d / 608). Adding a constructor
only requires updating `timing` instead of parallel match trees. -/
structure TriggerTiming where
  events : Array TriggerEvent := #[]
  targeting : EffectTargeting := .of .none
  /-- Zero targets is a legal announcement (CR 115.1c / 601.2c), e.g. “up to one”. -/
  allowsZeroTargets : Bool := false
  /-- Most targets one instance of “target” may take (“any number of target
  …”); 0 means the targeting's own count. -/
  maxTargets : Nat := 0
  /-- Damage amount and maximum number of targets when this ability divides
  damage as the controller chooses (CR 601.2d). -/
  dividedDamage : Option (Nat × Nat) := none
  /-- What happens when this ability resolves. -/
  resolution : TriggerResolution := .pump .greatestPower (.fixed 0) .source
  /-- Intervening “while you control a creature with power ≥ n” (e.g. Ferocious).
  Checked when the trigger event occurs (CR 603.2 / 603.4); not rechecked on
  resolution. -/
  youControlCreatureWithPower : Option Int := none
  /-- This trigger fires only once each turn. -/
  onceEachTurn : Bool := false
  /-- “Do this only once each turn”: the ability keeps triggering until the
  controller chooses to do the optional action (MSH 69). -/
  optionalOnceEachTurn : Bool := false
  /-- Intervening “another creature you control with power ≤ n”. -/
  anotherCreaturePowerAtMost : Option Int := none
  /-- “This or another nontoken {subtype} you control enters”. -/
  thisOrNontokenSubtype : Option String := none
  /-- Intervening “if you gained `n` or more life this turn”. -/
  gainedLifeAtLeast : Option Nat := none
  /-- “Another {subtype} or Equipment you control enters”. -/
  anotherSubtypeOrEquipment : Option String := none
  /-- “This or another {subtype} you control enters”. -/
  thisOrAnotherSubtype : Option String := none
deriving Repr, Inhabited, BEq

/-- Targeting and resolution for a printed Saga chapter (CR 714.3).
The chapter is still stored as `ChapterResolution`. What resolves is one
of these `TriggerResolution` constructors. -/
def chapterTiming (e : ChapterResolution) : TriggerTiming :=
  match e with
  | .dealDamageToOppCreature n =>
    { targeting := .of .oppCreature, resolution := .dealDamage (.fixed n) .target }
  | .destroyOppArtifact =>
    { targeting := .of .oppArtifact, resolution := .destroy .target }
  | .addMana mana =>
    { resolution := .addMana #[mana] }
  | .searchBasicLandToHand =>
    { resolution := .searchLibrary (.returnToHand .basicLand) }
  | .gainLandfallCreateElf =>
    { resolution := .grant .landfallCreateElf .source }
  | .elvesGetVigilance p =>
    { resolution := .sequence [
        .pump (.fixed p) (.fixed 0) (.youControlSubtype "Elf"),
        .grant (.keywords Keyword.vigilance) (.youControlSubtype "Elf")] }
  | .opponentDiscardsNonland =>
    { targeting := .of .opponent
      resolution := .discard .chosenNonland }
  | .amass n =>
    { resolution := .amass n }
  | .opponentLosesYouGain n =>
    { targeting := .of .opponent
      resolution := .sequence [.loseLife (.fixed n) .targetOpponent, .gainLife (.fixed n)] }
  | .grantHexproofWhileRemains =>
    { targeting := .of .creatureYouControl
      resolution := .grant .hexproofWhileSource .target }
  | .preventDamageWhileRemains =>
    { targeting := .of .creature, allowsZeroTargets := true
      resolution := .grant .preventDamageWhileSource .target }
  | .draw n =>
    { resolution := .draw (.fixed n) }
  | .searchBasicPlainsExileGainLife max life =>
    { resolution := .sequence [
        .searchLibrary (.exile (.basicUpTo "Plains" max) .forLater .linked),
        .gainLife (.fixed life)] }
  | .returnLinkedExileToHand =>
    { resolution := .returnToHand .linkedExile }
  | .grantAttackPumpPerPlainsThisTurn =>
    { resolution := .queueReflexive (.pump .perPlains .perPlains .target) }
  | .blinkUntilEndStep =>
    { targeting := .of .creatureOrLandYouControl, allowsZeroTargets := true
      resolution := .exile .target .nextEndStep }
  | .treasureThenDragonIfFour =>
    { resolution := .sequence [
        .createTokens .treasure 1 false,
        .«if» (.controlsAtLeast "Treasure" 4)
          (.sacrifice (.sacrificedSource .isSacrificed) .noted),
        .«if» .sourceWasSacrificed (.createTokens .dragon 1 false)] }
  | .recruit =>
    { resolution := .recruit }
  | .returnCreatureFromGyMvAtMost n =>
    { targeting := .of (.creatureCardInYourGraveyardMvAtMost n)
      resolution := .put (.creatureMvAtMost n) }
  | .plusOneUpToOne =>
    { targeting := .of .creature, allowsZeroTargets := true
      resolution := .putCounters (.ofKind .plusOnePlusOne) .permanent }
  | .gainControlOfUpToTwoCreaturesTotalMvAtMost n =>
    { targeting := .of (.upToTwoCreaturesTotalMvAtMost n), allowsZeroTargets := true
      resolution := .gainControl .whileSourceRemains }
  | .dealDamageToEachNonSubtypeAndOpponents n subtype =>
    { resolution := .dealDamage (.fixed n) (.eachNonSubtypeAndOpponents subtype) }
  | .dealXDamageToTargetOpponentGreatestArtifactMv =>
    { targeting := .of .opponent
      resolution := .dealDamage .greatestArtifactMv (.player .targetOpponent) }
  | .spell s =>
    { targeting := s.targeting, allowsZeroTargets := s.allowsZeroTargets
      resolution := TriggerResolution.ofSpell s.resolution }

end TriggeredAbility

namespace SharedTriggerWhen

/-- Whenever this creature enters or attacks. -/
def enterOrAttack : SharedTriggerWhen := .or .enter .attack

/-- Whenever you cast a green spell and whenever a Forest you control enters. -/
def castGreenOrForestEnters : SharedTriggerWhen :=
  .or .youCastGreen .forestYouControlEnters

/-- When this enters and whenever an opponent draws except their first draw-step card. -/
def enterOrOpponentDrawsExceptFirst : SharedTriggerWhen :=
  .or .enter .opponentDrawsExceptFirst

/-- Events this reusable trigger watches. -/
def events : SharedTriggerWhen → Array TriggerEvent
  | .enter => #[.entering]
  | .attack => #[.attacking]
  | .dies => #[.dying]
  | .youAttack => #[.youAttack]
  | .youAttackWithElves => #[.youAttackWithElves]
  | .youCastColor c => #[.youCastColor c]
  | .youCastNoncreature => #[.youCastNoncreature]
  | .landYouControlEnters => #[.landYouControlEnters]
  | .yourUpkeep => #[.yourUpkeep]
  | .yourEndStep => #[.yourEndStep]
  | .yourBeginCombat => #[.yourBeginCombat]
  | .youDrawSecond => #[.youDrawSecondCard]
  | .theRingTemptsYou => #[.theRingTemptsYou]
  | .youChooseRingBearer => #[.youChooseRingBearer]
  | .becomesTarget => #[.becomesTarget]
  | .artifactYouControlEnters => #[.artifactYouControlEnters]
  | .combatDamageToPlayer => #[.dealsCombatDamageToPlayer]
  | .oneOrMoreOtherCreaturesDie => #[.oneOrMoreOtherCreaturesDie]
  | .creatureCardLeavesYourGy => #[.creatureCardLeavesYourGy]
  | .youDraw => #[.youDraw]
  | .youGainLife => #[.youGainLife]
  | .anotherArtifactEnters => #[.anotherArtifactEnters]
  | .sourceDealtDamage => #[.sourceDealtDamage]
  | .equippedAttacksAlone => #[.equippedAttacksAlone]
  | .youCastWithTreasure => #[.youCastWithTreasure]
  | .youCastColorFromHand c => #[.youCastColorFromHand c]
  | .equippedCreatureYouControlAttacks => #[.equippedCreatureYouControlAttacks]
  | .anotherElfYouControlEnters => #[.anotherElfYouControlEnters]
  | .youActivateCreatureAbility => #[.youActivateCreatureAbility]
  | .opponentDrawsSecond => #[.opponentDrawsSecondCard]
  | .opponentCastsFirstNoncreature => #[.opponentCastsFirstNoncreature]
  | .youCastFirstNoncreature => #[.youCastFirstNoncreature]
  | .youCastSpell => #[.youCastSpell]
  | .youCastTargetingOpponentOrTheirCreature => #[.youCastTargetingOpponentOrTheirCreature]
  | .youActivateLoyaltyAbility => #[.youActivateLoyaltyAbility]
  | .eachUpkeep => #[.eachUpkeep]
  | .youScryOrSurveil => #[.youScryOrSurveil]
  | .opponentsDealtCombatDamageYourTurn => #[.opponentsDealtCombatDamageYourTurn]
  | .creatureYouControlDies => #[.creatureYouControlDies]
  | .eachOpponentDrawStep => #[.eachOpponentDrawStep]
  | .eachEndStep => #[.eachEndStep]
  | .thisOrNontokenSubtypeEnters => #[.thisOrNontokenSubtypeYouControlEnters]
  | .thisOrAnotherSubtypeEnters => #[.thisOrAnotherSubtypeYouControlEnters]
  | .anotherSubtypeOrEquipmentEnters => #[.anotherSubtypeOrEquipmentYouControlEnters]
  | .combatDamageToPlayerOrBattle => #[.dealsCombatDamageToPlayerOrBattle]
  | .youCastGreen => #[.youCastGreen]
  | .forestYouControlEnters => #[.forestYouControlEnters]
  | .youCastInstantOrSorcery => #[.youCastInstantOrSorcery]
  | .equipmentYouControlEnters => #[.equipmentYouControlEnters]
  | .anotherCreatureYouControlEnters => #[.anotherCreatureYouControlEnters]
  | .anotherGoblinOrcArmyDies => #[.anotherGoblinOrcArmyDies]
  | .creatureYouControlAttacksAlone => #[.creatureYouControlAttacksAlone]
  | .opponentCastsSpell => #[.opponentCastsSpell]
  | .youScry => #[.youScry]
  | .becomesBlocked => #[.becomesBlocked]
  | .leaving => #[.leaving]
  | .youAttackWithTwoOrMore => #[.youAttackWithTwoOrMore]
  | .youSacrificeToken => #[.youSacrificeToken]
  | .armyYouControlCombatDamage => #[.armyYouControlCombatDamage]
  | .yourFirstMain => #[.yourFirstMain]
  | .anyPlayerCastsSecondSpell => #[.anyPlayerCastsSecondSpell]
  | .eachBeginCombat => #[.eachBeginCombat]
  | .youCastCreature => #[.youCastCreature]
  | .mountainYouControlEnters => #[.mountainYouControlEnters]
  | .equippedDealsCombatDamageToPlayer => #[.equippedDealsCombatDamageToPlayer]
  | .nontokenYouControlDies => #[.nontokenYouControlDies]
  | .playerLosesLife => #[.playerLosesLife]
  | .youCastSecondSpell => #[.youCastSecondSpell]
  | .equippedAttacks => #[.equippedAttacks]
  | .cascade => #[]
  | .tokenYouControlEnters => #[.tokenYouControlEnters]
  | .bolgSacrificedForReflexive => #[.bolgSacrificedForReflexive]
  | .opponentDrawsExceptFirst => #[.opponentDrawsExceptFirstDrawStep]
  | .youAttackWithTotalPower => #[.youAttackWithTotalPower]
  | .eaglesCreateBirds => #[.eaglesCreateBirds]
  | .opponentCastsMatchingParity => #[.opponentCastsMatchingParity]
  | .youPutCountersOnGoblinOrcArmy => #[.youPutCountersOnGoblinOrcArmy]
  | .sourceDealtNoncombatDamage => #[.sourceDealtNoncombatDamage]
  | .finalSagaChapterResolves => #[.finalSagaChapterResolves]
  | .combatDamageToYou => #[.combatDamageToYou]
  | .sagaChapter => #[.sagaChapter]
  | .tappedForTeamwork => #[.tappedForTeamwork]
  | .creatureYouControlEnters => #[.creatureYouControlEnters]
  | .creaturesYouControlBecomeTapped => #[.creaturesYouControlBecomeTapped]
  | .subtypeYouControlEnters subtype => #[.subtypeYouControlEnters subtype]
  | .creatureCardsPutIntoYourGy => #[.creatureCardsPutIntoYourGy]
  | .nthPlanCounter n => #[.nthPlanCounter n]
  | .or a b => a.events ++ b.events
  | .fromEffect => #[]
  | .fra e => #[.fra e]

end SharedTriggerWhen

namespace SharedTrigger

/-- Targeting, divided-damage parameters, and resolution for this shared effect. -/
def timing : SharedTrigger → TriggeredAbility.TriggerTiming
  | .scry n => { resolution := .scry (.fixed n) }
  | .draw n => { resolution := .draw (.fixed n) }
  | .createTokens kind n tapped => { resolution := .createTokens kind n tapped }
  | .amass n subtype amount attachSource =>
    { resolution := .amass n subtype amount attachSource }
  | .recruit who => { resolution := .recruit who }
  | .dividedDamage amount maxTargets =>
    { targeting := .of .playerOrCreature,
      dividedDamage := some (amount, maxTargets), resolution := .dividedDamage }
  | .gainLife n => { resolution := .gainLife (.fixed n) }
  | .connive who =>
    match who with
    | .source => { resolution := .connive who }
    | .target kind => { targeting := .of kind, resolution := .connive who }
    | .enteringVillain => { resolution := .connive who }
  | .exileUntilLeaves kind =>
    { targeting := .of kind, resolution := .exile .target .untilSourceLeaves }
  | .damageEachOpponent n =>
    { targeting := .of .opponent, resolution := .dealDamage (.fixed n) (.player .eachOpponent) }
  | .attachTo kind =>
    { targeting := .of kind, resolution := .attach .source .target }
  | .opponentSacrificesCreature =>
    { targeting := .of .opponent,
      resolution := .sacrifice .opponentChosenCreature }
  | .onPermanent kind action =>
    { targeting := .of kind
      resolution := TriggeredAbility.TriggerResolution.ofPermanent action }
  | .onSource action =>
    { resolution := TriggeredAbility.TriggerResolution.ofSource action }
  | .exileTop => { resolution := .exile .top .playUntilNextTurn }
  | .discard n => { resolution := .discard (.cards n) }
  | .mayTo can thenDo =>
    let left := timing can
    let right := timing thenDo
    { targeting :=
        if left.targeting.kind == .none then right.targeting else left.targeting
      allowsZeroTargets := left.allowsZeroTargets || right.allowsZeroTargets
      maxTargets :=
        if left.targeting.kind == .none then right.maxTargets else left.maxTargets
      dividedDamage :=
        match left.dividedDamage with
        | some d => some d
        | none => right.dividedDamage
      resolution := .may left.resolution right.resolution .ifYouDo }
  | .may action =>
    let inner := timing action
    { inner with resolution := .may inner.resolution (.sequence []) }
  | .opponentDiscards n who =>
    match who with
    | .each => { resolution := .discard (.cards n .eachOpponent) }
    | .target =>
      { targeting := .of .opponent, resolution := .discard (.cards n .targetOpponent) }
  | .millPlayer n =>
    { targeting := .of .player, resolution := .mill n .target }
  | .investigate => { resolution := .investigate }
  | .pumpCause p t => { resolution := .pump (.fixed p) (.fixed t) .cause }
  | .searchLibrary => { resolution := .searchLibrary (.put .forest) }
  | .searchBasicLandToHand =>
    { resolution := .searchLibrary (.returnToHand .basicLand) }
  | .eachPlayerSacrificesCreature =>
    { resolution := .sacrifice .eachPlayersCreature }
  | .exileTarget kind =>
    { targeting := .of kind, resolution := .exile .target .leaveTrigger }
  | .returnCreatureFromGyToHand =>
    { targeting := .of .creatureCardInYourGraveyard,
      resolution := .returnToHand .graveyardCard }
  | .plusOneEachYouControl which =>
    { resolution := .putCounters (.ofKind .plusOnePlusOne) (.youControl which) }
  | .honeEachEquipment => { resolution := .honeEachEquipment }
  | .plusOneEachOtherGainLife =>
    { resolution := .sequence
        [.putCounters (.ofKind .plusOnePlusOne) .eachOther,
         .gainLife .perOtherCreature] }
  | .becomePT p t => { resolution := .becomePT p t }
  | .pumpTargetPerPlains =>
    { targeting := .of .creatureYouControl, resolution := .pump .perPlains .perPlains .target }
  | .mayDiscardHandDraw n =>
    { resolution := .may (.discard .hand) (.draw (.fixed n)) .ifYouDo }
  | .pumpByLookedAt => { resolution := .pump .perLookedAt .perLookedAt .source }
  | .pumpGreatestPower => { resolution := .pump .greatestPower (.fixed 0) .source }
  | .pumpForEachOtherCreature =>
    { resolution := .pump .perOtherCreature .perOtherCreature .source }
  | .damageBlockers n => { resolution := .dealDamage (.fixed n) .blockers }
  | .returnLinkedExile => { resolution := .put .linkedExile }
  | .createThenAttach kind =>
    { resolution := .sequence [.createTokens kind 1 false, .attach .source .created] }
  | .gainLifeSearchBasicOnTop n =>
    { resolution := .sequence [.gainLife (.fixed n), .searchLibrary (.put .basicLandOnTop)] }
  | .addMana types => { resolution := .addMana types }
  | .createAxe attach =>
    { resolution :=
        .createTokens .treasure 1 false .axe
          (note := if attach then .attachReflexive else .none) }
  | .tapOppOrUntapYours =>
    { resolution := .or [.tap .target, .untap] }
  | .gainControlOppUntilEot =>
    { targeting := .of .oppCreature, resolution := .gainControl .untilEndOfTurn }
  | .payReturnFromGy =>
    { resolution := .may
        (.pay (.mana #[.generic 1, .colored .green, .colored .blue])) (.returnToHand .source) .ifYouDo }
  | .targetOpponentLosesLife n =>
    { targeting := .of .opponent, resolution := .loseLife (.fixed n) .targetOpponent }
  | .drawXDiscard n =>
    { resolution := .sequence
        [.draw .equalToManaSpent, .«if» .manaSpent (.discard (.cards n))] }
  | .ringTempts => { resolution := .ringTempts }
  | .setOtherBasePT =>
    { targeting := .of .anotherCreatureYouControl, allowsZeroTargets := true,
      resolution := .setBasePT .equalSourcePower .equalSourceToughness }
  | .returnElfGainLife =>
    { targeting := .of .elfInYourGraveyard
      resolution := .sequence
        [.returnToHand .graveyardCard, .gainLife .equalToTargetPower] }
  | .damageFromLastKnownPower =>
    { targeting := .of .oppCreature,
      resolution := .dealDamage .lastKnownPower .permanent }
  | .mayPayGenericDraw n plusOne =>
    { resolution :=
        if plusOne then
          .may (.pay (.mana #[.generic n]))
            (.sequence [.putCounters (.ofKind .plusOnePlusOne) .source, .draw (.fixed 1)]) .ifYouDo
        else
          .may (.pay (.mana #[.generic n])) (.draw (.fixed 1)) .ifYouDo }
  | .drawThenBottomIfNoLegendary =>
    { resolution := .sequence
        [.draw (.fixed 1), .«if» .noLegendaryCreature (.putOnLibrary .bottom .cardFromHand)] }
  | .removeHopeDrawSac =>
    { resolution := .sequence
        [.removeCounters .hope .source, .«if» .removedHope (.draw (.fixed 1)), .«if» .noHopeOnSource (.sequence [.sacrifice .source, .gainLife (.fixed 4)])] }
  | .tapHumansDraw =>
    { resolution := .sequence
        [.may (.tap .humans) (.sequence []), .draw .forEachTappedHuman] }
  | .destroyOppArtifactsEnchantmentsGainLife =>
    { resolution := .sequence
        [.destroy .oppArtifactsEnchantments (note := .countDestroyed),
         .gainLife .forEachDestroyedThisWay] }
  | .damageEqualSubtypeToEachOpponent subtype =>
    { resolution := .dealDamage (.subtypeCount subtype) (.player .eachOpponent) }
  | .damageEqualTreasures =>
    { targeting := .of .playerOrCreature,
      resolution := .dealDamage (.subtypeCount "Treasure") .target }
  | .dealDamageDestroyIfSubtype n subtype =>
    { targeting := .of .playerOrCreature,
      resolution := .sequence
        [.dealDamage (.fixed n) .target .markedPermanent,
         .«if» (.dealtDamageToSubtype subtype) (.destroy .permanentDealtDamage)] }
  | .attachEquipmentToCreature =>
    { targeting := .of .equipmentYouControlThenCreatureYouControl,
      allowsZeroTargets := true, resolution := .attach .target .optionalCreature }
  | .defenderSacsLeastPower =>
    { resolution := .sacrifice .leastPower }
  | .returnOtherPlusOne =>
    { targeting := .of (.filtered { noun := "up to one other target permanent you control"
                                    controller := .you, another := true })
      allowsZeroTargets := true
      resolution := .sequence
        [.returnToHand .permanent .returnedPermanent,
         .«if» .returnedPermanent (.putCounters (.ofKind .plusOnePlusOne) .source)] }
  | .lookAtTopRevealTypes n types =>
    { resolution := .lookAtTopRevealTypes n types }
  | .createTappedTreasuresEqualOppArtifacts =>
    { resolution := .createTokens .treasure 0 true (qty := .oppArtifacts) }
  | .putNonlandMvAtMostFromGy mv =>
    { targeting := .of (.filtered
        { noun := s!"up to one target nonland permanent card with mana value {mv} or less from a graveyard"
          zone := .anyGraveyard, permanentCard := true, nonland := true, mvAtMost := some mv })
      allowsZeroTargets := true, resolution := .put (.nonlandMvAtMost mv) }
  | .othersGetAndOppsGet subtypes p t oppP oppT =>
    { resolution := .sequence
        [.pump (.fixed p) (.fixed t) (.othersOfSubtypes subtypes),
         .pump (.fixed oppP) (.fixed oppT) .opponentsCreatures] }
  | .wolfPlusOneOrTreasure =>
    { resolution := .or
        [.putCounters (.ofKind .plusOnePlusOne) .permanent,
         .createTokens .treasure 1 false] }
  | .trampleCounterBecomeBear =>
    { targeting := .of .creatureYouControl, allowsZeroTargets := true,
      resolution := .sequence
        [.putCounters (.ofKind .trample) .permanent, .becomeBear, .«if» (.bearsAtLeast 3) (.draw (.fixed 2))] }
  | .millThenSubtypeToHand n subtype =>
    { resolution := .sequence
        [.mill n (note := .milledCards), .returnToHand (.milledSubtype subtype)] }
  | .exileOppNonlandEachUntilLeaves =>
    { targeting := .of (.filtered
        { noun := "for each opponent, up to one target nonland permanent that player controls"
          nonland := true, controller := .eachOpponent })
      allowsZeroTargets := true
      resolution := .exile .eachTarget .untilSourceLeaves }
  | .plusOneEqualLastKnownMv =>
    { targeting := .of .creatureYouControl,
      resolution := .putCounters .plusOneLastKnownMv .permanent }
  | .mountainQuestDragon =>
    { resolution := .sequence [.putCounters (.ofKind .quest) .source, .«if» (.questAtLeast 6) (.sequence [.sacrifice (.sacrificedSource .movedAsSacrificed), .searchLibrary (.put .dragon)])] }
  | .treasuresPerChosenType =>
    { resolution := .createTokens .treasure 0 false (qty := .chosenCreatureType) }
  | .revealUntilCreature =>
    { resolution := .revealLibrary .untilCreature
        (.ifElse .revealedManaValueAtMostLands (.put .revealed) (.returnToHand .revealed)) }
  | .attackSacPlusOneEqualPower =>
    { resolution := .may (.pay .anotherCreature)
        (.putCounters .plusOneSacrificedPower .source) .ifYouDo }
  | .lootLandEntersTapped =>
    { resolution := .sequence
        [.draw (.fixed 1), .discard (.cards 1), .put .discardedLand (how := .tapped)] }
  | .millThatManyLost =>
    { resolution := .mill 0 .thatPlayer .thatManyLost }
  | .drawPerFatGraveyard =>
    { resolution := .draw .perFatGraveyard }
  | .maySacDrawTreasure =>
    { resolution := .may (.pay .anotherCreatureOrArtifact)
        (.sequence [.draw (.fixed 1), .createTokens .treasure 1 false]) .ifYouDo }
  | .castInstantSorceryFromHand =>
    { resolution := .mayCast .hand .twiceLegendaryWizards .withoutPaying }
  | .castInstantSorceryMvAtMost =>
    { resolution := .mayCast .hand .lastKnown .withoutPaying }
  | .millThenCopy =>
    { resolution := .sequence
        [.mill 2 .eachOpponent (note := .opponentsMilled),
         .«if» .opponentsMilled (.queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying))] }
  | .pumpTargetBySourcePower =>
    { targeting := .of .anotherCreatureYouControl,
      resolution := .pump .equalSourcePower (.fixed 0) .target }
  | .createAlienPerInvasion =>
    { resolution := .sequence
        [.createTokens .treasure 1 false .alien (note := .invasion),
         .putCounters .plusOneNoted .createdToken,
         .putCounters (.ofKind .invasion) .source] }
  | .mayPutArtifactAttachEquipment =>
    { resolution := .sequence
        [.may (.put .artifactFromHand (note := .forAttach)) (.sequence []),
         .«if» .putArtifactIsEquipment (.attach .putArtifact .notedHost)] }
  | .cascade => { resolution := .cascade }
  | .belladonnaTokenReward =>
    { resolution := .sequence [
        .noteResolveThisTurn 3,
        .«if» (.nthResolve 1) (.gainLife (.fixed 1)),
        .«if» (.nthResolve 2) (.draw (.fixed 1)),
        .«if» (.nthResolve 3) (.putCounters (.ofKind .plusOnePlusOne) .youControl)] }
  | .bolgMaySacrifice => { resolution := .may (.sacrifice .another) (.sequence []) }
  | .bolgDealSacrificedPower =>
    { targeting := .of .anotherCreature,
      resolution := .sequence
        [.dealDamage .lastKnownPower .permanent .excess,
         .amass 0 (amount := .notedExcess)] }
  | .createSpiritsForEquipped =>
    { resolution := .sequence
        [.createTokens .spirit 2 true, .«if» .equippedLegendaryYouControl .markRecentTokensAttacking] }
  | .createTreasuresEqualDamagedPlayerArtifacts =>
    { resolution :=
        .createTokens .treasure 0 false (qty := .damagedPlayerArtifacts) }
  | .deal1ThenAmassOrcs =>
    { targeting := .of .playerOrCreature,
      resolution := .sequence
        [.dealDamage (.fixed 1) .target .markedPermanent, .amass 1 "Orc"] }
  | .untapAttackersExtraCombat _n =>
    { resolution := .sequence [.untap .attackingCreatures, .additionalCombatPhase] }
  | .eaglesCreateBirds =>
    { resolution := .createTokens .birdSoldier 0 false (qty := .lastKnown) }
  | .allianceMode =>
    { resolution := .chooseModes TriggeredAbility.TriggerResolution.allianceModes
        .oneUnusedThisTurn }
  | .destroyOtherAmassControllerPower =>
    { targeting := .of .anotherCreature, allowsZeroTargets := true,
      resolution := .sequence
        [.destroy .target (note := .forAmass),
         .amass 0 (amount := .notedPower) (who := .notedController),
         .«if» .youControlledDestroyed (.draw (.fixed 1))] }
  | .gollumMode =>
    { resolution := .chooseModes TriggeredAbility.TriggerResolution.gollumModes
        .oneUnused }
  | .discardHandDrawDamageIfStory =>
    { resolution := .sequence
        [.may (.discard .hand) (.sequence []), .draw .discardedHand,
         .«if» .enduringStoryNoted (.dealDamage .discardedHand (.player .eachOpponent))] }
  | .castFromGyArtifactInstantSorcery =>
    { resolution := .mayCast .graveyard .unlimited .pay .exileInstead }
  | .equippedAttackersGainDoubleStrike =>
    { resolution := .grant .doubleStrike .equippedAttackers }
  | .tapEnchantedRemoveCounters =>
    { resolution := .sequence [.tap .enchanted, .removeCounters .all .enchanted] }
  | .revealTopPutRandomCreature n =>
    { resolution := .revealLibrary (.top n) (.put .randomCreature) }
  | .beginCombatIfDrawnTwoPump =>
    { targeting := .of .anotherCreatureYouControl,
      resolution := .«if» (.drewAtLeast 2) (.sequence [
        .pump (.fixed 3) (.fixed 0) .target,
        .grant (.keywords Keyword.firstStrike) .target]) }
  | .honePerOppAttach =>
    { targeting := .of (.multi #[
        { noun := "target opponent", zone := .player, controller := .opponent },
        { noun := "target creature you control", controller := .you, types := #[.creature] }
      ] #[1])
      resolution := .sequence
        [.putCounters .honePerOpponent .source, .attach .source .creatureTarget] }
  | .damageTargetOpponent n =>
    { targeting := .of .opponent, resolution := .dealDamage (.fixed n) (.player .targetOpponent) }
  | .copySelfNonlegendary => { resolution := .copySelfNonlegendary }
  | .attachEquipmentThenFight =>
    { targeting := .of .creatureYouControl,
      resolution := .sequence [.attach .anyYouControl .target,
        .«if» .equipmentAttached (.fight .equipmentHost .reflexive)] }
  | .returnAsArtifact => { resolution := .put .source (how := .asArtifact) }
  | .exileLandsThenReturnTapped =>
    { targeting := .of (.filtered {
        noun := "up to three target lands you control"
        types := #[.land], controller := .you })
      allowsZeroTargets := true, maxTargets := 3
      resolution := .sequence
        [.exile .landsYouControl .forLater .lands,
         .put .notedLands (how := .tapped)] }
  | .grimaImpulse =>
    { resolution := .sequence
        [.revealLibrary .untilInstantOrSorcery (.exile .top .forLater .impulse) .damagedPlayer,
         .mayCast .impulse .unlimited .withoutPaying] }
  | .palantir =>
    { targeting := .of .opponent,
      resolution := .sequence
        [.putCounters (.ofKind .influence) .source, .scry (.fixed 2),
         .may (.draw (.fixed 1) (who := .opponentHasYou)) (.sequence [])] }
  | .treasuresEqualLastKnown =>
    { resolution := .createTokens .treasure 0 false (qty := .lastKnown) }
  | .protectionEverything =>
    { resolution := .grant .protectionEverything .youIfCast }
  | .loseLifePerBurden => { resolution := .loseLife .perBurden }
  | .revealSaga =>
    { resolution := .revealLibrary .untilSaga (.put .revealed) }
  | .sacDamagersRingTempts =>
    { resolution := .sequence [.sacrifice .combatDamager, .ringTempts] }
  | .chapter _n e =>
    TriggeredAbility.chapterTiming e
  | .drawIfAttackedOrEnteredSubtype subtype =>
    { resolution := .«if» (.attackedOrEntered subtype) (.draw (.fixed 1)) }
  | .othersOfSubtypeGetEqualSourceToughness subtype =>
    { resolution := .pump .equalSourceToughness .equalSourceToughness
        (.othersOfSubtype subtype) }
  | .scryAndPlan n =>
    { resolution := .sequence [.putCounters (.ofKind .plan) .source, .scry (.fixed n)] }
  | .lootAndPlan =>
    { resolution := .sequence
        [.putCounters (.ofKind .plan) .source, .draw (.fixed 1), .discard (.cards 1)] }
  | .createVillainAndPlan =>
    { resolution := .sequence
        [.putCounters (.ofKind .plan) .source, .createTokens .villain21menace 1 false] }
  | .drainAndPlan n =>
    { resolution := .sequence
        [.putCounters (.ofKind .plan) .source, .loseLife (.fixed n) .eachOpponent, .gainLife (.fixed n)] }
  | .drawLoseLifeAndPlan =>
    { resolution := .sequence
        [.putCounters (.ofKind .plan) .source, .draw (.fixed 1), .loseLife (.fixed 1)] }
  | .treasureTappedAndPlan =>
    { resolution := .sequence
        [.putCounters (.ofKind .plan) .source, .createTokens .treasure 1 true] }
  | .plusOneOnTargetAndPlan =>
    { targeting := .of .creatureYouControl,
      resolution := .sequence
        [.putCounters (.ofKind .plan) .source,
         .putCounters (.ofKind .plusOnePlusOne) (.permanent true)] }
  | .planFinishDrawPlusOneEach =>
    { resolution := .sequence
        [.sacrifice .plan, .draw (.fixed 1), .putCounters (.ofKind .plusOnePlusOne) .youControl] }
  | .planFinishReturnInstants =>
    { resolution := .sequence
        [.sacrifice .plan .forReflexive,
         .«if» .planWasSacrificed (.queueReflexive (.returnToHand (.graveyardInstants 2)))] }
  | .planFinishControlOpponent =>
    { resolution := .sequence
        [.sacrifice .plan .forReflexive,
         .«if» .planWasSacrificed (.queueReflexive (.gainControl .duringNextTurn))] }
  | .planFinishExileTopCast =>
    { resolution := .sequence
        [.sacrifice .plan .forReflexive,
         .«if» .planWasSacrificed (.queueReflexive (.exile (.opponentTop 5) (.mayCastUpTo 2)))] }
  | .planFinishCreateRobots n =>
    { resolution := .sequence
        [.sacrifice .plan, .createTokens .robotVillain22 n false] }
  | .planFinishDividedDamage n =>
    { resolution := .sequence
        [.sacrifice .plan .forReflexive,
         .«if» .planWasSacrificed (.queueReflexive (.dealDamage (.fixed n) .target .divided))] }
  | .planFinishIndestructibleOnTarget =>
    { resolution := .sequence
        [.sacrifice .plan .forReflexive,
         .«if» .planWasSacrificed (.queueReflexive (.putCounters (.ofKind .indestructible) .permanent))] }
  | .surveil n => { resolution := .surveil n }
  | .empowerJace n => { resolution := .empowerJace n }
  | .prepareSource .ifNotPrepared =>
    { events := #[.yourUpkeep], resolution := .prepareSource .ifNotPrepared }
  | .prepareSource .ifThreeCreaturesDied =>
    { events := #[.eachEndStep], resolution := .prepareSource .ifThreeCreaturesDied }
  | .drawIfRemovedTwoLoyalty =>
    { resolution := .«if» (.removedLoyaltyAtLeast 2) (.draw (.fixed 1)) }
  | .loyaltyOnSource =>
    { resolution := .putCounters (.ofKind .loyalty) .source }
  | .grantThenCounterByType k =>
    { targeting := .of .permanentYouControl,
      resolution := .sequence
        [.grant (.keywords k) .target,
         .«if» .targetIsCreature (.putCounters (.ofKind .plusOnePlusOne) .permanent),
         .«if» .targetIsPlaneswalker (.putCounters (.ofKind .loyalty) .permanent)] }
  | .destroyOppPermanentIfSixLands =>
    { targeting := .of .oppPermanent,
      resolution := .«if» (.landsAtLeast 6) (.sequence [
        .destroy .target,
        .createTokens .treasure 1 false (who := .targetController)]) }
  | .pumpOrCounterIfScried =>
    { events := #[.yourBeginCombat], targeting := .of .anotherCreatureYouControl,
      resolution := .ifElse .scriedOrSurveilledThisTurn
        (.putCounters (.ofKind .plusOnePlusOne) .permanent)
        (.pump (.fixed 1) (.fixed 1) .target) }
  | .sacrificeSourceIfNoPlaneswalker =>
    { events := #[.eachEndStep],
      resolution := .«if» .noPlaneswalker (.sacrifice (.sacrificedSource .controllerSacrifices)) }
  | .creaturesYouControlGet p t =>
    { resolution := .pump (.fixed p) (.fixed t) .creaturesYouControl }
  | .putSourceCountersOnTarget =>
    { targeting := .of .creatureYouControl, allowsZeroTargets := true,
      resolution := .putCounters .sourceCounters .permanent }
  | .chargeCounterOnSource =>
    { resolution := .putCounters (.ofKind .charge) .source }
  | .addGreenPerChargeCounter =>
    { events := #[.yourFirstMain],
      resolution := .addMana #[.colored .green] (amount := .perChargeCounter) }
  | .drawTwoWinIfEmptyShuffleSource =>
    { resolution := .sequence
        [.draw (.fixed 2), .«if» .libraryEmpty .winTheGame, .«if» .libraryNotEmpty .shuffleSource] }
  | .surveilReturnIfGainedLife =>
    { events := #[.yourEndStep],
      resolution := .sequence [.armSurveilReturnLifeGained, .surveil 1] }
  | .pumpIfFiveOtherForests =>
    { targeting := .of .creatureYouControl,
      resolution := .«if» (.otherForestsAtLeast 5) (.pump (.fixed 3) (.fixed 3) .target) }
  | .onEnchanted action =>
    { resolution := TriggeredAbility.TriggerResolution.ofEnchanted action }
  | .attachThen followup =>
    { targeting := .of .creatureYouControl,
      resolution := .sequence
        ([.attach .source .target] ++
          (TriggeredAbility.TriggerResolution.ofTargetWhileSource followup).flatten) }
  | .exileOtherCopyEnchanted =>
    { targeting := .of .creature, allowsZeroTargets := true,
      resolution := .sequence
        [.exile .target .untilSourceLeaves .copyAndHost, .becomeCopy .noted] }
  | .exileUntilNextEndStep =>
    { targeting := .of .creatureYouControl, allowsZeroTargets := true,
      resolution := .exile .target .nextEndStep }
  | .tapOrUntapNonland =>
    { targeting := .of .nonland,
      resolution := .or [.tap .target, .untap] }
  | .createFoodOrTreasure =>
    { resolution := .or
        [.createTokens .food 1 false, .createTokens .treasure 1 false] }
  | .villainIfGyElseMill =>
    { resolution := .ifElse (.creatureCardsInGraveyardAtLeast 2)
        (.createTokens .villain21menace 1 true) (.mill 2) }
  | .drawMayPutLandTapped =>
    { resolution := .sequence
        [.draw (.fixed 1), .may (.put .landFromHand (how := .tapped)) (.sequence [])] }
  | .drawGainLifeIfAnotherHero =>
    { resolution := .sequence [.draw (.fixed 1), .«if» .anotherHero (.gainLife (.fixed 2))] }
  | .plusOneOrTwoIfAnotherHero =>
    { targeting := .of .creature,
      resolution := .ifElse (.targetIsAnotherSubtype "Hero")
        (.putCounters (.ofKind .plusOnePlusOne 2) .permanent)
        (.putCounters (.ofKind .plusOnePlusOne) .permanent) }
  | .maySacArtifactOrDiscardDraw =>
    { resolution := .may (.pay .artifactOrDiscard) (.draw (.fixed 1)) .ifYouDo }
  | .enter (.destroy kind) =>
    { events := #[.entering], targeting := .of kind, resolution := .destroy .target }
  | .enter (.dealDamageUpToOne n) =>
    { events := #[.entering], targeting := .of .creature, allowsZeroTargets := true,
      resolution := .dealDamage (.fixed n) .target }
  | .enter .fightUpToOne =>
    { events := #[.entering], targeting := .of .anotherCreature, allowsZeroTargets := true,
      resolution := .fight }
  | .enter .returnNonlandNontoken =>
    { events := #[.entering], targeting := .of .nonlandNontoken, allowsZeroTargets := true,
      resolution := .returnToHand .permanent .returnedPermanent }
  | .enter .createZabu =>
    { events := #[.entering], resolution := .createTokens .treasure 1 false .zabu }
  | .enter .oppCreatesTheVoid =>
    { events := #[.entering], targeting := .of .opponent,
      resolution := .createTokens .treasure 1 false .theVoid .targetOpponent }
  | .enter .createSturdyShieldAttach =>
    { events := #[.entering],
      resolution := .sequence
        [.createTokens .treasure 1 false .sturdyShield (note := .remember),
         .attach .created .source] }
  | .enter .exileGyPlayUntilNextTurn =>
    { events := #[.entering], targeting := .of .equipmentInstantOrSorceryInYourGraveyard,
      resolution := .sequence
        [.exile .graveyardCard .forLater .playCard, .grantPlayNotedUntilNextTurn] }
  | .enter .returnGyPermanentThisTurn =>
    { events := #[.entering], targeting := .of .permanentCardInYourGraveyard,
      resolution := .returnToHand .graveyardPermanent }
  | .enter .tapOppCantUntapWhileControl =>
    { events := #[.entering], targeting := .of .oppCreature,
      resolution := .sequence [.tap .target, .cant .untapWhileYouControl] }
  | .enter .maySacAnotherThenDestroyOppNonland =>
    { events := #[.entering],
      resolution := .may (.pay .anotherCreature) (.queueReflexive (.destroy .target)) .ifYouDo }
  | .enter .maySacOrDiscardNonlandThenDamage =>
    { events := #[.entering],
      resolution := .may (.pay .artifactOrDiscardNonland)
        (.queueReflexive (.dealDamage (.fixed 2) .target)) .ifYouDo }
  | .enter .revealHandExileUntilLeaves =>
    { events := #[.entering], targeting := .of .opponent, allowsZeroTargets := true,
      resolution := .revealFromHand .hand (.exile .target .untilSourceLeaves) }
  | .enter .plusOnesOrReturnArtEnch =>
    { events := #[.entering], targeting := .of .creature, allowsZeroTargets := true,
      resolution := .or
        [.putCounters (.ofKind .plusOnePlusOne) .permanent,
         .returnToHand .graveyardCard] }
  | .enter .chooseUpToXModes =>
    { events := #[.entering], targeting := .of .opponent, allowsZeroTargets := true,
      resolution := .chooseModes TriggeredAbility.TriggerResolution.upToXModes
        .alreadyChosen }
  | .enter .mayTapThenGrantIndestructible =>
    { events := #[.entering],
      resolution := .may (.tap .source) (.queueReflexive (.grant (.keywords Keyword.indestructible) .target)) .ifYouDo }
  | .enter .tapLoseAbilitiesWhileSource =>
    { events := #[.entering], targeting := .of .creature, allowsZeroTargets := true,
      resolution := .sequence
        [.tap .targetIfPresent, .lose .allAbilities .targetIfPresent] }
  | .enter .revealDiscardFromHand =>
    { events := #[.entering], targeting := .of .player,
      resolution := .revealFromHand .onePlusCreatureCards
        (.discard (.cards 1 .targetOpponent)) }
  | .enter .createRedwing =>
    { events := #[.entering], resolution := .createTokens .treasure 1 false .redwing }
  | .step .enchantedControllerDraws =>
    { events := #[.enchantedControllerUpkeep]
      resolution := .draw (.fixed 1) (who := .enchantedController) }
  | .step .drawToTen =>
    { events := #[.yourEndStep], resolution := .draw (.upToHandSize 10) }
  | .step .copyAbsorbingMan =>
    { events := #[.yourFirstMain]
      targeting := .of (.filtered {
        noun := "up to one target artifact, non-Aura enchantment, or land"
        types := #[.artifact, .enchantment, .land]
        nonAura := true })
      allowsZeroTargets := true, maxTargets := 1
      resolution := .becomeCopy .artifactEnchantmentOrLand }
  | .step .hydeChoose =>
    { events := #[.yourUpkeep],
      resolution := .chooseModes TriggeredAbility.TriggerResolution.hydeModes
        .plusOneOrRemoveCounter }
  | .step .copyTaskmaster =>
    { events := #[.yourFirstMain], targeting := .of .creatureOrGyCreatureCard,
      allowsZeroTargets := true, maxTargets := 1
      resolution := .becomeCopy .creatureOrGraveyardCard }
  | .step .harnessedFlicker =>
    { events := #[.yourEndStep]
      targeting := .of (.filtered {
        noun := "up to one other target nonland permanent you control"
        nonland := true, controller := .you, another := true })
      allowsZeroTargets := true, maxTargets := 1
      resolution := .«if» .sourceHarnessed (.exile .target .returnImmediately) }
  | .death .hellcatReturn =>
    { events := #[.dying]
      resolution := .put .source .underOwner (.entering [
        .loseAllAbilities, .keywords Keyword.haste,
        .counter .plusOnePlusOne (asEnters := true)]) }
  | .death .villainReturnAsHero =>
    { events := #[.villainYouControlDies]
      resolution := .put (.cause (some "Villain")) .underOwner (.entering [
        .additionalSubtype "Hero", .counter .finality]) }
  | .death .attackingReturnHand =>
    { events := #[.attackingCreatureYouControlDies]
      resolution := .returnToHand .cause }
  | .death .deathtouchOppSac =>
    { events := #[.creatureYouControlDies]
      resolution := .sacrifice .chosenNontokenCreature }
  | .thisAttack .mayPayPlusOne =>
    { events := #[.attacking]
      resolution := .may (.pay (.mana #[.generic 1])) (.queueReflexive (.putCounters (.ofKind .plusOnePlusOne) .permanent)) .ifYouDo }
  | .thisAttack .payReturnAttacking =>
    { events := #[.attacking]
      resolution := .may (.pay (.mana #[.generic 3, .colored .black]))
        (.queueReflexive (.put .creatureCard .tapped (.entering [.attacking, .counter .finality]))) .ifYouDo }
  | .thisAttack .ifArtifactEnteredDraw =>
    { events := #[.attacking]
      resolution := .«if» .artifactEnteredThisTurn (.draw (.fixed 1)) }
  | .thisAttack .blinkNontoken =>
    { events := #[.attacking]
      targeting := .of (.filtered {
        noun := "up to one target nontoken artifact or creature"
        types := #[.artifact, .creature], nontoken := true })
      allowsZeroTargets := true, maxTargets := 1
      resolution := .exile .target .returnTapped }
  | .thisAttack .equippedDrain =>
    { events := #[.attacking]
      resolution := .«if» .attachedEquipment (.sequence [
        .loseLife .attachedEquipment .eachOpponent,
        .gainLife .attachedEquipment]) }
  | .thisAttack .drawIfPower4 =>
    { events := #[.attacking]
      resolution := .«if» (.sourcePowerAtLeast 4) (.draw (.fixed 1)) }
  | .thisAttack .attacksAlonePlus2Indestructible =>
    { events := #[.attacking]
      resolution := .sequence [
        .pump (.fixed 2) (.fixed 0) .source,
        .grant (.keywords Keyword.indestructible) .source] }
  | .enterOrAttack .copyKeywords =>
    { events := #[.entering, .attacking], targeting := .of .anotherCreature,
      resolution := .putCounters .missingKeywordsFromTarget .source }
  | .enterOrAttack .createSquirrel =>
    { events := #[.entering, .attacking],
      resolution := .createTokens .squirrel11green 1 false }
  | .watch .combatDamageExileUntilNonland =>
    { events := #[.dealsCombatDamageToPlayer],
      resolution := .revealLibrary .untilNonland
        (.may (.putCounters (.ofKind .plusOnePlusOne) .source)
          (.exile .top .forLater .anyManaThisTurn) .ifYouDont)
        .announced }
  | .watch .attacksAloneDrain =>
    { events := #[.creatureYouControlAttacksAlone], targeting := .of .opponent,
      resolution := .sequence [.loseLife (.fixed 1) .targetOpponent, .gainLife (.fixed 1)] }
  | .watch .attacksAloneFirstStrikeMenace =>
    { events := #[.creatureYouControlAttacksAlone],
      resolution := .grant
        (.keywords (Keywords.merge Keyword.firstStrike Keyword.menace)) .attackingAlone }
  | .watch .firstTapUntap =>
    { events := #[.creatureYouControlTapped], resolution := .untap .firstThisTurn }
  | .watch .sheHulkRedirectOnce =>
    { events := #[.creatureYouControlDealtDamage], targeting := .of .playerOrCreature,
      resolution := .may (.dealDamage .lastKnownPower .target) (.sequence []) .ifYouDo }
  | .watch .speedballTargeted =>
    { events := #[.spellTargetsSource],
      resolution := .sequence [
        .pump (.fixed 2) (.fixed 2) .source, .may .retargetCause (.sequence []) .ifYouDo] }
  | .watch .anyPlayerSecondDraw =>
    { events := #[.anyPlayerDrawsSecond], resolution := .draw (.fixed 1) }
  | .watch .youTargetDrawOnce =>
    { events := #[.youTargetSomething], onceEachTurn := true, resolution := .draw (.fixed 1) }
  | .watch .villainOrArtifactDamage =>
    { events := #[.anotherVillainOrArtifactEnters], targeting := .of .opponent,
      resolution := .dealDamage (.fixed 1) (.player .targetOpponent) }
  | .watch .villainConniveOnce =>
    { events := #[.anotherVillainEnters], optionalOnceEachTurn := true,
      resolution := .connive .enteringVillain }
  | .watch .villainPlusOneDamageOnce =>
    { events := #[.anotherVillainEnters], onceEachTurn := true,
      resolution := .sequence [
        .putCounters (.ofKind .plusOnePlusOne) .sourceIfPresent,
        .dealDamage (.fixed 2) (.player .eachOpponent)] }
  | .watch .villainAttachEquipment =>
    { events := #[.anotherVillainEnters]
      targeting := .of .upToOneEquipmentThenCreatureYouControl
      resolution := .attach .announcedEquipment .announcedCreature }
  | .watch .villainPlusOneLifelink =>
    { events := #[.anotherVillainEnters],
      resolution := .sequence [
        .pump (.fixed 1) (.fixed 0) .source, .grant (.keywords Keyword.lifelink) .source] }
  | .watch .hulklingCompare =>
    { events := #[.anotherCreatureYouControlEnters],
      resolution := .«if» .causeGreaterPowerOrToughness
        (.putCounters (.ofKind .plusOnePlusOne) .source) }
  | .watch .justiceBounce =>
    { events := #[.anotherNonlandReturned],
      resolution := .putCounters (.ofKind .plusOnePlusOne) .source }
  | .watch .nontokenHeroModal =>
    { events := #[.anotherNontokenHeroEnters],
      resolution := .chooseModes
        [.createTokens .soldier11white 1 false,
         .pump (.fixed 1) (.fixed 1) .creaturesYouControl]
        .fromLastKnown }
  | .watch .ultronCopy =>
    { events := #[.anotherNontokenArtifactEnters],
      resolution := .may (.pay (.mana #[.generic 2])) (.becomeCopy .cause) .ifYouDo }
  | .watch .enchantedAttachEquipment =>
    { events := #[.enchantedAttacksOrBlocks], targeting := .of .equipmentYouControl
      allowsZeroTargets := true, maxTargets := 1000,
      resolution := .attach .eachTargetEquipment .enchantedCreature }
  | .watch .equippedAttacksAloneUntapScry =>
    { events := #[.equippedAttacksAlone],
      resolution := .sequence [.untap .equipped, .scry (.fixed 1)] }
  | .watch .equippedAttacksTap =>
    { events := #[.equippedAttacks], targeting := .of .defendingPlayerCreature,
      resolution := .tap .target }
  | .watch .equippedTappedDamage =>
    { events := #[.equippedBecomesTapped],
      resolution := .dealDamage (.fixed 1) (.player .eachOpponent) .fromEquipped }
  | .watch .heroesDamagePlusTwo =>
    { events := #[.heroesDealDamageToPlayer],
      resolution := .putCounters (.ofKind .plusOnePlusOne 2) .source }
  | .watch .merfolkAttackDraw =>
    { events := #[.merfolkAttackPlayer], resolution := .draw (.fixed 1) }
  | .watch .tokensEnterMayDraw =>
    { events := #[.tokenYouControlEnters],
      resolution := .may (.draw (.fixed 1)) (.sequence []) .ifYouDo }
  | .watch .hawkeyeModes =>
    { events := #[.sourceBecomesTapped], allowsZeroTargets := true,
      resolution := .may (.pay (.mana #[.generic 1])) (.queueReflexive (.chooseModes TriggeredAbility.TriggerResolution.trickArrowModes .alreadyChosen)) .ifYouDo }
  | .watch .redHulk =>
    { events := #[.sourceDealtDamage],
      resolution := .sequence [
        .putCounters (.ofKind .plusOnePlusOne) .source,
        .queueReflexive (.dealDamage .plusOneCounters .target)] }
  | .watch .hulk =>
    { events := #[.sourceDealtDamage],
      resolution := .sequence [
        .putCounters (.ofKind .plusOnePlusOne) .source,
        .«if» .sourceAttacking (.untap .source),
        .«if» .enrageGrantsCombat .additionalCombatPhase] }
  | .youAttacking .pay2LifeToughness =>
    { events := #[.youAttack],
      resolution := .may (.loseLife (.fixed 2))
        (.grant .assignCombatDamageEqualToughness .creaturesYouControl) .ifYouDo }
  | .youAttacking .exileTopHeroPump =>
    { events := #[.youAttack],
      resolution := .may (.exile .top .playThisTurn .ifHero) (.sequence []) }
  | .youAttacking .lookSixCast =>
    { events := #[.youAttack],
      resolution := .revealLibrary (.top 6)
        (.mayCast .looked .greatestAttackingPower .withoutPaying) }
  | .casting .villainToken =>
    { events := #[.youCastVillain],
      resolution := .createTokens .villain21menace 1 false }
  | .casting .merfolkFromBlue =>
    { events := #[.youCastNoncreature],
      resolution := .createTokens .treasure 0 false .merfolk (qty := .blueManaSymbols) }
  | .casting .mayPayHasteUnblockable =>
    { events := #[.youCastNoncreature],
      resolution := .may (.pay (.mana #[.generic 1])) (.queueReflexive (.cant (.beBlockedExceptByHaste .target))) .ifYouDo }
  | .casting .plusOneEachOther =>
    { events := #[.youCastNoncreature],
      resolution := .putCounters (.ofKind .plusOnePlusOne) .eachOther }
  | .casting .exileFlicker =>
    { events := #[.youCastNoncreature]
      targeting := .of (.filtered {
        noun := "another target nonland, nontoken permanent"
        nonland := true, nontoken := true, another := true })
      resolution := .exile .target .nextEndStep }
  | .casting .visionModes =>
    { events := #[.youCastNoncreature],
      resolution := .chooseModes TriggeredAbility.TriggerResolution.visionModes .vision }
  | .casting .damageEqualMv =>
    { events := #[.youCastNoncreature], targeting := .of .playerOrCreature,
      resolution := .dealDamage .spellManaValue .target }
  | .casting .drawPowerEqualHand =>
    { events := #[.youCastTargetingCreatureYouControl],
      resolution := .sequence [.draw (.fixed 1), .grant .basePowerEqualHand .source] }
  | .casting .plusOneThis =>
    { events := #[.youCastTargetingCreatureYouControl],
      resolution := .putCounters (.ofKind .plusOnePlusOne) .source }
  | .casting .plusOneScry =>
    { events := #[.youCastTargetingCreatureYouControl],
      resolution := .sequence [.putCounters (.ofKind .plusOnePlusOne) .source, .scry (.fixed 1)] }
  | .casting .ironFistTap =>
    { events := #[.youCastTargetingCreatureYouControl],
      resolution := .grant .ironFistTap .source }
  | .casting .targetsGainFlying =>
    { events := #[.youCastTargetingCreature],
      resolution := .grant (.keywords Keyword.flying) .spellTargets }
  | .casting .copyIfArtifactOrLand =>
    { events := #[.youCastInstantSorceryTargetingArtifactOrLand],
      resolution := .sequence [
        .putCounters (.ofKind .plusOnePlusOne 2) .source, .copyCause] }
  | .casting .tapCreatureOrLand =>
    { events := #[.youCastNoncreature],
      targeting := .of (.filtered {
        noun := "target creature or land",
        types := #[.creature, .land] }),
      resolution := .tap .target }
  | .resource .discardExilePlay =>
    { events := #[.youDiscard],
      resolution := .may (.exile .discarded .playUntilNextTurn) (.sequence []) .ifYouDo }
  | .resource .drawIfAnotherHeroDamage =>
    { events := #[.youDraw], targeting := .of .opponent,
      resolution := .«if» .anotherHero (.dealDamage (.fixed 1) (.player .targetOpponent)) }
  | .resource .secondDrawBecome66 =>
    { events := #[.youDrawSecondCard],
      resolution := .sequence [
        .setBasePT (.fixed 6) (.fixed 6) .source, .grant (.keywords Keyword.trample) .source] }
  | .resource .secondDrawPlusOneTarget =>
    { events := #[.youDrawSecondCard], targeting := .of .creature,
      resolution := .putCounters (.ofKind .plusOnePlusOne) .permanent }
  | .resource .secondDrawDrain =>
    { events := #[.youDrawSecondCard],
      resolution := .sequence [.loseLife (.fixed 1) .eachOpponent, .gainLife (.fixed 1)] }
  | .resource .gainLifePlusOnes =>
    { events := #[.youGainLife], targeting := .of .creatureYouControl,
      allowsZeroTargets := true,
      resolution := .putCounters (.ofKind .plusOnePlusOne) .eachUpToLastKnown }
  | .resource .plusOneCreateInsectOnce =>
    { events := #[.youPutPlusOne], onceEachTurn := true,
      resolution := .createTokens .insect11green 1 false }
  | .resource .plusOneOnThisOnce =>
    { events := #[.youPutPlusOne], onceEachTurn := true,
      resolution := .putCounters (.ofKind .plusOnePlusOne) .source }
  | .resource .plusOneOnHeroesCreateWall =>
    { events := #[.youPutPlusOne],
      resolution := .may (.createTokens .wall04defender 1 false) (.sequence []) .ifYouDo }

end SharedTrigger

#guard !(SharedTrigger.timing (.watch .sheHulkRedirectOnce)).onceEachTurn
#guard (SharedTrigger.timing (.watch .sheHulkRedirectOnce)).targeting.kind ==
  .playerOrCreature
#guard (SharedTrigger.timing (.thisAttack .blinkNontoken)).allowsZeroTargets &&
  (SharedTrigger.timing (.thisAttack .blinkNontoken)).maxTargets == 1
#guard (SharedTrigger.timing (.thisAttack .mayPayPlusOne)).resolution ==
  .may (.pay (.mana #[.generic 1])) (.queueReflexive (.putCounters (.ofKind .plusOnePlusOne) .permanent)) .ifYouDo
#guard (SharedTrigger.timing (.thisAttack .payReturnAttacking)).resolution ==
  .may (.pay (.mana #[.generic 3, .colored .black])) (.queueReflexive (.put .creatureCard .tapped (.entering [.attacking, .counter .finality]))) .ifYouDo
#guard (SharedTrigger.timing (.thisAttack .ifArtifactEnteredDraw)).resolution ==
  .«if» .artifactEnteredThisTurn (.draw (.fixed 1))
#guard (SharedTrigger.timing (.thisAttack .blinkNontoken)).resolution ==
  .exile .target .returnTapped
#guard (SharedTrigger.timing (.thisAttack .equippedDrain)).resolution ==
  .«if» .attachedEquipment (.sequence [
    .loseLife .attachedEquipment .eachOpponent,
    .gainLife .attachedEquipment])
#guard (SharedTrigger.timing (.thisAttack .drawIfPower4)).resolution ==
  .«if» (.sourcePowerAtLeast 4) (.draw (.fixed 1))
#guard (SharedTrigger.timing (.thisAttack .attacksAlonePlus2Indestructible)).resolution ==
  .sequence [.pump (.fixed 2) (.fixed 0) .source, .grant (.keywords Keyword.indestructible) .source]
#guard (SharedTrigger.timing (.enterOrAttack .copyKeywords)).targeting.kind ==
  .anotherCreature
#guard (SharedTrigger.timing (.enterOrAttack .copyKeywords)).resolution ==
  .putCounters .missingKeywordsFromTarget .source
#guard (SharedTrigger.timing (.enterOrAttack .createSquirrel)).resolution ==
  .createTokens .squirrel11green 1 false
#guard (SharedTrigger.timing (.watch .villainConniveOnce)).optionalOnceEachTurn
#guard (SharedTrigger.timing (.watch .combatDamageExileUntilNonland)).resolution ==
  .revealLibrary .untilNonland
    (.may (.putCounters (.ofKind .plusOnePlusOne) .source)
      (.exile .top .forLater .anyManaThisTurn) .ifYouDont)
    .announced
#guard (SharedTrigger.timing (.watch .hawkeyeModes)).resolution ==
  .may (.pay (.mana #[.generic 1])) (.queueReflexive (.chooseModes TriggeredAbility.TriggerResolution.trickArrowModes .alreadyChosen)) .ifYouDo
#guard (SharedTrigger.timing (.watch .hulk)).resolution ==
  .sequence [
    .putCounters (.ofKind .plusOnePlusOne) .source,
    .«if» .sourceAttacking (.untap .source),
    .«if» .enrageGrantsCombat .additionalCombatPhase]
#guard (SharedTrigger.timing (.enterOrAttack .copyKeywords)).events ==
  #[TriggerEvent.entering, TriggerEvent.attacking]
#guard (SharedTrigger.timing (.death .hellcatReturn)).resolution ==
  .put .source .underOwner (.entering [
    .loseAllAbilities, .keywords Keyword.haste,
    .counter .plusOnePlusOne (asEnters := true)])
#guard (SharedTrigger.timing (.death .villainReturnAsHero)).resolution ==
  .put (.cause (some "Villain")) .underOwner (.entering [
    .additionalSubtype "Hero", .counter .finality])
#guard (SharedTrigger.timing (.death .attackingReturnHand)).resolution ==
  .returnToHand .cause
#guard (SharedTrigger.timing (.death .deathtouchOppSac)).resolution ==
  .sacrifice .chosenNontokenCreature
#guard TriggeredAbility.TriggerResolution.ofPermanent .loseIndestructible ==
  .lose .indestructible
#guard TriggeredAbility.TriggerResolution.ofSource .loseIndestructible ==
  .lose .indestructible .source
#guard TriggeredAbility.TriggerResolution.ofEnchanted .loseIndestructible ==
  .lose .indestructible .enchanted
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .loseIndestructible ==
  .lose .indestructible .targetWhileSource
#guard TriggeredAbility.TriggerResolution.ofPermanent .cantBeBlocked ==
  .cant .beBlocked
#guard TriggeredAbility.TriggerResolution.ofPermanent .indestructibleCounter ==
  .putCounters (.ofKind .indestructible) .permanent
#guard TriggeredAbility.TriggerResolution.ofPermanent .doubleStrikeCounter ==
  .putCounters (.ofKind .doubleStrike) .permanent
#guard TriggeredAbility.TriggerResolution.ofPermanent .burdenCounter ==
  .putCounters (.ofKind .burden) .permanent
#guard TriggeredAbility.TriggerResolution.ofPermanent .becomeArtifactIndestructible ==
  .sequence [.becomeArtifact, .grant (.keywords Keyword.indestructible) .target]
#guard TriggeredAbility.TriggerResolution.ofPermanent .becomePrepared == .becomePrepared
#guard TriggeredAbility.TriggerResolution.ofPermanent (.setBasePT 2 2) ==
  .setBasePT (.fixed 2) (.fixed 2)
#guard TriggeredAbility.TriggerResolution.ofPermanent .tapAndStun ==
  .sequence [.tap .target, .putCounters (.ofKind .stun) .permanent]
#guard TriggeredAbility.TriggerResolution.ofPermanent .putOnTopOfLibrary ==
  .putOnLibrary .top
#guard TriggeredAbility.TriggerResolution.ofPermanent .putOnBottomOfLibrary ==
  .putOnLibrary .bottom
#guard TriggeredAbility.TriggerResolution.ofSource .putOnTopOfLibrary ==
  .putOnLibrary .top .source
#guard TriggeredAbility.TriggerResolution.ofSource .putOnBottomOfLibrary ==
  .putOnLibrary .bottom .source
#guard TriggeredAbility.TriggerResolution.ofEnchanted .putOnTopOfLibrary ==
  .putOnLibrary .top .enchanted
#guard TriggeredAbility.TriggerResolution.ofEnchanted .putOnBottomOfLibrary ==
  .putOnLibrary .bottom .enchanted
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .putOnTopOfLibrary ==
  .putOnLibrary .top .targetWhileSource
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .putOnBottomOfLibrary ==
  .putOnLibrary .bottom .targetWhileSource
#guard TriggeredAbility.TriggerResolution.ofPermanent .exile == .exile .target .forLater
#guard TriggeredAbility.TriggerResolution.ofSource .exile == .exile .source .forLater
#guard TriggeredAbility.TriggerResolution.ofEnchanted .exile ==
  .exile .enchanted .forLater
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .exile ==
  .exile .targetWhileSource .forLater
#guard TriggeredAbility.TriggerResolution.ofPermanent .doublePowerAndToughness ==
  .pump .double .double .target
#guard TriggeredAbility.TriggerResolution.ofPermanent (.pumpAndTrample 2 0) ==
  .sequence [.pump (.fixed 2) (.fixed 0) .target, .grant (.keywords Keyword.trample) .target]
#guard TriggeredAbility.TriggerResolution.ofSource (.plusOne 1) ==
  .putCounters (.ofKind .plusOnePlusOne) .source
#guard TriggeredAbility.TriggerResolution.ofSource (.pump 1 1) ==
  .pump (.fixed 1) (.fixed 1) .source
#guard TriggeredAbility.TriggerResolution.ofSource .tap == .tap .source
#guard TriggeredAbility.TriggerResolution.ofEnchanted .tap == .tap .enchantedWhileSource
#guard TriggeredAbility.TriggerResolution.ofEnchanted (.grantKeywords Keyword.firstStrike) ==
  .grant (.keywords Keyword.firstStrike) .enchanted
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .untap ==
  .untap .targetWhileSource
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource
    (.grantKeywords Keyword.indestructible) ==
  .grant (.keywords Keyword.indestructible) .targetWhileSource
#guard (SharedTrigger.timing (.resource .discardExilePlay)).resolution ==
  .may (.exile .discarded .playUntilNextTurn) (.sequence []) .ifYouDo
#guard (SharedTrigger.timing (.resource .drawIfAnotherHeroDamage)).resolution ==
  .«if» .anotherHero (.dealDamage (.fixed 1) (.player .targetOpponent))
#guard (SharedTrigger.timing (.resource .secondDrawBecome66)).resolution ==
  .sequence [.setBasePT (.fixed 6) (.fixed 6) .source, .grant (.keywords Keyword.trample) .source]
#guard (SharedTrigger.timing (.resource .secondDrawPlusOneTarget)).resolution ==
  .putCounters (.ofKind .plusOnePlusOne) .permanent
#guard (SharedTrigger.timing (.resource .secondDrawDrain)).resolution ==
  .sequence [.loseLife (.fixed 1) .eachOpponent, .gainLife (.fixed 1)]
#guard (SharedTrigger.timing (.resource .gainLifePlusOnes)).resolution ==
  .putCounters (.ofKind .plusOnePlusOne) .eachUpToLastKnown
#guard (SharedTrigger.timing (.resource .plusOneCreateInsectOnce)).resolution ==
  .createTokens .insect11green 1 false
#guard (SharedTrigger.timing (.resource .plusOneOnThisOnce)).resolution ==
  .putCounters (.ofKind .plusOnePlusOne) .source
#guard (SharedTrigger.timing (.resource .plusOneOnHeroesCreateWall)).resolution ==
  .may (.createTokens .wall04defender 1 false) (.sequence []) .ifYouDo

end Mtg.Engine
