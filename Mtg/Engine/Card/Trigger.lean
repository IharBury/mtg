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
`.source`. -/
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
deriving Repr, Inhabited, BEq

/-- Objects chosen for `TriggerResolution.objectCost`, the optional action of
`TriggerResolution.mayThen`. -/
inductive TriggerObjectCost where
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

/-- A reflexive triggered ability queued by `TriggerResolution.queueReflexive`
after the optional action of `mayThen` (“When you do”). -/
inductive TriggerReflexive where
  /-- An MSH modeled reflexive. `0` grants indestructible. `7` destroys an
  opposing nonland. -/
  | modeled (kind : Nat)
  /-- “This deals `n` damage to any target.” -/
  | damageAny (n : Nat)
deriving Repr, Inhabited, BEq

/-- Who `TriggerResolution.dealDamage` damages. -/
inductive TriggerDamageWho where
  /-- Each creature blocking the source. -/
  | blockers
  /-- The announced permanent. -/
  | permanent
  /-- Each opponent, or the announced opponent when the ability targets. -/
  | eachOpponent
  /-- The announced target, a player or a permanent. -/
  | target
  /-- The announced opponent. -/
  | targetOpponent
deriving Repr, Inhabited, BEq

/-- Where `TriggerResolution.dealDamage` reads the amount. The `n` argument
is used when this is `.fixed`. -/
inductive TriggerDamageAmount where
  /-- The `n` argument. -/
  | fixed
  /-- The source's last-known power. -/
  | lastKnownPower
  /-- How many permanents of this subtype the controller controls. -/
  | subtypeCount (subtype : String)
  /-- How many cards an earlier step discarded from the controller's hand. -/
  | discardedHand
deriving Repr, Inhabited, BEq

/-- What `TriggerResolution.dealDamage` records for a later step. -/
inductive TriggerDamageNote where
  /-- The damage only. -/
  | none
  /-- The permanent that was actually marked, for a later destroy. -/
  | markedPermanent
  /-- Excess over the permanent's remaining toughness, for a later amass. -/
  | excess
deriving Repr, Inhabited, BEq

/-- Who `TriggerResolution.putCounters` puts counters on. -/
inductive TriggerCounterWho where
  /-- Permanents you control.
  Each creature is `.youControl`.
  Each permanent of a subtype is `.youControl (.subtype s)`.
  One counter, or two with the city's blessing, is `.youControl .citysBlessing`. -/
  | youControl (which : YouControlPlusOne := .eachCreature)
  /-- Each other creature you control. -/
  | eachOther
  /-- The announced permanent. `byYou` means the controller puts the counters,
  and an illegal target logs that you won't put counters. -/
  | permanent (byYou : Bool := false)
  /-- The ability's source. -/
  | source
  /-- The token an earlier step created. -/
  | createdToken
deriving Repr, Inhabited, BEq

/-- What `TriggerResolution.putCounters` puts. `ofKind` uses its `n`. -/
inductive TriggerCounterWhat where
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
deriving Repr, Inhabited, BEq

/-- Who `TriggerResolution.pump` gives +P/+T until end of turn. -/
inductive TriggerPumpWho where
  /-- The ability's source. -/
  | source
  /-- The announced permanent. -/
  | target
  /-- The creature that caused the trigger. -/
  | cause
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

/-- What `TriggerResolution.exile` exiles. -/
inductive TriggerExileWhat where
  /-- The announced permanent. -/
  | target
  /-- Each announced permanent. -/
  | eachTarget
  /-- The top card of the controller's library. -/
  | top
  /-- Each announced land the controller still controls. -/
  | landsYouControl
  /-- The announced graveyard card. -/
  | graveyardCard
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
  /-- Move it to exile. `note` tells the next step which cards moved. -/
  | forLater
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
deriving Repr, Inhabited, BEq

/-- Who `TriggerResolution.sacrifice` asks to sacrifice. -/
inductive TriggerSacrificeWho where
  /-- The announced opponent. -/
  | targetOpponent
  /-- Each player, in turn order. -/
  | eachPlayer
  /-- The player the source is attacking, or the controller's opponent. -/
  | defender
  /-- Each opponent. -/
  | eachOpponent
  /-- The controller of the ability. -/
  | you
deriving Repr, Inhabited, BEq

/-- Which permanent `TriggerResolution.sacrifice` sacrifices. -/
inductive TriggerSacrificeWhat where
  /-- A creature of that player's choice. -/
  | chosenCreature
  /-- A creature with the least power among creatures that player controls. -/
  | leastPower
  /-- A creature that dealt combat damage to you this turn. -/
  | combatDamager
  /-- The ability's source. `how` says how it moves to the graveyard. -/
  | source (how : SacrificeSourceHow := .isSacrificed)
  /-- The Plan, if it is still on the battlefield. -/
  | plan
  /-- Another creature the controller controls. -/
  | another
deriving Repr, Inhabited, BEq

/-- What a later step of `TriggerResolution.sacrifice` can read. -/
inductive TriggerSacrificeNote where
  /-- Nothing beyond the sacrifice itself. -/
  | none
  /-- Whether the Plan was actually sacrificed. A following reflexive
  ability triggers only when it was. -/
  | forReflexive
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
deriving Repr, Inhabited, BEq

/-- Where `TriggerResolution.pump` reads the bonus. `power` and `toughness`
are used when this is `.fixed`. -/
inductive TriggerPumpAmount where
  /-- +X/+0, where X is the greatest power among creatures the controller controls. -/
  | greatestPower
  /-- +1/+1 for each card looked at while scrying. -/
  | perLookedAt
  /-- +1/+1 for each other creature the controller controls. -/
  | perOtherCreature
  /-- +1/+1 for each Plains the controller controls. -/
  | perPlains
  /-- The `power` and `toughness` arguments. -/
  | fixed
  /-- +X/+X, where X is the source's toughness. -/
  | equalSourceToughness
  /-- +X/+0, where X is the source's power. -/
  | equalSourcePower
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

/-- Who `TriggerResolution.draw` draws for. -/
inductive TriggerDrawWho where
  /-- The controller of the ability. -/
  | you
  /-- The targeted opponent may have the controller draw a card.
  Declining mills X cards, where X is the influence counters on the source,
  and that player loses life equal to the total mana value of those cards.
  An earlier step must have recorded the offer. -/
  | opponentHasYou
deriving Repr, Inhabited, BEq

/-- Where `TriggerResolution.draw` reads how many cards. The `n` argument
is used when this is `.fixed`. -/
inductive TriggerDrawAmount where
  /-- The `n` argument. -/
  | fixed
  /-- One card for each Human tapped by an earlier step. -/
  | forEachTappedHuman
  /-- One card for each graveyard with seven or more cards. -/
  | perFatGraveyard
  /-- As many cards as an earlier step discarded from the controller's hand. -/
  | discardedHandCount
  /-- X cards, where X is the mana spent to cast the triggering spell.
  Spending none skips the later steps of the sequence. -/
  | equalToManaSpent
deriving Repr, Inhabited, BEq

/-- Which cards `TriggerResolution.returnToHand` returns. -/
inductive TriggerReturnWhat where
  /-- The announced graveyard card. A card that has left is reported. -/
  | graveyardCard
  /-- The announced permanent. -/
  | permanent
  /-- The announced graveyard card, or that card as a permanent target. -/
  | graveyardPermanent
  /-- Cards an earlier step milled that have this subtype. -/
  | milledSubtype (subtype : String)
  /-- The source, if it is still in its owner's graveyard. -/
  | source
  /-- The card `revealLibrary .untilCreature` revealed, on the hand branch.
  Outside that resolution, `.returnToHand .revealed` does nothing. -/
  | revealed
  /-- A basic land card `searchLibrary` found. Outside that resolution,
  `.returnToHand .basicLand` does nothing. -/
  | basicLand
deriving Repr, Inhabited, BEq

/-- Whose hand `TriggerResolution.returnToHand` returns those cards to. -/
inductive TriggerReturnWhose where
  /-- The controller of the ability. -/
  | you
  /-- The card's owner. -/
  | owner
deriving Repr, Inhabited, BEq

/-- What a later step of `TriggerResolution.returnToHand` can read. -/
inductive TriggerReturnNote where
  /-- Nothing beyond the return itself. -/
  | none
  /-- Whether a permanent was actually returned. -/
  | returnedPermanent
deriving Repr, Inhabited, BEq

/-- Which cards `TriggerResolution.put` puts onto the battlefield. -/
inductive TriggerPutWhat where
  /-- Each card the source exiled. -/
  | linkedExile
  /-- The announced nonland permanent card. Its mana value is at most `mv`. -/
  | nonlandMvAtMost (mv : Nat)
  /-- The source, from its owner's graveyard. -/
  | source
  /-- Lands an earlier step exiled. -/
  | notedLands
  /-- The card an earlier step discarded, when it is a land. -/
  | discardedLand
  /-- A land card from the controller's hand. -/
  | landFromHand
  /-- An artifact card from the controller's hand. -/
  | artifactFromHand
  /-- A random creature from the cards `revealLibrary (.top n)` revealed.
  Outside that resolution, `.put .randomCreature` does nothing. -/
  | randomCreature
  /-- The card `revealLibrary` revealed. Outside `.untilSaga` and the
  battlefield branch of `.untilCreature`, `.put .revealed` does nothing. -/
  | revealed
  /-- A Forest card `searchLibrary` found. Outside that resolution,
  `.put .forest` does nothing. -/
  | forest
  /-- A basic land card `searchLibrary` found, put on top of the library.
  Outside that resolution, `.put .basicLandOnTop` does nothing. -/
  | basicLandOnTop
  /-- A Dragon card `searchLibrary` found in the hand and/or library.
  Outside that resolution, `.put .dragon` does nothing. -/
  | dragon
deriving Repr, Inhabited, BEq

/-- How `TriggerResolution.put` puts those cards onto the battlefield. -/
inductive TriggerPutHow where
  /-- Untapped, as printed. -/
  | asPrinted
  /-- Tapped. -/
  | tapped
  /-- As an artifact. It is not a creature. -/
  | asArtifact
deriving Repr, Inhabited, BEq

/-- What a later step of `TriggerResolution.put` can read. -/
inductive TriggerPutNote where
  /-- Nothing beyond putting the cards. -/
  | none
  /-- The artifact put from hand, and the creature it may attach to. -/
  | forAttach
deriving Repr, Inhabited, BEq

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
deriving Repr, Inhabited, BEq

/-- Which permanents `TriggerResolution.destroy` destroys. -/
inductive TriggerDestroyWhat where
  /-- All artifacts and enchantments opponents control. -/
  | oppArtifactsEnchantments
  /-- The announced creature, if any. Choosing none destroys nothing. -/
  | target
  /-- The permanent an earlier step dealt damage to. -/
  | permanentDealtDamage
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
deriving Repr, Inhabited, BEq

/-- Who `TriggerResolution.discard` asks to discard. -/
inductive TriggerDiscardWho where
  /-- The controller. -/
  | you
  /-- Each opponent. -/
  | each
  /-- The announced opponent. -/
  | target
deriving Repr, Inhabited, BEq

/-- What `TriggerResolution.discard` discards. The `n` argument is the
count when this is `.cards`. -/
inductive TriggerDiscardWhat where
  /-- `n` cards. -/
  | cards
  /-- The controller's hand. The number discarded is noted for a later step.
  Declining leaves the note empty. -/
  | hand
deriving Repr, Inhabited, BEq

/-- When `TriggerResolution.discard` discards those cards. -/
inductive TriggerDiscardWhen where
  /-- As this step resolves. -/
  | now
  /-- When mana was spent to cast the triggering spell. An earlier step
  that saw none skips this one. -/
  | ifManaSpent
deriving Repr, Inhabited, BEq

/-- Who `TriggerResolution.fight` uses. -/
inductive TriggerFightWho where
  /-- The source. -/
  | source
  /-- The creature an earlier step attached Equipment to. -/
  | equipmentHost
deriving Repr, Inhabited, BEq

/-- How `TriggerResolution.fight` uses that creature. -/
inductive TriggerFightHow where
  /-- It fights the announced creature. Each deals damage equal to its
  power to the other. Choosing none fights nothing. -/
  | mutual
  /-- It deals damage equal to its power. The target is chosen when a
  reflexive ability is put on the stack. -/
  | reflexive
deriving Repr, Inhabited, BEq

/-- What `TriggerResolution.grant` grants. -/
inductive TriggerGrantWhat where
  /-- Double strike until end of turn. -/
  | doubleStrike
  /-- Protection from everything until that player's next turn. -/
  | protectionEverything
deriving Repr, Inhabited, BEq

/-- Who `TriggerResolution.grant` grants that to. -/
inductive TriggerGrantWho where
  /-- Each equipped attacking creature. -/
  | equippedAttackers
  /-- The controller, when the source was cast. -/
  | youIfCast
deriving Repr, Inhabited, BEq

/-- Where `TriggerResolution.gainLife` reads how much life. The `n` argument
is used when this is `.fixed`. -/
inductive TriggerLifeAmount where
  /-- The `n` argument. -/
  | fixed
  /-- The targeted card's power. Inside `sequence`, that power is read
  when the sequence starts, before an earlier step moves the card. -/
  | equalToTargetPower
  /-- One life for each permanent an earlier step destroyed.
  Indestructible permanents and shield counters do not count. -/
  | forEachDestroyedThisWay
  /-- One life for each other creature the controller controls.
  The source is not included. -/
  | forEachOtherCreature
deriving Repr, Inhabited, BEq

/-- Who loses life from `TriggerResolution.loseLife`. -/
inductive TriggerLifeLossWho where
  /-- The controller. -/
  | you
  /-- The announced opponent. An illegal target loses nothing. -/
  | targetOpponent
  /-- Each opponent of the controller. -/
  | eachOpponent
deriving Repr, Inhabited, BEq

/-- Where `TriggerResolution.loseLife` reads how much life. The `n` argument
is used when this is `.fixed`. -/
inductive TriggerLifeLossAmount where
  /-- The `n` argument. -/
  | fixed
  /-- One life for each burden counter on the source.
  A source that can no longer be found loses nothing. -/
  | perBurden
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

/-- Who `TriggerResolution.removeCounters` removes counters from. -/
inductive TriggerRemoveWho where
  /-- The ability's source. -/
  | source
  /-- The creature the source enchants. -/
  | enchanted
deriving Repr, Inhabited, BEq

/-- Who `TriggerResolution.tap` taps. -/
inductive TriggerTapWho where
  /-- Any number of untapped Humans the controller controls.
  Choosing none taps nothing. -/
  | humans
  /-- The creature the source enchants. Nothing enchanted taps nothing. -/
  | enchanted
  /-- The announced permanent, while it is still on the battlefield.
  A missing target taps nothing. -/
  | targetIfPresent
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
deriving Repr, Inhabited, BEq

/-- Whose library `TriggerResolution.revealLibrary` looks at. -/
inductive TriggerLibraryWho where
  /-- The controller's library. -/
  | you
  /-- The player who was dealt combat damage. That seat is
  `lastCombatDamagePlayer`. A missing seat is the controller's opponent. -/
  | damagedPlayer
deriving Repr, Inhabited, BEq

/-- How many cards `TriggerResolution.revealFromHand` shows (CR 701.16). -/
inductive TriggerRevealCount where
  /-- The whole hand. -/
  | hand
  /-- One card, plus one for each creature card in the controller's
  graveyard. A smaller hand is shown in full. -/
  | onePlusCreatureCards
deriving Repr, Inhabited, BEq

/-- What a triggered ability does when it resolves (CR 608). Grouped so
`Game.applyTriggeredAbility` matches resolution shapes instead of every
constructor: scry, drawing, discarding, +1/+1 on the source, divided damage,
putting counters, removing counters, until-end-of-turn pumps, creating tokens,
exile, sacrifice, attach, amass, casting a spell, returning cards to hand,
putting onto the battlefield, adding mana, choosing modes, destroying,
fighting, granting, gaining life, losing life, milling, revealing from
a hand, revealing from a library, searching a library, and tapping each
cover multiple printed abilities.
Permanent-target counters and pumps, and source pumps, share
`PermanentAction` with spells and activated abilities. -/
inductive TriggerResolution where
  /-- Until end of turn, permanents of `who` get the bonus from `amount`.
  `power` and `toughness` are that bonus when `amount` is `.fixed`.
  The source by the greatest power among creatures you control is
  `.pump 0 0 .source .greatestPower`.
  The source +1/+1 per card looked at while scrying is
  `.pump 0 0 .source .perLookedAt`.
  The source +1/+1 for each other creature you control is
  `.pump 0 0 .source .perOtherCreature`.
  A target creature you control +1/+1 per Plains is
  `.pump 0 0 .target .perPlains`.
  The creature that caused this +P/+T is `.pump p t .cause`.
  Other permanents of a subtype +X/+X, X = this toughness, is
  `.pump 0 0 (.othersOfSubtype subtype) .equalSourceToughness`.
  Another target creature +X/+0, X = this power, is
  `.pump 0 0 .target .equalSourcePower`.
  Creatures you control +P/+T is `.pump p t .creaturesYouControl`.
  Other creatures of these subtypes +P/+T is
  `.pump p t (.othersOfSubtypes subtypes)`.
  Creatures opponents control +P/+T is `.pump p t .opponentsCreatures`. -/
  | pump (power toughness : Int) (who : TriggerPumpWho)
      (amount : TriggerPumpAmount := .fixed)
  /-- Set another creature's base P/T to this creature's. -/
  | setOtherBasePT
  /-- Deal damage. `n` is the amount when `amount` is `.fixed`.
  Each creature blocking the source is `.dealDamage n .blockers`.
  Last-known power to the announced creature is
  `.dealDamage 0 .permanent .lastKnownPower`.
  `n` damage to each opponent is `.dealDamage n .eachOpponent`.
  When that ability targets, only the announced opponent is dealt damage.
  Damage equal to permanents of `subtype` you control, to each opponent, is
  `.dealDamage 0 .eachOpponent (.subtypeCount subtype)`.
  Damage equal to Treasures you control, to the target, is
  `.dealDamage 0 .target (.subtypeCount "Treasure")`.
  `n` damage to the target, remembering a marked permanent, is
  `.dealDamage n .target .fixed .markedPermanent`.
  Last-known power, noting excess damage, is
  `.dealDamage 0 .permanent .lastKnownPower .excess`.
  Damage to each opponent equal to the hand discarded by an earlier step is
  `.dealDamage 0 .eachOpponent .discardedHand`.
  `n` damage to the announced opponent is `.dealDamage n .targetOpponent`. -/
  | dealDamage (n : Nat) (who : TriggerDamageWho)
      (amount : TriggerDamageAmount := .fixed)
      (note : TriggerDamageNote := .none)
  /-- Scry `n`. -/
  | scry (n : Nat)
  /-- `who` draws cards, as `amount` says. `n` is the count when `amount`
  is `.fixed`.
  The controller draws `n` is `.draw n`.
  A card for each Human tapped by an earlier step is
  `.draw 0 (amount := .forEachTappedHuman)`.
  A card for each graveyard with seven or more cards is
  `.draw 0 (amount := .perFatGraveyard)`.
  Cards equal to the hand an earlier step discarded are
  `.draw 0 (amount := .discardedHandCount)`.
  X cards, where X is the mana spent to cast the triggering spell, are
  `.draw 0 (amount := .equalToManaSpent)`. Spending none skips later steps.
  The targeted opponent may have you draw a card is
  `.draw 1 (who := .opponentHasYou)`.
  Optional as `.may (.draw 1 (who := .opponentHasYou))`. Declining that
  offer mills and that player loses life; it does not skip. -/
  | draw (n : Nat) (who : TriggerDrawWho := .you)
      (amount : TriggerDrawAmount := .fixed)
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
  /-- Discard cards. `n` is the count when `what` is `.cards`.
  One card from the controller is `.discard`.
  Inside `mayThen`, one card is optional: declining skips the conditional.
  Each opponent discards one is `.discard (who := .each)`.
  The announced opponent discards `n` is `.discard n (who := .target)`.
  The controller's hand, noting how many cards were discarded, is
  `.discard (what := .hand)`.
  Optional as `.may (.discard (what := .hand))`. Declining leaves the note
  empty so the following draw and damage steps do nothing.
  `n` cards when mana was spent to cast the triggering spell is
  `.discard n (when := .ifManaSpent)`. -/
  | discard (n : Nat := 1) (who : TriggerDiscardWho := .you)
      (what : TriggerDiscardWhat := .cards)
      (when : TriggerDiscardWhen := .now)
  /-- You may resolve `optional`. If you do, resolve `conditional`.
  Declining, or being unable to perform `optional`, skips `conditional`.
  You may discard a card to draw `n` is `.mayThen (.discard 1) (.draw n)`.
  `SharedTrigger.mayTo a b` resolves as `.mayThen` of each step's resolution.
  You may pay `{n}` to draw is `.mayThen (.pay #[.generic n]) (.draw 1)`.
  Paying `{n}` to put a +1/+1 counter on the source and draw is
  `.mayThen (.pay #[.generic n]) (.sequence [.onSource (.plusOne 1), .draw 1])`.
  You may sacrifice another creature for +1/+1 counters equal to its power is
  `.mayThen (.objectCost .anotherCreature) (.putCounters .plusOneSacrificedPower .source)`.
  You may pay `{1}{G}{U}` to return this from the graveyard is
  `.mayThen (.pay #[.generic 1, .colored .green, .colored .blue]) (.returnToHand .source .owner)`.
  You may sacrifice another creature or artifact to draw and create a Treasure is
  `.mayThen (.objectCost .anotherCreatureOrArtifact) (.sequence [.draw 1, .createTokens .treasure 1 false])`.
  You may discard your hand to draw `n` is `.mayThen (.discard (what := .hand)) (.draw n)`.
  You may sacrifice an artifact or discard a card to draw is
  `.mayThen (.objectCost .artifactOrDiscard) (.draw 1)`.
  You may sacrifice another creature to destroy an opposing nonland is
  `.mayThen (.objectCost .anotherCreature) (.queueReflexive (.modeled 7))`.
  You may sacrifice an artifact or discard a nonland to deal 2 damage is
  `.mayThen (.objectCost .artifactOrDiscardNonland) (.queueReflexive (.damageAny 2))`.
  You may tap this to grant indestructible is
  `.mayThen (.onSource .tap) (.queueReflexive (.modeled 0))`. -/
  | mayThen (optional conditional : TriggerResolution)
  /-- Pay `symbols`. Inside `mayThen`, declining skips the conditional.
  `{n}` is `.pay #[.generic n]`. `{1}{G}{U}` is
  `.pay #[.generic 1, .colored .green, .colored .blue]`. -/
  | pay (symbols : Array ManaSymbol)
  /-- Choose objects for `how`. Inside `mayThen`, declining skips the conditional.
  Sacrificing another creature notes its power. -/
  | objectCost (how : TriggerObjectCost)
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
  `.putCounters .plusOneSacrificedPower .source`. -/
  | putCounters (what : TriggerCounterWhat) (who : TriggerCounterWho)
  /-- Return cards to a hand. `what` says which cards, `whose` says whose
  hand, and `note` says what a later step can read.
  A creature card from your graveyard to your hand is
  `.returnToHand .graveyardCard`.
  The targeted permanent to its owner's hand, noting the return, is
  `.returnToHand .permanent .owner .returnedPermanent`.
  A graveyard permanent card to your hand is
  `.returnToHand .graveyardPermanent`.
  Milled cards of a subtype are `.returnToHand (.milledSubtype subtype)`.
  The source from its owner's graveyard to their hand is
  `.returnToHand .source .owner`.
  The card revealed until a creature, when it does not enter, is
  `.returnToHand .revealed`. Outside that resolution, it does nothing.
  A basic land found by searching is `.returnToHand .basicLand`.
  Outside `searchLibrary`, it does nothing. -/
  | returnToHand (what : TriggerReturnWhat) (whose : TriggerReturnWhose := .you)
      (note : TriggerReturnNote := .none)
  /-- Put reflexive ability `followup` on the stack (“When you do”). -/
  | queueReflexive (followup : TriggerReflexive)
/-- The controller may resolve `action`. Declining skips it.
A choice that already includes decline is that choice, so the player
is not asked twice. You may draw X cards, where X is the mana spent to
cast the triggering spell, then discard two, is
`.may (.sequence [.draw 0 (amount := .equalToManaSpent), .discard 2 (when := .ifManaSpent)])`.
You may tap any number of untapped Humans is `.may (.tap .humans)`.
You may sacrifice another creature is `.may (.sacrifice .you .another)`.
You may put an artifact from your hand onto the battlefield is
`.may (.put .artifactFromHand (note := .forAttach))`.
You may discard your hand is `.may (.discard (what := .hand))`.
The targeted opponent may have you draw a card is
`.may (.draw 1 (who := .opponentHasYou))`. Declining that offer mills and
that player loses life; it does not skip.
You may put a land card from your hand onto the battlefield tapped is
`.may (.put .landFromHand (how := .tapped))`.
`SharedTrigger.may a` resolves as `.may` of `a`'s resolution. -/
| may (action : TriggerResolution)
  /-- Sacrifice a permanent. `who` says who sacrifices, `what` says which
  permanent, and `note` says what a later step can read.
  The announced opponent sacrifices a creature of their choice with
  `.sacrifice .targetOpponent .chosenCreature`.
  Each player sacrifices a creature of their choice with
  `.sacrifice .eachPlayer .chosenCreature`.
  The defending player sacrifices a least-power creature with
  `.sacrifice .defender .leastPower`.
  Each opponent sacrifices a creature that dealt combat damage to you with
  `.sacrifice .eachOpponent .combatDamager`.
  The source is sacrificed with `.sacrifice .you .source`.
  The controller sacrifices the source with
  `.sacrifice .you (.source .controllerSacrifices)`.
  The source moves as sacrificed, without a token-sacrifice trigger, with
  `.sacrifice .you (.source .movedAsSacrificed)`.
  The Plan, if it is still on the battlefield, is `.sacrifice .you .plan`.
  The Plan, noting whether the sacrifice happened, is
  `.sacrifice .you .plan .forReflexive`.
  You may sacrifice another creature with `.may (.sacrifice .you .another)`. -/
  | sacrifice (who : TriggerSacrificeWho) (what : TriggerSacrificeWhat)
      (note : TriggerSacrificeNote := .none)
  /-- Affect a still-legal permanent target. -/
  | onPermanent (action : PermanentAction)
  /-- Deal previously divided damage to the announced targets. -/
  | dividedDamage
  /-- Apply each resolution in order. An illegal required target skips every
  step (CR 608.2b). Return a graveyard card, then gain life equal to its
  power, is `.sequence [.returnToHand .graveyardCard, .gainLife 0 (amount := .equalToTargetPower)]`.
  Draw, then bottom a card if you control no legendary, is
  `.sequence [.draw 1, .«if» .noLegendaryCreature .putFromHandOnBottom]`.
  Remove a hope counter, draw if one was removed, then sacrifice and gain
  life if none remain, is
  `.sequence [.removeCounters .hope .source, .«if» .removedHope (.draw 1), .«if» .noHopeOnSource (.sequence [.sacrifice .you .source, .gainLife 4])]`.
  A step that asks a player to choose pauses the later steps until that
  choice finishes; they are still part of this resolution. Tap any number
  of Humans, then draw that many, is
  `.sequence [.may (.tap .humans), .draw 0 (amount := .forEachTappedHuman)]`.
  Create one token, then attach the source to it, is
  `.sequence [.createTokens kind 1 false, .attach .source .created]`.
  Gain life, then you may search a basic land onto the top, is
  `.sequence [.gainLife n, .searchLibrary (.put .basicLandOnTop)]`.
  Destroy opponents' artifacts and enchantments, then gain 1 life for each
  one actually destroyed, is
  `.sequence [.destroy .oppArtifactsEnchantments (note := .countDestroyed), .gainLife 0 (amount := .forEachDestroyedThisWay)]`.
  Put a +1/+1 counter on each other creature you control, then gain 1 life
  for each other creature you control, is
  `.sequence [.putCounters (.ofKind .plusOnePlusOne) .eachOther, .gainLife 0 (amount := .forEachOtherCreature)]`.
  Deal `n` damage to the target, then destroy it if that damage marked a
  permanent of this subtype, is
  `.sequence [.dealDamage n .target .fixed .markedPermanent, .«if» (.dealtDamageToSubtype subtype) (.destroy .permanentDealtDamage)]`.
  Destroy the announced creature, then its controller amasses that power, is
  `.sequence [.destroy .target (note := .forAmass), .amass 0 (amount := .notedPower) (who := .notedController), .«if» .youControlledDestroyed (.draw 1)]`.
  Return another permanent to its owner's hand, then put a +1/+1 counter on
  the source if one was actually returned, is
  `.sequence [.returnToHand .permanent .owner .returnedPermanent, .«if» .returnedPermanent (.onSource (.plusOne 1))]`.
  Other creatures you control of these subtypes get +P/+T, and creatures
  your opponents control get +oppP/+oppT, is
  `.sequence [.pump p t (.othersOfSubtypes subtypes), .pump oppP oppT .opponentsCreatures]`.
  Gain 1 life, draw, or put a +1/+1 counter on each creature you control
  when this is the first, second, or third resolve this turn (Belladonna
  Took), is
  `.sequence [.noteResolveThisTurn 3, .«if» (.nthResolve 1) (.gainLife 1), .«if» (.nthResolve 2) (.draw 1), .«if» (.nthResolve 3) (.putCounters (.ofKind .plusOnePlusOne) .youControl)]`.
  Deal the sacrificed creature's power, then amass Goblins for the excess
  (Bolg), is
  `.sequence [.dealDamage 0 .permanent .lastKnownPower .excess, .amass 0 (amount := .notedExcess)]`.
  Put a plan counter, then scry, is
  `.sequence [.putCounters (.ofKind .plan) .source, .scry n]`.
  Put a trample counter on the target, then make it a Bear, is
  `.sequence [.putCounters (.ofKind .trample) .permanent, .becomeBear]`.
  Draw, discard, and a land discarded this way enters tapped, is
  `.sequence [.draw 1, .discard 1, .put .discardedLand (how := .tapped)]`.
  Put an influence counter, scry 2, then offer the opponent's choice
  (Palantír of Orthanc), is
  `.sequence [.putCounters (.ofKind .influence) .source, .scry 2, .may (.draw 1 (who := .opponentHasYou))]`.
  Grant keywords, then a +1/+1 counter if the target is a creature and a
  loyalty counter if it is a planeswalker, is
  `.sequence [.onPermanent (.grantKeywords k), .«if» .targetIsCreature (.onPermanent (.plusOne 1)), .«if» .targetIsPlaneswalker (.putCounters (.ofKind .loyalty) .permanent)]`.
  The target gets +3/+0 and gains first strike until end of turn, is
  `.sequence [.onPermanent (.pump 3 0), .onPermanent (.grantKeywords Keyword.firstStrike)]`.
  Destroy the target, then its controller creates a Treasure, is
  `.sequence [.onPermanent .destroy, .createTokens .treasure 1 false (who := .targetController)]`.
  You may put an artifact from your hand onto the battlefield, then attach
  it to the source if it is Equipment, is
  `.sequence [.may (.put .artifactFromHand (note := .forAttach)), .«if» .putArtifactIsEquipment (.attach .putArtifact .notedHost)]`. -/
  | sequence (rs : List TriggerResolution)
  /-- Affect the trigger's source if it is still on the battlefield. -/
  | onSource (action : PermanentAction)
  /-- You gain life (CR 118.2), as `amount` says. `n` is the amount when
  `amount` is `.fixed`.
  You gain `n` life is `.gainLife n`.
  Life equal to the targeted card's power is
  `.gainLife 0 (amount := .equalToTargetPower)`.
  Inside `sequence`, that power is read when the sequence starts, before an
  earlier step moves the card.
  1 life for each permanent destroyed by an earlier step is
  `.gainLife 0 (amount := .forEachDestroyedThisWay)`.
  1 life for each other creature you control is
  `.gainLife 0 (amount := .forEachOtherCreature)`. -/
  | gainLife (n : Nat) (amount : TriggerLifeAmount := .fixed)
  /-- Put a card from your hand on the bottom of your library.
  An empty hand skips the choice. -/
  | putFromHandOnBottom
  /-- Exile cards. `what` says which cards, `how` says for how long, and
  `note` says what a later step can read.
  The targeted permanent, linked for a leave trigger, is
  `.exile .target .leaveTrigger`.
  The targeted permanent until the source leaves is
  `.exile .target .untilSourceLeaves`.
  The top card, playable until the end of your next turn, is
  `.exile .top .playUntilNextTurn`.
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
  resolution, the exile does nothing. -/
  | exile (what : TriggerExileWhat) (how : TriggerExileHow)
      (note : TriggerExileNote := .none)
  /-- Put cards onto the battlefield. `what` says which cards, `how` says
  how they enter, and `note` says what a later step can read.
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
  Optional as `.may (.put .landFromHand (how := .tapped))`.
  An artifact card from your hand, remembered for a later attach, is
  `.put .artifactFromHand (note := .forAttach)`.
  Optional as `.may (.put .artifactFromHand (note := .forAttach))`.
  An empty hand skips that choice.
  A random creature from the cards revealed off the top is
  `.put .randomCreature`. The card revealed until a Saga, or the cheap
  creature, is `.put .revealed`. Outside those resolutions, both do nothing.
  A Forest found by searching is `.put .forest`. A basic land put on top
  after that search is `.put .basicLandOnTop`. A Dragon found in the hand
  and/or library is `.put .dragon`. Outside `searchLibrary`, those do nothing. -/
  | put (what : TriggerPutWhat) (how : TriggerPutHow := .asPrinted)
      (note : TriggerPutNote := .none)
  /-- Remove counters. `what` says which, and `who` says from whom.
  A hope counter from the source is `.removeCounters .hope .source`.
  Removing none leaves the later draw skipped. A missing source, or a
  source that has left the battlefield, removes nothing.
  All counters from the enchanted creature are
  `.removeCounters .all .enchanted`. Nothing enchanted removes nothing.
  Any other combination removes nothing. -/
  | removeCounters (what : TriggerRemoveWhat) (who : TriggerRemoveWho)
  /-- Tap permanents, as `who` says.
  Any number of untapped Humans you control is `.tap .humans`.
  Choosing none taps nothing. Optional as `.may (.tap .humans)`.
  The creature the source enchants is `.tap .enchanted`.
  Nothing enchanted taps nothing. A missing source taps nothing.
  The announced permanent, if it is still on the battlefield, is
  `.tap .targetIfPresent`. A missing target taps nothing.
  Wrapping one in `may` is that tap. -/
  | tap (who : TriggerTapWho)
  /-- Destroy permanents. `what` says which, and `note` says what a later
  step can read.
  Opponents' artifacts and enchantments, counted for the next step, are
  `.destroy .oppArtifactsEnchantments (note := .countDestroyed)`.
  Only permanents that actually leave are counted.
  The permanent an earlier step dealt damage to is
  `.destroy .permanentDealtDamage`.
  The announced creature, noting its controller and power, is
  `.destroy .target (note := .forAmass)`. No target means no player amasses. -/
  | destroy (what : TriggerDestroyWhat) (note : TriggerDestroyNote := .none)
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
  `.createTokens .treasure 1 false (who := .targetController)`. -/
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
  /-- Gain control of the target until end of turn; untap; haste. -/
  | gainControlOppUntilEot
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
  `.«if» .noLegendaryCreature .putFromHandOnBottom`.
  Drawing when an earlier step removed a hope counter is
  `.«if» .removedHope (.draw 1)`.
  Doing `thenDo` on the nth resolution this turn is
  `.«if» (.nthResolve n) thenDo`.
  Attaching the artifact put from hand when it is Equipment is
  `.«if» .putArtifactIsEquipment (.attach .putArtifact .notedHost)`. -/
  | «if» (cond : TriggerIf) (thenDo : TriggerResolution)
  /-- Resolve `whenTrue` when `cond` holds, and `whenFalse` otherwise.
  A tapped Villain when your graveyard has two creature cards, and milling
  two otherwise, is
  `.ifElse (.creatureCardsInGraveyardAtLeast 2) (.createTokens .villain21menace 1 true) (.mill 2)`.
  Two +1/+1 counters when the target is another Hero, and one otherwise, is
  `.ifElse (.targetIsAnotherSubtype "Hero") (.onPermanent (.plusOne 2)) (.onPermanent (.plusOne 1))`.
  A +1/+1 counter when you have scried or surveilled, and +1/+1 until end of
  turn otherwise, is
  `.ifElse .scriedOrSurveilledThisTurn (.onPermanent (.plusOne 1)) (.onPermanent (.pump 1 1))`.
  The revealed creature enters when its mana value is at most the lands
  you control, and goes to your hand otherwise, with
  `.ifElse .revealedManaValueAtMostLands (.put .revealed) (.returnToHand .revealed)`.
  Outside `revealLibrary .untilCreature`, that condition does not hold. -/
  | ifElse (cond : TriggerIf) (whenTrue whenFalse : TriggerResolution)
  /-- The controller chooses one of these resolutions.
  Tap an opposing creature or untap one you control is
  `.or [.onPermanent .tap, .onPermanent .untap]`.
  A +1/+1 counter on a Wolf you control, or a Treasure token, is
  `.or [.onPermanent (.plusOne 1), .createTokens .treasure 1 false]`.
  Tap or untap the targeted nonland is
  `.or [.onPermanent .tap, .onPermanent .untap]`.
  A Food token or a Treasure token is
  `.or [.createTokens .food 1 false, .createTokens .treasure 1 false]`.
  +1/+1 counters on the creature targets, or returning an artifact or
  enchantment card from the graveyard, is
  `.or [.onPermanent (.plusOne 1), .returnToHand .graveyardCard]`. -/
  | or (rs : List TriggerResolution)
  /-- Resolve these modes, as `how` says.
  Alliance is `.chooseModes TriggerResolution.allianceModes .oneUnusedThisTurn`.
  Gollum is `.chooseModes TriggerResolution.gollumModes .oneUnused`.
  Chosen up to X, in printed order, is
  `.chooseModes TriggerResolution.upToXModes .alreadyChosen`. -/
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
  `.mayCast .impulse .unlimited .withoutPaying`. -/
  | mayCast (origin : TriggerCastFrom) (maxMv : TriggerCastMv)
      (cost : TriggerCastCost) (note : TriggerCastNote := .none)
  /-- Grant an ability. `what` says which, and `who` says to whom.
  Each equipped attacking creature gains double strike until end of turn
  with `.grant .doubleStrike .equippedAttackers`.
  If the source was cast, the controller gains protection from everything
  until their next turn with `.grant .protectionEverything .youIfCast`.
  A source that was not cast does nothing.
  Any other combination does nothing. -/
  | grant (what : TriggerGrantWhat) (who : TriggerGrantWho)
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
  /-- Resolve a printed Saga chapter. -/
  | chapter (effect : ChapterResolution)
  /-- Investigate (create a Clue). -/
  | investigate
  /-- Connive (CR 701.48). The source is `.connive`. A target is
  `.connive (.target kind)`. -/
  | connive (who : ConniveSubject := .source)
  /-- Apply `action` to the creature this Aura enchants. -/
  | onEnchanted (action : PermanentAction)
  /-- A creature fights, or deals damage equal to its power. `who` says
  which creature, and `how` says which.
  The source fights up to one other target creature with `.fight`.
  Choosing none fights nothing. A missing source or an illegal target
  fights nothing.
  The creature that received Equipment deals damage equal to its power
  to up to one target creature with `.fight .equipmentHost .reflexive`.
  That target is chosen when the reflexive ability is put on the stack.
  Nothing is queued when no creature received Equipment. -/
  | fight (who : TriggerFightWho := .source) (how : TriggerFightHow := .mutual)
  /-- A player reveals cards from their hand (CR 701.16), as `count` says,
  then resolves `thenDo`.
  The opponent reveals their hand. You may exile a nonland card from it, or
  the chosen creature, until the source leaves, with
  `.revealFromHand .hand (.exile .target .untilSourceLeaves)`.
  A source that has already left still reveals; nothing is exiled.
  The announced player reveals one card plus one for each creature card in
  your graveyard. You choose one of them and that player discards it, with
  `.revealFromHand .onePlusCreatureCards (.discard 1 (who := .target))`.
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
  /-- Untap each attacking creature. -/
  | untapAttackingCreatures
  /-- There is an additional combat phase after this one. -/
  | additionalCombatPhase
  /-- The target becomes a Bear in addition to its other types. -/
  | becomeBear
  /-- Queue the reflexive exile-and-copy of a milled spell. -/
  | reflexiveCopyMilled
  /-- A player loses life (CR 118.3a), as `who` and `amount` say. `n` is
  the amount when `amount` is `.fixed`. Losing 0 life does nothing.
  You lose `n` life is `.loseLife n`.
  The announced opponent loses `n` life is
  `.loseLife n (who := .targetOpponent)`.
  Each opponent loses `n` life is `.loseLife n (who := .eachOpponent)`.
  You lose 1 life for each burden counter on the source is
  `.loseLife 0 (amount := .perBurden)`.
  A missing source loses nothing.
  Any other combination does nothing. -/
  | loseLife (n : Nat) (who : TriggerLifeLossWho := .you)
      (amount : TriggerLifeLossAmount := .fixed)
  /-- Queue reflexive ability `kind` if the Plan was sacrificed this way. -/
  | queueReflexiveIfSacrificed (kind : Nat)
  /-- Queue the divided-damage reflexive. `amount` is the printed number. -/
  | queuePlanDividedDamage (amount : Nat)
  /-- Apply `action` to the target while the source is still on the battlefield.
  A source that already left is silent. -/
  | onTargetWhileSource (action : PermanentAction)
  /-- The enchanted creature becomes a copy of the creature exiled this way. -/
  | enchantedCopiesNoted
  /-- You may play the exiled card until the end of your next turn. -/
  | grantPlayNotedUntilNextTurn
  /-- The tapped creature can't untap while you control the source. -/
  | cantUntapWhileSource
  /-- The tapped creature loses all abilities while the source remains. -/
  | loseAbilitiesWhileSourceRemains
  /-- You win the game. -/
  | winTheGame
  /-- Shuffle the source into its owner's library. -/
  | shuffleSource
  /-- The following surveil returns a card with mana value at most the life
  you gained this turn. -/
  | armSurveilReturnLifeGained
  /-- Resolve a leftover StepLeftover. -/
  | step (e : StepLeftover)
  /-- Resolve a leftover DeathLeftover. -/
  | death (e : DeathLeftover)
  /-- Resolve a leftover ThisAttackLeftover. -/
  | thisAttack (e : ThisAttackLeftover)
  /-- Resolve a leftover EnterOrAttackLeftover. -/
  | enterOrAttack (e : EnterOrAttackLeftover)
  /-- Resolve a leftover WatchLeftover. -/
  | watch (e : WatchLeftover)
  /-- Resolve a leftover YouAttackLeftover. -/
  | youAttacking (e : YouAttackLeftover)
  /-- Resolve a leftover CastLeftover. -/
  | casting (e : CastLeftover)
  /-- Resolve a leftover ResourceLeftover. -/
  | resource (e : ResourceLeftover)
deriving Repr, Inhabited, BEq

namespace TriggerResolution

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
   .sequence [.scry 2, .draw 1]]

/-- Put a +1/+1 counter on the source. Each opponent loses 2 life and you
gain 2 life. Draw a card. -/
def gollumModes : List TriggerResolution :=
  [.onSource (.plusOne 1),
   .sequence [.loseLife 2 (who := .eachOpponent), .gainLife 2],
   .draw 1]

/-- Draw a card, then discard a card. Each opponent loses 2 life.
Destroy the announced token. Each player sacrifices the announced creature,
which is already gone when an earlier mode destroyed it. -/
def upToXModes : List TriggerResolution :=
  [.sequence [.draw 1, .discard 1],
   .loseLife 2 (who := .eachOpponent),
   .onPermanent .destroy,
   .sacrifice .eachPlayer .chosenCreature]

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
  resolution : TriggerResolution := .pump 0 0 .source .greatestPower
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
  | .scry n => { resolution := .scry n }
  | .draw n => { resolution := .draw n }
  | .createTokens kind n tapped => { resolution := .createTokens kind n tapped }
  | .amass n subtype amount attachSource =>
    { resolution := .amass n subtype amount attachSource }
  | .recruit who => { resolution := .recruit who }
  | .dividedDamage amount maxTargets =>
    { targeting := .of .playerOrCreature,
      dividedDamage := some (amount, maxTargets), resolution := .dividedDamage }
  | .gainLife n => { resolution := .gainLife n }
  | .connive who =>
    match who with
    | .source => { resolution := .connive who }
    | .target kind => { targeting := .of kind, resolution := .connive who }
  | .exileUntilLeaves kind =>
    { targeting := .of kind, resolution := .exile .target .untilSourceLeaves }
  | .damageEachOpponent n =>
    { targeting := .of .opponent, resolution := .dealDamage n .eachOpponent }
  | .attachTo kind =>
    { targeting := .of kind, resolution := .attach .source .target }
  | .opponentSacrificesCreature =>
    { targeting := .of .opponent,
      resolution := .sacrifice .targetOpponent .chosenCreature }
  | .onPermanent kind action =>
    { targeting := .of kind, resolution := .onPermanent action }
  | .onSource action =>
    { resolution := .onSource action }
  | .exileTop => { resolution := .exile .top .playUntilNextTurn }
  | .discard n => { resolution := .discard n }
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
      resolution := .mayThen left.resolution right.resolution }
  | .may action =>
    let inner := timing action
    { inner with resolution := .may inner.resolution }
  | .opponentDiscards n who =>
    match who with
    | .each => { resolution := .discard n (who := .each) }
    | .target =>
      { targeting := .of .opponent, resolution := .discard n (who := .target) }
  | .millPlayer n =>
    { targeting := .of .player, resolution := .mill n .target }
  | .investigate => { resolution := .investigate }
  | .pumpCause p t => { resolution := .pump p t .cause }
  | .searchLibrary => { resolution := .searchLibrary (.put .forest) }
  | .searchBasicLandToHand =>
    { resolution := .searchLibrary (.returnToHand .basicLand) }
  | .eachPlayerSacrificesCreature =>
    { resolution := .sacrifice .eachPlayer .chosenCreature }
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
         .gainLife 0 (amount := .forEachOtherCreature)] }
  | .becomePT p t => { resolution := .becomePT p t }
  | .pumpTargetPerPlains =>
    { targeting := .of .creatureYouControl, resolution := .pump 0 0 .target .perPlains }
  | .mayDiscardHandDraw n =>
    { resolution := .mayThen (.discard (what := .hand)) (.draw n) }
  | .pumpByLookedAt => { resolution := .pump 0 0 .source .perLookedAt }
  | .pumpGreatestPower => { resolution := .pump 0 0 .source .greatestPower }
  | .pumpForEachOtherCreature => { resolution := .pump 0 0 .source .perOtherCreature }
  | .damageBlockers n => { resolution := .dealDamage n .blockers }
  | .returnLinkedExile => { resolution := .put .linkedExile }
  | .createThenAttach kind =>
    { resolution := .sequence [.createTokens kind 1 false, .attach .source .created] }
  | .gainLifeSearchBasicOnTop n =>
    { resolution := .sequence [.gainLife n, .searchLibrary (.put .basicLandOnTop)] }
  | .addMana types => { resolution := .addMana types }
  | .createAxe attach =>
    { resolution :=
        .createTokens .treasure 1 false .axe
          (note := if attach then .attachReflexive else .none) }
  | .tapOppOrUntapYours =>
    { resolution := .or [.onPermanent .tap, .onPermanent .untap] }
  | .gainControlOppUntilEot =>
    { targeting := .of .oppCreature, resolution := .gainControlOppUntilEot }
  | .payReturnFromGy =>
    { resolution := .mayThen
        (.pay #[.generic 1, .colored .green, .colored .blue]) (.returnToHand .source .owner) }
  | .targetOpponentLosesLife n =>
    { targeting := .of .opponent, resolution := .loseLife n (who := .targetOpponent) }
  | .drawXDiscard n =>
    { resolution := .sequence
        [.draw 0 (amount := .equalToManaSpent), .discard n (when := .ifManaSpent)] }
  | .ringTempts => { resolution := .ringTempts }
  | .setOtherBasePT =>
    { targeting := .of .anotherCreatureYouControl, allowsZeroTargets := true,
      resolution := .setOtherBasePT }
  | .returnElfGainLife =>
    { targeting := .of .elfInYourGraveyard
      resolution := .sequence
        [.returnToHand .graveyardCard, .gainLife 0 (amount := .equalToTargetPower)] }
  | .damageFromLastKnownPower =>
    { targeting := .of .oppCreature,
      resolution := .dealDamage 0 .permanent .lastKnownPower }
  | .mayPayGenericDraw n plusOne =>
    { resolution :=
        if plusOne then
          .mayThen (.pay #[.generic n]) (.sequence [.onSource (.plusOne 1), .draw 1])
        else
          .mayThen (.pay #[.generic n]) (.draw 1) }
  | .drawThenBottomIfNoLegendary =>
    { resolution := .sequence [.draw 1, .«if» .noLegendaryCreature .putFromHandOnBottom] }
  | .removeHopeDrawSac =>
    { resolution := .sequence
        [.removeCounters .hope .source, .«if» .removedHope (.draw 1), .«if» .noHopeOnSource (.sequence [.sacrifice .you .source, .gainLife 4])] }
  | .tapHumansDraw =>
    { resolution := .sequence
        [.may (.tap .humans), .draw 0 (amount := .forEachTappedHuman)] }
  | .destroyOppArtifactsEnchantmentsGainLife =>
    { resolution := .sequence
        [.destroy .oppArtifactsEnchantments (note := .countDestroyed),
         .gainLife 0 (amount := .forEachDestroyedThisWay)] }
  | .damageEqualSubtypeToEachOpponent subtype =>
    { resolution := .dealDamage 0 .eachOpponent (.subtypeCount subtype) }
  | .damageEqualTreasures =>
    { targeting := .of .playerOrCreature,
      resolution := .dealDamage 0 .target (.subtypeCount "Treasure") }
  | .dealDamageDestroyIfSubtype n subtype =>
    { targeting := .of .playerOrCreature,
      resolution := .sequence
        [.dealDamage n .target .fixed .markedPermanent,
         .«if» (.dealtDamageToSubtype subtype) (.destroy .permanentDealtDamage)] }
  | .attachEquipmentToCreature =>
    { targeting := .of .equipmentYouControlThenCreatureYouControl,
      allowsZeroTargets := true, resolution := .attach .target .optionalCreature }
  | .defenderSacsLeastPower =>
    { resolution := .sacrifice .defender .leastPower }
  | .returnOtherPlusOne =>
    { targeting := .of (.filtered { noun := "up to one other target permanent you control"
                                    controller := .you, another := true })
      allowsZeroTargets := true
      resolution := .sequence
        [.returnToHand .permanent .owner .returnedPermanent, .«if» .returnedPermanent (.onSource (.plusOne 1))] }
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
        [.pump p t (.othersOfSubtypes subtypes), .pump oppP oppT .opponentsCreatures] }
  | .wolfPlusOneOrTreasure =>
    { resolution := .or
        [.onPermanent (.plusOne 1), .createTokens .treasure 1 false] }
  | .trampleCounterBecomeBear =>
    { targeting := .of .creatureYouControl, allowsZeroTargets := true,
      resolution := .sequence
        [.putCounters (.ofKind .trample) .permanent, .becomeBear, .«if» (.bearsAtLeast 3) (.draw 2)] }
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
    { resolution := .sequence [.putCounters (.ofKind .quest) .source, .«if» (.questAtLeast 6) (.sequence [.sacrifice .you (.source .movedAsSacrificed), .searchLibrary (.put .dragon)])] }
  | .treasuresPerChosenType =>
    { resolution := .createTokens .treasure 0 false (qty := .chosenCreatureType) }
  | .revealUntilCreature =>
    { resolution := .revealLibrary .untilCreature
        (.ifElse .revealedManaValueAtMostLands (.put .revealed) (.returnToHand .revealed)) }
  | .attackSacPlusOneEqualPower =>
    { resolution := .mayThen (.objectCost .anotherCreature)
        (.putCounters .plusOneSacrificedPower .source) }
  | .lootLandEntersTapped =>
    { resolution := .sequence
        [.draw 1, .discard 1, .put .discardedLand (how := .tapped)] }
  | .millThatManyLost =>
    { resolution := .mill 0 .thatPlayer .thatManyLost }
  | .drawPerFatGraveyard =>
    { resolution := .draw 0 (amount := .perFatGraveyard) }
  | .maySacDrawTreasure =>
    { resolution := .mayThen (.objectCost .anotherCreatureOrArtifact)
        (.sequence [.draw 1, .createTokens .treasure 1 false]) }
  | .castInstantSorceryFromHand =>
    { resolution := .mayCast .hand .twiceLegendaryWizards .withoutPaying }
  | .castInstantSorceryMvAtMost =>
    { resolution := .mayCast .hand .lastKnown .withoutPaying }
  | .millThenCopy =>
    { resolution := .sequence
        [.mill 2 .eachOpponent (note := .opponentsMilled),
         .«if» .opponentsMilled .reflexiveCopyMilled] }
  | .pumpTargetBySourcePower =>
    { targeting := .of .anotherCreatureYouControl,
      resolution := .pump 0 0 .target .equalSourcePower }
  | .createAlienPerInvasion =>
    { resolution := .sequence
        [.createTokens .treasure 1 false .alien (note := .invasion),
         .putCounters .plusOneNoted .createdToken,
         .putCounters (.ofKind .invasion) .source] }
  | .mayPutArtifactAttachEquipment =>
    { resolution := .sequence
        [.may (.put .artifactFromHand (note := .forAttach)),
         .«if» .putArtifactIsEquipment (.attach .putArtifact .notedHost)] }
  | .cascade => { resolution := .cascade }
  | .belladonnaTokenReward =>
    { resolution := .sequence [
        .noteResolveThisTurn 3,
        .«if» (.nthResolve 1) (.gainLife 1),
        .«if» (.nthResolve 2) (.draw 1),
        .«if» (.nthResolve 3) (.putCounters (.ofKind .plusOnePlusOne) .youControl)] }
  | .bolgMaySacrifice => { resolution := .may (.sacrifice .you .another) }
  | .bolgDealSacrificedPower =>
    { targeting := .of .anotherCreature,
      resolution := .sequence
        [.dealDamage 0 .permanent .lastKnownPower .excess,
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
        [.dealDamage 1 .target .fixed .markedPermanent, .amass 1 "Orc"] }
  | .untapAttackersExtraCombat _n =>
    { resolution := .sequence [.untapAttackingCreatures, .additionalCombatPhase] }
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
         .«if» .youControlledDestroyed (.draw 1)] }
  | .gollumMode =>
    { resolution := .chooseModes TriggeredAbility.TriggerResolution.gollumModes
        .oneUnused }
  | .discardHandDrawDamageIfStory =>
    { resolution := .sequence
        [.may (.discard (what := .hand)), .draw 0 (amount := .discardedHandCount),
         .«if» .enduringStoryNoted (.dealDamage 0 .eachOpponent .discardedHand)] }
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
        .onPermanent (.pump 3 0),
        .onPermanent (.grantKeywords Keyword.firstStrike)]) }
  | .honePerOppAttach =>
    { targeting := .of (.multi #[
        { noun := "target opponent", zone := .player, controller := .opponent },
        { noun := "target creature you control", controller := .you, types := #[.creature] }
      ] #[1])
      resolution := .sequence
        [.putCounters .honePerOpponent .source, .attach .source .creatureTarget] }
  | .damageTargetOpponent n =>
    { targeting := .of .opponent, resolution := .dealDamage n .targetOpponent }
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
        [.putCounters (.ofKind .influence) .source, .scry 2,
         .may (.draw 1 (who := .opponentHasYou))] }
  | .treasuresEqualLastKnown =>
    { resolution := .createTokens .treasure 0 false (qty := .lastKnown) }
  | .protectionEverything =>
    { resolution := .grant .protectionEverything .youIfCast }
  | .loseLifePerBurden => { resolution := .loseLife 0 (amount := .perBurden) }
  | .revealSaga =>
    { resolution := .revealLibrary .untilSaga (.put .revealed) }
  | .sacDamagersRingTempts =>
    { resolution := .sequence [.sacrifice .eachOpponent .combatDamager, .ringTempts] }
  | .chapter _n e =>
    { resolution := .chapter e }
  | .drawIfAttackedOrEnteredSubtype subtype =>
    { resolution := .«if» (.attackedOrEntered subtype) (.draw 1) }
  | .othersOfSubtypeGetEqualSourceToughness subtype =>
    { resolution := .pump 0 0 (.othersOfSubtype subtype) .equalSourceToughness }
  | .scryAndPlan n =>
    { resolution := .sequence [.putCounters (.ofKind .plan) .source, .scry n] }
  | .lootAndPlan =>
    { resolution := .sequence
        [.putCounters (.ofKind .plan) .source, .draw 1, .discard 1] }
  | .createVillainAndPlan =>
    { resolution := .sequence
        [.putCounters (.ofKind .plan) .source, .createTokens .villain21menace 1 false] }
  | .drainAndPlan n =>
    { resolution := .sequence
        [.putCounters (.ofKind .plan) .source, .loseLife n (who := .eachOpponent), .gainLife n] }
  | .drawLoseLifeAndPlan =>
    { resolution := .sequence
        [.putCounters (.ofKind .plan) .source, .draw 1, .loseLife 1] }
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
        [.sacrifice .you .plan, .draw 1, .putCounters (.ofKind .plusOnePlusOne) .youControl] }
  | .planFinishReturnInstants =>
    { resolution := .sequence
        [.sacrifice .you .plan .forReflexive, .queueReflexiveIfSacrificed 11] }
  | .planFinishControlOpponent =>
    { resolution := .sequence
        [.sacrifice .you .plan .forReflexive, .queueReflexiveIfSacrificed 4] }
  | .planFinishExileTopCast =>
    { resolution := .sequence
        [.sacrifice .you .plan .forReflexive, .queueReflexiveIfSacrificed 5] }
  | .planFinishCreateRobots n =>
    { resolution := .sequence
        [.sacrifice .you .plan, .createTokens .robotVillain22 n false] }
  | .planFinishDividedDamage n =>
    { resolution := .sequence
        [.sacrifice .you .plan .forReflexive, .queuePlanDividedDamage n] }
  | .planFinishIndestructibleOnTarget =>
    { resolution := .sequence
        [.sacrifice .you .plan .forReflexive, .queueReflexiveIfSacrificed 3] }
  | .surveil n => { resolution := .surveil n }
  | .empowerJace n => { resolution := .empowerJace n }
  | .prepareSource .ifNotPrepared =>
    { events := #[.yourUpkeep], resolution := .prepareSource .ifNotPrepared }
  | .prepareSource .ifThreeCreaturesDied =>
    { events := #[.eachEndStep], resolution := .prepareSource .ifThreeCreaturesDied }
  | .drawIfRemovedTwoLoyalty =>
    { resolution := .«if» (.removedLoyaltyAtLeast 2) (.draw 1) }
  | .loyaltyOnSource =>
    { resolution := .putCounters (.ofKind .loyalty) .source }
  | .grantThenCounterByType k =>
    { targeting := .of .permanentYouControl,
      resolution := .sequence
        [.onPermanent (.grantKeywords k),
         .«if» .targetIsCreature (.onPermanent (.plusOne 1)),
         .«if» .targetIsPlaneswalker (.putCounters (.ofKind .loyalty) .permanent)] }
  | .destroyOppPermanentIfSixLands =>
    { targeting := .of .oppPermanent,
      resolution := .«if» (.landsAtLeast 6) (.sequence [
        .onPermanent .destroy,
        .createTokens .treasure 1 false (who := .targetController)]) }
  | .pumpOrCounterIfScried =>
    { events := #[.yourBeginCombat], targeting := .of .anotherCreatureYouControl,
      resolution := .ifElse .scriedOrSurveilledThisTurn
        (.onPermanent (.plusOne 1)) (.onPermanent (.pump 1 1)) }
  | .sacrificeSourceIfNoPlaneswalker =>
    { events := #[.eachEndStep],
      resolution := .«if» .noPlaneswalker (.sacrifice .you (.source .controllerSacrifices)) }
  | .creaturesYouControlGet p t => { resolution := .pump p t .creaturesYouControl }
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
        [.draw 2, .«if» .libraryEmpty .winTheGame, .«if» .libraryNotEmpty .shuffleSource] }
  | .surveilReturnIfGainedLife =>
    { events := #[.yourEndStep],
      resolution := .sequence [.armSurveilReturnLifeGained, .surveil 1] }
  | .pumpIfFiveOtherForests =>
    { targeting := .of .creatureYouControl,
      resolution := .«if» (.otherForestsAtLeast 5) (.onPermanent (.pump 3 3)) }
  | .onEnchanted action => { resolution := .onEnchanted action }
  | .attachThen followup =>
    { targeting := .of .creatureYouControl,
      resolution := .sequence [.attach .source .target, .onTargetWhileSource followup] }
  | .exileOtherCopyEnchanted =>
    { targeting := .of .creature, allowsZeroTargets := true,
      resolution := .sequence
        [.exile .target .untilSourceLeaves .copyAndHost, .enchantedCopiesNoted] }
  | .exileUntilNextEndStep =>
    { targeting := .of .creatureYouControl, allowsZeroTargets := true,
      resolution := .exile .target .nextEndStep }
  | .tapOrUntapNonland =>
    { targeting := .of .nonland,
      resolution := .or [.onPermanent .tap, .onPermanent .untap] }
  | .createFoodOrTreasure =>
    { resolution := .or
        [.createTokens .food 1 false, .createTokens .treasure 1 false] }
  | .villainIfGyElseMill =>
    { resolution := .ifElse (.creatureCardsInGraveyardAtLeast 2)
        (.createTokens .villain21menace 1 true) (.mill 2) }
  | .drawMayPutLandTapped =>
    { resolution := .sequence
        [.draw 1, .may (.put .landFromHand (how := .tapped))] }
  | .drawGainLifeIfAnotherHero =>
    { resolution := .sequence [.draw 1, .«if» .anotherHero (.gainLife 2)] }
  | .plusOneOrTwoIfAnotherHero =>
    { targeting := .of .creature,
      resolution := .ifElse (.targetIsAnotherSubtype "Hero")
        (.onPermanent (.plusOne 2)) (.onPermanent (.plusOne 1)) }
  | .maySacArtifactOrDiscardDraw =>
    { resolution := .mayThen (.objectCost .artifactOrDiscard) (.draw 1) }
  | .enter (.destroy kind) =>
    { events := #[.entering], targeting := .of kind, resolution := .onPermanent .destroy }
  | .enter (.dealDamageUpToOne n) =>
    { events := #[.entering], targeting := .of .creature, allowsZeroTargets := true,
      resolution := .onPermanent (.dealDamage n) }
  | .enter .fightUpToOne =>
    { events := #[.entering], targeting := .of .anotherCreature, allowsZeroTargets := true,
      resolution := .fight }
  | .enter .returnNonlandNontoken =>
    { events := #[.entering], targeting := .of .nonlandNontoken, allowsZeroTargets := true,
      resolution := .returnToHand .permanent .owner .returnedPermanent }
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
      resolution := .sequence [.onPermanent .tap, .cantUntapWhileSource] }
  | .enter .maySacAnotherThenDestroyOppNonland =>
    { events := #[.entering],
      resolution := .mayThen (.objectCost .anotherCreature) (.queueReflexive (.modeled 7)) }
  | .enter .maySacOrDiscardNonlandThenDamage =>
    { events := #[.entering],
      resolution := .mayThen (.objectCost .artifactOrDiscardNonland)
        (.queueReflexive (.damageAny 2)) }
  | .enter .revealHandExileUntilLeaves =>
    { events := #[.entering], targeting := .of .opponent, allowsZeroTargets := true,
      resolution := .revealFromHand .hand (.exile .target .untilSourceLeaves) }
  | .enter .plusOnesOrReturnArtEnch =>
    { events := #[.entering], targeting := .of .creature, allowsZeroTargets := true,
      resolution := .or
        [.onPermanent (.plusOne 1), .returnToHand .graveyardCard] }
  | .enter .chooseUpToXModes =>
    { events := #[.entering], targeting := .of .opponent, allowsZeroTargets := true,
      resolution := .chooseModes TriggeredAbility.TriggerResolution.upToXModes
        .alreadyChosen }
  | .enter .mayTapThenGrantIndestructible =>
    { events := #[.entering],
      resolution := .mayThen (.onSource .tap) (.queueReflexive (.modeled 0)) }
  | .enter .tapLoseAbilitiesWhileSource =>
    { events := #[.entering], targeting := .of .creature, allowsZeroTargets := true,
      resolution := .sequence
        [.tap .targetIfPresent, .loseAbilitiesWhileSourceRemains] }
  | .enter .revealDiscardFromHand =>
    { events := #[.entering], targeting := .of .player,
      resolution := .revealFromHand .onePlusCreatureCards
        (.discard 1 (who := .target)) }
  | .enter .createRedwing =>
    { events := #[.entering], resolution := .createTokens .treasure 1 false .redwing }
  | .step .enchantedControllerDraws =>
    { events := #[.enchantedControllerUpkeep], resolution := .step .enchantedControllerDraws }
  | .step .drawToTen =>
    { events := #[.yourEndStep], resolution := .step .drawToTen }
  | .step .copyAbsorbingMan =>
    { events := #[.yourFirstMain]
      targeting := .of (.filtered {
        noun := "up to one target artifact, non-Aura enchantment, or land"
        types := #[.artifact, .enchantment, .land]
        nonAura := true })
      allowsZeroTargets := true, maxTargets := 1
      resolution := .step .copyAbsorbingMan }
  | .step .hydeChoose =>
    { events := #[.yourUpkeep], resolution := .step .hydeChoose }
  | .step .copyTaskmaster =>
    { events := #[.yourFirstMain], targeting := .of .creatureOrGyCreatureCard,
      allowsZeroTargets := true, maxTargets := 1
      resolution := .step .copyTaskmaster }
  | .step .harnessedFlicker =>
    { events := #[.yourEndStep]
      targeting := .of (.filtered {
        noun := "up to one other target nonland permanent you control"
        nonland := true, controller := .you, another := true })
      allowsZeroTargets := true, maxTargets := 1
      resolution := .step .harnessedFlicker }
  | .death .hellcatReturn =>
    { events := #[.dying], resolution := .death .hellcatReturn }
  | .death .villainReturnAsHero =>
    { events := #[.villainYouControlDies], resolution := .death .villainReturnAsHero }
  | .death .attackingReturnHand =>
    { events := #[.attackingCreatureYouControlDies], resolution := .death .attackingReturnHand }
  | .death .deathtouchOppSac =>
    { events := #[.creatureYouControlDies], resolution := .death .deathtouchOppSac }
  | .thisAttack .mayPayPlusOne =>
    { events := #[.attacking], resolution := .thisAttack .mayPayPlusOne }
  | .thisAttack .payReturnAttacking =>
    { events := #[.attacking], resolution := .thisAttack .payReturnAttacking }
  | .thisAttack .ifArtifactEnteredDraw =>
    { events := #[.attacking], resolution := .thisAttack .ifArtifactEnteredDraw }
  | .thisAttack .blinkNontoken =>
    { events := #[.attacking]
      targeting := .of (.filtered {
        noun := "up to one target nontoken artifact or creature"
        types := #[.artifact, .creature], nontoken := true })
      allowsZeroTargets := true, maxTargets := 1
      resolution := .thisAttack .blinkNontoken }
  | .thisAttack .equippedDrain =>
    { events := #[.attacking], resolution := .thisAttack .equippedDrain }
  | .thisAttack .drawIfPower4 =>
    { events := #[.attacking], resolution := .thisAttack .drawIfPower4 }
  | .thisAttack .attacksAlonePlus2Indestructible =>
    { events := #[.attacking], resolution := .thisAttack .attacksAlonePlus2Indestructible }
  | .enterOrAttack .copyKeywords =>
    { events := #[.entering, .attacking], targeting := .of .anotherCreature,
      resolution := .enterOrAttack .copyKeywords }
  | .enterOrAttack .createSquirrel =>
    { events := #[.entering, .attacking], resolution := .enterOrAttack .createSquirrel }
  | .watch .combatDamageExileUntilNonland =>
    { events := #[.dealsCombatDamageToPlayer], resolution := .watch .combatDamageExileUntilNonland }
  | .watch .attacksAloneDrain =>
    { events := #[.creatureYouControlAttacksAlone], targeting := .of .opponent,
      resolution := .watch .attacksAloneDrain }
  | .watch .attacksAloneFirstStrikeMenace =>
    { events := #[.creatureYouControlAttacksAlone], resolution := .watch .attacksAloneFirstStrikeMenace }
  | .watch .firstTapUntap =>
    { events := #[.creatureYouControlTapped], resolution := .watch .firstTapUntap }
  | .watch .sheHulkRedirectOnce =>
    { events := #[.creatureYouControlDealtDamage], targeting := .of .playerOrCreature,
      resolution := .watch .sheHulkRedirectOnce }
  | .watch .speedballTargeted =>
    { events := #[.spellTargetsSource], resolution := .watch .speedballTargeted }
  | .watch .anyPlayerSecondDraw =>
    { events := #[.anyPlayerDrawsSecond], resolution := .watch .anyPlayerSecondDraw }
  | .watch .youTargetDrawOnce =>
    { events := #[.youTargetSomething], onceEachTurn := true, resolution := .watch .youTargetDrawOnce }
  | .watch .villainOrArtifactDamage =>
    { events := #[.anotherVillainOrArtifactEnters], targeting := .of .opponent,
      resolution := .watch .villainOrArtifactDamage }
  | .watch .villainConniveOnce =>
    { events := #[.anotherVillainEnters], optionalOnceEachTurn := true,
      resolution := .watch .villainConniveOnce }
  | .watch .villainPlusOneDamageOnce =>
    { events := #[.anotherVillainEnters], onceEachTurn := true,
      resolution := .watch .villainPlusOneDamageOnce }
  | .watch .villainAttachEquipment =>
    { events := #[.anotherVillainEnters]
      targeting := .of .upToOneEquipmentThenCreatureYouControl
      resolution := .watch .villainAttachEquipment }
  | .watch .villainPlusOneLifelink =>
    { events := #[.anotherVillainEnters], resolution := .watch .villainPlusOneLifelink }
  | .watch .hulklingCompare =>
    { events := #[.anotherCreatureYouControlEnters], resolution := .watch .hulklingCompare }
  | .watch .justiceBounce =>
    { events := #[.anotherNonlandReturned], resolution := .watch .justiceBounce }
  | .watch .nontokenHeroModal =>
    { events := #[.anotherNontokenHeroEnters], resolution := .watch .nontokenHeroModal }
  | .watch .ultronCopy =>
    { events := #[.anotherNontokenArtifactEnters], resolution := .watch .ultronCopy }
  | .watch .enchantedAttachEquipment =>
    { events := #[.enchantedAttacksOrBlocks], targeting := .of .equipmentYouControl
      allowsZeroTargets := true, maxTargets := 1000, resolution := .watch .enchantedAttachEquipment }
  | .watch .equippedAttacksAloneUntapScry =>
    { events := #[.equippedAttacksAlone], resolution := .watch .equippedAttacksAloneUntapScry }
  | .watch .equippedAttacksTap =>
    { events := #[.equippedAttacks], targeting := .of .defendingPlayerCreature,
      resolution := .watch .equippedAttacksTap }
  | .watch .equippedTappedDamage =>
    { events := #[.equippedBecomesTapped], resolution := .watch .equippedTappedDamage }
  | .watch .heroesDamagePlusTwo =>
    { events := #[.heroesDealDamageToPlayer], resolution := .watch .heroesDamagePlusTwo }
  | .watch .merfolkAttackDraw =>
    { events := #[.merfolkAttackPlayer], resolution := .watch .merfolkAttackDraw }
  | .watch .tokensEnterMayDraw =>
    { events := #[.tokenYouControlEnters], resolution := .watch .tokensEnterMayDraw }
  | .watch .hawkeyeModes =>
    { events := #[.sourceBecomesTapped], allowsZeroTargets := true,
      resolution := .watch .hawkeyeModes }
  | .watch .redHulk =>
    { events := #[.sourceDealtDamage], resolution := .watch .redHulk }
  | .watch .hulk =>
    { events := #[.sourceDealtDamage], resolution := .watch .hulk }
  | .youAttacking .pay2LifeToughness =>
    { events := #[.youAttack], resolution := .youAttacking .pay2LifeToughness }
  | .youAttacking .exileTopHeroPump =>
    { events := #[.youAttack], resolution := .youAttacking .exileTopHeroPump }
  | .youAttacking .lookSixCast =>
    { events := #[.youAttack], resolution := .youAttacking .lookSixCast }
  | .casting .villainToken =>
    { events := #[.youCastVillain], resolution := .casting .villainToken }
  | .casting .merfolkFromBlue =>
    { events := #[.youCastNoncreature], resolution := .casting .merfolkFromBlue }
  | .casting .mayPayHasteUnblockable =>
    { events := #[.youCastNoncreature], resolution := .casting .mayPayHasteUnblockable }
  | .casting .plusOneEachOther =>
    { events := #[.youCastNoncreature], resolution := .casting .plusOneEachOther }
  | .casting .exileFlicker =>
    { events := #[.youCastNoncreature]
      targeting := .of (.filtered {
        noun := "another target nonland, nontoken permanent"
        nonland := true, nontoken := true, another := true })
      resolution := .casting .exileFlicker }
  | .casting .visionModes =>
    { events := #[.youCastNoncreature], resolution := .casting .visionModes }
  | .casting .damageEqualMv =>
    { events := #[.youCastNoncreature], targeting := .of .playerOrCreature,
      resolution := .casting .damageEqualMv }
  | .casting .drawPowerEqualHand =>
    { events := #[.youCastTargetingCreatureYouControl], resolution := .casting .drawPowerEqualHand }
  | .casting .plusOneThis =>
    { events := #[.youCastTargetingCreatureYouControl], resolution := .casting .plusOneThis }
  | .casting .plusOneScry =>
    { events := #[.youCastTargetingCreatureYouControl], resolution := .casting .plusOneScry }
  | .casting .ironFistTap =>
    { events := #[.youCastTargetingCreatureYouControl], resolution := .casting .ironFistTap }
  | .casting .targetsGainFlying =>
    { events := #[.youCastTargetingCreature], resolution := .casting .targetsGainFlying }
  | .casting .copyIfArtifactOrLand =>
    { events := #[.youCastInstantSorceryTargetingArtifactOrLand], resolution := .casting .copyIfArtifactOrLand }
  | .casting .tapCreatureOrLand =>
    { events := #[.youCastNoncreature],
      targeting := .of (.filtered {
        noun := "target creature or land",
        types := #[.creature, .land] }),
      resolution := .casting .tapCreatureOrLand }
  | .resource .discardExilePlay =>
    { events := #[.youDiscard], resolution := .resource .discardExilePlay }
  | .resource .drawIfAnotherHeroDamage =>
    { events := #[.youDraw], targeting := .of .opponent,
      resolution := .resource .drawIfAnotherHeroDamage }
  | .resource .secondDrawBecome66 =>
    { events := #[.youDrawSecondCard], resolution := .resource .secondDrawBecome66 }
  | .resource .secondDrawPlusOneTarget =>
    { events := #[.youDrawSecondCard], targeting := .of .creature,
      resolution := .resource .secondDrawPlusOneTarget }
  | .resource .secondDrawDrain =>
    { events := #[.youDrawSecondCard], resolution := .resource .secondDrawDrain }
  | .resource .gainLifePlusOnes =>
    { events := #[.youGainLife], targeting := .of .creatureYouControl,
      allowsZeroTargets := true, resolution := .resource .gainLifePlusOnes }
  | .resource .plusOneCreateInsectOnce =>
    { events := #[.youPutPlusOne], onceEachTurn := true,
      resolution := .resource .plusOneCreateInsectOnce }
  | .resource .plusOneOnThisOnce =>
    { events := #[.youPutPlusOne], onceEachTurn := true,
      resolution := .resource .plusOneOnThisOnce }
  | .resource .plusOneOnHeroesCreateWall =>
    { events := #[.youPutPlusOne], resolution := .resource .plusOneOnHeroesCreateWall }

end SharedTrigger

#guard !(SharedTrigger.timing (.watch .sheHulkRedirectOnce)).onceEachTurn
#guard (SharedTrigger.timing (.watch .sheHulkRedirectOnce)).targeting.kind ==
  .playerOrCreature
#guard (SharedTrigger.timing (.thisAttack .blinkNontoken)).allowsZeroTargets &&
  (SharedTrigger.timing (.thisAttack .blinkNontoken)).maxTargets == 1
#guard (SharedTrigger.timing (.enterOrAttack .copyKeywords)).targeting.kind ==
  .anotherCreature
#guard (SharedTrigger.timing (.watch .villainConniveOnce)).optionalOnceEachTurn
#guard (SharedTrigger.timing (.enterOrAttack .copyKeywords)).events ==
  #[TriggerEvent.entering, TriggerEvent.attacking]
#guard (SharedTrigger.timing (.death .hellcatReturn)).resolution ==
  TriggeredAbility.TriggerResolution.death .hellcatReturn

end Mtg.Engine
