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

/-- How `TriggerResolution.sacrificeSource` moves the source to the graveyard. -/
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
  /-- An earlier step milled a card from an opponent. -/
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
deriving Repr, Inhabited, BEq

/-- Objects chosen for `TriggerResolution.objectCost`, the optional action of
`TriggerResolution.mayThen`. -/
inductive TriggerObjectCost where
  /-- Sacrifice another creature. Its power is noted for
  `plusOneEqualSacrificedPower`. -/
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

/-- What a triggered ability does when it resolves (CR 608). Grouped so
`Game.applyTriggeredAbility` matches resolution shapes instead of every
constructor: scry, +1/+1 on the source, and divided damage each cover
multiple printed abilities. Permanent-target counters and pumps, and source
pumps, share `PermanentAction` with spells and activated abilities. -/
inductive TriggerResolution where
  /-- Pump the source by the greatest power among creatures you control. -/
  | pumpGreatestPower
  /-- Set another creature's base P/T to this creature's. -/
  | setOtherBasePT
  /-- Deal `amount` damage to each creature blocking the source. -/
  | damageBlockers (amount : Nat)
  /-- Scry `n`. -/
  | scry (n : Nat)
  /-- Draw `n` cards. -/
  | draw (n : Nat)
  /-- Search your library, as `how` says.
  A Forest onto the battlefield is `.searchLibrary`.
  A basic land into your hand is `.searchLibrary .basicLandToHand`.
  You may put a basic land on top is `.searchLibrary .basicLandOnTop`. -/
  | searchLibrary (how : TriggerLibrarySearch := .forestToBattlefield)
  /-- Discard `n` cards. One card is `.discard`.
  Inside `mayThen`, one card is optional: declining skips the conditional. -/
  | discard (n : Nat := 1)
  /-- You may resolve `optional`. If you do, resolve `conditional`.
  Declining, or being unable to perform `optional`, skips `conditional`.
  You may discard a card to draw `n` is `.mayThen (.discard 1) (.draw n)`.
  `SharedTrigger.mayTo a b` resolves as `.mayThen` of each step's resolution.
  You may pay `{n}` to draw is `.mayThen (.pay #[.generic n]) (.draw 1)`.
  Paying `{n}` to put a +1/+1 counter on the source and draw is
  `.mayThen (.pay #[.generic n]) (.sequence [.onSource (.plusOne 1), .draw 1])`.
  You may sacrifice another creature for +1/+1 counters equal to its power is
  `.mayThen (.objectCost .anotherCreature) .plusOneEqualSacrificedPower`.
  You may pay `{1}{G}{U}` to return this from the graveyard is
  `.mayThen (.pay #[.generic 1, .colored .green, .colored .blue]) .returnSourceToHand`.
  You may sacrifice another creature or artifact to draw and create a Treasure is
  `.mayThen (.objectCost .anotherCreatureOrArtifact) (.sequence [.draw 1, .createTokens .treasure 1 false])`.
  You may discard your hand to draw `n` is `.mayThen .discardHand (.draw n)`.
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
  /-- Put +1/+1 counters on the source equal to the power noted by sacrificing
  another creature. -/
  | plusOneEqualSacrificedPower
  /-- Return the source from its owner's graveyard to their hand. -/
  | returnSourceToHand
  /-- Put reflexive ability `followup` on the stack (“When you do”). -/
  | queueReflexive (followup : TriggerReflexive)
/-- The controller may resolve `action`. Declining skips it.
A choice that already includes decline is that choice, so the player
is not asked twice. You may draw X cards, where X is the mana spent to
cast the triggering spell, then discard two, is
`.may (.sequence [.drawEqualToManaSpent, .discardIfManaSpent 2])`.
You may tap any number of untapped Humans is `.may .tapHumans`.
You may sacrifice another creature is `.may .sacrificeAnother`.
You may put an artifact from your hand onto the battlefield is
`.may .putArtifactFromHand`.
You may discard your hand is `.may .discardHand`.
The targeted opponent may have you draw a card is
`.may .opponentHasYouDraw`. Declining that offer mills and that player
loses life; it does not skip.
You may put a land card from your hand onto the battlefield tapped is
`.may .putLandFromHandTapped`.
`SharedTrigger.may a` resolves as `.may` of `a`'s resolution. -/
| may (action : TriggerResolution)
  /-- Target opponent sacrifices a creature of their choice. -/
  | opponentSacrificesCreature
  /-- Affect a still-legal permanent target. -/
  | onPermanent (action : PermanentAction)
  /-- Deal previously divided damage to the announced targets. -/
  | dividedDamage
  /-- Deal last-known power as damage to the announced creature. -/
  | damageFromLastKnownPower
  /-- Apply each resolution in order. An illegal required target skips every
  step (CR 608.2b). Return a graveyard card, then gain life equal to its
  power, is `.sequence [.returnCreatureFromGyToHand, .gainLifeEqualToTargetPower]`.
  Draw, then bottom a card if you control no legendary, is
  `.sequence [.draw 1, .«if» .noLegendaryCreature .putFromHandOnBottom]`.
  Remove a hope counter, draw if one was removed, then sacrifice and gain
  life if none remain, is
  `.sequence [.removeHopeCounter, .«if» .removedHope (.draw 1), .«if» .noHopeOnSource (.sequence [.sacrificeSource .isSacrificed, .gainLife 4])]`.
  A step that asks a player to choose pauses the later steps until that
  choice finishes; they are still part of this resolution. Tap any number
  of Humans, then draw that many, is
  `.sequence [.may .tapHumans, .drawForEachTappedHuman]`.
  Create one token, then attach the source to it, is
  `.sequence [.createTokens kind 1 false, .attachSourceToCreated]`.
  Gain life, then you may search a basic land onto the top, is
  `.sequence [.gainLife n, .searchLibrary .basicLandOnTop]`.
  Destroy opponents' artifacts and enchantments, then gain 1 life for each
  one actually destroyed, is
  `.sequence [.destroyOppArtifactsEnchantments, .gainLifeForEachDestroyedThisWay]`.
  Put a +1/+1 counter on each other creature you control, then gain 1 life
  for each other creature you control, is
  `.sequence [.plusOneEachOther, .gainLifeForEachOtherCreature]`.
  Deal `n` damage to the target, then destroy it if that damage marked a
  permanent of this subtype, is
  `.sequence [.dealDamageToTarget n, .«if» (.dealtDamageToSubtype subtype) .destroyPermanentDealtDamage]`.
  Return another permanent to its owner's hand, then put a +1/+1 counter on
  the source if one was actually returned, is
  `.sequence [.returnToOwnerHand, .«if» .returnedPermanent (.onSource (.plusOne 1))]`.
  Other creatures you control of these subtypes get +P/+T, and creatures
  your opponents control get +oppP/+oppT, is
  `.sequence [.othersOfSubtypesGet subtypes p t, .opponentsCreaturesGet oppP oppT]`.
  Gain 1 life, draw, or put a +1/+1 counter on each creature you control
  when this is the first, second, or third resolve this turn (Belladonna
  Took), is
  `.sequence [.noteResolveThisTurn 3, .«if» (.nthResolve 1) (.gainLife 1), .«if» (.nthResolve 2) (.draw 1), .«if» (.nthResolve 3) (.plusOneEachYouControl)]`.
  Deal the sacrificed creature's power, then amass Goblins for the excess
  (Bolg), is
  `.sequence [.dealLastKnownPowerNoteExcess, .amassGoblinsNotedExcess]`.
  Put a plan counter, then scry, is
  `.sequence [.planCounterOnSource, .scry n]`.
  Put a trample counter on the target, then make it a Bear, is
  `.sequence [.trampleCounterOnTarget, .becomeBear]`.
  Draw, discard, and a land discarded this way enters tapped, is
  `.sequence [.draw 1, .discard 1, .discardedLandEntersTapped]`.
  Put an influence counter, scry 2, then offer the opponent's choice
  (Palantír of Orthanc), is
  `.sequence [.influenceCounterOnSource, .scry 2, .may .opponentHasYouDraw]`.
  Grant keywords, then a +1/+1 counter if the target is a creature and a
  loyalty counter if it is a planeswalker, is
  `.sequence [.onPermanent (.grantKeywords k), .«if» .targetIsCreature (.onPermanent (.plusOne 1)), .«if» .targetIsPlaneswalker .loyaltyOnTarget]`.
  The target gets +3/+0 and gains first strike until end of turn, is
  `.sequence [.onPermanent (.pump 3 0), .onPermanent (.grantKeywords Keyword.firstStrike)]`.
  Destroy the target, then its controller creates a Treasure, is
  `.sequence [.onPermanent .destroy, .targetControllerCreatesTreasure]`.
  You may put an artifact from your hand onto the battlefield, then attach
  it to the source if it is Equipment, is
  `.sequence [.may .putArtifactFromHand, .«if» .putArtifactIsEquipment .attachPutArtifact]`. -/
  | sequence (rs : List TriggerResolution)
  /-- Gain life equal to the targeted card's power. Inside `sequence`, the
  amount is that power when the sequence starts, before an earlier step
  moves the card. -/
  | gainLifeEqualToTargetPower
  /-- Deal `amount` damage to each opponent. -/
  | damageEachOpponent (amount : Nat)
  /-- Pump the source +1/+1 per card looked at while scrying. -/
  | pumpByLookedAt
  /-- Affect the trigger's source if it is still on the battlefield. -/
  | onSource (action : PermanentAction)
  /-- You gain `n` life (CR 118.2). -/
  | gainLife (n : Nat)
  /-- Each player sacrifices a creature of their choice. -/
  | eachPlayerSacrificesCreature
  /-- An opponent discards `n` cards. Each opponent discards one is
  `.opponentDiscards`. The announced opponent is `.opponentDiscards n .target`. -/
  | opponentDiscards (n : Nat := 1) (who : OpponentDiscard := .each)
  /-- Pump the source +1/+1 for each other creature you control. -/
  | pumpForEachOtherCreature
  /-- Put a card from your hand on the bottom of your library.
  An empty hand skips the choice. -/
  | putFromHandOnBottom
  /-- Exile the targeted permanent. Link it if the source is still in play. -/
  | exileTarget
  /-- Exile the targeted permanent until the source leaves the battlefield. -/
  | exileUntilLeaves
  /-- Return cards exiled by the source. -/
  | returnLinkedExile
  /-- Remove a hope counter from the source. -/
  | removeHopeCounter
  /-- Sacrifice the source, as `how` says. -/
  | sacrificeSource (how : SacrificeSourceHow := .isSacrificed)
  /-- Tap any number of untapped Humans you control.
  Choosing none taps nothing. Optional as `.may .tapHumans`. -/
  | tapHumans
  /-- Draw a card for each Human tapped by an earlier step. -/
  | drawForEachTappedHuman
  /-- Destroy all artifacts and enchantments opponents control.
  Only permanents that actually leave are counted for the next step. -/
  | destroyOppArtifactsEnchantments
  /-- Gain 1 life for each permanent destroyed by an earlier step. -/
  | gainLifeForEachDestroyedThisWay
  /-- Recruit. “recruit” is `.recruit`. “you recruit” is `.recruit .you`. -/
  | recruit (who : RecruitSubject := .recruit)
  /-- Exile the top card; you may play it until the end of your next turn. -/
  | exileTop
  /-- Put a +1/+1 counter on permanents you control.
  Each creature is `.plusOneEachYouControl`.
  Each permanent of a subtype is `.plusOneEachYouControl (.subtype s)`.
  One counter, or two with the city's blessing, is
  `.plusOneEachYouControl .citysBlessing`. -/
  | plusOneEachYouControl (which : YouControlPlusOne := .eachCreature)
  /-- Amass `subtype` `n`, as `amount` says. Attach the source when
  `attachSource` is true. -/
  | amassGoblins (n : Nat) (subtype : String := "Goblin")
      (amount : AmassAmount := .fixed) (attachSource : Bool := false)
  /-- Create `n` tokens of this kind. -/
  | createTokens (kind : TokenKind) (n : Nat) (tapped : Bool)
  /-- Attach the source to the token created by the previous step. -/
  | attachSourceToCreated
  /-- Attach the source to the targeted permanent. -/
  | attachSourceToTarget
  /-- Put a +1/+1 counter on each other creature you control. -/
  | plusOneEachOther
  /-- Gain 1 life for each other creature you control. -/
  | gainLifeForEachOtherCreature
  /-- Deal damage equal to the count of this subtype you control to each
  opponent. -/
  | damageEqualSubtypeToEachOpponent (subtype : String)
  /-- Deal damage equal to Treasures you control to the target. -/
  | damageEqualTreasures
  /-- Deal `n` damage to the target. A permanent actually marked by that
  damage is remembered for the next step. -/
  | dealDamageToTarget (n : Nat)
  /-- Destroy the permanent an earlier step dealt damage to. -/
  | destroyPermanentDealtDamage
  /-- Attach the first target (Equipment) to the second (creature). -/
  | attachEquipmentToCreature
  /-- Add these mana types. -/
  | addMana (types : Array ManaType)
  /-- Defending player sacrifices a least-power creature. -/
  | defenderSacsLeastPower
  /-- Create an Axe Equipment token.
  Attaching it to a creature you control is `.createAxe (attach := true)`. -/
  | createAxe (attach : Bool := false)
  /-- Set the source's base P/T. -/
  | becomePT (power toughness : Int)
  /-- Look at the top `n` and reveal a listed type. -/
  | lookAtTopRevealTypes (n : Nat) (types : Array String)
  /-- Create tapped Treasures equal to opposing artifacts. -/
  | createTappedTreasuresEqualOppArtifacts
  /-- Gain control of the target until end of turn; untap; haste. -/
  | gainControlOppUntilEot
  /-- Other creatures you control of these subtypes get +P/+T until end of turn.
  The source is not included. -/
  | othersOfSubtypesGet (subtypes : Array String) (power toughness : Int)
  /-- Creatures your opponents control get +P/+T until end of turn. -/
  | opponentsCreaturesGet (power toughness : Int)
  /-- Put a nonland permanent card with mana value at most `mv` from a
  graveyard onto the battlefield. -/
  | putNonlandMvAtMostFromGy (mv : Nat)
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
  `.«if» .putArtifactIsEquipment .attachPutArtifact`. -/
  | «if» (cond : TriggerIf) (thenDo : TriggerResolution)
  /-- Resolve `whenTrue` when `cond` holds, and `whenFalse` otherwise.
  A tapped Villain when your graveyard has two creature cards, and milling
  two otherwise, is
  `.ifElse (.creatureCardsInGraveyardAtLeast 2) (.createTokens .villain21menace 1 true) (.mill 2)`.
  Two +1/+1 counters when the target is another Hero, and one otherwise, is
  `.ifElse (.targetIsAnotherSubtype "Hero") (.onPermanent (.plusOne 2)) (.onPermanent (.plusOne 1))`.
  A +1/+1 counter when you have scried or surveilled, and +1/+1 until end of
  turn otherwise, is
  `.ifElse .scriedOrSurveilledThisTurn (.onPermanent (.plusOne 1)) (.onPermanent (.pump 1 1))`. -/
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
  `.or [.onPermanent (.plusOne 1), .returnCreatureFromGyToHand]`. -/
  | or (rs : List TriggerResolution)
  /-- Sacrifice another creature you control. When you do, Bolg's reflexive
  trigger deals that creature's power as damage.
  Optional as `.may .sacrificeAnother`. -/
  | sacrificeAnother
  /-- Create a Treasure for each artifact the damaged player controls. -/
  | createTreasuresEqualDamagedPlayerArtifacts
  /-- Create Bird Soldier tokens equal to last-known count. -/
  | eaglesCreateBirds
  /-- Apply an unused Alliance mode, or do nothing if all were chosen. -/
  | allianceMode
  /-- Apply an unused Gollum mode, or do nothing if all were chosen. -/
  | gollumMode
  /-- Return a creature card from your graveyard to your hand. -/
  | returnCreatureFromGyToHand
  /-- You may cast an artifact, instant, or sorcery from your graveyard. -/
  | castFromGyArtifactInstantSorcery
  /-- Exile up to one opposing nonland per opponent until this leaves. -/
  | exileOppNonlandEachUntilLeaves
  /-- +1/+1 counters equal to the last-known mana value. -/
  | plusOneEqualLastKnownMv
  /-- Equipped attacking creatures gain double strike. -/
  | equippedAttackersGainDoubleStrike
  /-- Reveal the top `n`; put a random creature onto the battlefield. -/
  | revealTopPutRandomCreature (n : Nat)
  /-- Target player mills `n`. -/
  | millPlayer (n : Nat)
  /-- The controller mills `n`. -/
  | mill (n : Nat)
  /-- Treasures equal to permanents of a chosen type. -/
  | treasuresPerChosenType
  /-- Reveal until a creature; put it onto the battlefield or into hand. -/
  | revealUntilCreature
  /-- Deal 2 to target opponent. -/
  | damageTargetOpponent (n : Nat)
  /-- Each player who lost life mills that much. -/
  | millThatManyLost
  /-- Draw per graveyard with seven or more cards. -/
  | drawPerFatGraveyard
  /-- Create two nonlegendary token copies of the source. -/
  | copySelfNonlegendary
  /-- Target opponent loses 1 life. -/
  | targetOpponentLosesLife (n : Nat)
  /-- Return the source as an artifact. -/
  | returnAsArtifact
  /-- You may cast an instant or sorcery from hand without paying. -/
  | castInstantSorceryFromHand
  /-- You may cast an instant or sorcery of MV at most last-known power. -/
  | castInstantSorceryMvAtMost
  /-- The Ring tempts you. -/
  | ringTempts
  /-- Create Treasures equal to last-known damage. -/
  | treasuresEqualLastKnown
  /-- You gain protection from everything until your next turn. -/
  | protectionEverything
  /-- Lose 1 life per burden counter. -/
  | loseLifePerBurden
  /-- Reveal until a Saga and put it onto the battlefield. -/
  | revealSaga
  /-- Resolve a printed Saga chapter. -/
  | chapter (effect : ChapterResolution)
  /-- Target creature you control gets +1/+1 per Plains you control. -/
  | pumpTargetPerPlains
  /-- Investigate (create a Clue). -/
  | investigate
  /-- Connive (CR 701.48). The source is `.connive`. A target is
  `.connive (.target kind)`. -/
  | connive (who : ConniveSubject := .source)
  /-- Pump the creature that caused the trigger. -/
  | pumpCause (power toughness : Int)
  /-- Other permanents you control of this subtype get +X/+X, X = source toughness. -/
  | othersOfSubtypeGetEqualSourceToughness (subtype : String)
  /-- Apply `action` to the creature this Aura enchants. -/
  | onEnchanted (action : PermanentAction)
  /-- Exile the targeted creature; return it at the next end step. -/
  | exileUntilNextEndStep
  /-- Another target creature gets +X/+0, X = source power. -/
  | pumpTargetBySourcePower
  /-- Put an artifact card from your hand onto the battlefield.
  The permanent, and the creature it may attach to, are remembered for the
  next step. An empty hand skips the choice.
  Optional as `.may .putArtifactFromHand`. -/
  | putArtifactFromHand
  /-- Attach the artifact an earlier step put from hand to that creature. -/
  | attachPutArtifact
  /-- This fights the targeted creature. -/
  | fightUpToOne
  /-- Return the targeted permanent to its owner's hand.
  Whether a permanent was actually returned is recorded for the next step. -/
  | returnToOwnerHand
  /-- Create Zabu. -/
  | createZabu
  /-- Target opponent creates The Void. -/
  | oppCreatesTheVoid
  /-- Return the targeted GY permanent card to your hand. -/
  | returnGyPermanentThisTurn
  /-- Reveal the opponent's hand; exile a card or creature until this leaves. -/
  | revealHandExileUntilLeaves
  /-- Resolve chosen “up to X” modes in printed order. -/
  | chooseUpToXModes
  /-- Target player reveals cards from hand; you choose one to discard. -/
  | revealDiscardFromHand
  /-- Create Redwing. -/
  | createRedwing
  /-- Surveil `n` (CR 701.25). -/
  | surveil (n : Nat)
  /-- Empower Jace `n` (Reality Fracture). -/
  | empowerJace (n : Nat)
  /-- The source becomes prepared.
  If it isn't prepared is `.prepareSource`.
  If three or more creatures died this turn is
  `.prepareSource .ifThreeCreaturesDied`. -/
  | prepareSource (when : PrepareWhen := .ifNotPrepared)
  /-- Put a loyalty counter on the source. -/
  | loyaltyOnSource
  /-- The target's controller creates a Treasure token.
  After `.onPermanent .destroy`, the permanent may already have left; its
  controller is the one it had on the battlefield. -/
  | targetControllerCreatesTreasure
  /-- Creatures you control get +P/+T until end of turn. -/
  | creaturesYouControlGet (power toughness : Int)
  /-- Put the source's last-known counters on the target. -/
  | putSourceCountersOnTarget
  /-- Put a charge counter on the source. -/
  | chargeCounterOnSource
  /-- Add {G} for each charge counter on the source. -/
  | addGreenPerChargeCounter
  /-- Deal the sacrificed creature's last-known power and note excess damage. -/
  | dealLastKnownPowerNoteExcess
  /-- Amass Goblins equal to the excess noted by the previous step. -/
  | amassGoblinsNotedExcess
  /-- Mark tokens from the previous step attacking. -/
  | markRecentTokensAttacking
  /-- Untap each attacking creature. -/
  | untapAttackingCreatures
  /-- There is an additional combat phase after this one. -/
  | additionalCombatPhase
  /-- Destroy the targeted creature, if any, and note its controller and power.
  No target means no player amasses. -/
  | destroyNotedForAmass
  /-- Amass Goblins for the controller noted by the previous step. -/
  | amassNotedController
  /-- Discard your hand and note how many cards were discarded.
  Optional as `.may .discardHand`. Declining leaves the note empty so the
  following draw and damage steps do nothing. -/
  | discardHand
  /-- Draw cards equal to the hand discarded by the previous step. -/
  | drawDiscardedHandCount
  /-- Deal damage to each opponent equal to the hand discarded by an earlier step. -/
  | damageEachOpponentDiscardedHand
  /-- Put a trample counter on the target. -/
  | trampleCounterOnTarget
  /-- The target becomes a Bear in addition to its other types. -/
  | becomeBear
  /-- Mill `n` and remember the cards milled. -/
  | millNote (n : Nat)
  /-- Put milled cards of this subtype into your hand. -/
  | returnMilledSubtype (subtype : String)
  /-- Tap the creature enchanted by the source. -/
  | tapEnchanted
  /-- Remove all counters from the creature enchanted by the source. -/
  | removeCountersFromEnchanted
  /-- Put a quest counter on the source. -/
  | questCounterOnSource
  /-- Search your hand and/or library for a Dragon and put it onto the battlefield. -/
  | searchDragonFromHandOrLibrary
  /-- Put the land discarded by the previous step onto the battlefield tapped. -/
  | discardedLandEntersTapped
  /-- Put hone counters on the source equal to the opponent's creatures. -/
  | honeCountersPerOpponent
  /-- Attach the source to the creature target. -/
  | attachToCreatureTarget
  /-- You may attach any number of Equipment you control to the target. -/
  | offerAttachAnyEquipment
  /-- The creature that received Equipment deals damage equal to its power
  to up to one target creature. -/
  | reflexiveFightHost
  /-- Draw X cards, where X is the mana spent to cast the triggering spell. -/
  | drawEqualToManaSpent
  /-- Discard `n` cards when mana was spent to cast the triggering spell. -/
  | discardIfManaSpent (n : Nat)
  /-- Exile the targeted lands and remember them. -/
  | exileLandsNote
  /-- Return the lands exiled this way to the battlefield tapped. -/
  | returnNotedLandsTapped
  /-- Exile cards from the top of the damaged player's library until an
  instant or sorcery. -/
  | grimaExileUntil
  /-- You may cast the instant or sorcery exiled by the previous step. -/
  | grimaMayCast
  /-- Put an influence counter on the source when the target is still legal.
  An illegal target skips the later scry and the opponent's choice. -/
  | influenceCounterOnSource
  /-- The targeted opponent may have you draw a card.
  Declining mills X cards, where X is the influence counters on the source,
  and that player loses life equal to their mana value.
  Optional as `.may .opponentHasYouDraw`. An earlier step must have recorded
  the offer. -/
  | opponentHasYouDraw
  /-- Each opponent mills `n`. The next step sees whether any card was milled. -/
  | opponentsMillNote (n : Nat)
  /-- Queue the reflexive exile-and-copy of a milled spell. -/
  | reflexiveCopyMilled
  /-- Each opponent sacrifices a creature that dealt combat damage to you. -/
  | sacDamagingCreatures
  /-- Put a plan counter on the source. Later steps do not run if it left. -/
  | planCounterOnSource
  /-- Each opponent loses `n` life. -/
  | eachOpponentLosesLife (n : Nat)
  /-- You lose `n` life. -/
  | loseLife (n : Nat)
  /-- Put a +1/+1 counter on the target. You put that counter. -/
  | plusOneOnTargetByYou
  /-- Sacrifice the Plan if it is still on the battlefield. -/
  | sacrificePlan
  /-- Sacrifice the Plan. Note whether the sacrifice happened. -/
  | sacrificePlanForReflexive
  /-- Queue reflexive ability `kind` if the Plan was sacrificed this way. -/
  | queueReflexiveIfSacrificed (kind : Nat)
  /-- Queue the divided-damage reflexive. `amount` is the printed number. -/
  | queuePlanDividedDamage (amount : Nat)
  /-- Apply `action` to the target while the source is still on the battlefield.
  A source that already left is silent. -/
  | onTargetWhileSource (action : PermanentAction)
  /-- Exile the targeted creature until the source leaves, and remember it. -/
  | exileOtherUntilLeavesNote
  /-- The enchanted creature becomes a copy of the creature exiled this way. -/
  | enchantedCopiesNoted
  /-- Put a land card from your hand onto the battlefield tapped.
  Optional as `.may .putLandFromHandTapped`. -/
  | putLandFromHandTapped
  /-- Put a loyalty counter on the target. -/
  | loyaltyOnTarget
  /-- Create an Alien token and remember how many invasion counters to put. -/
  | createAlienToken
  /-- Put the noted number of +1/+1 counters on the Alien token. -/
  | plusOneOnAlienNoted
  /-- Put an invasion counter on the source. -/
  | invasionCounterOnSource
  /-- Create a Sturdy Shield token. -/
  | createSturdyShieldToken
  /-- Attach the token created by the previous step to the source. -/
  | attachCreatedToSource
  /-- Exile the targeted graveyard card. -/
  | exileGyCardNote
  /-- You may play the exiled card until the end of your next turn. -/
  | grantPlayNotedUntilNextTurn
  /-- The tapped creature can't untap while you control the source. -/
  | cantUntapWhileSource
  /-- Tap the target if it is still on the battlefield. -/
  | tapTargetIfPresent
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
  resolution : TriggerResolution := .pumpGreatestPower
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
  | .amassGoblins n subtype amount attachSource =>
    { resolution := .amassGoblins n subtype amount attachSource }
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
    { targeting := .of kind, resolution := .exileUntilLeaves }
  | .damageEachOpponent n =>
    { targeting := .of .opponent, resolution := .damageEachOpponent n }
  | .attachTo kind =>
    { targeting := .of kind, resolution := .attachSourceToTarget }
  | .opponentSacrificesCreature =>
    { targeting := .of .opponent, resolution := .opponentSacrificesCreature }
  | .onPermanent kind action =>
    { targeting := .of kind, resolution := .onPermanent action }
  | .onSource action =>
    { resolution := .onSource action }
  | .exileTop => { resolution := .exileTop }
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
    | .each => { resolution := .opponentDiscards n who }
    | .target =>
      { targeting := .of .opponent, resolution := .opponentDiscards n who }
  | .millPlayer n =>
    { targeting := .of .player, resolution := .millPlayer n }
  | .investigate => { resolution := .investigate }
  | .pumpCause p t => { resolution := .pumpCause p t }
  | .searchLibrary how => { resolution := .searchLibrary how }
  | .eachPlayerSacrificesCreature => { resolution := .eachPlayerSacrificesCreature }
  | .exileTarget kind =>
    { targeting := .of kind, resolution := .exileTarget }
  | .returnCreatureFromGyToHand =>
    { targeting := .of .creatureCardInYourGraveyard,
      resolution := .returnCreatureFromGyToHand }
  | .plusOneEachYouControl which => { resolution := .plusOneEachYouControl which }
  | .honeEachEquipment => { resolution := .honeEachEquipment }
  | .plusOneEachOtherGainLife =>
    { resolution := .sequence
        [.plusOneEachOther, .gainLifeForEachOtherCreature] }
  | .becomePT p t => { resolution := .becomePT p t }
  | .pumpTargetPerPlains =>
    { targeting := .of .creatureYouControl, resolution := .pumpTargetPerPlains }
  | .mayDiscardHandDraw n =>
    { resolution := .mayThen .discardHand (.draw n) }
  | .pumpByLookedAt => { resolution := .pumpByLookedAt }
  | .pumpGreatestPower => { resolution := .pumpGreatestPower }
  | .pumpForEachOtherCreature => { resolution := .pumpForEachOtherCreature }
  | .damageBlockers n => { resolution := .damageBlockers n }
  | .returnLinkedExile => { resolution := .returnLinkedExile }
  | .createThenAttach kind =>
    { resolution := .sequence [.createTokens kind 1 false, .attachSourceToCreated] }
  | .gainLifeSearchBasicOnTop n =>
    { resolution := .sequence [.gainLife n, .searchLibrary .basicLandOnTop] }
  | .addMana types => { resolution := .addMana types }
  | .createAxe attach => { resolution := .createAxe attach }
  | .tapOppOrUntapYours =>
    { resolution := .or [.onPermanent .tap, .onPermanent .untap] }
  | .gainControlOppUntilEot =>
    { targeting := .of .oppCreature, resolution := .gainControlOppUntilEot }
  | .payReturnFromGy =>
    { resolution := .mayThen
        (.pay #[.generic 1, .colored .green, .colored .blue]) .returnSourceToHand }
  | .targetOpponentLosesLife n =>
    { targeting := .of .opponent, resolution := .targetOpponentLosesLife n }
  | .drawXDiscard n =>
    { resolution := .sequence [.drawEqualToManaSpent, .discardIfManaSpent n] }
  | .ringTempts => { resolution := .ringTempts }
  | .setOtherBasePT =>
    { targeting := .of .anotherCreatureYouControl, allowsZeroTargets := true,
      resolution := .setOtherBasePT }
  | .returnElfGainLife =>
    { targeting := .of .elfInYourGraveyard
      resolution := .sequence
        [.returnCreatureFromGyToHand, .gainLifeEqualToTargetPower] }
  | .damageFromLastKnownPower =>
    { targeting := .of .oppCreature, resolution := .damageFromLastKnownPower }
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
        [.removeHopeCounter, .«if» .removedHope (.draw 1), .«if» .noHopeOnSource (.sequence [.sacrificeSource .isSacrificed, .gainLife 4])] }
  | .tapHumansDraw =>
    { resolution := .sequence [.may .tapHumans, .drawForEachTappedHuman] }
  | .destroyOppArtifactsEnchantmentsGainLife =>
    { resolution := .sequence
        [.destroyOppArtifactsEnchantments, .gainLifeForEachDestroyedThisWay] }
  | .damageEqualSubtypeToEachOpponent subtype =>
    { resolution := .damageEqualSubtypeToEachOpponent subtype }
  | .damageEqualTreasures =>
    { targeting := .of .playerOrCreature, resolution := .damageEqualTreasures }
  | .dealDamageDestroyIfSubtype n subtype =>
    { targeting := .of .playerOrCreature,
      resolution := .sequence
        [.dealDamageToTarget n, .«if» (.dealtDamageToSubtype subtype) .destroyPermanentDealtDamage] }
  | .attachEquipmentToCreature =>
    { targeting := .of .equipmentYouControlThenCreatureYouControl,
      allowsZeroTargets := true, resolution := .attachEquipmentToCreature }
  | .defenderSacsLeastPower => { resolution := .defenderSacsLeastPower }
  | .returnOtherPlusOne =>
    { targeting := .of (.filtered { noun := "up to one other target permanent you control"
                                    controller := .you, another := true })
      allowsZeroTargets := true
      resolution := .sequence
        [.returnToOwnerHand, .«if» .returnedPermanent (.onSource (.plusOne 1))] }
  | .lookAtTopRevealTypes n types =>
    { resolution := .lookAtTopRevealTypes n types }
  | .createTappedTreasuresEqualOppArtifacts =>
    { resolution := .createTappedTreasuresEqualOppArtifacts }
  | .putNonlandMvAtMostFromGy mv =>
    { targeting := .of (.filtered
        { noun := s!"up to one target nonland permanent card with mana value {mv} or less from a graveyard"
          zone := .anyGraveyard, permanentCard := true, nonland := true, mvAtMost := some mv })
      allowsZeroTargets := true, resolution := .putNonlandMvAtMostFromGy mv }
  | .othersGetAndOppsGet subtypes p t oppP oppT =>
    { resolution := .sequence
        [.othersOfSubtypesGet subtypes p t, .opponentsCreaturesGet oppP oppT] }
  | .wolfPlusOneOrTreasure =>
    { resolution := .or
        [.onPermanent (.plusOne 1), .createTokens .treasure 1 false] }
  | .trampleCounterBecomeBear =>
    { targeting := .of .creatureYouControl, allowsZeroTargets := true,
      resolution := .sequence
        [.trampleCounterOnTarget, .becomeBear, .«if» (.bearsAtLeast 3) (.draw 2)] }
  | .millThenSubtypeToHand n subtype =>
    { resolution := .sequence [.millNote n, .returnMilledSubtype subtype] }
  | .exileOppNonlandEachUntilLeaves =>
    { targeting := .of (.filtered
        { noun := "for each opponent, up to one target nonland permanent that player controls"
          nonland := true, controller := .eachOpponent })
      allowsZeroTargets := true
      resolution := .exileOppNonlandEachUntilLeaves }
  | .plusOneEqualLastKnownMv =>
    { targeting := .of .creatureYouControl, resolution := .plusOneEqualLastKnownMv }
  | .mountainQuestDragon =>
    { resolution := .sequence [.questCounterOnSource, .«if» (.questAtLeast 6) (.sequence [.sacrificeSource .movedAsSacrificed, .searchDragonFromHandOrLibrary])] }
  | .treasuresPerChosenType => { resolution := .treasuresPerChosenType }
  | .revealUntilCreature => { resolution := .revealUntilCreature }
  | .attackSacPlusOneEqualPower =>
    { resolution := .mayThen (.objectCost .anotherCreature) .plusOneEqualSacrificedPower }
  | .lootLandEntersTapped =>
    { resolution := .sequence [.draw 1, .discard 1, .discardedLandEntersTapped] }
  | .millThatManyLost => { resolution := .millThatManyLost }
  | .drawPerFatGraveyard => { resolution := .drawPerFatGraveyard }
  | .maySacDrawTreasure =>
    { resolution := .mayThen (.objectCost .anotherCreatureOrArtifact)
        (.sequence [.draw 1, .createTokens .treasure 1 false]) }
  | .castInstantSorceryFromHand => { resolution := .castInstantSorceryFromHand }
  | .castInstantSorceryMvAtMost => { resolution := .castInstantSorceryMvAtMost }
  | .millThenCopy =>
    { resolution := .sequence [.opponentsMillNote 2, .«if» .opponentsMilled .reflexiveCopyMilled] }
  | .pumpTargetBySourcePower =>
    { targeting := .of .anotherCreatureYouControl,
      resolution := .pumpTargetBySourcePower }
  | .createAlienPerInvasion =>
    { resolution := .sequence
        [.createAlienToken, .plusOneOnAlienNoted, .invasionCounterOnSource] }
  | .mayPutArtifactAttachEquipment =>
    { resolution := .sequence
        [.may .putArtifactFromHand, .«if» .putArtifactIsEquipment .attachPutArtifact] }
  | .cascade => { resolution := .cascade }
  | .belladonnaTokenReward =>
    { resolution := .sequence [
        .noteResolveThisTurn 3,
        .«if» (.nthResolve 1) (.gainLife 1),
        .«if» (.nthResolve 2) (.draw 1),
        .«if» (.nthResolve 3) (.plusOneEachYouControl)] }
  | .bolgMaySacrifice => { resolution := .may .sacrificeAnother }
  | .bolgDealSacrificedPower =>
    { targeting := .of .anotherCreature,
      resolution := .sequence [.dealLastKnownPowerNoteExcess, .amassGoblinsNotedExcess] }
  | .createSpiritsForEquipped =>
    { resolution := .sequence
        [.createTokens .spirit 2 true, .«if» .equippedLegendaryYouControl .markRecentTokensAttacking] }
  | .createTreasuresEqualDamagedPlayerArtifacts =>
    { resolution := .createTreasuresEqualDamagedPlayerArtifacts }
  | .deal1ThenAmassOrcs =>
    { targeting := .of .playerOrCreature,
      resolution := .sequence [.dealDamageToTarget 1, .amassGoblins 1 "Orc"] }
  | .untapAttackersExtraCombat _n =>
    { resolution := .sequence [.untapAttackingCreatures, .additionalCombatPhase] }
  | .eaglesCreateBirds => { resolution := .eaglesCreateBirds }
  | .allianceMode => { resolution := .allianceMode }
  | .destroyOtherAmassControllerPower =>
    { targeting := .of .anotherCreature, allowsZeroTargets := true,
      resolution := .sequence
        [.destroyNotedForAmass, .amassNotedController, .«if» .youControlledDestroyed (.draw 1)] }
  | .gollumMode => { resolution := .gollumMode }
  | .discardHandDrawDamageIfStory =>
    { resolution := .sequence
        [.may .discardHand, .drawDiscardedHandCount,
         .«if» .enduringStoryNoted .damageEachOpponentDiscardedHand] }
  | .castFromGyArtifactInstantSorcery =>
    { resolution := .castFromGyArtifactInstantSorcery }
  | .equippedAttackersGainDoubleStrike =>
    { resolution := .equippedAttackersGainDoubleStrike }
  | .tapEnchantedRemoveCounters =>
    { resolution := .sequence [.tapEnchanted, .removeCountersFromEnchanted] }
  | .revealTopPutRandomCreature n =>
    { resolution := .revealTopPutRandomCreature n }
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
      resolution := .sequence [.honeCountersPerOpponent, .attachToCreatureTarget] }
  | .damageTargetOpponent n =>
    { targeting := .of .opponent, resolution := .damageTargetOpponent n }
  | .copySelfNonlegendary => { resolution := .copySelfNonlegendary }
  | .attachEquipmentThenFight =>
    { targeting := .of .creatureYouControl,
      resolution := .sequence [.offerAttachAnyEquipment, .«if» .equipmentAttached .reflexiveFightHost] }
  | .returnAsArtifact => { resolution := .returnAsArtifact }
  | .exileLandsThenReturnTapped =>
    { targeting := .of (.filtered {
        noun := "up to three target lands you control"
        types := #[.land], controller := .you })
      allowsZeroTargets := true, maxTargets := 3
      resolution := .sequence [.exileLandsNote, .returnNotedLandsTapped] }
  | .grimaImpulse =>
    { resolution := .sequence [.grimaExileUntil, .grimaMayCast] }
  | .palantir =>
    { targeting := .of .opponent,
      resolution := .sequence
        [.influenceCounterOnSource, .scry 2, .may .opponentHasYouDraw] }
  | .treasuresEqualLastKnown => { resolution := .treasuresEqualLastKnown }
  | .protectionEverything => { resolution := .protectionEverything }
  | .loseLifePerBurden => { resolution := .loseLifePerBurden }
  | .revealSaga => { resolution := .revealSaga }
  | .sacDamagersRingTempts =>
    { resolution := .sequence [.sacDamagingCreatures, .ringTempts] }
  | .chapter _n e =>
    { resolution := .chapter e }
  | .drawIfAttackedOrEnteredSubtype subtype =>
    { resolution := .«if» (.attackedOrEntered subtype) (.draw 1) }
  | .othersOfSubtypeGetEqualSourceToughness subtype =>
    { resolution := .othersOfSubtypeGetEqualSourceToughness subtype }
  | .scryAndPlan n =>
    { resolution := .sequence [.planCounterOnSource, .scry n] }
  | .lootAndPlan =>
    { resolution := .sequence [.planCounterOnSource, .draw 1, .discard 1] }
  | .createVillainAndPlan =>
    { resolution := .sequence
        [.planCounterOnSource, .createTokens .villain21menace 1 false] }
  | .drainAndPlan n =>
    { resolution := .sequence
        [.planCounterOnSource, .eachOpponentLosesLife n, .gainLife n] }
  | .drawLoseLifeAndPlan =>
    { resolution := .sequence [.planCounterOnSource, .draw 1, .loseLife 1] }
  | .treasureTappedAndPlan =>
    { resolution := .sequence
        [.planCounterOnSource, .createTokens .treasure 1 true] }
  | .plusOneOnTargetAndPlan =>
    { targeting := .of .creatureYouControl,
      resolution := .sequence [.planCounterOnSource, .plusOneOnTargetByYou] }
  | .planFinishDrawPlusOneEach =>
    { resolution := .sequence
        [.sacrificePlan, .draw 1, .plusOneEachYouControl] }
  | .planFinishReturnInstants =>
    { resolution := .sequence
        [.sacrificePlanForReflexive, .queueReflexiveIfSacrificed 11] }
  | .planFinishControlOpponent =>
    { resolution := .sequence
        [.sacrificePlanForReflexive, .queueReflexiveIfSacrificed 4] }
  | .planFinishExileTopCast =>
    { resolution := .sequence
        [.sacrificePlanForReflexive, .queueReflexiveIfSacrificed 5] }
  | .planFinishCreateRobots n =>
    { resolution := .sequence
        [.sacrificePlan, .createTokens .robotVillain22 n false] }
  | .planFinishDividedDamage n =>
    { resolution := .sequence
        [.sacrificePlanForReflexive, .queuePlanDividedDamage n] }
  | .planFinishIndestructibleOnTarget =>
    { resolution := .sequence
        [.sacrificePlanForReflexive, .queueReflexiveIfSacrificed 3] }
  | .surveil n => { resolution := .surveil n }
  | .empowerJace n => { resolution := .empowerJace n }
  | .prepareSource .ifNotPrepared =>
    { events := #[.yourUpkeep], resolution := .prepareSource .ifNotPrepared }
  | .prepareSource .ifThreeCreaturesDied =>
    { events := #[.eachEndStep], resolution := .prepareSource .ifThreeCreaturesDied }
  | .drawIfRemovedTwoLoyalty =>
    { resolution := .«if» (.removedLoyaltyAtLeast 2) (.draw 1) }
  | .loyaltyOnSource => { resolution := .loyaltyOnSource }
  | .grantThenCounterByType k =>
    { targeting := .of .permanentYouControl,
      resolution := .sequence
        [.onPermanent (.grantKeywords k),
         .«if» .targetIsCreature (.onPermanent (.plusOne 1)),
         .«if» .targetIsPlaneswalker .loyaltyOnTarget] }
  | .destroyOppPermanentIfSixLands =>
    { targeting := .of .oppPermanent,
      resolution := .«if» (.landsAtLeast 6) (.sequence [
        .onPermanent .destroy,
        .targetControllerCreatesTreasure]) }
  | .pumpOrCounterIfScried =>
    { events := #[.yourBeginCombat], targeting := .of .anotherCreatureYouControl,
      resolution := .ifElse .scriedOrSurveilledThisTurn
        (.onPermanent (.plusOne 1)) (.onPermanent (.pump 1 1)) }
  | .sacrificeSourceIfNoPlaneswalker =>
    { events := #[.eachEndStep],
      resolution := .«if» .noPlaneswalker (.sacrificeSource .controllerSacrifices) }
  | .creaturesYouControlGet p t => { resolution := .creaturesYouControlGet p t }
  | .putSourceCountersOnTarget =>
    { targeting := .of .creatureYouControl, allowsZeroTargets := true,
      resolution := .putSourceCountersOnTarget }
  | .chargeCounterOnSource => { resolution := .chargeCounterOnSource }
  | .addGreenPerChargeCounter =>
    { events := #[.yourFirstMain], resolution := .addGreenPerChargeCounter }
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
      resolution := .sequence [.attachSourceToTarget, .onTargetWhileSource followup] }
  | .exileOtherCopyEnchanted =>
    { targeting := .of .creature, allowsZeroTargets := true,
      resolution := .sequence [.exileOtherUntilLeavesNote, .enchantedCopiesNoted] }
  | .exileUntilNextEndStep =>
    { targeting := .of .creatureYouControl, allowsZeroTargets := true,
      resolution := .exileUntilNextEndStep }
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
    { resolution := .sequence [.draw 1, .may .putLandFromHandTapped] }
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
      resolution := .fightUpToOne }
  | .enter .returnNonlandNontoken =>
    { events := #[.entering], targeting := .of .nonlandNontoken, allowsZeroTargets := true,
      resolution := .returnToOwnerHand }
  | .enter .createZabu =>
    { events := #[.entering], resolution := .createZabu }
  | .enter .oppCreatesTheVoid =>
    { events := #[.entering], targeting := .of .opponent, resolution := .oppCreatesTheVoid }
  | .enter .createSturdyShieldAttach =>
    { events := #[.entering],
      resolution := .sequence [.createSturdyShieldToken, .attachCreatedToSource] }
  | .enter .exileGyPlayUntilNextTurn =>
    { events := #[.entering], targeting := .of .equipmentInstantOrSorceryInYourGraveyard,
      resolution := .sequence [.exileGyCardNote, .grantPlayNotedUntilNextTurn] }
  | .enter .returnGyPermanentThisTurn =>
    { events := #[.entering], targeting := .of .permanentCardInYourGraveyard,
      resolution := .returnGyPermanentThisTurn }
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
      resolution := .revealHandExileUntilLeaves }
  | .enter .plusOnesOrReturnArtEnch =>
    { events := #[.entering], targeting := .of .creature, allowsZeroTargets := true,
      resolution := .or
        [.onPermanent (.plusOne 1), .returnCreatureFromGyToHand] }
  | .enter .chooseUpToXModes =>
    { events := #[.entering], targeting := .of .opponent, allowsZeroTargets := true,
      resolution := .chooseUpToXModes }
  | .enter .mayTapThenGrantIndestructible =>
    { events := #[.entering],
      resolution := .mayThen (.onSource .tap) (.queueReflexive (.modeled 0)) }
  | .enter .tapLoseAbilitiesWhileSource =>
    { events := #[.entering], targeting := .of .creature, allowsZeroTargets := true,
      resolution := .sequence
        [.tapTargetIfPresent, .loseAbilitiesWhileSourceRemains] }
  | .enter .revealDiscardFromHand =>
    { events := #[.entering], targeting := .of .player, resolution := .revealDiscardFromHand }
  | .enter .createRedwing =>
    { events := #[.entering], resolution := .createRedwing }
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
