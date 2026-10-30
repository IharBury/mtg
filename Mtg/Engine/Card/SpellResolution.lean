import Mtg.Engine.Card.Counter
import Mtg.Engine.Card.FrcEffect
import Mtg.Engine.Card.PermanentAction
import Mtg.Engine.Card.Targeting
import Mtg.Engine.Card.Token
import Mtg.Engine.Mana
import Mtg.Engine.TypeLine

/-!
# Resolutions (CR 608 / 603)

One vocabulary for spells, triggered abilities, and activated abilities.
`Resolution` is that inductive. `SpellResolution` and
`TriggeredAbility.TriggerResolution` are abbreviations for it.
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

/-- Which creatures an until-end-of-turn pump affects. -/
inductive CreaturePumpScope where
  /-- Every creature. -/
  | all
  /-- Creatures the targeted player controls. -/
  | ofTargetPlayer
  /-- Creatures the controller of the resolving spell controls. -/
  | youControl
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which milled cards `SpellResolution.millThenPut` puts into hand. -/
inductive MilledToHand where
  /-- Up to one card of type `a` or `b`. A lone eligible card is taken. -/
  | oneOf (a b : CardType)
  /-- Up to `max` cards of type `ty`. The player may take fewer. -/
  | upTo (max : Nat) (ty : CardType)
  /-- Every milled card of type `a` or `b`. -/
  | allOf (a b : CardType)
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which spells `SpellResolution.spellsCostLessThisTurn` makes cheaper. -/
inductive SpellCostLess where
  /-- Spells of this card type (CR 205.2a). -/
  | cardType (ty : CardType)
  /-- Spells of this supertype (CR 205.4a). -/
  | supertype (s : Supertype)
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which creatures `SpellResolution.dealDamageToEachCreature` damages. -/
inductive EachCreatureDamage where
  /-- Every creature. -/
  | each
  /-- Each creature an opponent of the controller controls. -/
  | opponentsControl
  /-- Each creature that does not have this subtype. -/
  | nonSubtype (subtype : CardSubtype)
deriving Repr, Inhabited, BEq, DecidableEq

/-- Where the damage from `SpellResolution.dealDamageToEachCreature` comes from. -/
inductive EachCreatureAmount where
  /-- The `n` argument. -/
  | fixed
  /-- The total mana value of other spells the controller has cast this turn.
  The resolving spell itself is not counted. -/
  | otherSpellsManaValue
deriving Repr, Inhabited, BEq, DecidableEq

/-- How `SpellResolution.mutualFight` uses the announced creatures. -/
inductive MutualFight where
  /-- Both announced creatures must still be legal. Each deals damage equal
  to its power to the other. -/
  | both
  /-- The creature you control fights up to one other creature. No second
  target means it has nothing to fight. -/
  | upToOne
deriving Repr, Inhabited, BEq, DecidableEq

/-- How `SpellResolution.searchLibrary` searches. -/
inductive LibrarySearch where
  /-- The controller searches their library and puts the card into their hand. -/
  | youToHand
  /-- The targeted permanent's owner may search and put the card onto the
  battlefield tapped. -/
  | ownerMayToBattlefield
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which announced creatures `SpellResolution.countersOnCreatureTargets`
puts counters on. -/
inductive CreatureCounterTargets where
  /-- Each announced target that is still a legal creature. A player target
  is left alone. -/
  | each
  /-- The first announced target, when it is a creature the controller of the
  resolving spell controls. -/
  | firstYouControl
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which creatures you control `SpellResolution.plusOneOnEachYouControl` affects. -/
inductive YouControlCounters where
  /-- Each creature you control. -/
  | each
  /-- Each creature you control other than the first announced target. -/
  | eachOther
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which targeted card `SpellResolution.returnTargetToHand` returns to a hand. -/
inductive ReturnedCard where
  /-- A spell on the stack, returned to its owner's hand. -/
  | spell
  /-- A graveyard card. Up to one, returned to your hand. -/
  | graveyard
deriving Repr, Inhabited, BEq, DecidableEq

/-- The event `SpellResolution.replace` replaces. -/
inductive ReplaceEvent where
  /-- The targeted permanent dying this turn. -/
  | diesThisTurn
deriving Repr, Inhabited, BEq, DecidableEq

/-- What `SpellResolution.replace` does instead of `ReplaceEvent`. -/
inductive ReplaceInstead where
  /-- Exile it. -/
  | exile
deriving Repr, Inhabited, BEq, DecidableEq

/-- Who the printed `SharedTrigger.recruit` names. -/
inductive RecruitSubject where
  /-- “recruit”. -/
  | recruit
  /-- “you recruit”. -/
  | you
deriving Repr, Inhabited, BEq, DecidableEq

/-- Which permanents `SharedTrigger.plusOneEachYouControl` puts a counter on. -/
inductive YouControlPlusOne where
  /-- Each creature you control. -/
  | eachCreature
  /-- Each permanent of this subtype you control. -/
  | subtype (subtype : CardSubtype)
  /-- Each creature you control, or two counters with the city's blessing. -/
  | citysBlessing
deriving Repr, Inhabited, BEq

/-- When `SharedTrigger.prepareSource` makes this creature prepared. -/
inductive PrepareWhen where
  /-- If it isn't prepared yet. -/
  | ifNotPrepared
  /-- If three or more creatures died this turn. -/
  | ifThreeCreaturesDied
deriving Repr, Inhabited, BEq, DecidableEq

namespace TriggeredAbility

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

/-- Which MSH reflexive `TriggerResolution.queueReflexive` queues.
`toNat` is the index `Resolution.mshReflexive` matches. -/
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

/-- The index `Resolution.mshReflexive` matches. -/
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
mutual

/-- Which player `ObjectSelector.player` names, who
`TriggerResolution.draw` draws for, who
`TriggerResolution.loseLife` loses life, who
`TriggerResolution.mill` mills, whose library
`TriggerResolution.revealLibrary` looks at, and who
`TriggerResolution.amass` amasses for.
An announced target is `.target`, and `which` is the `PlayerSelector`
restricting it. A player is `.target .player`.
The controllers of the objects an `ObjectSelector` names are `.controller`. -/
inductive PlayerSelector where
  /-- Each opponent, or the announced opponent when the ability targets.
  `n` damage to each opponent is `.dealDamage (.fixed n) (.player .eachOpponent)`.
  Each opponent draws `n` is `.draw (.fixed n) .eachOpponent`.
  Each opponent loses `n` life is `.loseLife (.fixed n) .eachOpponent`.
  Each opponent mills `n` is `.mill (.fixed n) .eachOpponent`. -/
  | eachOpponent
  /-- The controller of the ability.
  That player draws `n` is `.draw (.fixed n)` (`.you`).
  That player loses `n` life is `.loseLife (.fixed n)`.
  That player mills `n` is `.mill (.fixed n)`.
  That player's library is `.revealLibrary (.top n) (.put .randomCreature)`.
  That player amasses Goblins `n` is `.amass (.fixed n)`. -/
  | you
  /-- The targeted opponent may have the controller draw a card.
  Declining mills X cards, where X is the influence counters on the source,
  and that player loses life equal to the total mana value of those cards.
  An earlier step must have recorded the offer.
  `.draw (.fixed 1) .opponentHasYou`. -/
  | opponentHasYou
  /-- The announced player. This is the restriction `.target` uses for a player.
  An illegal target mills nothing.
  `.mill (.fixed n) (.target .player)`.
  Read on its own, this is that same player. A missing target names nothing. -/
  | player
  /-- The announced opponent. This is the restriction `.target` uses for an opponent.
  `n` damage to that player is `.dealDamage (.fixed n) (.player (.target .opponent))`.
  That player loses `n` life is `.loseLife (.fixed n) (.target .opponent)`.
  Read on its own, this is that same player. A missing target names nothing. -/
  | opponent
  /-- The controllers of the objects `what` names.
  Each object names the player who controls it. A permanent that has
  left names the controller it had. The same player is named once.
  The enchanted creature's controller is `.controller .enchanted`.
  Nothing enchanted names no player.
  `.draw (.fixed 1) (.controller .enchanted)`.
  The targeted permanent's controller is `.controller .target`.
  Destroy may already have moved it.
  `.createTokens .treasure (.fixed 1) false (who := .controller .target)`.
  The creature an earlier step destroyed is that target, so its
  controller amasses with
  `.amass .notedPower (who := .controller .target)`.
  No destruction amasses nothing.
  Each creature the controller controls names that player with
  `.controller .creaturesYouControl`.
  A selector that does not name objects names no player. -/
  | controller (what : ObjectSelector)
  /-- The announced target `which` names. `which` is a `PlayerSelector`.
  The announced player is `.target .player`.
  An illegal target mills nothing.
  `.mill (.fixed n) (.target .player)`.
  The announced opponent is `.target .opponent`.
  `n` damage to that player is `.dealDamage (.fixed n) (.player (.target .opponent))`.
  That player loses `n` life is `.loseLife (.fixed n) (.target .opponent)`.
  Any other restriction names nothing. -/
  | target (which : PlayerSelector)
  /-- The player who lost life. That player's seat is the trigger's
  last-known toughness. A missing seat mills nothing.
  `.mill .thatManyLost .thatPlayer`. -/
  | thatPlayer
  /-- The player who was dealt combat damage. That seat is the latest
  combat-damage event. A missing event is the controller's opponent.
  `.revealLibrary .untilInstantOrSorcery (.exile .top .forLater .impulse) .damagedPlayer`. -/
  | damagedPlayer
  /-- The announced player. When none was announced, the resolving ability's
  last-known toughness is that player's index.
  `.revealLibrary .untilNonland (.may (.putCounters (.ofKind .plusOnePlusOne) .source) (.exile .top .forLater .anyManaThisTurn) .ifYouDont) .announced`. -/
  | announced
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
Putting cards onto the battlefield names which cards.
Which objects `NumberSelector.count` counts are these selectors.
Which permanents `CostSelector.sacrifice` sacrifices are these selectors.
Which cards `CostSelector.discard` discards are these selectors.
An announced target is `.target`, and `which` is the `ObjectSelector`
restricting it. The announced permanent is `.target` (`.any`).
Objects every selector names are `.intersection`. Objects any selector
names are `.union`. -/
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
  /-- Any announced target. This is the restriction `.target` uses when the
  printed target is not narrowed.
  A pump of the announced permanent is `.pump (.fixed p) (.fixed t) .target`
  (`.any`).
  `n` damage to the announced target, a player or a permanent, is
  `.dealDamage (.fixed n) .target`.
  It loses indestructible until end of turn is `.lose .indestructible`
  (`.target`). An illegal target is reported.
  It becomes an artifact until end of turn is `.becomeArtifact`
  (`.target`).
  It becomes prepared is `.becomePrepared` (`.target`).
  Its base power and toughness become `p`/`t` is
  `.setBasePT (.fixed p) (.fixed t)` (`.target`).
  Its owner puts it on top of their library is `.putOnLibrary .top`
  (`.target`). On the bottom is `.putOnLibrary .bottom`.
  Exiling it is `.exile .target .forLater`.
  Read on its own, this is that same target. A missing target names nothing. -/
  | any
  /-- The announced permanent, while the source is still on the battlefield.
  This is the restriction `.target` uses for that permanent.
  A source that already left is silent.
  A counter on it is
  `.putCounters (.ofKind .plusOnePlusOne) (.target .whileSource)`.
  It loses indestructible until end of turn is
  `.lose .indestructible (.target .whileSource)`.
  It becomes an artifact until end of turn is
  `.becomeArtifact (.target .whileSource)`.
  It becomes prepared is `.becomePrepared (.target .whileSource)`.
  Its base power and toughness become `p`/`t` is
  `.setBasePT (.fixed p) (.fixed t) (.target .whileSource)`.
  Its owner puts it on top of their library is
  `.putOnLibrary .top (.target .whileSource)`.
  On the bottom is `.putOnLibrary .bottom (.target .whileSource)`.
  Exiling it is `.exile (.target .whileSource) .forLater`.
  Read on its own, this is that same permanent. -/
  | whileSource
  /-- The announced permanent, while it is still on the battlefield.
  This is the restriction `.target` uses when a missing target is silent.
  A missing target loses nothing.
  It loses all abilities while the source remains is
  `.lose .allAbilities (.target .ifPresent)`.
  A source that has left leaves that permanent able.
  Tapping it is `.tap (.target .ifPresent)`. A missing target taps nothing.
  Read on its own, this is that same permanent. -/
  | ifPresent
  /-- A creature. This is the restriction `.target` uses for a creature.
  The announced permanent, when it is a creature, is `.target .creature`.
  An illegal target is reported.
  A creature target is `.atLeast (.count (.target .creature)) (.fixed 1)`.
  Read on its own, this is that same creature. A missing target names
  nothing. -/
  | creature
  /-- The announced creature. When two targets were announced, the later one.
  This is the restriction `.target` uses for that creature.
  `.attach .source (.target .laterCreature)`.
  Read on its own, this is that same creature. -/
  | laterCreature
  /-- A planeswalker. This is the restriction `.target` uses for a planeswalker.
  The announced permanent, when it is a planeswalker, is
  `.target .planeswalker`.
  An illegal target is reported.
  A planeswalker target is
  `.atLeast (.count (.target .planeswalker)) (.fixed 1)`.
  Read on its own, this is that same planeswalker. A missing target names
  nothing. -/
  | planeswalker
  /-- Another permanent of this subtype. Not the source.
  This is the restriction `.target` uses for that permanent.
  Another Hero is `.target (.anotherSubtype .hero)`.
  `.atLeast (.count (.target (.anotherSubtype .hero))) (.fixed 1)`.
  Read on its own, this is that same permanent. A missing target names
  nothing. -/
  | anotherSubtype (subtype : CardSubtype)
  /-- Each announced permanent.
  This is the restriction `.target` uses for each of them.
  Each one until the source leaves is
  `.exile (.target .eachPermanent) .untilSourceLeaves`.
  A source that has left exiles nothing.
  Read on its own, this is those permanents. -/
  | eachPermanent
  /-- Each announced Equipment.
  This is the restriction `.target` uses for that Equipment.
  `.attach (.target .eachEquipment) .enchantedCreature`.
  Read on its own, this is that Equipment. -/
  | eachEquipment
  /-- The announced target `which` names. `which` is an `ObjectSelector`.
  The announced permanent is `.target` (`.any`).
  For damage, that target is a player or a permanent.
  It loses indestructible until end of turn is `.lose .indestructible`
  (`.target`). An illegal target is reported.
  Exiling it is `.exile .target .forLater`.
  The announced permanent, while the source remains, is
  `.target .whileSource`. A source that already left is silent.
  The announced permanent, while it remains, is `.target .ifPresent`.
  A missing target is silent.
  The announced permanent, when it is a creature, is `.target .creature`.
  When it is a planeswalker, `.target .planeswalker`.
  Another permanent of this subtype is `.target (.anotherSubtype subtype)`.
  Each announced permanent is `.target .eachPermanent`.
  The later announced creature is `.target .laterCreature`.
  Each announced Equipment is `.target .eachEquipment`.
  Read on its own, a restriction names that same target.
  Any other restriction names nothing. -/
  | target (which : ObjectSelector := by exact .any)
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
  /-- The creature that caused the trigger.
  Returned to its owner's hand is `.returnToHand .cause`.
  A token ceases to exist.
  `subtype`, when set, requires that subtype.
  The Villain that caused this, under its owner's control, as a Hero with
  a finality counter, is
  `.put (.cause (some .villain)) .underOwner (.entering [.additionalSubtype .hero, .counter .finality])`.
  An announced card or permanent is used when one was chosen; otherwise the
  recorded cause. A missing cause, or the wrong subtype, puts nothing.
  A token copy of that artifact, with no subtype, is `.becomeCopy .cause`.
  A subtype copies nothing that way. -/
  | cause (subtype : Option CardSubtype := none)
  /-- Each creature the controller controls. -/
  | creaturesYouControl
  /-- Each other permanent the controller controls of this subtype.
  The source is not included.
  Each other creature of these subtypes is
  `.intersection [.creaturesYouControl, .union (subtypes.toList.map .othersOfSubtype)]`. -/
  | othersOfSubtype (subtype : CardSubtype)
  /-- Each creature an opponent controls. -/
  | opponentsCreatures
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
  | eachNonSubtypeAndOpponents (subtype : CardSubtype)
  /-- The player `who` names.
  The controller is `.player .you`.
  Each opponent is `.player .eachOpponent`.
  The announced opponent is `.player (.target .opponent)`. -/
  | player (who : PlayerSelector)
  /-- `n` cards from the hand of `who`.
  The controller discards `n` is `.cards n` (`.you`).
  Each opponent discards one is `.cards 1 .eachOpponent`.
  The announced opponent discards `n` is `.cards n (.target .opponent)`.
  `TriggerResolution.discard` reads this selector. -/
  | cards (n : Nat := 1) (who : PlayerSelector := by exact .you)
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
  | milledSubtype (subtype : CardSubtype)
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
  `.sacrifice .another`.
  Sacrificing one as a cost is `.pay (.sacrifice (.fixed 1) .another)`.
  Its power is noted. -/
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
  `.putCounters .plusOneNoted .createdToken`.
  Attaching the source to the token the previous step created is
  `.attach .source .createdToken`.
  Attaching the token an earlier step remembered to the source is
  `.attach .createdToken .source`. -/
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
  /-- A card from the controller's hand.
  An empty hand skips the choice.
  Putting it on the bottom of that player's library is
  `.putOnLibrary .bottom .cardFromHand`.
  Putting it on top puts nothing. -/
  | cardFromHand
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
  | basicUpTo (subtype : CardSubtype) (max : Nat)
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
  | creatureFromHand (subtype : CardSubtype) (maxMv : Nat)
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
  /-- Up to one target artifact, non-Aura enchantment, or land.
  The source becomes that copy until the controller's next turn and keeps
  its name. It is also a legendary 4/4 Human Villain creature with vigilance.
  `.becomeCopy .artifactEnchantmentOrLand`.
  Choosing none copies nothing. An illegal object is reported.
  A missing source copies nothing. -/
  | artifactEnchantmentOrLand
  /-- Up to one target creature, or creature card in a graveyard.
  The source becomes that copy until the controller's next turn and keeps
  its name. It is a legendary Human Mercenary Villain creature.
  `.becomeCopy .creatureOrGraveyardCard`. -/
  | creatureOrGraveyardCard
  /-- The creature an earlier step exiled and noted.
  The enchanted creature becomes that copy until the source leaves.
  Nothing noted, or nothing enchanted, copies nothing.
  `.becomeCopy .noted`. -/
  | noted
  /-- The Villain that caused this trigger. You may have it connive.
  Already chosen this turn does nothing. A Villain that will not connive
  is reported.
  `.connive .enteringVillain`. -/
  | enteringVillain
  /-- Any number of Equipment the controller chooses.
  `.attach .anyYouControl .target`. -/
  | anyYouControl
  /-- The artifact an earlier step put from hand.
  `.attach .putArtifact .notedHost`. -/
  | putArtifact
  /-- The announced Equipment. An illegal Equipment does not move.
  `.attach .announcedEquipment .announcedCreature`. -/
  | announcedEquipment
  /-- Up to one announced creature. A missing creature is reported.
  `.attach .target .optionalCreature`. -/
  | optionalCreature
  /-- The creature remembered with the artifact put from hand.
  `.attach .putArtifact .notedHost`. -/
  | notedHost
  /-- The announced creature. An illegal pair does not move the Equipment.
  `.attach .announcedEquipment .announcedCreature`. -/
  | announcedCreature
  /-- The creature the source enchants. A missing creature leaves Equipment
  where it is.
  `.attach (.target .eachEquipment) .enchantedCreature`. -/
  | enchantedCreature
  /-- Each legendary creature the controller controls.
  You control one is
  `.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1)`. -/
  | legendaryCreaturesYouControl
  /-- Each planeswalker the controller controls.
  You control one is
  `.atLeast (.count .planeswalkersYouControl) (.fixed 1)`. -/
  | planeswalkersYouControl
  /-- Each Forest the controller controls other than the one that caused this.
  That Forest's id is this trigger's last-known power.
  At least `n` other Forests is
  `.atLeast (.count .forestsExceptCause) (.fixed n)`. -/
  | forestsExceptCause
  /-- The quest counters on the source, while it is on the battlefield.
  At least `n` is `.atLeast (.count .questCounters) (.fixed n)`.
  A missing source is reported. A source that has left is reported. -/
  | questCounters
  /-- Creature cards in the controller's graveyard.
  At least `n` is `.atLeast (.count .creatureCardsInGraveyard) (.fixed n)`. -/
  | creatureCardsInGraveyard
  /-- The artifact an earlier step put from hand, when it is Equipment.
  Equipment is `.atLeast (.count .putEquipment) (.fixed 1)`.
  An artifact that is not Equipment clears that note. -/
  | putEquipment
  /-- The source, when it is harnessed.
  Harnessed is `.atLeast (.count .harnessedSource) (.fixed 1)`.
  An unharnessed source is reported. A missing source does nothing. -/
  | harnessedSource
  /-- Each artifact the controller controls.
  The source is included when it is an artifact.
  Sacrificing one as a cost is `.pay (.sacrifice (.fixed 1) .artifact)`.
  Sacrificing each of them is `.sacrifice .artifact`. -/
  | artifact
  /-- Each other creature or artifact the controller controls.
  The source is not included. A missing source names nothing.
  Sacrificing one as a cost is
  `.pay (.sacrifice (.fixed 1) .anotherCreatureOrArtifact)`.
  Sacrificing each of them is `.sacrifice .anotherCreatureOrArtifact`. -/
  | anotherCreatureOrArtifact
  /-- Each card in the controller's hand.
  Discarding one as a cost is `.pay (.discard (.fixed 1) .card)`.
  A permanent is not a card in hand. -/
  | card
  /-- Each nonland card in the controller's hand.
  Discarding one as a cost is `.pay (.discard (.fixed 1) .nonland)`.
  A land is not included. A permanent is not a card in hand. -/
  | nonland
  /-- Objects every selector in `what` names.
  An object is named when each selector names it. The same object is named
  once, in the order the first selector names it. An empty list names nothing.
  A selector that does not name objects names nothing here.
  The source, while it is on the battlefield and attacking, is
  `.intersection [.source, .attackingCreatures]`.
  Each creature the controller controls of this subtype is
  `.intersection [.creaturesYouControl, .youControl (.subtype subtype)]`.
  Elves the controller controls are
  `.intersection [.creaturesYouControl, .youControl (.subtype "Elf")]`.
  Each other creature the controller controls of these subtypes is
  `.intersection [.creaturesYouControl, .union (subtypes.toList.map .othersOfSubtype)]`.
  The creature this Equipment is attached to, when that creature is legendary
  and the controller controls it, is
  `.intersection [.equipped, .legendaryCreaturesYouControl]`.
  That creature is
  `.atLeast (.count (.intersection [.equipped, .legendaryCreaturesYouControl])) (.fixed 1)`.
  A missing Equipment is reported. -/
  | intersection (what : List ObjectSelector)
  /-- Objects any selector in `what` names.
  An object is named when one selector names it. The same object is named
  once, in the order the selectors name it. An empty list names nothing.
  A selector that does not name objects adds nothing.
  Each other permanent of these subtypes is
  `.union (subtypes.toList.map .othersOfSubtype)`.
  The creatures among them are
  `.intersection [.creaturesYouControl, .union (subtypes.toList.map .othersOfSubtype)]`. -/
  | union (what : List ObjectSelector)
deriving Repr, Inhabited, BEq

end

/-- Where one statistic of `TriggerResolution.pump` reads its bonus,
where `TriggerResolution.dealDamage` reads its amount, how many cards
`TriggerResolution.scry` looks at, how many cards `TriggerResolution.draw`
draws, where one statistic of `TriggerResolution.setBasePT` reads its
new base, how much life `TriggerResolution.gainLife` gains, how much
life `TriggerResolution.loseLife` loses, how many cards
`TriggerResolution.mill` mills, how many counters
`TriggerResolution.amass` puts on an Army, how many times
`TriggerResolution.addMana` adds its mana, how many tokens
`TriggerResolution.createTokens` creates, how many cards
`TriggerResolution.surveil` surveils, how many loyalty counters
`TriggerResolution.empowerJace` puts on a Jace token, how much less
`TriggerResolution.spellsCostLess` makes a spell cost, how many cards
`TriggerResolution.lookAtTopRevealTypes` looks at, and the base power
and toughness `TriggerResolution.becomePT` sets, how many permanents
`CostSelector.sacrifice` sacrifices, how many cards
`CostSelector.discard` discards, and each number
`ConditionSelector.atLeast` compares.
`.greatestPower` is first so a default resolution uses it.
`.count` is how many objects an `ObjectSelector` names.
`.cardsDrawnThisTurn` is how many cards the controller has drawn this turn.
`.libraryCards` is how many cards are in the controller's library.
`.fixed` is a fixed bonus, `n` damage, scry `n`, draw `n`, a base of `n`,
`n` life gained, `n` life lost, mill `n`, amass `n`, add mana
`n` times, or discard `n` cards. -/
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
  `n` life gained, `n` life lost, mill `n`, amass `n`, or add mana
  `n` times.
  A base of `p`/`t` is `.setBasePT (.fixed p) (.fixed t)`.
  You gain `n` life is `.gainLife (.fixed n)`.
  You lose `n` life is `.loseLife (.fixed n)`.
  You mill `n` cards is `.mill (.fixed n)`.
  You amass Goblins `n` is `.amass (.fixed n)`.
  Adding the printed mana `n` times is `.addMana types (.fixed n)`.
  Once is `.addMana types`.
  Discarding `n` cards is `.discard (.fixed n) .card`.
  Discarding `n` nonland cards is `.discard (.fixed n) .nonland`. -/
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
  /-- The source's last-known power.
  Amass that many is `.amass .lastKnownPower`.
  A missing power is zero. -/
  | lastKnownPower
  /-- How many permanents of this subtype the controller controls. -/
  | subtypeCount (subtype : CardSubtype)
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
  /-- The life that player lost. The amount is the trigger's last-known
  power. A missing amount mills nothing.
  `.mill .thatManyLost .thatPlayer`. -/
  | thatManyLost
  /-- Excess damage an earlier step recorded. Zero excess amasses nothing.
  `.amass .notedExcess`. -/
  | notedExcess
  /-- The power an earlier step recorded when it destroyed a creature.
  No destruction amasses nothing.
  The noted controller amasses that many with
  `.amass .notedPower (who := .controller .target)`. -/
  | notedPower
  /-- The printed mana types, once for each charge counter on the source.
  A source that has left uses its last-known charge counters.
  Zero counters add nothing.
  `.addMana #[.colored .green] .perChargeCounter`. -/
  | perChargeCounter
  /-- One tapped Treasure for each artifact opponents control.
  `.createTokens .treasure .oppArtifacts true`. -/
  | oppArtifacts
  /-- One Treasure for each artifact the damaged player controls.
  `.createTokens .treasure .damagedPlayerArtifacts false`. -/
  | damagedPlayerArtifacts
  /-- One Treasure for each creature the controller controls of a chosen type.
  `.createTokens .treasure .chosenCreatureType false`. -/
  | chosenCreatureType
  /-- One token for each permanent of this subtype the controller controls.
  `.createTokens kind (.perSubtype subtype) false`. -/
  | perSubtype (subtype : CardSubtype)
  /-- One 1/1 blue Merfolk for each blue mana symbol in the spell that
  caused this. No such spell, or no blue symbol, creates nothing.
  `.createTokens .treasure .blueManaSymbols false .merfolk`. -/
  | blueManaSymbols
  /-- How many objects `what` names.
  A selector that does not name a counted set is not a number.
  Quest counters are counted only while the source is on the battlefield.
  A missing source, or one that has left, is not a number.
  At least one legendary creature you control is
  `.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1)`. -/
  | count (what : ObjectSelector)
  /-- How many cards the controller has drawn this turn.
  At least two is `.atLeast .cardsDrawnThisTurn (.fixed 2)`. -/
  | cardsDrawnThisTurn
  /-- How many cards are in the controller's library.
  A card remains is `.atLeast .libraryCards (.fixed 1)`.
  An empty library is `.not (.atLeast .libraryCards (.fixed 1))`. -/
  | libraryCards
  /-- X, chosen as the spell was cast.
  `.createTokens kind .chosenX`. -/
  | chosenX
deriving Repr, Inhabited, BEq

instance : Coe Nat NumberSelector where
  coe n := .fixed (Int.ofNat n)

instance : Coe Int NumberSelector where
  coe := .fixed

instance (n : Nat) : OfNat NumberSelector n where
  ofNat := .fixed (Int.ofNat n)

/-- What `TriggerResolution.pay` pays.
`sacrifice` pays by sacrificing permanents.
`discard` pays by discarding cards.
`or` pays any one of its costs. -/
inductive CostSelector where
  /-- Pay these mana symbols.
  `{n}` is `.mana #[.generic n]`. `{1}{G}{U}` is
  `.mana #[.generic 1, .colored .green, .colored .blue]`. -/
  | mana (symbols : Array ManaSymbol)
  /-- Sacrifice `n` permanents `what` names.
  Sacrificing another creature is `.sacrifice (.fixed 1) .another`.
  Its power is noted for
  `TriggerResolution.putCounters .plusOneSacrificedPower`.
  Sacrificing another creature or artifact is
  `.sacrifice (.fixed 1) .anotherCreatureOrArtifact`.
  Sacrificing an artifact is `.sacrifice (.fixed 1) .artifact`.
  Sacrificing an artifact, or discarding a card, is
  `.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .card]`.
  Sacrificing an artifact, or discarding a nonland card, is
  `.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .nonland]`.
  Any other positive count offers that many permanents `what` names.
  A count that is not a positive number pays nothing.
  Fewer permanents than that count pays nothing.
  A selector that does not name permanents pays nothing.
  A card or a hand is not sacrificed. -/
  | sacrifice (n : NumberSelector) (what : ObjectSelector)
  /-- Discard `n` cards `what` names.
  Discarding a card is `.discard (.fixed 1) .card`.
  Discarding a nonland card is `.discard (.fixed 1) .nonland`.
  Sacrificing an artifact, or discarding a card, is
  `.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .card]`.
  Sacrificing an artifact, or discarding a nonland card, is
  `.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .nonland]`.
  Any other positive count offers that many cards `what` names.
  A count that is not a positive number pays nothing.
  Fewer cards than that count pays nothing.
  A selector that does not name cards in hand pays nothing.
  A permanent is not discarded. -/
  | discard (n : NumberSelector) (what : ObjectSelector)
  /-- Pay any one of `costs`.
  Sacrificing an artifact, or discarding a card, is
  `.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .card]`.
  Sacrificing an artifact, or discarding a nonland card, is
  `.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .nonland]`.
  Any other list offers each cost that can be paid. One payable cost
  is that cost. Several are a choice of which to pay. None pays nothing. -/
  | or (costs : List CostSelector)
deriving Repr, Inhabited, BEq

/-- When `TriggerResolution.if` and `TriggerResolution.ifElse` choose a branch.
`not` negates another condition. `or` holds when any of its conditions hold.
`atLeast` holds when its first number is at least its second. -/
inductive ConditionSelector where
  /-- The first number is at least the second.
  Each number is a `NumberSelector`. `.fixed` is a printed number.
  `.count` is how many objects an `ObjectSelector` names.
  You control a legendary creature is
  `.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1)`.
  Controlling none is
  `.not (.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1))`.
  You control at least `n` lands is
  `.atLeast (.count .landsYouControl) (.fixed n)`.
  Fewer than six is reported.
  You control a planeswalker is
  `.atLeast (.count .planeswalkersYouControl) (.fixed 1)`.
  Controlling one is reported.
  Controlling none is
  `.not (.atLeast (.count .planeswalkersYouControl) (.fixed 1))`.
  You control at least `n` Forests other than the one that caused this is
  `.atLeast (.count .forestsExceptCause) (.fixed n)`.
  Fewer than five is reported.
  You control at least `n` Bears is
  `.atLeast (.count (.youControl (.subtype "Bear"))) (.fixed n)`.
  You control at least `n` permanents of this subtype is
  `.atLeast (.count (.youControl (.subtype subtype))) (.fixed n)`.
  The source has at least `n` quest counters is
  `.atLeast (.count .questCounters) (.fixed n)`.
  A missing source is reported. A source that has left is reported.
  You control a Hero other than the source is
  `.atLeast (.count (.othersOfSubtype "Hero")) (.fixed 1)`.
  This Equipment is attached to a legendary creature you control is
  `.atLeast (.count (.intersection [.equipped, .legendaryCreaturesYouControl])) (.fixed 1)`.
  A missing Equipment is reported.
  The target is a creature is
  `.atLeast (.count (.target .creature)) (.fixed 1)`.
  The target is a planeswalker is
  `.atLeast (.count (.target .planeswalker)) (.fixed 1)`.
  An illegal target is reported.
  Your graveyard has at least `n` creature cards is
  `.atLeast (.count .creatureCardsInGraveyard) (.fixed n)`.
  The targeted permanent has this subtype and is not the source is
  `.atLeast (.count (.target (.anotherSubtype subtype))) (.fixed 1)`.
  The artifact an earlier step put from hand is Equipment is
  `.atLeast (.count .putEquipment) (.fixed 1)`.
  An artifact that is not Equipment clears that note.
  The source is harnessed is
  `.atLeast (.count .harnessedSource) (.fixed 1)`.
  An unharnessed source is reported. A missing source does nothing.
  The source is on the battlefield and attacking is
  `.atLeast (.count (.intersection [.source, .attackingCreatures])) (.fixed 1)`.
  A missing source does not hold.
  Any other counted selector is the number of objects it names.
  A count that cannot be read does not hold.
  A selector that does not name a counted set does not hold.
  You have drawn at least `n` cards this turn is
  `.atLeast .cardsDrawnThisTurn (.fixed n)`.
  At least `n` loyalty counters were removed to activate this ability is
  `.atLeast .lastKnownPower (.fixed n)`.
  That count is the ability's last-known power. A missing power is zero.
  Your library still has a card is
  `.atLeast .libraryCards (.fixed 1)`.
  An empty library is `.not (.atLeast .libraryCards (.fixed 1))`.
  The source's power as this ability resolves is at least `n` is
  `.atLeast .equalSourcePower (.fixed n)`.
  A source that has left uses its last-known power.
  Power below 4 is reported as Viv Vision's.
  Any other pair compares the two numbers.
  A number that cannot be read does not hold. -/
  | atLeast (left right : NumberSelector)
  /-- `cond` does not hold.
  Controlling no legendary creature is
  `.not (.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1))`.
  The source on the battlefield with no hope counters is `.not .hopeOnSource`.
  Controlling no planeswalker is
  `.not (.atLeast (.count .planeswalkersYouControl) (.fixed 1))`.
  An empty library is `.not (.atLeast .libraryCards (.fixed 1))`. -/
  | not (cond : ConditionSelector)
  /-- Any of `conds` holds. Once one holds, later conditions are not checked.
  Attacking with a Hero, or a Hero entering, is
  `.or [.attackedWithSubtype "Hero", .subtypeEntered "Hero"]`.
  Having scried or surveilled is
  `.or [.scriedThisTurn, .surveilledThisTurn]`.
  Greater power or toughness is
  `.or [.causeGreaterPower, .causeGreaterToughness]`. -/
  | or (conds : List ConditionSelector)
  /-- An earlier step removed a hope counter. -/
  | removedHope
  /-- The source is missing, has left the battlefield, or has a hope counter.
  On the battlefield with none, this does not hold.
  No hope counters on that permanent is `.not .hopeOnSource`. -/
  | hopeOnSource
  /-- An earlier step dealt damage to a permanent of this subtype. -/
  | dealtDamageToSubtype (subtype : CardSubtype)
  /-- You attacked with a permanent of this subtype this turn.
  A Hero that left after attacking still counts.
  Attacking with a Hero, or a Hero entering, is
  `.or [.attackedWithSubtype .hero, .subtypeEntered .hero]`. -/
  | attackedWithSubtype (subtype : CardSubtype)
  /-- A permanent of this subtype entered under your control this turn.
  A Hero that left after entering still counts. -/
  | subtypeEntered (subtype : CardSubtype)
  /-- An earlier step returned a permanent to its owner's hand. -/
  | returnedPermanent
  /-- `noteResolveThisTurn` recorded ordinal `n`. -/
  | nthResolve (n : Nat)
  /-- You controlled the creature an earlier step destroyed. -/
  | youControlledDestroyed
  /-- You have an enduring story, and an earlier step discarded your hand. -/
  | enduringStoryNoted
  /-- An earlier `.sacrifice .source .noted` sacrificed the source. -/
  | sourceWasSacrificed
  /-- An earlier `.sacrifice .plan .forReflexive` sacrificed the Plan.
  Checking this consumes that note. -/
  | planWasSacrificed
  /-- An earlier step attached Equipment to a creature that is still in play. -/
  | equipmentAttached
  /-- `.mill` noted `.opponentsMilled`: an opponent milled a card. -/
  | opponentsMilled
  /-- You have scried this turn.
  Scry 0 does not count.
  Having scried or surveilled is
  `.or [.scriedThisTurn, .surveilledThisTurn]`. -/
  | scriedThisTurn
  /-- You have surveilled this turn.
  Surveil 0 does not count. -/
  | surveilledThisTurn
  /-- The card `revealLibrary .untilCreature` revealed has mana value at
  most the lands the controller controls. Outside that resolution, the
  condition does not hold. -/
  | revealedManaValueAtMostLands
  /-- An artifact entered the battlefield under your control this turn.
  None did is reported. -/
  | artifactEnteredThisTurn
  /-- Equipment is attached to the source, or its last-known power is
  positive when the source has left. None is reported. -/
  | attachedEquipment
  /-- An earlier Enrage trigger noted an additional combat phase.
  Checking this consumes that note. -/
  | enrageGrantsCombat
  /-- The creature that caused this has greater power than the source.
  An announced permanent is used when one was chosen; otherwise the
  recorded cause. A missing source is reported. No cause does not hold.
  The source itself does not hold.
  Greater power or toughness is
  `.or [.causeGreaterPower, .causeGreaterToughness]`. -/
  | causeGreaterPower
  /-- The creature that caused this has greater toughness than the source.
  An announced permanent is used when one was chosen; otherwise the
  recorded cause. A missing source is reported. No cause does not hold.
  The source itself does not hold. -/
  | causeGreaterToughness
  /-- Mana was spent to cast the triggering spell.
  Spending none does not hold. -/
  | manaSpent
  /-- The targeted permanent has this subtype. -/
  | subtype (subtype : CardSubtype)
  /-- The targeted spell's mana value was this much or less.
  That value includes `{X}` from when the spell was on the stack (CR 202.3e). -/
  | mvAtMost (n : Nat)
  /-- The resolving spell was cast from a graveyard. -/
  | castFromGraveyard
  /-- The resolving spell was cast using teamwork. -/
  | teamwork
  /-- A gift was promised as the spell was cast. -/
  | giftPromised
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
  /-- A 1/1 blue Merfolk creature token. With amount `.blueManaSymbols`,
  the count is the blue mana symbols in the spell that caused this.
  No blue symbol creates nothing. -/
  | merfolk
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
  | additionalSubtype (subtype : CardSubtype)
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
  /-- It deals `k` times its power to the announced opposing creature.
  One times its power is `.fight .announced (.timesPower 1)`. -/
  | timesPower (k : Nat)
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

/-- How many cards `TriggerResolution.revealFromHand` shows (CR 701.20). -/
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

/-- What `TriggerResolution.cant` prevents, and who can't do it.
The announced permanent can't be blocked this turn is `.beBlocked`.
The source is `.beBlocked .source`.
The enchanted creature is `.beBlocked .enchanted`.
The target, while the source remains, is `.beBlocked (.target .whileSource)`.
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
  `.cant (.beBlocked (.target .whileSource))`.
  Any other selector does nothing. -/
  | beBlocked (who : ObjectSelector := .target)
  /-- Can't be blocked this turn except by creatures with haste.
  `.cant (.beBlockedExceptByHaste .target)`.
  Any other selector does nothing. -/
  | beBlockedExceptByHaste (who : ObjectSelector := .target)
  /-- Can't become untapped for as long as you control the source.
  The announced permanent is `.cant .untapWhileYouControl`.
  An opponent's creature is the only recipient. A creature you control
  is left alone. Any other `who` does nothing. -/
  | untapWhileYouControl (who : ObjectSelector := .target)
deriving Repr, Inhabited, BEq

end TriggeredAbility

open TriggeredAbility

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
source remains is `.grant (.keywords k) (.target .whileSource)`.
Spell steps, trigger steps, activated-ability steps, and the former
`FraResolution` steps are constructors of this inductive. -/
inductive Resolution where
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
  `.pump (.fixed p) (.fixed t) (.intersection [.creaturesYouControl, .union (subtypes.toList.map .othersOfSubtype)])`.
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
  `n` damage to the announced opponent is `.dealDamage (.fixed n) (.player (.target .opponent))`.
  `n` damage to the announced target is `.dealDamage (.fixed n) .target`.
  `n` damage to each creature that is not `subtype`, and to each opponent, is
  `.dealDamage (.fixed n) (.eachNonSubtypeAndOpponents subtype)`.
  Damage equal to the greatest mana value among artifacts you control, to
  the announced opponent, is
  `.dealDamage .greatestArtifactMv (.player (.target .opponent))`.
  Damage equal to the mana value of the spell that caused this, to the
  announced player or permanent, is `.dealDamage .spellManaValue .target`.
  The trigger's last-known power to the announced player or permanent, offered
  as a may, is `.may (.dealDamage .lastKnownPower .target) (.sequence []) .ifYouDo`. -/
  | dealDamage (amount : NumberSelector) (who : ObjectSelector)
      (note : TriggerDamageNote := .none)
  /-- Scry, as `n` says. `.fixed` is that many cards.
  Scry 2 is `.scry (.fixed 2)`. Any other count scries that many cards.
  Scry 0 looks at nothing and does not trigger “whenever you scry.” A
  selector that is not a count scries nothing. -/
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
  `.draw (.fixed 1) (.controller .enchanted)`. Nothing enchanted draws nothing.
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
  A creature card onto the battlefield is `.searchLibrary (.put .creatureCard)`.
  Any other follow-up is resolved on its own, and the library is not searched.
  `thenDo` on its own, outside `searchLibrary`, does what that resolution does. -/
  | searchLibrary (thenDo : Resolution)
  /-- Discard cards, as `what` says.
  One card from the controller is `.discard` (`.cards`).
  Inside `.may _ _ .ifYouDo`, one card is optional: declining skips the follow-up.
  Each opponent discards one is `.discard (.cards 1 .eachOpponent)`.
  The announced opponent discards `n` is `.discard (.cards n (.target .opponent))`.
  The controller's hand, noting how many cards were discarded, is
  `.discard .hand`.
  Optional as `.may (.discard .hand) (.sequence [])`. Declining leaves the note
  empty so the following draw and damage steps do nothing.
  `n` cards when mana was spent to cast the triggering spell is
  `.«if» .manaSpent (.discard (.cards n))`. Spending none discards nothing.
  The announced opponent reveals their hand and discards a nonland you
  choose with `.discard .chosenNonland`.
  `.cards n` for any other player discards that many cards. A selector that
  does not name cards discards nothing. -/
  | discard (what : ObjectSelector := .cards)
  /-- Pay `what`. Inside `.may _ _ .ifYouDo`, declining skips the follow-up.
  `{n}` is `.pay (.mana #[.generic n])`. `{1}{G}{U}` is
  `.pay (.mana #[.generic 1, .colored .green, .colored .blue])`.
  Sacrificing another creature is `.pay (.sacrifice (.fixed 1) .another)`.
  Its power is noted.
  Sacrificing another creature or artifact is
  `.pay (.sacrifice (.fixed 1) .anotherCreatureOrArtifact)`.
  Sacrificing an artifact is `.pay (.sacrifice (.fixed 1) .artifact)`.
  Discarding a card is `.pay (.discard (.fixed 1) .card)`.
  Discarding a nonland card is `.pay (.discard (.fixed 1) .nonland)`.
  Sacrificing an artifact, or discarding a card, is
  `.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .card])`.
  Sacrificing an artifact, or discarding a nonland card, is
  `.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .nonland])`. -/
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
  Any other permanent the selector names gets `n` counters of that kind.
  A card or a hand receives none. -/
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
  Any other permanent the selector names returns to its owner's hand.
  `.revealed` returns the cards an earlier reveal found. A card or a hand
  that is not one of those returns nothing. -/
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
  now. Any other follow-up is put on the stack and resolves as that
  follow-up. It keeps the targets this ability already has. -/
  | queueReflexive (followup : Resolution)
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
  Any other permanent the selector names is sacrificed. `.noted` records
  that a sacrifice happened. `.forReflexive` records it for the next
  reflexive step. A card or a hand is not sacrificed. -/
  | sacrifice (what : ObjectSelector) (note : TriggerSacrificeNote := .none)
  /-- A permanent loses `what`, as `who` says.
  The announced permanent loses indestructible until end of turn is
  `.lose .indestructible`.
  The source is `.lose .indestructible .source`.
  The enchanted creature is `.lose .indestructible .enchanted`.
  The target, while the source remains, is
  `.lose .indestructible (.target .whileSource)`.
  The announced permanent loses all abilities while the source remains is
  `.lose .allAbilities (.target .ifPresent)`. A missing target loses nothing.
  A source that has left leaves that permanent able.
  Any other permanent the selector names loses that ability. A card or a
  hand loses nothing. -/
  | lose (what : AbilitySelector) (who : ObjectSelector := .target)
  /-- `action` says what can't be done, and who can't do it.
  The announced permanent can't be blocked this turn is `.cant .beBlocked`.
  The source is `.cant (.beBlocked .source)`.
  The enchanted creature is `.cant (.beBlocked .enchanted)`.
  The target, while the source remains, is
  `.cant (.beBlocked (.target .whileSource))`.
  The announced permanent can't become untapped for as long as you control
  the source is `.cant .untapWhileYouControl`. An opponent's creature is
  the only recipient. A creature you control is left alone. A missing
  source still records a stand-in. Any other permanent the selector names
  can't do that. A card or a hand is unchanged. -/
  | cant (action : ActionSelector)
  /-- Until end of turn, `who` becomes an artifact in addition to its other
  types. The announced permanent is `.becomeArtifact` (`.target`).
  The source is `.becomeArtifact .source`.
  The enchanted creature is `.becomeArtifact .enchanted`.
  The target, while the source remains, is
  `.becomeArtifact (.target .whileSource)`.
  Gaining indestructible as well is
  `.sequence [.becomeArtifact, .grant (.keywords Keyword.indestructible) .target]`.
  Any other permanent the selector names becomes an artifact until end of
  turn. A card or a hand does not. -/
  | becomeArtifact (who : ObjectSelector := .target)
  /-- `who` becomes prepared. A creature that is already prepared, or has no
  prepare spell, does not. The announced permanent is `.becomePrepared`
  (`.target`).
  The source is `.becomePrepared .source`.
  The enchanted creature is `.becomePrepared .enchanted`.
  The target, while the source remains, is
  `.becomePrepared (.target .whileSource)`.
  Any other permanent the selector names becomes prepared. A creature that
  is already prepared, or has no prepare spell, does not. A card or a hand
  does not. -/
  | becomePrepared (who : ObjectSelector := .target)
  /-- Until end of turn, `who`'s base power and toughness become `power` and
  `toughness`. Each statistic reads its own value.
  The announced permanent becoming `p`/`t` is `.setBasePT (.fixed p) (.fixed t)`.
  The source is `.setBasePT (.fixed p) (.fixed t) .source`.
  The enchanted creature is `.setBasePT (.fixed p) (.fixed t) .enchanted`.
  The target, while the source remains, is
  `.setBasePT (.fixed p) (.fixed t) (.target .whileSource)`.
  Another target creature becoming equal to this creature's power and
  toughness is `.setBasePT .equalSourcePower .equalSourceToughness`.
  A source that has left uses its last-known power and toughness.
  No target logs that none was chosen.
  Any other permanent the selector names receives the two counts.
  A count that is not a number, and a selector that names no permanent,
  sets nothing. -/
  | setBasePT (power toughness : NumberSelector) (who : ObjectSelector := .target)
  /-- Put a card onto a library. `place` says top or bottom, and `what`
  says which card.
  The announced permanent on top of its owner's library is `.putOnLibrary .top`.
  The announced permanent on the bottom is `.putOnLibrary .bottom`.
  The source is `.putOnLibrary .top .source` or `.putOnLibrary .bottom .source`.
  The enchanted creature is `.putOnLibrary .top .enchanted` or
  `.putOnLibrary .bottom .enchanted`.
  The target, while the source remains, is
  `.putOnLibrary .top (.target .whileSource)` or
  `.putOnLibrary .bottom (.target .whileSource)`.
  A card from your hand on the bottom of your library is
  `.putOnLibrary .bottom .cardFromHand`. An empty hand skips the choice.
  A card from your hand on top puts nothing.
  Any other permanent the selector names is put there. A card or a hand
  that is not that choice puts nothing. -/
  | putOnLibrary (place : TriggerLibraryPlace := .top)
      (what : ObjectSelector := .target)
  /-- Deal previously divided damage to the announced targets. -/
  | dividedDamage
  /-- Apply each resolution in order. An illegal required target skips every
  step (CR 608.2b). Return a graveyard card, then gain life equal to its
  power, is `.sequence [.returnToHand .graveyardCard, .gainLife .equalToTargetPower]`.
  Draw, then bottom a card if you control no legendary, is
  `.sequence [.draw (.fixed 1), .«if» (.not (.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1))) (.putOnLibrary .bottom .cardFromHand)]`.
  Remove a hope counter, draw if one was removed, then sacrifice and gain
  life if none remain, is
  `.sequence [.removeCounters .hope .source, .«if» .removedHope (.draw (.fixed 1)), .«if» (.not .hopeOnSource) (.sequence [.sacrifice .source, .gainLife (.fixed 4)])]`.
  A step that asks a player to choose pauses the later steps until that
  choice finishes; they are still part of this resolution. Tap any number
  of Humans, then draw that many, is
  `.sequence [.may (.tap .humans) (.sequence []), .draw .forEachTappedHuman]`.
  Create one token, then attach the source to it, is
  `.sequence [.createTokens kind (.fixed 1) false, .attach .source .createdToken]`.
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
  `.sequence [.destroy .target (note := .forAmass), .amass .notedPower (who := .controller .target), .«if» .youControlledDestroyed (.draw (.fixed 1))]`.
  Return another permanent to its owner's hand, then put a +1/+1 counter on
  the source if one was actually returned, is
  `.sequence [.returnToHand .permanent .returnedPermanent, .«if» .returnedPermanent (.putCounters (.ofKind .plusOnePlusOne) .source)]`.
  Other creatures you control of these subtypes get +P/+T, and creatures
  your opponents control get +oppP/+oppT, is
  `.sequence [.pump (.fixed p) (.fixed t) (.intersection [.creaturesYouControl, .union (subtypes.toList.map .othersOfSubtype)]), .pump (.fixed oppP) (.fixed oppT) .opponentsCreatures]`.
  Gain 1 life, draw, or put a +1/+1 counter on each creature you control
  when this is the first, second, or third resolve this turn (Belladonna
  Took), is
  `.sequence [.noteResolveThisTurn 3, .«if» (.nthResolve 1) (.gainLife (.fixed 1)), .«if» (.nthResolve 2) (.draw (.fixed 1)), .«if» (.nthResolve 3) (.putCounters (.ofKind .plusOnePlusOne) .youControl)]`.
  Deal the sacrificed creature's power, then amass Goblins for the excess
  (Bolg), is
  `.sequence [.dealDamage .lastKnownPower .permanent .excess, .amass .notedExcess]`.
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
  `.sequence [.grant (.keywords k) .target, .«if» (.atLeast (.count (.target .creature)) (.fixed 1)) (.putCounters (.ofKind .plusOnePlusOne) .permanent), .«if» (.atLeast (.count (.target .planeswalker)) (.fixed 1)) (.putCounters (.ofKind .loyalty) .permanent)]`.
  The target gets +3/+0 and gains first strike until end of turn, is
  `.sequence [.pump (.fixed 3) (.fixed 0) .target, .grant (.keywords Keyword.firstStrike) .target]`.
  +P/+T and trample is
  `.sequence [.pump (.fixed p) (.fixed t) .target, .grant (.keywords Keyword.trample) .target]`.
  Becoming an artifact and gaining indestructible is
  `.sequence [.becomeArtifact, .grant (.keywords Keyword.indestructible) .target]`.
  Tap and a stun counter is
  `.sequence [.tap .target, .putCounters (.ofKind .stun) .permanent]`.
  Destroy the target, then its controller creates a Treasure, is
  `.sequence [.destroy .target, .createTokens .treasure (.fixed 1) false (who := .controller .target)]`.
  You may put an artifact from your hand onto the battlefield, then attach
  it to the source if it is Equipment, is
  `.sequence [.may (.put .artifactFromHand (note := .forAttach)) (.sequence []), .«if» (.atLeast (.count .putEquipment) (.fixed 1)) (.attach .putArtifact .notedHost)]`. -/
  | sequence (rs : List Resolution)
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
  `.may (.pay (.sacrifice (.fixed 1) .another)) (.putCounters .plusOneSacrificedPower .source) .ifYouDo`.
  You may pay `{1}{G}{U}` to return this from the graveyard is
  `.may (.pay (.mana #[.generic 1, .colored .green, .colored .blue])) (.returnToHand .source) .ifYouDo`.
  You may sacrifice another creature or artifact to draw and create a Treasure is
  `.may (.pay (.sacrifice (.fixed 1) .anotherCreatureOrArtifact)) (.sequence [.draw (.fixed 1), .createTokens .treasure (.fixed 1) false]) .ifYouDo`.
  You may discard your hand to draw `n` is `.may (.discard .hand) (.draw (.fixed n)) .ifYouDo`.
  You may draw for each permanent of a type, and each opponent draws if you do, is
  `.may (.draw (.perControlled ty)) (.draw (.fixed 1) (who := .eachOpponent)) .ifYouDo`.
  You may sacrifice an artifact or discard a card to draw is
  `.may (.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .card])) (.draw (.fixed 1)) .ifYouDo`.
  You may sacrifice another creature to destroy an opposing nonland is
  `.may (.pay (.sacrifice (.fixed 1) .another)) (.queueReflexive (.destroy .target)) .ifYouDo`.
  You may sacrifice an artifact or discard a nonland to deal 2 damage is
  `.may (.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .nonland])) (.queueReflexive (.dealDamage (.fixed 2) .target)) .ifYouDo`.
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
  `.may (.createTokens .wall04defender (.fixed 1) false) (.sequence []) .ifYouDo`.
  Declining creates nothing. -/
  | may (action follow : Resolution) (when : TriggerMayWhen := .ifYouDont)
  /-- You gain life (CR 119.3), as `amount` says.
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
  Any other count gains that much life. A count that cannot be read
  gains nothing. -/
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
  `.exile (.target .eachPermanent) .untilSourceLeaves`.
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
  `.exile (.target .whileSource) .forLater`.
  The announced nonland the controller still controls, other than the
  source, exiled and returned immediately, is
  `.exile .target .returnImmediately`. Choosing none does nothing.
  While the source is harnessed is
  `.«if» (.atLeast (.count .harnessedSource) (.fixed 1)) (.exile .target .returnImmediately)`.
  An unharnessed source is reported and exiles nothing.
  The announced nontoken artifact or creature, returned tapped, is
  `.exile .target .returnTapped`. Choosing none does nothing.
  You may exile the card recorded as this trigger's last-known power and
  play it until the end of your next turn with
  `.may (.exile .discarded .playUntilNextTurn) (.sequence []) .ifYouDo`.
  A card that has left your graveyard is reported. No recorded card is
  reported. Declining exiles nothing.
  Any other permanent the selector names is exiled as `how` and `note` say.
  A graveyard card, the top of a library, a linked exile, a milled card, a
  discarded card, or a card an earlier reveal found is exiled the same way.
  `.top` with `.impulse` or `.anyManaThisTurn` exiles nothing unless an
  earlier reveal found a card. A hand or an unmade choice exiles nothing. -/
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
  Any other graveyard card the selector names, the top card of your library,
  or the source in its owner's graveyard is put onto the battlefield as
  `how` and `note` say. `.revealed` and `.randomCreature` use the cards an
  earlier reveal found. Outside that reveal, both do nothing. A permanent
  already on the battlefield is not put again. -/
  | put (what : ObjectSelector) (how : TriggerPutHow := .asPrinted)
      (note : TriggerPutNote := .none)
  /-- Remove counters. `what` says which, and `who` says from whom.
  A hope counter from the source is `.removeCounters .hope .source`.
  Removing none leaves the later draw skipped. A missing source, or a
  source that has left the battlefield, removes nothing.
  All counters from the enchanted creature are
  `.removeCounters .all .enchanted`. Nothing enchanted removes nothing.
  Any other permanent the selector names loses that counter, or every
  counter. A card or a hand loses nothing. -/
  | removeCounters (what : TriggerRemoveWhat) (who : ObjectSelector)
  /-- Tap permanents, as `who` says.
  Any number of untapped Humans you control is `.tap .humans`.
  Choosing none taps nothing. Optional as `.may (.tap .humans) (.sequence [])`.
  The creature the source enchants is `.tap .enchanted`.
  Nothing enchanted taps nothing. A missing source taps nothing.
  The announced permanent, if it is still on the battlefield, is
  `.tap (.target .ifPresent)`. A missing target taps nothing.
  The announced permanent, while it is still a legal target, is
  `.tap .target`. An illegal target is reported.
  Wrapping one in `may` is that tap.
  The creature this Aura enchants, while the Aura remains, is
  `.tap .enchantedWhileSource`.
  Any other permanent the selector names is tapped. A card or a hand
  is not. -/
  | tap (who : ObjectSelector)
  /-- Untap permanents, as `who` says.
  The announced permanent, while it is still a legal target, is `.untap`.
  An illegal target is reported. A stun counter is removed instead of
  untapping (CR 122.1d).
  The source is `.untap .source`. A missing source untaps nothing.
  The enchanted creature is `.untap .enchanted`. Nothing enchanted untaps
  nothing.
  The announced permanent while the source remains is
  `.untap (.target .whileSource)`. A source that already left is silent.
  Each attacking creature is `.untap .attackingCreatures`.
  Tap or untap is `.or [.tap .target, .untap]`.
  Any other permanent the selector names is untapped. A card or a hand
  is not. -/
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
  The target, while the source remains, is `.destroy (.target .whileSource)`.
  Any other permanent the selector names is destroyed. A card or a hand
  is not. -/
  | destroy (what : ObjectSelector) (note : TriggerDestroyNote := .none)
  /-- Recruit. “recruit” is `.recruit`. “you recruit” is `.recruit .you`. -/
  | recruit (who : RecruitSubject := .recruit)
  /-- Amass `subtype` for `who`, as `amount` says. Attach the source when
  `attachSource` is true.
  Goblins `n` is `.amass (.fixed n)`.
  Orcs `n` is `.amass (.fixed n) "Orc"`.
  Equal to this creature's power is `.amass .lastKnownPower`.
  A missing power is zero.
  Then attach this Equipment is `.amass (.fixed n) (attachSource := true)`.
  Equal to the excess an earlier step noted is `.amass .notedExcess`.
  Zero excess amasses nothing.
  The noted controller amasses that creature's power is
  `.amass .notedPower (who := .controller .target)`.
  No destruction amasses nothing.
  Any other count is amassed for the players the selector names.
  A count that cannot be read amasses nothing. -/
  | amass (amount : NumberSelector) (subtype : CardSubtype := .goblin)
      (attachSource : Bool := false) (who : PlayerSelector := .you)
  /-- Create tokens. How many is `amount`. Who receives them is a
  `PlayerSelector`. `token` says which token, and `note` says what a later
  step can read.
  `n` of `kind` is `.createTokens kind (.fixed n) tapped`.
  An Axe is `.createTokens .treasure (.fixed 1) false .axe`.
  Attaching that Axe is
  `.createTokens .treasure (.fixed 1) false .axe (note := .attachReflexive)`.
  Tapped Treasures equal to opposing artifacts are
  `.createTokens .treasure .oppArtifacts true`.
  A Treasure for each artifact the damaged player controls is
  `.createTokens .treasure .damagedPlayerArtifacts false`.
  Bird Soldiers equal to the last-known count are
  `.createTokens .birdSoldier .lastKnownPower false`.
  Treasures equal to that count are
  `.createTokens .treasure .lastKnownPower false`.
  Treasures for each creature of a chosen type are
  `.createTokens .treasure .chosenCreatureType false`.
  Zabu is `.createTokens .treasure (.fixed 1) false .zabu`.
  The announced opponent creates The Void with
  `.createTokens .treasure (.fixed 1) false .theVoid (.target .opponent)`.
  Redwing is `.createTokens .treasure (.fixed 1) false .redwing`.
  An Alien, remembering invasion counters, is
  `.createTokens .treasure (.fixed 1) false .alien (note := .invasion)`.
  A Sturdy Shield, remembered for a later attach, is
  `.createTokens .treasure (.fixed 1) false .sturdyShield (note := .remember)`.
  The target's controller creates a Treasure with
  `.createTokens .treasure (.fixed 1) false (who := .controller .target)`.
  One 1/1 blue Merfolk for each blue mana symbol in the spell that caused
  this is `.createTokens .treasure .blueManaSymbols false .merfolk`.
  Any other count creates that many of the named token for the players
  the selector names. Zero creates nothing. A count that cannot be read
  creates nothing. -/
  | createTokens (kind : TokenKind) (amount : NumberSelector) (tapped : Bool := false)
      (token : TriggerToken := .kind) (who : PlayerSelector := .you)
      (note : TriggerTokenNote := .none)
  /-- Attach `what` to `host`.
  The source to the token created by the previous step is
  `.attach .source .createdToken`.
  The source to the targeted permanent is `.attach .source .target`.
  Target Equipment to up to one target creature you control is
  `.attach .target .optionalCreature`.
  The source to the creature target is `.attach .source (.target .laterCreature)`.
  Any number of Equipment you control to the target creature is
  `.attach .anyYouControl .target`.
  The token an earlier step remembered, attached to the source, is
  `.attach .createdToken .source`.
  The artifact put from hand, attached to the remembered creature, is
  `.attach .putArtifact .notedHost`.
  Any other pair attaches each permanent `what` names to the first permanent
  `host` names. A card or a hand attaches nothing. -/
  | attach (what host : ObjectSelector)
  /-- Add mana, as `amount` says. `types` is the printed mana.
  Adding those types once is `.addMana types`.
  Adding them `n` times is `.addMana types (.fixed n)`.
  Zero times adds nothing.
  {G} for each charge counter on the source is
  `.addMana #[.colored .green] .perChargeCounter`.
  A source that has left uses its last-known charge counters.
  Any other count adds the printed types that many times. Zero adds
  nothing. A count that cannot be read adds nothing. -/
  | addMana (types : Array ManaType) (amount : NumberSelector := .fixed 1)
  /-- Set the source's base power and toughness, as the selectors say.
  `.fixed` is that number. Both printed numbers are `.fixed`.
  Base power `p` and toughness `t` is `.becomePT (.fixed p) (.fixed t)`.
  Any other counts offer those base values. A count that is not a number
  changes nothing. -/
  | becomePT (power toughness : NumberSelector)
  /-- Look at the top cards, as `n` says, and you may reveal a listed type.
  `.fixed` is that many cards.
  The top `n` is `.lookAtTopRevealTypes (.fixed n) types`.
  Any other count looks at that many cards. A count that cannot be read
  looks at nothing. -/
  | lookAtTopRevealTypes (n : NumberSelector) (types : Array String)
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
  `.«if» (.not (.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1))) (.putOnLibrary .bottom .cardFromHand)`.
  Drawing when an earlier step removed a hope counter is
  `.«if» .removedHope (.draw (.fixed 1))`.
  Doing `thenDo` on the nth resolution this turn is
  `.«if» (.nthResolve n) thenDo`.
  Attaching the artifact put from hand when it is Equipment is
  `.«if» (.atLeast (.count .putEquipment) (.fixed 1)) (.attach .putArtifact .notedHost)`.
  Exiling and returning the announced permanent while the source is
  harnessed is
  `.«if» (.atLeast (.count .harnessedSource) (.fixed 1)) (.exile .target .returnImmediately)`.
  An unharnessed source is reported. A missing source does nothing.
  Drawing when an artifact entered under your control this turn is
  `.«if» .artifactEnteredThisTurn (.draw (.fixed 1))`. None did is reported.
  Drawing when the source's power is at least 4 is
  `.«if» (.atLeast .equalSourcePower (.fixed 4)) (.draw (.fixed 1))`. A source that has left uses
  its last-known power. Power below 4 is reported.
  Draining for the Equipment attached to the source is
  `.«if» .attachedEquipment (.sequence [.loseLife .attachedEquipment .eachOpponent, .gainLife .attachedEquipment])`.
  No Equipment is reported.
  Discarding `n` cards when mana was spent to cast the triggering spell is
  `.«if» .manaSpent (.discard (.cards n))`. Spending none discards nothing. -/
  | «if» (cond : ConditionSelector) (thenDo : Resolution)
  /-- Resolve `whenTrue` when `cond` holds, and `whenFalse` otherwise.
  A tapped Villain when your graveyard has two creature cards, and milling
  two otherwise, is
  `.ifElse ((.atLeast (.count .creatureCardsInGraveyard) (.fixed 2))) (.createTokens .villain21menace (.fixed 1) true) (.mill (.fixed 2))`.
  Two +1/+1 counters when the target is another Hero, and one otherwise, is
  `.ifElse ((.atLeast (.count (.target (.anotherSubtype "Hero"))) (.fixed 1))) (.putCounters (.ofKind .plusOnePlusOne 2) .permanent) (.putCounters (.ofKind .plusOnePlusOne) .permanent)`.
  A +1/+1 counter when you have scried or surveilled, and +1/+1 until end of
  turn otherwise, is
  `.ifElse (.or [.scriedThisTurn, .surveilledThisTurn]) (.putCounters (.ofKind .plusOnePlusOne) .permanent) (.pump (.fixed 1) (.fixed 1) .target)`.
  The revealed creature enters when its mana value is at most the lands
  you control, and goes to your hand otherwise, with
  `.ifElse .revealedManaValueAtMostLands (.put .revealed) (.returnToHand .revealed)`.
  Outside `revealLibrary .untilCreature`, that condition does not hold. -/
  | ifElse (cond : ConditionSelector) (whenTrue whenFalse : Resolution)
  /-- The controller chooses one of these resolutions.
  Tap an opposing creature or untap one you control is
  `.or [.tap .target, .untap]`.
  A +1/+1 counter on a Wolf you control, or a Treasure token, is
  `.or [.putCounters (.ofKind .plusOnePlusOne) .permanent, .createTokens .treasure (.fixed 1) false]`.
  Tap or untap the targeted nonland is
  `.or [.tap .target, .untap]`.
  A Food token or a Treasure token is
  `.or [.createTokens .food (.fixed 1) false, .createTokens .treasure (.fixed 1) false]`.
  +1/+1 counters on the creature targets, or returning an artifact or
  enchantment card from the graveyard, is
  `.or [.putCounters (.ofKind .plusOnePlusOne) .permanent, .returnToHand .graveyardCard]`. -/
  | or (rs : List Resolution)
  /-- Resolve these modes, as `how` says.
  Alliance is `.chooseModes TriggerResolution.allianceModes .oneUnusedThisTurn`.
  Gollum is `.chooseModes TriggerResolution.gollumModes .oneUnused`.
  Chosen up to X, in printed order, is
  `.chooseModes TriggerResolution.upToXModes .alreadyChosen`.
  A +1/+1 counter on the source, or removing a counter to draw, is
  `.chooseModes TriggerResolution.hydeModes .plusOneOrRemoveCounter`.
  One unused Vision mode this turn is
  `.chooseModes TriggerResolution.visionModes .vision`. -/
  | chooseModes (modes : List Resolution) (how : TriggerModeHow)
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
  Any other permanent the selector names receives that ability. A card, a
  hand, or an unmade choice receives nothing. -/
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
  Whose library is a `PlayerSelector`.
  Any other combination reveals the cards `how` and `who` name, then
  resolves `thenDo`. A player the selector does not name reveals nothing. -/
  | revealLibrary (how : TriggerLibraryHow) (thenDo : Resolution)
      (who : PlayerSelector := .you)
  /-- Mill cards (CR 701.17), as `amount` and `who` say. `note` says what a
  later step can read.
  Milling zero cards changes nothing. A library that runs out logs that
  it is empty and mills nothing further.
  The controller mills `n` with `.mill (.fixed n)`.
  The announced player mills `n` with `.mill (.fixed n) (.target .player)`.
  An illegal target mills nothing.
  The player who lost life mills that many with
  `.mill .thatManyLost .thatPlayer`.
  The count is the trigger's last-known power. That player's seat is the
  trigger's last-known toughness. A missing count or seat mills nothing.
  The controller mills `n` and remembers those cards with
  `.mill (.fixed n) (note := .milledCards)`.
  Each opponent mills `n`, and a later step sees whether any card was
  milled, with `.mill (.fixed n) .eachOpponent (note := .opponentsMilled)`.
  Any other count is milled by the players the selector names, and the
  note records what it says. A missing count or player mills nothing. -/
  | mill (amount : NumberSelector) (who : PlayerSelector := .you)
      (note : TriggerMillNote := .none)
  /-- Create two nonlegendary token copies of the source. -/
  | copySelfNonlegendary
  /-- The Ring tempts you. -/
  | ringTempts
  /-- Spells of `which` cost less this turn, as `n` says.
  `.fixed` is that much generic mana.
  A card type is `.spellsCostLess (.cardType ty) (.fixed n)`.
  A supertype is `.spellsCostLess (.supertype s) (.fixed n)`.
  Any other count reduces the cost by that much. A count that cannot be
  read changes nothing. -/
  | spellsCostLess (which : SpellCostLess) (n : NumberSelector)
  /-- Investigate (create a Clue). -/
  | investigate
  /-- Connive (CR 701.50). `who` says which creature.
  The source is `.connive`.
  The announced creature is `.connive .target`. The kind of that target is
  chosen when the ability is put on the stack.
  The Villain that caused this is `.connive .enteringVillain`.
  Already chosen this turn does nothing. A Villain that will not connive
  is reported.
  Any other permanent the selector names connives. A card or a hand
  connives nothing. -/
  | connive (who : ObjectSelector := .source)
  /-- A creature fights, or deals damage equal to its power. `who` says
  which creature, and `how` says which.
  The source fights up to one other target creature with `.fight`.
  Choosing none fights nothing. A missing source or an illegal target
  fights nothing.
  The creature that received Equipment deals damage equal to its power
  to up to one target creature with `.fight .equipmentHost .reflexive`.
  That target is chosen when the reflexive ability is put on the stack.
  Nothing is queued when no creature received Equipment.
  Any other permanent the selector names fights another targeted creature,
  or deals damage equal to its power when `how` is `.reflexive`. A card or
  a hand fights nothing. -/
  | fight (who : ObjectSelector := .source) (how : TriggerFightHow := .mutual)
  /-- A player reveals cards from their hand (CR 701.20), as `count` says,
  then resolves `thenDo`.
  The opponent reveals their hand. You may exile a nonland card from it, or
  the chosen creature, until the source leaves, with
  `.revealFromHand .hand (.exile .target .untilSourceLeaves)`.
  A source that has already left still reveals; nothing is exiled.
  The announced player reveals one card plus one for each creature card in
  your graveyard. You choose one of them and that player discards it, with
  `.revealFromHand .onePlusCreatureCards (.discard (.cards 1 (.target .opponent)))`.
  A smaller hand is revealed in full.
  Any other combination reveals that hand, then resolves `thenDo`. -/
  | revealFromHand (count : TriggerRevealCount) (thenDo : Resolution)
  /-- Surveil, as `n` says (CR 701.25). `.fixed` is that many cards.
  Surveil 2 is `.surveil (.fixed 2)`. Any other count surveils that many
  cards. Surveil 0 looks at nothing. A count that cannot be read surveils
  nothing. -/
  | surveil (n : NumberSelector)
  /-- Empower Jace, as `n` says (Reality Fracture).
  `.fixed` is that many loyalty counters.
  Empower Jace `n` is `.empowerJace (.fixed n)`.
  Any other count puts that many loyalty counters. A count that cannot
  be read empowers nothing. -/
  | empowerJace (n : NumberSelector)
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
  /-- A player loses life (CR 119.3), as `amount` and `who` say.
  Losing 0 life does nothing.
  You lose `n` life is `.loseLife (.fixed n)`.
  The announced opponent loses `n` life is
  `.loseLife (.fixed n) (.target .opponent)`.
  Each opponent loses `n` life is `.loseLife (.fixed n) .eachOpponent`.
  You lose 1 life for each burden counter on the source is
  `.loseLife .perBurden`.
  A missing source loses nothing.
  Each opponent loses life equal to the Equipment attached to the source with
  `.loseLife .attachedEquipment .eachOpponent`.
  A source that has left uses its last-known power. Zero loses nothing.
  Any other count is lost by the players the selector names. An offer
  is not a player, and a missing count loses nothing. -/
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
  enters. A subtype on `.cause` copies nothing.
  Any other permanent the selector names, other than the source itself, is
  what the source copies. A missing source copies nothing. A card or a hand
  copies nothing. -/
  | becomeCopy (of : ObjectSelector)
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

  /-- You may play an additional land this turn. -/
  | extraLand
  /-- The two announced creatures fight (CR 701.14): each deals damage equal
  to its power to the other. Both creatures required is `.mutualFight` (`.both`).
  Up to one other creature is `.mutualFight .upToOne`. Counters and then the
  required fight are
  `.sequence [.countersOnCreatureTargets .plusOnePlusOne n .firstYouControl, .mutualFight]`. -/
  | mutualFight (how : MutualFight := .both)
  /-- Affect a still-legal target. Damage can hit a player or a creature;
  other actions require a permanent. -/
  | onPermanent (action : PermanentAction)
  /-- Creatures in `scope` get +P/+T until end of turn.
  Creatures you control are `.creaturesPump p t` (`.youControl`).
  Every creature is `.creaturesPump p t .all`. Creatures the targeted
  player controls are `.creaturesPump p t .ofTargetPlayer`. -/
  | creaturesPump (power toughness : Int) (scope : CreaturePumpScope := .youControl)
  /-- Exile cards of type `ty` from the targeted player's graveyard and grant
  permission to cast them, spending mana as though it were any type. -/
  | exileGraveyardCreaturesGrantCast (ty : CardType := .creature)
  /-- Tap each targeted creature (one or two). -/
  | tapTargets
  /-- Counter the targeted spell. -/
  | counter
  /-- Resolve `r` unless its controller pays `{n}`.
  Countering unless they pay is `.unlessPays .counter n`. -/
  | unlessPays (r : Resolution) (n : Nat)
  /-- Counter; exile a permanent spell and grant a free cast. -/
  | counterExilePermanentMayCast
  /-- Attach an Equipment you control to the targeted creature. -/
  | attachEquipment
  /-- Exchange control of the two targeted permanents. -/
  | exchangeControl
  /-- Put `n` counters of `kind` on creatures among the announced targets.
  Each legal creature target is `.countersOnCreatureTargets` (`.each`).
  The first targeted creature you control is
  `.countersOnCreatureTargets .plusOnePlusOne n .firstYouControl`. -/
  | countersOnCreatureTargets (kind : CounterKind := .plusOnePlusOne) (n : Nat := 1)
      (which : CreatureCounterTargets := .each)
  /-- Return the targeted `card` to a hand.
  A spell on the stack is `.returnTargetToHand` (`.spell`), to its owner's hand.
  A graveyard card is `.returnTargetToHand .graveyard`: up to one, to your hand. -/
  | returnTargetToHand (card : ReturnedCard := .spell)
  /-- Creatures you control gain these keywords until end of turn. -/
  | teamGain (k : Keywords)
  /-- Search a library for a `s` `ty` card, as `how` says.
  The controller, into their hand, is `.searchCard` (`.youToHand`).
  The targeted permanent's owner, who may put it onto the battlefield tapped,
  is `.searchCard .basic .land .ownerMayToBattlefield`. -/
  | searchCard (s : Supertype := .legendary) (ty : CardType := .creature)
      (how : LibrarySearch := .youToHand)
  /-- If `what` would happen, `instead` happens in its place.
  The targeted creature dying this turn, exiled instead, is
  `.replace .diesThisTurn .exile`. A pump and that replacement are
  `.sequence [.onPermanent (.pump p t), .replace .diesThisTurn .exile]`.
  Damage, losing indestructible, and that replacement are
  `.sequence [.onPermanent (.dealDamage n), .onPermanent .loseIndestructible, .replace .diesThisTurn .exile]`. -/
  | replace (what : ReplaceEvent) (instead : ReplaceInstead)
  /-- Add {R} for each permanent of type `ty` opponents control. -/
  | addRedPerOppArtifacts (ty : CardType := .artifact)
  /-- Choose a creature type and bounce the rest. -/
  | chooseTypeReturnOthers
  /-- Draw equal to greatest toughness, then put creatures onto the battlefield. -/
  | drawEqualToughnessThenPutCreatures
  /-- Mill `n`, then put cards from among them into your hand as `which` says.
  Up to one instant or sorcery is `.millThenPut n (.oneOf .instant .sorcery)`.
  Up to `max` lands is `.millThenPut n (.upTo max .land)`.
  Every instant or sorcery is `.millThenPut n (.allOf .instant .sorcery)`. -/
  | millThenPut (n : Nat) (which : MilledToHand)
  /-- Exile targeted permanents you control, then return them. -/
  | exileThenReturnYouControl
  /-- Add `n` mana in any combination of colors, spendable only on `subtype` spells. -/
  | addFourManaDragonSpells (n : Nat := 4) (subtype : CardSubtype := .dragon)
  /-- Exile attacking creatures; that player may search basics. -/
  | exileAttackersSearchBasics
  /-- Exile the top `n`; play them if you control this subtype. -/
  | exileTopPlayIfYouControlSubtype (n : Nat) (subtype : CardSubtype)
  /-- Players can't cast spells this turn. A promised gift gates this with
  `.«if» .playersCantCastThisTurn .giftPromised`. -/
  | playersCantCastThisTurn
  /-- Exile the top X of the targeted opponent; play them for life. -/
  | exileTopXOppPlayForLife
  /-- Separate the top `n` cards into two piles (Riddles in the Dark). -/
  | riddlesInTheDark (n : Nat := 4)
  /-- Return this-turn battlefield-to-gy creatures as Food. -/
  | supperForSpiders
  /-- Bounce owned creatures; delayed Bird Soldiers. -/
  | eaglesAreComing
  /-- Look at the top `n`; put lands onto the battlefield tapped; gain life. -/
  | lookAtTopLandsGainLife (n life : Nat)
  /-- Gain control of targeted opposing artifacts. -/
  | gainControlOppArtifacts
  /-- Phase out the target, or each of a player's creatures if kicked. -/
  | phaseOutKicker
  /-- Deal `n` damage to the targeted permanent's controller.
  Teamwork gates this with `.«if» (.dealDamageToControllerOfTarget n) .teamwork`. -/
  | dealDamageToControllerOfTarget (n : Nat)
  /-- Exile MV-limited creature, or any plus gain life if teamwork. -/
  | exileCreatureMvAtMostOrAnyIfTeamwork (n life : Nat)
  /-- Return a gy creature, MV-limited unless teamwork. -/
  | returnGyCreatureMvAtMostOrAny (n : Nat)
  /-- Reveal the top `n` and put creatures onto the battlefield. -/
  | revealTopPutCreatures (n : Nat)
  /-- Return one or two targeted nonlands to hand. -/
  | returnOneOrTwoNonlands
  /-- The targeted player investigates. -/
  | targetPlayerInvestigates
  /-- Apply `action` to the creature among the announced targets. -/
  | onCreatureAmongTargets (action : PermanentAction)
  /-- Deal damage to each creature in `which`. `n` is the amount when `amount`
  is `.fixed` (the default). Every creature is `.dealDamageToEachCreature n`
  (`.each`). Creatures opponents control are
  `.dealDamageToEachCreature n .opponentsControl`. Creatures that are not
  `subtype` are `.dealDamageToEachCreature n (.nonSubtype subtype)`.
  Damage equal to other spells' mana value, to creatures opponents control, is
  `.dealDamageToEachCreature 0 .opponentsControl .otherSpellsManaValue`. -/
  | dealDamageToEachCreature (n : Nat) (which : EachCreatureDamage := .each)
      (amount : EachCreatureAmount := .fixed)
  /-- Return a graveyard card of this subtype to hand. -/
  | returnGySubtypeToHand (subtype : CardSubtype)
  /-- Become a P/T artifact creature and gain `kw`. -/
  | becomeArtifactCreature44Flying (p : Int := 4) (t : Int := 4) (kw : String := "flying")
  /-- Discard `n` cards unless a card of type `ty` is discarded. -/
  | discardTwoUnlessArtifact (n : Nat := 2) (ty : CardType := .artifact)
  /-- `n` +1/+1 counters on creatures you control.
  Each creature is `.plusOneOnEachYouControl` (`.each`).
  Each creature other than the first announced target is
  `.plusOneOnEachYouControl n .eachOther`. -/
  | plusOneOnEachYouControl (n : Nat := 1) (which : YouControlCounters := .each)
  /-- `n` +1/+1 counters on a creature you control. -/
  | plusOneOnCreatureN (n : Nat)
  /-- Exile the top `n` cards. You may play them until your next turn. -/
  | exileTopPlayUntilNext (n : Nat)
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
  /-- Maybe draw one card for each permanent of type `ty`; opponents draw if you do. -/
  | mayDrawPerArtifactOppsDraw (ty : CardType := .artifact)
  /-- Maybe put a `subtype` creature from hand with mana value `n` or less; otherwise draw. -/
  | mayPutHeroMvOrDraw (n : Nat) (subtype : CardSubtype := .hero)
  /-- Maybe sacrifice or discard, then draw. -/
  | maySacArtifactOrDiscardDraw (cards : Nat)
  /-- Return up to two modal graveyard cards. -/
  | returnUpToTwoGyModal
  /-- Spells described by `which` cost `{n}` less this turn.
  Card type `ty` is `.spellsCostLessThisTurn (.cardType ty) n`.
  Supertype `s` is `.spellsCostLessThisTurn (.supertype s) n`. -/
  | spellsCostLessThisTurn (which : SpellCostLess) (n : Nat)
  /-- A resolution that is not a spell shape. It does not play an extra land. -/
  | unrecognized
  /-- Each announced player target gains `n` life. -/
  | targetPlayersGainLife (n : Nat)
  /-- Affect the source if it is still on the battlefield. -/
  | onSource (action : PermanentAction)
  /-- Search for a basic land, put it onto the battlefield tapped, then shuffle. -/
  | searchBasicLand
  /-- Search for a card with this land type, put it into your hand, then shuffle. -/
  | searchLandTypeToHand (landType : String)
  /-- Exile the top card and grant permission to play it. -/
  | exileTop
  /-- Become this subtype with lands-you-control P/T. -/
  | becomeSubtypeWithLandsPT (subtype : CardSubtype)
  /-- Return the source from the graveyard to the battlefield tapped. -/
  | returnFromGraveyardTapped
  /-- Return the source from the graveyard to its owner's hand. -/
  | returnFromGraveyardToHand
  /-- Creatures you control get +P/+T until end of turn. -/
  | creaturesYouControlPump (power toughness : Int)
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
  | subtypesGainMenace (subtypes : Array CardSubtype)
  /-- Exile then return at the next end step. -/
  | exileThenReturnNextEnd
  /-- Search a basic tapped, then behold this subtype to untap it. -/
  | searchBasicBeholdSubtypeUntap (subtype : CardSubtype)
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
  /-- +1/+1 on each other permanent of this subtype. -/
  | plusOneOnEachOtherSubtype (subtype : CardSubtype) (n : Nat)
  /-- Take an extra turn after this one. Power-up abilities can't be activated during it. -/
  | extraTurn
  /-- X +1/+1 counters on the source. -/
  | plusOneX
  /-- Each opponent discards; +1/+1 on the source. -/
  | eachOppDiscardThenPlusOne
  /-- Look at the top `n`; you may put a card of one of these types onto the battlefield. -/
  | lookAtTopPutTypes (n : Nat) (types : Array CardSubtype)
  /-- Transform the source. -/
  | transform
  /-- Draw X cards. -/
  | drawX
  /-- Look at the top `n`; reveal an artifact to hand. -/
  | lookAtTopRevealArtifact (n : Nat)
  /-- Add one mana of any color, spendable only on this subtype's spells or sources. -/
  | addAnyColorSpendOnlySubtype (subtype : CardSubtype)
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
  /-- Create that many tokens of this kind (X = removed +1/+1 counters). -/
  | createTokensEqualRemovedPlusOnes (kind : TokenKind)
  /-- Exile the top X cards; you may play them this turn. -/
  | exileTopXPlayThisTurn
  /-- Target player draws `n` cards. -/
  | targetPlayerDraw (n : Nat)
  /-- Copy target activated or triggered ability you control from this source type. -/
  | copyControlledAbility (ty : CardType)
  /-- Create tokens equal to the number of permanents you control of this subtype. -/
  | createTokensEqualSubtype (kind : TokenKind) (subtype : CardSubtype)
  /-- For each kind of counter on target permanent or player, give another of that kind. -/
  | proliferateEachKind
  /-- If this Equipment isn't a creature, it becomes a 0/0 Construct Hero with flying. -/
  | equipmentBecomesConstructHero
  /-- Look at the top `n`; you may reveal a card of this subtype and put it into your hand. -/
  | lookAtTopRevealSubtype (n : Nat) (subtype : CardSubtype)
  /-- Mill `n`. You may put a card of this subtype or an enchantment into your hand. -/
  | millThenPutSubtypeOrEnchantment (n : Nat) (subtype : CardSubtype)
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
  | becomeTypes (types : Array CardSubtype) (power toughness : Int) (k : Keywords)
  /-- When you next cast an instant or sorcery with MV ≤ this's power this turn, copy it. -/
  | nextInstantSorceryCopyIfMvAtMostSourcePower
  /-- Harness this Infinity Stone. -/
  | harnessInfinityStone
  /-- Target permanent you control of this subtype connives. -/
  | targetSubtypeConnives (subtype : CardSubtype)
  /-- Mill `n` cards (CR 701.17). -/
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
  /-- Deal `n` damage to the target. If excess damage was dealt, empower Jace
  that much. -/
  | damageThenEmpowerExcess (n : Nat)
  /-- The first target deals damage equal to its power (or loyalty) to the
  second target, checked as the spell resolves (Compel Brutality). -/
  | firstDealsStatDamageToSecond (useLoyalty : Bool)
  /-- Exile the top card of your library. You may cast it. If you don't, this
  deals `n` damage to each opponent (Chandra, Torch of Defiance). -/
  | exileTopMayCastElseDamageOpponents (n : Nat)
  /-- You get an emblem with “Whenever you cast a spell, this emblem deals
  `n` damage to any target.” -/
  | emblemCastSpellDamage (n : Nat)
  /-
  Field-bearing constructors must keep a runtime tag ≤ 243.
  Nullary constructors may follow this block. Former `FraResolution`
  steps with arguments are inserted here so those tags stay in range.
  -/
  /-- This deals `n` damage to each player. -/
  | damageEachPlayer (n : Nat)
  /-- This deals `amount` damage to the permanent target at `index`. -/
  | damageSourceAt (index amount : Nat)
  /-- Put `n` +1/+1 counters on the permanent target at `index`. -/
  | plusOneAt (index n : Nat)
  /-- Return the target card from your graveyard to the battlefield with
  `plusOnes` additional +1/+1 counters. -/
  | returnFromGyToBattlefield (plusOnes : Nat)
  /-- Put `n` +1/+1 counters on each target. -/
  | plusOneOnEachTarget (n : Nat)
  /-- The target player reveals their hand; you choose a card from it
  (nonland permanent card if `permanentOnly`, else nonland card). They
  discard it. -/
  | revealHandDiscardNonland (permanentOnly : Bool)
  /-- This deals `n` damage to each creature and planeswalker your opponents
  control. -/
  | damageEachOppCreatureAndPlaneswalker (n : Nat)
  /-- The permanent target at `index` loses all abilities until end of turn. -/
  | loseAbilitiesAt (index : Nat)
  /-- The permanent at `fromIdx` deals damage equal to its power to the permanent at `toIdx`. -/
  | powerDamageFromTo (fromIdx toIdx : Nat)
  /-- Destroy the permanent target at `index`. -/
  | destroyAt (index : Nat)
  /-- Put a +1/+1 counter on each creature the player target at `index` controls. -/
  | plusOneOnCreaturesOfPlayerAt (index : Nat)
  /-- Exile the target. If its mana value was `n` or less, return it tapped
  under your control and exile it at the next end step. -/
  | exileReturnBrieflyIfMvAtMost (n : Nat)
  /-- Each player may discard their hand and draw `n` cards. -/
  | eachPlayerMayWheel (n : Nat)
  /-- Counter the target spell unless its controller pays `{n}`. -/
  | counterUnlessPays (n : Nat)
  /-- Deal `n` damage to the target. If that permanent would die this turn,
  exile it instead. -/
  | damageExileIfDies (n : Nat)
  /-- Mill `n` cards. You may put a permanent card from among them into your
  hand. You gain `life` life. -/
  | millMayPutPermanentGainLife (n life : Nat)
  /-- Return the source card from your graveyard to your hand, or to the
  battlefield (tapped if `tapped`, with `plusOnes` +1/+1 counters). -/
  | returnSourceFromGy (toHand : Bool) (tapped : Bool) (plusOnes : Nat)
  /-- You may pay `{n}`. When you do, for each opponent, destroy up to one
  target creature or planeswalker that player controls (Lich's Relic). -/
  | mayPayThenDestroyPerOpponent (n : Nat)
  /-- You may discard a card. When you do, this deals `n` damage to any target. -/
  | mayDiscardThenDamage (n : Nat)
  /-- The creature that triggered this deals `n` damage to each opponent. -/
  | causeDealsDamageToEachOpponent (n : Nat)
  /-- Mill `n` cards. When you do, return target land card from your
  graveyard to the battlefield tapped. -/
  | millThenReturnLandTapped (n : Nat)
  /-- The creature that triggered this gains `k` until end of turn. -/
  | causeGains (k : Keywords)
  /-- This deals `n` damage to the controller of the object that triggered it. -/
  | damageCauseController (n : Nat)
  /-- Remove up to `n` counters from the target. -/
  | removeUpToCounters (n : Nat)
  /-- Put `n` +1/+1 counters on the source. -/
  | plusOneOnSource (n : Nat)
  /-- You may pay `{pay}`. If you do, proliferate `times` times. -/
  | mayPayThenProliferate (pay times : Nat)
  /-- Proliferate `times` times (CR 701.34). -/
  | proliferate (times : Nat)
  /-- Put the reflexive triggered ability `kind` of an MSH card on the stack
  (“When you do, …”; MSH 359–369). `paid` is how many times its cost was
  paid. -/
  | queueMshReflexive (kind paid : Nat)
  /-- Resolve the reflexive triggered ability `kind` of an MSH card. -/
  | mshReflexive (kind paid : Nat)
  /-- Hawkeye's Trick Arrows: resolve the chosen modes (0 Net, 1 Explosive,
  2 Boomerang) in order. -/
  | hawkeyeArrows (modes : List Nat)
  /-- The creature that caused this ability gets +P/+T until end of turn. -/
  | causeGetsPump (power toughness : Int)
  /-- The source gains your choice of the keywords coded in `options` until
  end of turn. -/
  | chooseKeyword (options : List Nat)
  /-- This deals `n` damage to each creature except tokens you control. -/
  | damageEachCreatureExceptYourTokens (n : Nat)
  /-- This deals `n` damage to up to one target creature or planeswalker and
  `n` damage to target player. -/
  | damageUpToOneAndPlayer (n : Nat)
  /-- This deals `n` damage to any target. -/
  | damageAny (n : Nat)
  /-- Search for up to `n` land cards and put them onto the battlefield
  tapped. -/
  | searchLandsTapped (n : Nat)
  /-- Create `n` tapped Heartwood tokens. -/
  | tappedHeartwoods (n : Nat)
  /-- Put a reflexive “deal `n` damage to any target” ability on the stack. -/
  | reflexiveDamageAnyTarget (n : Nat)
  /-- Choose `count` modes of this triggered ability as it is put on the
  stack; the modes are `CardDef.fraTriggerModes`. -/
  | chooseTriggerModes (count : Nat)
  /-- A Reality Fracture Commander resolution. -/
  | frc (e : FrcEffect)
  /-
  Nullary steps. A constructor with fields appended after this point
  exceeds the runtime tag limit.
  -/
  /-- Return the targeted spell to its owner's hand. -/
  | returnTargetSpell
  /-- Each creature you control becomes prepared. -/
  | eachCreatureYouControlBecomesPrepared
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
  /-- Return the target permanent (or spell) to its owner's hand. -/
  | bounce
  /-- Exile the target permanent. -/
  | exileTarget
  /-- Destroy the target creature. If it wasn't attacking, its controller
  draws a card (Prophesied End). -/
  | destroyDrawIfNotAttacking
  /-- Return the target card from your graveyard to your hand. -/
  | returnFromGyToHand
  /-- Choose a creature type. Destroy all creatures that aren't of it. -/
  | destroyAllNotChosenType
  /-- Search for a planeswalker card, reveal it, shuffle, and put it on top. -/
  | searchPlaneswalkerToTop
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
  /-- Until end of turn, whenever you tap a Mountain for mana, add an
  additional {R}. -/
  | mountainsAddExtraRed
  /-- Search for a land card, put it into your graveyard, then shuffle. -/
  | searchLandToGraveyard
  /-- Counter the target spell. -/
  | counterTarget
  /-- Destroy the target permanent. -/
  | destroyTarget
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
  /-- The target opponent reveals their hand; you exile a nonland card from it
  until the source leaves the battlefield (Null Summoner). -/
  | exileFromHandUntilLeaves
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
  /-- Untap the source. -/
  | untapSource
  /-- For each opponent, tap up to one target creature that player controls;
  put a stun counter on each. -/
  | tapAndStunPerOpponent
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
  /-- The source Vehicle becomes an artifact creature until end of turn
  (crew, CR 702.122). -/
  | becomeArtifactCreatureUntilEot
  /-- Extort: you may pay {W/B}. If you do, each opponent loses 1 life and
  you gain that much life (CR 702.101). -/
  | extort
  /-- Copy the cards exiled to pay this boast activation; you may cast up to
  three of the copies without paying their mana costs (Baron Helmut Zemo). -/
  | zemoBoastCopies
  /-- Copy the source spell X times; you may choose new targets for the
  copies (Photon Blast Barrage). -/
  | copySourceSpellXTimes
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
  /-- Destroy each legal target. -/
  | destroyEachTarget
  /-- Return the target card from your graveyard to the battlefield tapped. -/
  | returnFromGyToBattlefieldTapped
  /-- Search for a basic land card and put it onto the battlefield tapped. -/
  | searchBasicLandTapped
  /-- Search for an enchantment card, reveal it, and put it into your hand. -/
  | searchEnchantmentToHand
  /-- Each opponent sacrifices a creature of their choice. -/
  | eachOpponentSacrificesCreature
  /-- Draw a card; then put a +1/+1 counter on the creature that triggered
  this for each card you've discarded this turn (Jiang Yanggu, Alone). -/
  | drawThenCountersPerDiscard
  /-- If seven or more cards are in your graveyard, sacrifice the source, deal
  2 damage to each opponent, and gain 2 life (Eye of Jace). -/
  | eyeOfJaceCheck
  /-- Put a reflexive “for each opponent, destroy up to one target creature or
  planeswalker that player controls” ability on the stack. -/
  | reflexiveDestroyPerOpponent
  /-- Put a reflexive “return target land card from your graveyard to the
  battlefield tapped” ability on the stack. -/
  | reflexiveReturnLandTapped
deriving Repr, Inhabited, BEq

namespace Resolution

/-- A step that used to be a `FraResolution` constructor. -/
def isFra : Resolution → Bool
  | .bounce .. | .exileTarget .. | .destroyDrawIfNotAttacking .. | .damageEachPlayer .. => true
  | .damageSourceAt .. | .plusOneAt .. | .returnFromGyToBattlefield .. | .returnFromGyToHand .. => true
  | .destroyAllNotChosenType .. | .searchPlaneswalkerToTop .. | .plusOneOnEachTarget .. | .returnAllNonlandPermanentsFromGy .. => true
  | .drawMilledThisTurn .. | .exileAllCreaturesEmpower .. | .drawGreatestPowerLoseLife .. | .revealHandDiscardNonland .. => true
  | .discardHand .. | .drawPerCreatureYouControl .. | .extrapolate .. | .sphinxsApproach .. => true
  | .plusOneOnWizardTokensExceptRecent .. | .damageEachOppCreatureAndPlaneswalker .. | .loseAbilitiesAt .. | .powerDamageFromTo .. => true
  | .clashOfElements .. | .entrustTheSpark .. | .plusOnePerThreeGraveyardOnRecentIfFromGy .. | .grantHasteToRecentTokens .. => true
  | .drawOneOrTwoIfNotFromHand .. | .destroyAt .. | .plusOneOnCreaturesOfPlayerAt .. | .exileReturnBrieflyIfMvAtMost .. => true
  | .eachPlayerMayWheel .. | .mountainsAddExtraRed .. | .searchLandToGraveyard .. | .counterTarget .. => true
  | .counterUnlessPays .. | .destroyTarget .. | .damageExileIfDies .. | .millMayPutPermanentGainLife .. => true
  | .untapAllLandsYouControl .. | .blink .. | .mayMovePlusOneToEachOther .. | .empowerJacePerCreature .. => true
  | .tapEnchantedUnprepare .. | .ownerPutsOnTopOrBottom .. | .drawTwoDiscardTwoStun .. | .copyTokenOfSourceIfNotToken .. => true
  | .returnSourceFromGy .. | .mayPayThenDestroyPerOpponent .. | .damageX .. | .creaturesGetPowerPerArtifact .. => true
  | .searchCardThenDiscardRandom .. | .grantFlashbackUntilEot .. | .mayDiscardThenDamage .. | .maySearchLandsEqualDamage .. => true
  | .maySearchBasicLandTapped .. | .returnCauseTapped .. | .sacrificeSource .. | .causeDealsDamageToEachOpponent .. => true
  | .exileFromHandUntilLeaves .. | .millThenReturnLandTapped .. | .maySacrificeLandForHeartwoods .. | .uldarosCopies .. => true
  | .exileCardFromGraveyard .. | .copyCauseSpell .. | .eyeOfJace .. | .loyaltyOnEachPlaneswalkerYouControl .. => true
  | .causeGains .. | .untapSource .. | .tapAndStunPerOpponent .. | .damageCauseController .. => true
  | .removeUpToCounters .. | .maySacrificeThenEdict .. | .sourceGetsCausePower .. | .jiangYangguAlone .. => true
  | .kothGeomancer .. | .fblthpSearch .. | .untapAllTokensYouControl .. | .mayDiscardThenSearchEnchantment .. => true
  | .firstFightsSecond .. | .minusOnesPerOpponent .. | .drawPerColorAmongOtherArtifacts .. | .untapUnblockable .. => true
  | .minusPowerPerGraveyard .. | .plusOneOnEachCreatureYouControl .. | .plusOneOnSource .. | .sourceFightsTarget .. => true
  | .exileUntilSourceLeaves .. | .beastToken .. | .putCauseCountersOnSource .. | .mayMoveSourceCountersToTarget .. => true
  | .mayPayThenProliferate .. | .proliferate .. | .becomeArtifactCreatureUntilEot .. | .extort .. => true
  | .queueMshReflexive .. | .mshReflexive .. | .hawkeyeArrows .. | .zemoBoastCopies .. => true
  | .copySourceSpellXTimes .. | .plusOnesEqualToHandOnEachCreature .. | .damageEqualSourcePower .. | .returnSourceToHand .. => true
  | .sarumanExileCopyMayCast .. | .causeGetsPump .. | .attackersOfPlayerGetTwoTwoTrample .. | .emrakulGrantMana .. => true
  | .nextSpellCantBeCountered .. | .identityEcho .. | .destroyDrawIfLegendaryEnchantment .. | .chooseKeyword .. => true
  | .graveyardCardToLibraryBottom .. | .destroyAllCreatures .. | .ownerShufflesIntoLibrary .. | .grantCombatDamageDrawTwo .. => true
  | .sourceGetsPowerPerArtifact .. | .pumpPerArtifact .. | .plusOneOnEachWithPlusOne .. | .bounceEachTarget .. => true
  | .surveilReturnNoncreatureNonland .. | .addBlueNoncreatureOnly .. | .tapAndStunX .. | .emblemDrawOnCast .. => true
  | .empowerJacePerIsland .. | .attackersGetMinusFiveUntilYourTurn .. | .exileOpponentLibrariesButBottom .. | .minusFourMinusOneUntilYourTurn .. => true
  | .eachPlayerSacrificesThenBeast .. | .eachOpponentDiscardsTwoDrawPerShort .. | .damageEachCreatureExceptYourTokens .. | .emblemCreaturesGetTwoTwo .. => true
  | .untapTargets .. | .attackersGetTwoTwoTrampleUntilYourTurn .. | .plusOnePerLand .. | .maySacrificeCreatureForBeast .. => true
  | .damageUpToOneAndPlayer .. | .destroyEachTarget .. | .damageAny .. | .returnFromGyToBattlefieldTapped .. => true
  | .searchBasicLandTapped .. | .searchLandsTapped .. | .searchEnchantmentToHand .. | .tappedHeartwoods .. => true
  | .eachOpponentSacrificesCreature .. | .drawThenCountersPerDiscard .. | .eyeOfJaceCheck .. | .reflexiveDamageAnyTarget .. => true
  | .reflexiveDestroyPerOpponent .. | .reflexiveReturnLandTapped .. | .chooseTriggerModes .. | .frc .. => true
  | _ => false

/-- Oracle wording for a former `FraResolution` step. `none` for every other step. -/
def fraPhrase? (r : Resolution) (noun : String) : Option String :=
  match r with
  | .bounce => some (s!"Return {noun} to its owner's hand")
  | .exileTarget => some (s!"Exile {noun}")
  | .destroyDrawIfNotAttacking => some (s!"Destroy {noun}. If it wasn't attacking, its controller draws a card")
  | .damageEachPlayer n => some (s!"This deals {n} damage to each player")
  | .damageSourceAt _ n => some (s!"This deals {n} damage to {noun}")
  | .plusOneAt _ n => some (s!"Put {plusOnePlusOneCountersPhrase n} on {noun}")
  | .returnFromGyToBattlefield n => some (if n == 0 then s!"Return {noun} to the battlefield"
    else s!"Return {noun} to the battlefield with an additional +1/+1 counter on it")
  | .returnFromGyToHand => some (s!"Return {noun} to your hand")
  | .destroyAllNotChosenType => some ("Choose a creature type. Destroy all creatures that aren't of the chosen type")
  | .searchPlaneswalkerToTop => some ("Search your library for a planeswalker card, reveal it, then shuffle and put that card on top")
  | .plusOneOnEachTarget n => some (s!"Put {plusOnePlusOneCountersPhrase n} on each of {noun}")
  | .returnAllNonlandPermanentsFromGy => some ("Return all nonland permanent cards from your graveyard to the battlefield")
  | .drawMilledThisTurn => some ("Draw X cards, where X is the number of cards that were put into target player's graveyard from their library this turn")
  | .exileAllCreaturesEmpower => some ("Exile all creatures. Empower Jace X, where X is the number of creatures exiled this way")
  | .drawGreatestPowerLoseLife => some ("Draw cards equal to the greatest power among creatures you control. You lose life equal to the number of cards drawn this way")
  | .revealHandDiscardNonland permanentOnly => some (let what := if permanentOnly then "nonland permanent card" else "nonland card"
    s!"{capitalizeAscii noun} reveals their hand. You choose a {what} from it. That player discards that card")
  | .discardHand => some ("Discard your hand")
  | .drawPerCreatureYouControl => some ("Draw a card for each creature you control")
  | .extrapolate => some ("You may reveal exactly two cards you own with different names from outside the game. An opponent chooses one of them. You put that card into your hand")
  | .sphinxsApproach => some ("You may exile this spell and four cards named Sphinx's Approach from your graveyard. If you do, search your library for a Sphinx creature card, put it onto the battlefield, then shuffle")
  | .plusOneOnWizardTokensExceptRecent => some ("Put a +1/+1 counter on each other Wizard token you control")
  | .damageEachOppCreatureAndPlaneswalker n => some (s!"This deals {n} damage to each creature and planeswalker your opponents control")
  | .loseAbilitiesAt _ => some (s!"{capitalizeAscii noun} loses all abilities until end of turn")
  | .powerDamageFromTo _ _ => some ("Target creature you control deals damage equal to its power to that permanent")
  | .clashOfElements => some ("Choose target nonland permanent. Its owner may put it on top of their library. If they do, this deals 2 damage to them. If they didn't put the card on top of their library, they put it on the bottom")
  | .entrustTheSpark => some ("You may sacrifice a planeswalker. If you do, search your library for a planeswalker card, put it onto the battlefield, then shuffle")
  | .plusOnePerThreeGraveyardOnRecentIfFromGy => some ("If this spell was cast from a graveyard, put a +1/+1 counter on each of them for every three cards in your graveyard")
  | .grantHasteToRecentTokens => some ("It gains haste until end of turn")
  | .drawOneOrTwoIfNotFromHand => some ("Draw a card. If this spell wasn't cast from your hand, draw two cards instead")
  | .destroyAt _ => some (s!"Destroy {noun}")
  | .plusOneOnCreaturesOfPlayerAt _ => some ("Put a +1/+1 counter on each creature target player controls")
  | .exileReturnBrieflyIfMvAtMost n => some (s!"Exile {noun}. If that permanent's mana value was {n} or less, return it to the battlefield tapped under your control. Exile it at the beginning of the next end step")
  | .eachPlayerMayWheel n => some (s!"Each player may discard their hand and draw {englishNumber n} cards")
  | .mountainsAddExtraRed => some ("Until end of turn, whenever you tap a Mountain for mana, add an additional {R}")
  | .searchLandToGraveyard => some ("Search your library for a land card, put it into your graveyard, then shuffle")
  | .counterTarget => some (s!"Counter {noun}")
  | .counterUnlessPays n => some (s!"Counter {noun} unless its controller pays \{{n}}")
  | .destroyTarget => some (s!"Destroy {noun}")
  | .damageExileIfDies n => some (s!"This deals {n} damage to {noun}. If that permanent would die this turn, exile it instead")
  | .millMayPutPermanentGainLife n l => some (s!"Mill {englishNumber n} cards. You may put a permanent card from among them into your hand. You gain {l} life")
  | .chooseTriggerModes n => some (if n == 2 then "choose two" else "choose one")
  | .minusPowerPerGraveyard => some (s!"{capitalizeAscii noun} gets -X/-0 until end of turn, where X is the number of cards in your graveyard")
  | r => if r.isFra then some "" else none

end Resolution

namespace TriggeredAbility

abbrev TriggerResolution := Resolution

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
   .dealDamage (.fixed 2) (.player (.target .opponent)),
   .sequence [.discard, .draw (.fixed 1)]]

/-- Which reflexive `follow` queues as a printed MSH ability. Any other
resolution is `.none`; the caller still puts that follow-up on the stack. -/
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
  | .cantBeBlocked => .cant (.beBlocked (affectedWho who))
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
    | .targetWhileSource => .target .whileSource
  affectedWho : TriggerAffected → ObjectSelector
    | .target => .target
    | .source => .source
    | .enchanted => .enchanted
    | .targetWhileSource => .target .whileSource
  tapWho : TriggerAffected → ObjectSelector
    | .target => .target
    | .source => .source
    | .enchanted => .enchantedWhileSource
    | .targetWhileSource => .target .whileSource
  loseWho : TriggerAffected → ObjectSelector
    | .target => .target
    | .source => .source
    | .enchanted => .enchanted
    | .targetWhileSource => .target .whileSource

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

/-- A spell step as the same step in this vocabulary.
Shapes whose spell constructor is a different step are rewritten.
Every other shape passes through. -/
def ofSpell : TriggerResolution → TriggerResolution
  | .sequence rs => .sequence (rs.map ofSpell)
  | .onPermanent a => ofPermanent a
  | .creaturesPump p t .youControl => .pump (.fixed p) (.fixed t) .creaturesYouControl
  | .teamGain k => .grant (.keywords k) .creaturesYouControl
  | .plusOneOnEachYouControl n .each =>
    .putCounters (.ofKind .plusOnePlusOne n) .youControl
  | .plusOneOnEachYouControl n .eachOther =>
    .putCounters (.ofKind .plusOnePlusOne n) .eachOther
  | .plusOneOnCreatureN n =>
    .putCounters (.ofKind .plusOnePlusOne n) .permanent
  | .destroyUpToOneNonland => .destroy .target
  | .mutualFight .upToOne => .fight .announced .upToOneOther
  | .mutualFight .both => .fight .announced .mutual
  | .createGalactus => .createTokens .treasure (.fixed 1) false .galactus
  | .nextFreeRGCreature =>
    .mayCast .nextRedOrGreenCreature .unlimited .withoutPaying
  | .mayDrawPerArtifactOppsDraw ty =>
    .may (.draw (.perControlled ty)) (.draw (.fixed 1) (who := .eachOpponent)) .ifYouDo
  | .mayPutHeroMvOrDraw n subtype =>
    .may (.put (.creatureFromHand subtype n)) (.draw (.fixed 1))
  | .spellsCostLessThisTurn which n => .spellsCostLess which (.fixed n)
  | r => r

end TriggerResolution

end TriggeredAbility

/-- How a spell resolves (CR 608). The same inductive as a trigger resolution. -/
abbrev SpellResolution := Resolution

namespace SpellResolution

-- Constructors stay addressable as `SpellResolution.draw` and the rest.
export Resolution (
  pump
  dealDamage
  scry
  draw
  searchLibrary
  discard
  pay
  putCounters
  returnToHand
  queueReflexive
  sacrifice
  lose
  cant
  becomeArtifact
  becomePrepared
  setBasePT
  putOnLibrary
  dividedDamage
  sequence
  may
  gainLife
  exile
  put
  removeCounters
  tap
  untap
  destroy
  recruit
  amass
  createTokens
  attach
  addMana
  becomePT
  lookAtTopRevealTypes
  gainControl
  honeEachEquipment
  cascade
  noteResolveThisTurn
  «if»
  ifElse
  or
  chooseModes
  mayCast
  grant
  revealLibrary
  mill
  copySelfNonlegendary
  ringTempts
  spellsCostLess
  investigate
  connive
  fight
  revealFromHand
  surveil
  empowerJace
  prepareSource
  markRecentTokensAttacking
  additionalCombatPhase
  becomeBear
  loseLife
  grantPlayNotedUntilNextTurn
  winTheGame
  shuffleSource
  armSurveilReturnLifeGained
  becomeCopy
  retargetCause
  copyCause
  extraLand
  mutualFight
  onPermanent
  creaturesPump
  exileGraveyardCreaturesGrantCast
  tapTargets
  counter
  unlessPays
  counterExilePermanentMayCast
  attachEquipment
  exchangeControl
  countersOnCreatureTargets
  returnTargetToHand
  teamGain
  searchCard
  replace
  addRedPerOppArtifacts
  chooseTypeReturnOthers
  drawEqualToughnessThenPutCreatures
  millThenPut
  exileThenReturnYouControl
  addFourManaDragonSpells
  exileAttackersSearchBasics
  exileTopPlayIfYouControlSubtype
  playersCantCastThisTurn
  exileTopXOppPlayForLife
  riddlesInTheDark
  supperForSpiders
  eaglesAreComing
  lookAtTopLandsGainLife
  gainControlOppArtifacts
  phaseOutKicker
  dealDamageToControllerOfTarget
  exileCreatureMvAtMostOrAnyIfTeamwork
  returnGyCreatureMvAtMostOrAny
  revealTopPutCreatures
  returnOneOrTwoNonlands
  targetPlayerInvestigates
  onCreatureAmongTargets
  dealDamageToEachCreature
  returnGySubtypeToHand
  becomeArtifactCreature44Flying
  discardTwoUnlessArtifact
  plusOneOnEachYouControl
  plusOneOnCreatureN
  exileTopPlayUntilNext
  destroyUpToOneNonland
  createGalactus
  worldsWithinWorlds
  exileHandDrawPlayUntilNext
  copyNontokenCreaturesYouControl
  gainControlUntilEotOrNextIfVillain
  millThenPutPermanentGainLife
  searchLibraryOrGyArtifactCreatureX
  gainLifeSearchBasicPlusOne
  nextFreeRGCreature
  ownerPutsLibraryThenConnive
  copyThisSpellXTimesThenDamage
  mayDrawPerArtifactOppsDraw
  mayPutHeroMvOrDraw
  maySacArtifactOrDiscardDraw
  returnUpToTwoGyModal
  spellsCostLessThisTurn
  unrecognized
  targetPlayersGainLife
)


/-- The “if …” clause for `cond`, without a following resolution. -/
private def ifClause (cond : TriggeredAbility.ConditionSelector) (noun : String) : String :=
  match cond with
  | .subtype subtype => s!"if {noun} is {indefinite subtype} {subtype}"
  | .mvAtMost n => s!"if that spell's mana value was {n} or less"
  | .castFromGraveyard => "if this spell was cast from a graveyard"
  | .teamwork => "if this spell was cast using teamwork"
  | .giftPromised => "if the gift was promised"
  | _ => "if that is true"

/-- The “if … would …” clause for `what`, without the replacement. -/
private def replaceWhatClause (what : ReplaceEvent) (noun : String) : String :=
  match what with
  | .diesThisTurn => s!"if {noun} would die this turn"

/-- What happens instead of `what`. -/
private def replaceInsteadClause (instead : ReplaceInstead) : String :=
  match instead with
  | .exile => "exile it instead"

/-- Drop one trailing period so a following clause can continue the sentence. -/
private def trimPeriod (s : String) : String :=
  if s.endsWith "." then (s.dropEnd 1).toString else s

/-- One step, not a sequence or a choice. Sequence and `or` phrasing stay
outside this match so the constructor splitter is not recursive. -/
private def phraseOne (r : SpellResolution) (noun : String) : String :=
  match r with
  | .fight _ (.timesPower 1) =>
    "target creature you control deals damage equal to its power to target creature an opponent controls"
  | .fight _ (.timesPower k) =>
    s!"Target creature you control deals damage equal to {timesPhrase k} its power to target creature an opponent controls."
  | .mutualFight .both =>
    "target creature you control fights target creature an opponent controls"
  | .mutualFight .upToOne =>
    "target creature you control fights up to one other target creature"
  | .extraLand => "you may play an additional land this turn"
  | .unrecognized => "this effect does nothing"
  | .sequence _ => ""
  | .discard (.cards n) => s!"discard {cardPhrase n}"
  | .loseLife (.fixed n) .you => s!"lose {n} life"
  | .loseLife (.fixed n) .player => s!"{noun} loses {n} life"
  | .loseLife (.fixed n) (.controller .target) => s!"its controller loses {n} life"
  | .loseLife (.fixed n) .eachOpponent => s!"each opponent loses {n} life"
  | .gainLife (.fixed n) => s!"you gain {n} life"
  | .targetPlayersGainLife n => s!"Target player gains {n} life"
  | .surveil (.fixed n) => s!"surveil {n}"
  | .teamGain k => s!"creatures you control gain {k.joinedAnd} until end of turn"
  | .returnTargetToHand .spell => s!"return {noun} to its owner's hand"
  | .returnTargetToHand .graveyard => s!"return up to one {noun} to your hand"
  | .onPermanent action => PermanentAction.toNotation action noun
  | .creaturesPump p t .youControl =>
    s!"creatures you control get {signedStat p}/{signedStat t} until end of turn"
  | .creaturesPump p t .all =>
    s!"all creatures get {signedStat p}/{signedStat t} until end of turn"
  | .creaturesPump p t .ofTargetPlayer =>
    s!"creatures {noun} controls get {signedStat p}/{signedStat t} until end of turn"
  | .exileGraveyardCreaturesGrantCast ty =>
    s!"exile all {ty.oracleWord} cards from target player's graveyard. You may cast spells from among those cards for as long as they remain exiled, and mana of any type can be spent to cast them"
  | .draw (.fixed n) .you => s!"draw {cardPhrase n.toNat}"
  | .draw (.fixed n) .player => s!"{noun} draws {cardPhrase n.toNat}"
  | .scry (.fixed n) => s!"scry {n}"
  | .tapTargets => "tap one or two target creatures"
  | .counter => s!"counter {noun}"
  | .unlessPays r n =>
    let base := phraseOne r noun
    let base := if base.endsWith "." then (base.dropEnd 1).toString else base
    if base.isEmpty then s!"unless its controller pays \{{n}}"
    else s!"{base} unless its controller pays \{{n}}"
  | .counterExilePermanentMayCast =>
    s!"counter {noun}. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled"
  | .or _ => ""
  | .attachEquipment =>
    "attach an Equipment you control to it"
  | .may r _ _ =>
    let base := phraseOne r noun
    let base := if base.endsWith "." then (base.dropEnd 1).toString else base
    let base := if base.startsWith "you " then (base.drop 4).toString else base
    if base.isEmpty then "you may" else s!"you may {base}"
  | .recruit => "recruit"
  | .«if» cond r =>
    let base := trimPeriod (phraseOne r noun)
    let cond := ifClause cond noun
    if base.isEmpty then cond else s!"{cond}, {base}"
  | .ifElse .teamwork (.onPermanent (.dealDamage teamworkN)) (.onPermanent (.dealDamage n)) =>
    s!"deals {n} damage to target attacking or blocking creature. If this spell was cast using teamwork, it deals {teamworkN} damage to that creature instead"
  | .ifElse .teamwork (.unlessPays .counter teamworkN) (.unlessPays .counter n) =>
    s!"counter target spell unless its controller pays \{{n}}. Counter that spell unless its controller pays \{{teamworkN}} instead if this spell was cast using teamwork"
  | .ifElse cond whenTrue whenFalse =>
    let no := trimPeriod (phraseOne whenFalse noun)
    let yes := trimPeriod (phraseOne whenTrue noun)
    let cond := ifClause cond noun
    if no.isEmpty then
      if yes.isEmpty then cond else s!"{cond}, {yes}"
    else if yes.isEmpty then no
    else s!"{no}. {capitalizeAscii cond}, {yes} instead"
  | .exchangeControl =>
    "exchange control of two target nonland permanents that share a card type"
  | .countersOnCreatureTargets kind n .each =>
    s!"put {kind.countersPhrase n} on up to one target creature"
  | .countersOnCreatureTargets kind n .firstYouControl =>
    s!"put {kind.countersPhrase n} on target creature you control"
  | .amass (.fixed n) subtype =>
    s!"amass {pluralizeName subtype} {n}"
  | .searchCard s ty .youToHand =>
    searchLibraryToHandPhrase s!"a {s.oracleWord} {ty.oracleWord} card"
  | .searchCard s ty .ownerMayToBattlefield =>
    s!"its controller may search their library for a {s.oracleWord} {ty.oracleWord} card, put it onto the battlefield tapped, then shuffle"
  | .dealDamageToEachCreature _ .opponentsControl .otherSpellsManaValue =>
    "deals damage to each creature your opponents control equal to the total mana value of other spells you've cast this turn"
  | .dealDamageToEachCreature n .each .fixed =>
    s!"deals {n} damage to each creature"
  | .dealDamageToEachCreature n .opponentsControl .fixed =>
    s!"deals {n} damage to each creature your opponents control"
  | .dealDamageToEachCreature n (.nonSubtype subtype) .fixed =>
    s!"deals {n} damage to each non-{subtype} creature"
  | .dealDamageToEachCreature _ .each .otherSpellsManaValue =>
    "deals damage to each creature equal to the total mana value of other spells you've cast this turn"
  | .dealDamageToEachCreature _ (.nonSubtype subtype) .otherSpellsManaValue =>
    s!"deals damage to each non-{subtype} creature equal to the total mana value of other spells you've cast this turn"
  | .replace what instead =>
    s!"{replaceWhatClause what noun}, {replaceInsteadClause instead}"
  | .addRedPerOppArtifacts ty =>
    s!"add {"{R}"} for each {ty.oracleWord} your opponents control"
  | .chooseTypeReturnOthers =>
    "choose a creature type. Return all creatures that aren't of the chosen type to their owners' hands"
  | .drawEqualToughnessThenPutCreatures =>
    "draw cards equal to the greatest toughness among creatures you control, then put any number of creature cards from your hand onto the battlefield"
  | .millThenPut n (.oneOf a b) =>
    s!"mill {n} cards, then put {indefinite a.oracleWord} {a.oracleWord} or {b.oracleWord} card from among them into your hand"
  | .millThenPut n (.upTo max ty) =>
    s!"mill {n} cards, then put up to {englishNumber max} {ty.oracleWord} cards from among them into your hand"
  | .millThenPut n (.allOf a b) =>
    s!"mill {n} cards, then put all {a.oracleWord} and {b.oracleWord} cards from among them into your hand"
  | .exileThenReturnYouControl =>
    "exile two target creatures and/or lands you control, then return them to the battlefield under their owner's control"
  | .addFourManaDragonSpells n subtype =>
    s!"add {englishNumber n} mana in any combination of colors. Spend this mana only to cast {subtype} spells"
  | .exileAttackersSearchBasics =>
    s!"exile all attacking creatures {noun} controls. That player may search their library for that many basic land cards, put those cards onto the battlefield tapped, then shuffle"
  | .exileTopPlayIfYouControlSubtype n subtype =>
    s!"look at the top {n} cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a {subtype}"
  | .playersCantCastThisTurn =>
    "players can't cast spells this turn"
  | .exileTopXOppPlayForLife =>
    "exile the top X cards of target opponent's library. You may play those cards this turn. If you cast a spell this way, pay life equal to its mana value rather than pay its mana cost"
  | .riddlesInTheDark n =>
    s!"look at the top {englishNumber n} cards of your library and separate them into a face-down pile and a face-up pile. An opponent chooses one of the piles. Put that pile into your hand and the other into your graveyard"
  | .supperForSpiders =>
    "put onto the battlefield under your control all creature cards in your opponents' graveyards that were put there from the battlefield this turn. They are Food artifacts with \"{2}, {T}, Sacrifice this artifact: You gain 3 life.\""
  | .eaglesAreComing =>
    "choose target creature you own. If this spell was kicked, instead choose any number of target creatures you own. Return each chosen creature to your hand. At the beginning of the next upkeep, create a 4/4 white Bird Soldier creature token with flying for each creature returned to your hand this way"
  | .lookAtTopLandsGainLife n life =>
    s!"look at the top {n} cards of your library, put any number of land cards from among them onto the battlefield tapped, then shuffle. You gain {life} life"
  | .gainControlOppArtifacts =>
    "for each opponent, gain control of up to one target artifact that player controls"
  | .phaseOutKicker =>
    "target creature phases out. If this spell was kicked, each creature target player controls phases out instead"
  | .dealDamageToControllerOfTarget n =>
    s!"it also deals {n} damage to that creature's controller"
  | .exileCreatureMvAtMostOrAnyIfTeamwork n life =>
    s!"exile target creature with mana value {n} or less. If this spell was cast using teamwork, instead exile target creature and you gain {life} life"
  | .returnGyCreatureMvAtMostOrAny n =>
    s!"choose target creature card in your graveyard with mana value {n} or less. If this spell was cast using teamwork, instead choose target creature card in your graveyard. Return the chosen card to the battlefield"
  | .revealTopPutCreatures n =>
    s!"reveal the top {n} cards of your library. You may put a creature card from among them onto the battlefield. If this spell was cast using teamwork, put any number of creature cards from among them onto the battlefield instead. Put the rest into your graveyard"
  | .createTokens kind .chosenX _ _ _ _ =>
    s!"create X {kind.pluralNoun}"
  | .createTokens kind (.perSubtype subtype) _ _ _ _ =>
    s!"Create a {kind.oracleNoun} for each {subtype} you control"
  | .createTokens kind (.fixed n) _ .kind .you _ =>
    TokenKind.createPhrase kind n.toNat
  | .createTokens kind (.fixed n) _ .kind .player _ =>
    s!"{noun} creates {TokenKind.createdTokensPhrase kind n.toNat}"
  | .returnOneOrTwoNonlands =>
    "return one or two target nonland permanents to their owners' hands"
  | .targetPlayerInvestigates =>
    "target player investigates"
  | .onCreatureAmongTargets action =>
    PermanentAction.toNotation action "target creature"
  | .returnGySubtypeToHand subtype =>
    s!"return target {subtype} card from your graveyard to your hand"
  | .becomeArtifactCreature44Flying p t kw =>
    s!"until end of turn, {noun} becomes an artifact creature with base power and toughness {p}/{t} and gains {kw}"
  | .discardTwoUnlessArtifact n ty =>
    s!"discard {englishNumber n} cards unless you discard {indefinite ty.oracleWord} {ty.oracleWord} card"
  | .plusOneOnEachYouControl n .each =>
    s!"put {plusOnePlusOneCountersPhrase n} on each creature you control"
  | .plusOneOnEachYouControl n .eachOther =>
    s!"put {plusOnePlusOneCountersPhrase n} on each other creature you control"
  | .plusOneOnCreatureN n =>
    s!"put {plusOnePlusOneCountersPhrase n} on {noun}"
  | .exileTopPlayUntilNext _ =>
    s!"exile the top card of your library. {playThatCardUntilNextTurnPhrase}"
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
  | .mayDrawPerArtifactOppsDraw ty =>
    s!"You may draw a card for each {ty.oracleWord} you control. If you do, each opponent draws a card"
  | .mayPutHeroMvOrDraw n subtype =>
    s!"You may put {indefinite subtype} {subtype} creature card with mana value {n} or less from your hand onto the battlefield. If you don't, draw a card"
  | .maySacArtifactOrDiscardDraw cards =>
    s!"You may sacrifice an artifact or discard a card. If you do, draw {cardPhrase cards}."
  | .returnUpToTwoGyModal =>
    "Choose up to two. Return those cards from your graveyard to your hand. • Target artifact card. • Target creature card. • Target enchantment card. • Target land card."
  | .spellsCostLessThisTurn (.cardType ty) n =>
    s!"{ty} spells you cast this turn cost \{{n}} less to cast"
  | .spellsCostLessThisTurn (.supertype s) n =>
    s!"{s} spells you cast this turn cost \{{n}} less to cast"
  | _ => ""

/-- Nested `sequence` constructors, left to right. An `or` stays one step:
flattening it would resolve every alternative. -/
def flatten : SpellResolution → List SpellResolution
  | .sequence rs => rs.flatMap flatten
  | r => [r]

/-- Printed wording of a flat sequence. Known shapes keep their Oracle text;
other sequences join each step. -/
private def phraseSequence (rs : List SpellResolution) (noun : String) : String :=
  match rs with
  | [.draw (.fixed n) .you, .discard (.cards 1)] =>
    s!"draw {cardPhrase n.toNat}, then discard a card"
  | [.draw (.fixed cards) .you, .loseLife (.fixed life) .you] =>
    s!"you draw {cardPhrase cards.toNat} and lose {life} life"
  | [.draw (.fixed cards) .player, .loseLife (.fixed life) .player] =>
    s!"{noun} draws {cardPhrase cards.toNat} and loses {life} life"
  | [.onPermanent .destroy, .loseLife (.fixed n) (.controller .target)] =>
    s!"destroy {noun}. Its controller loses {n} life"
  | [.returnTargetToHand .spell, .draw (.fixed 1)] =>
    s!"return {noun} to its owner's hand. Draw a card"
  | [.counter, .«if» (.mvAtMost n) .recruit] =>
    s!"counter {noun}. If that spell's mana value was {n} or less, recruit"
  | [.returnTargetToHand .graveyard, .amass (.fixed n) subtype] =>
    s!"return up to one {noun} to your hand. Amass {pluralizeName subtype} {n}"
  | [.draw (.fixed 1), .loseLife (.fixed 1), .amass (.fixed n) subtype] =>
    s!"you draw a card and lose 1 life. Amass {pluralizeName subtype} {n}"
  | [.createTokens kind (.fixed n) _ .kind .you _, .creaturesPump p t .youControl] =>
    let tokens := capitalizeAscii (TokenKind.createPhrase kind n.toNat)
    s!"{tokens}, then creatures you control get {signedStat p}/{signedStat t} until end of turn."
  | [.onPermanent .destroy, .gainLife (.fixed n)] =>
    s!"destroy {noun}. You gain {n} life"
  | [.onPermanent .destroy, .surveil (.fixed 1)] =>
    s!"destroy {noun}. Surveil 1"
  | [.onPermanent .tap, .scry (.fixed scryN), .draw (.fixed drawN)] =>
    s!"tap {noun}. Scry {scryN}. Draw {cardPhrase drawN.toNat}"
  | [.onPermanent (.pump p t), .draw (.fixed 1)] =>
    let tStr := if t == 0 && p < 0 then "-0" else signedStat t
    s!"Target creature gets {signedStat p}/{tStr} until end of turn.\nDraw a card."
  | [.onPermanent (.plusOne 1), .onPermanent (.grantKeywords k)] =>
    if k == Keyword.lifelink.merge Keyword.indestructible then
      "put a +1/+1 counter on target creature. It gains lifelink and indestructible until end of turn"
    else
      String.intercalate ". " (rs.map (phraseOne · noun))
  | [.onPermanent (.grantKeywords k), .draw (.fixed 1)] =>
    if k == Keyword.vigilance.merge Keyword.cantBeBlocked then
      s!"{noun} gains vigilance until end of turn and can't be blocked this turn"
    else
      String.intercalate ". " (rs.map (phraseOne · noun))
  | [.creaturesPump p t .youControl, .teamGain k] =>
    s!"Creatures you control get {signedStat p}/{signedStat t} and gain {k.joinedAnd} until end of turn"
  | [.onPermanent .untap, .onPermanent (.pump p t), .«if» (.subtype subtype) (.may .attachEquipment (.sequence []))] =>
    s!"untap {noun}. It gets {signedStat p}/{signedStat t} until end of turn. If it's {indefinite subtype} {subtype}, you may attach an Equipment you control to it"
  | [.countersOnCreatureTargets kind k .firstYouControl, .mutualFight .both] =>
    s!"put {kind.countersPhrase k} on target creature you control. Then it fights target creature an opponent controls"
  | [.countersOnCreatureTargets kind k .firstYouControl,
     .«if» .castFromGraveyard (.plusOneOnEachYouControl m .eachOther)] =>
    s!"put {kind.countersPhrase k} on target creature you control. If this spell was cast from a graveyard, also put {plusOnePlusOneCountersPhrase m} on each other creature you control"
  | [.dealDamageToEachCreature n (.nonSubtype sub) .fixed, .addFourManaDragonSpells m sub2] =>
    s!"deals {n} damage to each non-{sub} creature. Add {englishNumber m} mana in any combination of colors. Spend this mana only to cast {sub2} spells"
  | [.returnTargetToHand .spell, .«if» .giftPromised .playersCantCastThisTurn] =>
    "return target spell to its owner's hand. If the gift was promised, players can't cast spells this turn"
  | [.onPermanent (.dealDamage n), .«if» .teamwork (.dealDamageToControllerOfTarget extra)] =>
    s!"deals {n} damage to target creature. If this spell was cast using teamwork, it also deals {extra} damage to that creature's controller"
  | [.onPermanent (.grantKeywords k), .«if» .teamwork (.onPermanent (.grantKeywords kw))] =>
    if k == Keyword.doubleStrike then
      s!"target creature gains double strike until end of turn. If this spell was cast using teamwork, that creature also gains {kw.joinedAnd} until end of turn"
    else
      String.intercalate ". " (rs.map (phraseOne · noun))
  | [.targetPlayerInvestigates,
     .onCreatureAmongTargets (.grantKeywords k),
     .onCreatureAmongTargets .untap,
     .onCreatureAmongTargets (.pump 1 0)] =>
    if k == Keyword.flying then
      "target player investigates. Target creature gets +1/+0 and gains flying until end of turn. Untap it"
    else
      String.intercalate ". " (rs.map (phraseOne · noun))
  | [.countersOnCreatureTargets kind k .each, .targetPlayersGainLife n] =>
    s!"put {kind.countersPhrase k} on up to one target creature. Target player gains {n} life"
  | [.onPermanent .destroy, .searchCard s ty .ownerMayToBattlefield] =>
    s!"destroy {noun}. Its controller may search their library for a {s.oracleWord} {ty.oracleWord} card, put it onto the battlefield tapped, then shuffle"
  | [.draw (.fixed 3), .discardTwoUnlessArtifact n ty] =>
    s!"draw three cards. Then discard {englishNumber n} cards unless you discard {indefinite ty.oracleWord} {ty.oracleWord} card"
  | [.replace .diesThisTurn .exile, .onPermanent (.dealDamage n)] =>
    s!"deals {n} damage to {noun}. If that creature would die this turn, exile it instead"
  | [.onPermanent (.pump p t), .replace .diesThisTurn .exile] =>
    s!"{noun} gets {signedStat p}/{signedStat t} until end of turn. If that creature would die this turn, exile it instead"
  | [.onPermanent (.dealDamage n), .onPermanent .loseIndestructible, .replace .diesThisTurn .exile] =>
    s!"deals {n} damage to {noun}. That creature loses indestructible until end of turn. If that creature would die this turn, exile it instead"
  | [.onPermanent (.pump p t), .exileTopPlayUntilNext 1] =>
    s!"Target creature gets {signedStat p}/{signedStat t} until end of turn.\nExile the top card of your library. {playThatCardUntilNextTurnPhrase}."
  | [.onPermanent .doublePowerAndToughness, .onPermanent (.grantKeywords k)] =>
    if k == Keyword.trample then
      "Choose target creature you control. Until end of turn, double its power and toughness and it gains trample"
    else
      String.intercalate ". " (rs.map (phraseOne · noun))
  | _ =>
    String.intercalate ". " (rs.map (phraseOne · noun))

/-- Printed wording of a choice. The library pair keeps its Oracle sentence;
other choices join each alternative. -/
private def phraseOr (rs : List SpellResolution) (noun : String) : String :=
  match rs with
  | [.onPermanent .putOnTopOfLibrary, .onPermanent .putOnBottomOfLibrary] =>
    s!"{noun}'s owner puts it on their choice of the top or bottom of their library"
  | [.onPermanent .putOnBottomOfLibrary, .onPermanent .putOnTopOfLibrary] =>
    s!"{noun}'s owner puts it on their choice of the top or bottom of their library"
  | _ =>
    String.intercalate " or " ((rs.map (phraseOne · noun)).filter (· != ""))

/-- Oracle-style reminder from targeting and resolution. `.fight` is the
one-sided Quarrel wording, including a multiple of that power. `.mutualFight`
is the two-creature fight, including the later step of a counter-then-fight
sequence and a fight of up to one other creature. -/
def toPhrase (r : SpellResolution) (noun : String) : String :=
  match r with
  | .sequence rs => phraseSequence (rs.flatMap flatten) noun
  | .or rs => phraseOr rs noun
  | r => phraseOne r noun

end SpellResolution

end Mtg.Engine
