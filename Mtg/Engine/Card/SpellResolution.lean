import Mtg.Engine.Card.Counter
import Mtg.Engine.Card.Keywords
import Mtg.Engine.Card.Targeting
import Mtg.Engine.Card.Text
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

/-- How the demonstration agent classifies an activated-ability mode. -/
inductive AbilityCastKind where
  /-- Damage to a creature. -/
  | creatureDamage
  /-- Destroy a colorless nonland permanent. -/
  | destroyColorless
  /-- Any other mode. -/
  | other
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

/-- Which permanents `SharedTrigger.plusOneEachYouControl` puts a counter on. -/
inductive YouControlPlusOne where
  /-- Each creature you control. -/
  | eachCreature
  /-- Each permanent of this subtype you control. -/
  | subtype (subtype : String)
  /-- Each creature you control, or two counters with the city's blessing. -/
  | citysBlessing
deriving Repr, Inhabited, BEq

namespace TriggeredAbility

/-- Spending restriction or color choice for `Resolution.addMana` (CR 106.4). -/
inductive ManaSpendNote where
  /-- No spending restriction; `types` are added directly. -/
  | none
  /-- Mana of any one color (`types` is `#[]`). -/
  | anyColor
  /-- Mana in any combination of colors (`types` is `#[]`). -/
  | anyCombination
  /-- Spend this mana only to cast spells of `subtype`. -/
  | subtypeSpells (subtype : String)
  /-- Spend this mana only to cast `subtype` spells or activate abilities of `subtype` sources. -/
  | subtypeSpellsOrAbilities (subtype : String)
  /-- Spend this mana only to cast an artifact spell. -/
  | artifactSpell
  /-- Spend this mana only to activate abilities of creature sources. -/
  | creatureSources
  /-- This mana can't be spent to cast a nonartifact spell. -/
  | cantNonartifact
  /-- Spend this mana only to cast Equipment spells or activate equip abilities. -/
  | equipment
  /-- Spend this mana only to cast a noncreature spell. -/
  | noncreatureSpell
deriving Repr, Inhabited, BEq

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
/-- Target-restriction and announced-target object selectors (CR 115). -/
inductive TargetObject where
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
  Another Hero is `.target (.anotherSubtype "Hero")`.
  `.atLeast (.count (.target (.anotherSubtype "Hero"))) (.fixed 1)`.
  Read on its own, this is that same permanent. A missing target names
  nothing. -/
  | anotherSubtype (subtype : String)
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
  /-- The announced permanent. `byYou` means the controller puts the counters,
  and an illegal target logs that you won't put counters.
  Returned to its owner's hand, noting the return, is
  `.returnToHand .permanent .returnedPermanent`.
  A +1/+1 counter you put on the target is
  `.putCounters (.ofKind .plusOnePlusOne) (.permanent true)`. -/
  | permanent (byYou : Bool := false)
  /-- The announced creature.
  It fights up to one other announced creature with
  `.fight .announced .upToOneOther`.
  It fights another announced creature with `.fight .announced .mutual`. -/
  | announced
  /-- The announced Equipment. An illegal Equipment does not move.
  `.attach .announcedEquipment .announcedCreature`. -/
  | announcedEquipment
  /-- Up to one announced creature. A missing creature is reported.
  `.attach .target .optionalCreature`. -/
  | optionalCreature
  /-- The announced creature. An illegal pair does not move the Equipment.
  `.attach .announcedEquipment .announcedCreature`. -/
  | announcedCreature
  /-- The target at `index`. -/
  | targetAt (index : Nat)
  /-- Each legal creature target among the announced targets. -/
  | creatureTargets
  /-- The first targeted creature the controller controls. -/
  | firstTargetCreatureYouControl
  /-- A second targeted artifact the controller controls, copied as nonlegendary until end of turn. -/
  | secondArtifactTargetNotLegendary
  /-- The targeted creature, copied until end of turn with the legend rule turned off this turn. -/
  | targetLegendRuleOff
  /-- The announced permanent, until the controller's next turn. -/
  | untilYourNextTurn
  /-- Target creature you own, or any number of target creatures you own if kicked. -/
  | ownedCreaturesKicker
  /-- Target permanent an opponent controls, copied as two tokens with haste sacrificed at the next end step. -/
  | targetPermanentTwoTokensHasteSacrifice
deriving Repr, Inhabited, BEq, DecidableEq

/-- Permanent selectors on the battlefield (CR 110 / CR 403). -/
inductive BattlefieldObject where
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
  `.put (.cause (some "Villain")) .underOwner (.entering [.additionalSubtype "Hero", .counter .finality])`.
  An announced card or permanent is used when one was chosen; otherwise the
  recorded cause. A missing cause, or the wrong subtype, puts nothing.
  A token copy of that artifact, with no subtype, is `.becomeCopy .cause`.
  A subtype copies nothing that way. -/
  | cause (subtype : Option String := none)
  /-- Each creature the controller controls. -/
  | creaturesYouControl
  /-- Each other permanent the controller controls of this subtype.
  The source is not included.
  Each other creature of these subtypes is
  `.intersection [.creaturesYouControl, .union (subtypes.toList.map .othersOfSubtype)]`. -/
  | othersOfSubtype (subtype : String)
  /-- Each creature an opponent controls. -/
  | opponentsCreatures
  /-- Each creature blocking the source. -/
  | blockers
  /-- Each creature that is not this subtype, and each opponent. -/
  | eachNonSubtypeAndOpponents (subtype : String)
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
  /-- Each announced land the controller still controls.
  Remembered so they return tapped is
  `.exile .landsYouControl .forLater .lands`. -/
  | landsYouControl
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
  /-- The one creature the controller has attacking alone.
  None is reported. -/
  | attackingAlone
  /-- The creature an earlier step attached Equipment to.
  It deals damage equal to its power with `.fight .equipmentHost .reflexive`.
  Nothing is queued when no creature received Equipment. -/
  | equipmentHost
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
  /-- The creature remembered with the artifact put from hand.
  `.attach .putArtifact .notedHost`. -/
  | notedHost
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
  /-- Every creature on the battlefield. -/
  | allCreatures
  /-- Creatures the targeted player controls. -/
  | creaturesOfTargetPlayer
  /-- Each creature that does not have this subtype. -/
  | nonSubtypeCreatures (subtype : String)
  /-- Each creature and planeswalker opponents control. -/
  | oppCreaturesAndPlaneswalkers
  /-- Each creature except tokens you control. -/
  | creaturesExceptYourTokens
  /-- Each creature you control with a +1/+1 counter on it. -/
  | creaturesWithPlusOne
  /-- Each Wizard token you control except tokens just created. -/
  | wizardTokensExceptRecent
  /-- Each token you control. -/
  | tokensYouControl
  /-- Creatures without flying. -/
  | creaturesWithoutFlying
  /-- A land the controller controls. -/
  | land
  /-- A creature or planeswalker the controller controls. -/
  | creatureOrPlaneswalker
  /-- Permanents of type `ty` opponents control. -/
  | oppPermanents (ty : CardType := .artifact)
  /-- Two nonlegendary token copies of the source. -/
  | sourceTwoNonlegendaryTokens
  /-- Each nontoken creature the controller controls. -/
  | nontokenCreaturesYouControl
  /-- A token copy of the source if the source wasn't a token. -/
  | sourceIfNotToken
  /-- All creatures except up to two chosen by the controller. -/
  | allCreaturesExceptTwoChosen
  /-- Each other creature with mana value of the chosen odd or even quality. -/
  | otherCreaturesOddOrEvenMv
  /-- All creatures that aren't of the chosen creature type. -/
  | creaturesNotChosenType
  /-- A creature or planeswalker with the greatest mana value among those the targeted opponent controls. -/
  | oppGreatestMvCreatureOrPlaneswalker
  /-- Creatures attacking the player recorded as the cause's controller, also gaining trample. -/
  | attackersOfCauseControllerWithTrample
  /-- Creatures attacking the controller or a planeswalker they control until their next turn. -/
  | attackersAgainstYouUntilYourTurn
  /-- Creatures attacking one of the controller's opponents until the controller's next turn, also gaining trample. -/
  | attackersAgainstOpponentsUntilYourTurn
  /-- An Equipment the controller controls. -/
  | equipmentYouControl
  /-- All tapped creatures opponents control. -/
  | oppTappedCreatures
  /-- All creatures with power 4 or greater. -/
  | creaturesPowerAtLeast4
  /-- Creatures that dealt combat damage to the controller, while the controller is the monarch. -/
  | combatDamagerIfMonarch
  /-- A creature on the battlefield, copied until end of turn with haste. -/
  | anyCreatureOnBattlefieldWithHaste
deriving Repr, Inhabited, BEq

/-- Card selectors in graveyards, exile, or noted across zones (CR 404 / CR 406). -/
inductive GraveyardExileObject where
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
  /-- The card recorded as this trigger's last-known power.
  You may exile it from your graveyard and play it until the end of your
  next turn with
  `.may (.exile .discarded .playUntilNextTurn) (.sequence []) .ifYouDo`.
  A card that has left the graveyard is reported. No recorded card is
  reported. Declining exiles nothing. -/
  | discarded
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
  /-- The announced creature card. Its mana value is at most `mv`.
  `.put (.creatureMvAtMost mv)`. -/
  | creatureMvAtMost (mv : Nat)
  /--   The announced creature card in the controller's graveyard.
  Returned tapped and attacking with a finality counter is
  `.put .creatureCard .tapped (.entering [.attacking, .counter .finality])`.
  Inside `queueReflexive`, that card is chosen when the reflexive ability
  is put on the stack. Outside it, this puts nothing. -/
  | creatureCard
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
  /-- Creature cards in the controller's graveyard.
  At least `n` is `.atLeast (.count .creatureCardsInGraveyard) (.fixed n)`. -/
  | creatureCardsInGraveyard
  /-- The targeted card of this subtype in the controller's graveyard. -/
  | graveyardSubtype (subtype : String)
  /-- All nonland permanent cards in the controller's graveyard. -/
  | allNonlandPermanentsInGraveyard
  /-- The targeted land card in the controller's graveyard. -/
  | landCard
  /-- A creature or creature card with mana value at most `n`, or any if teamwork was paid. -/
  | creatureMvAtMostOrTeamwork (n : Nat)
  /-- Up to two modal graveyard cards (artifact, creature, enchantment, land). -/
  | upToTwoGyModal
  /-- Creature cards in opponents' graveyards that were put there from the battlefield this turn. -/
  | creaturesDiedThisTurn
  /-- Two cards you own from outside the game, one chosen by an opponent. -/
  | outsideGameOpponentChoice
  /-- This spell and four cards named Sphinx's Approach in your graveyard. -/
  | sphinxsApproach
deriving Repr, Inhabited, BEq, DecidableEq

/-- Card selectors in libraries and hands (CR 401 / CR 402). -/
inductive LibraryHandObject where
  /-- The controller's hand. The number discarded is noted for a later step.
  Declining leaves the note empty.
  `.discard .hand`. -/
  | hand
  /-- A nonland card chosen from the announced player's revealed hand.
  `.discard .chosenNonland`. -/
  | chosenNonland
  /-- The card `revealLibrary .untilCreature` revealed, put into the
  controller's hand on the hand branch.
  Outside that resolution, `.returnToHand .revealed` does nothing.
  Put onto the battlefield is `.put .revealed`. Outside `.untilSaga` and
  the battlefield branch of `.untilCreature`, that put does nothing. -/
  | revealed
  /-- A basic land card `searchLibrary` found, put into the controller's hand.
  Outside that resolution, `.returnToHand .basicLand` does nothing. -/
  | basicLand
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
  /-- Up to `max` basic cards of this subtype from the controller's library.
  Linked to the source is
  `.exile (.basicUpTo subtype max) .forLater .linked`. -/
  | basicUpTo (subtype : String) (max : Nat)
  /-- The top `n` cards of the announced opponent's library.
  `.exile (.opponentTop 5) (.mayCastUpTo 2)`.
  Inside `queueReflexive`, the opponent is chosen when the reflexive
  ability is put on the stack. Outside it, this exiles nothing. -/
  | opponentTop (n : Nat)
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
  /-- A creature card of `subtype` with mana value at most `maxMv` from hand.
  `.may (.put (.creatureFromHand subtype maxMv)) (.draw (.fixed 1))`. -/
  | creatureFromHand (subtype : String) (maxMv : Nat)
  /-- Each card in the controller's hand.
  Discarding one as a cost is `.pay (.discard (.fixed 1) .card)`.
  A permanent is not a card in hand. -/
  | card
  /-- Each nonland card in the controller's hand.
  Discarding one as a cost is `.pay (.discard (.fixed 1) .nonland)`.
  A land is not included. A permanent is not a card in hand. -/
  | nonland
  /-- A nonland permanent card chosen from the targeted player's revealed hand. -/
  | chosenNonlandPermanent
  /-- The top X cards of the controller's library, where X is the source's power. -/
  | topPower
  /-- Up to `n` land cards. -/
  | landsUpTo (n : Nat)
  /-- Up to that many land cards, where that many is the damage dealt. -/
  | landsEqualDamage
  /-- A planeswalker card. -/
  | planeswalkerCard
  /-- An enchantment card. -/
  | enchantmentCard
  /-- A card with supertype `s` and card type `ty`. -/
  | supertypeCard (s : Supertype := .legendary) (ty : CardType := .creature)
  /-- A card with land subtype `subtype`. -/
  | landSubtype (subtype : String)
  /-- A basic land card; you may behold `subtype` to untap it. -/
  | basicBeholdUntap (subtype : String)
  /-- Up to X basic land cards with different names. -/
  | basicLandsDifferentNamesX
  /-- An artifact creature card with mana value X or less from library and/or graveyard. -/
  | artifactCreatureX
  /-- A card at random from the controller's hand. -/
  | random
  /-- The top `n` cards of the controller's library. -/
  | topN (n : Nat)
  /-- The top X cards of the announced opponent's library. -/
  | opponentTopX
  /-- A card of one of `types` among the cards just looked at. -/
  | lookedTypes (types : Array String)
  /-- A face-down pile and a face-up pile separated from the looked-at cards. -/
  | twoPiles
  /-- `n` cards unless a card of type `ty` is discarded. -/
  | cardsUnlessType (n : Nat := 2) (ty : CardType := .artifact)
  /-- All but the bottom card of each opponent's library. -/
  | opponentLibrariesButBottom
  /-- Draw two cards, then discard two cards, tapping and stunning up to that many target creatures for nonlands discarded. -/
  | drawTwoDiscardTwoStun
  /-- Two cards from each opponent, drawing a card for each opponent who didn't discard two nonland cards. -/
  | eachOpponentTwoDrawPerNonlandShortfall
  /-- Discard a card, then draw a card and put a +1/+1 counter on the triggering creature for each card discarded this turn. -/
  | lootThenCountersPerDiscard
  /-- Draw X cards, then discard X cards and create a 1/1 white Spirit token with flying for each card type discarded this way. -/
  | drawAndDiscardXCreateSpiritPerType
  /-- A basic land card of one of `kinds`, untapped if the controller controls at least `untapAt` lands. -/
  | basicSubtypesUntapAt (kinds : Array String) (untapAt : Nat)
  /-- Draw a card, then discard a card. -/
  | drawOneDiscardOne
  /-- One pile into hand and the other into graveyard from the top five cards (Fact or Fiction). -/
  | factOrFiction
deriving Repr, Inhabited, BEq, DecidableEq

/-- Sacrifice-choice and stack object selectors (CR 405 / CR 701.17). -/
inductive SacrificeStackObject where
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
  /-- The controller, when the source was cast.
  A source that was not cast does nothing.
  `.grant .protectionEverything .youIfCast`. -/
  | youIfCast
  /-- Each creature the spell that caused this trigger targets.
  A permanent that is not a creature is skipped. No recorded spell grants
  nothing.
  `.grant (.keywords Keyword.flying) .spellTargets`. -/
  | spellTargets
  /-- A creature of each opponent's choice. -/
  | eachOpponentsCreature
  /-- The targeted spell on the stack. -/
  | targetSpell
  /-- The targeted activated or triggered ability on the stack from a creature or artifact source. -/
  | stackAbility (fromCreature : Bool := true)
  /-- The source spell, copied X times. -/
  | sourceSpellXTimes
  /-- The next spell the controller casts this turn. -/
  | nextSpellThisTurn
  /-- The spell that caused this trigger. -/
  | causingSpell
  /-- Target opponent sacrifices a creature or planeswalker, discards a card, and loses 3 life; you draw a card and gain 3 life. -/
  | archonCruelty
  /-- Target instant or sorcery spell an opponent controls, copied twice. -/
  | targetSpellTwice
deriving Repr, Inhabited, BEq

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
  /-- The player who was dealt combat damage. That seat is
  `lastCombatDamagePlayer`. A missing seat is the controller's opponent.
  `.revealLibrary .untilInstantOrSorcery (.exile .top .forLater .impulse) .damagedPlayer`. -/
  | damagedPlayer
  /-- The announced player. When none was announced, the resolving ability's
  last-known toughness is that player's index.
  `.revealLibrary .untilNonland (.may (.putCounters (.ofKind .plusOnePlusOne) .source) (.exile .top .forLater .anyManaThisTurn) .ifYouDont) .announced`. -/
  | announced
  /-- Each player. -/
  | eachPlayer
  /-- The player target at `index`. -/
  | targetAt (index : Nat)
  /-- Each targeted player. -/
  | targetPlayers
  /-- Each opponent loses 1 life and you gain that much life, if {W/B} is paid (CR 702.101). -/
  | extort
  /-- Each opponent loses 1 life and you gain 1 life. -/
  | eachOpponentAndYouGain1
  /-- You lose 1 life and amass. -/
  | youLose1Life
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
  /-- Target-restriction or announced-target object selector (CR 115). -/
  | targetObj (o : TargetObject)
  /-- Battlefield permanent selector (CR 110 / CR 403). -/
  | battlefield (o : BattlefieldObject)
  /-- Graveyard, exile, or noted card selector (CR 404 / CR 406). -/
  | graveyardExile (o : GraveyardExileObject)
  /-- Library or hand card selector (CR 401 / CR 402). -/
  | libraryHand (o : LibraryHandObject)
  /-- Sacrifice-choice or stack object selector (CR 405 / CR 701.17). -/
  | sacrificeStack (o : SacrificeStackObject)
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
  /-- Each creature controlled by `who`. -/
  | creaturesControlledBy (who : PlayerSelector)
  /-- All cards of `ty` in `who`'s graveyard. -/
  | graveyardCardsOfType (ty : CardType) (who : PlayerSelector)
  /-- Each player's hand, optionally discarded to draw `n` cards. -/
  | mayWheel (n : Nat) (who : PlayerSelector := by exact .eachPlayer)
deriving Repr, Inhabited, BEq

end

namespace PlayerSelector

@[match_pattern] abbrev each : PlayerSelector := .eachOpponent
@[match_pattern] abbrev recruit : PlayerSelector := .player

end PlayerSelector

namespace ObjectSelector

-- TargetObject aliases
@[match_pattern] abbrev whileSource : ObjectSelector := .targetObj .whileSource
@[match_pattern] abbrev ifPresent : ObjectSelector := .targetObj .ifPresent
@[match_pattern] abbrev creature : ObjectSelector := .targetObj .creature
@[match_pattern] abbrev laterCreature : ObjectSelector := .targetObj .laterCreature
@[match_pattern] abbrev planeswalker : ObjectSelector := .targetObj .planeswalker
@[match_pattern] abbrev anotherSubtype (subtype : String) : ObjectSelector := .targetObj (.anotherSubtype subtype)
@[match_pattern] abbrev eachPermanent : ObjectSelector := .targetObj .eachPermanent
@[match_pattern] abbrev eachEquipment : ObjectSelector := .targetObj .eachEquipment
@[match_pattern] abbrev permanent (byYou : Bool := false) : ObjectSelector := .targetObj (.permanent byYou)
@[match_pattern] abbrev announced : ObjectSelector := .targetObj .announced
@[match_pattern] abbrev announcedEquipment : ObjectSelector := .targetObj .announcedEquipment
@[match_pattern] abbrev optionalCreature : ObjectSelector := .targetObj .optionalCreature
@[match_pattern] abbrev announcedCreature : ObjectSelector := .targetObj .announcedCreature
@[match_pattern] abbrev targetAt (index : Nat) : ObjectSelector := .targetObj (.targetAt index)
@[match_pattern] abbrev creatureTargets : ObjectSelector := .targetObj .creatureTargets
@[match_pattern] abbrev firstTargetCreatureYouControl : ObjectSelector := .targetObj .firstTargetCreatureYouControl
@[match_pattern] abbrev secondArtifactTargetNotLegendary : ObjectSelector := .targetObj .secondArtifactTargetNotLegendary
@[match_pattern] abbrev targetLegendRuleOff : ObjectSelector := .targetObj .targetLegendRuleOff
@[match_pattern] abbrev untilYourNextTurn : ObjectSelector := .targetObj .untilYourNextTurn
@[match_pattern] abbrev ownedCreaturesKicker : ObjectSelector := .targetObj .ownedCreaturesKicker
@[match_pattern] abbrev targetPermanentTwoTokensHasteSacrifice : ObjectSelector := .targetObj .targetPermanentTwoTokensHasteSacrifice

-- BattlefieldObject aliases
@[match_pattern] abbrev enchanted : ObjectSelector := .battlefield .enchanted
@[match_pattern] abbrev cause (subtype : Option String := none) : ObjectSelector := .battlefield (.cause subtype)
@[match_pattern] abbrev creaturesYouControl : ObjectSelector := .battlefield .creaturesYouControl
@[match_pattern] abbrev othersOfSubtype (subtype : String) : ObjectSelector := .battlefield (.othersOfSubtype subtype)
@[match_pattern] abbrev opponentsCreatures : ObjectSelector := .battlefield .opponentsCreatures
@[match_pattern] abbrev blockers : ObjectSelector := .battlefield .blockers
@[match_pattern] abbrev eachNonSubtypeAndOpponents (subtype : String) : ObjectSelector := .battlefield (.eachNonSubtypeAndOpponents subtype)
@[match_pattern] abbrev youControl (which : YouControlPlusOne := .eachCreature) : ObjectSelector := .battlefield (.youControl which)
@[match_pattern] abbrev eachOther : ObjectSelector := .battlefield .eachOther
@[match_pattern] abbrev createdToken : ObjectSelector := .battlefield .createdToken
@[match_pattern] abbrev sourceIfPresent : ObjectSelector := .battlefield .sourceIfPresent
@[match_pattern] abbrev eachUpToLastKnown : ObjectSelector := .battlefield .eachUpToLastKnown
@[match_pattern] abbrev landsYouControl : ObjectSelector := .battlefield .landsYouControl
@[match_pattern] abbrev humans : ObjectSelector := .battlefield .humans
@[match_pattern] abbrev enchantedWhileSource : ObjectSelector := .battlefield .enchantedWhileSource
@[match_pattern] abbrev attackingCreatures : ObjectSelector := .battlefield .attackingCreatures
@[match_pattern] abbrev equipped : ObjectSelector := .battlefield .equipped
@[match_pattern] abbrev firstThisTurn : ObjectSelector := .battlefield .firstThisTurn
@[match_pattern] abbrev oppArtifactsEnchantments : ObjectSelector := .battlefield .oppArtifactsEnchantments
@[match_pattern] abbrev permanentDealtDamage : ObjectSelector := .battlefield .permanentDealtDamage
@[match_pattern] abbrev equippedAttackers : ObjectSelector := .battlefield .equippedAttackers
@[match_pattern] abbrev attackingAlone : ObjectSelector := .battlefield .attackingAlone
@[match_pattern] abbrev equipmentHost : ObjectSelector := .battlefield .equipmentHost
@[match_pattern] abbrev enteringVillain : ObjectSelector := .battlefield .enteringVillain
@[match_pattern] abbrev anyYouControl : ObjectSelector := .battlefield .anyYouControl
@[match_pattern] abbrev putArtifact : ObjectSelector := .battlefield .putArtifact
@[match_pattern] abbrev notedHost : ObjectSelector := .battlefield .notedHost
@[match_pattern] abbrev enchantedCreature : ObjectSelector := .battlefield .enchantedCreature
@[match_pattern] abbrev legendaryCreaturesYouControl : ObjectSelector := .battlefield .legendaryCreaturesYouControl
@[match_pattern] abbrev planeswalkersYouControl : ObjectSelector := .battlefield .planeswalkersYouControl
@[match_pattern] abbrev forestsExceptCause : ObjectSelector := .battlefield .forestsExceptCause
@[match_pattern] abbrev questCounters : ObjectSelector := .battlefield .questCounters
@[match_pattern] abbrev putEquipment : ObjectSelector := .battlefield .putEquipment
@[match_pattern] abbrev harnessedSource : ObjectSelector := .battlefield .harnessedSource
@[match_pattern] abbrev artifact : ObjectSelector := .battlefield .artifact
@[match_pattern] abbrev anotherCreatureOrArtifact : ObjectSelector := .battlefield .anotherCreatureOrArtifact
@[match_pattern] abbrev allCreatures : ObjectSelector := .battlefield .allCreatures
@[match_pattern] abbrev creaturesOfTargetPlayer : ObjectSelector := .battlefield .creaturesOfTargetPlayer
@[match_pattern] abbrev nonSubtypeCreatures (subtype : String) : ObjectSelector := .battlefield (.nonSubtypeCreatures subtype)
@[match_pattern] abbrev oppCreaturesAndPlaneswalkers : ObjectSelector := .battlefield .oppCreaturesAndPlaneswalkers
@[match_pattern] abbrev creaturesExceptYourTokens : ObjectSelector := .battlefield .creaturesExceptYourTokens
@[match_pattern] abbrev creaturesWithPlusOne : ObjectSelector := .battlefield .creaturesWithPlusOne
@[match_pattern] abbrev wizardTokensExceptRecent : ObjectSelector := .battlefield .wizardTokensExceptRecent
@[match_pattern] abbrev tokensYouControl : ObjectSelector := .battlefield .tokensYouControl
@[match_pattern] abbrev creaturesWithoutFlying : ObjectSelector := .battlefield .creaturesWithoutFlying
@[match_pattern] abbrev land : ObjectSelector := .battlefield .land
@[match_pattern] abbrev creatureOrPlaneswalker : ObjectSelector := .battlefield .creatureOrPlaneswalker
@[match_pattern] abbrev oppPermanents (ty : CardType := .artifact) : ObjectSelector := .battlefield (.oppPermanents ty)
@[match_pattern] abbrev sourceTwoNonlegendaryTokens : ObjectSelector := .battlefield .sourceTwoNonlegendaryTokens
@[match_pattern] abbrev nontokenCreaturesYouControl : ObjectSelector := .battlefield .nontokenCreaturesYouControl
@[match_pattern] abbrev sourceIfNotToken : ObjectSelector := .battlefield .sourceIfNotToken
@[match_pattern] abbrev allCreaturesExceptTwoChosen : ObjectSelector := .battlefield .allCreaturesExceptTwoChosen
@[match_pattern] abbrev otherCreaturesOddOrEvenMv : ObjectSelector := .battlefield .otherCreaturesOddOrEvenMv
@[match_pattern] abbrev creaturesNotChosenType : ObjectSelector := .battlefield .creaturesNotChosenType
@[match_pattern] abbrev oppGreatestMvCreatureOrPlaneswalker : ObjectSelector := .battlefield .oppGreatestMvCreatureOrPlaneswalker
@[match_pattern] abbrev attackersOfCauseControllerWithTrample : ObjectSelector := .battlefield .attackersOfCauseControllerWithTrample
@[match_pattern] abbrev attackersAgainstYouUntilYourTurn : ObjectSelector := .battlefield .attackersAgainstYouUntilYourTurn
@[match_pattern] abbrev attackersAgainstOpponentsUntilYourTurn : ObjectSelector := .battlefield .attackersAgainstOpponentsUntilYourTurn
@[match_pattern] abbrev equipmentYouControl : ObjectSelector := .battlefield .equipmentYouControl
@[match_pattern] abbrev oppTappedCreatures : ObjectSelector := .battlefield .oppTappedCreatures
@[match_pattern] abbrev creaturesPowerAtLeast4 : ObjectSelector := .battlefield .creaturesPowerAtLeast4
@[match_pattern] abbrev combatDamagerIfMonarch : ObjectSelector := .battlefield .combatDamagerIfMonarch
@[match_pattern] abbrev anyCreatureOnBattlefieldWithHaste : ObjectSelector := .battlefield .anyCreatureOnBattlefieldWithHaste

-- GraveyardExileObject aliases
@[match_pattern] abbrev graveyardCard : ObjectSelector := .graveyardExile .graveyardCard
@[match_pattern] abbrev graveyardPermanent : ObjectSelector := .graveyardExile .graveyardPermanent
@[match_pattern] abbrev milledSubtype (subtype : String) : ObjectSelector := .graveyardExile (.milledSubtype subtype)
@[match_pattern] abbrev linkedExile : ObjectSelector := .graveyardExile .linkedExile
@[match_pattern] abbrev graveyardInstants (n : Nat) : ObjectSelector := .graveyardExile (.graveyardInstants n)
@[match_pattern] abbrev discarded : ObjectSelector := .graveyardExile .discarded
@[match_pattern] abbrev nonlandMvAtMost (mv : Nat) : ObjectSelector := .graveyardExile (.nonlandMvAtMost mv)
@[match_pattern] abbrev notedLands : ObjectSelector := .graveyardExile .notedLands
@[match_pattern] abbrev discardedLand : ObjectSelector := .graveyardExile .discardedLand
@[match_pattern] abbrev creatureMvAtMost (mv : Nat) : ObjectSelector := .graveyardExile (.creatureMvAtMost mv)
@[match_pattern] abbrev creatureCard : ObjectSelector := .graveyardExile .creatureCard
@[match_pattern] abbrev artifactEnchantmentOrLand : ObjectSelector := .graveyardExile .artifactEnchantmentOrLand
@[match_pattern] abbrev creatureOrGraveyardCard : ObjectSelector := .graveyardExile .creatureOrGraveyardCard
@[match_pattern] abbrev noted : ObjectSelector := .graveyardExile .noted
@[match_pattern] abbrev creatureCardsInGraveyard : ObjectSelector := .graveyardExile .creatureCardsInGraveyard
@[match_pattern] abbrev graveyardSubtype (subtype : String) : ObjectSelector := .graveyardExile (.graveyardSubtype subtype)
@[match_pattern] abbrev allNonlandPermanentsInGraveyard : ObjectSelector := .graveyardExile .allNonlandPermanentsInGraveyard
@[match_pattern] abbrev landCard : ObjectSelector := .graveyardExile .landCard
@[match_pattern] abbrev creatureMvAtMostOrTeamwork (n : Nat) : ObjectSelector := .graveyardExile (.creatureMvAtMostOrTeamwork n)
@[match_pattern] abbrev upToTwoGyModal : ObjectSelector := .graveyardExile .upToTwoGyModal
@[match_pattern] abbrev creaturesDiedThisTurn : ObjectSelector := .graveyardExile .creaturesDiedThisTurn
@[match_pattern] abbrev outsideGameOpponentChoice : ObjectSelector := .graveyardExile .outsideGameOpponentChoice
@[match_pattern] abbrev sphinxsApproach : ObjectSelector := .graveyardExile .sphinxsApproach

-- LibraryHandObject aliases
@[match_pattern] abbrev hand : ObjectSelector := .libraryHand .hand
@[match_pattern] abbrev chosenNonland : ObjectSelector := .libraryHand .chosenNonland
@[match_pattern] abbrev revealed : ObjectSelector := .libraryHand .revealed
@[match_pattern] abbrev basicLand : ObjectSelector := .libraryHand .basicLand
@[match_pattern] abbrev cardFromHand : ObjectSelector := .libraryHand .cardFromHand
@[match_pattern] abbrev top : ObjectSelector := .libraryHand .top
@[match_pattern] abbrev basicUpTo (subtype : String) (max : Nat) : ObjectSelector := .libraryHand (.basicUpTo subtype max)
@[match_pattern] abbrev opponentTop (n : Nat) : ObjectSelector := .libraryHand (.opponentTop n)
@[match_pattern] abbrev landFromHand : ObjectSelector := .libraryHand .landFromHand
@[match_pattern] abbrev artifactFromHand : ObjectSelector := .libraryHand .artifactFromHand
@[match_pattern] abbrev randomCreature : ObjectSelector := .libraryHand .randomCreature
@[match_pattern] abbrev forest : ObjectSelector := .libraryHand .forest
@[match_pattern] abbrev basicLandOnTop : ObjectSelector := .libraryHand .basicLandOnTop
@[match_pattern] abbrev dragon : ObjectSelector := .libraryHand .dragon
@[match_pattern] abbrev creatureFromHand (subtype : String) (maxMv : Nat) : ObjectSelector := .libraryHand (.creatureFromHand subtype maxMv)
@[match_pattern] abbrev card : ObjectSelector := .libraryHand .card
@[match_pattern] abbrev nonland : ObjectSelector := .libraryHand .nonland
@[match_pattern] abbrev chosenNonlandPermanent : ObjectSelector := .libraryHand .chosenNonlandPermanent
@[match_pattern] abbrev topPower : ObjectSelector := .libraryHand .topPower
@[match_pattern] abbrev landsUpTo (n : Nat) : ObjectSelector := .libraryHand (.landsUpTo n)
@[match_pattern] abbrev landsEqualDamage : ObjectSelector := .libraryHand .landsEqualDamage
@[match_pattern] abbrev planeswalkerCard : ObjectSelector := .libraryHand .planeswalkerCard
@[match_pattern] abbrev enchantmentCard : ObjectSelector := .libraryHand .enchantmentCard
@[match_pattern] abbrev supertypeCard (s : Supertype := .legendary) (ty : CardType := .creature) : ObjectSelector := .libraryHand (.supertypeCard s ty)
@[match_pattern] abbrev landSubtype (subtype : String) : ObjectSelector := .libraryHand (.landSubtype subtype)
@[match_pattern] abbrev basicBeholdUntap (subtype : String) : ObjectSelector := .libraryHand (.basicBeholdUntap subtype)
@[match_pattern] abbrev basicLandsDifferentNamesX : ObjectSelector := .libraryHand .basicLandsDifferentNamesX
@[match_pattern] abbrev artifactCreatureX : ObjectSelector := .libraryHand .artifactCreatureX
@[match_pattern] abbrev random : ObjectSelector := .libraryHand .random
@[match_pattern] abbrev topN (n : Nat) : ObjectSelector := .libraryHand (.topN n)
@[match_pattern] abbrev opponentTopX : ObjectSelector := .libraryHand .opponentTopX
@[match_pattern] abbrev lookedTypes (types : Array String) : ObjectSelector := .libraryHand (.lookedTypes types)
@[match_pattern] abbrev twoPiles : ObjectSelector := .libraryHand .twoPiles
@[match_pattern] abbrev cardsUnlessType (n : Nat := 2) (ty : CardType := .artifact) : ObjectSelector := .libraryHand (.cardsUnlessType n ty)
@[match_pattern] abbrev opponentLibrariesButBottom : ObjectSelector := .libraryHand .opponentLibrariesButBottom
@[match_pattern] abbrev drawTwoDiscardTwoStun : ObjectSelector := .libraryHand .drawTwoDiscardTwoStun
@[match_pattern] abbrev eachOpponentTwoDrawPerNonlandShortfall : ObjectSelector := .libraryHand .eachOpponentTwoDrawPerNonlandShortfall
@[match_pattern] abbrev lootThenCountersPerDiscard : ObjectSelector := .libraryHand .lootThenCountersPerDiscard
@[match_pattern] abbrev drawAndDiscardXCreateSpiritPerType : ObjectSelector := .libraryHand .drawAndDiscardXCreateSpiritPerType
@[match_pattern] abbrev basicSubtypesUntapAt (kinds : Array String) (untapAt : Nat) : ObjectSelector := .libraryHand (.basicSubtypesUntapAt kinds untapAt)
@[match_pattern] abbrev drawOneDiscardOne : ObjectSelector := .libraryHand .drawOneDiscardOne
@[match_pattern] abbrev factOrFiction : ObjectSelector := .libraryHand .factOrFiction

-- SacrificeStackObject aliases
@[match_pattern] abbrev opponentChosenCreature : ObjectSelector := .sacrificeStack .opponentChosenCreature
@[match_pattern] abbrev eachPlayersCreature : ObjectSelector := .sacrificeStack .eachPlayersCreature
@[match_pattern] abbrev leastPower : ObjectSelector := .sacrificeStack .leastPower
@[match_pattern] abbrev combatDamager : ObjectSelector := .sacrificeStack .combatDamager
@[match_pattern] abbrev sacrificedSource (how : SacrificeSourceHow := .isSacrificed) : ObjectSelector := .sacrificeStack (.sacrificedSource how)
@[match_pattern] abbrev plan : ObjectSelector := .sacrificeStack .plan
@[match_pattern] abbrev another : ObjectSelector := .sacrificeStack .another
@[match_pattern] abbrev chosenNontokenCreature : ObjectSelector := .sacrificeStack .chosenNontokenCreature
@[match_pattern] abbrev youIfCast : ObjectSelector := .sacrificeStack .youIfCast
@[match_pattern] abbrev spellTargets : ObjectSelector := .sacrificeStack .spellTargets
@[match_pattern] abbrev eachOpponentsCreature : ObjectSelector := .sacrificeStack .eachOpponentsCreature
@[match_pattern] abbrev targetSpell : ObjectSelector := .sacrificeStack .targetSpell
@[match_pattern] abbrev stackAbility (fromCreature : Bool := true) : ObjectSelector := .sacrificeStack (.stackAbility fromCreature)
@[match_pattern] abbrev sourceSpellXTimes : ObjectSelector := .sacrificeStack .sourceSpellXTimes
@[match_pattern] abbrev nextSpellThisTurn : ObjectSelector := .sacrificeStack .nextSpellThisTurn
@[match_pattern] abbrev causingSpell : ObjectSelector := .sacrificeStack .causingSpell
@[match_pattern] abbrev archonCruelty : ObjectSelector := .sacrificeStack .archonCruelty
@[match_pattern] abbrev targetSpellTwice : ObjectSelector := .sacrificeStack .targetSpellTwice

end ObjectSelector


/-- Characteristic, power/toughness, mana value, and counter numbers (CR 202.3 / CR 208). -/
inductive StatNumber where
  /-- The source's toughness. -/
  | equalSourceToughness
  /-- The source's power. -/
  | equalSourcePower
  /-- This statistic's current value, which doubles it. -/
  | double
  /-- The source's last-known power. -/
  | lastKnownPower
  /-- The greatest mana value among artifacts the controller controls. -/
  | greatestArtifactMv
  /-- The mana value of the spell that caused this, including the chosen value of X. -/
  | spellManaValue
  /-- X cards, where X is the mana spent to cast the triggering spell. -/
  | equalToManaSpent
  /-- The number of +1/+1 counters on the source. -/
  | plusOneCounters
  /-- The targeted card's power. -/
  | equalToTargetPower
  /-- One life for each burden counter on the source. -/
  | perBurden
  /-- The printed mana types, once for each charge counter on the source. -/
  | perChargeCounter
  /-- One 1/1 blue Merfolk for each blue mana symbol in the spell that caused this. -/
  | blueManaSymbols
  /-- X, chosen as the spell was cast. -/
  | chosenX
  /-- The power of the creature that caused this trigger. -/
  | causePower
  /-- Greatest power among creatures you control, losing life equal to cards drawn. -/
  | greatestPowerAndLoseLife
  /-- Greatest toughness among creatures you control, then put any number of creature cards from your hand onto the battlefield. -/
  | greatestToughnessThenPutCreatures
deriving Repr, Inhabited, BEq, DecidableEq

/-- Zone, permanent, subtype, and feature counts (CR 109 / CR 400). -/
inductive CountNumber where
  /-- One for each other creature the controller controls. -/
  | perOtherCreature
  /-- One for each Plains the controller controls. -/
  | perPlains
  /-- How many permanents of this subtype the controller controls. -/
  | subtypeCount (subtype : String)
  /-- One card for each graveyard with seven or more cards. -/
  | perFatGraveyard
  /-- One card for each permanent of this type the controller controls. -/
  | perControlled (ty : CardType)
  /-- Enough cards that the controller's hand has `n` cards. -/
  | upToHandSize (n : Nat)
  /-- One for each Equipment attached to the source. -/
  | attachedEquipment
  /-- One tapped Treasure for each artifact opponents control. -/
  | oppArtifacts
  /-- One Treasure for each artifact the damaged player controls. -/
  | damagedPlayerArtifacts
  /-- One Treasure for each creature the controller controls of a chosen type. -/
  | chosenCreatureType
  /-- One token for each permanent of this subtype the controller controls. -/
  | perSubtype (subtype : String)
  /-- How many cards are in the controller's library. -/
  | libraryCards
  /-- Minus X, where X is the number of cards in the controller's graveyard. -/
  | minusGraveyardCards
  /-- The number of colors among other artifacts the controller controls. -/
  | colorsAmongOtherArtifacts
  /-- The number of planeswalker types among planeswalkers the controller controls. -/
  | planeswalkerTypes
deriving Repr, Inhabited, BEq, DecidableEq

/-- Step-noted and turn-history numbers (CR 608 / CR 700). -/
inductive TurnEventNumber where
  /-- One for each card looked at while scrying. -/
  | perLookedAt
  /-- How many cards an earlier step discarded from the controller's hand. -/
  | discardedHand
  /-- One card for each Human tapped by an earlier step. -/
  | forEachTappedHuman
  /-- One for each permanent an earlier step destroyed. -/
  | forEachDestroyedThisWay
  /-- The life that player lost. -/
  | thatManyLost
  /-- Excess damage an earlier step recorded. -/
  | notedExcess
  /-- The power an earlier step recorded when it destroyed a creature. -/
  | notedPower
  /-- How many cards the controller has drawn this turn. -/
  | cardsDrawnThisTurn
  /-- The total mana value of other spells the controller has cast this turn. -/
  | otherSpellsManaValue
  /-- The number of +1/+1 counters removed to activate this ability. -/
  | removedPlusOnes
  /-- The amount of life the controller gained this turn. -/
  | lifeGainedThisTurn
  /-- The number of cards the controller has discarded this turn. -/
  | cardsDiscardedThisTurn
  /-- The number of cards put into the targeted player's graveyard from their library this turn. -/
  | milledByTargetPlayerThisTurn
  /-- The number of creatures that died this turn. -/
  | creaturesDiedThisTurn
  /-- The amount of life that player lost this turn. -/
  | lifeLostThisTurn
deriving Repr, Inhabited, BEq, DecidableEq

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
  /-- A fixed bonus of `n`, `n` damage, scry `n`, draw `n`, a base of `n`,
  `n` life gained, `n` life lost, mill `n`, amass `n`, or add mana
  `n` times. -/
  | fixed (n : Int)
  /-- How many objects `what` names. -/
  | count (what : ObjectSelector)
  /-- The power of `of`. -/
  | power (of : ObjectSelector)
  /-- The loyalty counters on `of`. -/
  | loyalty (of : ObjectSelector := .source)
  /-- Characteristic, power/toughness, mana value, or counter number (CR 202.3 / CR 208). -/
  | stat (s : StatNumber)
  /-- Zone, permanent, subtype, or feature count (CR 109 / CR 400). -/
  | countKind (c : CountNumber)
  /-- Step-noted or turn-history number (CR 608 / CR 700). -/
  | turnEvent (e : TurnEventNumber)
deriving Repr, Inhabited, BEq

namespace NumberSelector

-- StatNumber aliases
@[match_pattern] abbrev equalSourceToughness : NumberSelector := .stat .equalSourceToughness
@[match_pattern] abbrev equalSourcePower : NumberSelector := .stat .equalSourcePower
@[match_pattern] abbrev double : NumberSelector := .stat .double
@[match_pattern] abbrev lastKnownPower : NumberSelector := .stat .lastKnownPower
@[match_pattern] abbrev sourcePower : NumberSelector := .stat .lastKnownPower
@[match_pattern] abbrev greatestArtifactMv : NumberSelector := .stat .greatestArtifactMv
@[match_pattern] abbrev spellManaValue : NumberSelector := .stat .spellManaValue
@[match_pattern] abbrev equalToManaSpent : NumberSelector := .stat .equalToManaSpent
@[match_pattern] abbrev plusOneCounters : NumberSelector := .stat .plusOneCounters
@[match_pattern] abbrev equalToTargetPower : NumberSelector := .stat .equalToTargetPower
@[match_pattern] abbrev perBurden : NumberSelector := .stat .perBurden
@[match_pattern] abbrev perChargeCounter : NumberSelector := .stat .perChargeCounter
@[match_pattern] abbrev blueManaSymbols : NumberSelector := .stat .blueManaSymbols
@[match_pattern] abbrev chosenX : NumberSelector := .stat .chosenX
@[match_pattern] abbrev causePower : NumberSelector := .stat .causePower
@[match_pattern] abbrev greatestPowerAndLoseLife : NumberSelector := .stat .greatestPowerAndLoseLife
@[match_pattern] abbrev greatestToughnessThenPutCreatures : NumberSelector := .stat .greatestToughnessThenPutCreatures

-- CountNumber aliases
@[match_pattern] abbrev perOtherCreature : NumberSelector := .countKind .perOtherCreature
@[match_pattern] abbrev perPlains : NumberSelector := .countKind .perPlains
@[match_pattern] abbrev subtypeCount (subtype : String) : NumberSelector := .countKind (.subtypeCount subtype)
@[match_pattern] abbrev perFatGraveyard : NumberSelector := .countKind .perFatGraveyard
@[match_pattern] abbrev perControlled (ty : CardType) : NumberSelector := .countKind (.perControlled ty)
@[match_pattern] abbrev upToHandSize (n : Nat) : NumberSelector := .countKind (.upToHandSize n)
@[match_pattern] abbrev attachedEquipment : NumberSelector := .countKind .attachedEquipment
@[match_pattern] abbrev oppArtifacts : NumberSelector := .countKind .oppArtifacts
@[match_pattern] abbrev damagedPlayerArtifacts : NumberSelector := .countKind .damagedPlayerArtifacts
@[match_pattern] abbrev chosenCreatureType : NumberSelector := .countKind .chosenCreatureType
@[match_pattern] abbrev perSubtype (subtype : String) : NumberSelector := .countKind (.perSubtype subtype)
@[match_pattern] abbrev libraryCards : NumberSelector := .countKind .libraryCards
@[match_pattern] abbrev minusGraveyardCards : NumberSelector := .countKind .minusGraveyardCards
@[match_pattern] abbrev colorsAmongOtherArtifacts : NumberSelector := .countKind .colorsAmongOtherArtifacts
@[match_pattern] abbrev planeswalkerTypes : NumberSelector := .countKind .planeswalkerTypes

-- TurnEventNumber aliases
@[match_pattern] abbrev perLookedAt : NumberSelector := .turnEvent .perLookedAt
@[match_pattern] abbrev discardedHand : NumberSelector := .turnEvent .discardedHand
@[match_pattern] abbrev forEachTappedHuman : NumberSelector := .turnEvent .forEachTappedHuman
@[match_pattern] abbrev forEachDestroyedThisWay : NumberSelector := .turnEvent .forEachDestroyedThisWay
@[match_pattern] abbrev thatManyLost : NumberSelector := .turnEvent .thatManyLost
@[match_pattern] abbrev notedExcess : NumberSelector := .turnEvent .notedExcess
@[match_pattern] abbrev notedPower : NumberSelector := .turnEvent .notedPower
@[match_pattern] abbrev cardsDrawnThisTurn : NumberSelector := .turnEvent .cardsDrawnThisTurn
@[match_pattern] abbrev otherSpellsManaValue : NumberSelector := .turnEvent .otherSpellsManaValue
@[match_pattern] abbrev removedPlusOnes : NumberSelector := .turnEvent .removedPlusOnes
@[match_pattern] abbrev lifeGainedThisTurn : NumberSelector := .turnEvent .lifeGainedThisTurn
@[match_pattern] abbrev cardsDiscardedThisTurn : NumberSelector := .turnEvent .cardsDiscardedThisTurn
@[match_pattern] abbrev milledByTargetPlayerThisTurn : NumberSelector := .turnEvent .milledByTargetPlayerThisTurn
@[match_pattern] abbrev creaturesDiedThisTurn : NumberSelector := .turnEvent .creaturesDiedThisTurn
@[match_pattern] abbrev lifeLostThisTurn : NumberSelector := .turnEvent .lifeLostThisTurn

end NumberSelector

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
  /-- Sacrifice `n` permanents `what` names. -/
  | sacrifice (n : NumberSelector) (what : ObjectSelector)
  /-- Discard `n` cards `what` names. -/
  | discard (n : NumberSelector) (what : ObjectSelector)
  /-- Pay any one of `costs`. -/
  | or (costs : List CostSelector)
deriving Repr, Inhabited, BEq

/-- Permanent, source, and target state conditions (CR 110 / CR 205 / CR 208). -/
inductive StateCondition where
  /-- The source is missing, has left the battlefield, or has a hope counter. -/
  | hopeOnSource
  /-- Equipment is attached to the source, or its last-known power is positive when the source has left. -/
  | attachedEquipment
  /-- The creature that caused this has greater power than the source. -/
  | causeGreaterPower
  /-- The creature that caused this has greater toughness than the source. -/
  | causeGreaterToughness
  /-- The targeted permanent has this subtype. -/
  | subtype (subtype : String)
  /-- The targeted spell's mana value was this much or less (CR 202.3e). -/
  | mvAtMost (n : Nat)
  /-- The source is already prepared. -/
  | preparedSource
deriving Repr, Inhabited, BEq, DecidableEq

/-- Turn history and spell cast conditions (CR 601.2 / CR 603). -/
inductive TurnHistoryCondition where
  /-- You attacked with a permanent of this subtype this turn. -/
  | attackedWithSubtype (subtype : String)
  /-- A permanent of this subtype entered under your control this turn. -/
  | subtypeEntered (subtype : String)
  /-- `noteResolveThisTurn` recorded ordinal `n`. -/
  | nthResolve (n : Nat)
  /-- You have scried this turn. -/
  | scriedThisTurn
  /-- You have surveilled this turn. -/
  | surveilledThisTurn
  /-- An artifact entered the battlefield under your control this turn. -/
  | artifactEnteredThisTurn
  /-- Mana was spent to cast the triggering spell. -/
  | manaSpent
  /-- The resolving spell was cast from a graveyard. -/
  | castFromGraveyard
  /-- The resolving spell was cast using teamwork. -/
  | teamwork
  /-- A gift was promised as the spell was cast. -/
  | giftPromised
  /-- The resolving spell was not cast from your hand. -/
  | notFromHand
deriving Repr, Inhabited, BEq, DecidableEq

/-- Earlier-step resolution note conditions (CR 608.2c). -/
inductive StepNoteCondition where
  /-- An earlier step removed a hope counter. -/
  | removedHope
  /-- An earlier step dealt damage to a permanent of this subtype. -/
  | dealtDamageToSubtype (subtype : String)
  /-- An earlier step returned a permanent to its owner's hand. -/
  | returnedPermanent
  /-- You controlled the creature an earlier step destroyed. -/
  | youControlledDestroyed
  /-- You have an enduring story, and an earlier step discarded your hand. -/
  | enduringStoryNoted
  /-- An earlier `.sacrifice .source .noted` sacrificed the source. -/
  | sourceWasSacrificed
  /-- An earlier `.sacrifice .plan .forReflexive` sacrificed the Plan. -/
  | planWasSacrificed
  /-- An earlier step attached Equipment to a creature that is still in play. -/
  | equipmentAttached
  /-- `.mill` noted `.opponentsMilled`: an opponent milled a card. -/
  | opponentsMilled
  /-- The card `revealLibrary .untilCreature` revealed has mana value at most the lands the controller controls. -/
  | revealedManaValueAtMostLands
  /-- An earlier Enrage trigger noted an additional combat phase. -/
  | enrageGrantsCombat
deriving Repr, Inhabited, BEq, DecidableEq

/-- When `TriggerResolution.if` and `TriggerResolution.ifElse` choose a branch.
`not` negates another condition. `or` holds when any of its conditions hold.
`atLeast` holds when its first number is at least its second. -/
inductive ConditionSelector where
  /-- The first number is at least the second. -/
  | atLeast (left right : NumberSelector)
  /-- `cond` does not hold. -/
  | not (cond : ConditionSelector)
  /-- Any of `conds` holds. Once one holds, later conditions are not checked. -/
  | or (conds : List ConditionSelector)
  /-- Permanent, source, or target state condition (CR 110 / CR 205 / CR 208). -/
  | state (s : StateCondition)
  /-- Turn history or spell cast condition (CR 601.2 / CR 603). -/
  | turnHistory (t : TurnHistoryCondition)
  /-- Earlier-step resolution note condition (CR 608.2c). -/
  | stepNote (n : StepNoteCondition)
deriving Repr, Inhabited, BEq

namespace ConditionSelector

-- StateCondition aliases
@[match_pattern] abbrev hopeOnSource : ConditionSelector := .state .hopeOnSource
@[match_pattern] abbrev attachedEquipment : ConditionSelector := .state .attachedEquipment
@[match_pattern] abbrev causeGreaterPower : ConditionSelector := .state .causeGreaterPower
@[match_pattern] abbrev causeGreaterToughness : ConditionSelector := .state .causeGreaterToughness
@[match_pattern] abbrev subtype (subtype : String) : ConditionSelector := .state (.subtype subtype)
@[match_pattern] abbrev mvAtMost (n : Nat) : ConditionSelector := .state (.mvAtMost n)
@[match_pattern] abbrev preparedSource : ConditionSelector := .state .preparedSource
@[match_pattern] abbrev ifNotPrepared : ConditionSelector := .not .preparedSource
@[match_pattern] abbrev ifThreeCreaturesDied : ConditionSelector := .atLeast .creaturesDiedThisTurn (.fixed 3)

-- TurnHistoryCondition aliases
@[match_pattern] abbrev attackedWithSubtype (subtype : String) : ConditionSelector := .turnHistory (.attackedWithSubtype subtype)
@[match_pattern] abbrev subtypeEntered (subtype : String) : ConditionSelector := .turnHistory (.subtypeEntered subtype)
@[match_pattern] abbrev nthResolve (n : Nat) : ConditionSelector := .turnHistory (.nthResolve n)
@[match_pattern] abbrev scriedThisTurn : ConditionSelector := .turnHistory .scriedThisTurn
@[match_pattern] abbrev surveilledThisTurn : ConditionSelector := .turnHistory .surveilledThisTurn
@[match_pattern] abbrev artifactEnteredThisTurn : ConditionSelector := .turnHistory .artifactEnteredThisTurn
@[match_pattern] abbrev manaSpent : ConditionSelector := .turnHistory .manaSpent
@[match_pattern] abbrev castFromGraveyard : ConditionSelector := .turnHistory .castFromGraveyard
@[match_pattern] abbrev teamwork : ConditionSelector := .turnHistory .teamwork
@[match_pattern] abbrev giftPromised : ConditionSelector := .turnHistory .giftPromised
@[match_pattern] abbrev notFromHand : ConditionSelector := .turnHistory .notFromHand

-- StepNoteCondition aliases
@[match_pattern] abbrev removedHope : ConditionSelector := .stepNote .removedHope
@[match_pattern] abbrev dealtDamageToSubtype (subtype : String) : ConditionSelector := .stepNote (.dealtDamageToSubtype subtype)
@[match_pattern] abbrev returnedPermanent : ConditionSelector := .stepNote .returnedPermanent
@[match_pattern] abbrev youControlledDestroyed : ConditionSelector := .stepNote .youControlledDestroyed
@[match_pattern] abbrev enduringStoryNoted : ConditionSelector := .stepNote .enduringStoryNoted
@[match_pattern] abbrev sourceWasSacrificed : ConditionSelector := .stepNote .sourceWasSacrificed
@[match_pattern] abbrev planWasSacrificed : ConditionSelector := .stepNote .planWasSacrificed
@[match_pattern] abbrev equipmentAttached : ConditionSelector := .stepNote .equipmentAttached
@[match_pattern] abbrev opponentsMilled : ConditionSelector := .stepNote .opponentsMilled
@[match_pattern] abbrev revealedManaValueAtMostLands : ConditionSelector := .stepNote .revealedManaValueAtMostLands
@[match_pattern] abbrev enrageGrantsCombat : ConditionSelector := .stepNote .enrageGrantsCombat

end ConditionSelector


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
  /-- The creature that caused this trigger deals the damage. -/
  | fromCause
  /-- Pre-allocated divided damage (CR 601.2d). -/
  | preallocated
  /-- If the land that caused this is a Mountain, add {R}. -/
  | addRedIfMountain
deriving Repr, Inhabited, BEq

/-- What `TriggerResolution.lose` removes. -/
inductive AbilitySelector where
  /-- Indestructible, until end of turn. -/
  | indestructible
  /-- All abilities, for as long as the source remains on the battlefield. -/
  | allAbilities
deriving Repr, Inhabited, BEq

/-- What `TriggerResolution.removeCounters` removes. -/
inductive TriggerRemoveWhat where
  /-- One hope counter. A later `«if» .removedHope` sees whether one was removed. -/
  | hope
  /-- Every counter on that permanent. -/
  | all
  /-- Up to `n` counters of the controller's choice. -/
  | upTo (n : Nat)
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
  /-- One +1/+1 counter for each land the controller controls. -/
  | plusOnePerLand
  /-- +1/+1 counters equal to the number of cards in the controller's hand. -/
  | plusOneEqualToHand
  /-- The counters the causing object had as it left the battlefield (The Ozolith). -/
  | causeCounters
  /-- X +1/+1 counters, where X was chosen as the ability was activated. -/
  | plusOneChosenX
  /-- If cast from a graveyard, one +1/+1 counter for every three cards in the controller's graveyard. -/
  | plusOnePerThreeGraveyardIfFromGy
  /-- Minus-one counters equal to the greatest mana value among cards in the controller's graveyard. -/
  | minusOneGreatestGraveyardMv
  /-- Tap and put X stun counters, where X is the loyalty removed to activate this ability. -/
  | stunRemovedLoyalty
  /-- Draw a card, then put a +1/+1 counter for each card you've discarded this turn. -/
  | plusOnePerDiscardAfterDraw
  /-- Give each recipient another counter of each kind already on it `times` times (proliferate, CR 701.34). -/
  | eachKindOnIt (times : NumberSelector := .fixed 1)
  /-- Remove counters as `what` says (CR 122). -/
  | remove (what : TriggerRemoveWhat)
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
  /-- Creatures you control gain indestructible until end of turn. -/
  | teamIndestructible
  /-- If X is 5 or more, destroy all other creatures. -/
  | destroyOthersIfXAtLeast5
  /-- Gain X life first, and if X is 5 or more, destroy all other creatures. -/
  | gainXLifeAndDestroyOthersIf5
  /-- Only if you gained life this turn. -/
  | ifGainedLife
  /-- Only if you are the monarch. -/
  | ifMonarch
  /-- If the source is not Mardu, create the Goblin and grant lifelink and haste until end of turn. -/
  | ifNotMarduLifelinkHaste
  /-- Put a card exiled with the source into its owner's graveyard, then create a Treasure if it was a land or a Rogue otherwise. -/
  | currencyReturn
  /-- Lose 1 life first. -/
  | lose1Life
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
  /-- For as long as they remain exiled, you may play them if you control `subtype`. -/
  | playIfYouControlSubtype (subtype : String)
  /-- You may play those cards this turn by paying life equal to their mana value rather than paying their mana cost. -/
  | playForLifeThisTurn
  /-- You may cast that card. If you don't, this deals `damage` damage to each opponent. -/
  | mayCastElseDamageOpponents (damage : Nat)
  /-- You may cast spells from among those cards for as long as they remain exiled, spending mana as though it were mana of any type. -/
  | anyManaWhileExiled
  /-- If its mana value was `maxMv` or less, return it tapped under your control and exile it at the next end step. -/
  | returnBrieflyIfMvAtMost (maxMv : Nat)
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
  /-- Empower Jace X, where X is the number of creatures exiled this way. -/
  | empowerJace
  /-- You gain `life` life if teamwork was paid. -/
  | gainLifeIfTeamwork (life : Nat)
  /-- Its controller may search their library for that many basic land cards and put them onto the battlefield tapped. -/
  | controllerMaySearchBasic
  /-- Draw that many cards after exiling your hand. -/
  | thenDrawThree
  /-- Counter the spell; if a permanent spell is countered this way, exile it and you may cast it without paying its mana cost. -/
  | counteredPermanentMayCast
  /-- Each player may put any number of creature cards from their hand onto the battlefield, then return all cards exiled this way to their owners' hands and exile the resolving spell. -/
  | worldsWithinWorlds
  /-- Reveal from the top of your library until a creature or planeswalker card, put it onto the battlefield, and put the rest on the bottom in a random order. -/
  | revealUntilCreatureOrPlaneswalker
  /-- Exile target permanent or card; log when Despark has no legal target. -/
  | despark
  /-- Its controller gains life equal to its power (Swords to Plowshares). -/
  | controllerGainsLifePower
  /-- Incubate X, where X is the number of creatures exiled this way (Sunfall). -/
  | incubateCount
  /-- Reveal creature cards from the top of your library until that many are revealed, put them onto the battlefield, and shuffle the rest into your library. -/
  | revealCreaturesToBattlefield
  /-- At the beginning of the next end step, reveal creature cards from the top of your library until that many are revealed and put them onto the battlefield. -/
  | revealCreaturesAtEndStep
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
  /-- If you sacrifice a creature this way, create a 4/4 Beast. -/
  | ifYouDoCreateBeast
  /-- If seven or more cards are in your graveyard, sacrifice the source, deal 2 damage to each opponent, and gain 2 life. -/
  | eyeOfJaceIfSevenInGy
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
  /-- Exile up to one target nonland card of each card type from your graveyard, copy them, and cast copies with total mana value 6 or less without paying their mana costs. -/
  | uldarosGraveyardTypes
  /-- Copy the cards exiled to pay this boast activation and cast up to three of the copies without paying their mana costs. -/
  | boastExiled
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
  /-- At the beginning of the next upkeep, create a 4/4 white Bird Soldier creature token with flying for each creature returned to your hand this way. -/
  | delayedBirds
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
  /-- At the beginning of the next end step. -/
  | atNextEndStep
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
  /-- Entering as Food artifacts in addition to their other types. -/
  | asFood
deriving Repr, Inhabited, BEq

namespace TriggerPutNote

/-- Modifications carried by `entering`. Any other note changes nothing. -/
def enterMods : TriggerPutNote → List TriggerEnterWith
  | .entering mods => mods
  | _ => []

end TriggerPutNote

/-- How `TriggerResolution.chooseModes` chooses those modes. -/
inductive TriggerModeHow where
  /-- The controller chooses one of the alternatives (`Resolution.or`). -/
  | one
  /-- Resolve the first branch when `cond` holds, and the second otherwise (`Resolution.ifElse`). -/
  | ifElse (cond : ConditionSelector)
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
  /-- Resolve Hawkeye's Trick Arrows modes by index. -/
  | hawkeyeIndices (indices : List Nat)
  /-- Choose `count` modes of `CardDef.fraTriggerModes` when put on the stack. -/
  | fraTrigger (count : Nat)
  /-- Resolve the single mode when `cond` holds (CR 608.2c). -/
  | «if» (cond : ConditionSelector)
  /-- Resolve the single mode unless its controller pays `{n}` (CR 118.12). -/
  | unlessPays (n : Nat)
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
  /-- If it wasn't attacking, its controller draws a card. -/
  | drawIfNotAttacking
  /-- If it was a legendary enchantment, draw a card. -/
  | drawIfLegendaryEnchantment
  /-- Its controller creates a 1/1 white Human creature token. -/
  | controllerCreatesHuman
  /-- You gain 1 life for each creature destroyed this way. -/
  | gainLifeEach
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
  /-- Permanently gain control of up to one targeted artifact per opponent. -/
  | oppArtifacts
  /-- Gain control until end of turn, or until the end of your next turn if you control a Villain with greater mana value. -/
  | untilEotOrNextIfVillain
  /-- Exchange control of two targeted permanents sharing a card type (CR 701.10). -/
  | exchangeTargets
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
  /-- Can't block this turn. -/
  | block (who : ObjectSelector := .target)
  /-- Players can't cast spells this turn. -/
  | castSpellsThisTurn (who : ObjectSelector := .any)
  /-- Can't be countered. -/
  | beCountered (who : ObjectSelector := .target)
  /-- Can't be blocked this turn by creatures controlled by a chosen player with the most life. -/
  | beBlockedByMostLifePlayer (who : ObjectSelector := .target)
  /-- Can't attack Jaces this turn unless their controller pays {1} for each creature. -/
  | attackJaces (who : ObjectSelector := .opponentsCreatures)
deriving Repr, Inhabited, BEq

/-- Layer 4 type-changing and animation grants (CR 613.1d). -/
inductive Layer4TypeGrant where
  /-- Become an artifact in addition to its other types (CR 613.1d Layer 4). -/
  | artifact
  /-- Become a Bear in addition to its other types. -/
  | bearType
  /-- If this Equipment isn't a creature, it becomes a 0/0 Construct Hero artifact creature with flying. -/
  | constructHero
  /-- The source Vehicle becomes an artifact creature until end of turn (crew, CR 702.122). -/
  | artifactCreatureVehicle
  /-- Become a `p`/`t` artifact creature and gain `kw` until end of turn. -/
  | artifactCreature (p : Int := 4) (t : Int := 4) (kw : String := "flying")
  /-- Become a creature of `subtype` with power and toughness equal to lands you control. -/
  | subtypeWithLandsPT (subtype : String)
  /-- Become `types` with base power and toughness `power`/`toughness` and gain `k` until end of turn. -/
  | typesPTAndKeywords (types : Array String) (power toughness : Int) (k : Keywords)
  /-- Animate the source land as a `power`/`toughness` creature until end of turn. -/
  | animateLand (power toughness : Nat) (flying firstStrike : Bool)
deriving Repr, Inhabited, BEq

/-- Layer 6 ability-adding, keyword, ability-removing, and restriction grants (CR 613.1f). -/
inductive Layer6AbilityGrant where
  /-- Protection from everything until that player's next turn. -/
  | protectionEverything
  /-- These keywords until end of turn. -/
  | keywords (k : Keywords)
  /-- Hexproof for as long as the source remains on the battlefield. -/
  | hexproofWhileSource
  /-- Your choice of the keywords coded in `options` until end of turn. -/
  | choiceOfKeywords (options : List Nat)
  /-- Landfall: create a 1/1 green Elf whenever a land you control enters. -/
  | landfallCreateElf
  /-- Until end of turn, the source gains "{T}: This deals damage equal to its power to any other target." -/
  | ironFistTap
  /-- Until end of turn, "Whenever this creature deals combat damage to a player, create a Treasure token." -/
  | combatDamageCreateTreasure
  /-- Until end of turn, "Whenever this creature deals combat damage to a player, draw two cards." -/
  | combatDamageDrawTwo
  /-- Flashback until end of turn equal to its mana cost. -/
  | flashback
  /-- "{T}: Add {C}{C}" until the exiled source is cast, and you may cast the source while exiled. -/
  | emrakulManaAndCast
  /-- Lose `what` abilities (CR 613.1f Layer 6). -/
  | lose (what : AbilitySelector)
  /-- Prevent `action` (CR 613.1f / CR 508 / CR 509). -/
  | cant (action : ActionSelector)
deriving Repr, Inhabited, BEq

/-- Layer 7 power/toughness and combat damage assignment grants (CR 613.1g / CR 510.1c). -/
inductive Layer7PtGrant where
  /-- Set base power and toughness to `power`/`toughness` (CR 613.4b Layer 7b). -/
  | basePT (power toughness : NumberSelector)
  /-- Until end of turn, the source's base power is the number of cards in its controller's hand. -/
  | basePowerEqualHand
  /-- Until end of turn, creatures with toughness greater than their power assign combat damage equal to their toughness. -/
  | assignCombatDamageEqualToughness
deriving Repr, Inhabited, BEq

/-- Replacement, prevention, permission, cost-reduction, turn, and emblem grants (CR 614 / CR 615 / CR 114). -/
inductive RuleEffectGrant where
  /-- Replacement effect: if the target permanent would die this turn, exile it instead (CR 614.1). -/
  | replace
  /-- Prevent all damage this permanent would deal for as long as the source remains (CR 615). -/
  | preventDamageWhileSource
  /-- Spells of `which` cost `n` less to cast this turn (CR 601.2f). -/
  | spellsCostLess (which : SpellCostLess) (n : NumberSelector)
  /-- You may play the exiled card until the end of your next turn. -/
  | playNotedUntilNextTurn
  /-- Until end of turn, loyalty abilities of Jace planeswalkers you control may be activated at instant speed. -/
  | jaceLoyaltyAtInstantSpeed
  /-- Until end of turn, whenever you tap a Mountain for mana, add an additional {R}. -/
  | mountainsAddExtraRed
  /-- Emblem with "Whenever you cast a spell, this emblem deals `n` damage to any target." -/
  | emblemCastSpellDamage (n : Nat)
  /-- Emblem with "Whenever you cast a spell, draw a card." -/
  | emblemDrawOnCast
  /-- Emblem with "Creatures you control get +2/+2." -/
  | emblemCreaturesGetTwoTwo
  /-- Emblem with "Creatures you control get +2/+2 and have flying." -/
  | emblemCreaturesGetTwoTwoFlying
  /-- Copy the next instant or sorcery spell you cast this turn (optionally limited to source's power). -/
  | nextSpellCopy (mvAtMostSourcePower : Bool := false)
  /-- Play an additional land this turn (CR 305.2). -/
  | extraLand
  /-- Take an extra turn after this one; power-up abilities can't be activated during it (CR 500.7). -/
  | extraTurn
  /-- Protection from everything, life total can't change, and nonland permanents phase out until next turn. -/
  | teferisReproach
  /-- Additional combat phase after this one (CR 500.8). -/
  | additionalCombatPhase
  /-- You win the game (CR 104.2a). -/
  | winTheGame
deriving Repr, Inhabited, BEq

/-- One-shot keyword actions and permanent state changes (CR 701 / CR 702 / CR 724). -/
inductive ActionStateGrant where
  /-- Mark tokens created by an earlier step attacking. -/
  | attacking
  /-- Choose new targets for the spell (CR 115.7). -/
  | newTargets
  /-- Transform the permanent (CR 701.28). -/
  | transformed
  /-- Harness this Infinity Stone (MSH). -/
  | harnessed
  /-- Put an indestructible counter and a +1/+1 counter on the target. -/
  | arwenShare
  /-- Phase out the target, or each creature target player controls if kicked (CR 702.26). -/
  | phaseOutKicker
  /-- You become the monarch (CR 724). -/
  | monarch
  /-- Explore (CR 701.40). -/
  | explored
  /-- Transform an Incubator token into a 0/0 Phyrexian artifact creature (CR 701.51). -/
  | transformedIncubator
  /-- Turn the source face up (CR 702.37). -/
  | faceUp
  /-- Become prepared (or unprepared if `prepared == false`). -/
  | prepared (prepared : Bool := true)
  /-- Investigate (CR 701.36). -/
  | investigate
  /-- Empower Jace `n` (FRA 732). -/
  | empowerJace (n : NumberSelector)
  /-- Recruit as `who` says. -/
  | recruit (who : PlayerSelector := .recruit)
  /-- Record another resolution of this ability this turn, up to `limit`. -/
  | noteResolveThisTurn (limit : Nat)
  /-- Resolve the reflexive triggered ability `kind` of an MSH card. -/
  | mshReflexive (kind paid : Nat)
  /-- Connive (CR 701.48). -/
  | connive
  /-- Fight or deal power damage (CR 701.12). -/
  | fight (how : TriggerFightHow := .mutual)
  /-- Attach to `host` (CR 701.3). -/
  | attachTo (host : ObjectSelector)
  /-- Cascade (CR 702.85). -/
  | cascade
  /-- The Ring tempts you (CR 701.54). -/
  | ringTempts
  /-- Counter target spell (CR 701.5). -/
  | counterSpell
deriving Repr, Inhabited, BEq

/-- What `TriggerResolution.grant` grants, organized by CR 613 layers, CR 614/615 rule effects, and CR 701 actions. -/
inductive TriggerGrantWhat where
  /-- Layer 6 ability-adding, keyword, ability-removing, or restriction effect (CR 613.1f). -/
  | layer6Ability (g : Layer6AbilityGrant)
  /-- Become a copy of `of` (CR 613.1a Layer 1). -/
  | copy (of : ObjectSelector)
  /-- Gain control as `how` says (CR 613.1b Layer 2). -/
  | control (how : TriggerControlHow)
  /-- Layer 4 type-changing or animation effect (CR 613.1d). -/
  | layer4Type (g : Layer4TypeGrant)
  /-- Layer 7 power/toughness or combat damage assignment effect (CR 613.1g). -/
  | layer7PT (g : Layer7PtGrant)
  /-- Replacement, prevention, permission, cost-reduction, turn, or emblem effect (CR 614 / CR 615 / CR 114). -/
  | ruleEffect (g : RuleEffectGrant)
  /-- One-shot keyword action or permanent state change (CR 701 / CR 702 / CR 724). -/
  | actionState (g : ActionStateGrant)
deriving Repr, Inhabited, BEq

namespace TriggerGrantWhat

-- Layer4TypeGrant aliases
@[match_pattern] abbrev artifact : TriggerGrantWhat := .layer4Type .artifact
@[match_pattern] abbrev bearType : TriggerGrantWhat := .layer4Type .bearType
@[match_pattern] abbrev constructHero : TriggerGrantWhat := .layer4Type .constructHero
@[match_pattern] abbrev artifactCreatureVehicle : TriggerGrantWhat := .layer4Type .artifactCreatureVehicle
@[match_pattern] abbrev artifactCreature (p : Int := 4) (t : Int := 4) (kw : String := "flying") : TriggerGrantWhat :=
  .layer4Type (.artifactCreature p t kw)
@[match_pattern] abbrev subtypeWithLandsPT (subtype : String) : TriggerGrantWhat := .layer4Type (.subtypeWithLandsPT subtype)
@[match_pattern] abbrev typesPTAndKeywords (types : Array String) (power toughness : Int) (k : Keywords) : TriggerGrantWhat :=
  .layer4Type (.typesPTAndKeywords types power toughness k)
@[match_pattern] abbrev animateLand (power toughness : Nat) (flying firstStrike : Bool) : TriggerGrantWhat :=
  .layer4Type (.animateLand power toughness flying firstStrike)

-- Layer6AbilityGrant aliases
@[match_pattern] abbrev protectionEverything : TriggerGrantWhat := .layer6Ability .protectionEverything
@[match_pattern] abbrev keywords (k : Keywords) : TriggerGrantWhat := .layer6Ability (.keywords k)
def doubleStrike : TriggerGrantWhat := .keywords Keyword.doubleStrike
@[match_pattern] abbrev hexproofWhileSource : TriggerGrantWhat := .layer6Ability .hexproofWhileSource
@[match_pattern] abbrev choiceOfKeywords (options : List Nat) : TriggerGrantWhat := .layer6Ability (.choiceOfKeywords options)
@[match_pattern] abbrev landfallCreateElf : TriggerGrantWhat := .layer6Ability .landfallCreateElf
@[match_pattern] abbrev ironFistTap : TriggerGrantWhat := .layer6Ability .ironFistTap
@[match_pattern] abbrev combatDamageCreateTreasure : TriggerGrantWhat := .layer6Ability .combatDamageCreateTreasure
@[match_pattern] abbrev combatDamageDrawTwo : TriggerGrantWhat := .layer6Ability .combatDamageDrawTwo
@[match_pattern] abbrev flashback : TriggerGrantWhat := .layer6Ability .flashback
@[match_pattern] abbrev emrakulManaAndCast : TriggerGrantWhat := .layer6Ability .emrakulManaAndCast
@[match_pattern] abbrev lose (what : AbilitySelector) : TriggerGrantWhat := .layer6Ability (.lose what)
@[match_pattern] abbrev cant (action : ActionSelector) : TriggerGrantWhat := .layer6Ability (.cant action)

-- Layer7PtGrant aliases
@[match_pattern] abbrev basePT (power toughness : NumberSelector) : TriggerGrantWhat := .layer7PT (.basePT power toughness)
@[match_pattern] abbrev basePowerEqualHand : TriggerGrantWhat := .layer7PT .basePowerEqualHand
@[match_pattern] abbrev assignCombatDamageEqualToughness : TriggerGrantWhat := .layer7PT .assignCombatDamageEqualToughness

-- RuleEffectGrant aliases
@[match_pattern] abbrev replace : TriggerGrantWhat := .ruleEffect .replace
@[match_pattern] abbrev preventDamageWhileSource : TriggerGrantWhat := .ruleEffect .preventDamageWhileSource
@[match_pattern] abbrev spellsCostLess (which : SpellCostLess) (n : NumberSelector) : TriggerGrantWhat := .ruleEffect (.spellsCostLess which n)
@[match_pattern] abbrev playNotedUntilNextTurn : TriggerGrantWhat := .ruleEffect .playNotedUntilNextTurn
@[match_pattern] abbrev jaceLoyaltyAtInstantSpeed : TriggerGrantWhat := .ruleEffect .jaceLoyaltyAtInstantSpeed
@[match_pattern] abbrev mountainsAddExtraRed : TriggerGrantWhat := .ruleEffect .mountainsAddExtraRed
@[match_pattern] abbrev emblemCastSpellDamage (n : Nat) : TriggerGrantWhat := .ruleEffect (.emblemCastSpellDamage n)
@[match_pattern] abbrev emblemDrawOnCast : TriggerGrantWhat := .ruleEffect .emblemDrawOnCast
@[match_pattern] abbrev emblemCreaturesGetTwoTwo : TriggerGrantWhat := .ruleEffect .emblemCreaturesGetTwoTwo
@[match_pattern] abbrev emblemCreaturesGetTwoTwoFlying : TriggerGrantWhat := .ruleEffect .emblemCreaturesGetTwoTwoFlying
@[match_pattern] abbrev nextSpellCopy (mvAtMostSourcePower : Bool := false) : TriggerGrantWhat := .ruleEffect (.nextSpellCopy mvAtMostSourcePower)
@[match_pattern] abbrev extraLand : TriggerGrantWhat := .ruleEffect .extraLand
@[match_pattern] abbrev extraTurn : TriggerGrantWhat := .ruleEffect .extraTurn
@[match_pattern] abbrev teferisReproach : TriggerGrantWhat := .ruleEffect .teferisReproach
@[match_pattern] abbrev additionalCombatPhase : TriggerGrantWhat := .ruleEffect .additionalCombatPhase
@[match_pattern] abbrev winTheGame : TriggerGrantWhat := .ruleEffect .winTheGame

-- ActionStateGrant aliases
@[match_pattern] abbrev attacking : TriggerGrantWhat := .actionState .attacking
@[match_pattern] abbrev newTargets : TriggerGrantWhat := .actionState .newTargets
@[match_pattern] abbrev transformed : TriggerGrantWhat := .actionState .transformed
@[match_pattern] abbrev harnessed : TriggerGrantWhat := .actionState .harnessed
@[match_pattern] abbrev arwenShare : TriggerGrantWhat := .actionState .arwenShare
@[match_pattern] abbrev phaseOutKicker : TriggerGrantWhat := .actionState .phaseOutKicker
@[match_pattern] abbrev monarch : TriggerGrantWhat := .actionState .monarch
@[match_pattern] abbrev explored : TriggerGrantWhat := .actionState .explored
@[match_pattern] abbrev transformedIncubator : TriggerGrantWhat := .actionState .transformedIncubator
@[match_pattern] abbrev faceUp : TriggerGrantWhat := .actionState .faceUp
@[match_pattern] abbrev prepared (prepared : Bool := true) : TriggerGrantWhat := .actionState (.prepared prepared)
@[match_pattern] abbrev investigate : TriggerGrantWhat := .actionState .investigate
@[match_pattern] abbrev empowerJace (n : NumberSelector) : TriggerGrantWhat := .actionState (.empowerJace n)
@[match_pattern] abbrev recruit (who : PlayerSelector := .recruit) : TriggerGrantWhat := .actionState (.recruit who)
@[match_pattern] abbrev noteResolveThisTurn (limit : Nat) : TriggerGrantWhat := .actionState (.noteResolveThisTurn limit)
@[match_pattern] abbrev mshReflexive (kind paid : Nat) : TriggerGrantWhat := .actionState (.mshReflexive kind paid)
@[match_pattern] abbrev connive : TriggerGrantWhat := .actionState .connive
@[match_pattern] abbrev fight (how : TriggerFightHow := .mutual) : TriggerGrantWhat := .actionState (.fight how)
@[match_pattern] abbrev attachTo (host : ObjectSelector) : TriggerGrantWhat := .actionState (.attachTo host)
@[match_pattern] abbrev cascade : TriggerGrantWhat := .actionState .cascade
@[match_pattern] abbrev ringTempts : TriggerGrantWhat := .actionState .ringTempts
@[match_pattern] abbrev counterSpell : TriggerGrantWhat := .actionState .counterSpell

end TriggerGrantWhat


/-- What a later step of `TriggerResolution.mill` can read. -/
inductive TriggerMillNote where
  /-- Nothing beyond the mill. -/
  | none
  /-- The cards the controller milled. -/
  | milledCards
  /-- Whether an opponent milled a card. -/
  | opponentsMilled
  /-- Put milled cards into hand as `which` says. -/
  | toHand (which : MilledToHand)
  /-- You may put a permanent card from among the milled cards into your hand, and you gain `life` life. -/
  | permanentAndGainLife (life : Nat)
  /-- You may put a `subtype` or enchantment card from among the milled cards into your hand. -/
  | subtypeOrEnchantmentToHand (subtype : String)
  /-- Each player may cast an instant or sorcery card milled this way without paying its mana cost. -/
  | freeCastFromGraveyard
deriving Repr, Inhabited, BEq

/-- How many cards `TriggerResolution.revealFromHand` shows (CR 701.16). -/
inductive TriggerRevealCount where
  /-- The whole hand. -/
  | hand
  /-- One card, plus one for each creature card in the controller's
  graveyard. A smaller hand is shown in full. -/
  | onePlusCreatureCards
deriving Repr, Inhabited, BEq

/-- How far `TriggerResolution.revealLibrary` looks from the top of a library. -/
inductive TriggerLibraryHow where
  /-- The top `n` cards. Looking at zero cards finds nothing. -/
  | top (n : Nat)
  /-- The top `n` cards, where `n` is a `NumberSelector`. -/
  | topNumber (n : NumberSelector)
  /-- Cards until a creature card. An empty library finds nothing. -/
  | untilCreature
  /-- Cards until a Saga card. An empty library finds nothing. -/
  | untilSaga
  /-- Cards until an instant or sorcery card. An empty library finds nothing. -/
  | untilInstantOrSorcery
  /-- Cards until a nonland card. An empty library finds nothing. -/
  | untilNonland
  /-- Cards until one creature card per opponent, put under each opponent's control and goaded. -/
  | untilCreaturesPerOpponent
  /-- Cards until a historic permanent card, put onto the battlefield and you lose life equal to its mana value. -/
  | untilHistoric
  /-- Draw a card, then on the first resolution this turn reveal until a creature card and put it onto the battlefield. -/
  | firstResolveUntilCreature
  /-- Reveal cards from hand (CR 701.16). -/
  | fromHand (count : TriggerRevealCount)
  /-- Search a library (CR 701.23). -/
  | search
deriving Repr, Inhabited, BEq

/-- Where `TriggerResolution.putOnLibrary` puts the card. -/
inductive TriggerLibraryPlace where
  /-- On top of the owner's library. -/
  | top
  /-- On the bottom of the owner's library. A card from hand uses the
  controller's library. -/
  | bottom
  /-- On the owner's choice of the top or bottom of their library. -/
  | topOrBottom
  /-- Shuffled into the owner's library (CR 701.24). -/
  | shuffled
  /-- Second from the top or on the bottom of its owner's library, then up to one target creature you control connives. -/
  | secondOrBottomThenConnive
  /-- Its owner may put it on top of their library; if they do, deal 2 damage to them, otherwise put it on the bottom. -/
  | topOrBottomDamage2
  /-- Draw `drawN` cards, then put `putN` cards from your hand on top of your library. -/
  | topAfterDraw (drawN putN : Nat)
  /-- On the bottom of its owner's library, then its controller reveals until a creature card and puts it onto the battlefield. -/
  | bottomRevealCreature
  /-- Draw two cards, then put a card from your hand on the bottom of your library. -/
  | bottomAfterDrawTwo
deriving Repr, Inhabited, BEq

/-- What a later step of `TriggerResolution.surveil` can read or do. -/
inductive TriggerSurveilNote where
  /-- Surveil only. -/
  | none
  /-- Arm the following surveil to return a card with mana value at most the life gained this turn. -/
  | armReturnLifeGained
  /-- Put a noncreature, nonland card put into your graveyard this way into your hand. -/
  | returnNoncreatureNonland
  /-- Then if seven or more cards are in your graveyard, sacrifice the source, deal 2 damage to each opponent, and gain 2 life. -/
  | eyeOfJace
deriving Repr, Inhabited, BEq

/-- Which outcome of `TriggerResolution.may` resolves `follow`. -/
inductive TriggerMayWhen where
  /-- The player performed `action`. Declining skips `follow`. -/
  | ifYouDo
  /-- The player declined `action`. Performing `action` skips `follow`. -/
  | ifYouDont
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
  | scry (n : NumberSelector) (surveil : Option TriggerSurveilNote := none)
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
  `.sequence [.putCounters (.ofKind .trample) .permanent, .grant .bearType .target]`.
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
  Any other count gains that much life. A count that cannot be read
  gains nothing. -/
  | gainLife (amount : NumberSelector) (who : PlayerSelector := .you) (lose : Bool := false)
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
  /-- Tap or untap permanents, as `who` and `tapped` say.
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
  Any other permanent the selector names is tapped or untapped. A card or a hand
  is not. -/
  | tap (who : ObjectSelector) (tapped : Bool := true)
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
  | amass (amount : NumberSelector) (subtype : String := "Goblin")
      (attachSource : Bool := false) (who : PlayerSelector := .you)
  /-- Create tokens. How many is `amount`. Who receives them is a
  `PlayerSelector`. `kind` says which token, and `note` says what a later
  step can read.
  `n` of `kind` is `.createTokens kind (.fixed n) tapped`.
  An Axe is `.createTokens .axe (.fixed 1) false`.
  Attaching that Axe is
  `.createTokens .axe (.fixed 1) false (note := .attachReflexive)`.
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
  Zabu is `.createTokens .zabu (.fixed 1) false`.
  The announced opponent creates The Void with
  `.createTokens .theVoid (.fixed 1) false (.target .opponent)`.
  Redwing is `.createTokens .redwing (.fixed 1) false`.
  An Alien, remembering invasion counters, is
  `.createTokens .alien (.fixed 1) false (note := .invasion)`.
  A Sturdy Shield, remembered for a later attach, is
  `.createTokens .sturdyShield (.fixed 1) false (note := .remember)`.
  The target's controller creates a Treasure with
  `.createTokens .treasure (.fixed 1) false (who := .controller .target)`.
  One 1/1 blue Merfolk for each blue mana symbol in the spell that caused
  this is `.createTokens .merfolk .blueManaSymbols false`.
  Any other count creates that many of the named token for the players
  the selector names. Zero creates nothing. A count that cannot be read
  creates nothing. -/
  | createTokens (kind : TokenKind) (amount : NumberSelector) (tapped : Bool := false)
      (who : PlayerSelector := .you) (note : TriggerTokenNote := .none)
  /-- Add mana, as `amount` says. `types` is the printed mana, and `note`
  describes any color choice or spending restriction.
  Adding those types once is `.addMana types`.
  Adding them `n` times is `.addMana types (.fixed n)`.
  Zero times adds nothing.
  {G} for each charge counter on the source is
  `.addMana #[.colored .green] .perChargeCounter`.
  A source that has left uses its last-known charge counters.
  Any other count adds the printed types that many times. Zero adds
  nothing. A count that cannot be read adds nothing. -/
  | addMana (types : Array ManaType) (amount : NumberSelector := .fixed 1)
      (note : ManaSpendNote := .none)
  /-- Resolve these modes, as `how` says.
  Alliance is `.chooseModes TriggerResolution.allianceModes .oneUnusedThisTurn`.
  Gollum is `.chooseModes TriggerResolution.gollumModes .oneUnused`.
  Chosen up to X, in printed order, is
  `.chooseModes TriggerResolution.upToXModes .alreadyChosen`.
  A +1/+1 counter on the source, or removing a counter to draw, is
  `.chooseModes TriggerResolution.hydeModes .plusOneOrRemoveCounter`.
  One unused Vision mode this turn is
  `.chooseModes TriggerResolution.visionModes .vision`. -/
  | chooseModes (modes : List Resolution) (how : TriggerModeHow := .one)
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
  /-- Grant an ability or continuous effect. `what` says which, and `who` says to whom.
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
  | grant (what : TriggerGrantWhat) (who : ObjectSelector := .target)
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
  /-- Mill cards (CR 701.13), as `amount` and `who` say. `note` says what a
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
  /-- A resolution that is not a spell shape. It does not play an extra land. -/
  | unrecognized
deriving Repr, Inhabited, BEq

namespace Resolution

/-- Search a library (CR 701.23), then resolve `thenDo` for the card that was found. -/
@[match_pattern] abbrev searchLibrary (thenDo : Resolution) : Resolution :=
  .revealLibrary .search thenDo .you

/-- Attach `what` to `host` (CR 701.3). -/
@[match_pattern] abbrev attach (what host : ObjectSelector) : Resolution :=
  .grant (.attachTo host) what

/-- Resolve `thenDo` when `cond` holds (CR 608.2c). -/
@[match_pattern] abbrev «if» (cond : ConditionSelector) (thenDo : Resolution) : Resolution :=
  .chooseModes [thenDo] (.«if» cond)

/-- Connive (CR 701.48). `who` says which creature. -/
@[match_pattern] abbrev connive (who : ObjectSelector := .source) : Resolution :=
  .grant .connive who

/-- A creature fights, or deals damage equal to its power (CR 701.12). `who` says
which creature, and `how` says which. -/
@[match_pattern] abbrev fight (who : ObjectSelector := .source) (how : TriggerFightHow := .mutual) : Resolution :=
  .grant (.fight how) who

/-- Resolve `r` unless its controller pays `{n}` (CR 118.12). -/
@[match_pattern] abbrev unlessPays (r : Resolution) (n : Nat) : Resolution :=
  .chooseModes [r] (.unlessPays n)

/-- Cascade: exile until a cheaper nonland, then you may cast it (CR 702.85). -/
@[match_pattern] abbrev cascade : Resolution :=
  .grant .cascade .source

/-- The Ring tempts you (CR 701.54). -/
@[match_pattern] abbrev ringTempts : Resolution :=
  .grant .ringTempts .youIfCast

/-- There is an additional combat phase after this one (CR 500.8). -/
@[match_pattern] abbrev additionalCombatPhase : Resolution :=
  .grant .additionalCombatPhase .youIfCast

/-- You win the game (CR 104.2a). -/
@[match_pattern] abbrev winTheGame : Resolution :=
  .grant .winTheGame .youIfCast

/-- Counter the targeted spell (CR 701.5). -/
@[match_pattern] abbrev counter : Resolution :=
  .grant .counterSpell .target

/-- Surveil, as `n` and `note` say (CR 701.25). -/
@[match_pattern] abbrev surveil (n : NumberSelector) (note : TriggerSurveilNote := .none) : Resolution :=
  .scry n (some note)

/-- A player loses life (CR 118.3a), as `amount` and `who` say. -/
@[match_pattern] abbrev loseLife (amount : NumberSelector) (who : PlayerSelector := .you) : Resolution :=
  .gainLife amount who true

/-- Untap permanents, as `who` says. -/
@[match_pattern] abbrev untap (who : ObjectSelector := .target) : Resolution :=
  .tap who false

/-- Resolve `whenTrue` when `cond` holds, and `whenFalse` otherwise. -/
@[match_pattern] abbrev ifElse (cond : ConditionSelector) (whenTrue whenFalse : Resolution) : Resolution :=
  .chooseModes [whenTrue, whenFalse] (.ifElse cond)

/-- The controller chooses one of these resolutions. -/
@[match_pattern] abbrev or (rs : List Resolution) : Resolution :=
  .chooseModes rs .one

/-- Proliferate `amount` times (CR 701.34), or give `who` another counter of each kind on it. -/
@[match_pattern] abbrev proliferate (amount : NumberSelector := .fixed 1) (who : ObjectSelector := .youControl) : Resolution :=
  .putCounters (.eachKindOnIt amount) who

/-- Remove counters. `what` says which, and `who` says from whom. -/
@[match_pattern] abbrev removeCounters (what : TriggerRemoveWhat) (who : ObjectSelector) : Resolution :=
  .putCounters (.remove what) who

/-- A player reveals cards from their hand (CR 701.16), as `count` says, then resolves `thenDo`. -/
@[match_pattern] abbrev revealFromHand (count : TriggerRevealCount) (thenDo : Resolution) : Resolution :=
  .revealLibrary (.fromHand count) thenDo .you

/-- A permanent loses `what`, as `who` says (CR 613.1f Layer 6). -/
@[match_pattern] abbrev lose (what : AbilitySelector) (who : ObjectSelector := .target) : Resolution :=
  .grant (.lose what) who

/-- `action` says what can't be done, and who can't do it (CR 613.1f / CR 508 / CR 509). -/
@[match_pattern] abbrev cant (action : ActionSelector) : Resolution :=
  .grant (.cant action) .target

/-- Until end of turn, `who` becomes an artifact in addition to its other types (CR 613.1d Layer 4). -/
@[match_pattern] abbrev becomeArtifact (who : ObjectSelector := .target) : Resolution :=
  .grant .artifact who

/-- `who` becomes prepared (or unprepared when `prepared = false`). -/
@[match_pattern] abbrev becomePrepared (who : ObjectSelector := .target) (prepared : Bool := true) : Resolution :=
  .grant (.prepared prepared) who

/-- Until end of turn, `who`'s base power and toughness become `power` and `toughness` (CR 613.4b Layer 7b). -/
@[match_pattern] abbrev setBasePT (power toughness : NumberSelector) (who : ObjectSelector := .target) : Resolution :=
  .grant (.basePT power toughness) who

/-- Gain control of the announced permanents, as `how` says (CR 613.1b Layer 2). -/
@[match_pattern] abbrev gainControl (how : TriggerControlHow) : Resolution :=
  .grant (.control how) .target

/-- The source becomes a copy of `of` (CR 613.1a Layer 1). -/
@[match_pattern] abbrev becomeCopy (of : ObjectSelector) : Resolution :=
  .grant (.copy of) .source

/-- If the targeted permanent would die this turn, exile it instead (CR 614.1). -/
@[match_pattern] abbrev replace : Resolution :=
  .grant .replace .target

/-- Spells of `which` cost less this turn, as `n` says (CR 601.2f). -/
@[match_pattern] abbrev spellsCostLess (which : SpellCostLess) (n : NumberSelector) : Resolution :=
  .grant (.spellsCostLess which n) .youIfCast

/-- Investigate (create a Clue; CR 701.36). -/
@[match_pattern] abbrev investigate (who : PlayerSelector := .you) : Resolution :=
  .grant .investigate (.player who)

/-- Empower Jace, as `n` says (Reality Fracture). -/
@[match_pattern] abbrev empowerJace (n : NumberSelector) : Resolution :=
  .grant (.empowerJace n) .youIfCast

/-- Recruit. “recruit” is `.recruit`. “you recruit” is `.recruit .you`. -/
@[match_pattern] abbrev recruit (who : PlayerSelector := .recruit) : Resolution :=
  .grant (.recruit who) .youIfCast

/-- Record another resolution of this ability this turn. -/
@[match_pattern] abbrev noteResolveThisTurn (limit : Nat) : Resolution :=
  .grant (.noteResolveThisTurn limit) .source

/-- Resolve the reflexive triggered ability `kind` of an MSH card. -/
@[match_pattern] abbrev mshReflexive (kind paid : Nat) : Resolution :=
  .grant (.mshReflexive kind paid) .source

/-- A step that used to be a `FraResolution` constructor. -/
def isFra : Resolution → Bool
  | .destroy .target .drawIfNotAttacking | .destroy .creaturesNotChosenType _ => true
  | .exile .allCreatures .forLater .empowerJace | .draw .greatestPowerAndLoseLife _ => true
  | .returnToHand .outsideGameOpponentChoice _ | .exile .sphinxsApproach .forLater _ => true
  | .putOnLibrary .topOrBottomDamage2 .target | .may (.sacrifice .planeswalker _) (.searchLibrary (.put .planeswalkerCard _ _)) .ifYouDo | .putCounters .plusOnePerThreeGraveyardIfFromGy .createdToken | .grant (.keywords _) .createdToken => true
  | .exile .target (.returnBrieflyIfMvAtMost _) _ | .discard (.mayWheel _ _) | .grant .mountainsAddExtraRed .landsYouControl => true
  | .may (.removeCounters (.upTo 1) .source) (.putCounters (.ofKind .plusOnePlusOne 1) .eachOther) .ifYouDo => true
  | .becomePrepared .enchanted false | .putOnLibrary .topOrBottom .target | .discard .drawTwoDiscardTwoStun | .becomeCopy .sourceIfNotToken => true
  | .put .source .asPrinted .none | .put .source _ (.entering [.counter .plusOnePlusOne _ _]) | .grant .flashback .target => true
  | .revealFromHand .hand (.exile .chosenNonland .untilSourceLeaves _) | .mayCast .uldarosGraveyardTypes .unlimited .withoutPaying _ => true
  | .surveil (.fixed 1) .eyeOfJace | .putCounters (.ofKind .stun _) (.creaturesControlledBy .eachOpponent) | .discard .lootThenCountersPerDiscard => true
  | .dealDamage (.fixed 1) (.player .eachOpponent) .addRedIfMountain | .putCounters .minusOneGreatestGraveyardMv (.creaturesControlledBy .eachOpponent) | .may (.removeCounters .all .source) (.putCounters .sourceCounters .target) .ifYouDo => true
  | .proliferate (.fixed _) .youControl | .grant .artifactCreatureVehicle .source | .loseLife (.fixed 1) .extort => true
  | .queueReflexive (.mshReflexive _ _) | .mshReflexive _ _ | .chooseModes _ (.hawkeyeIndices _) | .mayCast .boastExiled .unlimited .withoutPaying _ | .becomeCopy .sourceSpellXTimes => true
  | .mayCast .milledSpell .causingSpell .withoutPaying _ | .pump (.fixed 2) (.fixed 2) .attackersOfCauseControllerWithTrample | .grant .emrakulManaAndCast .target => true
  | .cant (.beCountered .nextSpellThisTurn) | .exile .target .forLater .revealUntilCreatureOrPlaneswalker | .destroy .target .drawIfLegendaryEnchantment | .grant (.choiceOfKeywords _) .source => true
  | .putOnLibrary .shuffled .target | .grant .combatDamageDrawTwo .source => true
  | .surveil (.fixed 1) .returnNoncreatureNonland | .putCounters .stunRemovedLoyalty .target | .grant .emblemDrawOnCast .youIfCast => true
  | .pump (.fixed (-5)) (.fixed 0) .attackersAgainstYouUntilYourTurn | .exile .opponentLibrariesButBottom .forLater _ | .pump (.fixed (-4)) (.fixed (-1)) (.target .untilYourNextTurn) => true
  | .sacrifice .eachPlayersCreature .ifYouDoCreateBeast | .discard .eachOpponentTwoDrawPerNonlandShortfall | .grant .emblemCreaturesGetTwoTwo .youIfCast => true
  | .pump (.fixed 2) (.fixed 2) .attackersAgainstOpponentsUntilYourTurn => true
  | .putCounters .plusOnePerDiscardAfterDraw .cause | .sacrifice .source .eyeOfJaceIfSevenInGy | .chooseModes _ (.fraTrigger _) => true
  | .putOnLibrary (.topAfterDraw _ _) .cardFromHand | .exile .target .forLater .despark => true
  | .exile .target .forLater .controllerMaySearchBasic | .exile .target .forLater .controllerGainsLifePower => true
  | .destroy .target .controllerCreatesHuman | .discard .drawAndDiscardXCreateSpiritPerType => true
  | .createTokens .citizen _ _ _ _ | .createTokens .warrior _ _ _ _ | .createTokens .insect _ _ _ _ => true
  | .createTokens .myr _ _ _ _ | .createTokens .kobold _ _ _ _ | .createTokens .mite _ _ _ _ => true
  | .createTokens .shark _ _ _ _ | .createTokens .gingerbrute _ _ _ _ | .createTokens .angel _ _ _ _ => true
  | .createTokens .human _ _ _ _ | .createTokens .goblin _ _ _ _ | .createTokens .map _ _ _ _ => true
  | .createTokens .rogue _ _ _ _ | .createTokens .incubator _ _ _ _ | .createTokens _ _ _ _ .destroyOthersIfXAtLeast5 => true
  | .exile .allCreatures .forLater .incubateCount | .exile .creaturesYouControl .forLater .revealCreaturesToBattlefield => true
  | .exile .creaturesYouControl .forLater .revealCreaturesAtEndStep | .searchLibrary (.put (.basicSubtypesUntapAt _ _) _ _) => true
  | .putOnLibrary .bottomRevealCreature .target | .grant (.animateLand _ _ _ _) .source | .sacrifice .archonCruelty _ => true
  | .put (.cause none) .atNextEndStep _ | .revealLibrary .untilCreaturesPerOpponent _ _ | .revealLibrary .untilHistoric _ _ => true
  | .revealLibrary .firstResolveUntilCreature _ _ | .may (.loseLife .lastKnownPower _) (.draw .lastKnownPower _) .ifYouDo => true
  | .loseLife (.fixed 1) .eachOpponentAndYouGain1 | .destroy .oppTappedCreatures .gainLifeEach | .destroy .creaturesPowerAtLeast4 _ => true
  | .grant .emblemCreaturesGetTwoTwoFlying .youIfCast | .putOnLibrary .bottomAfterDrawTwo .cardFromHand => true
  | .exile (.target .another) .forLater .revealUntilCreatureOrPlaneswalker | .cant (.attackJaces _) | .grant .monarch .youIfCast => true
  | .putCounters (.ofKind .stun _) .combatDamagerIfMonarch | .grant .teferisReproach (.player (.target .opponent)) => true
  | .mill .lastKnownPower .eachPlayer .freeCastFromGraveyard | .becomeCopy .targetSpellTwice | .becomeCopy .targetPermanentTwoTokensHasteSacrifice => true
  | .putCounters (.ofKind .story _) .source | .exile (.cause none) .untilSourceLeaves _ | .discard .drawOneDiscardOne => true
  | .becomeCopy .anyCreatureOnBattlefieldWithHaste | .loseLife .lifeLostThisTurn .eachOpponent | .amass (.fixed 1) "Zombie" false .youLose1Life => true
  | .revealLibrary (.top 5) (.returnToHand .factOrFiction _) _ | .grant .explored .source | .grant .transformedIncubator .source => true
  | .grant .faceUp .source | .cant (.beBlockedExceptByHaste .source) => true
  | .searchLibrary (.putOnLibrary .top .planeswalkerCard) | .searchLibrary (.mill (.fixed 1) _ _) => true
  | .searchLibrary (.returnToHand .basicLandsDifferentNamesX _) | .searchLibrary (.put (.landsUpTo _) .tapped _) => true
  | .searchLibrary (.returnToHand .enchantmentCard _) | .searchLibrary (.returnToHand .card _) => true
  | .addMana #[.colored .blue] (.fixed 1) .noncreatureSpell => true
  | .returnToHand .target .none | .returnToHand (.target .eachPermanent) .none => true
  | .returnToHand (.target .graveyardCard) .none | .returnToHand .source _ => true
  | .exile .target .forLater .none | .exile .target .returnImmediately .none | .exile .target .untilSourceLeaves .none => true
  | .exile .graveyardCard .forLater .none | .exile (.target .graveyardCard) .forLater .none => true
  | .dealDamage (.fixed _) (.targetAt _) .none | .dealDamage (.power (.targetAt 1)) (.targetAt 0) .none => true
  | .dealDamage .equalSourcePower .target .none | .dealDamage (.power .source) .target .none => true
  | .dealDamage .chosenX .target .none => true
  | .dealDamage (.fixed _) (.player .eachPlayer) _ | .dealDamage (.fixed _) .oppCreaturesAndPlaneswalkers _ => true
  | .dealDamage (.fixed _) .creaturesExceptYourTokens _ | .dealDamage (.fixed _) (.player (.controller .cause)) _ => true
  | .dealDamage (.fixed _) (.player .eachOpponent) .fromCause => true
  | .putCounters (.ofKind .plusOnePlusOne _) (.targetAt _) => true
  | .putCounters (.ofKind .plusOnePlusOne _) (.creaturesControlledBy (.targetAt _)) => true
  | .putCounters (.ofKind .loyalty _) .planeswalkersYouControl => true
  | .putCounters (.ofKind .plusOnePlusOne _) (.target .eachPermanent) | .putCounters .plusOnePerLand .target => true
  | .putCounters .plusOneEqualToHand .creaturesYouControl | .putCounters .causeCounters .source => true
  | .putCounters (.ofKind .plusOnePlusOne _) .creaturesWithPlusOne | .putCounters (.ofKind .plusOnePlusOne _) .wizardTokensExceptRecent => true
  | .put .graveyardCard .asPrinted _ | .put .allNonlandPermanentsInGraveyard .asPrinted .none => true
  | .put .cause .tapped .none | .put .landCard .tapped .none => true
  | .discard .chosenNonland | .discard .chosenNonlandPermanent | .discard .hand | .discard .random => true
  | .lose .allAbilities (.targetAt _) => true
  | .destroy (.targetAt _) .none | .destroy .allCreatures .none | .destroy (.target .eachPermanent) .none => true
  | .removeCounters (.upTo _) .target => true
  | .putOnLibrary .bottom .graveyardCard => true
  | .may (.searchLibrary (.put .basicLand .tapped _)) (.sequence []) _ => true
  | .may (.searchLibrary (.put .landsEqualDamage .tapped _)) (.sequence []) _ => true
  | .may (.sacrifice .land) (.createTokens .heartwood (.fixed 2) true _ _) .ifYouDo => true
  | .may (.sacrifice .creatureOrPlaneswalker) (.sacrifice .eachOpponentsCreature _) .ifYouDo => true
  | .may (.sacrifice .another) (.createTokens .beast44trample (.fixed 1) false _ _) .ifYouDo => true
  | .may (.discard (.cards 1 .you)) (.searchLibrary (.returnToHand .enchantmentCard _)) .ifYouDo => true
  | .may (.discard (.cards 1 .you)) (.queueReflexive (.dealDamage (.fixed _) .target _)) .ifYouDo => true
  | .may (.pay (.mana #[.generic _])) (.queueReflexive (.destroy (.target .eachPermanent) _)) .ifYouDo => true
  | .may (.pay (.mana #[.generic _])) (.proliferate _ _) .ifYouDo => true
  | .queueReflexive (.dealDamage (.fixed _) .target _) => true
  | .queueReflexive (.destroy (.target .eachPermanent) _) => true
  | .queueReflexive (.put .landCard .tapped .none) => true
  | .sacrifice .source _ | .grant (.keywords _) (.cause none) => true
  | .pump (.fixed _) (.fixed _) (.cause none) => true
  | .pump (.count .artifact) (.fixed 0) .creaturesYouControl | .pump (.count .artifact) (.fixed 0) .source => true
  | .pump (.count .artifact) (.fixed 0) .target | .pump .causePower (.fixed 0) .source => true
  | .pump .minusGraveyardCards (.fixed 0) .target => true
  | .empowerJace (.count .creaturesYouControl) | .empowerJace (.subtypeCount "Island") => true
  | .draw (.perControlled .creature) _ | .draw .milledByTargetPlayerThisTurn _ | .draw .colorsAmongOtherArtifacts _ => true
  | .untap (.target .eachPermanent) | .untap .landsYouControl | .untap .tokensYouControl => true
  | .fight .source .mutual | .becomeCopy .causingSpell => true
  | _ => false

/-- Oracle wording for a former `FraResolution` step. `none` for every other step. -/
def fraPhrase? (r : Resolution) (noun : String) : Option String :=
  match r with
  | .returnToHand .target .none => some (s!"Return {noun} to its owner's hand")
  | .exile .target .forLater .none => some (s!"Exile {noun}")
  | .destroy .target .drawIfNotAttacking => some (s!"Destroy {noun}. If it wasn't attacking, its controller draws a card")
  | .dealDamage (.fixed n) (.player .eachPlayer) _ => some (s!"This deals {n} damage to each player")
  | .dealDamage (.fixed n) (.targetAt _) .none => some (s!"This deals {n} damage to {noun}")
  | .putCounters (.ofKind .plusOnePlusOne n) (.targetAt _) => some (s!"Put {plusOnePlusOneCountersPhrase n} on {noun}")
  | .returnToHand (.target .graveyardCard) .none => some (s!"Return {noun} to your hand")
  | .put .graveyardCard .asPrinted .none => some (s!"Return {noun} to the battlefield")
  | .put .graveyardCard .asPrinted (.entering [.counter .plusOnePlusOne _ true]) =>
    some (s!"Return {noun} to the battlefield with an additional +1/+1 counter on it")
  | .destroy .creaturesNotChosenType _ => some ("Choose a creature type. Destroy all creatures that aren't of the chosen type")
  | .searchLibrary (.putOnLibrary .top .planeswalkerCard) => some ("Search your library for a planeswalker card, reveal it, then shuffle and put that card on top")
  | .putCounters (.ofKind .plusOnePlusOne n) (.target .eachPermanent) => some (s!"Put {plusOnePlusOneCountersPhrase n} on each of {noun}")
  | .put .allNonlandPermanentsInGraveyard .asPrinted .none => some ("Return all nonland permanent cards from your graveyard to the battlefield")
  | .draw .milledByTargetPlayerThisTurn _ => some ("Draw X cards, where X is the number of cards that were put into target player's graveyard from their library this turn")
  | .exile .allCreatures .forLater .empowerJace => some ("Exile all creatures. Empower Jace X, where X is the number of creatures exiled this way")
  | .draw .greatestPowerAndLoseLife _ => some ("Draw cards equal to the greatest power among creatures you control. You lose life equal to the number of cards drawn this way")
  | .discard .chosenNonlandPermanent =>
    some (s!"{capitalizeAscii noun} reveals their hand. You choose a nonland permanent card from it. That player discards that card")
  | .discard .chosenNonland =>
    some (s!"{capitalizeAscii noun} reveals their hand. You choose a nonland card from it. That player discards that card")
  | .discard .hand => some ("Discard your hand")
  | .draw (.perControlled .creature) _ => some ("Draw a card for each creature you control")
  | .returnToHand .outsideGameOpponentChoice _ => some ("You may reveal exactly two cards you own with different names from outside the game. An opponent chooses one of them. You put that card into your hand")
  | .exile .sphinxsApproach .forLater _ => some ("You may exile this spell and four cards named Sphinx's Approach from your graveyard. If you do, search your library for a Sphinx creature card, put it onto the battlefield, then shuffle")
  | .putCounters (.ofKind .plusOnePlusOne _) .wizardTokensExceptRecent => some ("Put a +1/+1 counter on each other Wizard token you control")
  | .dealDamage (.fixed n) .oppCreaturesAndPlaneswalkers _ => some (s!"This deals {n} damage to each creature and planeswalker your opponents control")
  | .lose .allAbilities (.targetAt _) => some (s!"{capitalizeAscii noun} loses all abilities until end of turn")
  | .dealDamage (.power (.targetAt 1)) (.targetAt 0) .none => some ("Target creature you control deals damage equal to its power to that permanent")
  | .putOnLibrary .topOrBottomDamage2 .target => some ("Choose target nonland permanent. Its owner may put it on top of their library. If they do, this deals 2 damage to them. If they didn't put the card on top of their library, they put it on the bottom")
  | .may (.sacrifice .planeswalker _) (.searchLibrary (.put .planeswalkerCard _ _)) .ifYouDo => some ("You may sacrifice a planeswalker. If you do, search your library for a planeswalker card, put it onto the battlefield, then shuffle")
  | .putCounters .plusOnePerThreeGraveyardIfFromGy .createdToken => some ("If this spell was cast from a graveyard, put a +1/+1 counter on each of them for every three cards in your graveyard")
  | .grant (.keywords _) .createdToken => some ("It gains haste until end of turn")
  | .ifElse .notFromHand (.draw (.fixed 2) _) (.draw (.fixed 1) _) => some ("Draw a card. If this spell wasn't cast from your hand, draw two cards instead")
  | .destroy (.targetAt _) .none => some (s!"Destroy {noun}")
  | .putCounters (.ofKind .plusOnePlusOne 1) (.creaturesControlledBy (.targetAt _)) => some ("Put a +1/+1 counter on each creature target player controls")
  | .exile .target (.returnBrieflyIfMvAtMost n) _ => some (s!"Exile {noun}. If that permanent's mana value was {n} or less, return it to the battlefield tapped under your control. Exile it at the beginning of the next end step")
  | .discard (.mayWheel n _) => some (s!"Each player may discard their hand and draw {englishNumber n} cards")
  | .grant .mountainsAddExtraRed .landsYouControl => some ("Until end of turn, whenever you tap a Mountain for mana, add an additional {R}")
  | .searchLibrary (.mill (.fixed 1) _ _) => some ("Search your library for a land card, put it into your graveyard, then shuffle")
  | .counter => some (s!"Counter {noun}")
  | .unlessPays .counter n => some (s!"Counter {noun} unless its controller pays \{{n}}")
  | .destroy .target .none => some (s!"Destroy {noun}")
  | .sequence [.replace, .dealDamage (.fixed n) .target .none] => some (s!"This deals {n} damage to {noun}. If that permanent would die this turn, exile it instead")
  | .mill (.fixed n) .you (.permanentAndGainLife l) => some (s!"Mill {englishNumber n.toNat} cards. You may put a permanent card from among them into your hand. You gain {l} life")
  | .chooseModes _ (.fraTrigger n) => some (if n == 2 then "choose two" else "choose one")
  | .pump .minusGraveyardCards (.fixed 0) .target => some (s!"{capitalizeAscii noun} gets -X/-0 until end of turn, where X is the number of cards in your graveyard")
  | r => if r.isFra then some "" else none

end Resolution

/-- What a spell, activated ability, or trigger does to a permanent (CR 608.2b).
Defined as a type alias for `Resolution` (targeting `.target` by default). -/
def PermanentAction : Type := Resolution
deriving Repr, Inhabited, BEq

namespace PermanentAction

/-- Until-end-of-turn +P/+T. -/
def pump (power toughness : Int) : PermanentAction :=
  Resolution.pump (.fixed power) (.fixed toughness) .target

/-- Until-end-of-turn +P/+T and trample. -/
def pumpAndTrample (power toughness : Int) : PermanentAction :=
  Resolution.sequence [.pump (.fixed power) (.fixed toughness) .target, .grant (.keywords Keyword.trample) .target]

/-- Destroy the permanent (CR 701.7). -/
def destroy : PermanentAction :=
  Resolution.destroy .target

/-- Put `n` +1/+1 counters on the permanent (CR 122.1). -/
def plusOne (n : Nat) : PermanentAction :=
  Resolution.putCounters (.ofKind .plusOnePlusOne n) .permanent

/-- Deal `amount` damage. -/
def dealDamage (amount : Nat) : PermanentAction :=
  Resolution.dealDamage (.fixed amount) .target

/-- The permanent loses indestructible until end of turn. -/
def loseIndestructible : PermanentAction :=
  Resolution.lose .indestructible .target

/-- The permanent can't be blocked this turn. -/
def cantBeBlocked : PermanentAction :=
  Resolution.cant (.beBlocked .target)

/-- Grant these keywords until end of turn. -/
def grantKeywords (k : Keywords) : PermanentAction :=
  Resolution.grant (.keywords k) .target

/-- Put an indestructible counter on the permanent. -/
def indestructibleCounter : PermanentAction :=
  Resolution.putCounters (.ofKind .indestructible) .permanent

/-- Put a double strike counter on the permanent. -/
def doubleStrikeCounter : PermanentAction :=
  Resolution.putCounters (.ofKind .doubleStrike) .permanent

/-- Put a burden counter on the permanent. -/
def burdenCounter : PermanentAction :=
  Resolution.putCounters (.ofKind .burden) .permanent

/-- Tap the permanent. -/
def tap : PermanentAction :=
  Resolution.tap .target

/-- Untap the permanent. -/
def untap : PermanentAction :=
  Resolution.untap .target

/-- Until end of turn, this becomes an artifact in addition to its other
types and gains indestructible. -/
def becomeArtifactIndestructible : PermanentAction :=
  Resolution.sequence [.becomeArtifact .target, .grant (.keywords Keyword.indestructible) .target]

/-- The permanent becomes prepared (Reality Fracture). -/
def becomePrepared : PermanentAction :=
  Resolution.becomePrepared .target

/-- Until-end-of-turn layer-7b base power and toughness (CR 613.4b). -/
def setBasePT (power toughness : Int) : PermanentAction :=
  Resolution.setBasePT (.fixed power) (.fixed toughness) .target

/-- Tap the permanent and put a stun counter on it (CR 122.1d). -/
def tapAndStun : PermanentAction :=
  Resolution.sequence [.tap .target, .putCounters (.ofKind .stun) .permanent]

/-- The owner puts this permanent on top of their library. -/
def putOnTopOfLibrary : PermanentAction :=
  Resolution.putOnLibrary .top .target

/-- The owner puts this permanent on the bottom of their library. -/
def putOnBottomOfLibrary : PermanentAction :=
  Resolution.putOnLibrary .bottom .target

/-- Exile the permanent. -/
def exile : PermanentAction :=
  Resolution.exile .target .forLater

/-- Until end of turn, add this permanent's power and toughness to itself,
which doubles them. -/
def doublePowerAndToughness : PermanentAction :=
  Resolution.pump .double .double .target

/-- Oracle-style text for this action on `noun` (e.g. `target creature`).
`sentence` capitalizes the first letter for activated-ability lines. -/
def toNotation (action : PermanentAction) (noun : String) (sentence := false) : String :=
  let damage (n : Nat) : String := s!"deals {n} damage to {noun}"
  let r : Resolution := action
  let raw :=
    match r with
    | .pump (.fixed p) (.fixed t) _ =>
      s!"{noun} gets {signedStat p}/{signedStat t} until end of turn"
    | .sequence [.pump (.fixed p) (.fixed t) _, .grant (.keywords k) _] =>
      if k == Keyword.trample then
        s!"{noun} gets {signedStat p}/{signedStat t} and gains trample until end of turn"
      else ""
    | .destroy _ .none => s!"destroy {noun}"
    | .putCounters (.ofKind .plusOnePlusOne n) _ => s!"put {plusOnePlusOneCountersPhrase n} on {noun}"
    | .dealDamage (.fixed n) _ .none => damage n.toNat
    | .lose .indestructible _ =>
      s!"{noun} loses indestructible until end of turn"
    | .cant (.beBlocked _) => s!"{noun} can't be blocked this turn"
    | .grant (.keywords k) _ =>
      s!"{noun} gains {k.joinedAnd} until end of turn"
    | .putCounters (.ofKind .indestructible 1) _ =>
      s!"put an indestructible counter on {noun}"
    | .putCounters (.ofKind .doubleStrike 1) _ =>
      s!"put a double strike counter on {noun}"
    | .putCounters (.ofKind .burden 1) _ =>
      s!"put a burden counter on {noun}"
    | .tap _ true => s!"tap {noun}"
    | .untap _ => s!"untap {noun}"
    | .sequence [.becomeArtifact _, .grant (.keywords k) _] =>
      if k == Keyword.indestructible then
        s!"until end of turn, {noun} becomes an artifact in addition to its other types and gains indestructible"
      else ""
    | .becomePrepared _ true => s!"{noun} becomes prepared"
    | .setBasePT (.fixed p) (.fixed t) _ =>
      s!"{noun} has base power and toughness {p}/{t} until end of turn"
    | .sequence [.tap _ true, .putCounters (.ofKind .stun 1) _] =>
      s!"tap {noun} and put a stun counter on it"
    | .putOnLibrary .top _ =>
      s!"{noun}'s owner puts it on top of their library"
    | .putOnLibrary .bottom _ =>
      s!"{noun}'s owner puts it on the bottom of their library"
    | .exile _ .forLater .none => s!"exile {noun}"
    | .pump .double .double _ =>
      s!"double {noun}'s power and toughness until end of turn"
    | _ => ""
  if sentence then capitalizeAscii raw else raw

end PermanentAction

namespace Resolution

/-- What `action` does to `who`. `target` is the announced permanent. -/
def ofAffected (who : ObjectSelector) (action : PermanentAction) : Resolution :=
  let r : Resolution := action
  match r with
  | .putCounters what _ => .putCounters what (counterWho who)
  | .pump p t _ => .pump p t who
  | .sequence [.pump p t _, .grant what _] =>
    .sequence [.pump p t who, .grant what who]
  | .destroy _ note => .destroy who note
  | .dealDamage n _ note => .dealDamage n who note
  | .lose what _ => .lose what who
  | .cant (.beBlocked _) => .cant (.beBlocked who)
  | .sequence [.becomeArtifact _, .grant what _] =>
    .sequence [.becomeArtifact who, .grant what who]
  | .becomePrepared _ prep => .becomePrepared who prep
  | .setBasePT p t _ => .setBasePT p t who
  | .grant what _ => .grant what who
  | .tap _ true => .tap (tapWho who) true
  | .untap _ => .untap who
  | .sequence [.tap _ true, .putCounters what _] =>
    .sequence [.tap (tapWho who), .putCounters what (counterWho who)]
  | .putOnLibrary place _ => .putOnLibrary place who
  | .exile _ how note => .exile who how note
  | r => r
where
  counterWho : ObjectSelector → ObjectSelector
    | .any | .target .any => .permanent
    | w => w
  tapWho : ObjectSelector → ObjectSelector
    | .enchanted => .enchantedWhileSource
    | w => w

/-- Affect a still-legal permanent (by default `.target`, or `.source` if the
source is still on the battlefield). -/
def onPermanent (action : PermanentAction) (who : ObjectSelector := .target) : Resolution :=
  ofAffected who action

/-- Affect the source if it is still on the battlefield. -/
def onSource (action : PermanentAction) : Resolution :=
  ofAffected .source action

/-- What `action` does to the announced permanent. -/
def ofPermanent : PermanentAction → Resolution :=
  ofAffected .target

/-- What `action` does to the source if it is still on the battlefield. -/
def ofSource : PermanentAction → Resolution :=
  ofAffected .source

/-- What `action` does to the creature this Aura enchants. -/
def ofEnchanted : PermanentAction → Resolution :=
  ofAffected .enchanted

/-- What `action` does to the target while the source is still on the battlefield.
A source that already left is silent. -/
def ofTargetWhileSource : PermanentAction → Resolution :=
  ofAffected (.target .whileSource)

/-- The `PermanentAction` that `ofAffected who` built for `r`, if any. -/
def affectedAction? (who : ObjectSelector) (r : Resolution) : Option PermanentAction :=
  let cWho := match who with | .any | .target .any => .permanent | w => w
  let tWho := match who with | .enchanted => .enchantedWhileSource | w => w
  match r with
  | .putCounters (.ofKind .plusOnePlusOne n) w => if w == cWho then some (.plusOne n) else none
  | .pump (.fixed p) (.fixed t) w => if w == who then some (.pump p t) else none
  | .sequence [.pump (.fixed p) (.fixed t) w1, .grant (.keywords k) w2] =>
    if w1 == who && w2 == who && k == Keyword.trample then some (.pumpAndTrample p t) else none
  | .destroy w .none => if w == who then some .destroy else none
  | .dealDamage (.fixed n) w .none => if w == who then some (.dealDamage n.toNat) else none
  | .grant (.keywords k) w => if w == who then some (.grantKeywords k) else none
  | .tap w true => if w == tWho then some .tap else none
  | .untap w => if w == who then some .untap else none
  | .lose .indestructible w => if w == who then some .loseIndestructible else none
  | .cant (.beBlocked w) => if w == who then some .cantBeBlocked else none
  | .putCounters (.ofKind .indestructible 1) w => if w == cWho then some .indestructibleCounter else none
  | .putCounters (.ofKind .doubleStrike 1) w => if w == cWho then some .doubleStrikeCounter else none
  | .putCounters (.ofKind .burden 1) w => if w == cWho then some .burdenCounter else none
  | .sequence [.becomeArtifact w1, .grant (.keywords k) w2] =>
    if w1 == who && w2 == who && k == Keyword.indestructible then some .becomeArtifactIndestructible else none
  | .becomePrepared w true => if w == who then some .becomePrepared else none
  | .setBasePT (.fixed p) (.fixed t) w => if w == who then some (.setBasePT p t) else none
  | .sequence [.tap w1 true, .putCounters (.ofKind .stun 1) w2] =>
    if w1 == tWho && w2 == cWho then some .tapAndStun else none
  | .putOnLibrary .top w => if w == who then some .putOnTopOfLibrary else none
  | .putOnLibrary .bottom w => if w == who then some .putOnBottomOfLibrary else none
  | .exile w .forLater .none => if w == who then some .exile else none
  | .pump .double .double w => if w == who then some .doublePowerAndToughness else none
  | _ => none

/-- The `PermanentAction` that `onPermanent` built for `r`, if any. -/
def onPermanent? : Resolution → Option PermanentAction :=
  affectedAction? .target

/-- The `PermanentAction` that `onSource` built for `r`, if any. -/
def onSource? : Resolution → Option PermanentAction :=
  affectedAction? .source

end Resolution

namespace TriggeredAbility

abbrev TriggerResolution := Resolution

namespace TriggerResolution

export Resolution (
  ofAffected
  ofPermanent
  ofSource
  ofEnchanted
  ofTargetWhileSource
  onPermanent
  onSource
  lose
  cant
  becomeArtifact
  becomePrepared
  setBasePT
  removeCounters
  untap
  recruit
  gainControl
  noteResolveThisTurn
  ifElse
  or
  spellsCostLess
  revealFromHand
  surveil
  empowerJace
  loseLife
  becomeCopy
  replace
  investigate
  proliferate
  mshReflexive
)

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

/-- A spell step as the same step in this vocabulary. -/
def ofSpell (r : TriggerResolution) : TriggerResolution := r

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
  gainControl
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
  ringTempts
  spellsCostLess
  investigate
  proliferate
  mshReflexive
  connive
  fight
  revealFromHand
  surveil
  empowerJace
  additionalCombatPhase
  loseLife
  winTheGame
  becomeCopy
  onPermanent
  onSource
  counter
  unlessPays
  replace
  unrecognized
)


/-- The “if …” clause for `cond`, without a following resolution. -/
private def ifClause (cond : TriggeredAbility.ConditionSelector) (noun : String) : String :=
  match cond with
  | .subtype subtype => s!"if {noun} is {indefinite subtype} {subtype}"
  | .mvAtMost n => s!"if that spell's mana value was {n} or less"
  | .castFromGraveyard => "if this spell was cast from a graveyard"
  | .notFromHand => "if this spell wasn't cast from your hand"
  | .teamwork => "if this spell was cast using teamwork"
  | .giftPromised => "if the gift was promised"
  | _ => "if that is true"

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
  | .fight .announced .mutual =>
    "target creature you control fights target creature an opponent controls"
  | .fight .announced .upToOneOther =>
    "target creature you control fights up to one other target creature"
  | .grant .extraLand .youIfCast => "you may play an additional land this turn"
  | .unrecognized => "this effect does nothing"
  | .sequence _ => ""
  | .discard (.cards n) => s!"discard {cardPhrase n}"
  | .loseLife (.fixed n) .you => s!"lose {n} life"
  | .loseLife (.fixed n) .player => s!"{noun} loses {n} life"
  | .loseLife (.fixed n) (.controller .target) => s!"its controller loses {n} life"
  | .loseLife (.fixed n) .eachOpponent => s!"each opponent loses {n} life"
  | .gainLife (.fixed n) .you => s!"you gain {n} life"
  | .gainLife (.fixed n) .player => s!"Target player gains {n} life"
  | .surveil (.fixed n) .none => s!"surveil {n}"
  | .grant (.keywords k) .creaturesYouControl => s!"creatures you control gain {k.joinedAnd} until end of turn"
  | .returnToHand .targetSpell _ => s!"return {noun} to its owner's hand"
  | .returnToHand (.target .graveyardCard) _ => s!"return up to one {noun} to your hand"
  | .pump (.fixed p) (.fixed t) .creaturesYouControl =>
    s!"creatures you control get {signedStat p}/{signedStat t} until end of turn"
  | .pump (.fixed p) (.fixed t) .allCreatures =>
    s!"all creatures get {signedStat p}/{signedStat t} until end of turn"
  | .pump (.fixed p) (.fixed t) .creaturesOfTargetPlayer =>
    s!"creatures {noun} controls get {signedStat p}/{signedStat t} until end of turn"
  | .exile (.graveyardCardsOfType ty (.target .player)) .anyManaWhileExiled _ =>
    s!"exile all {ty.oracleWord} cards from target player's graveyard. You may cast spells from among those cards for as long as they remain exiled, and mana of any type can be spent to cast them"
  | .draw (.fixed n) .you => s!"draw {cardPhrase n.toNat}"
  | .draw (.fixed n) .player => s!"{noun} draws {cardPhrase n.toNat}"
  | .scry (.fixed n) => s!"scry {n}"
  | .tap (.target .eachPermanent) => "tap one or two target creatures"
  | .counter => s!"counter {noun}"
  | .unlessPays r n =>
    let base := phraseOne r noun
    let base := if base.endsWith "." then (base.dropEnd 1).toString else base
    if base.isEmpty then s!"unless its controller pays \{{n}}"
    else s!"{base} unless its controller pays \{{n}}"
  | .exile .targetSpell .forLater .counteredPermanentMayCast =>
    s!"counter {noun}. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled"
  | .or _ => ""
  | .attach .equipmentYouControl .target =>
    "attach an Equipment you control to it"
  | .may (.draw (.perControlled ty) _) (.draw (.fixed 1) .eachOpponent) .ifYouDo =>
    s!"You may draw a card for each {ty.oracleWord} you control. If you do, each opponent draws a card"
  | .may (.put (.creatureFromHand subtype n) _ _) (.draw (.fixed 1) _) .ifYouDont =>
    s!"You may put {indefinite subtype} {subtype} creature card with mana value {n} or less from your hand onto the battlefield. If you don't, draw a card"
  | .may (.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .card])) (.draw (.fixed cards) _) .ifYouDo =>
    s!"You may sacrifice an artifact or discard a card. If you do, draw {cardPhrase cards.toNat}."
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
  | .ifElse .teamwork (.dealDamage (.fixed teamworkN) .target .none) (.dealDamage (.fixed n) .target .none) =>
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
  | .gainControl .exchangeTargets =>
    "exchange control of two target nonland permanents that share a card type"
  | .putCounters (.ofKind kind n) .creatureTargets =>
    s!"put {kind.countersPhrase n} on up to one target creature"
  | .putCounters (.ofKind kind n) .firstTargetCreatureYouControl =>
    s!"put {kind.countersPhrase n} on target creature you control"
  | .amass (.fixed n) subtype =>
    s!"amass {pluralizeName subtype} {n}"
  | .searchLibrary (.returnToHand (.supertypeCard s ty) _) =>
    searchLibraryToHandPhrase s!"a {s.oracleWord} {ty.oracleWord} card"
  | .searchLibrary (.put (.supertypeCard s ty) .tapped _) =>
    s!"its controller may search their library for a {s.oracleWord} {ty.oracleWord} card, put it onto the battlefield tapped, then shuffle"
  | .searchLibrary (.put .artifactCreatureX _ _) =>
    "Search your library and/or graveyard for an artifact creature card with mana value X or less and put it onto the battlefield with X additional +1/+1 counters on it. If X is 4 or greater, it gains haste until end of turn. If you search your library this way, shuffle."
  | .dealDamage .otherSpellsManaValue .opponentsCreatures _ =>
    "deals damage to each creature your opponents control equal to the total mana value of other spells you've cast this turn"
  | .dealDamage (.fixed n) .allCreatures _ =>
    s!"deals {n} damage to each creature"
  | .dealDamage (.fixed n) .opponentsCreatures _ =>
    s!"deals {n} damage to each creature your opponents control"
  | .dealDamage (.fixed n) (.nonSubtypeCreatures subtype) _ =>
    s!"deals {n} damage to each non-{subtype} creature"
  | .dealDamage .otherSpellsManaValue .allCreatures _ =>
    "deals damage to each creature equal to the total mana value of other spells you've cast this turn"
  | .dealDamage .otherSpellsManaValue (.nonSubtypeCreatures subtype) _ =>
    s!"deals damage to each non-{subtype} creature equal to the total mana value of other spells you've cast this turn"
  | .replace =>
    s!"if {noun} would die this turn, exile it instead"
  | .addMana #[.colored .red] (.count (.oppPermanents ty)) _ =>
    s!"add {"{R}"} for each {ty.oracleWord} your opponents control"
  | .returnToHand .creaturesNotChosenType _ =>
    "choose a creature type. Return all creatures that aren't of the chosen type to their owners' hands"
  | .draw .greatestToughnessThenPutCreatures _ =>
    "draw cards equal to the greatest toughness among creatures you control, then put any number of creature cards from your hand onto the battlefield"
  | .mill (.fixed n) _ (.toHand (.oneOf a b)) =>
    s!"mill {n} cards, then put {indefinite a.oracleWord} {a.oracleWord} or {b.oracleWord} card from among them into your hand"
  | .mill (.fixed n) _ (.toHand (.upTo max ty)) =>
    s!"mill {n} cards, then put up to {englishNumber max} {ty.oracleWord} cards from among them into your hand"
  | .mill (.fixed n) _ (.toHand (.allOf a b)) =>
    s!"mill {n} cards, then put all {a.oracleWord} and {b.oracleWord} cards from among them into your hand"
  | .exile .eachPermanent .returnImmediately _ =>
    "exile two target creatures and/or lands you control, then return them to the battlefield under their owner's control"
  | .addMana #[] (.fixed n) (.subtypeSpells subtype) =>
    s!"add {englishNumber n.toNat} mana in any combination of colors. Spend this mana only to cast {subtype} spells"
  | .exile .attackingCreatures .forLater .controllerMaySearchBasic =>
    s!"exile all attacking creatures {noun} controls. That player may search their library for that many basic land cards, put those cards onto the battlefield tapped, then shuffle"
  | .exile (.topN n) (.playIfYouControlSubtype subtype) _ =>
    s!"look at the top {n} cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a {subtype}"
  | .cant (.castSpellsThisTurn .any) =>
    "players can't cast spells this turn"
  | .exile .opponentTopX .playForLifeThisTurn _ =>
    "exile the top X cards of target opponent's library. You may play those cards this turn. If you cast a spell this way, pay life equal to its mana value rather than pay its mana cost"
  | .revealLibrary (.top n) (.returnToHand .twoPiles _) _ =>
    s!"look at the top {englishNumber n} cards of your library and separate them into a face-down pile and a face-up pile. An opponent chooses one of the piles. Put that pile into your hand and the other into your graveyard"
  | .put .creaturesDiedThisTurn .tapped .asFood =>
    "put onto the battlefield under your control all creature cards in your opponents' graveyards that were put there from the battlefield this turn. They are Food artifacts with \"{2}, {T}, Sacrifice this artifact: You gain 3 life.\""
  | .returnToHand .ownedCreaturesKicker .delayedBirds =>
    "choose target creature you own. If this spell was kicked, instead choose any number of target creatures you own. Return each chosen creature to your hand. At the beginning of the next upkeep, create a 4/4 white Bird Soldier creature token with flying for each creature returned to your hand this way"
  | .revealLibrary (.top n) (.sequence [.put .landsYouControl .tapped _, .gainLife (.fixed life) _]) _ =>
    s!"look at the top {n} cards of your library, put any number of land cards from among them onto the battlefield tapped, then shuffle. You gain {life} life"
  | .gainControl .oppArtifacts =>
    "for each opponent, gain control of up to one target artifact that player controls"
  | .grant .phaseOutKicker .target =>
    "target creature phases out. If this spell was kicked, each creature target player controls phases out instead"
  | .dealDamage (.fixed n) (.player (.controller .target)) _ =>
    s!"it also deals {n} damage to that creature's controller"
  | .exile (.creatureMvAtMostOrTeamwork n) .forLater (.gainLifeIfTeamwork life) =>
    s!"exile target creature with mana value {n} or less. If this spell was cast using teamwork, instead exile target creature and you gain {life} life"
  | .put (.creatureMvAtMostOrTeamwork n) .asPrinted _ =>
    s!"choose target creature card in your graveyard with mana value {n} or less. If this spell was cast using teamwork, instead choose target creature card in your graveyard. Return the chosen card to the battlefield"
  | .revealLibrary (.top n) (.put .creaturesYouControl _ _) _ =>
    s!"reveal the top {n} cards of your library. You may put a creature card from among them onto the battlefield. If this spell was cast using teamwork, put any number of creature cards from among them onto the battlefield instead. Put the rest into your graveyard"
  | .createTokens kind .chosenX _ _ _ =>
    s!"create X {kind.pluralNoun}"
  | .createTokens kind (.perSubtype subtype) _ _ _ =>
    s!"Create a {kind.oracleNoun} for each {subtype} you control"
  | .createTokens .galactus (.fixed 1) false .you .none =>
    "Create Galactus, a legendary 16/16 black Elder Alien creature token with flying, trample, and \"Whenever Galactus attacks, destroy target land.\""
  | .createTokens kind (.fixed n) _ .you _ =>
    TokenKind.createPhrase kind n.toNat
  | .createTokens kind (.fixed n) _ .player _ =>
    s!"{noun} creates {TokenKind.createdTokensPhrase kind n.toNat}"
  | .returnToHand .eachPermanent _ =>
    "return one or two target nonland permanents to their owners' hands"
  | .investigate (.target .player) =>
    "target player investigates"
  | .grant (.keywords k) .creatureTargets =>
    PermanentAction.toNotation (.grantKeywords k) "target creature"
  | .untap .creatureTargets =>
    PermanentAction.toNotation .untap "target creature"
  | .pump (.fixed p) (.fixed t) .creatureTargets =>
    PermanentAction.toNotation (.pump p t) "target creature"
  | .returnToHand (.graveyardSubtype subtype) _ =>
    s!"return target {subtype} card from your graveyard to your hand"
  | .grant (.artifactCreature p t kw) .target =>
    s!"until end of turn, {noun} becomes an artifact creature with base power and toughness {p}/{t} and gains {kw}"
  | .discard (.cardsUnlessType n ty) =>
    s!"discard {englishNumber n} cards unless you discard {indefinite ty.oracleWord} {ty.oracleWord} card"
  | .putCounters (.ofKind .plusOnePlusOne n) (.youControl .eachCreature) =>
    s!"put {plusOnePlusOneCountersPhrase n} on each creature you control"
  | .putCounters (.ofKind .plusOnePlusOne n) .eachOther =>
    s!"put {plusOnePlusOneCountersPhrase n} on each other creature you control"
  | .putCounters (.ofKind .plusOnePlusOne n) (.permanent _) =>
    s!"put {plusOnePlusOneCountersPhrase n} on {noun}"
  | .exile (.topN _) .playUntilNextTurn _ =>
    s!"exile the top card of your library. {playThatCardUntilNextTurnPhrase}"
  | .exile .allCreatures .forLater .worldsWithinWorlds =>
    "Exile all creatures. Each player may put any number of creature cards from their hand onto the battlefield. Then put all cards exiled this way into their owners' hands. Exile Worlds Within Worlds."
  | .exile .hand .playUntilNextTurn .thenDrawThree =>
    "Exile all the cards from your hand, then draw that many cards. Until the end of your next turn, you may play cards exiled this way."
  | .becomeCopy .nontokenCreaturesYouControl =>
    "For each nontoken creature you control, create a token that's a copy of that creature, except it isn't legendary."
  | .gainControl .untilEotOrNextIfVillain =>
    "Gain control of target creature until end of turn. If you control a Villain with greater mana value than that creature, gain control of that creature until the end of your next turn instead. Untap that creature. It gains haste until end of turn."
  | .mill (.fixed n) _ (.permanentAndGainLife life) =>
    s!"Mill {n} cards. You may put a permanent card from among the milled cards into your hand. You gain {life} life."
  | .mayCast .nextRedOrGreenCreature .unlimited .withoutPaying _ =>
    "The next red or green creature spell you cast this turn can be cast without paying its mana cost"
  | .putOnLibrary .secondOrBottomThenConnive .target =>
    "The owner of target creature an opponent controls puts it into their library second from the top or on the bottom. Then up to one target creature you control connives."
  | .returnToHand .upToTwoGyModal _ =>
    "Choose up to two. Return those cards from your graveyard to your hand. • Target artifact card. • Target creature card. • Target enchantment card. • Target land card."
  | .spellsCostLess (.cardType ty) (.fixed n) =>
    s!"{ty} spells you cast this turn cost \{{n}} less to cast"
  | .spellsCostLess (.supertype s) (.fixed n) =>
    s!"{s} spells you cast this turn cost \{{n}} less to cast"
  | r =>
    match r.onPermanent? with
    | some action => PermanentAction.toNotation action noun
    | none => ""

/-- Nested `sequence` constructors, left to right. An `or` stays one step:
flattening it would resolve every alternative. -/
def flatten : SpellResolution → List SpellResolution
  | .sequence rs => rs.flatMap flatten
  | r => [r]

/-- Printed wording of a flat sequence. Known shapes keep their Oracle text;
other sequences join each step. -/
private def phraseSequence (rs : List SpellResolution) (noun : String) : String :=
  match (Resolution.sequence rs).onPermanent? with
  | some action => PermanentAction.toNotation action noun
  | none =>
  match rs with
  | [.draw (.fixed n) .you, .discard (.cards 1)] =>
    s!"draw {cardPhrase n.toNat}, then discard a card"
  | [.draw (.fixed cards) .you, .loseLife (.fixed life) .you] =>
    s!"you draw {cardPhrase cards.toNat} and lose {life} life"
  | [.draw (.fixed cards) .player, .loseLife (.fixed life) .player] =>
    s!"{noun} draws {cardPhrase cards.toNat} and loses {life} life"
  | [.destroy .target .none, .loseLife (.fixed n) (.controller .target)] =>
    s!"destroy {noun}. Its controller loses {n} life"
  | [.returnToHand .targetSpell _, .draw (.fixed 1)] =>
    s!"return {noun} to its owner's hand. Draw a card"
  | [.counter, .«if» (.mvAtMost n) .recruit] =>
    s!"counter {noun}. If that spell's mana value was {n} or less, recruit"
  | [.returnToHand (.target .graveyardCard) _, .amass (.fixed n) subtype] =>
    s!"return up to one {noun} to your hand. Amass {pluralizeName subtype} {n}"
  | [.draw (.fixed 1), .loseLife (.fixed 1), .amass (.fixed n) subtype] =>
    s!"you draw a card and lose 1 life. Amass {pluralizeName subtype} {n}"
  | [.createTokens kind (.fixed n) _ .you _, .pump (.fixed p) (.fixed t) .creaturesYouControl] =>
    let tokens := capitalizeAscii (TokenKind.createPhrase kind n.toNat)
    s!"{tokens}, then creatures you control get {signedStat p}/{signedStat t} until end of turn."
  | [.destroy .target .none, .gainLife (.fixed n) .you] =>
    s!"destroy {noun}. You gain {n} life"
  | [.destroy .target .none, .surveil (.fixed 1) .none] =>
    s!"destroy {noun}. Surveil 1"
  | [.tap .target true, .scry (.fixed scryN), .draw (.fixed drawN)] =>
    s!"tap {noun}. Scry {scryN}. Draw {cardPhrase drawN.toNat}"
  | [.pump (.fixed p) (.fixed t) .target, .draw (.fixed 1)] =>
    let tStr := if t == 0 && p < 0 then "-0" else signedStat t
    s!"Target creature gets {signedStat p}/{tStr} until end of turn.\nDraw a card."
  | [.putCounters (.ofKind .plusOnePlusOne 1) .permanent, .grant (.keywords k) .target] =>
    if k == Keyword.lifelink.merge Keyword.indestructible then
      "put a +1/+1 counter on target creature. It gains lifelink and indestructible until end of turn"
    else
      String.intercalate ". " (rs.map (phraseOne · noun))
  | [.grant (.keywords k) .target, .draw (.fixed 1)] =>
    if k == Keyword.vigilance.merge Keyword.cantBeBlocked then
      s!"{noun} gains vigilance until end of turn and can't be blocked this turn"
    else
      String.intercalate ". " (rs.map (phraseOne · noun))
  | [.pump (.fixed p) (.fixed t) .creaturesYouControl, .grant (.keywords k) .creaturesYouControl] =>
    s!"Creatures you control get {signedStat p}/{signedStat t} and gain {k.joinedAnd} until end of turn"
  | [.untap .target, .pump (.fixed p) (.fixed t) .target, .«if» (.subtype subtype) (.may (.attach .equipmentYouControl .target) (.sequence []))] =>
    s!"untap {noun}. It gets {signedStat p}/{signedStat t} until end of turn. If it's {indefinite subtype} {subtype}, you may attach an Equipment you control to it"
  | [.putCounters (.ofKind kind k) .firstTargetCreatureYouControl, .fight .announced .mutual] =>
    s!"put {kind.countersPhrase k} on target creature you control. Then it fights target creature an opponent controls"
  | [.putCounters (.ofKind kind k) .firstTargetCreatureYouControl,
     .«if» .castFromGraveyard (.putCounters (.ofKind .plusOnePlusOne m) .eachOther)] =>
    s!"put {kind.countersPhrase k} on target creature you control. If this spell was cast from a graveyard, also put {plusOnePlusOneCountersPhrase m} on each other creature you control"
  | [.dealDamage (.fixed n) (.nonSubtypeCreatures sub) _, .addMana #[] (.fixed m) (.subtypeSpells sub2)] =>
    s!"deals {n} damage to each non-{sub} creature. Add {englishNumber m.toNat} mana in any combination of colors. Spend this mana only to cast {sub2} spells"
  | [.returnToHand .targetSpell _, .«if» .giftPromised (.cant (.castSpellsThisTurn .any))] =>
    "return target spell to its owner's hand. If the gift was promised, players can't cast spells this turn"
  | [.dealDamage (.fixed n) .target .none, .«if» .teamwork (.dealDamage (.fixed extra) (.player (.controller .target)) _)] =>
    s!"deals {n} damage to target creature. If this spell was cast using teamwork, it also deals {extra} damage to that creature's controller"
  | [.grant (.keywords k) .target, .«if» .teamwork (.grant (.keywords kw) .target)] =>
    if k == Keyword.doubleStrike then
      s!"target creature gains double strike until end of turn. If this spell was cast using teamwork, that creature also gains {kw.joinedAnd} until end of turn"
    else
      String.intercalate ". " (rs.map (phraseOne · noun))
  | [.investigate (.target .player),
     .grant (.keywords k) .creatureTargets,
     .untap .creatureTargets,
     .pump (.fixed 1) (.fixed 0) .creatureTargets] =>
    if k == Keyword.flying then
      "target player investigates. Target creature gets +1/+0 and gains flying until end of turn. Untap it"
    else
      String.intercalate ". " (rs.map (phraseOne · noun))
  | [.putCounters (.ofKind kind k) .creatureTargets, .gainLife (.fixed n) .player] =>
    s!"put {kind.countersPhrase k} on up to one target creature. Target player gains {n} life"
  | [.destroy .target .none, .searchLibrary (.put (.supertypeCard s ty) .tapped _)] =>
    s!"destroy {noun}. Its controller may search their library for a {s.oracleWord} {ty.oracleWord} card, put it onto the battlefield tapped, then shuffle"
  | [.draw (.fixed 3), .discard (.cardsUnlessType n ty)] =>
    s!"draw three cards. Then discard {englishNumber n} cards unless you discard {indefinite ty.oracleWord} {ty.oracleWord} card"
  | [.replace, .dealDamage (.fixed n) .target .none] =>
    s!"deals {n} damage to {noun}. If that creature would die this turn, exile it instead"
  | [.pump (.fixed p) (.fixed t) .target, .replace] =>
    s!"{noun} gets {signedStat p}/{signedStat t} until end of turn. If that creature would die this turn, exile it instead"
  | [.dealDamage (.fixed n) .target .none, .lose .indestructible .target, .replace] =>
    s!"deals {n} damage to {noun}. That creature loses indestructible until end of turn. If that creature would die this turn, exile it instead"
  | [.pump (.fixed p) (.fixed t) .target, .exile (.topN 1) .playUntilNextTurn _] =>
    s!"Target creature gets {signedStat p}/{signedStat t} until end of turn.\nExile the top card of your library. {playThatCardUntilNextTurnPhrase}."
  | [.pump .double .double .target, .grant (.keywords k) .target] =>
    if k == Keyword.trample then
      "Choose target creature you control. Until end of turn, double its power and toughness and it gains trample"
    else
      String.intercalate ". " (rs.map (phraseOne · noun))
  | [.gainLife (.fixed life) .player, .searchLibrary (.put .basicLand .asPrinted _), .putCounters (.ofKind .plusOnePlusOne 1) .target] =>
    s!"Target player gains {life} life, then searches their library for a basic land card, puts it onto the battlefield tapped, then shuffles. Put a +1/+1 counter on up to one target creature."
  | [.becomeCopy .sourceSpellXTimes, .dealDamage (.fixed n) .target .none] =>
    s!"When you cast this spell, copy it X times. You may choose new targets for the copies.\ndeals {n} damage to target creature."
  | _ =>
    String.intercalate ". " (rs.map (phraseOne · noun))

/-- Printed wording of a choice. The library pair keeps its Oracle sentence;
other choices join each alternative. -/
private def phraseOr (rs : List SpellResolution) (noun : String) : String :=
  match rs with
  | [.putOnLibrary .top .target, .putOnLibrary .bottom .target] =>
    s!"{noun}'s owner puts it on their choice of the top or bottom of their library"
  | [.putOnLibrary .bottom .target, .putOnLibrary .top .target] =>
    s!"{noun}'s owner puts it on their choice of the top or bottom of their library"
  | _ =>
    String.intercalate " or " ((rs.map (phraseOne · noun)).filter (· != ""))

/-- Oracle-style reminder from targeting and resolution. `.fight` with
`.timesPower` is the one-sided Quarrel wording, including a multiple of that
power. `.fight .announced` is the two-creature fight, including the later step
of a counter-then-fight sequence and a fight of up to one other creature. -/
def toPhrase (r : SpellResolution) (noun : String) : String :=
  match r with
  | .sequence rs => phraseSequence (rs.flatMap flatten) noun
  | .or rs => phraseOr rs noun
  | r => phraseOne r noun

end SpellResolution

end Mtg.Engine
