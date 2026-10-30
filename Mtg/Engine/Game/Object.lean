import Mtg.Engine.Game.Status

/-!
# Game objects (CR 109)

`PlayPermission` (playing cards from exile, CR 701.18 / 715.3d),
`GameObject` — an object in the game with printed characteristics, status,
and stack metadata — `CreatureCombatAssignment` (CR 510.1),
current-characteristic helpers, and `WaitingTrigger` snapshots of
triggered abilities waiting to go on the stack (CR 603.3).
-/

namespace Mtg.Engine

set_option maxRecDepth 2048 in
deriving instance BEq for CardDef

/-- Permission to play a card from exile (CR 701.18 / 715.3d).
Duration (`untilEndOfTurn`, `untilEndOfNextTurnOf`, or `whileInZone`) is stored
on the enclosing `ContinuousEffectSpec.permission`. -/
structure PlayPermission where
  /-- The player who may play the card. -/
  player : PlayerId
  /-- CR 715.3d permission from resolving an Adventure: lasts while the card
  remains exiled, and the card cannot be recast as an Adventure this way. -/
  fromAdventure : Bool := false
  /-- Permission lasts while the card remains exiled (e.g. Shadow of the Enemy). -/
  whileExiled : Bool := false
  /-- Mana of any type can be spent to cast this card (CR 118.14). -/
  anyMana : Bool := false
  /-- The card may be cast without paying its mana cost. -/
  withoutManaCost : Bool := false
  /-- You may play this only while you control a permanent of this subtype
  (Flameshape). Checked as you begin to cast, not as the spell resolves. -/
  requireSubtype : Option CardSubtype := none
  /-- Timing restrictions based on card type are ignored (cast-as-it-resolves
  effects such as Glamdring, Gríma, and Gandalf). -/
  ignoreTiming : Bool := false
  /-- The card is exiled face down (Flameshape, Riddles in the Dark). -/
  faceDown : Bool := false
  /-- Casting this exiled copy unprepares `prepareSource`. -/
  prepareSource : Option ObjectId := none
  /-- Cast by paying life equal to mana value instead of the mana cost. -/
  payLifeEqualManaValue : Bool := false
deriving Repr, Inhabited, BEq

/-- An object currently in the game (CR 109). -/
structure GameObject where
  id : ObjectId
  printed : CardDef
  owner : PlayerId
  controller : Option PlayerId := none
  /-- Player under whose control this object entered the battlefield
  (CR 110.2). Used when a control-changing effect ends (CR 800.4a / 800.4c). -/
  defaultController : Option PlayerId := none
  zone : Zone
  status : Status := {}
  timestamp : Nat := 0
  /-- Present when this object is an activated ability on the stack (CR 602.2a). -/
  abilityEffect : Option Effect := none
  /-- Present when this object is a triggered ability on the stack (CR 603.3). -/
  triggeredAbility : Option TriggeredAbility := none
  /-- Follow-up a generic `queueReflexive` resolves as. Printed MSH reflexes
  use `abilityEffect` and leave this empty. -/
  reflexiveResolution : Option TriggeredAbility.TriggerResolution := none
  /-- Source of an activated or triggered ability on the stack (CR 113.7). -/
  sourceId : Option ObjectId := none
  /-- Object this Aura or Equipment is attached to (CR 303.4 / 301.5). -/
  attachedTo : Option ObjectId := none
  /-- Normal characteristics of an adventurer card, set while the spell is on
  the stack as an Adventure (CR 715.3b). -/
  adventurerCard : Option CardDef := none
  /-- Cards this permanent exiled that return when it leaves (CR 610.3). -/
  linkedExile : Array ObjectId := #[]
  /-- Zone a linked-exiled card returns to when the source leaves
  (Cloak and Dagger; MSH 234). `none` means the battlefield. -/
  returnToZone : Option Zone := none
  /-- Cards this permanent exiled that a leave trigger may return (Fiend
  Hunter). Unlike `linkedExile`, these do not return automatically. -/
  leaveTriggerExile : Array ObjectId := #[]
  /-- For a triggered ability on the stack: the object whose event caused it,
  that object's controller, and its power as the ability triggered. -/
  fraCauseId : Option ObjectId := none
  fraCauseController : Option PlayerId := none
  fraCausePower : Option Int := none
  /-- The causing object's status (its counters) as it last existed. -/
  fraCauseStatus : Option Status := none
  /-- The permanent that exiled this card, for permissions tied to it (Null
  Summoner). -/
  exiledBy : Option ObjectId := none
  /-- This object is a copy (CR 706). Copies of spells are not cast. -/
  isCopy : Bool := false
  /-- Value chosen for `{X}` while this spell is on the stack (CR 107.3a).
  Off the stack, `{X}` is 0. -/
  chosenX : Option Nat := none
deriving Repr, Inhabited, BEq

/-- How one attacking or blocking creature assigns its combat damage (CR 510.1). -/
structure CreatureCombatAssignment where
  source : ObjectId
  /-- Damage assigned to creatures blocking it (CR 510.1c) or that it is
  blocking (CR 510.1d). -/
  toCreatures : Array (ObjectId × Int) := #[]
  /-- Leftover assigned to the defending player (unblocked or trample). -/
  toPlayer : Int := 0
deriving Repr, Inhabited, BEq

namespace GameObject

def name (o : GameObject) : String := o.printed.name

/-- Name for the console and logs. A token is marked so it is not mistaken
for a card of the same name (CR 111). -/
def nameWithToken (o : GameObject) : String :=
  if o.printed.isToken then s!"{o.name} (token)" else o.name

#guard
  let tok : GameObject :=
    { id := ⟨0⟩, printed := { name := "Wolf", types := #[], isToken := true },
      owner := ⟨0⟩, zone := .battlefield }
  tok.nameWithToken == "Wolf (token)"

#guard
  let card : GameObject :=
    { id := ⟨1⟩, printed := { name := "Grizzly Bears", types := #[] },
      owner := ⟨0⟩, zone := .battlefield }
  card.nameWithToken == "Grizzly Bears"

/-- Printed card types of this object (CR 205.2). Layer-4 type-changing effects
are evaluated in `Game.objectTypes` (CR 613.1d). -/
def types (o : GameObject) : Array CardType :=
  o.printed.types

/-- Printed subtypes of this object (CR 205.3). Layer-3 and Layer-4 subtype
effects are evaluated in `Game.currentSubtypes` (CR 613.1c–d). -/
def subtypes (o : GameObject) : Array CardSubtype :=
  CardSubtype.ofSubtypes o.printed.subtypes

/-- Printed supertypes of this object (CR 205.4). Layer-4 supertype effects
are evaluated in `Game.supertypes` (CR 613.1d). -/
def supertypes (o : GameObject) : Array Supertype :=
  o.printed.supertypes

def hasSupertype (o : GameObject) (s : Supertype) : Bool :=
  o.supertypes.any (· == s)

/-- Type line from printed types and subtypes (CR 205.1a). -/
def typeLine (o : GameObject) : String :=
  formatTypeLine o.supertypes o.types (o.subtypes.map CardSubtype.englishName)

/-- Printed power/toughness plus +1/+1 counters. Layer 7a–7d effects, attached
Aura/Equipment bonuses, and lord bonuses are evaluated in `Game.power` /
`Game.toughness` (CR 613.4). -/
def power (o : GameObject) : Int :=
  (o.printed.power.getD 0) + (o.status.plusOnePlusOne : Int) - (o.status.minusOneMinusOne : Int)

def toughness (o : GameObject) : Int :=
  (o.printed.toughness.getD 0) + (o.status.plusOnePlusOne : Int) - (o.status.minusOneMinusOne : Int)

def isOnBattlefield (o : GameObject) : Bool :=
  o.zone == .battlefield && !o.status.phasedOut

/-- Still in the battlefield zone, including while phased out (CR 702.26d). -/
def isBattlefieldObject (o : GameObject) : Bool :=
  o.zone == .battlefield

def controlledBy (o : GameObject) (p : PlayerId) : Bool :=
  o.controller == some p

/-- The player “you” and “your” refer to on this object (CR 109.5): its
controller, or its owner if it has none. -/
def you (o : GameObject) : PlayerId :=
  o.controller.getD o.owner

/-- Whether this object has the printed creature card type (CR 205.2a / 302).
Prefer `Game.isCreature` when `Game` is in scope to include Layer-4 effects. -/
def isCreature (o : GameObject) : Bool :=
  o.printed.isCreature

/-- Whether this permanent has the legendary supertype (CR 205.4d / 704.5j). -/
def isLegendary (o : GameObject) : Bool :=
  o.hasSupertype .legendary

/-- True while this spell is on the stack as an Adventure (CR 715.3b). -/
def isAdventureSpell (o : GameObject) : Bool :=
  o.adventurerCard.isSome

def hasType (o : GameObject) (t : CardType) : Bool :=
  o.types.any (· == t)

def hasSubtype (o : GameObject) (s : CardSubtype) : Bool :=
  o.subtypes.any (· == s) ||
    (o.printed.keywords.changeling && (o.hasType .creature || o.hasType .kindred) && !s.isNoncreature)

/-- Printed static abilities of this object. Layer-6 ability grants and
removals are evaluated in `Game.staticAbilitiesOf` (CR 613.1f). -/
def staticAbilities (o : GameObject) : Array StaticAbility :=
  o.printed.staticAbilities

/-- Whether an Aura with card `aura` may enchant this permanent: an artifact
or non-Aura enchantment for “Enchant artifact or non-Aura enchantment”
(Puppet Crafting), otherwise a creature (CR 303.4). -/
def auraCanEnchant (host : GameObject) (aura : CardDef) : Bool :=
  host.isOnBattlefield &&
    if aura.staticAbilities.any (· == .fra .enchantArtifactOrNonAuraEnchantment) then
      host.printed.isArtifact || (host.printed.isEnchantment && !host.printed.isAura)
    else host.isCreature

/-- Colorless nonland permanent (e.g. a legal Goblin Cratermaker destroy target).
Prefer `Game.isColorlessNonland` when `Game` is in scope. -/
def isColorlessNonland (o : GameObject) : Bool :=
  o.isOnBattlefield && !o.printed.isLand && o.printed.colors.isColorless

/-- Printed keywords of this object. Layer-6 keyword grants and removals are
evaluated in `Game.currentKeywords` (CR 613.1f). -/
def printedOrUntilEot (o : GameObject) : Keywords :=
  o.printed.keywords

/-- True when summoning sickness currently prevents tapping or attacking
(CR 302.6). Haste overrides it; prefer `Game.hasSummoningSickness` when `Game`
is in scope. -/
def hasSummoningSickness (o : GameObject) : Bool :=
  o.isCreature && o.status.summoningSick && !o.printedOrUntilEot.haste

end GameObject

/-- Printed triggers of `source` that fire on `event`. Layer-6 granted triggers
and ability removals are evaluated in `Game.matchingTriggers` (CR 613.1f). -/
def GameObject.matchingTriggers (source : GameObject) (event : TriggerEvent) :
    Array TriggeredAbility :=
  source.printed.triggeredAbilities.filter (·.firesOn event)

/-- A game rule that causes an event directly (CR 103.5, 303.4h, 304.2, 307.2, 602.2b, 603.3, 608.3, 700.2d, 701.3d, 702.176, 715.3d, 733.1, 800.4a). -/
inductive GameRuleKind where
  | openingHandDraw
  | mulligan
  | instantOrSorceryFinishedResolving
  | permanentSpellResolved
  | adventureSpellResolved
  | abilityFinishedResolving
  | unattachOnHostLeave
  | playerLeftGame
  | stepAdvance
  | spellCast
  | abilityActivated
  | triggeredAbility      -- 603.3
  | reversedActivation
  | staticAbility
  | continuousEffect
  | leavingZone
  | impending             -- 702.176
  | noLegalMode           -- 700.2d
deriving DecidableEq, Repr, Inhabited, BEq

/-- A turn-based action (CR 703.4). -/
inductive TurnBasedAction where
  | phaseInOut          -- 502.1 / 703.4a
  | dayNightCheck       -- 502.2 / 703.4b
  | untapAll            -- 502.3 / 703.4c
  | drawStepDraw        -- 504.1 / 703.4d
  | sagaLoreOnMain      -- 714.3b / 703.4f
  | chooseDefendingPlayer -- 507.1 / 703.4h
  | declareAttackers    -- 508.1 / 703.4i
  | declareBlockers     -- 509.1 / 703.4j
  | assignCombatDamage (firstStrike : Bool)  -- 510.1 / 510.4 / 703.4k
  | dealCombatDamage   (firstStrike : Bool)  -- 510.2 / 510.4 / 703.4m
  | removeFromCombatAtEndOfCombat            -- 511.3
  | cleanupDiscard      -- 514.1 / 703.4n
  | cleanupClear        -- 514.2 / 703.4p (damage + until-EOT effects)
  | emptyManaPools      -- 500.5 / 703.4q
  | expireAtStepBegin   -- 500.4 / 611.2b
  | expireAtStepEnd     -- 500.5 / 611.2a
deriving DecidableEq, Repr, Inhabited, BEq

/-- A state-based action (CR 704.5 / 704.6). -/
inductive StateBasedAction where
  | lifeZeroOrLess      -- 704.5a
  | drewFromEmpty       -- 704.5b
  | tenPoison           -- 704.5c
  | tokenOutsideBattlefield  -- 704.5d
  | copyOutsideStackOrBf     -- 704.5e
  | zeroOrLessToughness -- 704.5f
  | lethalDamage        -- 704.5g
  | deathtouchDamage    -- 704.5h
  | zeroLoyalty         -- 704.5i
  | legendRule          -- 704.5j
  | worldRule           -- 704.5k
  | illegalAura         -- 704.5m
  | illegalEquipmentOrFortification  -- 704.5n
  | illegalCreatureAttachment        -- 704.5p
  | counterAnnihilation -- 704.5q (+1/+1 and -1/-1)
  | counterLimit        -- 704.5r
  | sagaFinalChapter    -- 704.5s / 714.4
  | dungeonCompleted    -- 704.5t
  | spaceSculptor       -- 704.5u
  | zeroDefenseBattle   -- 704.5v
  | illegalBattleProtector -- 704.5w
  | siegeCompleted      -- 704.5x
  | roleLimit           -- 704.5y
deriving DecidableEq, Repr, Inhabited, BEq

/-- A special action (CR 116.2). -/
inductive SpecialActionKind where
  | playLand            -- 116.2a / 305.1
  | turnFaceUp          -- 116.2b / 702.37e
  | suspend             -- 116.2f / 702.62a
  | companionToHand     -- 116.2g / 702.139a
  | foretell            -- 116.2h / 702.143a
  | plot                -- 116.2k / 702.170a
  | unlockDoor          -- 116.2m / 709.5
deriving DecidableEq, Repr, Inhabited, BEq

/-- A cost payment kind (CR 118, 601.2h, 602.2b). -/
inductive CostKind where
  | mana                -- 118.3
  | tap                 -- 118.3 / 602.2b ({T} symbol or "Tap an untapped …")
  | untap               -- 118.3 ({Q} symbol)
  | life                -- 118.3 / 119.4 ("Pay N life")
  | sacrifice           -- 118.3 / 701.21
  | discard             -- 118.3 / 701.9
  | exile               -- 118.3 / 406
  | removeCounters      -- 118.3 / 122.1
  | loyalty             -- 606.4 (+N, -N, 0 on a planeswalker)
  | collectEvidence     -- 701.59
  | behold              -- 701.4
  | waterbend           -- 701.67
  | convoke             -- 702.51
  | delve               -- 702.66
  | emerge              -- 702.119
  | casualty            -- 702.153
  | bargain             -- 702.166
  | ward                -- 702.21
  | teamwork            -- set mechanic (tap two untapped teammates)
  | returnToHand        -- 118.3 / 702.190a (sneak / return permanent to hand)
  | putCounters         -- 118.3 / 122.1
deriving DecidableEq, Repr, Inhabited, BEq

/-- The rule or effect kind that a `ReplacementId` identifies (CR 614 / 615). -/
inductive ReplacementEffectKind where
  | entersTappedSelf                     -- 616.1a
  | entersWithLoyalty                    -- 306.5b / 616.1a
  | entersWithPlusOneCounters            -- 616.1a
  | entersWithXPlusOne                   -- 616.1a
  | entersWithIndestructibleCounter      -- 616.1a
  | entersWithShield                     -- 616.1a
  | entersWithHopePerCreature            -- 616.1a
  | entersWithSagaLore                   -- 714.3a / 616.1a
  | entersUnderControl                   -- 616.1b
  | entersAsCopy                         -- 616.1c / 707.5
  | entersBackFaceUp                     -- 616.1d / 702.145b / 712.14
  | entersWithExtraCounters              -- 616.1e
  | othersEnterWithPlusOneEqualToughness -- 616.1e (Arwen, Weaver of Hope)
  | extraCounterOnPermanents             -- 122.6 / 614.1a (Doc Samson)
  | extraPlusOneCounter                  -- 122.6 / 614.1a (The Golden Gear)
  | addCountersPut                       -- 122.6 / 614.1a
  | multiplyCountersPut                  -- 122.6 / 614.1a
  | foodAlsoCreatesTreasure              -- 111 / 614.1a (Bilbo, Fellow Conspirator)
  | artifactTokensBecomeDragons          -- 111 / 614.1a (Draconic Visitor)
  | artifactTokensBecome                 -- 111 / 614.1a
  | tokenDoubling                        -- 111 / 614.1a (Bard, King of Dale)
  | multiplyTokenCreation                -- 111 / 614.1a
  | flashbackExile                       -- 702.34a
  | exileInstantSorceryInstead           -- 614.1a (Bilbo, Thief in the Night)
  | untilEotExileIfDies                  -- 614.1a (Smite, etc.)
  | finalityCounterExile                 -- 122.1h
  | exileOppDeath                        -- 614.1a (Head of the Hunt, Kalitas, etc.)
  | drawTwoExceptFirstDrawStep           -- 121.2 / 614.11
  | drawThreeExceptFirstDrawStep         -- 121.2 / 614.11
  | replaceDraw                          -- 121.2 / 614.11
  | extraDrawOnConnive                   -- 701.50 / 614.1a (Leader)
  | shieldCounterDestroy                 -- 122.1c
  | shieldCounterPreventDamage           -- 122.1c
  | preventDamageGrantedBy               -- 615
  | protectionPreventDamage              -- 702.16e
  | preventAllDamageToThis               -- 615
  | preventAllDamageToPermanent          -- 615
  | protectionFromEverythingPlayer       -- 702.16j
  | noncombatDamagePlusSourcePower       -- 614.1a (Hawkeye, Young Avenger)
  | noncombatDamagePlusOne               -- 614.1a (Tomik, Izzet Sparkmage)
  | equippedDealsDoubleDamage            -- 614.1a (Mjölnir)
  | addNoncombatDamage                   -- 614.1a
  | multiplyDamage                       -- 614.1a
  | addLifeGain                          -- 119 / 614.1a
  | multiplyLifeGain                     -- 119 / 614.1a
  | stunCounterUntap                     -- 122.1d
deriving DecidableEq, Repr, Inhabited, BEq

/-- Identifier for a replacement or prevention effect (CR 614 / 615). -/
structure ReplacementId where
  kind : ReplacementEffectKind
  object : Option ObjectId := none
  grantor : Option ObjectId := none
  player : Option PlayerId := none
  counterKind : Option CounterKind := none
deriving DecidableEq, Repr, Inhabited, BEq

/-- Every rules event carries the CR mechanism that caused it (CR 603.2, 610.1,
703.1, 704.1, 116.1, 118.1, 614.1, 615.1). -/
inductive EventCause where
  /-- A rule of the game (e.g., 103.5 draw, 307.2 sorcery goes to graveyard). -/
  | gameRule (rule : GameRuleKind)
  /-- A turn-based action (703.4). -/
  | turnBased (action : TurnBasedAction)
  /-- A state-based action (704.5). -/
  | stateBased (sba : StateBasedAction)
  /-- A special action (116.2). -/
  | specialAction (kind : SpecialActionKind) (player : PlayerId)
  /-- Payment of a cost (118, 601.2h, 602.2b). -/
  | costPayment (kind : CostKind) (payer : PlayerId) (forObject : Option ObjectId := none)
  /-- Resolution of a one-shot effect (610.1) from a spell or ability. -/
  | oneShotEffect (id : Option EffectId := none) (source : Option ObjectId := none)
      (controller : Option PlayerId := none)
  /-- A replacement effect (614) or prevention effect (615) modified a prior
  proposed event. `original` is the cause of the event that was replaced. -/
  | replaced (replacement : ReplacementId) (original : EventCause)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Extract the `EffectId` if this cause is (or replaces) a one-shot effect (CR 610). -/
def EventCause.oneShotEffectId? : EventCause → Option EffectId
  | .oneShotEffect id _ _ => id
  | .replaced _ orig => orig.oneShotEffectId?
  | _ => none

/-- Delayed triggered ability kinds created by resolving effects (CR 603.7). -/
inductive DelayedTriggerKind where
  /-- Create `count` 1/1 white Bird Soldier creature tokens with flying at the beginning of the next upkeep (The Eagles Are Coming!). -/
  | eaglesBirds (count : Nat)
  /-- Whenever you attack this turn, target creature you control gets +1/+1 until end of turn for each Plains you control (Roads Go Ever, Ever On). -/
  | attackPumpPerPlains
  /-- Return `objectId` from exile to the battlefield under its owner's control at the beginning of the next end step. -/
  | endStepReturn (objectId : ObjectId)
  /-- Exile `objectId` from the battlefield at the beginning of the next end step. -/
  | endStepExile (objectId : ObjectId)
  /-- Sacrifice `objectId` at the beginning of the next end step. -/
  | endStepSacrifice (objectId : ObjectId)
  /-- Return `objectId` from its owner's graveyard to the battlefield under `underController`'s control at the beginning of the next end step. -/
  | endStepGraveReturn (objectId : ObjectId) (underController : PlayerId)
  /-- Reveal creature cards from `controller`'s library for `count` exiled creatures at the beginning of the next end step (Synthetic Destiny). -/
  | endStepSynthetic (count : Nat)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Whether this delayed trigger fires at most once and is removed from `Game.delayedTriggers` when it triggers (CR 603.7b). -/
def DelayedTriggerKind.isOneShot : DelayedTriggerKind → Bool
  | .attackPumpPerPlains => false
  | _ => true

/-- A delayed triggered ability waiting for its trigger condition (CR 603.7). -/
structure DelayedTrigger where
  controller : PlayerId
  source : Option GameObject := none
  kind : DelayedTriggerKind
  cause : EventCause
deriving Repr, Inhabited, BEq

/-- A triggered ability waiting to be put onto the stack the next time a
player would receive priority (CR 603.3 / 603.3b). `source` is a snapshot of
the permanent as it existed when the trigger event occurred. `lastKnownPower`
is last-known power for dies triggers (CR 113.7a) and the number of cards
looked at for “whenever you scry” (CR 701.22). `lastKnownToughness` is
last-known toughness for attack triggers that copy P/T (CR 113.7a). -/
structure WaitingTrigger where
  controller : PlayerId
  source : GameObject
  ability : TriggeredAbility
  /-- Event this ability is waiting to be put on the stack for. -/
  event : TriggerEvent := .dying
  lastKnownPower : Option Int := none
  lastKnownToughness : Option Int := none
  /-- Object that caused this trigger, if any (the entering Villain for
  Baron Strucker; MSH 422). -/
  causeId : Option ObjectId := none
  /-- The causing object as it was when the ability triggered. -/
  cause : Option GameObject := none
  /-- Explicit causing player override (e.g. the attacked opponent for
  `creaturesAttackYourOpponent`). -/
  causeController : Option PlayerId := none
  /-- Rules cause for putting this trigger onto the stack (CR 603.3). -/
  eventCause : Option EventCause := none
  /-- Delayed trigger payload when this waiting trigger came from a CR 603.7 delayed triggered ability. -/
  delayedTrigger : Option (DelayedTriggerKind × EventCause) := none
  /-- “Only once each turn” and extra trigger copies were already applied
  when this was queued. -/
  checked : Bool := false
deriving Repr, Inhabited, BEq

/-- The object a `GameEvent` is about, as it existed when the change happened
(CR 113.7a / 613.1). -/
structure EventObject where
  id              : Option ObjectId      := none
  controller      : Option PlayerId      := none
  owner           : PlayerId             := ⟨0⟩
  -- characteristics (CR 109.3)
  name            : String               := ""
  colors          : ColorSet             := {}
  manaValue       : Nat                  := 0
  supertypes      : Array Supertype      := #[]
  types           : Array CardType       := #[]
  subtypes        : Array CardSubtype    := #[]
  power           : Option Int           := none
  toughness       : Option Int           := none
  loyalty         : Option Nat           := none
  keywords        : Keywords             := {}
  toxic           : Nat                  := 0
  staticAbilities : Array StaticAbility  := #[]
  -- status & designations (CR 110.5–110.6)
  zone            : Zone                 := .battlefield
  tapped          : Bool                 := false
  attacking       : Bool                 := false
  blocking        : Bool                 := false
  phasedOut       : Bool                 := false
  faceDown        : Bool                 := false
  transformed     : Bool                 := false
  attachedTo      : Option ObjectId      := none
  counters        : CounterBag           := #[]
  token              : Bool                        := false
  isCopy             : Bool                        := false
  changeling         : Bool                        := false
  -- Arrival status and printed card carried so `applyZoneEvent` reconstructs
  -- the `GameObject` without a follow-up `setObject`.
  summoningSick      : Bool                        := false
  attackingTarget    : Option AttackTarget         := none
  printed            : Option CardDef              := none
  adventurerCard     : Option CardDef              := none
  chosenX            : Option Nat                  := none
deriving Repr, Inhabited, BEq

namespace EventObject

/-- Synthesize a `CardDef` from the characteristics in `e` (CR 109.3). -/
def toCardDef (e : EventObject) : CardDef :=
  match e.printed with
  | some p => p
  | none =>
    { name := e.name
      colorIndicator := if e.colors.isColorless then none else some e.colors
      supertypes := e.supertypes
      types := e.types
      subtypes := e.subtypes.map CardSubtype.englishName
      power := e.power
      toughness := e.toughness
      loyalty := e.loyalty.map Int.ofNat
      keywords := { e.keywords with changeling := e.keywords.changeling || e.changeling }
      toxic := e.toxic
      staticAbilities := e.staticAbilities
      isToken := e.token }

/-- `s` is one of this object's supertypes. -/
def hasSupertype (o : EventObject) (s : Supertype) : Bool :=
  o.supertypes.any (· == s)

def legendary (o : EventObject) : Bool :=
  o.hasSupertype .legendary

def basic (o : EventObject) : Bool :=
  o.hasSupertype .basic

/-- `t` is one of this object's card types. -/
def hasType (o : EventObject) (t : CardType) : Bool :=
  o.types.any (· == t)

def creature (o : EventObject) : Bool :=
  o.hasType .creature

def artifact (o : EventObject) : Bool :=
  o.hasType .artifact

def land (o : EventObject) : Bool :=
  o.hasType .land

def planeswalker (o : EventObject) : Bool :=
  o.hasType .planeswalker

def instantOrSorcery (o : EventObject) : Bool :=
  o.types.any CardType.isInstantOrSorcery

/-- `s` is one of this object's types (CR 205.3; changeling creature types
are expanded into `subtypes` in Layer 4 per CR 613.3 / 702.73a). -/
def hasSubtype (o : EventObject) (s : CardSubtype) : Bool :=
  o.subtypes.any (· == s)

def equipment (o : EventObject) : Bool :=
  o.artifact && o.hasSubtype .equipment

/-- Goblin, Orc, or Army. -/
def goblinOrcArmy (o : EventObject) : Bool :=
  o.hasSubtype .goblin || o.hasSubtype .orc || o.hasSubtype .army

/-- Villain. -/
def villain (o : EventObject) : Bool :=
  o.hasSubtype .villain

/-- Hero. -/
def hero (o : EventObject) : Bool :=
  o.hasSubtype .hero

/-- Elf. -/
def elf (o : EventObject) : Bool :=
  o.hasSubtype .elf

/-- Merfolk. -/
def merfolk (o : EventObject) : Bool :=
  o.hasSubtype .merfolk

/-- Forest. -/
def forest (o : EventObject) : Bool :=
  o.hasSubtype .forest || (o.land && o.subtypes.any (· == .forest))

/-- Mountain. -/
def mountain (o : EventObject) : Bool :=
  o.hasSubtype .mountain

end EventObject

/-- This object's printed characteristics as an `EventObject` (CR 113.7a).
Prefer `Game.snapshot` when `Game` is in scope so Layers 1–7d (CR 613.1) are
evaluated. -/
def GameObject.asEvent (o : GameObject) : EventObject :=
  { id := some o.id
    controller := o.controller
    owner := o.owner
    name := o.printed.name
    colors := o.printed.colors
    manaValue := o.printed.manaValue + o.chosenX.getD 0
    supertypes := o.supertypes
    types := o.types
    subtypes :=
      if o.printed.keywords.changeling && (o.types.contains .creature || o.types.contains .kindred) then
        CardSubtype.allCreatureSubtypes.foldl (fun acc s => if acc.contains s then acc else acc.push s) o.subtypes
      else o.subtypes
    power := if o.isCreature || o.printed.power.isSome then some o.power else none
    toughness := if o.isCreature || o.printed.toughness.isSome then some o.toughness else none
    loyalty := o.printed.loyalty.map Int.toNat
    keywords := o.printedOrUntilEot
    toxic := o.printed.toxic
    staticAbilities := o.staticAbilities
    zone := o.zone
    tapped := o.status.tapped
    attacking := o.status.attacking
    blocking := !o.status.blocking.isEmpty
    phasedOut := o.status.phasedOut
    faceDown := o.status.faceDown
    transformed := o.status.transformed
    attachedTo := o.attachedTo
    counters := o.status.toCounterBag
    token := o.printed.isToken
    isCopy := o.isCopy
    changeling := o.printed.keywords.changeling
    summoningSick := o.status.summoningSick
    attackingTarget := o.status.attackingTarget
    printed := some o.printed
    adventurerCard := o.adventurerCard
    chosenX := o.chosenX }

end Mtg.Engine
