import Mtg.Engine.Game.Status

/-!
# Game objects (CR 109)

`PlayPermission` (playing cards from exile, CR 701.14 / 715.3d),
`GameObject` — an object in the game with printed characteristics, status,
and stack metadata — `CreatureCombatAssignment` (CR 510.1),
current-characteristic helpers, and `WaitingTrigger` snapshots of
triggered abilities waiting to go on the stack (CR 603.3).
-/

namespace Mtg.Engine

set_option maxRecDepth 2048 in
deriving instance BEq for CardDef

/-- Permission to play a card from exile (CR 701.14 / 715.3d). -/
structure PlayPermission where
  /-- The player who may play the card. -/
  player : PlayerId
  /-- Remaining endings of `player`'s turns before the permission expires.
  Granted as 2 during that player's turn so it lasts until the end of their
  next turn. Ignored when `fromAdventure` is true. -/
  turnEndsRemaining : Nat
  /-- CR 715.3d permission from resolving an Adventure: lasts while the card
  remains exiled, and the card cannot be recast as an Adventure this way. -/
  fromAdventure : Bool := false
  /-- Permission lasts while the card remains exiled (e.g. Shadow of the Enemy). -/
  whileExiled : Bool := false
  /-- Mana of any type can be spent to cast this card (CR 118.12). -/
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
  /-- Controller as this object last existed on the battlefield (CR 608.2c).
  Zone changes clear `controller`; this keeps “its controller” readable. -/
  lastController : Option PlayerId := none
  /-- Player under whose control this object entered the battlefield
  (CR 110.2). Used when a control-changing effect ends (CR 800.4a / 800.4c). -/
  defaultController : Option PlayerId := none
  /-- True while a control-changing effect is applying (CR 800.4a). -/
  controlChanged : Bool := false
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
  /-- Last known power of a trigger source (CR 113.7a / 608.2g). -/
  lastKnownPower : Option Int := none
  /-- Last known toughness of a trigger source (CR 113.7a / 608.2g). -/
  lastKnownToughness : Option Int := none
  /-- Set while this card may be played from exile. -/
  playPermission : Option PlayPermission := none
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
  /-- This spell was cast from a graveyard (flashback, CR 702.34). -/
  castFromGraveyard : Bool := false
  /-- An instant or sorcery cast this way is exiled instead of being put into
  its owner's graveyard (Bilbo, Thief in the Night). -/
  exileInstantSorceryInstead : Bool := false
  /-- This spell was cast from its owner's hand. -/
  castFromHand : Bool := false
  /-- This permanent entered the battlefield as a spell that was cast
  (“if you cast it”). -/
  wasCast : Bool := false
  /-- This spell is a copy of a prepare spell cast from exile (a “prepared
  spell”). -/
  isPreparedSpell : Bool := false
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
  /-- A command-zone effect object that ends when this player's next turn
  begins (Jace, Reality Sculptor; Garruk, Curse Breaker). -/
  fraEffectUntilTurnOf : Option PlayerId := none
  /-- The instant or sorcery card in a graveyard has flashback until end of
  turn, with its mana cost as the flashback cost (Stingcaster Mage). -/
  flashbackUntilEot : Bool := false
  /-- This spell's kicker cost was paid (CR 702.32). -/
  kicked : Bool := false
  /-- This spell's teamwork cost was paid (CR 702.194). -/
  teamworkPaid : Bool := false
  /-- This creature spell's sneak cost was paid (MSH sneak). -/
  sneakPaid : Bool := false
  /-- Player the sneak-returned attacker was attacking (MSH sneak). -/
  sneakAttackWhom : Option PlayerId := none
  /-- Player, planeswalker, or battle the sneak-returned attacker was attacking (CR 508.4 / MSH sneak). -/
  sneakAttackTarget : Option AttackTarget := none
  /-- Opponent promised a gift as an additional cost. Given on resolution. -/
  giftPromisedTo : Option PlayerId := none
  /-- This object is a copy (CR 706). Copies of spells are not cast. -/
  isCopy : Bool := false
  /-- Mana produced by Delighted Halfling (or similar) was spent to cast this
  legendary spell, so it can't be countered. Copies do not inherit this. -/
  uncounterableThisCast : Bool := false
  /-- Cards exiled to pay this boast activation (Baron Helmut Zemo; MSH 227). -/
  boastExiled : Array ObjectId := #[]
  /-- Its entering has been processed (enters triggers queued). -/
  enterProcessed : Bool := false
  /-- Mana from a Treasure was spent to cast this spell. -/
  treasureManaSpent : Bool := false
  /-- Value chosen for `{X}` while this spell is on the stack (CR 107.3a).
  Off the stack, `{X}` is 0. -/
  chosenX : Option Nat := none
  /-- Printed card to restore when a copy effect ends (CR 707 / MSH). -/
  copyRestore : Option CardDef := none
  /-- The current copy effect lasts until end of turn. -/
  copyUntilEot : Bool := false
  /-- The current copy effect lasts until this controller's next turn. -/
  copyUntilNextTurn : Bool := false
  /-- The current copy effect lasts until this source leaves the battlefield. -/
  copyUntilSourceLeaves : Option ObjectId := none
  /-- A control-changing effect lasts until this source leaves (Super Hero
  Civil War; MSH 143). -/
  controlUntilSourceLeaves : Option ObjectId := none
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

/-- Current card types, including a lasting “becomes a creature” effect. -/
def types (o : GameObject) : Array CardType :=
  if o.status.onlyFoodArtifact then #[.artifact]
  else if o.status.returnedAsArtifact then
    let ts := o.printed.types.filter (· != .creature)
    if ts.any (· == .artifact) then ts else ts.push .artifact
  else
    let asCreature :=
      o.status.additionalCreature || o.status.additionalCreatureUntilEot ||
        o.status.animatedConstruct55
    let ts :=
      if o.status.notACreature then
        o.printed.types.filter (· != .creature)
      else if asCreature && !o.printed.isCreature then
        o.printed.types.push .creature
      else
        o.printed.types
    if o.status.additionalArtifactUntilEot && !ts.any (· == .artifact) then
      ts.push .artifact
    else ts

/-- Current subtypes, including those granted by a lasting type-changing effect. -/
def subtypes (o : GameObject) : Array CardSubtype :=
  if o.status.onlyFoodArtifact then #[.food]
  else
    let printed := CardSubtype.ofSubtypes o.printed.subtypes
    let added :=
      if o.status.animatedConstruct55 then o.status.additionalSubtypes.push .construct
      else o.status.additionalSubtypes
    let extra := added.filter (fun s => !printed.any (· == s))
    let raw := printed ++ extra
    match o.status.replacedCreatureTypesUntilEot with
    | none => raw
    | some types =>
      let kept := raw.filter CardSubtype.isNoncreature
      let added := types.filter (fun t => !kept.any (· == t))
      kept ++ added

/-- Current supertypes of this object (CR 205.4). -/
def supertypes (o : GameObject) : Array Supertype :=
  o.printed.supertypes

def hasSupertype (o : GameObject) (s : Supertype) : Bool :=
  o.supertypes.any (· == s)

/-- Type line from current types and subtypes (CR 205.1a). -/
def typeLine (o : GameObject) : String :=
  formatTypeLine o.supertypes o.types (o.subtypes.map CardSubtype.englishName)

/-- Printed power/toughness plus until-EOT pumps and +1/+1 counters. Layer-7a
lands-you-control CDAs (all zones), layer-7b setting, attached Aura/Equipment
bonuses, and lord bonuses are applied in `Game.power` / `Game.toughness`. -/
def power (o : GameObject) : Int :=
  (o.printed.power.getD 0) + o.status.pumpPower + (o.status.plusOnePlusOne : Int)

def toughness (o : GameObject) : Int :=
  (o.printed.toughness.getD 0) + o.status.pumpToughness + (o.status.plusOnePlusOne : Int)

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

/-- Whether this object is currently a creature (CR 205.1a / 302). -/
def isCreature (o : GameObject) : Bool :=
  !o.status.notACreature &&
  !o.status.onlyFoodArtifact && !o.status.returnedAsArtifact &&
    (o.printed.isCreature || o.status.additionalCreature ||
      o.status.additionalCreatureUntilEot || o.status.animatedConstruct55)

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
    (o.printed.keywords.changeling && !s.isNoncreature)

/-- Printed static abilities plus those granted by a lasting effect. -/
def staticAbilities (o : GameObject) : Array StaticAbility :=
  o.printed.staticAbilities ++ o.status.grantedStaticAbilities

/-- Whether an Aura with card `aura` may enchant this permanent: an artifact
or non-Aura enchantment for “Enchant artifact or non-Aura enchantment”
(Puppet Crafting), otherwise a creature (CR 303.4). -/
def auraCanEnchant (host : GameObject) (aura : CardDef) : Bool :=
  host.isOnBattlefield &&
    if aura.staticAbilities.any (· == .fra .enchantArtifactOrNonAuraEnchantment) then
      host.printed.isArtifact || (host.printed.isEnchantment && !host.printed.isAura)
    else host.isCreature

/-- Colorless nonland permanent (e.g. a legal Goblin Cratermaker destroy target). -/
def isColorlessNonland (o : GameObject) : Bool :=
  o.isOnBattlefield && !o.printed.isLand && o.printed.colors.isColorless

/-- Artifact or land on the battlefield (e.g. a legal Fire of Orthanc target). -/
def isArtifactOrLand (o : GameObject) : Bool :=
  o.isOnBattlefield && (o.printed.isArtifact || o.printed.isLand)

/-- Keywords granted until end of turn, if this object is on the battlefield. -/
def grantedUntilEot (o : GameObject) : Keywords :=
  if o.isOnBattlefield then o.status.untilEotKeywords else Keywords.none

/-- Printed keywords plus until-end-of-turn grants (CR 611.2a / 514.3). -/
def printedOrUntilEot (o : GameObject) : Keywords :=
  Keywords.merge o.printed.keywords o.grantedUntilEot

/-- True when summoning sickness currently prevents tapping or attacking
(CR 302.6). Haste overrides it. -/
def hasSummoningSickness (o : GameObject) : Bool :=
  o.isCreature && o.status.summoningSick && !o.printedOrUntilEot.haste

/-- Whether `{T}` in an activation cost is currently payable (CR 302.6). -/
def canPayTapCost (o : GameObject) : Bool :=
  !o.status.tapped && !o.hasSummoningSickness

end GameObject

/-- Printed and granted triggers of `source` that fire on `event`. -/
def GameObject.matchingTriggers (source : GameObject) (event : TriggerEvent) :
    Array TriggeredAbility :=
  (source.printed.triggeredAbilities ++ source.status.grantedTriggeredAbilities ++
      (if source.isOnBattlefield then source.status.grantedTriggersUntilEot else #[])).filter
    (·.firesOn event)

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
  | behold              -- 701.62
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

/-- Identifier for a replacement or prevention effect (CR 614 / 615). -/
structure ReplacementId where
  raw : Nat
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
  /-- Migration-only: a call site not yet classified. Excluded from trigger
  matching that depends on cause; must reach zero uses for rules events by the
  end of Phase 3. -/
  | unclassified
deriving DecidableEq, Repr, Inhabited, BEq

/-- Extract the `EffectId` if this cause is (or replaces) a one-shot effect (CR 610). -/
def EventCause.oneShotEffectId? : EventCause → Option EffectId
  | .oneShotEffect id _ _ => id
  | .replaced _ orig => orig.oneShotEffectId?
  | _ => none

/-- A triggered ability waiting to be put onto the stack the next time a
player would receive priority (CR 603.3 / 603.3b). `source` is a snapshot of
the permanent as it existed when the trigger event occurred. `lastKnownPower`
is last-known power for dies triggers (CR 113.7a) and the number of cards
looked at for “whenever you scry” (CR 701.20). `lastKnownToughness` is
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
  /-- “Only once each turn” and extra trigger copies were already applied
  when this was queued. -/
  checked : Bool := false
deriving Repr, Inhabited, BEq

/-- Waiting-trigger snapshots of `source`'s printed abilities that fire on `event`. -/
def GameObject.waitingTriggersFor (source : GameObject) (controller : PlayerId)
    (event : TriggerEvent) (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none)
    (causeId : Option ObjectId := none)
    (cause : Option GameObject := none)
    (checked : Bool := false)
    (eventCause : Option EventCause := none) : Array WaitingTrigger :=
  source.matchingTriggers event |>.map (fun ab =>
    { controller, source, ability := ab, event, lastKnownPower, lastKnownToughness,
      causeId, cause, eventCause, checked })

end Mtg.Engine
