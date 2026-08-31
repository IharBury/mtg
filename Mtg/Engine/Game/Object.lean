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
  requireSubtype : Option String := none
  /-- Timing restrictions based on card type are ignored (cast-as-it-resolves
  effects such as Glamdring, Gríma, and Gandalf). -/
  ignoreTiming : Bool := false
  /-- The card is exiled face down (Flameshape, Riddles in the Dark). -/
  faceDown : Bool := false
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
  /-- True while a control-changing effect is applying (CR 800.4a). -/
  controlChanged : Bool := false
  zone : Zone
  status : Status := {}
  timestamp : Nat := 0
  /-- Present when this object is an activated ability on the stack (CR 602.2a). -/
  abilityEffect : Option Effect := none
  /-- Present when this object is a triggered ability on the stack (CR 603.3). -/
  triggeredAbility : Option TriggeredAbility := none
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
  /-- This spell's kicker cost was paid (CR 702.32). -/
  kicked : Bool := false
  /-- This spell's teamwork cost was paid (CR 702.194). -/
  teamworkPaid : Bool := false
  /-- This creature spell's sneak cost was paid (MSH sneak). -/
  sneakPaid : Bool := false
  /-- Player the sneak-returned attacker was attacking (MSH sneak). -/
  sneakAttackWhom : Option PlayerId := none
  /-- Opponent promised a gift as an additional cost. Given on resolution. -/
  giftPromisedTo : Option PlayerId := none
  /-- This object is a copy (CR 706). Copies of spells are not cast. -/
  isCopy : Bool := false
  /-- Mana produced by Delighted Halfling (or similar) was spent to cast this
  legendary spell, so it can't be countered. Copies do not inherit this. -/
  uncounterableThisCast : Bool := false
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
deriving Repr, Inhabited

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

/-- Current card types, including a lasting “becomes a creature” effect. -/
def types (o : GameObject) : Array CardType :=
  if o.status.onlyFoodArtifact then #[.artifact]
  else if o.status.returnedAsArtifact then
    let ts := o.printed.types.filter (· != .creature)
    if ts.any (· == .artifact) then ts else ts.push .artifact
  else
    let asCreature :=
      o.status.additionalCreature || o.status.additionalCreatureUntilEot
    let ts :=
      if asCreature && !o.printed.isCreature then
        o.printed.types.push .creature
      else
        o.printed.types
    if o.status.additionalArtifactUntilEot && !ts.any (· == .artifact) then
      ts.push .artifact
    else ts

/-- Current subtypes, including those granted by a lasting type-changing effect. -/
def subtypes (o : GameObject) : Array Subtype :=
  if o.status.onlyFoodArtifact then #["Food"]
  else
    let extra := o.status.additionalSubtypes.filter (fun s => !o.printed.subtypes.any (· == s))
    let raw := o.printed.subtypes ++ extra
    match o.status.replacedCreatureTypesUntilEot with
    | none => raw
    | some types =>
      let kept := raw.filter isNoncreatureSubtype
      let added := types.filter (fun t => !kept.any (· == t))
      kept ++ added

/-- Type line from current types and subtypes (CR 205.1a). -/
def typeLine (o : GameObject) : String :=
  formatTypeLine o.printed.supertypes o.types o.subtypes

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
  !o.status.onlyFoodArtifact && !o.status.returnedAsArtifact &&
    (o.printed.isCreature || o.status.additionalCreature ||
      o.status.additionalCreatureUntilEot)

/-- Whether this permanent has the legendary supertype (CR 205.4d / 704.5j). -/
def isLegendary (o : GameObject) : Bool :=
  o.printed.hasSupertype .legendary

/-- True while this spell is on the stack as an Adventure (CR 715.3b). -/
def isAdventureSpell (o : GameObject) : Bool :=
  o.adventurerCard.isSome

def hasSubtype (o : GameObject) (s : String) : Bool :=
  o.subtypes.any (· == s) ||
    (o.printed.keywords.changeling && !isNoncreatureSubtype s)

/-- Printed static abilities plus those granted by a lasting effect. -/
def staticAbilities (o : GameObject) : Array StaticAbility :=
  o.printed.staticAbilities ++ o.status.grantedStaticAbilities

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
  (source.printed.triggeredAbilities ++ source.status.grantedTriggeredAbilities).filter
    (·.firesOn event)

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
deriving Repr, Inhabited

/-- Waiting-trigger snapshots of `source`'s printed abilities that fire on `event`. -/
def GameObject.waitingTriggersFor (source : GameObject) (controller : PlayerId)
    (event : TriggerEvent) (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none) : Array WaitingTrigger :=
  source.matchingTriggers event |>.map (fun ab =>
    { controller, source, ability := ab, event, lastKnownPower, lastKnownToughness })

end Mtg.Engine
