import Mtg.Engine.Card
import Mtg.Engine.Deck
import Mtg.Engine.Mana
import Mtg.Engine.Rng
import Mtg.Engine.Rules
import Mtg.Engine.Turn
import Mtg.Engine.Zone

/-!
# Game state and rules engine

Encodes starting a game (CR 103), including the London mulligan (CR 103.5),
ending a game (CR 104), priority (CR 117), playing lands (CR 116.2a / 305),
including additional land plays this turn (CR 305.2b),
casting the spells we model (CR 601), including choosing modes of modal spells
and abilities (CR 601.2b / 700.2), announcing additional or alternative costs
(CR 601.2b) before targets (CR 601.2c), dividing
damage among those targets (CR 601.2d), then determining and paying costs
including sacrificing an artifact or creature (CR 601.2f / 601.2h) or paying life (CR 118.3b / 119.4),
drawing cards and losing life (CR 121 / 118.3a),
and activating mana abilities while
paying (CR 601.2g), activating non-mana abilities of permanents, cards in hand
(typecycling, CR 702.29), and graveyard cards (CR 602),
including destroying permanents (CR 701.7), equip (CR 702.6), and lasting
type-changing animations (CR 205.1a / 611.2a), static abilities that grant
trample, pump other creatures of listed types, pump an enchanted or equipped
creature, set power and toughness
equal to lands you control in all zones (CR 604.3 / 208.2a), restrict blocking unless you control certain
creature types (CR 604 / 208.2a / 613.3 / 509.1b), or prevent blocking except by
two or more (menace, CR 702.111) or N or more creatures, until-end-of-turn
effects that prevent creatures without flying from blocking, and can't-be-blocked
(CR 509.1b / 611.2a), until-end-of-turn
layer-7b base P/T setting (CR 613.3b), Aura spells (CR 303.4),
Equipment (CR 301.5), flash (CR 702.8), hexproof (CR 702.11),
indestructible (CR 702.12), deathtouch (CR 702.2 / 704.5h), lifelink (CR 702.15),
menace (CR 702.111), scry (CR 701.20),
discard (CR 701.9), destroy (CR 701.8), including a target artifact or land or
creature (and its controller losing life), mass until-end-of-turn P/T changes,
drawing and losing life, +1/+1 counters (CR 122), until-end-of-turn
keyword grants and losses, replacement effects that exile a creature instead of
dying this turn (CR 614.1 / 700.4), attack triggers (CR 508.2 / 603), including scrying, copying this
creature's P/T onto another creature you control, giving another creature
+2/+0 and trample, or gaining life while you control a creature with power 4
or greater (Ferocious), becomes-blocked triggers
(CR 509.5c / 603), enters triggers (CR 603.6a), including searching the library
for a Forest card (CR 701.19 / 305.7), drawing, scrying, optional
discard-to-draw, damage divided as you choose when a creature enters or
attacks (CR 601.2d), returning an Elf card from your graveyard to gain
life equal to its power (CR 701.19 / 118.2), each player sacrificing a creature,
a target opponent sacrificing a creature of their choice, each opponent discarding a card,
and exiling a card from an opponent's graveyard while opponents lose life,
another-Elf-enters pumps
(CR 603.6a), landfall triggers that put +1/+1 counters or pump the source
until end of turn (CR 603.6a / 603.3d / 601.2c),
triggered abilities waiting until a player would receive priority and
going on the stack in APNAP order (CR 603.3 / 603.3b),
dies triggers that deal damage equal to last-known power (CR 700.4 / 113.7a)
or give an opposing creature -1 / -1, and “whenever one or more other creatures die”
scry triggers,
cast triggers that deal damage to each opponent when you cast an instant or
sorcery (CR 601.2i / 603.3), attack-with-Elves scry triggers and scry pumps
for each card looked at (CR 508.2 / 701.20 / 603),
vigilance (CR 702.20), `{T}: Add` mana equal to power of any color with an
Elf-only spending restriction (CR 106.10 / 605),
activated pumps that last until end of turn (including paying life),
activated abilities that
put +1/+1 counters on the source, making a target creature unblockable
until end of turn (CR 602 / 611.2a / 122 / 509.1b / 118.3b), and graveyard
activations that return the card to the battlefield tapped or to hand
(CR 404 / 602), including only if you control a legendary creature,
adventurer cards including casting an Adventure and later the permanent
(CR 715), playing exiled creature cards with mana of any type
(CR 118.12 / 400.7), cost reductions if a creature died this turn or if the
target was dealt damage this turn (CR 118.7 / 601.2f), additional costs that
sacrifice an artifact or creature or pay extra generic mana (announced at
CR 601.2b, determined and paid at 601.2f–h),
typecycling from hand (CR 702.29: discard this card, search for a land type,
put it into your hand, then shuffle),
combat (CR 506–510, including combat damage assignment under
CR 510.1c–d, deathtouch as lethal for trample, CR 702.2c / 702.19b, and lifelink,
CR 702.15b), cleanup (CR 514.3), and the state-based actions we implement
(CR 704.5, including deathtouch, CR 704.5h, and the legend rule, CR 704.5j).
-/

namespace Mtg.Engine

/-- A target chosen while casting a spell or putting an ability on the stack
(CR 115). -/
inductive Target where
  | player (id : PlayerId)
  | permanent (id : ObjectId)
  /-- A card in a graveyard or a spell on the stack (CR 404 / 115.1). -/
  | card (id : ObjectId)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Permanent status (CR 110.5). Extra fields track combat and EOT pumps. -/
structure Status where
  tapped : Bool := false
  damage : Int := 0
  summoningSick : Bool := true
  /-- Until-end-of-turn +P/+T (cleared in cleanup, CR 514.3 / 613.4c). -/
  pump : Int × Int := (0, 0)
  attacking : Bool := false
  /-- Attacking creatures this creature is blocking (CR 509.1a / 510.1d). -/
  blocking : Array ObjectId := #[]
  /-- Set when this attacker becomes blocked (CR 509.1h). Remains true even if
  every blocking creature leaves combat. -/
  blocked : Bool := false
  /-- Non-mana activations this turn, for “only once each turn”. -/
  activationsThisTurn : Nat := 0
  /-- +1/+1 counters (CR 122.1). These do not wear off in cleanup. -/
  plusOnePlusOne : Nat := 0
  /-- Keywords granted until end of turn (cleared in cleanup, CR 514.3).
  Printed keywords stay on `GameObject.printed`; this field is merged in
  `GameObject.printedOrUntilEot`. -/
  untilEotKeywords : Keywords := {}
  /-- This creature loses indestructible until end of turn (e.g. Smite). -/
  untilEotLosesIndestructible : Bool := false
  /-- If this creature would die this turn, exile it instead (CR 614.1). -/
  untilEotExileIfDies : Bool := false
  /-- Until-end-of-turn layer-7b setting of base P/T (e.g. Galion). -/
  setBasePT : Option (Int × Int) := none
  /-- This permanent is a creature in addition to its other types (CR 205.1a).
  Lasting effects such as Beorn's Hospitality's activation do not end. -/
  additionalCreature : Bool := false
  /-- Subtypes granted by a lasting type-changing effect. -/
  additionalSubtypes : Array String := #[]
  /-- Static abilities granted by a lasting effect (CR 611.2a). -/
  grantedStaticAbilities : Array StaticAbility := #[]
  /-- Dealt damage by a source with deathtouch since the last time
  state-based actions were checked (CR 704.5h). Cleared after that check. -/
  dealtDeathtouch : Bool := false
  /-- Hope counters (e.g. Dawn of a New Age). -/
  hope : Nat := 0
  /-- A once-each-turn triggered ability of this permanent has fired. -/
  firedOnceEachTurn : Bool := false
  /-- This permanent is an artifact in addition to its other types until
  end of turn (e.g. Stone by Sunlight). -/
  additionalArtifactUntilEot : Bool := false
  /-- Hone counters. Each grants +1/+0 to the equipped creature while this
  Equipment is attached (judge rulings on Dwalin / Sting). -/
  hone : Nat := 0
deriving Repr, Inhabited, BEq

namespace Status

/-- Until-end-of-turn power bonus. -/
def pumpPower (s : Status) : Int := s.pump.1

/-- Until-end-of-turn toughness bonus. -/
def pumpToughness (s : Status) : Int := s.pump.2

/-- Until-end-of-turn layer-7b base power, if set. -/
def setBasePower (s : Status) : Option Int := s.setBasePT.map (·.1)

/-- Until-end-of-turn layer-7b base toughness, if set. -/
def setBaseToughness (s : Status) : Option Int := s.setBasePT.map (·.2)

/-- Mark `n` damage on this permanent (CR 120). `deathtouch` records that a
source with deathtouch dealt this damage (CR 702.2 / 704.5h). -/
def addDamage (s : Status) (n : Int) (deathtouch := false) : Status :=
  { s with
    damage := s.damage + n
    dealtDeathtouch := s.dealtDeathtouch || (deathtouch && n > 0) }

/-- Until-end-of-turn +P/+T (CR 613.4c / 611.2a). -/
def addPump (s : Status) (p t : Int) : Status :=
  { s with pump := (s.pump.1 + p, s.pump.2 + t) }

/-- Put `n` +1/+1 counters on this permanent (CR 122.1). -/
def addPlusOnePlusOne (s : Status) (n : Nat := 1) : Status :=
  { s with plusOnePlusOne := s.plusOnePlusOne + n }

/-- Union printed-style keyword grants that last until end of turn. -/
def grantUntilEot (s : Status) (k : Keywords) : Status :=
  { s with untilEotKeywords := Keywords.merge s.untilEotKeywords k }

/-- One until-EOT status field: how to tell it is set, and how to clear it.
`clearsAtCleanup` / `clearedAtCleanup` fold this table so a new until-EOT
field is one row rather than restated in both functions. -/
structure UntilEotField where
  isSet : Status → Bool
  clear : Status → Status

def untilEotFields : List UntilEotField := [
  ⟨fun s => s.damage != 0, fun s => { s with damage := 0 }⟩,
  ⟨fun s => s.pump != (0, 0), fun s => { s with pump := (0, 0) }⟩,
  ⟨fun s => s.untilEotKeywords != Keywords.none,
    fun s => { s with untilEotKeywords := Keywords.none }⟩,
  ⟨fun s => s.untilEotLosesIndestructible,
    fun s => { s with untilEotLosesIndestructible := false }⟩,
  ⟨fun s => s.untilEotExileIfDies,
    fun s => { s with untilEotExileIfDies := false }⟩,
  ⟨fun s => s.setBasePT.isSome, fun s => { s with setBasePT := none }⟩,
  ⟨fun s => s.additionalArtifactUntilEot,
    fun s => { s with additionalArtifactUntilEot := false }⟩
]

/-- True when cleanup must clear until-EOT pumps, damage, keyword grants, or
base P/T setting (CR 514.3). -/
def clearsAtCleanup (s : Status) : Bool :=
  untilEotFields.any (·.isSet s)

/-- Status after the cleanup step removes until-EOT effects (CR 514.3). -/
def clearedAtCleanup (s : Status) : Status :=
  untilEotFields.foldl (fun acc f => f.clear acc) s

end Status

#guard
  let s : Status := { pump := (1, 2), damage := 3, setBasePT := some (4, 4) }
  s.clearsAtCleanup && s.pumpPower == 1 && s.pumpToughness == 2 &&
    s.setBasePower == some 4 &&
    s.clearedAtCleanup.pump == (0, 0) && s.clearedAtCleanup.damage == 0 &&
    s.clearedAtCleanup.setBasePT.isNone
#guard !({} : Status).clearsAtCleanup

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
deriving Repr, Inhabited, BEq

/-- An object currently in the game (CR 109). -/
structure GameObject where
  id : ObjectId
  printed : CardDef
  owner : PlayerId
  controller : Option PlayerId := none
  zone : Zone
  status : Status := {}
  timestamp : Nat := 0
  /-- Present when this object is an activated ability on the stack (CR 602.2a). -/
  abilityEffect : Option AbilityEffect := none
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
  /-- This spell was cast from a graveyard (flashback, CR 702.34). -/
  castFromGraveyard : Bool := false
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
  let ts :=
    if o.status.additionalCreature && !o.printed.isCreature then
      o.printed.types.push .creature
    else
      o.printed.types
  if o.status.additionalArtifactUntilEot && !ts.any (· == .artifact) then
    ts.push .artifact
  else ts

/-- Current subtypes, including those granted by a lasting type-changing effect. -/
def subtypes (o : GameObject) : Array Subtype :=
  let extra := o.status.additionalSubtypes.filter (fun s => !o.printed.subtypes.any (· == s))
  o.printed.subtypes ++ extra

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

def isOnBattlefield (o : GameObject) : Bool := o.zone == .battlefield

def controlledBy (o : GameObject) (p : PlayerId) : Bool :=
  o.controller == some p

/-- The player “you” and “your” refer to on this object (CR 109.5): its
controller, or its owner if it has none. -/
def you (o : GameObject) : PlayerId :=
  o.controller.getD o.owner

/-- Whether this object is currently a creature (CR 205.1a / 302). -/
def isCreature (o : GameObject) : Bool :=
  o.printed.isCreature || o.status.additionalCreature

/-- Whether this permanent has the legendary supertype (CR 205.4d / 704.5j). -/
def isLegendary (o : GameObject) : Bool :=
  o.printed.hasSupertype .legendary

/-- True while this spell is on the stack as an Adventure (CR 715.3b). -/
def isAdventureSpell (o : GameObject) : Bool :=
  o.adventurerCard.isSome

def hasSubtype (o : GameObject) (s : String) : Bool :=
  o.subtypes.any (· == s)

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

/-- Printed triggers of `source` that fire on `event`. -/
def GameObject.matchingTriggers (source : GameObject) (event : TriggerEvent) :
    Array TriggeredAbility :=
  source.printed.triggeredAbilities.filter (·.firesOn event)

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
deriving Repr, Inhabited

/-- Waiting-trigger snapshots of `source`'s printed abilities that fire on `event`. -/
def GameObject.waitingTriggersFor (source : GameObject) (controller : PlayerId)
    (event : TriggerEvent) (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none) : Array WaitingTrigger :=
  source.matchingTriggers event |>.map (fun ab =>
    { controller, source, ability := ab, event, lastKnownPower, lastKnownToughness })

/-- A spell or ability on the stack (CR 405). Last array element is the top. -/
structure StackEntry where
  objectId : ObjectId
  controller : PlayerId
  targets : Array Target
  /-- Damage assigned to each target of a “divided as you choose” effect
  (CR 601.2d). Parallel to `targets`. -/
  dividedDamage : Array Nat := #[]
  /-- Set once targets (including choosing zero) have been announced
  (CR 603.3d / 601.2c). -/
  targetsAnnounced : Bool := false
  /-- Chosen mode index for a modal spell (CR 700.2). -/
  chosenMode : Option Nat := none
deriving Repr, Inhabited

/-- Whether a proposed payment is for a spell (CR 601) or an activated ability (CR 602). -/
inductive ProposalKind where
  | spell
  | activatedAbility
deriving DecidableEq, Repr, Inhabited, BEq

/-- Snapshot of a spell or activated ability whose total cost is being paid
(CR 601.2f–h / 602.2b). Used to reverse an illegal action (CR 733.1). -/
structure ProposedSpell where
  caster : PlayerId
  cost : ManaCost
  spellId : ObjectId
  original : GameObject
  handBefore : Array ObjectId
  stackBefore : Array StackEntry
  manaBefore : ManaPool
  tapped : Array ObjectId := #[]
  kind : ProposalKind := .spell
  /-- Source permanent of an activated ability; unused for spells. -/
  sourceId : Option ObjectId := none
  tapSource : Bool := false
  sacrificeSource : Bool := false
  /-- After mana is paid, the player must sacrifice an artifact or creature
  (another, when this is an activated ability). -/
  needsSacrificeOther : Bool := false
  /-- Life paid as part of the activation cost (CR 118.3b / 119.4). -/
  payLife : Nat := 0
  /-- Discard the source from hand as part of the activation cost (CR 702.29). -/
  discardSource : Bool := false
  /-- Modes of a modal activated ability, announced at CR 601.2b. -/
  abilityModes : Array AbilityEffect := #[]
  /-- Override the announced targeting shape (e.g. Equip Human). -/
  targetKindOverride : Option EffectTargetKind := none
deriving Repr, Inhabited

/-- Choice that must be made before priority proceeds. -/
inductive Pending where
  | none
  | declareAttackers
  | declareBlockers
  /-- The player may activate mana abilities before paying (CR 601.2g). -/
  | activateManaAbilities (caster : PlayerId)
  /-- The player must choose a mode of a modal spell or ability (CR 601.2b). -/
  | chooseMode (caster : PlayerId)
  /-- The player must announce targets for the proposed spell (CR 601.2c). -/
  | chooseTargets (caster : PlayerId)
  /-- After `pay`, choose an artifact or creature to sacrifice
  (another, when paying an activated ability). -/
  | sacrificePermanent (player : PlayerId) (sourceId : ObjectId)
  /-- A resolved trigger requires this player to sacrifice a creature
  of their choice (e.g. Crude Bent Blade). -/
  | sacrificeCreature (player : PlayerId)
  /-- This player declares whether they will take a mulligan (CR 103.5). -/
  | declareMulligan (player : PlayerId)
  /-- This player puts `count` cards on the bottom after a mulligan (CR 103.5). -/
  | putOnBottom (player : PlayerId) (count : Nat)
  /-- This player is looking at the top `count` cards of their library (CR 701.20). -/
  | scry (player : PlayerId) (count : Nat)
  /-- This player may discard a card; if they do, they draw `drawCount` (CR 701.9). -/
  | mayDiscardDraw (player : PlayerId) (drawCount : Nat)
  /-- The player must announce an additional or alternative additional cost
  (CR 601.2b), before targets (CR 601.2c). -/
  | chooseAdditionalCost (player : PlayerId)
  /-- This player must sacrifice a creature they control. `chosen` are
  already-selected sacrifices; `remaining` are later players in APNAP order. -/
  | chooseSacrificeCreature (player : PlayerId) (chosen : Array ObjectId)
      (remaining : Array PlayerId)
  /-- This player must discard a card. `remaining` are later opponents. -/
  | chooseDiscardCard (player : PlayerId) (remaining : Array PlayerId)
  /-- The player announces how attacking (`forAttackers`) or blocking creatures
  assign combat damage (CR 510.1c–d). -/
  | assignCombatDamage (player : PlayerId) (forAttackers : Bool)
  /-- This player chooses which of these legendary permanents with the same
  name to keep; the rest are put into their owners' graveyards (CR 704.5j). -/
  | chooseLegend (player : PlayerId) (name : String) (ids : Array ObjectId)
  /-- This player chooses the order of their waiting triggered abilities
  for the current CR 603.3b part. -/
  | chooseTriggerToStack (player : PlayerId)
  /-- You may pay `{n}` generic mana; if you do, draw a card. -/
  | mayPayGeneric (player : PlayerId) (n : Nat)
  /-- Choose top or bottom of library for this card. -/
  | chooseLibraryPlacement (player : PlayerId) (id : ObjectId)
  /-- You may attach an Equipment you control to this creature. -/
  | mayAttachEquipment (player : PlayerId) (hostId : ObjectId)
  /-- Tap any number of Humans you control, then draw that many. -/
  | tapHumans (player : PlayerId)
  /-- Pay `{n}` or let the targeted spell be countered. -/
  | payOrLetCounter (player : PlayerId) (n : Nat) (spellId : ObjectId)
  /-- You may put a +1/+1 counter on a creature. -/
  | mayPlusOneCreature (player : PlayerId)
  /-- Discard a card for recruit; if it is not a land, create a Human Soldier. -/
  | recruitDiscard (player : PlayerId)
deriving DecidableEq, Repr, Inhabited, BEq

inductive GameResult where
  | won (player : PlayerId)
  | draw
deriving DecidableEq, Repr, BEq

structure Player where
  id : PlayerId
  name : String
  life : Int := 20
  startingLife : Int := 20
  maxHandSize : Nat := 7
  /-- Cards drawn as the game begins (CR 103.5); normally seven. -/
  startingHandSize : Nat := 7
  manaPool : ManaPool := {}
  landsPlayedThisTurn : Nat := 0
  /-- Extra land plays granted this turn (CR 305.2b). Reset in untap. -/
  additionalLandsThisTurn : Nat := 0
  poison : Nat := 0
  lost : Bool := false
  drewFromEmpty : Bool := false
  /-- Completed London mulligans this game (CR 103.5). -/
  mulligansTaken : Nat := 0
  /-- Set once this player declines further mulligans (CR 103.5). -/
  keptOpeningHand : Bool := false
  library : Array ObjectId := #[]
  hand : Array ObjectId := #[]
  graveyard : Array ObjectId := #[]
  /-- Cards drawn this turn (for “second card each turn” triggers). -/
  cardsDrawnThisTurn : Nat := 0
  /-- Spells cast this turn (for “second spell each turn” triggers). -/
  spellsCastThisTurn : Nat := 0
  /-- Noncreature spells cast this turn. -/
  noncreatureSpellsCastThisTurn : Nat := 0
  /-- Storied: enduring story for the rest of the game. -/
  enduringStory : Bool := false
deriving Repr, Inhabited

/-- A seat at the table before objects are created. -/
structure Seat where
  name : String
  deck : Array CardDef
deriving Repr, Inhabited

structure StartConfig where
  seats : Array Seat
  format : Format := .constructed
  seed : UInt64 := 20260807
  /-- Index into `seats`. `none` means the RNG chooses. -/
  startingPlayer : Option Nat := none

inductive Action where
  | pass
  | playLand (id : ObjectId)
  | tapForMana (id : ObjectId) (mana : ManaType)
  | cast (id : ObjectId)
  /-- Cast this adventurer card as its Adventure (CR 715.3). -/
  | castAdventure (id : ObjectId)
  /-- Choose a mode of a modal spell or ability (CR 601.2b). -/
  | chooseMode (idx : Nat)
  /-- Announce a target for the current instance of the word “target”
  (CR 601.2c). For a divided-damage ability, assigns all remaining damage
  to this one target (CR 601.2d). For “one or two target creatures”, this
  chooses exactly that one creature. -/
  | target (t : Target)
  /-- Announce every target of one instance of the word “target” together
  (CR 601.2c), e.g. both creatures of “one or two target creatures”. -/
  | targets (ts : Array Target)
  /-- Announce every target of one instance of the word “target” on a
  “divided as you choose” effect, together with the damage assigned to each
  (CR 601.2c / 601.2d). -/
  | divideDamage (assignments : Array (Target × Nat))
  /-- Activate a non-mana activated ability of a permanent (CR 602). -/
  | activate (id : ObjectId) (abilityIdx : Nat)
  /-- Pay the locked-in cost of a proposed spell or ability (CR 601.2h / 602.2b). -/
  | pay
  /-- After `pay`, sacrifice an artifact or creature to finish paying
  (CR 601.2h / 602.2b), a creature a resolved trigger requires, or a creature
  as a resolving effect. -/
  | sacrifice (id : ObjectId)
  /-- Choose to pay extra generic mana rather than sacrifice, as an additional
  cost (CR 601.2b). `true` pays the generic alternative; `false` sacrifices. -/
  | chooseAdditionalCost (payGeneric : Bool)
  | declareAttackers (ids : Array ObjectId)
  | declareBlockers (assignments : Array (ObjectId × ObjectId))
  /-- Announce combat damage assignment (CR 510.1). Omitted sources use a
  legal default; listed sources must divide their power among legal creature
  recipients (and leftover to the defending player only with trample). -/
  | assignCombatDamage (assignments : Array CreatureCombatAssignment)
  /-- Keep this hand as the opening hand (CR 103.5). -/
  | keep
  /-- Choose which legendary permanent to keep under the legend rule (CR 704.5j). -/
  | keepLegend (id : ObjectId)
  /-- Put waiting triggered abilities on the stack in this source order
  (first listed is put first, so it is farthest from the top) (CR 603.3b). -/
  | stackTriggers (ids : Array ObjectId)
  /-- Declare a London mulligan; it is taken after every remaining player has
  declared (CR 103.5). -/
  | takeMulligan
  /-- Put these cards on the bottom after a mulligan, first listed = new bottom. -/
  | putOnBottom (ids : Array ObjectId)
  /-- Finish scrying: `top` (last = new top) go on top of the library in that
  order; `bottom` (first = new bottom) go to the bottom (CR 701.20). -/
  | scry (top : Array ObjectId) (bottom : Array ObjectId)
  /-- Discard this card from hand; if a pending “may discard, then draw” is
  waiting, draw afterward (CR 701.9). -/
  | discard (id : ObjectId)
  /-- Decline an optional “you may discard a card”, or choose no target for an
  “up to one” trigger (CR 608.2d / 601.2c). -/
  | decline
  /-- Pay a pending generic-mana “you may pay” or “unless pays” cost. -/
  | payGeneric
  /-- Put the pending card on top of its owner's library. -/
  | chooseTop
  /-- Put the pending card on the bottom of its owner's library. -/
  | chooseBottom
  /-- Attach this Equipment, or tap these Humans. -/
  | choosePermanents (ids : Array ObjectId)
  | concede
deriving Repr

structure Game where
  players : Array Player
  objects : Array GameObject
  stack : Array StackEntry := #[]
  activePlayer : PlayerId := ⟨0⟩
  priority : PlayerId := ⟨0⟩
  step : Step := .untap
  turnNumber : Nat := 1
  startingPlayer : PlayerId := ⟨0⟩
  isFirstTurn : Bool := true
  pending : Pending := .none
  nextObjectId : Nat := 0
  timestamp : Nat := 0
  rng : Rng := Rng.ofSeed 1
  result : Option GameResult := none
  log : Array String := #[]
  format : Format := .constructed
  consecutivePasses : Nat := 0
  /-- Set when CR 514.3a grants priority during the current cleanup step. -/
  cleanupGivesPriority : Bool := false
  /-- Until-end-of-turn continuous effect: creatures without flying can't
  block (e.g. Fire of Orthanc). Cleared in cleanup (CR 514.2 / 611.2a). -/
  creaturesWithoutFlyingCantBlock : Bool := false
  /-- A creature went to a graveyard from the battlefield this turn
  (used by cost reductions such as Dreaded Bat-Cloud). Cleared as the turn ends. -/
  creatureDiedThisTurn : Bool := false
  /-- Spell or ability proposed and waiting for mana abilities / payment
  (CR 601.2f–h / 602.2b). -/
  proposedSpell : Option ProposedSpell := none
  /-- Players still to declare keep-or-mulligan in the current CR 103.5 round. -/
  mulliganToDeclare : Array PlayerId := #[]
  /-- Players who declared they will mulligan this round; taken together after
  every remaining player has declared (CR 103.5). -/
  willMulligan : Array PlayerId := #[]
  /-- Players who still must put cards on the bottom after simultaneous mulligans. -/
  mulliganToBottom : Array PlayerId := #[]
  /-- Combat damage assigned this step and not yet dealt (CR 510.1 / 510.2). -/
  assignedCombatDamage : Array CreatureCombatAssignment := #[]
  /-- Triggered abilities waiting to be put onto the stack the next time a
  player would receive priority (CR 603.3 / 603.3b). Distinguished by
  `WaitingTrigger.event`. -/
  waitingTriggers : Array WaitingTrigger := #[]
  /-- True after a first-strike combat damage step has been dealt this combat
  (CR 702.7b). Cleared when combat ends. -/
  firstStrikeDamageDone : Bool := false
  /-- After first-strike damage, a regular combat damage step is still pending
  (CR 702.7b). -/
  pendingRegularCombatDamage : Bool := false
  /-- Draw these cards after the current scry finishes (e.g. Hithlain Knots). -/
  pendingDrawAfterScry : Option (PlayerId × Nat) := none
deriving Repr, Inhabited

namespace Game

def logMsg (g : Game) (msg : String) : Game :=
  { g with log := g.log.push msg }

def over (g : Game) : Bool := g.result.isSome

def player (g : Game) (p : PlayerId) : Player :=
  g.players[p.idx]!

def setPlayer (g : Game) (pl : Player) : Game :=
  { g with players := g.players.set! pl.id.idx pl }

def modifyPlayer (g : Game) (p : PlayerId) (f : Player → Player) : Game :=
  g.setPlayer (f (g.player p))

/-- Set `p`'s life total and log `msg`. -/
def setLife (g : Game) (p : PlayerId) (life : Int) (msg : String) : Game :=
  g.setPlayer { (g.player p) with life := life } |>.logMsg msg

def livingPlayers (g : Game) : Array Player :=
  g.players.filter (fun pl => !pl.lost)

/-- Living opponents of `p` (CR 102.2). -/
def livingOpponents (g : Game) (p : PlayerId) : Array Player :=
  g.livingPlayers.filter (fun pl => pl.id != p)

/-- Apply `f` to each living opponent of `controller`. -/
def forEachOpponent (g : Game) (controller : PlayerId) (f : Game → PlayerId → Game) :
    Game :=
  g.livingOpponents controller |>.foldl (fun g pl => f g pl.id) g

/-- Player targets for every member of `ps`. -/
def playerTargets (ps : Array Player) : Array Target :=
  ps.map (fun pl => Target.player pl.id)

/-- Living players in turn order from `start` who satisfy `eligible`. -/
def playersInOrderFrom (g : Game) (start : PlayerId) (eligible : Player → Bool) :
    Array PlayerId :=
  let n := g.players.size
  Id.run do
    let mut acc : Array PlayerId := #[]
    for k in [0:n] do
      let q : PlayerId := ⟨(start.idx + k) % n⟩
      if eligible (g.player q) then
        acc := acc.push q
    return acc

def opponent (g : Game) (p : PlayerId) : PlayerId :=
  let living := g.livingPlayers
  if living.size == 2 then
    if living[0]!.id == p then living[1]!.id else living[0]!.id
  else
    PlayerId.mk ((p.idx + 1) % g.players.size)

def nextLiving (g : Game) (p : PlayerId) : PlayerId :=
  let n := g.players.size
  Id.run do
    for k in [1:n+1] do
      let q : PlayerId := ⟨(p.idx + k) % n⟩
      if !(g.player q).lost then
        return q
    return p

def findObject? (g : Game) (id : ObjectId) : Option GameObject :=
  g.objects.find? (fun o => o.id == id)

def object! (g : Game) (id : ObjectId) : GameObject :=
  match g.findObject? id with
  | some o => o
  | none => panic! s!"missing object {id}"

def setObject (g : Game) (o : GameObject) : Game :=
  match g.objects.findIdx? (fun x => x.id == o.id) with
  | some i => { g with objects := g.objects.set! i o }
  | none => { g with objects := g.objects.push o }

def battlefield (g : Game) : Array GameObject :=
  g.objects.filter GameObject.isOnBattlefield

def permanentsOf (g : Game) (p : PlayerId) : Array GameObject :=
  g.battlefield.filter (fun o => o.controlledBy p)

/-- Whether `p` currently has an enduring story. -/
def hasEnduringStory (g : Game) (p : PlayerId) : Bool :=
  (g.player p).enduringStory

/-- A permanent counts once toward Storied even if it is legendary, an
artifact, and a Saga. -/
def countsTowardStoried (_g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield &&
    (o.isLegendary || o.printed.isArtifact || o.printed.hasSubtype "Saga")

/-- Number of legendary, Saga, and/or artifact permanents `p` controls. -/
def storiedPermanentCount (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).filter (g.countsTowardStoried) |>.size

/-- Whether `p` controls a permanent with storied. -/
def controlsStoried (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o => o.printed.keywords.storied)

/-- Grant an enduring story if `p` now qualifies. The designation is on the
player and is never removed. Not a triggered ability. -/
def grantEnduringStoryIfNeeded (g : Game) (p : PlayerId) : Game :=
  if (g.player p).enduringStory then g
  else if g.controlsStoried p && g.storiedPermanentCount p ≥ 3 then
    g.modifyPlayer p (fun pl => { pl with enduringStory := true })
      |>.logMsg s!"{(g.player p).name} has an enduring story"
  else g

/-- Grant an enduring story to every player who now qualifies. -/
def refreshEnduringStory (g : Game) : Game :=
  g.players.foldl (fun g pl => g.grantEnduringStoryIfNeeded pl.id) g

/-- Lands `p` currently controls (CR 305.1). -/
def landsYouControl (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).filter (·.printed.isLand) |>.size

/-- Whether `o` currently has a “P/T equal to lands you control” ability.
This characteristic-defining ability functions in all zones (CR 208.2a / 604.3). -/
def hasLandsYouControlPT (_g : Game) (o : GameObject) : Bool :=
  o.staticAbilities.any StaticAbility.isLandsYouControlPT

/-- Power or toughness from a lands-you-control CDA (CR 208.2a / 604.3). -/
def landsYouControlPT (g : Game) (o : GameObject) : Int :=
  Int.ofNat (g.landsYouControl o.you)

/-- Characteristic power or toughness before pumps, counters, and attached
bonuses: an until-EOT layer-7b set on the battlefield, else lands you control
when that CDA applies (in all zones), else the printed value
(CR 208.2a / 604.3 / 613.3). -/
def characteristicBase (g : Game) (o : GameObject) (printed setBase : Option Int) : Int :=
  let fromCdaOrPrinted :=
    if g.hasLandsYouControlPT o then g.landsYouControlPT o else printed.getD 0
  if o.isOnBattlefield then setBase.getD fromCdaOrPrinted else fromCdaOrPrinted

/-- Whether `o` currently has a “power equal to cards in your hand” ability. -/
def hasCardsInHandPower (_g : Game) (o : GameObject) : Bool :=
  o.staticAbilities.any StaticAbility.isCardsInHandPower

/-- Characteristic power and toughness before pumps, counters, and attached
bonuses: an until-EOT layer-7b set on the battlefield, else lands you control
when that CDA applies (in all zones), else the printed values
(CR 208.2a / 604.3 / 613.3). -/
def hasCreaturesYouControlPower (_g : Game) (o : GameObject) : Bool :=
  o.staticAbilities.any StaticAbility.isCreaturesYouControlPower

def characteristicBasePT (g : Game) (o : GameObject) : Int × Int :=
  let power :=
    if g.hasCardsInHandPower o then
      let fromHand : Int := Int.ofNat (g.player o.you).hand.size
      if o.isOnBattlefield then o.status.setBasePower.getD fromHand else fromHand
    else if g.hasCreaturesYouControlPower o then
      let fromTeam : Int :=
        Int.ofNat ((g.permanentsOf o.you).filter (·.isCreature) |>.size)
      if o.isOnBattlefield then o.status.setBasePower.getD fromTeam else fromTeam
    else
      g.characteristicBase o o.printed.power o.status.setBasePower
  (power, g.characteristicBase o o.printed.toughness o.status.setBaseToughness)

/-- Characteristic power before pumps, counters, and attached bonuses. -/
def characteristicBasePower (g : Game) (o : GameObject) : Int :=
  (g.characteristicBasePT o).1

/-- Characteristic toughness before pumps, counters, and attached bonuses. -/
def characteristicBaseToughness (g : Game) (o : GameObject) : Int :=
  (g.characteristicBasePT o).2

def allocId (g : Game) : Game × ObjectId :=
  ({ g with nextObjectId := g.nextObjectId + 1 }, ⟨g.nextObjectId⟩)

def bumpTime (g : Game) : Game × Nat :=
  ({ g with timestamp := g.timestamp + 1 }, g.timestamp)

/-- Allocate a new object identity and timestamp, then put `obj` into the game. -/
def allocObject (g : Game) (printed : CardDef) (owner : PlayerId) (zone : Zone)
    (controller : Option PlayerId := none) (status : Status := {})
    (abilityEffect : Option AbilityEffect := none)
    (triggeredAbility : Option TriggeredAbility := none)
    (sourceId : Option ObjectId := none)
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none)
    (attachedTo : Option ObjectId := none) : Game × GameObject :=
  let (g, id) := g.allocId
  let (g, ts) := g.bumpTime
  let obj : GameObject := {
    id, printed, owner, controller, zone, status, timestamp := ts,
    abilityEffect, triggeredAbility, sourceId, lastKnownPower, lastKnownToughness,
    attachedTo
  }
  ({ g with objects := g.objects.push obj }, obj)

/-- Push a stack entry for an already-allocated object (CR 601.2a / 602.2a / 603.3). -/
def putStackEntry (g : Game) (controller : PlayerId) (objectId : ObjectId) : Game :=
  { g with
    stack := g.stack.push { objectId, controller, targets := #[] }
    consecutivePasses := 0 }

/-- Allocate a stack object representing an activated or triggered ability of
`source` (CR 602.2a / 603.3). -/
def allocStackAbility (g : Game) (source : GameObject) (controller : PlayerId)
    (abilityEffect : Option AbilityEffect := none)
    (triggeredAbility : Option TriggeredAbility := none)
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none) : Game × GameObject :=
  g.allocObject
    { name := s!"{source.name}'s ability", types := #[],
      oracleText := source.printed.oracleText }
    source.owner .stack (some controller)
    (abilityEffect := abilityEffect) (triggeredAbility := triggeredAbility)
    (sourceId := some source.id)
    (lastKnownPower := lastKnownPower) (lastKnownToughness := lastKnownToughness)

/-- Allocate a stack ability of `source` and push it onto the stack. -/
def putStackAbility (g : Game) (source : GameObject) (controller : PlayerId)
    (abilityEffect : Option AbilityEffect := none)
    (triggeredAbility : Option TriggeredAbility := none)
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none) : Game × GameObject :=
  let (g, obj) := g.allocStackAbility source controller abilityEffect triggeredAbility
    lastKnownPower lastKnownToughness
  (g.putStackEntry controller obj.id, obj)

/-- A Treasure token (CR 111 / 701.42). -/
def treasureToken : CardDef := {
  name := "Treasure"
  types := #[.artifact]
  subtypes := #["Treasure"]
  oracleText := "{T}, Sacrifice this artifact: Add one mana of any color."
  tapSacrificeAddAnyColor := true
  isToken := true
}

/-- A 1/1 white Human Soldier creature token. -/
def humanSoldierToken : CardDef := {
  name := "Human Soldier"
  types := #[.creature]
  subtypes := #["Human", "Soldier"]
  power := some 1
  toughness := some 1
  colorIndicator := some (ColorSet.singleton .white)
  isToken := true
}

/-- Create a token under `controller` (CR 111.2 / 608.2c). Callers that must
let enters-the-battlefield triggers see the token (amass, recruit) invoke
`afterPermanentEnters` after this returns. -/
def createToken (g : Game) (controller : PlayerId) (printed : CardDef)
    (tapped := false) : Game × GameObject :=
  let printed := { printed with isToken := true }
  let sick := printed.isCreature && !printed.keywords.haste
  let (g, obj) := g.allocObject printed controller .battlefield (some controller)
    (status := { tapped := tapped, summoningSick := sick })
  let g := g.logMsg s!"{(g.player controller).name} creates {obj.name}"
  -- Storied is not a trigger; an artifact token can be the third permanent.
  let g := g.refreshEnduringStory
  (g, g.object! obj.id)

/-- Create `n` Treasure tokens, optionally tapped. -/
def createTreasureTokens (g : Game) (controller : PlayerId) (n : Nat)
    (tapped := false) : Game :=
  Id.run do
    let mut g := g
    for _ in [0:n] do
      let (g', _) := g.createToken controller treasureToken (tapped := tapped)
      g := g'
    return g

/-- A 0/0 black Army creature token of the given subtype (amass). -/
def armyToken (subtype : String) : CardDef := {
  name := s!"{subtype} Army"
  types := #[.creature]
  subtypes := #[subtype, "Army"]
  power := some 0
  toughness := some 0
  colorIndicator := some (ColorSet.singleton .black)
  isToken := true
}

/-- A 0/0 black Goblin Army creature token (amass Goblins). -/
def goblinArmyToken : CardDef := armyToken "Goblin"

/-- A 0/0 black Orc Army creature token (amass Orcs). -/
def orcArmyToken : CardDef := armyToken "Orc"

/-- A 0/0 black Zombie Army creature token (amass Zombies). -/
def zombieArmyToken : CardDef := armyToken "Zombie"

/-- A Food token (CR 111 / 701.34). -/
def foodToken : CardDef := {
  name := "Food"
  types := #[.artifact]
  subtypes := #["Food"]
  oracleText := "{2}, {T}, Sacrifice this artifact: You gain 3 life."
  activatedAbilities := #[{
    cost := { mana := ManaCost.ofGeneric 2, tap := true, sacrificeSource := true }
    effect := .gainLife 3
  }]
  isToken := true
}

def wolfToken : CardDef := {
  name := "Wolf"
  types := #[.creature]
  subtypes := #["Wolf"]
  power := some 2
  toughness := some 2
  colorIndicator := some (ColorSet.singleton .green)
  isToken := true
}

def dwarfToken : CardDef := {
  name := "Dwarf"
  types := #[.creature]
  subtypes := #["Dwarf"]
  power := some 2
  toughness := some 2
  colorIndicator := some (ColorSet.singleton .red)
  isToken := true
}

def bearToken : CardDef := {
  name := "Bear"
  types := #[.creature]
  subtypes := #["Bear"]
  power := some 2
  toughness := some 2
  colorIndicator := some (ColorSet.singleton .green)
  isToken := true
}

def elfToken : CardDef := {
  name := "Elf"
  types := #[.creature]
  subtypes := #["Elf"]
  power := some 1
  toughness := some 1
  colorIndicator := some (ColorSet.singleton .green)
  isToken := true
}

/-- Printed characteristics for a `TokenKind`. -/
def tokenPrinted (k : TokenKind) : CardDef :=
  match k with
  | .treasure => treasureToken
  | .food => foodToken
  | .humanSoldier => humanSoldierToken
  | .wolf => wolfToken
  | .dwarf => dwarfToken
  | .bear => bearToken
  | .elf => elfToken

/-- Create `n` tokens of `kind`. -/
def createKindTokens (g : Game) (controller : PlayerId) (kind : TokenKind)
    (n : Nat) (tapped := false) : Game :=
  Id.run do
    let mut g := g
    for _ in [0:n] do
      let (g', _) := g.createToken controller (tokenPrinted kind) (tapped := tapped)
      g := g'
    return g

/-- Attach `src` to `host` (CR 301.5 / 303.4). -/
def attachSourceTo (g : Game) (src host : GameObject) : Game :=
  let (g, ts) := g.bumpTime
  let src := g.object! src.id
  let g := g.setObject { src with attachedTo := some host.id, timestamp := ts }
  g.logMsg s!"{src.name} attaches to {host.name}"

/-- An ability object ceases to exist after it resolves (CR 608.2m). -/
def ceaseToExist (g : Game) (id : ObjectId) : Game :=
  { g with objects := g.objects.filter (fun o => o.id != id) }

/-- Remove an id from a zone list. -/
def stripId (ids : Array ObjectId) (id : ObjectId) : Array ObjectId :=
  ids.filter (fun x => x != id)

def removeFromZoneList (g : Game) (id : ObjectId) (z : Zone) : Game :=
  match z with
  | .library p => g.modifyPlayer p (fun pl => { pl with library := stripId pl.library id })
  | .hand p => g.modifyPlayer p (fun pl => { pl with hand := stripId pl.hand id })
  | .graveyard p => g.modifyPlayer p (fun pl => { pl with graveyard := stripId pl.graveyard id })
  | .stack => { g with stack := g.stack.filter (fun e => e.objectId != id) }
  | _ => g

/-- Move an object to a new zone, assigning a new object identity (CR 400.7).
Auras and Equipment attached to a permanent that leaves the battlefield
become unattached and remain on the battlefield (CR 701.3d). -/
def unattachFrom (g : Game) (hostId : ObjectId) : Game :=
  Id.run do
    let mut g := g
    for o in g.battlefield do
      if o.attachedTo == some hostId then
        g := g.setObject { o with attachedTo := none }
        g := g.logMsg s!"{o.name} becomes unattached"
    return g

/-- Componentwise sum of two power/toughness bonuses. -/
def addStats (a b : Int × Int) : Int × Int :=
  (a.1 + b.1, a.2 + b.2)

/-- True when `src` is a lord that can grant an ability to `target` (CR 604.2). -/
def isLordOf (src target : GameObject) : Bool :=
  src.id != target.id &&
  src.isOnBattlefield &&
  target.isOnBattlefield &&
  src.controller == target.controller &&
  src.controller.isSome &&
  target.isCreature

/-- Current subtypes after Aura type-setting (e.g. Fog on the Barrow-Downs
makes the enchanted creature only a Spirit; CR 205.3m / 613.1d). -/
def currentSubtypes (g : Game) (o : GameObject) : Array Subtype :=
  match g.battlefield.find? (fun a =>
    a.attachedTo == some o.id &&
      a.staticAbilities.any (fun ab => ab.enchantedOnlySubtype?.isSome)) with
  | none => o.subtypes
  | some aura =>
    match aura.staticAbilities.findSome? (fun ab => ab.enchantedOnlySubtype?) with
    | some s => #[s]
    | none => o.subtypes

/-- Whether `o` currently has subtype `s`, including Fog-style overwrites. -/
def hasSubtype (g : Game) (o : GameObject) (s : String) : Bool :=
  (g.currentSubtypes o).any (· == s)

/-- Continuous +P/+T `src` currently grants `target` as a lord (CR 604.2 / 613.3c). -/
def grantsStatBonusTo (g : Game) (src target : GameObject) : Int × Int :=
  src.staticAbilities.foldl
    (fun acc ab =>
      match ab.lordPump? with
      | none => acc
      | some (subtypes, p, t) =>
        let sameController :=
          src.isOnBattlefield && target.isOnBattlefield &&
            src.controller == target.controller && src.controller.isSome &&
            target.isCreature
        let otherOk := src.id != target.id || ab.lordIncludesSelf
        let legendaryOk :=
          (!ab.lordLegendaryOnly || target.isLegendary) &&
          (!ab.lordNonlegendaryOnly || !target.isLegendary)
        let subtypeOk := subtypes.isEmpty || subtypes.any (g.hasSubtype target)
        if sameController && otherOk && legendaryOk && subtypeOk then
          addStats acc (p, t)
        else acc)
    (0, 0)

/-- Continuous +P/+T granted to `o` by other permanents you control (CR 613.3c). -/
def lordStatBonus (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield then (0, 0)
  else
    g.battlefield.foldl
      (fun acc src => addStats acc (g.grantsStatBonusTo src o))
      (0, 0)

/-- Continuous +P/+T this Aura or Equipment currently grants its host (CR 613.3c). -/
def auraStatBonus (aura : GameObject) : Int × Int :=
  aura.staticAbilities.foldl
    (fun acc ab => addStats acc ab.hostStatBonus)
    (0, 0)

/-- Static power/toughness from Auras and Equipment attached to `o`. -/
def attachedStatBonus (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield then (0, 0)
  else
    g.battlefield.foldl
      (fun acc aura =>
        if aura.attachedTo == some o.id then
          addStats acc (addStats (auraStatBonus aura) ((aura.status.hone : Int), 0))
        else acc)
      (0, 0)

/-- Self +P/+T from “as long as you have an enduring story”. -/
def enduringStorySelfBonus (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield then (0, 0)
  else
    match o.controller with
    | none => (0, 0)
    | some p =>
      if !g.hasEnduringStory p then (0, 0)
      else
        o.staticAbilities.foldl
          (fun acc ab =>
            match ab.selfIfEnduringStory? with
            | some (pw, tw, _) => addStats acc (pw, tw)
            | none => acc)
          (0, 0)

/-- Team +P/+T from “as long as you have an enduring story, creatures you
control get …”. -/
def enduringStoryTeamBonus (g : Game) (o : GameObject) : Int × Int :=
  if !o.isOnBattlefield || !o.isCreature then (0, 0)
  else
    match o.controller with
    | none => (0, 0)
    | some p =>
      if !g.hasEnduringStory p then (0, 0)
      else
        (g.permanentsOf p).foldl
          (fun acc src =>
            src.staticAbilities.foldl
              (fun acc ab =>
                match ab.teamIfEnduringStory? with
                | some (pw, tw) => addStats acc (pw, tw)
                | none => acc)
              acc)
          (0, 0)

/-- Keywords granted while the controller has an enduring story. -/
def enduringStoryKeywords (g : Game) (o : GameObject) : Keywords :=
  if !o.isOnBattlefield then Keywords.none
  else
    match o.controller with
    | none => Keywords.none
    | some p =>
      if !g.hasEnduringStory p then Keywords.none
      else
        o.staticAbilities.foldl
          (fun acc ab =>
            match ab.selfIfEnduringStory? with
            | some (_, _, k) => Keywords.merge acc k
            | none => acc)
          Keywords.none

/-- Power and toughness of `o`, including pumps, counters, land-count setting
effects, until-EOT base setting, attached bonuses, lord bonuses, and enduring
story bonuses (CR 208.2). Also last-known information before `o` leaves the
battlefield (CR 113.7a). -/
def snapshotPT (g : Game) (o : GameObject) : Int × Int :=
  let n : Int := o.status.plusOnePlusOne
  #[g.characteristicBasePT o, o.status.pump, (n, n), g.attachedStatBonus o,
      g.lordStatBonus o, g.enduringStorySelfBonus o, g.enduringStoryTeamBonus o].foldl
    addStats (0, 0)

/-- Power of `o` as last known information (CR 113.7a / 208.2). -/
def snapshotPower (g : Game) (o : GameObject) : Int :=
  (g.snapshotPT o).1

/-- Toughness of `o` as last known information (CR 113.7a / 208.2). -/
def snapshotToughness (g : Game) (o : GameObject) : Int :=
  (g.snapshotPT o).2

/-- Dies triggers of a creature leaving the battlefield for a graveyard
(CR 700.4 / 603.6c). -/
def dyingTriggers (g : Game) (old : GameObject) (dest : Zone) : Array WaitingTrigger :=
  if old.zone == .battlefield && old.isCreature then
    match dest, old.controller with
    | .graveyard _, some p =>
      old.waitingTriggersFor p .dying (some (g.snapshotPower old))
    | _, _ => (#[] : Array WaitingTrigger)
  else (#[] : Array WaitingTrigger)

/-- `partial` because linked-exile returns recurse into `move` (CR 610.3). -/
partial def move (g : Game) (id : ObjectId) (dest : Zone)
    (controller : Option PlayerId := none) : Game × ObjectId :=
  let old := g.object! id
  let exileInstead :=
    old.zone == .battlefield && old.status.untilEotExileIfDies &&
      match dest with
      | .graveyard _ => true
      | _ => false
  let dest := if exileInstead then Zone.exile else dest
  let died :=
    old.zone == .battlefield && old.isCreature &&
      match dest with
      | .graveyard _ => true
      | _ => false
  let dying := g.dyingTriggers old dest
  let leaving :=
    if old.zone == .battlefield then
      match old.controller with
      | some p => old.waitingTriggersFor p .leaving
      | none => (#[] : Array WaitingTrigger)
    else (#[] : Array WaitingTrigger)
  let othersDie :=
    if died then
      g.battlefield.foldl (fun acc o =>
        if o.id == old.id then acc
        else
          match o.controller with
          | some p => acc ++ o.waitingTriggersFor p .oneOrMoreOtherCreaturesDie
          | none => acc) (#[] : Array WaitingTrigger)
    else (#[] : Array WaitingTrigger)
  let g :=
    if old.zone == .battlefield then g.unattachFrom id else g
  let g := g.removeFromZoneList id old.zone
  let (g, newId) := g.allocId
  let (g, ts) := g.bumpTime
  let fresh : GameObject := {
    id := newId
    printed := old.printed
    owner := old.owner
    controller := controller
    zone := dest
    status := {}
    timestamp := ts
  }
  let g : Game :=
    { g with objects := g.objects.filter (fun (o : GameObject) => o.id != id) |>.push fresh }
  let g :=
    match dest with
    | .library p => g.modifyPlayer p (fun pl => { pl with library := pl.library.push newId })
    | .hand p => g.modifyPlayer p (fun pl => { pl with hand := pl.hand.push newId })
    | .graveyard p => g.modifyPlayer p (fun pl => { pl with graveyard := pl.graveyard.push newId })
    | _ => g
  let g := { g with
    waitingTriggers := g.waitingTriggers ++ dying ++ othersDie ++ leaving
    creatureDiedThisTurn := g.creatureDiedThisTurn || died }
  let g :=
    if exileInstead then g.logMsg s!"{old.name} is exiled instead of dying" else g
  let g :=
    if old.zone == .battlefield && !old.linkedExile.isEmpty then
      Id.run do
        let mut g := g
        for exId in old.linkedExile do
          match g.findObject? exId with
          | some o =>
            if o.zone == .exile then
              let name := o.name
              let (g', returnedId) := g.move o.id .battlefield (some o.owner)
              g := g'
              let returned := g.object! returnedId
              let sick := !returned.printed.keywords.haste
              g := g.setObject { returned with
                status := { returned.status with summoningSick := sick } }
              g := g.logMsg s!"{name} returns to the battlefield"
              let returned := g.object! returnedId
              match returned.controller with
              | some p =>
                g := { g with waitingTriggers :=
                  g.waitingTriggers ++ returned.waitingTriggersFor p .entering }
              | none => pure ()
          | none => pure ()
        return g
    else g
  (g, newId)

/-- Move `o` to its owner's graveyard and log `reason`. Exile-if-dies
replacements are applied by `move` (CR 614.1). -/
def moveToOwnerGraveyard (g : Game) (o : GameObject) (reason : String) : Game :=
  let g := g.logMsg reason
  (g.move o.id (.graveyard o.owner) none).1

/-- Put `id` onto the battlefield under `controller`, then set tap, sickness,
and optional attachment. -/
def putOntoBattlefield (g : Game) (id : ObjectId) (controller : PlayerId)
    (tapped := false) (summoningSick := true)
    (attachedTo : Option ObjectId := none) : Game × ObjectId :=
  let (g, newId) := g.move id .battlefield (some controller)
  let o := g.object! newId
  let o := { o with
    status := { o.status with tapped := tapped, summoningSick := summoningSick } }
  let o :=
    match attachedTo with
    | some host => { o with attachedTo := some host }
    | none => o
  (g.setObject o, newId)

/-- If 0 or 1 living players remain, set the game result (CR 104). -/
def decideGameIfFinished (g : Game) : Option Game :=
  let living := g.livingPlayers
  if living.size == 0 then
    some ({ g with result := some .draw } |>.logMsg "The game is a draw")
  else if living.size == 1 then
    let w := living[0]!
    some ({ g with result := some (.won w.id) } |>.logMsg s!"{w.name} wins the game")
  else none

def emptyManaPools (g : Game) : Game :=
  Id.run do
    let mut g := g
    for pl in g.players do
      if !pl.manaPool.isEmpty then
        g := g.logMsg s!"{pl.name} empties mana pool ({pl.manaPool})"
        g := g.setPlayer { pl with manaPool := ManaPool.empty }
    return g

/-- Draw `n` cards for `p` (CR 121). -/
def draw (g : Game) (p : PlayerId) (n : Nat := 1) : Game :=
  Id.run do
    let mut g := g
    for _ in [0:n] do
      let pl := g.player p
      if pl.library.isEmpty then
        g := g.setPlayer { pl with drewFromEmpty := true }
        g := g.logMsg s!"{pl.name} tries to draw from an empty library"
        return g
      else
        let top := pl.library.back!
        let cardName := (g.object! top).name
        let rest := pl.library.pop
        g := g.setPlayer { pl with library := rest }
        let (g', _) := g.move top (.hand p) none
        g := g'
        let pl := g.player p
        let drawn := pl.cardsDrawnThisTurn + 1
        g := g.setPlayer { pl with cardsDrawnThisTurn := drawn }
        g := g.logMsg s!"{pl.name} draws {cardName}"
        for o in g.permanentsOf p do
          g := { g with waitingTriggers :=
            g.waitingTriggers ++ o.waitingTriggersFor p .youDraw }
          if drawn == 2 then
            g := { g with waitingTriggers :=
              g.waitingTriggers ++ o.waitingTriggersFor p .youDrawSecondCard }
    return g

/-- Draw, then discard; if the discarded card is not a land, create a
1/1 white Human Soldier (the Recruit keyword action). -/
def beginRecruit (g : Game) (p : PlayerId) : Game :=
  let g := g.draw p 1
  if (g.player p).hand.isEmpty then
    g.logMsg s!"{(g.player p).name} has no card to discard"
  else
    { g with pending := .recruitDiscard p }.logMsg
      s!"{(g.player p).name} discards a card. If it is not a land, they create a Human Soldier token"

/-- Return a spell on the stack to its owner's hand. -/
def returnStackSpell (g : Game) (spellId : ObjectId) : Game :=
  match g.findObject? spellId with
  | none => g.logMsg "The spell is no longer on the stack"
  | some o =>
    if o.zone != .stack then
      g.logMsg s!"{o.name} is no longer on the stack"
    else
      let name := o.name
      let owner := o.owner
      let (g, _) := g.move spellId (.hand owner) none
      g.logMsg s!"{name} is returned to {(g.player owner).name}'s hand"

def shuffleLibrary (g : Game) (p : PlayerId) : Game :=
  let pl := g.player p
  let (rng, lib) := g.rng.shuffle pl.library
  { g with rng := rng } |>.setPlayer { pl with library := lib }
   |>.logMsg s!"{pl.name} shuffles their library"

/-- True when an Aura attached to `o` makes it only a listed subtype and
unable to attack or block (e.g. Fog on the Barrow-Downs). -/
def enchantedCantAttackOrBlock (g : Game) (o : GameObject) : Bool :=
  g.battlefield.any (fun a =>
    a.attachedTo == some o.id &&
      a.staticAbilities.any (fun ab => ab.enchantedOnlySubtype?.isSome))

/-- Printed haste, until-EOT haste, or a static “haste as long as you control
another …” ability. -/
def hasHaste (g : Game) (o : GameObject) : Bool :=
  o.printedOrUntilEot.haste ||
  (o.isOnBattlefield &&
    o.staticAbilities.any (fun ab =>
      match ab.hasteIfOtherSubtype? with
      | none => false
      | some t =>
        match o.controller with
        | none => false
        | some p =>
          (g.permanentsOf p).any (fun x => x.id != o.id && g.hasSubtype x t)))

def canAttack (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield && o.isCreature &&
  o.controlledBy g.activePlayer &&
  !o.status.tapped && !o.printedOrUntilEot.defender &&
  !(o.status.summoningSick && !g.hasHaste o) &&
  !g.enchantedCantAttackOrBlock o &&
  o.staticAbilities.all (fun ab =>
    match ab.cantAttackUnlessNOther? with
    | none => true
    | some (n, subtype) =>
      match o.controller with
      | none => false
      | some p =>
        let others :=
          (g.permanentsOf p).filter (fun x =>
            x.id != o.id && g.hasSubtype x subtype) |>.size
        others >= n)

/-- Whether `p` currently controls a permanent with any of these subtypes. -/
def controlsAnySubtype (g : Game) (p : PlayerId) (subtypes : Array String) : Bool :=
  (g.permanentsOf p).any (fun o => subtypes.any (g.hasSubtype o))

/-- Whether `p` currently controls a legendary creature. -/
def controlsLegendaryCreature (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o =>
    o.isCreature && o.printed.hasSupertype .legendary)

/-- Whether `p` currently controls an Equipment. -/
def controlsEquipment (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o => o.printed.isEquipment)

/-- Whether this face should enter tapped given the controller's board. -/
def entersTapped (g : Game) (p : PlayerId) (card : CardDef) : Bool :=
  card.entersTapped ||
    (card.entersTappedUnlessLegendary && !g.controlsLegendaryCreature p) ||
    (card.entersTappedUnlessEquipment && !g.controlsEquipment p)

/-- Whether `blocker`'s static abilities currently allow it to be declared as
a blocker (CR 509.1b). Checked only when declaring blockers. -/
def mayDeclareAsBlocker (g : Game) (blocker : GameObject) : Bool :=
  blocker.staticAbilities.all (fun ab =>
    match ab.cantBlockUnless? with
    | some subtypes =>
      match blocker.controller with
      | none => false
      | some p => g.controlsAnySubtype p subtypes
    | none => true)

/-- Keywords an attached Aura or Equipment currently grants `o`. -/
def attachedGrantedKeywords (g : Game) (o : GameObject) : Keywords :=
  if !o.isOnBattlefield then Keywords.none
  else
    g.battlefield.foldl (fun acc aura =>
      if aura.attachedTo == some o.id then
        Keywords.merge acc
          (aura.staticAbilities.foldl (fun k ab =>
            Keywords.merge k ab.hostKeywords) Keywords.none)
      else acc) Keywords.none

/-- Printed, until-end-of-turn, attached-host, and enduring-story keywords. -/
def currentKeywords (g : Game) (o : GameObject) : Keywords :=
  Keywords.merge (Keywords.merge o.printedOrUntilEot (g.attachedGrantedKeywords o))
    (g.enduringStoryKeywords o)

/-- Printed or until-end-of-turn keyword selected by `sel`. -/
def hasPrintedOrEot (o : GameObject) (sel : Keywords → Bool) : Bool :=
  sel o.printedOrUntilEot

/-- Current keyword including attached grants. -/
def hasKeyword (g : Game) (o : GameObject) (sel : Keywords → Bool) : Bool :=
  sel (g.currentKeywords o)

/-- Whether `o` has vigilance (CR 702.20). Attacking does not cause it to tap. -/
def hasVigilance (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.vigilance)

/-- Whether `o` has flying, printed or granted (CR 702.9). -/
def hasFlying (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.flying)

/-- Whether `o` has first strike, printed or granted (CR 702.7). -/
def hasFirstStrike (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.firstStrike) || g.hasKeyword o (·.doubleStrike)

/-- Whether `o` has double strike (CR 702.4). -/
def hasDoubleStrike (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.doubleStrike)

/-- Whether `o` has islandwalk, printed or granted (CR 702.14). -/
def hasIslandwalk (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.islandwalk)

/-- Whether `o` can't be blocked, printed or granted until end of turn
(CR 509.1b / 611.2a). -/
def hasCantBeBlocked (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.cantBeBlocked)

/-- Whether `o` has lifelink, printed or granted until end of turn (CR 702.15). -/
def hasLifelink (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.lifelink) ||
  (o.isOnBattlefield &&
    o.staticAbilities.any (fun ab =>
      match ab.lifelinkIfOtherSubtype? with
      | none => false
      | some t =>
        match o.controller with
        | none => false
        | some p =>
          (g.permanentsOf p).any (fun x => x.id != o.id && g.hasSubtype x t)))

/-- Whether `o` has menace, printed or granted until end of turn (CR 702.111).
Pairwise `canBlock` stays true; the two-or-more restriction is checked on the
declaration as a whole (CR 509.1c). -/
def hasMenace (g : Game) (o : GameObject) : Bool :=
  hasPrintedOrEot o (·.menace) ||
  (o.isOnBattlefield && o.status.plusOnePlusOne > 0 &&
    match o.controller with
    | none => false
    | some p =>
      (g.permanentsOf p).any (fun src =>
        src.staticAbilities.any StaticAbility.creaturesWithPlusOneHaveMenace))

/-- Minimum number of creatures required to block `o`, or `0` if unrestricted.
Menace is 2; Troll of Khazad-dûm is 3. -/
def minBlockersRequired (g : Game) (o : GameObject) : Nat :=
  let fromStatic :=
    o.staticAbilities.foldl (fun acc ab =>
      match ab.cantBeBlockedExcept? with
      | some n => max acc n
      | none => acc) 0
  max fromStatic (if g.hasMenace o then 2 else 0)

/-- True when `n` blockers is a legal number for `attacker` (CR 702.111b).
Zero is always legal (the attacker is unblocked). -/
def legalBlockerCount (g : Game) (attacker : GameObject) (n : Nat) : Bool :=
  let need := g.minBlockersRequired attacker
  n == 0 || need <= 1 || n >= need

/-- Whether `blocker` may be assigned to `attacker` as one creature in a
declaration (CR 509.1b). Menace is not a pairwise restriction. -/
def canBlock (g : Game) (blocker attacker : GameObject) : Bool :=
  let defender := g.opponent g.activePlayer
  let islandwalkUnblockable :=
    g.hasIslandwalk attacker &&
      (g.permanentsOf defender).any (fun o => g.hasSubtype o "Island")
  blocker.isOnBattlefield && blocker.isCreature &&
  blocker.controlledBy defender && !blocker.status.tapped &&
  blocker.status.blocking.isEmpty &&
  g.mayDeclareAsBlocker blocker &&
  !g.enchantedCantAttackOrBlock blocker &&
  (!g.creaturesWithoutFlyingCantBlock || g.hasFlying blocker) &&
  attacker.status.attacking &&
  !g.hasCantBeBlocked attacker &&
  !islandwalkUnblockable &&
  !(attacker.staticAbilities.any StaticAbility.blocksTokens &&
    blocker.printed.isToken) &&
  !(attacker.staticAbilities.any (fun ab =>
      match ab.cantBeBlockedByPowerAtMost? with
      | some n => g.snapshotPower blocker <= n
      | none => false)) &&
  (!g.hasFlying attacker ||
    g.hasFlying blocker || (g.currentKeywords blocker).reach)

/-- Whether `src` currently grants trample to `target` (CR 604.2). -/
def grantsTrampleTo (g : Game) (src target : GameObject) : Bool :=
  isLordOf src target &&
  src.staticAbilities.any (fun ab =>
    match ab.trampleSubtypes? with
    | some subtypes => subtypes.any (g.hasSubtype target)
    | none => false)

/-- Whether `o` has hexproof, printed or granted until end of turn (CR 702.11). -/
def hasHexproof (_g : Game) (o : GameObject) : Bool :=
  hasPrintedOrEot o (·.hexproof)

/-- Whether `o` has deathtouch, printed or granted until end of turn (CR 702.2). -/
def hasDeathtouch (_g : Game) (o : GameObject) : Bool :=
  hasPrintedOrEot o (·.deathtouch)

/-- Whether `o` has indestructible (CR 702.12). An until-end-of-turn effect can
make it lose the keyword. -/
def hasIndestructible (_g : Game) (o : GameObject) : Bool :=
  o.printedOrUntilEot.indestructible &&
  !(o.isOnBattlefield && o.status.untilEotLosesIndestructible)

/-- Whether `o` has trample, printed, granted until end of turn, or granted by
a static ability (CR 702.19, 604.2). -/
def hasTrample (g : Game) (o : GameObject) : Bool :=
  o.printedOrUntilEot.trample ||
  (o.isOnBattlefield && g.battlefield.any (fun src => g.grantsTrampleTo src o))

/-- Keywords including those granted by static abilities and until-EOT effects.
Only trample (lords) and indestructible (until-EOT loss) differ from
`printedOrUntilEot`; overlaying the other keywords would restate identity. -/
def effectiveKeywords (g : Game) (o : GameObject) : Keywords :=
  { o.printedOrUntilEot with
    indestructible := g.hasIndestructible o
    trample := g.hasTrample o }

/-- Characteristic power before pumps, counters, and attached bonuses. -/
def basePower (g : Game) (o : GameObject) : Int :=
  g.characteristicBasePower o

/-- Characteristic toughness before pumps, counters, and attached bonuses. -/
def baseToughness (g : Game) (o : GameObject) : Int :=
  g.characteristicBaseToughness o

/-- Current power, including until-end-of-turn pumps, counters, land-count and
until-EOT base setting effects, attached bonuses, and lord bonuses (CR 208.2). -/
def power (g : Game) (o : GameObject) : Int :=
  g.snapshotPower o

/-- Current toughness, including until-end-of-turn pumps, counters, land-count and
until-EOT base setting effects, attached bonuses, and lord bonuses (CR 208.2). -/
def toughness (g : Game) (o : GameObject) : Int :=
  g.snapshotToughness o

/-- Greatest power among creatures `p` controls; `0` if they control none. -/
def greatestPowerAmongCreatures (g : Game) (p : PlayerId) : Int :=
  let creatures := g.permanentsOf p |>.filter (·.isCreature)
  if creatures.isEmpty then 0
  else creatures.foldl (fun acc o => max acc (g.power o)) (g.power creatures[0]!)

/-- Creatures currently blocking `attackerId`. -/
def blockersOf (g : Game) (attackerId : ObjectId) : Array GameObject :=
  g.battlefield.filter (fun b => b.status.blocking.contains attackerId)

/-- Attacking creatures `blocker` is still blocking (CR 510.1d). -/
def creaturesBlockedBy (g : Game) (blocker : GameObject) : Array GameObject :=
  blocker.status.blocking.filterMap (fun id =>
    match g.findObject? id with
    | some a =>
      if a.isOnBattlefield && a.status.attacking then some a else none
    | none => none)

/-- Combat damage already assigned to `id` in `asgns`. -/
def damageAssignedTo (asgns : Array CreatureCombatAssignment) (id : ObjectId) : Int :=
  asgns.foldl
    (fun acc a =>
      acc + a.toCreatures.foldl (fun n (tid, amt) => if tid == id then n + amt else n) 0)
    0

/-- Remaining lethal for trample (CR 702.19b): toughness minus marked damage
and damage already assigned this step. Any positive assignment from a
deathtouch source is lethal (CR 702.2c). `fromDeathtouch` is the source
currently assigning, so that source needs only 1 more if lethal remains. -/
def lethalRemaining (g : Game) (o : GameObject) (already : Array CreatureCombatAssignment)
    (fromDeathtouch := false) : Int :=
  let remaining := max (g.toughness o - o.status.damage - damageAssignedTo already o.id) 0
  let alreadyDeathtouch := already.any (fun a =>
    a.toCreatures.any (fun (tid, amt) => tid == o.id && amt > 0) &&
      match g.findObject? a.source with
      | some src => g.hasDeathtouch src
      | none => false)
  if remaining == 0 || alreadyDeathtouch then 0
  else if fromDeathtouch then 1
  else remaining

/-- True when any attacking or blocking creature has first strike (CR 702.7b). -/
def combatHasFirstStrike (g : Game) : Bool :=
  g.battlefield.any (fun o =>
    g.hasFirstStrike o && (o.status.attacking || !o.status.blocking.isEmpty))

/-- Creatures that assign combat damage in the current half of CR 510.1.
A first-strike combat damage step includes only first strikers; the regular
step includes only creatures without first strike (CR 702.7b). -/
def creaturesAssigningCombatDamage (g : Game) (forAttackers : Bool) : Array GameObject :=
  let all :=
    if forAttackers then
      g.battlefield.filter (·.status.attacking)
    else
      g.battlefield.filter (fun o => !o.status.blocking.isEmpty)
  if !g.combatHasFirstStrike then all
  else if !g.firstStrikeDamageDone then all.filter (g.hasFirstStrike)
  else all.filter (fun o => !g.hasFirstStrike o || g.hasDoubleStrike o)

/-- Legal creature recipients for `source`'s combat damage (CR 510.1c–d). -/
def legalCombatDamageRecipients (g : Game) (source : GameObject) (forAttackers : Bool) :
    Array GameObject :=
  if forAttackers then g.blockersOf source.id else g.creaturesBlockedBy source

/-- True when leftover combat damage may be assigned to the defending player
(unblocked, or trample; CR 510.1a / 702.19). -/
def canAssignCombatDamageToDefendingPlayer (g : Game) (source : GameObject)
    (forAttackers : Bool) : Bool :=
  forAttackers && (!source.status.blocked || g.hasTrample source)

/-- Combat damage `source` must assign this step (CR 510.1a), or `0` if it
assigns none because no recipients remain (CR 510.1c–d). -/
def combatDamageToAssign (g : Game) (source : GameObject) (forAttackers : Bool) : Int :=
  if (g.legalCombatDamageRecipients source forAttackers).isEmpty &&
      !g.canAssignCombatDamageToDefendingPlayer source forAttackers then
    0
  else
    max (g.power source) 0

/-- True when a creature this player controls has two or more creature
recipients, so the controller must divide combat damage (CR 510.1c–d). -/
def needsCombatDamageChoice (g : Game) (forAttackers : Bool) : Bool :=
  (g.creaturesAssigningCombatDamage forAttackers).any (fun o =>
    (g.legalCombatDamageRecipients o forAttackers).size ≥ 2 && max (g.power o) 0 > 0)

/-- Living players in APNAP order (CR 101.4): the active player, then the
next player in turn order, and so on. -/
def apnapPlayers (g : Game) : Array PlayerId :=
  g.playersInOrderFrom g.activePlayer (fun pl => !pl.lost)

/-- Alias of `apnapPlayers` (CR 101.4). -/
def apnapOrder (g : Game) : Array PlayerId :=
  g.apnapPlayers

/-- Legendary permanents `p` currently controls. -/
def legendaryPermanentsOf (g : Game) (p : PlayerId) : Array GameObject :=
  (g.permanentsOf p).filter (·.isLegendary)

/-- First legend-rule group that needs a choice (CR 704.5j / 201.2a): two or
more legendary permanents with the same name controlled by the same player,
taking players in APNAP order. -/
def firstLegendRuleChoice? (g : Game) : Option (PlayerId × String × Array ObjectId) :=
  Id.run do
    for p in g.apnapPlayers do
      let legs := g.legendaryPermanentsOf p
      let mut seen : Array String := #[]
      for o in legs do
        if !seen.contains o.name then
          seen := seen.push o.name
          let group := legs.filter (fun x => x.name == o.name)
          if group.size ≥ 2 then
            return some (p, o.name, group.map (·.id))
    return none

/-- True while a player must choose which legendary permanent to keep. -/
def legendChoicePending? (g : Game) : Bool :=
  match g.pending with
  | .chooseLegend .. => true
  | _ => false

/-- Default legend-rule choice: the copy that entered most recently. -/
def defaultLegendToKeep (g : Game) (ids : Array ObjectId) : ObjectId :=
  ids.foldl (fun best id =>
    match g.findObject? best, g.findObject? id with
    | some a, some b => if b.timestamp ≥ a.timestamp then id else best
    | _, some _ => id
    | _, none => best) (ids[0]!)

/-- Perform applicable state-based actions (CR 704.3). The `Bool` is `true` if
any state-based action was performed (used by CR 514.3a). If a legend-rule
choice is required (CR 704.5j), the check pauses: that SBA is not finished,
so CR 704.3 does not yet repeat, put triggers on the stack, or grant
priority. `keepLegend` resumes the loop. -/
partial def checkSBACounted (g : Game) : Game × Bool :=
  if g.over then (g, false)
  else
    Id.run do
      let mut g := g
      let mut changed := false
      -- Players losing (CR 704.5a–c).
      for pl in g.players do
        if !pl.lost then
          if pl.life ≤ 0 then
            g := g.setPlayer { pl with lost := true }
            g := g.logMsg s!"{pl.name} loses the game (life total {pl.life})"
            changed := true
          else if pl.drewFromEmpty then
            g := g.setPlayer { pl with lost := true }
            g := g.logMsg s!"{pl.name} loses the game (drew from empty library)"
            changed := true
          else if pl.poison ≥ 10 then
            g := g.setPlayer { pl with lost := true }
            g := g.logMsg s!"{pl.name} loses the game (poison)"
            changed := true
      match g.decideGameIfFinished with
      | some finished => return (finished, true)
      | none => pure ()
      -- Waiting for a legend-rule choice: do not apply further SBAs until
      -- the player keeps one copy (CR 704.5j). Drop a stale prompt if the
      -- group is no longer two or more.
      match g.pending with
      | .chooseLegend p name ids =>
        let still := ids.filter (fun id =>
          match g.findObject? id with
          | some o =>
            o.isOnBattlefield && o.controlledBy p && o.isLegendary && o.name == name
          | none => false)
        if still.size ≥ 2 then
          return (g, changed)
        else
          g := { g with pending := .none }
      | _ => pure ()
      -- Creatures with 0 toughness or lethal damage (CR 704.5f–g).
      for o in g.battlefield do
        if o.isCreature then
          let t := g.toughness o
          if t ≤ 0 then
            g := g.moveToOwnerGraveyard o s!"{o.name} dies (toughness {t})"
            changed := true
          else if o.status.damage ≥ t && !g.hasIndestructible o then
            g := g.moveToOwnerGraveyard o s!"{o.name} dies from lethal damage"
            changed := true
          else if o.status.dealtDeathtouch then
            -- CR 704.5h: any damage from a deathtouch source since the last
            -- SBA check is lethal. The flag is then cleared even if the
            -- creature survives (e.g. indestructible).
            if !g.hasIndestructible o then
              g := g.moveToOwnerGraveyard o s!"{o.name} dies from deathtouch"
              changed := true
            else
              g := g.setObject { o with status := { o.status with dealtDeathtouch := false } }
      -- Legend rule (CR 704.5j): pause so the controller chooses one to keep.
      match g.firstLegendRuleChoice? with
      | some (p, name, ids) =>
        g := { g with pending := .chooseLegend p name ids }
        g := g.logMsg
          s!"{(g.player p).name} chooses which {name} to keep (legend rule, CR 704.5j)"
        return (g, true)
      | none => pure ()
      -- Unattached or illegally attached Auras (CR 704.5m).
      for o in g.battlefield do
        if o.printed.isAura then
          let legal :=
            match o.attachedTo.bind g.findObject? with
            | some host => host.isOnBattlefield && host.isCreature
            | none => false
          if !legal then
            g := g.moveToOwnerGraveyard o
              s!"{o.name} is put into its owner's graveyard (CR 704.5n)"
            changed := true
      -- Illegally attached Equipment (CR 704.5n). Unattached Equipment stays.
      for o in g.battlefield do
        if o.printed.isEquipment then
          let legal :=
            match o.attachedTo.bind g.findObject? with
            | some host => host.isOnBattlefield && host.printed.isCreature
            | none => true
          if !legal then
            g := g.setObject { o with attachedTo := none }
            g := g.logMsg s!"{o.name} becomes unattached (CR 704.5n)"
            changed := true
      match g.decideGameIfFinished with
      | some finished => return (finished, true)
      | none => pure ()
      if changed then
        let (g', _) := checkSBACounted g
        return (g', true)
      return (g, false)

def checkSBA (g : Game) : Game :=
  (g.checkSBACounted).1

/-- Triggered abilities waiting to be put onto the stack (CR 603.3 / 603.3b,
514.3a). All triggered abilities wait until a player would receive priority. -/
def hasWaitingTriggers (g : Game) : Bool :=
  !g.waitingTriggers.isEmpty

/-- CR 103.8a: in a two-player game the starting player skips the draw step
of their first turn. -/
def skipsFirstDraw (g : Game) : Bool :=
  g.isFirstTurn && g.players.size == 2 && g.activePlayer == g.startingPlayer

/-- Whether a player currently receives priority (CR 117.3a, 502.4, 514.3,
103.8a / 500.11). A skipped draw step grants none. -/
def playersReceivePriority (g : Game) : Bool :=
  if g.step == .cleanup then g.cleanupGivesPriority
  else if g.step == .draw && g.skipsFirstDraw then false
  else g.step.playersReceivePriority

def asSorcery? (g : Game) (p : PlayerId) : Bool :=
  !g.over && g.pending == .none && g.stack.isEmpty &&
  g.step.isMainPhase && g.activePlayer == p && g.priority == p

def hasPriority (g : Game) (p : PlayerId) : Bool :=
  !g.over && g.pending == .none && g.priority == p && g.playersReceivePriority

/-- How many lands `p` may play this turn (CR 305.2 / 305.2b). -/
def landPlaysAllowed (g : Game) (p : PlayerId) : Nat :=
  1 + (g.player p).additionalLandsThisTurn

/-- Lands remaining this turn (CR 305.2 / 305.3 / 116.2a). -/
def canPlayLand (g : Game) (p : PlayerId) : Bool :=
  g.asSorcery? p && (g.player p).landsPlayedThisTurn < g.landPlaysAllowed p

/-- Whether `p` may play `o` from exile under a granted permission (CR 701.14 / 715.3d). -/
def mayPlayFromExile (_g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  o.zone == .exile &&
  match o.playPermission with
  | some perm =>
    perm.player == p &&
      (perm.fromAdventure || perm.whileExiled || perm.turnEndsRemaining > 0)
  | none => false

/-- Cards in exile that `p` currently may play. -/
def exiledPlayable (g : Game) (p : PlayerId) : Array GameObject :=
  g.objects.filter (fun o => g.mayPlayFromExile p o)

/-- Whether `p` may play `o` from hand or from exile under a permission. -/
def mayPlayFromGraveyard (_g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  o.zone == .graveyard p && o.owner == p && o.printed.flashback.isSome

def mayPlay (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  (g.player p).hand.contains o.id || g.mayPlayFromExile p o ||
    g.mayPlayFromGraveyard p o

def playZoneError (g : Game) (p : PlayerId) (o : GameObject) : String :=
  if o.zone == .exile && !g.mayPlayFromExile p o then
    "You may not play that card from exile"
  else if o.zone == .graveyard p && !g.mayPlayFromGraveyard p o then
    "You may not play that card from your graveyard"
  else
    "That card is not in your hand"

/-- Whether `caster` may target `o` (CR 115.1, 702.11b). -/
def canBeTargetedBy (g : Game) (caster : PlayerId) (o : GameObject) : Bool :=
  !g.hasHexproof o || o.controlledBy caster

/-- Battlefield permanents matching `pred` that `caster` may target. -/
def legalPermanentTargets (g : Game) (caster : PlayerId) (pred : GameObject → Bool) :
    Array Target :=
  g.battlefield.filter (fun o => pred o && g.canBeTargetedBy caster o)
    |>.map (fun o => Target.permanent o.id)

/-- Battlefield creatures matching `pred` that `caster` may target. -/
def legalCreatureTargets (g : Game) (caster : PlayerId) (pred : GameObject → Bool) :
    Array Target :=
  g.legalPermanentTargets caster (fun o => o.isCreature && pred o)

/-- Creatures `caster` controls that they may target (CR 115.1). -/
def legalCreatureYouControlTargets (g : Game) (caster : PlayerId) : Array Target :=
  g.legalCreatureTargets caster (fun o => o.controlledBy caster)

/-- Creatures an opponent of `caster` controls that `caster` may target. -/
def legalOppCreatureTargets (g : Game) (caster : PlayerId) : Array Target :=
  g.legalCreatureTargets caster (fun o => o.controlledBy (g.opponent caster))

/-- Cards in `p`'s graveyard matching `pred` (CR 404 / 115.1). Hexproof does
not apply off the battlefield (CR 702.11b). -/
def legalGraveyardCardTargets (g : Game) (p : PlayerId) (pred : GameObject → Bool) :
    Array Target :=
  (g.player p).graveyard.filterMap (fun id =>
    match g.findObject? id with
    | some o => if pred o then some (Target.card o.id) else none
    | none => none)

/-- Spells on the stack matching `pred` (not activated or triggered abilities). -/
def stackSpells (g : Game) (pred : GameObject → Bool := fun _ => true) : Array GameObject :=
  g.stack.filterMap (fun e =>
    match g.findObject? e.objectId with
    | some o =>
      if o.abilityEffect.isNone && o.triggeredAbility.isNone && pred o then some o
      else none
    | none => none)

/-- Legal spell-on-the-stack targets matching `pred` (CR 115.1). -/
def legalStackSpellTargets (g : Game) (pred : GameObject → Bool) : Array Target :=
  g.stackSpells pred |>.map (fun o => Target.card o.id)

/-- Legal targets for an atomic targeting shape (no sequential slots). -/
def legalTargetsForAtomicKind (g : Game) (caster : PlayerId) (kind : EffectTargetKind)
    (sourceId : Option ObjectId) : Array Target :=
  match kind with
  | .none => #[]
  | .creatureYouControl =>
    g.legalCreatureYouControlTargets caster
  | .anotherCreatureYouControl =>
    g.legalCreatureTargets caster (fun o => o.controlledBy caster && some o.id != sourceId)
  | .anotherCreature =>
    g.legalCreatureTargets caster (fun o => some o.id != sourceId)
  | .playerOrCreature =>
    playerTargets g.livingPlayers ++
      g.legalCreatureTargets caster (fun _ => true)
  | .elfInYourGraveyard =>
    g.legalGraveyardCardTargets caster (fun o => g.hasSubtype o "Elf")
  | .oppCreature =>
    g.legalOppCreatureTargets caster
  | .creature =>
    g.legalCreatureTargets caster (fun _ => true)
  | .creatureWithFlying =>
    g.legalCreatureTargets caster (fun o => g.hasFlying o)
  | .artifactOrLand =>
    g.legalPermanentTargets caster (·.isArtifactOrLand)
  | .colorlessNonland =>
    g.legalPermanentTargets caster (·.isColorlessNonland)
  | .creatureYouControlThenOppCreature => #[]
  | .player =>
    playerTargets g.livingPlayers
  | .opponent =>
    playerTargets (g.livingOpponents caster)
  | .oppGraveyardCard =>
    g.livingOpponents caster
      |>.foldl (fun acc pl => acc ++ g.legalGraveyardCardTargets pl.id (fun _ => true)) #[]
  | .artifactOrEnchantment =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && (o.printed.isArtifact || o.printed.isEnchantment))
  | .artifactOrCreatureYouControl =>
    g.legalPermanentTargets caster (fun o =>
      o.controlledBy caster && (o.isCreature || o.printed.isArtifact))
  | .nonland =>
    g.legalPermanentTargets caster (fun o => o.isOnBattlefield && !o.printed.isLand)
  | .oppNonland =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && !o.printed.isLand &&
        (g.livingOpponents caster).any (fun pl => o.controlledBy pl.id))
  | .attackingCreatureWithoutFlying =>
    g.legalCreatureTargets caster (fun o => o.status.attacking && !g.hasFlying o)
  | .creatureYouControlSubtype subtype =>
    g.legalCreatureTargets caster (fun o => o.controlledBy caster && g.hasSubtype o subtype)
  | .spell =>
    g.legalStackSpellTargets (fun _ => true)
  | .creatureSpell =>
    g.legalStackSpellTargets (·.printed.isCreature)
  | .creatureSpellPTAtMost n =>
    g.legalStackSpellTargets (fun o =>
      o.printed.isCreature &&
        ((o.printed.power.getD 0) <= (n : Int) ||
          (o.printed.toughness.getD 0) <= (n : Int)))
  | .defendingPlayerCreature =>
    g.legalCreatureTargets caster (fun o =>
      o.controlledBy (g.opponent g.activePlayer))
  | .twoNonlandsSharingType => #[]
  | .creaturePowerAtLeast n =>
    g.legalCreatureTargets caster (fun o => g.power o >= n)
  | .creaturePowerAtMost n =>
    g.legalCreatureTargets caster (fun o => g.power o <= n)
  | .creatureYouControlAnySubtype subtypes =>
    g.legalCreatureTargets caster (fun o =>
      o.controlledBy caster && subtypes.any (g.hasSubtype o))
  | .permanent =>
    g.legalPermanentTargets caster (·.isOnBattlefield)
  | .creatureCardInYourGraveyard =>
    g.legalGraveyardCardTargets caster (·.printed.isCreature)
  | .legendaryCreatureYouControl =>
    g.legalCreatureTargets caster (fun o =>
      o.controlledBy caster && o.isLegendary)
  | .creatureYouControlPowerAtMost n =>
    g.legalCreatureTargets caster (fun o =>
      o.controlledBy caster && g.power o <= n)
  | .artifact =>
    g.legalPermanentTargets caster (fun o => o.isOnBattlefield && o.printed.isArtifact)
  | .artifactToken =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && o.printed.isArtifact && o.printed.isToken)
  | .attackingCreature =>
    g.legalCreatureTargets caster (fun o => o.status.attacking)
  | .equipmentYouControl =>
    g.legalPermanentTargets caster (fun o =>
      o.controlledBy caster && o.printed.isEquipment)
  | .creatureOrLandYouControl =>
    g.legalPermanentTargets caster (fun o =>
      o.controlledBy caster && (o.isCreature || o.printed.isLand))
  | .twoCreaturesOrLandsYouControl => #[]
  | .equipmentYouControlThenCreatureYouControl => #[]

/-- Legal targets for a targeting shape (CR 115.1 / 601.2c / 603.3d).
`sourceId` excludes the source of an “another” creature. Shapes with
multiple instances of the word “target” read `spec.slots` instead of
restating each slot. -/
def legalTargetsForKind (g : Game) (caster : PlayerId) (kind : EffectTargetKind)
    (sourceId : Option ObjectId := none) : Array Target :=
  if kind.spec.slots.isEmpty then
    g.legalTargetsForAtomicKind caster kind sourceId
  else
    let parts := kind.spec.slots.map (fun k => g.legalTargetsForAtomicKind caster k sourceId)
    if parts.any (·.isEmpty) then #[] else parts.foldl (· ++ ·) #[]

/-- Legal targets for a triggered ability (CR 603.3d / 601.2c). `sourceId` is
the object that generated the ability, used to exclude “another” creature. -/
def legalTriggerTargets (g : Game) (p : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId := none) : Array Target :=
  g.legalTargetsForKind p ab.targetKind sourceId

/-- Damage already assigned on a “divided as you choose” stack entry (CR 601.2d). -/
def assignedDividedDamage (e : StackEntry) : Nat :=
  e.dividedDamage.foldl (· + ·) 0

/-- Whether this stacked triggered ability still needs targets or a damage
division announced (CR 603.3d / 601.2d). -/
def triggerStillNeedsTargets (e : StackEntry) (ab : TriggeredAbility) : Bool :=
  match ab.dividedDamage? with
  | some (amount, _) => assignedDividedDamage e < amount
  | none =>
    if ab.allowsZeroTargets then !e.targetsAnnounced
    else ab.requiresTarget && e.targets.isEmpty

/-- Stack entry for a triggered ability that still needs targets announced
(CR 603.3d). Oldest first so targets are chosen in the order abilities were
put on the stack. -/
def triggerNeedingTargets (g : Game) : Option StackEntry :=
  g.stack.find? (fun e =>
    match g.findObject? e.objectId with
    | some o =>
      match o.triggeredAbility with
      | some ab => triggerStillNeedsTargets e ab
      | none => false
    | none => false)

/-- Put a triggered ability of `source` onto the stack (CR 603.3). -/
def putTriggeredAbilityOnStack (g : Game) (controller : PlayerId) (source : GameObject)
    (ab : TriggeredAbility) (event : String) (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none) : Game :=
  let (g, _) := g.putStackAbility source controller
    (triggeredAbility := some ab)
    (lastKnownPower := lastKnownPower) (lastKnownToughness := lastKnownToughness)
  g.logMsg s!"{source.name}'s {event} is put on the stack"

/-- True when this trigger would be put on the stack with no legal target (CR 603.3d). -/
def triggerHasNoLegalTarget (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : ObjectId) : Bool :=
  ab.requiresTarget && !ab.allowsZeroTargets &&
    (g.legalTriggerTargets controller ab (some sourceId)).isEmpty

/-- Put `ab` on the stack, or log that it is removed for lack of a target (CR 603.3d). -/
def putTriggerOrFizzle (g : Game) (controller : PlayerId) (source : GameObject)
    (ab : TriggeredAbility) (event : String)
    (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none) : Game :=
  if g.triggerHasNoLegalTarget controller ab source.id then
    g.logMsg
      s!"{source.name}'s {event} is removed from the stack (no legal target) (CR 603.3d)"
  else
    g.putTriggeredAbilityOnStack controller source ab event lastKnownPower lastKnownToughness

/-- True when any intervening trigger condition holds (e.g. Ferocious). -/
def triggerConditionHolds (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (cause : Option GameObject := none) : Bool :=
  let powerOk :=
    match ab.youControlCreatureWithPower? with
    | none => true
    | some n => g.greatestPowerAmongCreatures controller ≥ n
  let otherOk :=
    match ab.anotherCreaturePowerAtMost? with
    | none => true
    | some n =>
      match cause with
      | some o => g.power o ≤ n
      | none => true
  powerOk && otherOk

/-- Put `ab` on the stack for `event`, using that event's spec for the log label
and CR 603.3d check so a new event is not restated at every queue site. -/
def putQueuedTrigger (g : Game) (controller : PlayerId) (source : GameObject)
    (ab : TriggeredAbility) (event : TriggerEvent)
    (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none)
    (cause : Option GameObject := none) : Game :=
  if !g.triggerConditionHolds controller ab cause then g
  else if event.checkTargets then
    g.putTriggerOrFizzle controller source ab event.label lastKnownPower lastKnownToughness
  else
    g.putTriggeredAbilityOnStack controller source ab event.label
      lastKnownPower lastKnownToughness

/-- Append waiting-trigger snapshots. -/
def enqueueWaitingTriggers (g : Game) (wts : Array WaitingTrigger) : Game :=
  if wts.isEmpty then g else { g with waitingTriggers := g.waitingTriggers ++ wts }

/-- Queue `ab` until a player would receive priority (CR 603.3 / 603.4). The
intervening condition is checked when the event occurs. -/
def queueTrigger (g : Game) (controller : PlayerId) (source : GameObject)
    (ab : TriggeredAbility) (event : TriggerEvent)
    (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none)
    (cause : Option GameObject := none) : Game :=
  if !g.triggerConditionHolds controller ab cause then g
  else if ab.onceEachTurn && source.status.firedOnceEachTurn then g
  else
    let g :=
      if ab.onceEachTurn then
        match g.findObject? source.id with
        | some o => g.setObject { o with status := { o.status with firedOnceEachTurn := true } }
        | none => g
      else g
    g.enqueueWaitingTriggers #[{
      controller, source, ability := ab, event, lastKnownPower, lastKnownToughness }]

/-- Queue each printed trigger of `source` that fires on `event` (CR 603.3). -/
def putMatchingSourceTriggers (g : Game) (controller : PlayerId) (source : GameObject)
    (event : TriggerEvent)
    (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none)
    (cause : Option GameObject := none) : Game :=
  Id.run do
    let mut g := g
    for ab in source.matchingTriggers event do
      g := g.queueTrigger controller source ab event lastKnownPower lastKnownToughness cause
    return g

/-- Apply `f` to each battlefield permanent `p` controls, optionally skipping one id. -/
def foldControlledPermanents (g : Game) (p : PlayerId)
    (excludeId : Option ObjectId := none) (f : Game → GameObject → Game) : Game :=
  Id.run do
    let mut g := g
    for o in g.battlefield do
      if o.controlledBy p && excludeId != some o.id then
        g := f g o
    return g

/-- Put matching triggers of permanents `p` controls that fire on `event`. -/
def putControlledTriggers (g : Game) (p : PlayerId)
    (event : TriggerEvent) (excludeId : Option ObjectId := none) : Game :=
  g.foldControlledPermanents p excludeId fun g o =>
    g.putMatchingSourceTriggers p o event

/-- If a stacked triggered ability still needs targets, prompt its controller
(CR 603.3d / 601.2c). -/
def promptTriggerTargetsIfNeeded (g : Game) : Game :=
  match g.triggerNeedingTargets with
  | some e =>
    if g.pending == .chooseTargets e.controller then g
    else
      let msg :=
        match (g.findObject? e.objectId).bind (fun o =>
            o.triggeredAbility.bind TriggeredAbility.dividedDamage?) with
        | some (n, maxTargets) =>
          s!"{(g.player e.controller).name} must divide {n} damage among one to {maxTargets} targets (CR 603.3d / 601.2d)"
        | none =>
          s!"{(g.player e.controller).name} must choose a target (CR 603.3d / 601.2c)"
      { g with pending := .chooseTargets e.controller }.logMsg msg
  | none => g

/-- Triggers waiting to be put on the stack for `event`. -/
def waitingFor (g : Game) (event : TriggerEvent) : Array WaitingTrigger :=
  g.waitingTriggers.filter (·.event == event)

/-- One “whenever one or more other creatures die” trigger per source
(CR 603.2a / 603.3b). -/
def dedupWaitingTriggers (wts : Array WaitingTrigger) : Array WaitingTrigger :=
  wts.foldl (fun acc wt =>
    if wt.event == .oneOrMoreOtherCreaturesDie &&
        acc.any (fun w =>
          w.event == .oneOrMoreOtherCreaturesDie && w.source.id == wt.source.id) then
      acc
    else acc.push wt) #[]

/-- CR 603.3b: part 1 is every waiting trigger whose condition is not another
ability triggering; part 2 is the remainder. -/
def waitingTriggersPart (g : Game) (part2 : Bool) : Array WaitingTrigger :=
  g.waitingTriggers.filter (fun wt => wt.event.isAnotherAbilityTriggering == part2)
    |> dedupWaitingTriggers

/-- The current CR 603.3b batch: part 1 if any remain, otherwise part 2. -/
def currentTriggerBatch (g : Game) : Array WaitingTrigger :=
  let part1 := g.waitingTriggersPart false
  if !part1.isEmpty then part1 else g.waitingTriggersPart true

/-- This player's waiting triggers in the current CR 603.3b part. -/
def waitingTriggersOf (g : Game) (p : PlayerId) : Array WaitingTrigger :=
  g.currentTriggerBatch.filter (·.controller == p)

/-- Source ids of `p`'s current batch, oldest first (the default order). -/
def defaultTriggerSourceIds (g : Game) (p : PlayerId) : Array ObjectId :=
  (g.waitingTriggersOf p).map (·.source.id)

/-- Next player in APNAP order who has a waiting trigger in this part
(CR 603.3b / 101.4). -/
def nextTriggerStackingPlayer? (g : Game) : Option PlayerId :=
  let batch := g.currentTriggerBatch
  g.apnapPlayers.find? (fun p => batch.any (·.controller == p))

/-- Remove `wt` from the waiting list. A “one or more other creatures die”
trigger consumes every queued copy from the same source. -/
def removeWaitingTrigger (g : Game) (wt : WaitingTrigger) : Game :=
  if wt.event == .oneOrMoreOtherCreaturesDie then
    { g with waitingTriggers :=
      g.waitingTriggers.filter (fun w =>
        !(w.event == .oneOrMoreOtherCreaturesDie && w.source.id == wt.source.id)) }
  else
    match g.waitingTriggers.findIdx? (fun w =>
      w.controller == wt.controller && w.source.id == wt.source.id &&
        w.ability == wt.ability && w.event == wt.event) with
    | none => g
    | some i => { g with waitingTriggers := g.waitingTriggers.eraseIdx! i }

/-- Put these waiting triggers on the stack in the given order (CR 603.3 / 603.3d). -/
def putTriggerBatch (g : Game) (wts : Array WaitingTrigger) : Game :=
  if wts.isEmpty then g
  else
    Id.run do
      let mut g := g
      for wt in wts do
        g := g.removeWaitingTrigger wt
        g := g.putQueuedTrigger wt.controller wt.source wt.ability wt.event
          wt.lastKnownPower wt.lastKnownToughness
      return g.promptTriggerTargetsIfNeeded

/-- Put queued triggers for `event` onto the stack (CR 603.3). The event spec
decides the log label and whether to remove abilities that require a target
and have none (CR 603.3d). -/
def flushWaitingTriggers (g : Game) (event : TriggerEvent) : Game :=
  let waiting :=
    let raw := g.waitingFor event
    if event == .oneOrMoreOtherCreaturesDie then
      raw.foldl (fun acc wt =>
        if acc.any (fun w => w.source.id == wt.source.id) then acc else acc.push wt) #[]
    else raw
  if waiting.isEmpty then g
  else
    Id.run do
      let mut g := { g with waitingTriggers := g.waitingTriggers.filter (·.event != event) }
      for wt in waiting do
        g := g.putQueuedTrigger wt.controller wt.source wt.ability event
          wt.lastKnownPower wt.lastKnownToughness
      return g.promptTriggerTargetsIfNeeded

/-- CR 704.3 / 603.3b: check state-based actions, then put waiting triggers
on the stack in APNAP order (each player choosing the order of their own).
After that batch, check state-based actions again. Repeat until idle, then
`p` receives priority. `recheckSba` is false while still placing the current
batch (targets or the next player's triggers). -/
partial def receivePriority (g : Game) (p : PlayerId) (recheckSba := true) : Game :=
  let g := if recheckSba then g.checkSBA else g
  if g.over then g
  -- CR 704.3 / 704.5j: a required legend-rule choice is part of performing
  -- the SBA. Do not put triggers on the stack or grant priority yet.
  else if g.legendChoicePending? then g
  else if g.pending != .none then g
  else
    match g.nextTriggerStackingPlayer? with
    | none =>
      if g.waitingTriggers.isEmpty then
        if recheckSba then
          { g with priority := p, consecutivePasses := 0 }
        else
          -- Finished this CR 603.3b pass; check SBAs and any new triggers.
          receivePriority g p true
      else
        let g := g.putTriggerBatch g.currentTriggerBatch
        if g.over || g.pending != .none then g
        else receivePriority g p true
    | some q =>
      let mine := g.waitingTriggersOf q
      if mine.size ≤ 1 then
        let g := g.putTriggerBatch mine
        if g.over || g.pending != .none then g
        else receivePriority g p false
      else
        { g with pending := .chooseTriggerToStack q }.logMsg
          s!"{(g.player q).name} chooses the order of triggered abilities (CR 603.3b)"

/-- Put enters-the-battlefield triggers of `o` onto the stack (CR 603.6a).
Abilities that require a target and have none are removed (CR 603.3d). -/
def putEnterTriggersOnStack (g : Game) (o : GameObject) : Game :=
  match o.controller with
  | none => g
  | some p =>
    Id.run do
      let mut g := g
      g := g.putMatchingSourceTriggers p o .entering
      return g.promptTriggerTargetsIfNeeded

/-- Put controlled triggers for `event` onto the stack, then prompt for targets
if a trigger requires them (CR 603.3d). -/
def putControlledTriggersWithPrompt (g : Game) (p : PlayerId) (event : TriggerEvent)
    (excludeId : Option ObjectId := none) : Game :=
  g.putControlledTriggers p event excludeId |>.promptTriggerTargetsIfNeeded

/-- Put “whenever a land you control enters” triggers onto the stack (CR 603.6a).
Abilities that require a target and have none are removed (CR 603.3d). -/
def putLandYouControlEntersTriggers (g : Game) (land : GameObject) : Game :=
  if !land.printed.isLand then g
  else
    match land.controller with
    | none => g
    | some landController =>
      g.putControlledTriggersWithPrompt landController .landYouControlEnters

/-- Put “whenever you cast an instant or sorcery” triggers onto the stack
(CR 601.2i / 603.3). -/
def putCastTriggersOnStack (g : Game) (caster : PlayerId) (spell : GameObject) : Game :=
  let pl := g.player caster
  let spells := pl.spellsCastThisTurn + 1
  let nonc :=
    if spell.printed.isCreature then pl.noncreatureSpellsCastThisTurn
    else pl.noncreatureSpellsCastThisTurn + 1
  let g := g.modifyPlayer caster (fun p =>
    { p with spellsCastThisTurn := spells, noncreatureSpellsCastThisTurn := nonc })
  let g :=
    if spell.printed.isInstantOrSorcery then
      g.putControlledTriggers caster .youCastInstantOrSorcery
    else g
  let g :=
    if spell.printed.isCreature then g
    else g.putControlledTriggers caster .youCastNoncreature
  let g :=
    if spells == 2 then
      g.livingPlayers.foldl (fun acc pl =>
        acc.putControlledTriggers pl.id .anyPlayerCastsSecondSpell) g
    else g
  if !spell.printed.isCreature && nonc == 1 then
    (g.livingOpponents caster).foldl (fun acc pl =>
      acc.putControlledTriggers pl.id .opponentCastsFirstNoncreature) g
  else g

/-- Put “whenever another Elf you control enters” triggers onto the stack
(CR 603.6a). The entering permanent itself does not trigger. -/
def putAnotherElfYouControlEntersTriggers (g : Game) (entering : GameObject) : Game :=
  if !g.hasSubtype entering "Elf" then g
  else
    match entering.controller with
    | none => g
    | some p =>
      g.putControlledTriggersWithPrompt p .anotherElfYouControlEnters
        (excludeId := some entering.id)

/-- Put “whenever another creature you control enters” triggers (CR 603.6a). -/
def putAnotherCreatureYouControlEntersTriggers (g : Game) (entering : GameObject) : Game :=
  if !entering.isCreature then g
  else
    match entering.controller with
    | none => g
    | some p =>
      g.foldControlledPermanents p (excludeId := some entering.id) (fun g o =>
        g.putMatchingSourceTriggers p o .anotherCreatureYouControlEnters
          (cause := some entering))
      |>.promptTriggerTargetsIfNeeded

/-- After a permanent enters, put its enters triggers and “another … enters”
triggers (CR 603.6a). -/
def afterPermanentEnters (g : Game) (o : GameObject) : Game :=
  -- Storied is granted as the permanent enters, before SBA (legend rule /
  -- 0 toughness) and before enters triggers use the stack.
  let g := g.refreshEnduringStory
  let g :=
    if o.printed.entersWithHopePerCreature then
      match o.controller with
      | some p =>
        let n := (g.permanentsOf p).filter (·.isCreature) |>.size
        let g := g.setObject { o with status := { o.status with hope := n } }
        g.logMsg s!"{o.name} enters with {n} hope counter(s)"
      | none => g
    else g
  let o := g.object! o.id
  let g := g.putEnterTriggersOnStack o
  let g := g.putAnotherElfYouControlEntersTriggers (g.object! o.id)
  let g := g.putAnotherCreatureYouControlEntersTriggers (g.object! o.id)
  let g :=
    if o.printed.isToken then g
    else
      match o.controller with
      | none => g
      | some p =>
        g.putControlledTriggersWithPrompt p .thisOrNontokenSubtypeYouControlEnters
  match (g.object! o.id).controller with
  | some p =>
    if (g.object! o.id).printed.isArtifact then
      g.putControlledTriggersWithPrompt p .artifactYouControlEnters
    else g
  | none => g

/-- After a land enters, put its enters triggers, Elf-enters triggers, and landfall. -/
def afterLandEnters (g : Game) (land : GameObject) : Game :=
  let g := g.afterPermanentEnters land
  g.putLandYouControlEntersTriggers (g.object! land.id)

def playLand (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  if !g.canPlayLand p then
    throw "Can't play a land now (CR 116.2a / 305.3)"
  let some card := g.findObject? id | throw "no such object"
  if !g.mayPlay p card then
    throw (g.playZoneError p card)
  if !card.printed.isLand then
    throw s!"{card.name} is not a land"
  let (g, newId) := g.putOntoBattlefield id p
    (tapped := g.entersTapped p card.printed) (summoningSick := false)
  let g := g.modifyPlayer p (fun pl => { pl with landsPlayedThisTurn := pl.landsPlayedThisTurn + 1 })
  let g := g.logMsg s!"{(g.player p).name} plays {card.name}"
  -- Lands have no summoning sickness. `entersTapped` overrides CR 110.5b.
  let g := g.afterLandEnters (g.object! newId)
  if g.pending != .none then
    return g
  return g.receivePriority p

def manaSources (g : Game) (p : PlayerId) : Array (GameObject × Array ManaType) :=
  g.permanentsOf p |>.filterMap (fun o =>
    let types := o.printed.manaAbilities
    if types.isEmpty || o.status.tapped then none
    else if o.hasSummoningSickness then none
    else some (o, types))

/-- Permanents `p` currently controls with this subtype. -/
def countSubtype (g : Game) (p : PlayerId) (subtype : String) : Nat :=
  (g.permanentsOf p).filter (fun o => g.hasSubtype o subtype) |>.size

/-- Mana added by tapping `o` for `mana` (CR 106.4 / 605.3b). A
`tapAddManaForEach` ability counts permanents the controller currently
controls with the listed subtype. `tapAddAnyColorEqualToPower` adds this
creature's current power (CR 208.2). -/
def manaFromTap (g : Game) (o : GameObject) (mana : ManaType) : Nat :=
  if o.printed.tapAddAnyColorEqualToPower then
    match mana with
    | .colored _ => (g.power o).toNat
    | .colorless => 0
  else
    match o.printed.tapAddManaForEach.find? (fun a => a.mana == mana) with
    | some a =>
      match o.controller with
      | some p => g.countSubtype p a.subtype
      | none => 0
    | none => 1

/-- A player may activate mana abilities with priority, or while paying a
spell they are casting (CR 605.3a / 601.2g). -/
def canActivateManaAbility (g : Game) (p : PlayerId) : Bool :=
  if g.over then false
  else if g.hasPriority p then true
  else
    match g.pending with
    | .activateManaAbilities caster => caster == p
    | .mayPayGeneric q _ => q == p
    | .payOrLetCounter q _ _ => q == p
    | _ => false

def tapForMana (g : Game) (p : PlayerId) (id : ObjectId) (mana : ManaType) : Except String Game := do
  if !g.canActivateManaAbility p then
    throw "You can't activate a mana ability now (CR 605.3a)"
  let o := g.object! id
  if !o.controlledBy p || !o.isOnBattlefield then
    throw "You don't control that permanent"
  if o.status.tapped then
    throw s!"{o.name} is already tapped"
  if (match g.proposedSpell with
      | some prop => prop.tapSource && prop.sourceId == some id
      | none => false) then
    throw s!"{o.name} is needed to pay \{T}"
  if o.hasSummoningSickness then
    throw s!"{o.name} has summoning sickness (CR 302.6)"
  if !o.printed.manaAbilities.contains mana then
    throw s!"{o.name} cannot produce {mana}"
  let amount := g.manaFromTap o mana
  let elfRestricted := o.printed.tapAddAnyColorEqualToPower
  let instRestricted := o.printed.tapAddAnyColorForInstantOrSorcery
  let g := g.setObject { o with status := { o.status with tapped := true } }
  let g :=
    if o.printed.tapSacrificeAddAnyColor then
      let o := g.object! o.id
      g.moveToOwnerGraveyard o s!"{(g.player p).name} sacrifices {o.name}"
    else g
  let g := g.modifyPlayer p (fun pl =>
    { pl with manaPool :=
      ManaPool.add pl.manaPool mana amount elfRestricted instRestricted })
  let produced :=
    if amount == 1 then toString mana else s!"{mana} ×{amount}"
  let restrictNote :=
    if elfRestricted then " (Elf spells and abilities)"
    else if instRestricted then " (instant or sorcery spells)"
    else ""
  let g := g.logMsg s!"{g.player p |>.name} taps {o.name} for {produced}{restrictNote}"
  let g :=
    match g.proposedSpell with
    | some prop => { g with proposedSpell := some { prop with tapped := prop.tapped.push id } }
    | none => g
  -- Mana abilities don't use the stack (CR 605.3b).
  return { g with consecutivePasses := 0 }

/-- Mana in `p`'s pool plus mana from each of their untapped sources, skipping
`exclude` (used when that source's `{T}` is part of an activation cost).
Any-color power mana is counted as green Elf-restricted mana for the heuristic. -/
def availableManaExcept (g : Game) (p : PlayerId) (exclude : Option ObjectId) : ManaPool :=
  (g.manaSources p).foldl
    (fun pool (src, types) =>
      if exclude == some src.id then pool
      else if src.printed.tapAddAnyColorEqualToPower then
        let n := g.manaFromTap src (.colored .green)
        pool.add (.colored .green) n (elfRestricted := true)
      else if src.printed.tapAddAnyColorForInstantOrSorcery then
        pool.add (.colored .blue) 1 (instRestricted := true)
      else
        match types[0]? with
        | some t => pool.add t (g.manaFromTap src t)
        | none => pool)
    (g.player p).manaPool

/-- Mana in `p`'s pool plus mana from each of their untapped sources. Any-color
power mana is counted as green Elf-restricted mana for the heuristic. -/
def availableMana (g : Game) (p : PlayerId) : ManaPool :=
  g.availableManaExcept p none

def legalTargets (g : Game) (caster : PlayerId) (effect : SpellEffect) : Array Target :=
  g.legalTargetsForKind caster effect.targetKind

/-- Legal targets for an Aura spell with “Enchant creature” (CR 303.4). -/
def legalAuraTargets (g : Game) (caster : PlayerId) : Array Target :=
  g.legalTargetsForKind caster .creature

/-- Chosen mode of `o` if it is a modal spell on the stack (CR 700.2). -/
def chosenModeOf (g : Game) (o : GameObject) : Option Nat :=
  match g.stack.find? (fun e => e.objectId == o.id) with
  | some e => e.chosenMode
  | none => none

/-- Spell effect after a modal choice, if one has been announced (CR 700.2). -/
def spellEffectOf (o : GameObject) (chosenMode : Option Nat) : Option SpellEffect :=
  if o.printed.isModal then
    match chosenMode with
    | some i => o.printed.spellModes[i]?
    | none => none
  else
    o.printed.spellEffect

/-- Spell effect of `o` using the mode announced on the stack, if any (CR 700.2). -/
def currentSpellEffect (g : Game) (o : GameObject) : Option SpellEffect :=
  spellEffectOf o (g.chosenModeOf o)

/-- Legal targets for card face `c`, using `chosenMode` when a modal mode has
been announced (CR 115.1, 303.4, 601.2c). `none` on a modal card unions every
mode's targets (used when beginning to cast). -/
def legalTargetsForFace (g : Game) (p : PlayerId) (c : CardDef)
    (chosenMode : Option Nat := none) : Array Target :=
  if c.isModal && chosenMode.isNone then
    c.spellModes.foldl (fun acc e => acc ++ g.legalTargets p e) #[]
  else
    let effect :=
      if c.isModal then chosenMode.bind (fun i => c.spellModes[i]?)
      else c.spellEffect
    match effect with
    | some e => g.legalTargets p e
    | none => if c.isAura then g.legalAuraTargets p else #[]

/-- Legal targets for beginning to cast `o`, or for the chosen mode (CR 115.1, 303.4, 601.2c). -/
def legalSpellTargets (g : Game) (p : PlayerId) (o : GameObject) : Array Target :=
  g.legalTargetsForFace p o.printed (g.chosenModeOf o)

/-- Legal mode indices for a modal spell (CR 700.2d). -/
def legalModes (g : Game) (p : PlayerId) (o : GameObject) : Array Nat :=
  if !o.printed.isModal then #[]
  else
    Id.run do
      let mut acc : Array Nat := #[]
      for i in [0:o.printed.spellModes.size] do
        if !(g.legalTargets p o.printed.spellModes[i]!).isEmpty then
          acc := acc.push i
      return acc

/-- Default mode: a preferred mode if that mode is legal, else the first legal mode. -/
def defaultMode (g : Game) (p : PlayerId) (spell : GameObject) : Option Nat :=
  let legal := g.legalModes p spell
  let preferredIdx := legal.find? (fun i =>
    match spell.printed.spellModes[i]? with
    | some e => e.preferAsDefaultMode
    | none => false)
  match preferredIdx with
  | some i => some i
  | none => legal[0]?

/-- Legal targets for an activated-ability effect (CR 115.1 / 601.2c / 702.11b). -/
def legalAbilityTargets (g : Game) (p : PlayerId) (e : AbilityEffect) : Array Target :=
  g.legalTargetsForKind p e.targetKind

/-- The spell, activated ability, or triggered ability currently waiting for
targets (CR 601.2c / 603.3d). -/
def objectAwaitingTargets (g : Game) : Option GameObject :=
  match g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) with
  | some o => some o
  | none => g.triggerNeedingTargets.bind (fun e => g.findObject? e.objectId)

/-- True while announcing a “divided as you choose” damage trigger (CR 601.2d). -/
def announcingDividedDamage (g : Game) : Bool :=
  match g.objectAwaitingTargets with
  | some o => (o.triggeredAbility.bind TriggeredAbility.dividedDamage?).isSome
  | none => false

/-- The stack entry for `objectId`, if that object is on the stack. -/
def stackEntry? (g : Game) (objectId : ObjectId) : Option StackEntry :=
  g.stack.find? (fun e => e.objectId == objectId)

/-- Targeting shape of the object currently being announced. -/
def targetingOf (g : Game) (obj : GameObject) : EffectTargeting :=
  let fromObj : EffectTargeting :=
    match obj.abilityEffect with
    | some e => e.targeting
    | none =>
      match obj.triggeredAbility with
      | some ab => ab.targeting
      | none =>
        match g.currentSpellEffect obj with
        | some e => e.targeting
        | none =>
          if obj.printed.isAura then EffectTargeting.of .creature .own
          else EffectTargeting.of .none
  match g.proposedSpell with
  | some prop =>
    if prop.spellId == obj.id then
      match prop.targetKindOverride with
      | some k => EffectTargeting.of k
      | none => fromObj
    else fromObj
  | none => fromObj

/-- True when two permanents share a card type (CR 205.2). -/
def sharesCardType (a b : GameObject) : Bool :=
  a.types.any (fun t => b.types.contains t)

/-- Legal targets for the object currently being announced (spell or ability).
Already-chosen targets are excluded (CR 115.3). Multiple instances of the
word “target” offer the next unset slot from `EffectTargetKind.slotKind`.
Multiple targets of one instance are announced together. -/
def legalProposedTargets (g : Game) (p : PlayerId) (o : GameObject) : Array Target :=
  let already :=
    match g.stackEntry? o.id with
    | some e => e.targets
    | none => #[]
  let kind := (g.targetingOf o).kind
  let slot := kind.slotKind already.size
  let legal := (g.legalTargetsForKind p slot o.sourceId).filter (fun t => !already.contains t)
  if kind == .twoNonlandsSharingType then
    match already[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some first =>
        legal.filter (fun t =>
          match t with
          | Target.permanent oid =>
            match g.findObject? oid with
            | some other => sharesCardType first other
            | none => false
          | _ => false)
      | none => legal
    | _ => legal
  else legal

/-- Required and maximum announced targets for `obj` (CR 601.2c). Spells
such as Gaze in Wonder require one target and allow a second; every target
of that one instance of the word “target” is announced together. -/
def announcedTargetBounds (g : Game) (obj : GameObject) : Nat × Nat :=
  match g.currentSpellEffect obj with
  | some e =>
    let maxN := e.maxTargetCount
    if e.allowsZeroTargets then (0, maxN) else (e.targetCount, maxN)
  | none =>
    match obj.abilityEffect with
    | some e => (e.targetCount, e.targetCount)
    | none =>
      match obj.triggeredAbility with
      | some ab =>
        let n := ab.targeting.targetCount
        -- “Up to one” is min 0, max the printed count (usually 1).
        if ab.allowsZeroTargets then (0, n) else (n, n)
      | none => (1, 1)

/-- True when at least the required targets are announced and another
optional target may still be chosen. Unused for one-word variable counts
such as “one or two target creatures”, which are announced together. -/
def canFinishOptionalTargets (g : Game) (obj : GameObject) : Bool :=
  match g.stackEntry? obj.id with
  | none => false
  | some e =>
    if (g.targetingOf obj).kind.spec.slots.isEmpty then false
    else
      let (minN, maxN) := g.announcedTargetBounds obj
      e.targets.size >= minN && e.targets.size < maxN

/-- True while announcing several targets of one instance of the word “target”
that is not a damage division (e.g. “one or two target creatures”). -/
def announcingSameWordMultiTargets (g : Game) : Bool :=
  match g.objectAwaitingTargets with
  | some o =>
    (g.targetingOf o).kind.spec.slots.isEmpty &&
      (g.announcedTargetBounds o).2 > 1 &&
      !g.announcingDividedDamage
  | none => false

/-- Whether `e` currently has a legal target, or does not require one. -/
def modeIsChoosable (g : Game) (p : PlayerId) (e : AbilityEffect) : Bool :=
  !e.requiresTarget || !(g.legalAbilityTargets p e).isEmpty

/-- Whether this activated ability currently has a legal target, or does not
require one. Equip restricted to a creature subtype uses that targeting
shape rather than “any creature you control” (CR 702.6 / 601.2c). -/
def abilityCanChooseTarget (g : Game) (p : PlayerId) (ab : ActivatedAbility) : Bool :=
  match ab.equipSubtype with
  | some t => !(g.legalTargetsForKind p (.creatureYouControlSubtype t)).isEmpty
  | none => ab.allModes.any (g.modeIsChoosable p)

/-- Last target in `legal` matching `pred`. -/
def lastLegalTarget (legal : Array Target) (pred : Target → Bool) : Option Target :=
  legal.filter pred |>.back?

/-- Whether this target is a permanent `p` controls. -/
def isOwnPermanentTarget (g : Game) (p : PlayerId) : Target → Bool
  | .permanent oid => (g.findObject? oid).any (fun o => o.controlledBy p)
  | _ => false

/-- Whether this target is a permanent an opponent of `p` controls. -/
def isOppPermanentTarget (g : Game) (p : PlayerId) : Target → Bool
  | .permanent oid => (g.findObject? oid).any (fun o => o.controlledBy (g.opponent p))
  | _ => false

/-- Default choice among `legal` for this targeting shape (CR 601.2c). -/
def preferredTarget (g : Game) (p : PlayerId) (targeting : EffectTargeting)
    (legal : Array Target) : Option Target :=
  let own := lastLegalTarget legal (g.isOwnPermanentTarget p)
  let opp := lastLegalTarget legal (g.isOppPermanentTarget p)
  match targeting.prefer with
  | .own => own
  | .opponent => opp
  | .opponentPlayer =>
    let player := Target.player (g.opponent p)
    if legal.contains player then some player else legal[0]?
  | .last => legal.back?
  | .ownThenOpponent => own <|> opp
  | .selfPlayer =>
    let player := Target.player p
    if legal.contains player then some player else legal[0]?

/-- Default object or player to announce as a target (CR 601.2c). Damage spells
and divided-damage enters or attack triggers prefer the opponent; creature-damage abilities
and dies triggers prefer an opposing creature; destroy-flying prefers an opponent's flyer;
destroy-creature prefers an opposing creature;
destroy-colorless prefers an opposing colorless nonland; destroy-artifact-or-land prefers
an opposing artifact or land; Mirkwood Elk prefers an Elf
card in the controller's graveyard; Crude Bent Blade prefers an opposing player; Smite the Deathless prefers an opposing creature; Quarrel prefers a creature you control, then
an opposing creature; Rogue's Passage, pumps, the +1/+1-counter
mode, Equip, landfall, Galion's and Oliphaunt's attack triggers, and Auras prefer a creature the
caster controls. -/
def defaultTarget (g : Game) (p : PlayerId) (obj : GameObject) : Option Target :=
  let legal := g.legalProposedTargets p obj
  match g.preferredTarget p (g.targetingOf obj) legal with
  | some t => if legal.contains t then some t else legal[0]?
  | none => legal[0]?

/-- Default mode index for a modal activated ability (CR 601.2b). Prefers
dealing damage to an opposing creature, then destroying a colorless nonland. -/
def defaultAbilityMode (g : Game) (p : PlayerId) (modes : Array AbilityEffect) : Option Nat :=
  let choosable : Array (Nat × AbilityEffect) :=
    Id.run do
      let mut acc : Array (Nat × AbilityEffect) := #[]
      for i in [0:modes.size] do
        let e := modes[i]!
        if g.modeIsChoosable p e then
          acc := acc.push (i, e)
      return acc
  let findKind (pred : AbilityEffect → Bool) : Option Nat :=
    (choosable.find? (fun (_, e) => pred e)).map (·.1)
  let damageIdx :=
    findKind (fun e => e.castKind == .creatureDamage)
  let destroyIdx :=
    findKind (fun e => e.castKind == .destroyColorless)
  let oppHasCreature :=
    (g.permanentsOf (g.opponent p)).any (·.isCreature)
  let hasColorless := g.battlefield.any (·.isColorlessNonland)
  if oppHasCreature then
    damageIdx <|> destroyIdx <|> choosable[0]?.map (·.1)
  else if hasColorless then
    destroyIdx <|> damageIdx <|> choosable[0]?.map (·.1)
  else
    choosable[0]?.map (·.1)

def targetLogName (g : Game) : Target → String
  | .player pid => (g.player pid).name
  | .permanent oid | .card oid =>
    match g.findObject? oid with
    | some o => o.name
    | none => toString oid

/-- Timing check shared by beginning to cast a spell or an Adventure (CR 601.3). -/
def timingAllowsCast (g : Game) (p : PlayerId) (face : CardDef) : Bool :=
  let hasConditionalFlash :=
    match face.flashIfYouControlSubtype with
    | some t => g.controlsAnySubtype p #[t]
    | none => false
  g.hasPriority p &&
  (if face.hasSorcerySpeed && !hasConditionalFlash then g.asSorcery? p else true)

/-- Whether `p` may begin to cast `o` (CR 601.3). Having enough mana in the
pool is not required; mana abilities are activated at CR 601.2g. Additional
non-mana costs such as sacrificing a permanent must still be payable. -/
def canCast (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  !o.printed.isLand &&
  g.mayPlay p o &&
  g.timingAllowsCast p o.printed &&
  (if o.printed.additionalCostSacrificeArtifactOrCreature &&
      o.printed.additionalCostOrPayGeneric.isNone then
    (g.permanentsOf p).any (fun perm =>
      perm.id != o.id && (perm.isCreature || perm.printed.isArtifact))
   else true) &&
  -- Untargeted permanents, and untargeted instants/sorceries with a modeled
  -- effect (e.g. Night's Whisper), may be proposed (CR 601.3).
  if o.printed.requiresTarget then
    o.printed.allowsZeroTargets || !(g.legalSpellTargets p o |>.isEmpty)
  else o.printed.isPermanentCard || o.printed.spellEffect.isSome || o.printed.isModal

/-- True when the CR 715.3d exile permission forbids recasting as an Adventure. -/
def adventureExileForbidsRecast (_g : Game) (o : GameObject) : Bool :=
  match o.playPermission with
  | some perm => perm.fromAdventure
  | none => false

/-- Legal targets for beginning to cast card `c` (from hand or as an Adventure). -/
def legalCastTargets (g : Game) (p : PlayerId) (c : CardDef) : Array Target :=
  g.legalTargetsForFace p c none

/-- Whether `p` may begin to cast `o` as an Adventure (CR 715.3). -/
def canCastAdventure (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  match o.printed.adventure with
  | none => false
  | some adv =>
    let face := adv.toCardDef
    !g.adventureExileForbidsRecast o &&
    g.mayPlay p o &&
    g.timingAllowsCast p face &&
    if face.requiresTarget then !(g.legalCastTargets p face).isEmpty
    else true

/-- Whether paying this proposed spell or ability may spend Elf-restricted mana
(CR 106.10): Elf spells, and activated abilities of Elf sources. -/
def proposedAllowsElfRestricted (g : Game) (prop : ProposedSpell) : Bool :=
  match prop.kind with
  | .spell =>
    match g.findObject? prop.spellId with
    | some o => g.hasSubtype o "Elf"
    | none => false
  | .activatedAbility =>
    match prop.sourceId.bind g.findObject? with
    | some src => g.hasSubtype src "Elf"
    | none => g.hasSubtype prop.original "Elf"

/-- Whether paying this proposed spell may spend instant/sorcery-restricted mana. -/
def proposedAllowsInstRestricted (g : Game) (prop : ProposedSpell) : Bool :=
  match prop.kind with
  | .spell =>
    match g.findObject? prop.spellId with
    | some o => o.printed.isInstantOrSorcery
    | none => false
  | .activatedAbility => false

/-- Untapped mana sources `p` may activate while paying `prop` (CR 601.2g).
Sources reserved for `{T}`, or whose mana cannot be spent on this spell or
ability, are omitted. -/
def manaSourcesForProposed (g : Game) (p : PlayerId) (prop : ProposedSpell) :
    Array (GameObject × Array ManaType) :=
  let allowElf := g.proposedAllowsElfRestricted prop
  let allowInst := g.proposedAllowsInstRestricted prop
  (g.manaSources p).filter (fun (src, types) =>
    !(prop.tapSource && prop.sourceId == some src.id) &&
    !(src.printed.tapAddAnyColorEqualToPower && !allowElf) &&
    !(src.printed.tapAddAnyColorForInstantOrSorcery && !allowInst) &&
    !types.isEmpty)

/-- A mana type among `types` that helps pay an unmet colored requirement. -/
def preferredManaType (g : Game) (p : PlayerId) (types : Array ManaType)
    (cost : ManaCost) (allowElfRestricted : Bool) : Option ManaType :=
  match types[0]? with
  | none => none
  | some first =>
    let pool := (g.player p).manaPool
    match Color.all.find? (fun c =>
      let req := cost.coloredCount c
      let held :=
        if allowElfRestricted then pool.get (.colored c)
        else pool.unrestricted (.colored c)
      held < req && types.contains (.colored c)) with
    | some c => some (.colored c)
    | none => some first

def payCost (g : Game) (p : PlayerId) (cost : ManaCost)
    (allowElfRestricted : Bool := false) (allowInstRestricted : Bool := false) :
    Except String Game := do
  let pl := g.player p
  match pl.manaPool.pay? cost allowElfRestricted allowInstRestricted with
  | none => throw s!"{pl.name} cannot pay {cost}"
  | some pool =>
    return g.setPlayer { pl with manaPool := pool }

/-- Undo a proposed spell or ability that could not be paid (CR 601.2 / 602.2 / 733.1). -/
def reverseProposedSpell (g : Game) : Game :=
  match g.proposedSpell with
  | none => g
  | some prop =>
    Id.run do
      let mut g := g
      let name := (g.player prop.caster).name
      let objects := g.objects.filter (fun o => o.id != prop.spellId)
      let objects :=
        match prop.kind with
        | .spell => objects.push prop.original
        | .activatedAbility => objects
      g := { g with
        objects := objects
        stack := prop.stackBefore
        pending := .none
        proposedSpell := none }
      g := g.modifyPlayer prop.caster (fun pl =>
        { pl with hand := prop.handBefore, manaPool := prop.manaBefore })
      for id in prop.tapped do
        if let some o := g.findObject? id then
          g := g.setObject { o with status := { o.status with tapped := false } }
      let reversed :=
        match prop.kind with
        | .spell => "the casting is reversed (CR 601.2 / 733.1)"
        | .activatedAbility => "the activation is reversed (CR 602.2 / 733.1)"
      g := g.logMsg s!"{name} cannot pay {prop.cost}; {reversed}"
      -- The player who had priority retains it (CR 733.2).
      return { g with priority := prop.caster, consecutivePasses := 0 }

def becomeCast (g : Game) (p : PlayerId) (spell : GameObject) : Game :=
  let g := g.logMsg s!"{(g.player p).name} casts {spell.name}"
  let g := g.putCastTriggersOnStack p spell
  g.receivePriority p

/-- After targets are announced, reduce the locked-in cost if the spell cares
about a damaged, tapped, or attacking nontoken target (CR 601.2f). -/
def lockInTargetCostReduction (g : Game) : Game :=
  match g.proposedSpell with
  | none => g
  | some prop =>
    match g.findObject? prop.spellId with
    | none => g
    | some spell =>
      let face :=
        match spell.adventurerCard with
        | some _ => spell.printed
        | none => spell.printed
      match (g.stackEntry? spell.id).bind (fun e => e.targets[0]?) with
      | some (Target.permanent oid) =>
        match g.findObject? oid with
        | some o =>
          let nDamaged :=
            if face.costReductionIfTargetDamaged > 0 && o.status.damage > 0 then
              face.costReductionIfTargetDamaged
            else 0
          let nTapped :=
            if face.costReductionIfTargetTapped > 0 && o.status.tapped then
              face.costReductionIfTargetTapped
            else 0
          let nAttacking :=
            if face.costReductionIfTargetAttackingNontoken > 0 && o.status.attacking then
              face.costReductionIfTargetAttackingNontoken
            else 0
          let n := nDamaged + nTapped + nAttacking
          if n == 0 then g
          else
            { g with proposedSpell := some { prop with
              cost := ManaCost.afterReduction prop.cost (prop.cost.reduceGeneric n) } }
        | none => g
      | _ => g

/-- Continue after CR 601.2c: determine the total cost (601.2f), then mana
abilities (601.2g). Additional-cost *choices* are announced earlier, at 601.2b. -/
def afterTargetsChosen (g : Game) : Game :=
  match g.proposedSpell with
  | none => g
  | some _ =>
    let g := g.lockInTargetCostReduction
    match g.proposedSpell with
    | none => g
    | some prop =>
      if prop.cost.includesManaPayment || prop.needsSacrificeOther then
        { g with pending := .activateManaAbilities prop.caster }
          |>.logMsg s!"{(g.player prop.caster).name} may activate mana abilities (CR 601.2g)"
      else
        let spell := g.object! prop.spellId
        let g := { g with pending := .none, proposedSpell := none, consecutivePasses := 0 }
        g.becomeCast prop.caster spell

/-- Whether the proposed spell or ability still needs targets announced (CR 601.2c). -/
def proposedNeedsTarget (g : Game) (prop : ProposedSpell) : Bool :=
  match g.findObject? prop.spellId with
  | none => false
  | some o =>
    match prop.kind with
    | .spell =>
      match g.currentSpellEffect o with
      | some e => e.requiresTarget
      | none => o.printed.requiresTarget || o.printed.isAura
    | .activatedAbility =>
      match o.abilityEffect with
      | some e => e.requiresTarget
      | none => false

/-- After CR 601.2b additional-cost announcement, continue to targets (601.2c)
or cost determination (601.2f). -/
def afterAdditionalCostAnnounced (g : Game) : Game :=
  match g.proposedSpell with
  | none => g
  | some prop =>
    if g.proposedNeedsTarget prop then
      { g with pending := .chooseTargets prop.caster }
        |>.logMsg s!"{(g.player prop.caster).name} must choose a target (CR 601.2c)"
    else
      g.afterTargetsChosen

/-- Write `targets` (and optional damage division) onto the stack entry. -/
def setStackEntryTargets (g : Game) (objectId : ObjectId) (targets : Array Target)
    (dividedDamage : Array Nat := #[]) : Game :=
  match g.stack.findIdx? (fun e => e.objectId == objectId) with
  | none => g
  | some i =>
    { g with stack := g.stack.set! i { g.stack[i]! with
        targets := targets, dividedDamage := dividedDamage, targetsAnnounced := true } }

/-- Write `targets` onto the stack entry for the proposed spell. -/
def setProposedTargets (g : Game) (targets : Array Target) : Game :=
  match g.proposedSpell with
  | none => g
  | some prop => g.setStackEntryTargets prop.spellId targets

/-- Record the chosen mode on the proposed spell's stack entry (CR 700.2). -/
def setProposedMode (g : Game) (mode : Nat) : Game :=
  match g.proposedSpell with
  | none => g
  | some prop =>
    match g.stack.findIdx? (fun e => e.objectId == prop.spellId) with
    | none => g
    | some i =>
      { g with stack := g.stack.set! i { g.stack[i]! with chosenMode := some mode } }

def becomeActivated (g : Game) (p : PlayerId) (sourceName : String)
    (sourceId : Option ObjectId := none) : Game :=
  let g :=
    match sourceId with
    | none => g
    | some sid =>
      match g.findObject? sid with
      | some src =>
        g.setObject { src with status := { src.status with
          activationsThisTurn := src.status.activationsThisTurn + 1 } }
      | none => g
  g.logMsg s!"{(g.player p).name} activates {sourceName}" |>.receivePriority p

/-- Permanents `p` may sacrifice to pay “sacrifice another creature or artifact”. -/
def sacrificeCreatureOrArtifactChoices (g : Game) (p : PlayerId) (sourceId : ObjectId) :
    Array GameObject :=
  g.permanentsOf p |>.filter (fun o =>
    o.id != sourceId && (o.isCreature || o.printed.isArtifact))

/-- Creatures `p` may sacrifice to a “sacrifices a creature of their choice” effect. -/
def sacrificeCreatureChoices (g : Game) (p : PlayerId) : Array GameObject :=
  g.permanentsOf p |>.filter (·.isCreature)

/-- Whether `sac` is a legal “another creature or artifact” sacrifice for `sourceId`. -/
def canSacrificeAsCreatureOrArtifact (g : Game) (p : PlayerId) (sourceId : ObjectId)
    (sac : GameObject) : Bool :=
  (g.sacrificeCreatureOrArtifactChoices p sourceId).any (·.id == sac.id)

/-- Whether `sac` is a legal creature for `p` to sacrifice to an edict. -/
def canSacrificeCreature (g : Game) (p : PlayerId) (sac : GameObject) : Bool :=
  (g.sacrificeCreatureChoices p).any (·.id == sac.id)

/-- Whether the source of a proposed activated ability can still pay tap/sacrifice/discard. -/
def sourceStillPayable (g : Game) (prop : ProposedSpell) : Bool :=
  match prop.sourceId with
  | none => true
  | some sid =>
    match g.findObject? sid with
    | none => false
    | some src =>
      (src.isOnBattlefield && src.controlledBy prop.caster &&
        (!prop.tapSource || !src.status.tapped) && !prop.discardSource) ||
      (src.zone == .graveyard src.owner && src.owner == prop.caster &&
        !prop.tapSource && !prop.sacrificeSource && !prop.discardSource) ||
      (src.zone == .hand src.owner && src.owner == prop.caster &&
        prop.discardSource && !prop.tapSource && !prop.sacrificeSource)

/-- Whether `p` can pay `n` life (CR 119.4). Paying 0 life is always legal. -/
def canPayLife (g : Game) (p : PlayerId) (n : Nat) : Bool :=
  n == 0 || (g.player p).life ≥ (n : Int)

/-- Pay `n` life as a cost (CR 118.3b / 119.4). Payment of life is not damage. -/
def payLifeCost (g : Game) (p : PlayerId) (n : Nat) : Except String Game := do
  if n == 0 then
    return g
  let pl := g.player p
  if pl.life < (n : Int) then
    throw s!"{pl.name} cannot pay {n} life"
  return g.setLife p (pl.life - (n : Int))
    s!"{pl.name} pays {n} life ({pl.life - (n : Int)} life)"

/-- Pay `{T}`, life, discard, and/or sacrifice the source as part of an activation cost
(CR 601.2h / 118.3b / 702.29). -/
def payActivationExtraCosts (g : Game) (p : PlayerId) (sourceId : ObjectId)
    (tapSource sacrificeSource : Bool) (payLife : Nat := 0)
    (discardSource : Bool := false) : Except String Game := do
  let some src := g.findObject? sourceId | throw "The source is no longer in play"
  if discardSource then
    if !(src.zone == .hand src.owner && src.owner == p) then
      throw s!"{src.name} is not in your hand"
    let g ← g.payLifeCost p payLife
    let src := g.object! sourceId
    let g := g.logMsg s!"{(g.player p).name} discards {src.name}"
    let (g, _) := g.move sourceId (.graveyard src.owner) none
    return g
  let fromGraveyard := src.zone == .graveyard src.owner && src.owner == p
  if fromGraveyard && !tapSource && !sacrificeSource then
    return (← g.payLifeCost p payLife)
  if !src.isOnBattlefield then
    throw "The source is no longer on the battlefield"
  if !src.controlledBy p then
    throw "You don't control that permanent"
  let mut g := g
  if tapSource then
    let src := g.object! sourceId
    if src.status.tapped then
      throw s!"{src.name} is already tapped"
    g := g.setObject { src with status := { src.status with tapped := true } }
  g := (← g.payLifeCost p payLife)
  if sacrificeSource then
    let src := g.object! sourceId
    g := g.logMsg s!"{(g.player p).name} sacrifices {src.name}"
    let (g', _) := g.move sourceId (.graveyard src.owner) none
    g := g'
  return g

/-- Pay the locked-in cost (CR 601.2h / 602.2b). Spells and abilities that still
need an artifact or creature sacrificed wait for the `sacrifice` action. -/
def finishProposedSpell (g : Game) : Except String Game := do
  let some prop := g.proposedSpell | throw "No spell or ability is waiting to be paid for"
  let allowElf := g.proposedAllowsElfRestricted prop
  let allowInst := g.proposedAllowsInstRestricted prop
  if !(g.player prop.caster).manaPool.canPay prop.cost allowElf allowInst ||
      !g.sourceStillPayable prop ||
      !g.canPayLife prop.caster prop.payLife then
    return g.reverseProposedSpell
  if prop.needsSacrificeOther then
    let excludeId := prop.sourceId.getD prop.spellId
    if (g.sacrificeCreatureOrArtifactChoices prop.caster excludeId).isEmpty then
      return g.reverseProposedSpell
  let g ← g.payCost prop.caster prop.cost allowElf allowInst
  let g ←
    match prop.kind, prop.sourceId with
    | .activatedAbility, some sid =>
      g.payActivationExtraCosts prop.caster sid prop.tapSource prop.sacrificeSource
        prop.payLife prop.discardSource
    | _, _ => pure g
  match prop.kind, prop.needsSacrificeOther, prop.sourceId with
  | .spell, true, _ =>
    let g := { g with
      pending := .sacrificePermanent prop.caster prop.spellId
      consecutivePasses := 0 }
    return g.logMsg
      s!"{(g.player prop.caster).name} must sacrifice an artifact or creature"
  | .spell, _, _ =>
    let g := { g with pending := .none, proposedSpell := none, consecutivePasses := 0 }
    return g.becomeCast prop.caster (g.object! prop.spellId)
  | .activatedAbility, true, some sid =>
    let g := { g with
      pending := .sacrificePermanent prop.caster sid
      consecutivePasses := 0 }
    return g.logMsg
      s!"{(g.player prop.caster).name} must sacrifice another creature or artifact"
  | .activatedAbility, _, _ =>
    let g := { g with pending := .none, proposedSpell := none, consecutivePasses := 0 }
    return g.becomeActivated prop.caster prop.original.name prop.sourceId

/-- Mana to pay for `face` after alternative costs and pre-target reductions
(CR 118.7 / 601.2f). `withoutManaCost` and a reduction that removes every
mana symbol become `{0}`, not an unpayable empty cost (CR 107.4d / 202.1b).
Target-based reductions lock in after CR 601.2c. -/
def playManaCost (g : Game) (card : GameObject) (face : CardDef) : ManaCost :=
  let printedCost :=
    if card.castFromGraveyard || card.zone == .graveyard card.owner then
      face.flashback.getD face.manaCost
    else if face.costReductionIfCreatureDied > 0 && g.creatureDiedThisTurn then
      face.manaCost.reduceGeneric face.costReductionIfCreatureDied
    else if face.costReductionEqualFlyingPower then
      let n :=
        match card.controller with
        | none => 0
        | some p =>
          (g.permanentsOf p).foldl (fun acc o =>
            if o.isCreature && g.hasFlying o then acc + (g.power o).toNat else acc) 0
      face.manaCost.reduceGeneric n
    else face.manaCost
  let cost :=
    match card.playPermission with
    | some perm =>
      if perm.withoutManaCost then ManaCost.zero
      else if perm.anyMana then ManaCost.ofGeneric printedCost.manaValue
      else printedCost
    | none => printedCost
  ManaCost.afterReduction face.manaCost cost

/-- True when `face` has a mana cost that would not be paid to play `card`. -/
def playsWithoutPayingManaCost (g : Game) (card : GameObject)
    (face : CardDef := card.printed) : Bool :=
  face.manaCost.includesManaPayment && !(g.playManaCost card face).includesManaPayment

/-- Mana to activate `ab` after applicable reductions (CR 118.7 / 602.2b).
A reduction that removes every mana symbol becomes `{0}`. -/
def activationManaCost (g : Game) (p : PlayerId) (ab : ActivatedAbility) : ManaCost :=
  let cost :=
    if ab.costReductionIfYouControlLegendary > 0 && g.controlsLegendaryCreature p then
      ab.cost.mana.reduceGeneric ab.costReductionIfYouControlLegendary
    else if ab.costReductionPerEquipment > 0 then
      let n := (g.permanentsOf p).filter (fun o => o.printed.isEquipment) |>.size
      ab.cost.mana.reduceGeneric (ab.costReductionPerEquipment * n)
    else ab.cost.mana
  ManaCost.afterReduction ab.cost.mana cost

/-- True when `ab` has a mana cost that `p` would not pay to activate it. -/
def activatesWithoutPayingManaCost (g : Game) (p : PlayerId) (ab : ActivatedAbility) :
    Bool :=
  ab.cost.mana.includesManaPayment && !(g.activationManaCost p ab).includesManaPayment

/-- After proposing a spell or activated ability, announce modes and additional
costs (CR 601.2b), then targets (CR 601.2c), then mana abilities (CR 601.2g). -/
def enterProposalWindow (g : Game) (p : PlayerId) (pl : Player) (prop : ProposedSpell)
    (needsMode needsTarget : Bool) (modeCitation : String)
    (needsAdditionalCost : Bool := false) : Game :=
  if needsMode then
    let g := { g with pending := .chooseMode p, proposedSpell := some prop }
    g.logMsg s!"{pl.name} must choose a mode ({modeCitation})"
  else if needsAdditionalCost then
    let g := { g with pending := .chooseAdditionalCost p, proposedSpell := some prop }
    g.logMsg s!"{pl.name} must choose an additional cost (CR 601.2b)"
  else if needsTarget then
    let g := { g with pending := .chooseTargets p, proposedSpell := some prop }
    g.logMsg s!"{pl.name} must choose a target (CR 601.2c)"
  else
    let g := { g with pending := .activateManaAbilities p, proposedSpell := some prop }
    g.logMsg s!"{pl.name} may activate mana abilities (CR 601.2g)"

def castSpell (g : Game) (p : PlayerId) (id : ObjectId) (asAdventure : Bool := false) :
    Except String Game := do
  if !g.hasPriority p then
    throw "You don't have priority"
  let some card := g.findObject? id | throw "no such object"
  if !g.mayPlay p card then
    throw (g.playZoneError p card)
  if asAdventure then
    if card.printed.adventure.isNone then
      throw s!"{card.name} has no Adventure"
    if g.adventureExileForbidsRecast card then
      throw "You may not cast that card as an Adventure this way (CR 715.3d)"
  let face :=
    match asAdventure, card.printed.adventure with
    | true, some adv => adv.toCardDef
    | _, _ => card.printed
  let pl := g.player p
  if face.isLand then
    throw "Lands are played, not cast (CR 305)"
  if face.hasSorcerySpeed && !g.asSorcery? p then
    throw s!"{face.name} has sorcery speed"
  if (face.requiresTarget || face.isModal) &&
      (g.legalCastTargets p face).isEmpty && !face.allowsZeroTargets then
    throw s!"{face.name} requires a target"
  if face.additionalCostSacrificeArtifactOrCreature &&
      face.additionalCostOrPayGeneric.isNone &&
      (g.sacrificeCreatureOrArtifactChoices p id).isEmpty then
    throw s!"{face.name} requires sacrificing an artifact or creature"
  -- CR 601.2a: propose the spell by moving it onto the stack. Modes and
  -- additional costs are announced at CR 601.2b, targets at CR 601.2c; mana
  -- is not required yet (CR 601.2g). CR 715.3: an adventurer card may be
  -- cast as its Adventure.
  let cost := g.playManaCost card face
  let fromGraveyard := card.zone == .graveyard card.owner
  let needsSacrifice :=
    face.additionalCostSacrificeArtifactOrCreature &&
      face.additionalCostOrPayGeneric.isNone
  let original := card
  let handBefore := pl.hand
  let stackBefore := g.stack
  let manaBefore := pl.manaPool
  let (g, newId) := g.move id .stack (some p)
  let g :=
    if asAdventure then
      let o := g.object! newId
      g.setObject { o with printed := face, adventurerCard := some original.printed }
    else g
  let g :=
    if fromGraveyard then
      let o := g.object! newId
      g.setObject { o with castFromGraveyard := true }
    else g
  let g := g.putStackEntry p newId
  let needsMode := face.isModal
  let needsTarget := face.requiresTarget && !needsMode
  let needsAdditionalCostChoice := face.additionalCostOrPayGeneric.isSome
  if !needsMode && !needsTarget && !cost.includesManaPayment && !needsSacrifice &&
      !needsAdditionalCostChoice then
    return g.becomeCast p (g.object! newId)
  let prop : ProposedSpell := {
    caster := p
    cost := cost
    spellId := newId
    original := original
    handBefore := handBefore
    stackBefore := stackBefore
    manaBefore := manaBefore
    needsSacrificeOther := needsSacrifice
  }
  let g := g.logMsg s!"{pl.name} begins casting {face.name}"
  return g.enterProposalWindow p pl prop needsMode needsTarget "CR 601.2b / 700.2"
    (needsAdditionalCost := needsAdditionalCostChoice)

/-- Announce the chosen mode for a modal spell or activated ability
(CR 601.2b / 700.2). -/
def announceMode (g : Game) (p : PlayerId) (mode : Nat) : Except String Game := do
  match g.pending with
  | .chooseMode caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may choose a mode (CR 601.2b)"
    let some prop := g.proposedSpell
      | throw "No spell or ability is waiting for a mode (CR 601.2b)"
    match prop.kind with
    | .activatedAbility =>
      let some chosen := prop.abilityModes[mode]?
        | throw "No such mode (CR 601.2b)"
      if !g.modeIsChoosable p chosen then
        throw "That mode requires a target (CR 700.2d)"
      let some obj := g.findObject? prop.spellId | throw "The ability left the stack"
      let g := g.setObject { obj with abilityEffect := some chosen }
      let g := g.logMsg
        s!"{(g.player p).name} chooses a mode: {chosen.toNotation} (CR 601.2b)"
      if chosen.requiresTarget then
        let g := { g with pending := .chooseTargets p }
        return g.logMsg s!"{(g.player p).name} must choose a target (CR 601.2c)"
      return g.afterTargetsChosen
    | .spell =>
      let some spell := g.findObject? prop.spellId | throw "The spell left the stack"
      if !spell.printed.isModal then
        throw "That spell is not modal (CR 700.2)"
      let some effect := spell.printed.spellModes[mode]? | throw "No such mode (CR 700.2)"
      if (g.legalTargets p effect).isEmpty then
        throw "That mode has no legal target (CR 700.2d)"
      let g := g.setProposedMode mode
      let g := g.logMsg
        s!"{(g.player p).name} chooses mode {mode + 1} ({effect.toNotation}) (CR 601.2b)"
      if spell.printed.additionalCostOrPayGeneric.isSome then
        let g := { g with pending := .chooseAdditionalCost p }
        return g.logMsg s!"{(g.player p).name} must choose an additional cost (CR 601.2b)"
      if effect.requiresTarget then
        let g := { g with pending := .chooseTargets p }
        return g.logMsg s!"{(g.player p).name} must choose a target (CR 601.2c)"
      return g.afterTargetsChosen
  | _ => throw "Not time to choose a mode (CR 601.2b)"

/-- After a trigger's targets (and any damage division) are fully announced,
prompt the next trigger that needs targets or continue the CR 603.3b
process (remaining waiting triggers, then SBAs). -/
def afterTriggerTargetsChosen (g : Game) : Game :=
  match g.triggerNeedingTargets with
  | some _ =>
    promptTriggerTargetsIfNeeded { g with pending := .none }
  | none =>
    receivePriority { g with pending := .none } g.activePlayer false

/-- Announce targets for the current instance of the word “target”
(CR 601.2c / 603.3d). Multiple targets of one instance (including a
“divided as you choose” division, CR 601.2d) are chosen together. Each
further instance is a later announcement. An omitted amount on a
divided-damage ability assigns all remaining damage to that one target. -/
def announceTargetChoices (g : Game) (p : PlayerId)
    (choices : Array (Target × Option Nat)) : Except String Game := do
  match g.pending with
  | .chooseTargets caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may choose targets (CR 601.2c)"
    let some obj := g.objectAwaitingTargets | throw "No spell is waiting for a target (CR 601.2c)"
    if choices.isEmpty then
      throw "Choose a target (CR 601.2c)"
    match obj.triggeredAbility.bind TriggeredAbility.dividedDamage? with
    | some (total, maxTargets) =>
      let some e := g.stackEntry? obj.id | throw "The ability left the stack"
      if !e.targets.isEmpty || assignedDividedDamage e != 0 then
        throw "Those targets must be chosen at the same time (CR 601.2c)"
      if total == 0 then
        throw "All damage has already been divided (CR 601.2d)"
      let assignments : Array (Target × Nat) ←
        if choices.size == 1 && choices[0]!.2.isNone then
          pure #[(choices[0]!.1, total)]
        else if choices.any (fun c => c.2.isNone) then
          throw "Each target must be assigned a damage amount (CR 601.2d)"
        else
          pure (choices.map (fun c => (c.1, c.2.getD 0)))
      if assignments.size > maxTargets then
        throw s!"Cannot choose more than {maxTargets} targets (CR 601.2d)"
      let legal := g.legalProposedTargets p obj
      let mut assigned : Nat := 0
      let mut targets : Array Target := #[]
      let mut amounts : Array Nat := #[]
      for (t, n) in assignments do
        if !legal.contains t then
          throw "Illegal target (CR 601.2c)"
        if targets.contains t then
          throw "Illegal target (CR 601.2c)"
        if n == 0 then
          throw "Each target must be dealt at least 1 damage (CR 601.2d)"
        assigned := assigned + n
        targets := targets.push t
        amounts := amounts.push n
      if assigned > total then
        throw s!"Only {total} damage remains to divide (CR 601.2d)"
      if assigned < total then
        throw "Must assign all remaining damage among the chosen targets (CR 601.2d)"
      let mut g := g.setStackEntryTargets obj.id targets amounts
      for (t, n) in assignments do
        g := g.logMsg
          s!"{(g.player p).name} chooses {g.targetLogName t} to be dealt {n} damage (CR 601.2d)"
      return g.afterTriggerTargetsChosen
    | none =>
      if choices.any (fun c => c.2.isSome) then
        throw "That spell or ability does not divide damage (CR 601.2d)"
      let some e := g.stackEntry? obj.id | throw "The ability left the stack"
      let kind := (g.targetingOf obj).kind
      let (minN, maxN) := g.announcedTargetBounds obj
      if kind.spec.slots.isEmpty then
        if !e.targets.isEmpty then
          throw "Those targets must be chosen at the same time (CR 601.2c)"
        if choices.size < minN then
          throw s!"Choose at least {minN} target(s) (CR 601.2c)"
        if choices.size > maxN then
          throw s!"Cannot choose more than {maxN} targets (CR 601.2c)"
        let legal := g.legalProposedTargets p obj
        let mut targets : Array Target := #[]
        for (t, _) in choices do
          if !legal.contains t then
            throw "Illegal target (CR 601.2c)"
          if targets.contains t then
            throw "Illegal target (CR 601.2c)"
          targets := targets.push t
        let mut g := g.setStackEntryTargets obj.id targets
        for t in targets do
          g := g.logMsg
            s!"{(g.player p).name} chooses {g.targetLogName t} as a target (CR 601.2c)"
        if g.proposedSpell.isSome then
          return g.afterTargetsChosen
        return g.afterTriggerTargetsChosen
      if choices.size != 1 then
        throw "Choose each instance of the word \"target\" separately (CR 601.2c)"
      let t := choices[0]!.1
      if !(g.legalProposedTargets p obj).contains t then
        throw "Illegal target (CR 601.2c)"
      let g := g.setStackEntryTargets obj.id (e.targets.push t)
      let g := g.logMsg
        s!"{(g.player p).name} chooses {g.targetLogName t} as a target (CR 601.2c)"
      if e.targets.size + 1 < kind.targetCount then
        return { g with pending := .chooseTargets p }
      if g.proposedSpell.isSome then
        return g.afterTargetsChosen
      return g.afterTriggerTargetsChosen
  | _ => throw "Not time to choose targets (CR 601.2c)"

/-- Announce one target of the current instance of the word “target”
(CR 601.2c / 603.3d). On a divided-damage ability this assigns all remaining
damage to that target (CR 601.2d). On “one or two target creatures” this
chooses that one creature and finishes the instance. -/
def announceTarget (g : Game) (p : PlayerId) (t : Target) : Except String Game :=
  g.announceTargetChoices p #[(t, none)]

/-- Announce every target of one instance of the word “target” together
(CR 601.2c), including “one or two target creatures”. -/
def announceTargets (g : Game) (p : PlayerId) (ts : Array Target) : Except String Game :=
  g.announceTargetChoices p (ts.map (fun t => (t, none)))

/-- Announce every target of one instance of the word “target” on a
“divided as you choose” effect (CR 601.2c / 601.2d). -/
def announceDividedDamage (g : Game) (p : PlayerId)
    (assignments : Array (Target × Nat)) : Except String Game :=
  g.announceTargetChoices p (assignments.map (fun (t, n) => (t, some n)))

/-- Shared activation legality (CR 602.3). `canActivate` is this check as a
`Bool`; `activateAbility` reports the first failing reason. -/
def validateActivation (g : Game) (p : PlayerId) (o : GameObject) (ab : ActivatedAbility) :
    Except String Unit := do
  if !g.hasPriority p then
    throw "You don't have priority"
  if ab.activateFromGraveyard then
    if !(o.zone == .graveyard o.owner && o.owner == p) then
      throw s!"{o.name}'s ability can be activated only from the graveyard"
  else if ab.activateFromHand then
    if !(o.zone == .hand o.owner && o.owner == p) then
      throw s!"{o.name}'s ability can be activated only from your hand"
  else
    if !o.isOnBattlefield then
      throw s!"{o.name} is not on the battlefield"
    if !o.controlledBy p then
      throw "You don't control that permanent"
  if ab.onlyIfYouControlLegendary && !g.controlsLegendaryCreature p then
    throw s!"{o.name}'s ability can be activated only if you control a legendary creature"
  if ab.onlyIfYouAttackedWithTwoOrMore &&
      (g.battlefield.filter (fun x =>
        x.isCreature && x.controlledBy p && x.status.attacking)).size < 2 then
    throw s!"{o.name}'s ability can be activated only if you attacked with two or more creatures this turn"
  if ab.onlyAsSorcery && !g.asSorcery? p then
    throw s!"{o.name}'s ability can be activated only as a sorcery"
  if ab.onlyDuringYourTurn && g.activePlayer != p then
    throw s!"{o.name}'s ability can be activated only during your turn"
  if ab.onceEachTurn && o.status.activationsThisTurn != 0 then
    throw s!"{o.name}'s ability can be activated only once each turn"
  if ab.cost.tap && o.status.tapped then
    throw s!"{o.name} is already tapped"
  if ab.cost.tap && o.hasSummoningSickness then
    throw s!"{o.name} has summoning sickness (CR 302.6)"
  if ab.cost.sacrificeAnotherCreatureOrArtifact &&
      (g.sacrificeCreatureOrArtifactChoices p o.id).isEmpty then
    throw s!"{o.name}'s ability requires sacrificing another creature or artifact"
  if !g.canPayLife p ab.cost.payLife then
    throw s!"{(g.player p).name} cannot pay {ab.cost.payLife} life"
  if !g.abilityCanChooseTarget p ab then
    throw s!"{o.name}'s ability requires a target"

/-- Whether `p` may begin activating `ab` of `o` (CR 602.3). Having
enough mana in the pool is not required; mana abilities are activated at
CR 601.2g. Cycling and other hand abilities use `activateFromHand` (CR 702.29). -/
def canActivate (g : Game) (p : PlayerId) (o : GameObject) (ab : ActivatedAbility) : Bool :=
  (g.validateActivation p o ab).isOk

def activateAbility (g : Game) (p : PlayerId) (id : ObjectId) (abilityIdx : Nat) :
    Except String Game := do
  if !g.hasPriority p then
    throw "You don't have priority"
  let some o := g.findObject? id | throw "no such object"
  if o.printed.activatedAbilities.isEmpty then
    throw s!"{o.name} has no activated ability"
  let some ab := o.printed.activatedAbilities[abilityIdx]?
    | throw s!"{o.name} has no such activated ability"
  g.validateActivation p o ab
  let pl := g.player p
  let stackBefore := g.stack
  let manaBefore := pl.manaPool
  let (g, abilityObj) := g.putStackAbility o p
    (abilityEffect := if ab.isModal then none else some ab.effect)
  let newId := abilityObj.id
  let g := g.logMsg s!"{pl.name} begins activating {o.name}"
  if !ab.isModal && !ab.effect.requiresTarget &&
      !ab.cost.mana.includesManaPayment && !ab.cost.sacrificeAnotherCreatureOrArtifact then
    let g ← g.payActivationExtraCosts p id ab.cost.tap ab.cost.sacrificeSource
      ab.cost.payLife ab.cost.discardSource
    return g.becomeActivated p o.name (some id)
  let manaCost := g.activationManaCost p ab
  let prop : ProposedSpell := {
    caster := p
    cost := manaCost
    spellId := newId
    original := o
    handBefore := pl.hand
    stackBefore := stackBefore
    manaBefore := manaBefore
    kind := .activatedAbility
    sourceId := some id
    tapSource := ab.cost.tap
    sacrificeSource := ab.cost.sacrificeSource
    needsSacrificeOther := ab.cost.sacrificeAnotherCreatureOrArtifact
    payLife := ab.cost.payLife
    discardSource := ab.cost.discardSource
    abilityModes := ab.allModes
    targetKindOverride := ab.equipSubtype.map EffectTargetKind.creatureYouControlSubtype
  }
  return g.enterProposalWindow p pl prop ab.isModal ab.effect.requiresTarget "CR 601.2b"

/-- Creatures `p` currently controls. -/
def creaturesControlledBy (g : Game) (p : PlayerId) : Array GameObject :=
  (g.permanentsOf p).filter (·.isCreature)

/-- First player in `players` who satisfies `pred`, plus those after them. -/
def nextActorWhere (_g : Game) (players : Array PlayerId) (pred : PlayerId → Bool) :
    Option (PlayerId × Array PlayerId) :=
  Id.run do
    for i in [0:players.size] do
      let p := players[i]!
      if pred p then
        return some (p, players.extract (i + 1) players.size)
    return none

/-- First player in `players` who controls a creature, plus those after them. -/
def nextActorWithCreatures (g : Game) (players : Array PlayerId) :
    Option (PlayerId × Array PlayerId) :=
  g.nextActorWhere players (fun p => !(g.creaturesControlledBy p).isEmpty)

/-- First player in `players` who has a card in hand, plus those after them. -/
def nextActorWithHandCard (g : Game) (players : Array PlayerId) :
    Option (PlayerId × Array PlayerId) :=
  g.nextActorWhere players (fun p => !(g.player p).hand.isEmpty)

/-- Sacrifice the chosen creatures simultaneously, then give priority. -/
def finishChosenSacrifices (g : Game) (chosen : Array ObjectId) : Game :=
  Id.run do
    let mut g := { g with pending := .none }
    for id in chosen do
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield && o.isCreature then
          let who := o.controller.getD o.owner
          g := g.moveToOwnerGraveyard o
            s!"{(g.player who).name} sacrifices {o.name}"
      | none => pure ()
    return g.receivePriority g.activePlayer

/-- Log `msg` for each player in `ps`. -/
def logForPlayers (g : Game) (ps : Array PlayerId) (msg : PlayerId → String) : Game :=
  ps.foldl (fun g p => g.logMsg (msg p)) g

/-- Ask the next player who can sacrifice a creature, or finish if none remain. -/
def beginSacrificeCreatures (g : Game) (players : Array PlayerId)
    (chosen : Array ObjectId := #[]) : Game :=
  match g.nextActorWithCreatures players with
  | none =>
    let skipped := players.filter (fun p => (g.creaturesControlledBy p).isEmpty)
    let g := g.logForPlayers skipped (fun p =>
      s!"{(g.player p).name} has no creature to sacrifice")
    g.finishChosenSacrifices chosen
  | some (p, rest) =>
    { g with pending := .chooseSacrificeCreature p chosen rest }
      |>.logMsg s!"{(g.player p).name} must sacrifice a creature"

/-- Ask the next player who has a card to discard, or resume priority. -/
def beginDiscardCards (g : Game) (players : Array PlayerId) : Game :=
  match g.nextActorWithHandCard players with
  | none =>
    let skipped := players.filter (fun p => (g.player p).hand.isEmpty)
    let g := g.logForPlayers skipped (fun p =>
      s!"{(g.player p).name} has no card to discard")
    { g with pending := .none }.receivePriority g.activePlayer
  | some (p, rest) =>
    { g with pending := .chooseDiscardCard p rest }
      |>.logMsg s!"{(g.player p).name} must discard a card"

/-- After mana is paid, sacrifice an artifact or creature (CR 601.2h / 602.2b), or sacrifice a creature a resolved trigger requires (CR 608.2d / 701.17). -/
def sacrificeForActivation (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  match g.pending with
  | .sacrificePermanent caster sourceId =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may sacrifice"
    let some sac := g.findObject? id | throw "no such object"
    if !g.canSacrificeAsCreatureOrArtifact p sourceId sac then
      throw s!"Can't sacrifice {sac.name}"
    let g := g.moveToOwnerGraveyard sac
      s!"{(g.player p).name} sacrifices {sac.name}"
    match g.proposedSpell with
    | some prop =>
      let g := { g with pending := .none, proposedSpell := none, consecutivePasses := 0 }
      match prop.kind with
      | .spell => return g.becomeCast prop.caster (g.object! prop.spellId)
      | .activatedAbility =>
        return g.becomeActivated p prop.original.name prop.sourceId
    | none =>
      let g := { g with pending := .none, proposedSpell := none, consecutivePasses := 0 }
      return g.becomeActivated p (g.object! sourceId).name (some sourceId)
  | .chooseSacrificeCreature q chosen remaining =>
    if q != p then
      throw s!"Only {(g.player q).name} may sacrifice"
    let some sac := g.findObject? id | throw "no such object"
    if !sac.isOnBattlefield || !sac.isCreature || !sac.controlledBy p then
      throw s!"Can't sacrifice {sac.name}"
    return g.beginSacrificeCreatures remaining (chosen.push id)
  | .sacrificeCreature q =>
    if p != q then
      throw s!"Only {(g.player q).name} may sacrifice"
    let some sac := g.findObject? id | throw "no such object"
    if !g.canSacrificeCreature p sac then
      throw s!"Can't sacrifice {sac.name}"
    let g := g.moveToOwnerGraveyard sac
      s!"{(g.player p).name} sacrifices {sac.name}"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | _ => throw "Not time to sacrifice a permanent"

/-- Destroy a permanent (CR 701.7). Indestructible permanents aren't destroyed
(CR 702.12b / 701.7b). If it would die this turn under an exile replacement,
`move` sends it to exile instead of the graveyard (CR 614.1). -/
def destroyPermanent (g : Game) (o : GameObject) : Game :=
  if g.hasIndestructible o then
    g.logMsg s!"{o.name} is indestructible and isn't destroyed"
  else
    g.moveToOwnerGraveyard o s!"{o.name} is destroyed"

/-- Update `o`'s status in place. -/
def mapObjectStatus (g : Game) (o : GameObject) (f : Status → Status) : Game :=
  g.setObject { o with status := f o.status }

/-- Deal `n` damage to a creature and log `msg`. `deathtouch` records that a
source with deathtouch dealt this damage (CR 702.2 / 704.5h). -/
def markDamageOn (g : Game) (o : GameObject) (n : Int) (msg : String)
    (deathtouch := false) : Game :=
  (g.mapObjectStatus o (fun s => s.addDamage n deathtouch)).logMsg msg

/-- Deal `n` damage to a creature and log the generic “is dealt” message. -/
def dealDamageToPermanent (g : Game) (o : GameObject) (n : Int) : Game :=
  g.markDamageOn o n s!"{o.name} is dealt {n} damage"

/-- Deal `n` damage from a named source (fight, dies trigger, blocked trigger). -/
def dealDamageFrom (g : Game) (sourceName : String) (o : GameObject) (n : Int)
    (deathtouch := false) : Game :=
  g.markDamageOn o n s!"{sourceName} deals {n} damage to {o.name}" deathtouch

/-- Deal `n` damage to a player and log the resulting life total (CR 120). -/
def dealDamageToPlayer (g : Game) (pid : PlayerId) (n : Int) : Game :=
  let pl := g.player pid
  g.setLife pid (pl.life - n) s!"{pl.name} is dealt {n} damage ({pl.life - n} life)"

/-- Decrease `p`'s life total (CR 118.3a). Losing 0 life does nothing
(CR 118.9). Loss of life is not damage (CR 120.3). -/
def loseLife (g : Game) (p : PlayerId) (n : Nat) : Game :=
  if n == 0 then g
  else
    let pl := g.player p
    g.setLife p (pl.life - (n : Int)) s!"{pl.name} loses {n} life ({pl.life - (n : Int)} life)"

/-- Deal `n` damage to an already-legal player or permanent target. -/
def dealDamageToTarget (g : Game) (t : Target) (n : Int) : Game :=
  match t with
  | Target.player pid => g.dealDamageToPlayer pid n
  | Target.permanent oid =>
    match g.findObject? oid with
    | some o => g.dealDamageToPermanent o n
    | none => g.logMsg "The target is no longer in play"
  | Target.card _ => g.logMsg "The target is no longer legal"

/-- Until-end-of-turn +P/+T on `o` (CR 613.4c / 611.2a). `trample` also grants
trample until end of turn (e.g. Oliphaunt). -/
def pumpPermanent (g : Game) (o : GameObject) (p t : Int) (trample := false) : Game :=
  let g := g.mapObjectStatus o (fun s =>
    let s := s.addPump p t
    if trample then s.grantUntilEot Keyword.trample else s)
  let gain := if trample then " and gains trample" else ""
  g.logMsg s!"{o.name} gets {signedStat p}/{signedStat t}{gain} until end of turn"

/-- Put `n` +1/+1 counters on `o` (CR 122.1). -/
def addPlusOnePlusOneTo (g : Game) (o : GameObject) (n : Nat := 1) : Game :=
  let g := g.mapObjectStatus o (·.addPlusOnePlusOne n)
  g.logMsg s!"{o.name} gets {plusOnePlusOneCountersPhrase n}"

/-- Amass `[subtype]` `n` (CR 701.43). If you control no Army, the token
enters as 0/0 and triggers see that power before counters are put on it. If
you control more than one Army, the newest is chosen (the player would
choose; tests use a single Army). -/
def amass (g : Game) (controller : PlayerId) (subtype : String) (n : Nat) : Game :=
  let armies := (g.permanentsOf controller).filter (fun o => g.hasSubtype o "Army")
  let createdFresh := armies.isEmpty
  let (g, army) :=
    match armies.toList with
    | [] => g.createToken controller (armyToken subtype)
    | x :: xs =>
      (g, xs.foldl (fun (best : GameObject) (o : GameObject) =>
        if o.timestamp ≥ best.timestamp then o else best) x)
  let g :=
    if createdFresh then
      let g := g.afterPermanentEnters (g.object! army.id)
      g.logMsg s!"the amassed Army entered as a 0/0 creature"
    else g
  let army := g.object! army.id
  let g :=
    if g.hasSubtype army subtype then g
    else
      g.mapObjectStatus army (fun s =>
        { s with additionalSubtypes := s.additionalSubtypes.push subtype })
  let army := g.object! army.id
  let g := g.addPlusOnePlusOneTo army n
  g.logMsg
    s!"{(g.player controller).name} amasses {subtype}s {n} ({army.name} is the amassed Army)"

/-- Amass Goblins `n` (CR 701.43). -/
def amassGoblins (g : Game) (controller : PlayerId) (n : Nat) : Game :=
  g.amass controller "Goblin" n

/-- Amass Orcs `n` (CR 701.43). -/
def amassOrcs (g : Game) (controller : PlayerId) (n : Nat) : Game :=
  g.amass controller "Orc" n

/-- Amass Zombies `n` (CR 701.43). -/
def amassZombies (g : Game) (controller : PlayerId) (n : Nat) : Game :=
  g.amass controller "Zombie" n

/-- +1/+1 counter plus trample and hexproof until end of turn. -/
def grantPlusOnePlusOneTrampleHexproof (g : Game) (o : GameObject) : Game :=
  let g := g.mapObjectStatus o (fun s =>
    (s.addPlusOnePlusOne 1).grantUntilEot (Keyword.trample.merge Keyword.hexproof))
  g.logMsg
    s!"{o.name} gets a +1/+1 counter and gains trample and hexproof until end of turn"

/-- Damage plus until-EOT lose-indestructible and exile-if-dies (e.g. Smite). -/
def dealDamageLoseIndestructibleExileTo (g : Game) (o : GameObject) (n : Nat) : Game :=
  let g := g.mapObjectStatus o (fun s =>
    let s := s.addDamage n
    { s with
      untilEotLosesIndestructible := true
      untilEotExileIfDies := true })
  g.logMsg
    s!"{o.name} is dealt {n} damage, loses indestructible until end of turn, and will be exiled if it would die this turn"

/-- Until-end-of-turn “can't be blocked” (CR 509.1b / 611.2a). -/
def grantCantBeBlockedThisTurn (g : Game) (o : GameObject) : Game :=
  let g := g.mapObjectStatus o (·.grantUntilEot Keyword.cantBeBlocked)
  g.logMsg s!"{o.name} can't be blocked this turn"

/-- Until-end-of-turn +P/+T and trample (e.g. Oliphaunt). -/
def pumpAndGrantTrample (g : Game) (o : GameObject) (p t : Int) : Game :=
  g.pumpPermanent o p t (trample := true)

/-- First library card of `p` whose printed characteristics satisfy `pred`
(bottom of the library first). -/
def findLibraryCard? (g : Game) (p : PlayerId) (pred : CardDef → Bool) : Option ObjectId :=
  (g.player p).library.find? (fun id =>
    match g.findObject? id with
    | some o => pred o.printed
    | none => false)

/-- Search `p`'s library for a card matching `pred`, apply `onFound` or log a
miss, then shuffle (CR 701.19). Picks the first matching card in library
order (bottom first). -/
def resolveLibrarySearch (g : Game) (p : PlayerId) (pred : CardDef → Bool)
    (kind : String) (onFound : Game → ObjectId → Game) : Game :=
  let pl := g.player p
  let g :=
    match g.findLibraryCard? p pred with
    | none => g.logMsg s!"{pl.name} searches their library and finds no {kind}"
    | some id => onFound g id
  g.shuffleLibrary p

/-- Search `p`'s library for a card matching `pred`, put it onto the battlefield
(tapped if `tapped`), then shuffle (CR 701.19). Picks the first matching card
in library order (bottom first). -/
def resolveSearchLibrary (g : Game) (p : PlayerId) (pred : CardDef → Bool)
    (tapped : Bool) (kind : String) : Game :=
  g.resolveLibrarySearch p pred kind fun g landId =>
    let landName := (g.object! landId).name
    let (g, newId) := g.putOntoBattlefield landId p (tapped := tapped)
      (summoningSick := false)
    let suffix := if tapped then " tapped" else ""
    let g := g.logMsg
      s!"{(g.player p).name} puts {landName} onto the battlefield{suffix}"
    g.afterLandEnters (g.object! newId)

/-- Search `p`'s library for a basic land card, put it onto the battlefield
tapped, then shuffle (CR 701.19). -/
def resolveSearchBasicLandTapped (g : Game) (p : PlayerId) : Game :=
  g.resolveSearchLibrary p isBasicLandCard true "basic land card"

/-- Search `p`'s library for a Forest card, put it onto the battlefield, then
shuffle (CR 701.19 / 305.7). -/
def resolveSearchForest (g : Game) (p : PlayerId) : Game :=
  g.resolveSearchLibrary p isForestCard false "Forest card"

/-- Search `p`'s library for a card with land type `landType`, reveal it, put
it into their hand, then shuffle (CR 701.19 / 702.29). Picks the first matching
card in library order (bottom first). -/
def resolveSearchLandTypeToHand (g : Game) (p : PlayerId) (landType : String) : Game :=
  g.resolveLibrarySearch p (fun c => c.hasSubtype landType) s!"{landType} card"
    fun g cardId =>
      let cardName := (g.object! cardId).name
      let (g, _) := g.move cardId (.hand p) none
      g.logMsg s!"{(g.player p).name} reveals {cardName} and puts it into their hand"

/-- Exile the top card of `p`'s library and grant permission to play it until
the end of that player's next turn (CR 701.14). -/
def resolveExileTopPlayUntilEndOfNextTurn (g : Game) (p : PlayerId) : Game :=
  let pl := g.player p
  if pl.library.isEmpty then
    g.logMsg s!"{pl.name} has no cards in their library to exile"
  else
    let top := pl.library.back!
    let cardName := (g.object! top).name
    let (g, newId) := g.move top .exile none
    let o := g.object! newId
    let g := g.setObject { o with
      playPermission := some { player := p, turnEndsRemaining := 2 } }
    g.logMsg
      s!"{pl.name} exiles {cardName} and may play it until the end of their next turn"

/-- Log why a targeted ability failed to affect its announced target (CR 608.2b). -/
def illegalAbilityTarget (g : Game) : Target → Game
  | Target.player _ => g.logMsg "The target is no longer legal"
  | Target.permanent oid =>
    match g.findObject? oid with
    | some o =>
      if o.isOnBattlefield then g.logMsg "The target is no longer legal"
      else g.logMsg "The target is no longer in play"
    | none => g.logMsg "The target is no longer in play"
  | Target.card oid =>
    match g.findObject? oid with
    | some o =>
      match o.zone with
      | .graveyard _ => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "The target is no longer in the graveyard"
    | none => g.logMsg "The target is no longer in the graveyard"

/-- Apply `f` when the announced target is still in `legal` (CR 608.2b).
`missing` is logged when no target was announced; `none` leaves the game unchanged. -/
def withLegalTarget (g : Game) (legal : Array Target) (targets : Array Target)
    (f : Game → Target → Game) (missing : Option String := none) : Game :=
  match targets[0]? with
  | none =>
    match missing with
    | some msg => g.logMsg msg
    | none => g
  | some t =>
    if legal.contains t then f g t else g.illegalAbilityTarget t

/-- Apply `f` to a still-legal permanent target. -/
def withLegalPermanentTarget (g : Game) (legal : Array Target) (targets : Array Target)
    (f : Game → GameObject → Game) (missing : Option String := none) : Game :=
  g.withLegalTarget legal targets (fun g t =>
    match t with
    | Target.permanent oid =>
      match g.findObject? oid with
      | none => g.logMsg "The target is no longer in play"
      | some o => f g o
    | Target.player _ | Target.card _ => g.logMsg "The target is no longer legal")
    missing

/-- Apply `f` when the announced target is still legal for `kind` (CR 608.2b). -/
def withLegalKindTarget (g : Game) (controller : PlayerId) (kind : EffectTargetKind)
    (targets : Array Target) (f : Game → Target → Game)
    (sourceId : Option ObjectId := none) (missing : Option String := none) : Game :=
  g.withLegalTarget (g.legalTargetsForKind controller kind sourceId) targets f missing

/-- Apply `f` to a still-legal permanent target of `kind`. -/
def withLegalKindPermanent (g : Game) (controller : PlayerId) (kind : EffectTargetKind)
    (targets : Array Target) (f : Game → GameObject → Game)
    (sourceId : Option ObjectId := none) (missing : Option String := none) : Game :=
  g.withLegalPermanentTarget (g.legalTargetsForKind controller kind sourceId) targets f
    missing

/-- Apply `f` when the announced trigger target is still legal (CR 608.2b). -/
def withLegalTriggerTarget (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (f : Game → Target → Game) (noneMsg : String := "The target is no longer legal") : Game :=
  g.withLegalKindTarget controller ab.targetKind targets f sourceId (some noneMsg)

/-- Apply `f` to a still-legal permanent target of a triggered ability. -/
def withLegalTriggerPermanent (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (f : Game → GameObject → Game) (noneMsg : String := "The target is no longer legal") : Game :=
  g.withLegalKindPermanent controller ab.targetKind targets f sourceId (some noneMsg)

/-- Deal `n` damage to a still-legal target of `kind`. -/
def applyDamageToKindTarget (g : Game) (controller : PlayerId) (kind : EffectTargetKind)
    (targets : Array Target) (n : Nat) (sourceId : Option ObjectId := none)
    (missing : Option String := none) : Game :=
  g.withLegalKindTarget controller kind targets (fun g t => g.dealDamageToTarget t n)
    sourceId missing

/-- Exile creature cards from `fromPlayer`'s graveyard and grant `controller`
permission to cast them, spending mana as though it were any type. -/
def exileCreaturesFromGraveyard (g : Game) (controller fromPlayer : PlayerId) : Game :=
  let ids :=
    (g.player fromPlayer).graveyard.filter (fun id =>
      match g.findObject? id with
      | some o => o.printed.isCreature
      | none => false)
  Id.run do
    let mut g := g
    for id in ids do
      match g.findObject? id with
      | none => pure ()
      | some o =>
        let name := o.name
        let (g', newId) := g.move id .exile none
        g := g'
        let o := g.object! newId
        g := g.setObject { o with
          playPermission := some {
            player := controller
            turnEndsRemaining := 0
            whileExiled := true
            anyMana := true } }
        g := g.logMsg
          s!"{name} is exiled. {(g.player controller).name} may cast it for as long as it remains exiled"
    return g

/-- Apply a shared permanent action (spells, activated abilities, and triggers). -/
def applyPermanentAction (g : Game) (o : GameObject) : PermanentAction → Game
  | .pump pw tw => g.pumpPermanent o pw tw
  | .pumpAndTrample pw tw => g.pumpAndGrantTrample o pw tw
  | .destroy => g.destroyPermanent o
  | .plusOne n => g.addPlusOnePlusOneTo o n
  | .plusOnePlusOneTrampleHexproof => g.grantPlusOnePlusOneTrampleHexproof o
  | .dealDamage n => g.dealDamageToPermanent o n
  | .dealDamageLoseIndestructibleExile n =>
    g.dealDamageLoseIndestructibleExileTo o n
  | .destroyThenNonflyersCantBlock =>
    let g := g.destroyPermanent o
    let g := { g with creaturesWithoutFlyingCantBlock := true }
    g.logMsg "Creatures without flying can't block this turn"
  | .cantBeBlocked => g.grantCantBeBlockedThisTurn o
  | .pumpAndLifelink pw tw =>
    let g := g.pumpPermanent o pw tw
    let o := g.object! o.id
    let g := g.mapObjectStatus o (·.grantUntilEot Keyword.lifelink)
    g.logMsg s!"{o.name} gains lifelink until end of turn"
  | .pumpAndExileIfDies pw tw =>
    let g := g.pumpPermanent o pw tw
    let o := g.object! o.id
    let g := g.mapObjectStatus o (fun s => { s with untilEotExileIfDies := true })
    g.logMsg s!"If {o.name} would die this turn, exile it instead"
  | .grantKeywords k =>
    let g := g.mapObjectStatus o (·.grantUntilEot k)
    g.logMsg s!"{o.name} gains {k} until end of turn"
  | .tap =>
    if o.status.tapped then
      g.logMsg s!"{o.name} is already tapped"
    else
      let g := g.mapObjectStatus o (fun s => { s with tapped := true })
      g.logMsg s!"{o.name} becomes tapped"
  | .untap =>
    if !o.status.tapped then
      g.logMsg s!"{o.name} is already untapped"
    else
      let g := g.mapObjectStatus o (fun s => { s with tapped := false })
      g.logMsg s!"{o.name} untaps"
  | .becomeArtifactIndestructible =>
    let g := g.mapObjectStatus o (fun s =>
      { s with
        additionalArtifactUntilEot := true
        untilEotKeywords := Keywords.merge s.untilEotKeywords Keyword.indestructible })
    g.logMsg
      s!"{o.name} becomes an artifact and gains indestructible until end of turn"
  | .pumpAndGrant pw tw k =>
    let g := g.pumpPermanent o pw tw
    let o := g.object! o.id
    let g := g.mapObjectStatus o (·.grantUntilEot k)
    g.logMsg s!"{o.name} gains {k} until end of turn"
def applyOnPermanent (g : Game) (controller : PlayerId) (kind : EffectTargetKind)
    (targets : Array Target) (action : PermanentAction)
    (sourceId : Option ObjectId := none) (missing : Option String := none) : Game :=
  match action with
  | .dealDamage n =>
    g.applyDamageToKindTarget controller kind targets n sourceId missing
  | _ =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      g.applyPermanentAction o action) sourceId missing

/-- Queue “whenever you scry” triggers for permanents `p` controls (CR 701.20). -/
def queueScryTriggers (g : Game) (p : PlayerId) (lookedAt : Nat) : Game :=
  g.foldControlledPermanents p none fun g o =>
    g.enqueueWaitingTriggers
      (o.waitingTriggersFor p .youScry (some (Int.ofNat lookedAt)))

/-- Start scrying `n` as a keyword action during resolution (CR 701.20).
Scry 0 is skipped and does not trigger “whenever you scry” (CR 701.20c). -/
def beginScry (g : Game) (p : PlayerId) (n : Nat) : Game :=
  let pl := g.player p
  let count := min n pl.library.size
  let g := if n == 0 then g else g.queueScryTriggers p count
  if count == 0 then
    g.logMsg s!"{pl.name} scries {n} (no cards to look at)"
  else
    { g with pending := .scry p count }.logMsg s!"{pl.name} scries {n}"

/-- Put the top `n` cards of `p`'s library into their graveyard (CR 701.13). -/
def mill (g : Game) (p : PlayerId) (n : Nat) : Game :=
  Id.run do
    let mut g := g
    for _ in [0:n] do
      let pl := g.player p
      if pl.library.isEmpty then
        return g.logMsg s!"{pl.name} mills nothing (empty library)"
      else
        let top := pl.library.back!
        let name := (g.object! top).name
        let (g', _) := g.move top (.graveyard p) none
        g := g'.logMsg s!"{pl.name} mills {name}"
    return g

/-- Counter a spell on the stack. `exile` puts a permanent spell into exile
and may grant a free cast (CR 701.5 / Thranduil's Decree). -/
def counterStackSpell (g : Game) (spellId : ObjectId) (exilePermanent := false)
    (grantFreeCast := false) (controller : PlayerId := ⟨0⟩) : Game :=
  match g.findObject? spellId with
  | none => g.logMsg "The spell is no longer on the stack"
  | some o =>
    if o.zone != .stack then
      g.logMsg s!"{o.name} is no longer on the stack"
    else if o.printed.cantBeCountered then
      g.logMsg s!"{o.name} can't be countered"
    else
      let dest :=
        if exilePermanent && o.printed.isPermanentCard then Zone.exile
        else Zone.graveyard o.owner
      let name := o.name
      let (g, newId) := g.move spellId dest none
      let g :=
        if dest == .exile && grantFreeCast then
          let o := g.object! newId
          g.setObject { o with
            playPermission := some {
              player := controller
              turnEndsRemaining := 0
              whileExiled := true
              withoutManaCost := true } }
        else g
      let destNote := if dest == .exile then "exiled" else "countered"
      g.logMsg s!"{name} is {destNote}"

/-- Exile `o` until `source` leaves the battlefield, linking the new exile id. -/
def exileUntilSourceLeaves (g : Game) (sourceId : Option ObjectId) (o : GameObject) :
    Game :=
  let name := o.name
  let (g, newId) := g.move o.id .exile none
  let g :=
    match sourceId.bind g.findObject? with
    | some src =>
      g.setObject { src with linkedExile := src.linkedExile.push newId }
    | none => g
  g.logMsg s!"{name} is exiled until the source leaves the battlefield"

/-- Return cards linked-exiled by `source`. -/
def returnLinkedExile (g : Game) (source : GameObject) : Game :=
  Id.run do
    let mut g := g
    for id in source.linkedExile do
      match g.findObject? id with
      | some o =>
        if o.zone == .exile then
          let name := o.name
          let owner := o.owner
          let (g', newId) := g.move id .battlefield (some owner)
          g := g'
          let o := g.object! newId
          let sick := !o.printed.keywords.haste
          g := g.setObject { o with status := { o.status with summoningSick := sick } }
          g := g.logMsg s!"{name} returns to the battlefield"
          g := g.afterPermanentEnters (g.object! newId)
      | none => pure ()
    return g

def applyEffect (g : Game) (controller : PlayerId) (effect : SpellEffect)
    (targets : Array Target) (castFromGraveyard := false) : Game :=
  match effect.resolution with
  | .fight =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent srcId), some (Target.permanent destId) =>
      let srcOk := (g.legalCreatureYouControlTargets controller).contains
        (Target.permanent srcId)
      let destOk := (g.legalOppCreatureTargets controller).contains
        (Target.permanent destId)
      if srcOk && destOk then
        let src := g.object! srcId
        g.dealDamageFrom src.name (g.object! destId) (g.power src).toNat
          (deathtouch := g.hasDeathtouch src)
      else
        let logIllegal (g : Game) (ok : Bool) (id : ObjectId) : Game :=
          if ok then g else g.illegalAbilityTarget (Target.permanent id)
        logIllegal (logIllegal g srcOk srcId) destOk destId
    | _, _ => g.logMsg "The target is no longer legal"
  | .extraLand =>
    let g := g.modifyPlayer controller (fun pl =>
      { pl with additionalLandsThisTurn := pl.additionalLandsThisTurn + 1 })
    g.logMsg s!"{(g.player controller).name} may play an additional land this turn"
  | .drawAndLoseLife cards life =>
    let g := g.draw controller cards
    g.loseLife controller life
  | .onPermanent action =>
    g.applyOnPermanent controller effect.targetKind targets action
  | .allCreaturesPump p t =>
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.isCreature then
          g := g.pumpPermanent o p t
      return g
  | .playerDrawLoseLife cards life =>
    g.withLegalKindTarget controller effect.targetKind targets (fun g tgt =>
      match tgt with
      | Target.player pid =>
        let g := g.draw pid cards
        g.loseLife pid life
      | _ => g.logMsg "The target is no longer legal")
  | .creaturesOfPlayerPump pw tw =>
    g.withLegalKindTarget controller effect.targetKind targets (fun g tgt =>
      match tgt with
      | Target.player pid =>
        Id.run do
          let mut g := g
          for o in g.battlefield do
            if o.isCreature && o.controlledBy pid then
              g := g.pumpPermanent o pw tw
          return g
      | _ => g.logMsg "The target is no longer legal")
  | .destroyAndControllerLosesLife n =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let ctrl := o.controller
      let g := g.destroyPermanent o
      match ctrl with
      | some pid => g.loseLife pid n
      | none => g)
  | .exileGraveyardCreaturesGrantCast =>
    g.withLegalKindTarget controller effect.targetKind targets (fun g tgt =>
      match tgt with
      | Target.player pid => g.exileCreaturesFromGraveyard controller pid
      | _ => g.logMsg "The target is no longer legal")
  | .draw n =>
    g.draw controller n
  | .drawThenDiscard n =>
    let g := g.draw controller n
    g.beginDiscardCards #[controller]
  | .scry n =>
    g.beginScry controller n
  | .tapScryDraw scryN drawN =>
    let g := g.applyOnPermanent controller effect.targetKind targets .tap
    let g := { g with pendingDrawAfterScry := some (controller, drawN) }
    let g := g.beginScry controller scryN
    if g.pendingDrawAfterScry.isSome &&
        (match g.pending with | .scry _ _ => false | _ => true) then
      let g := { g with pendingDrawAfterScry := none }
      g.draw controller drawN
    else g
  | .tapTargets =>
    Id.run do
      let mut g := g
      for t in targets do
        match t with
        | Target.permanent id =>
          match g.findObject? id with
          | some o =>
            if o.isOnBattlefield && o.isCreature then
              g := g.applyPermanentAction o .tap
          | none => pure ()
        | _ => pure ()
      return g
  | .counter =>
    match targets[0]? with
    | some (Target.card id) => g.counterStackSpell id
    | _ => g.logMsg "The target is no longer legal"
  | .counterUnlessPays n =>
    match targets[0]? with
    | some (Target.card id) =>
      match g.findObject? id with
      | some o =>
        let ctrl := o.controller.getD o.owner
        { g with pending := .payOrLetCounter ctrl n id }.logMsg
          s!"{(g.player ctrl).name} may pay \{{n}} or {o.name} is countered"
      | none => g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | .counterExilePermanentMayCast =>
    match targets[0]? with
    | some (Target.card id) =>
      g.counterStackSpell id (exilePermanent := true) (grantFreeCast := true)
        controller
    | _ => g.logMsg "The target is no longer legal"
  | .putOnTopOrBottom =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield then
          { g with pending := .chooseLibraryPlacement o.owner id }.logMsg
            s!"{(g.player o.owner).name} chooses top or bottom of their library for {o.name}"
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | .untapPumpMaybeAttach p t =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.applyPermanentAction o .untap
      let o := g.object! o.id
      let g := g.pumpPermanent o p t
      let o := g.object! o.id
      if g.hasSubtype o "Dwarf" then
        { g with pending := .mayAttachEquipment controller o.id }.logMsg
          s!"{(g.player controller).name} may attach an Equipment to {o.name}"
      else g)
  | .exchangeControl =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent a), some (Target.permanent b) =>
      match g.findObject? a, g.findObject? b with
      | some oa, some ob =>
        if oa.isOnBattlefield && ob.isOnBattlefield then
          let ca := oa.controller
          let cb := ob.controller
          let g := g.setObject { oa with controller := cb }
          let g := g.setObject { (g.object! b) with controller := ca }
          g.logMsg s!"{oa.name} and {ob.name} exchange control"
        else g.logMsg "The target is no longer legal"
      | _, _ => g.logMsg "The target is no longer legal"
    | _, _ => g.logMsg "The target is no longer legal"
  | .plusOneAndPlayerGainsLife n =>
    let g :=
      g.withLegalKindTarget controller effect.targetKind targets (fun g tgt =>
        match tgt with
        | Target.player pid =>
          if n == 0 then g
          else
            let pl := g.player pid
            g.setLife pid (pl.life + (n : Int))
              s!"{pl.name} gains {n} life ({pl.life + (n : Int)} life)"
        | _ => g)
    { g with pending := .mayPlusOneCreature controller }.logMsg
      s!"{(g.player controller).name} may put a +1/+1 counter on a creature"
  | .returnSpellDraw =>
    let g :=
      match targets[0]? with
      | some (Target.card id) => g.returnStackSpell id
      | _ => g.logMsg "The target is no longer legal"
    g.draw controller 1
  | .creaturesYouControlPump pw tw =>
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.isCreature && o.controlledBy controller then
          g := g.pumpPermanent o pw tw
      return g
  | .amassGoblins n =>
    g.amassGoblins controller n
  | .drawLoseLifeThenAmass n =>
    let g := g.draw controller 1
    let g := g.loseLife controller 1
    g.amassGoblins controller n
  | .returnCreatureFromGyThenAmass n =>
    let g :=
      match targets[0]? with
      | some (Target.card oid) =>
        match g.findObject? oid with
        | none => g.logMsg "The target is no longer in the graveyard"
        | some o =>
          let name := o.name
          let (g, _) := g.move oid (.hand controller) none
          g.logMsg s!"{name} is returned to {(g.player controller).name}'s hand"
      | _ => g
    g.amassGoblins controller n
  | .counterThenRecruitIfMvAtMost n =>
    match targets[0]? with
    | some (Target.card id) =>
      match g.findObject? id with
      | none => g.logMsg "The target is no longer legal"
      | some o =>
        let mv := o.printed.manaValue
        let g := g.counterStackSpell id
        if mv <= n then g.beginRecruit controller else g
    | _ => g.logMsg "The target is no longer legal"
  | .plusOneThenFight n =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent srcId), some (Target.permanent destId) =>
      match g.findObject? srcId, g.findObject? destId with
      | some src, some _dest =>
        let g := g.addPlusOnePlusOneTo src n
        let src := g.object! srcId
        let dest := g.object! destId
        let g := g.dealDamageFrom src.name dest (g.power src).toNat
          (deathtouch := g.hasDeathtouch src)
        match g.findObject? destId, g.findObject? srcId with
        | some dest, some src =>
          g.dealDamageFrom dest.name src (g.power dest).toNat
            (deathtouch := g.hasDeathtouch dest)
        | _, _ => g
      | _, _ => g.logMsg "The target is no longer legal"
    | _, _ => g.logMsg "The target is no longer legal"
  | .plusOneThenEachOtherIfFromGy =>
    match targets[0]? with
    | some (Target.permanent oid) =>
      match g.findObject? oid with
      | none => g.logMsg "The target is no longer legal"
      | some o =>
        let g := g.addPlusOnePlusOneTo o 1
        if !castFromGraveyard then g
        else
          Id.run do
            let mut g := g
            for c in g.battlefield do
              if c.isCreature && c.controlledBy controller && c.id != oid then
                g := g.addPlusOnePlusOneTo c 1
            return g
    | _ => g.logMsg "The target is no longer legal"
  | .drawIfFromGy n fromGy =>
    g.draw controller (if castFromGraveyard then fromGy else n)
  | .amassGoblinsOrFromGy n fromGy =>
    g.amassGoblins controller (if castFromGraveyard then fromGy else n)
  | .searchLegendaryCreatureToHand =>
    g.resolveLibrarySearch controller (fun c =>
      c.isCreature && c.hasSupertype .legendary) "legendary creature card"
      fun g cardId =>
        let cardName := (g.object! cardId).name
        let (g, _) := g.move cardId (.hand controller) none
        g.logMsg s!"{(g.player controller).name} reveals {cardName} and puts it into their hand"
  | .dealDamageToEachOppCreature n =>
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.isCreature && !o.controlledBy controller then
          g := g.applyPermanentAction o (.dealDamage n)
      return g
  | .targetPlayerDraw n =>
    g.withLegalKindTarget controller effect.targetKind targets (fun g tgt =>
      match tgt with
      | Target.player pid => g.draw pid n
      | _ => g.logMsg "The target is no longer legal")
  | .dealDamageToCreatureExileIfDies n =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.mapObjectStatus o (fun s => { s with untilEotExileIfDies := true })
      g.applyPermanentAction (g.object! o.id) (.dealDamage n))
  | .addRedPerOppArtifacts =>
    let n :=
      g.battlefield.filter (fun o =>
        o.printed.isArtifact && !o.controlledBy controller) |>.size
    let g := g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .red) n })
    g.logMsg s!"{(g.player controller).name} adds {n} red mana"
  | .dealDamageToEachNonDragon n =>
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.isCreature && !g.hasSubtype o "Dragon" then
          g := g.applyPermanentAction o (.dealDamage n)
      return g
  | .chooseTypeReturnOthers =>
    let chosen :=
      (g.battlefield.find? (fun o => o.isCreature && o.controlledBy controller)
        |>.bind (fun o => o.printed.subtypes[0]?)).getD "Elf"
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.isCreature && !g.hasSubtype o chosen then
          let owner := o.owner
          let name := o.name
          let (g', _) := g.move o.id (.hand owner) none
          g := g'.logMsg s!"{name} is returned to {(g'.player owner).name}'s hand"
      return g
  | .drawEqualToughnessThenPutCreatures =>
    let greatest :=
      (g.permanentsOf controller).foldl (fun acc o =>
        if o.isCreature then max acc (g.toughness o).toNat else acc) 0
    let g := g.draw controller greatest
    Id.run do
      let mut g := g
      for id in (g.player controller).hand do
        let o := g.object! id
        if o.printed.isCreature then
          let sick := !o.printed.keywords.haste
          let (g', newId) := g.putOntoBattlefield id controller (summoningSick := sick)
          g := g'.logMsg s!"{o.name} enters the battlefield"
          g := g.afterPermanentEnters (g.object! newId)
      return g
  | .millThenPutInstantOrSorcery n =>
    let g := g.mill controller n
    let gy := (g.player controller).graveyard
    let take := gy.size.min n
    let milled := gy.extract (gy.size - take) gy.size
    match milled.find? (fun id =>
      let c := (g.object! id).printed
      c.isInstant || c.isSorcery) with
    | none => g
    | some id =>
      let name := (g.object! id).name
      let (g, _) := g.move id (.hand controller) none
      g.logMsg s!"{(g.player controller).name} puts {name} into their hand"
  | .millThenPutLands n max =>
    let g := g.mill controller n
    let gy := (g.player controller).graveyard
    let take := gy.size.min n
    let milled := gy.extract (gy.size - take) gy.size
    Id.run do
      let mut g := g
      let mut left := max
      for id in milled do
        if left > 0 && (g.object! id).printed.isLand then
          let name := (g.object! id).name
          let (g', _) := g.move id (.hand controller) none
          g := g'.logMsg s!"{(g.player controller).name} puts {name} into their hand"
          left := left - 1
      return g
  | .dealDamageToEachNonDragonThenAddDragonMana n =>
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.isCreature && !g.hasSubtype o "Dragon" then
          g := g.applyPermanentAction o (.dealDamage n)
      g := g.modifyPlayer controller (fun pl =>
        { pl with manaPool := pl.manaPool.add (.colored .red) 4 })
      return g.logMsg
        s!"{(g.player controller).name} adds four mana that can be spent only on Dragon spells"
  | .millThenPutAllInstantsOrSorceries n =>
    let g := g.mill controller n
    let gy := (g.player controller).graveyard
    let take := gy.size.min n
    let milled := gy.extract (gy.size - take) gy.size
    Id.run do
      let mut g := g
      for id in milled do
        let o := g.object! id
        if o.printed.isInstant || o.printed.isSorcery then
          let name := o.name
          let (g', _) := g.move id (.hand controller) none
          g := g'.logMsg s!"{(g.player controller).name} puts {name} into their hand"
      return g
  | .exileAttackersSearchBasics =>
    g.withLegalKindTarget controller effect.targetKind targets (fun g tgt =>
      match tgt with
      | Target.player pid =>
        Id.run do
          let mut g := g
          let mut n : Nat := 0
          for o in g.battlefield do
            if o.isCreature && o.status.attacking && o.controlledBy pid then
              let name := o.name
              let (g', _) := g.move o.id (.exile) none
              g := g'.logMsg s!"{name} is exiled"
              n := n + 1
          return g.logMsg s!"{(g.player pid).name} may search for {n} basic lands"
      | _ => g.logMsg "The target is no longer legal")
  | .createTokensX kind =>
    g.createKindTokens controller kind 1
  | .exileTopPlayIfYouControlSubtype n _subtype =>
    let g := Id.run do
      let mut g := g
      for _ in List.range n do
        g := g.resolveExileTopPlayUntilEndOfNextTurn controller
      return g
    g
  | .exileThenReturnYouControl =>
    Id.run do
      let mut g := g
      for t in targets do
        match t with
        | Target.permanent oid =>
          match g.findObject? oid with
          | none => pure ()
          | some o =>
            if o.controlledBy controller then
              let owner := o.owner
              let name := o.name
              let (g', newId) := g.move oid .exile none
              let (g'', retId) := g'.move newId .battlefield (some owner)
              g := g''
              let o := g.object! retId
              let sick := !o.printed.keywords.haste
              g := g.setObject { o with status := { o.status with summoningSick := sick } }
              g := g.logMsg s!"{name} is exiled, then returned to the battlefield"
              g := g.afterPermanentEnters (g.object! retId)
        | _ => pure ()
      return g
  | .destroyArtifactOrEnchantmentGainLife n =>
    let g := g.applyOnPermanent controller effect.targetKind targets .destroy
    if n == 0 then g
    else
      let pl := g.player controller
      g.setLife controller (pl.life + (n : Int))
        s!"{pl.name} gains {n} life ({pl.life + (n : Int)} life)"
  | .printed text =>
    g.logMsg text

def withSourceOnBattlefield (g : Game) (sourceId : Option ObjectId)
    (f : Game → GameObject → Game)
    (missing := "The ability's source is no longer in play") : Game :=
  match sourceId.bind g.findObject? with
  | some o =>
    if o.isOnBattlefield then f g o
    else g.logMsg s!"{o.name} is no longer on the battlefield"
  | none =>
    g.logMsg missing

/-- Increase `p`'s life total (CR 118.2). Gaining 0 life does nothing (CR 118.9). -/
def gainLife (g : Game) (p : PlayerId) (n : Nat) : Game :=
  if n == 0 then g
  else
    let pl := g.player p
    g.setLife p (pl.life + (n : Int)) s!"{pl.name} gains {n} life ({pl.life + (n : Int)} life)"

/-- Apply `action` if `sourceId` is still on the battlefield. -/
def applyOnSource (g : Game) (sourceId : Option ObjectId) (action : PermanentAction)
    (missing := "The ability's source is no longer in play") : Game :=
  g.withSourceOnBattlefield sourceId (fun g o => g.applyPermanentAction o action) missing

/-- Return a graveyard source to the battlefield tapped or to its owner's hand. -/
def returnSourceFromGraveyard (g : Game) (sourceId : Option ObjectId)
    (controller : PlayerId) (tapped := false) (toHand := false) : Game :=
  match sourceId.bind g.findObject? with
  | none => g.logMsg "The ability's source is no longer in the graveyard"
  | some o =>
    if o.zone != .graveyard o.owner then
      g.logMsg s!"{o.name} is no longer in the graveyard"
    else if toHand then
      let name := o.name
      let (g, _) := g.move o.id (.hand o.owner) none
      g.logMsg s!"{name} is returned to {(g.player o.owner).name}'s hand"
    else
      let name := o.name
      let sick := !o.printed.keywords.haste
      let (g, newId) := g.putOntoBattlefield o.id controller (tapped := tapped)
        (summoningSick := sick)
      let g := g.logMsg
        (if tapped then s!"{name} returns to the battlefield tapped"
         else s!"{name} returns to the battlefield")
      g.afterPermanentEnters (g.object! newId)

def applyAbilityEffect (g : Game) (controller : PlayerId) (effect : AbilityEffect)
    (targets : Array Target) (sourceId : Option ObjectId := none) : Game :=
  match effect.resolution with
  | .searchBasicLand => g.resolveSearchBasicLandTapped controller
  | .searchLandTypeToHand t => g.resolveSearchLandTypeToHand controller t
  | .exileTop => g.resolveExileTopPlayUntilEndOfNextTurn controller
  | .attach =>
    g.withLegalKindPermanent controller effect.targetKind targets fun g host =>
      g.withSourceOnBattlefield sourceId (fun g src =>
        if src.attachedTo == some host.id then
          g.logMsg s!"{src.name} is already attached to {host.name}"
        else
          let (g, ts) := g.bumpTime
          let src := g.object! src.id
          let g := g.setObject { src with attachedTo := some host.id, timestamp := ts }
          g.logMsg s!"{src.name} attaches to {host.name}")
        "The Equipment is no longer in play"
  | .onPermanent action =>
    g.applyOnPermanent controller effect.targetKind targets action sourceId
  | .onSource action =>
    g.applyOnSource sourceId action
  | .becomeBear =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let subtypes :=
        if g.hasSubtype o "Bear" then o.status.additionalSubtypes
        else o.status.additionalSubtypes.push "Bear"
      let granted :=
        if g.hasLandsYouControlPT o then o.status.grantedStaticAbilities
        else o.status.grantedStaticAbilities.push .powerToughnessEqualLandsYouControl
      let g := g.mapObjectStatus o (fun s =>
        { s with
          additionalCreature := true
          additionalSubtypes := subtypes
          grantedStaticAbilities := granted })
      g.logMsg
        s!"{o.name} becomes a Bear creature. Its power and toughness are each equal to the number of lands you control"
  | .returnFromGraveyardTapped =>
    g.returnSourceFromGraveyard sourceId controller (tapped := true)
  | .returnFromGraveyardToHand =>
    g.returnSourceFromGraveyard sourceId controller (toHand := true)
  | .creaturesYouControlPump pw tw =>
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.isCreature && o.controlledBy controller then
          g := g.pumpPermanent o pw tw
      return g
  | .mill n =>
    g.withLegalKindTarget controller effect.targetKind targets (fun g tgt =>
      match tgt with
      | Target.player pid => g.mill pid n
      | _ => g.logMsg "The target is no longer legal")
  | .drawThenDiscard =>
    let g := g.draw controller 1
    g.beginDiscardCards #[controller]
  | .addAnyColor =>
    let g := g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .white) })
    g.logMsg s!"{(g.player controller).name} adds one mana of any color"
  | .drawThenDiscardN n =>
    let g := g.draw controller n
    g.beginDiscardCards #[controller]
  | .createTreasure n =>
    g.createTreasureTokens controller n
  | .recruit =>
    g.beginRecruit controller
  | .scry n =>
    g.beginScry controller n
  | .gainLife n =>
    g.gainLife controller n
  | .createTokens kind n =>
    g.createKindTokens controller kind n
  | .ownerShuffleSourceDraw n =>
    match sourceId.bind g.findObject? with
    | none => g.logMsg "The source is no longer in play"
    | some src =>
      let owner := src.owner
      let (g, _) := g.move src.id (.library owner) none
      let g := g.shuffleLibrary owner
      g.draw owner n
  | .returnFromGyAttach =>
    match sourceId.bind g.findObject?, targets[0]? with
    | some src, some (Target.permanent hostId) =>
      match g.findObject? hostId with
      | none => g.logMsg "The target is no longer legal"
      | some host =>
        if !host.isOnBattlefield then g.logMsg "The target is no longer legal"
        else
          let (g, newId) := g.putOntoBattlefield src.id controller
            (attachedTo := some host.id)
          let o := g.object! newId
          let g := g.logMsg s!"{o.name} enters the battlefield attached to {host.name}"
          g.afterPermanentEnters (g.object! newId)
    | _, _ => g.logMsg "The source is no longer in the graveyard"
  | .addMana types =>
    let g := g.modifyPlayer controller (fun pl =>
      { pl with manaPool :=
        types.foldl (fun pool t => pool.add t) pl.manaPool })
    g.logMsg s!"{(g.player controller).name} adds mana"
  | .searchBasicLandToHand =>
    g.resolveLibrarySearch controller isBasicLandCard "basic land card"
      fun g cardId =>
        let cardName := (g.object! cardId).name
        let (g, _) := g.move cardId (.hand controller) none
        g.logMsg s!"{(g.player controller).name} reveals {cardName} and puts it into their hand"
  | .createTokensX kind =>
    g.createKindTokens controller kind 1
  | .draw n =>
    g.draw controller n
  | .searchTwoBasicsSplit =>
    g.resolveLibrarySearch controller isBasicLandCard "basic land card"
      fun g cardId =>
        let cardName := (g.object! cardId).name
        let (g, _) := g.move cardId .battlefield (some controller)
        let g :=
          match g.findObject? cardId with
          | some o => g.setObject { o with status := { o.status with tapped := true } }
          | none => g
        g.logMsg s!"{(g.player controller).name} puts {cardName} onto the battlefield tapped"
  | .creaturesYouControlGetOppsLoseLife p t life =>
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.isCreature && o.controlledBy controller then
          g := g.pumpPermanent o p t
      for pl in g.livingOpponents controller do
        g := g.loseLife pl.id life
      return g
  | .printed text =>
    g.logMsg text

/-- Top `count` cards of `p`'s library (last = current top). -/
def scryLookedIds (g : Game) (p : PlayerId) (count : Nat) : Array ObjectId :=
  let lib := (g.player p).library
  let n := min count lib.size
  lib.extract (lib.size - n) lib.size

/-- Start an optional “discard a card. If you do, draw `n`” (CR 701.9 / 608.2d). -/
def beginMayDiscardDraw (g : Game) (p : PlayerId) (n : Nat) : Game :=
  let pl := g.player p
  if pl.hand.isEmpty then
    g.logMsg s!"{pl.name} has no card to discard"
  else
    { g with pending := .mayDiscardDraw p n }.logMsg
      s!"{pl.name} may discard a card. If they do, they draw {n}"

/-- Start “sacrifices a creature of their choice” for `p` (CR 701.17 / 608.2d). -/
def beginSacrificeCreature (g : Game) (p : PlayerId) : Game :=
  if (g.sacrificeCreatureChoices p).isEmpty then
    g.logMsg s!"{(g.player p).name} has no creature to sacrifice"
  else
    { g with pending := .sacrificeCreature p }.logMsg
      s!"{(g.player p).name} must sacrifice a creature of their choice"

/-- Apply `f` if the trigger's source is still on the battlefield. -/
def withTriggerSource (g : Game) (sourceId : Option ObjectId)
    (f : Game → GameObject → Game) : Game :=
  g.withSourceOnBattlefield sourceId f
    "The triggered ability's source is no longer in play"

/-- Apply `action` if the trigger's source is still on the battlefield. -/
def applyOnTriggerSource (g : Game) (sourceId : Option ObjectId) (action : PermanentAction) :
    Game :=
  g.applyOnSource sourceId action "The triggered ability's source is no longer in play"

/-- Resolve a triggered ability (CR 608). `sourceId` is the object that generated it. -/
def applyTriggeredAbility (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target := #[])
    (dividedDamage : Array Nat := #[]) (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none)
    (sourceName : String := "This creature") : Game :=
  match ab.resolution with
  | .pumpGreatestPower =>
    g.applyOnTriggerSource sourceId (.pump (g.greatestPowerAmongCreatures controller) 0)
  | .setOtherBasePT =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let (pw, tw) :=
        match sourceId.bind g.findObject? with
        | some src =>
          if src.isOnBattlefield then (g.power src, g.toughness src)
          else (lastKnownPower.getD 0, lastKnownToughness.getD 0)
        | none => (lastKnownPower.getD 0, lastKnownToughness.getD 0)
      let g := g.mapObjectStatus o (fun s => { s with setBasePT := some (pw, tw) })
      g.logMsg
        s!"{o.name}'s base power and toughness become {pw}/{tw} until end of turn")
      "No target was chosen"
  | .damageBlockers n =>
    g.withTriggerSource sourceId fun g o =>
      let blockers := g.blockersOf o.id
      if blockers.isEmpty then
        g.logMsg s!"there are no creatures blocking {o.name}"
      else
        Id.run do
          let mut g := g
          for b in blockers do
            g := g.dealDamageFrom o.name (g.object! b.id) n
              (deathtouch := g.hasDeathtouch o)
          return g
  | .scry n =>
    g.beginScry controller n
  | .draw n =>
    g.draw controller n
  | .searchForest =>
    g.resolveSearchForest controller
  | .mayDiscardDraw n =>
    g.beginMayDiscardDraw controller n
  | .opponentSacrificesCreature =>
    g.withLegalTriggerTarget controller ab sourceId targets (fun g t =>
      match t with
      | Target.player pid => g.beginSacrificeCreature pid
      | _ => g.logMsg "The target is no longer legal")
  | .onPermanent action =>
    g.applyOnPermanent controller ab.targetKind targets action sourceId
      (some "The target is no longer legal")
  | .dividedDamage =>
    Id.run do
      let mut g := g
      for i in [0:targets.size] do
        let t := targets[i]!
        let n := dividedDamage[i]?.getD 0
        if n > 0 then
          g := g.applyEffect controller (.dealDamage n) #[t]
      return g
  | .damageFromLastKnownPower =>
    let n := (lastKnownPower.getD 0).toNat
    g.withLegalTriggerPermanent controller ab sourceId targets fun g o =>
      g.dealDamageFrom sourceName o n
  | .returnElfGainLife =>
    g.withLegalTriggerTarget controller ab sourceId targets fun g t =>
      match t with
      | Target.card oid =>
        match g.findObject? oid with
        | none => g.logMsg "The target is no longer in the graveyard"
        | some o =>
          let n := (g.power o).toNat
          let name := o.name
          let (g, _) := g.move oid (.hand controller) none
          let g := g.logMsg s!"{name} is returned to {(g.player controller).name}'s hand"
          g.gainLife controller n
      | _ => g.logMsg "The target is no longer legal"
  | .damageEachOpponent n =>
    g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid n)
  | .pumpByLookedAt =>
    let n := (lastKnownPower.getD 0).toNat
    g.applyOnTriggerSource sourceId (.pump (n : Int) (n : Int))
  | .onSource action =>
    g.applyOnTriggerSource sourceId action
  | .gainLife n =>
    g.gainLife controller n
  | .targetOpponentSacrifices =>
    g.withLegalTriggerTarget controller ab sourceId targets (fun g t =>
      match t with
      | Target.player pid => g.beginSacrificeCreatures #[pid]
      | _ => g.logMsg "The target is no longer legal")
      "The target is no longer legal"
  | .eachPlayerSacrificesCreature =>
    g.beginSacrificeCreatures (g.apnapOrder)
  | .eachOpponentDiscards =>
    g.beginDiscardCards (g.apnapOrder.filter (· != controller))
  | .exileOppGyCardOppsLoseLife n =>
    let g :=
      match targets[0]? with
      | some (Target.card oid) =>
        match g.findObject? oid with
        | some o =>
          let name := o.name
          let (g, _) := g.move oid .exile none
          g.logMsg s!"{name} is exiled"
        | none => g.logMsg "The target is no longer in the graveyard"
      | _ => g
    g.forEachOpponent controller (fun g pid => g.loseLife pid n)
  | .creaturesYouControlPumpAndFirstStrike pw =>
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.isCreature && o.controlledBy controller then
          g := g.pumpPermanent o pw 0
          let o := g.object! o.id
          g := g.mapObjectStatus o (·.grantUntilEot Keyword.firstStrike)
          g := g.logMsg s!"{o.name} gains first strike until end of turn"
      return g
  | .pumpForEachOtherCreature =>
    g.withTriggerSource sourceId fun g o =>
      let others :=
        g.battlefield.filter (fun c =>
          c.isCreature && c.controlledBy controller && c.id != o.id) |>.size
      g.pumpPermanent o others others
  | .grantFlying =>
    g.applyOnPermanent controller ab.targetKind targets
      (.grantKeywords Keyword.flying) sourceId (some "The target is no longer legal")
  | .mayPayGenericDraw n =>
    { g with pending := .mayPayGeneric controller n }.logMsg
      s!"{(g.player controller).name} may pay \{{n}}. If they do, they draw a card"
  | .drawThenBottomIfNoLegendary =>
    let g := g.draw controller 1
    if g.controlsLegendaryCreature controller then g
    else if (g.player controller).hand.isEmpty then g
    else
      { g with pending := .putOnBottom controller 1 }.logMsg
        s!"{(g.player controller).name} puts a card from their hand on the bottom of their library"
  | .exileUntilLeaves =>
    g.withLegalKindPermanent controller ab.targetKind targets (fun g o =>
      g.exileUntilSourceLeaves sourceId o) sourceId (some "The target is no longer legal")
  | .returnLinkedExile =>
    match sourceId.bind g.findObject? with
    | some src => g.returnLinkedExile src
    | none => g
  | .removeHopeDrawSac =>
    g.withTriggerSource sourceId fun g src =>
      if src.status.hope == 0 then g
      else
        let g := g.setObject { src with status := { src.status with hope := src.status.hope - 1 } }
        let g := g.logMsg s!"{src.name} loses a hope counter"
        let g := g.draw controller 1
        match g.findObject? src.id with
        | some src =>
          if src.status.hope == 0 then
            let g := g.logMsg s!"{src.name} is sacrificed"
            let (g, _) := g.move src.id (.graveyard src.owner) none
            g.gainLife controller 4
          else g
        | none => g
  | .loot =>
    let g := g.draw controller 1
    g.beginDiscardCards #[controller]
  | .tapHumansDraw =>
    { g with pending := .tapHumans controller }.logMsg
      s!"{(g.player controller).name} may tap any number of untapped Humans they control"
  | .pumpAndUnblockable =>
    g.withTriggerSource sourceId fun g o =>
      let g := g.pumpPermanent o 1 0
      g.grantCantBeBlockedThisTurn (g.object! o.id)
  | .recruit =>
    g.beginRecruit controller
  | .youRecruit =>
    g.beginRecruit controller
  | .createTreasureTapped =>
    g.createTreasureTokens controller 1 (tapped := true)
  | .createTreasure =>
    g.createTreasureTokens controller 1
  | .exileTop =>
    g.resolveExileTopPlayUntilEndOfNextTurn controller
  | .untapPlusOneIfSubtype subtype =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let g := g.applyPermanentAction o .untap
      let o := g.object! o.id
      if g.hasSubtype o subtype then g.addPlusOnePlusOneTo o 1 else g)
  | .plusOneEachYouControl =>
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.isCreature && o.controlledBy controller then
          g := g.addPlusOnePlusOneTo o 1
      return g
  | .sourceGetsAndTeamTrample p =>
    let g := g.applyOnTriggerSource sourceId (.pump p 0)
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.isCreature && o.controlledBy controller then
          g := g.mapObjectStatus o (·.grantUntilEot Keyword.trample)
          g := g.logMsg s!"{o.name} gains trample until end of turn"
      return g
  | .drawAndLoseLife =>
    let g := g.draw controller 1
    g.loseLife controller 1
  | .amassGoblins n =>
    g.amassGoblins controller n
  | .createTokens kind n tapped =>
    g.createKindTokens controller kind n (tapped := tapped)
  | .createThenAttach kind =>
    let (g, tok) := g.createToken controller (tokenPrinted kind)
    g.withSourceOnBattlefield sourceId (fun g src => g.attachSourceTo src tok)
      "The Equipment is no longer in play"
  | .amassThenAttach n =>
    let g := g.amassGoblins controller n
    let army :=
      (g.permanentsOf controller).find? (fun o => g.hasSubtype o "Army")
    match army, sourceId.bind g.findObject? with
    | some host, some src =>
      if src.isOnBattlefield then g.attachSourceTo src host else g
    | _, _ => g
  | .attachSourceToTarget =>
    g.withLegalKindPermanent controller ab.targetKind targets (fun g host =>
      g.withSourceOnBattlefield sourceId (fun g src => g.attachSourceTo src host)
        "The Equipment is no longer in play")
      sourceId (some "The target is no longer legal")
  | .searchBasicToHand =>
    g.resolveLibrarySearch controller isBasicLandCard "basic land card"
      fun g cardId =>
        let cardName := (g.object! cardId).name
        let (g, _) := g.move cardId (.hand controller) none
        g.logMsg s!"{(g.player controller).name} reveals {cardName} and puts it into their hand"
  | .gainLifeSearchBasicOnTop n =>
    let g := g.gainLife controller n
    g.resolveLibrarySearch controller isBasicLandCard "basic land card"
      fun g cardId =>
        let cardName := (g.object! cardId).name
        let pl := g.player controller
        let lib := pl.library.filter (· != cardId) |>.push cardId
        let g := g.setPlayer { pl with library := lib }
        g.logMsg s!"{(g.player controller).name} puts {cardName} on top of their library"
  | .plusOneEachOtherGainLife =>
    Id.run do
      let mut g := g
      let mut n : Nat := 0
      for o in g.battlefield do
        if o.isCreature && o.controlledBy controller && some o.id != sourceId then
          g := g.addPlusOnePlusOneTo o 1
          n := n + 1
      return if n == 0 then g else g.gainLife controller n
  | .destroyOppArtifactsEnchantmentsGainLife =>
    Id.run do
      let mut g := g
      let mut n : Nat := 0
      for o in g.battlefield do
        if !o.controlledBy controller &&
            (o.printed.isArtifact || o.printed.isEnchantment) then
          let name := o.name
          let (g', _) := g.move o.id (.graveyard o.owner) none
          g := g'.logMsg s!"{name} is destroyed"
          n := n + 1
      return if n == 0 then g else g.gainLife controller n
  | .damageEqualSubtypeToEachOpponent subtype =>
    let n := g.countSubtype controller subtype
    Id.run do
      let mut g := g
      for pl in g.livingOpponents controller do
        g := g.loseLife pl.id n
      return g
  | .damageEqualTreasures =>
    let n := g.countSubtype controller "Treasure"
    g.applyEffect controller (.dealDamage n) targets
  | .loseLifeCreateTreasure =>
    let g := g.loseLife controller 1
    g.createTreasureTokens controller 1
  | .dealDamageDestroyIfSubtype n subtype =>
    g.withLegalKindTarget controller ab.targetKind targets (fun g tgt =>
      match tgt with
      | Target.player _pid => g.applyEffect controller (.dealDamage n) #[tgt]
      | Target.permanent oid =>
        match g.findObject? oid with
        | none => g.logMsg "The target is no longer legal"
        | some o =>
          let g := g.applyEffect controller (.dealDamage n) #[tgt]
          if g.hasSubtype o subtype then
            match g.findObject? oid with
            | some o =>
              let name := o.name
              let (g, _) := g.move o.id (.graveyard o.owner) none
              g.logMsg s!"{name} is destroyed"
            | none => g
          else g
      | _ => g.logMsg "The target is no longer legal")
  | .attachEquipmentToCreature =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent eqId), some (Target.permanent hostId) =>
      match g.findObject? eqId, g.findObject? hostId with
      | some eq, some host =>
        if eq.isOnBattlefield && host.isOnBattlefield then
          g.attachSourceTo eq host
        else g.logMsg "The target is no longer legal"
      | _, _ => g.logMsg "The target is no longer legal"
    | some (Target.permanent _), none =>
      g.logMsg "No creature was chosen"
    | _, _ => g.logMsg "The target is no longer legal"
  | .addMana types =>
    let g := g.modifyPlayer controller (fun pl =>
      { pl with manaPool :=
        types.foldl (fun pool t => pool.add t) pl.manaPool })
    g.logMsg s!"{(g.player controller).name} adds mana"
  | .defenderSacsLeastPower =>
    g.logMsg "Defending player sacrifices a least-power creature"
  | .createAxe =>
    g.logMsg "An Axe token is created"
  | .tapOppOrUntapYours =>
    g.logMsg "Choose tap an opposing creature or untap yours"
  | .becomePT p t =>
    g.withTriggerSource sourceId fun g o =>
      g.setObject { o with status := { o.status with setBasePT := some (p, t) } }
  | .returnOtherPlusOne =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let owner := o.owner
      let (g, _) := g.move o.id (.hand owner) none
      g.applyOnTriggerSource sourceId (.plusOne 1))
  | .lookAtTopRevealTypes n _types =>
    g.logMsg s!"{(g.player controller).name} looks at the top {n} cards"
  | .pumpAndDamageOpponents n =>
    let g := g.applyOnTriggerSource sourceId (.pump 1 1)
    Id.run do
      let mut g := g
      for pl in g.livingOpponents controller do
        g := g.loseLife pl.id n
      return g
  | .createTappedTreasuresEqualOppArtifacts =>
    let n :=
      g.battlefield.filter (fun o =>
        o.printed.isArtifact && !o.controlledBy controller) |>.size
    g.createTreasureTokens controller n (tapped := true)
  | .gainControlOppUntilEot =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let g := g.applyPermanentAction o .untap
      g.mapObjectStatus (g.object! o.id) (·.grantUntilEot Keyword.haste))
  | .othersGetAndOppsGet subtypes p t oppP oppT =>
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.isCreature && o.controlledBy controller &&
            subtypes.any (fun s => g.hasSubtype o s) && some o.id != sourceId then
          g := g.pumpPermanent o p t
        else if o.isCreature && !o.controlledBy controller then
          g := g.pumpPermanent o oppP oppT
      return g
  | .putNonlandMvAtMostFromGy _mv =>
    g.logMsg "A nonland permanent card may enter from a graveyard"
  | .honeEachEquipment =>
    let eqs :=
      g.battlefield.filter (fun o => o.controlledBy controller && o.printed.isEquipment)
    eqs.foldl (init := g) fun acc eq =>
      acc.mapObjectStatus eq (fun s => { s with hone := s.hone + 1 })
        |>.logMsg s!"{eq.name} received a hone counter"
  | .printed text =>
    g.logMsg text

/-- Put attack-triggered abilities of `attackerIds` onto the stack (CR 508.2),
including “whenever you attack with one or more Elves” (once if any Elf attacks). -/
def putAttackTriggersOnStack (g : Game) (p : PlayerId) (attackerIds : Array ObjectId) : Game :=
  Id.run do
    let mut g := g
    for id in attackerIds do
      let o := g.object! id
      g := g.putMatchingSourceTriggers p o .attacking
        (some (g.snapshotPower o)) (some (g.snapshotToughness o))
    let attackedWithElves := attackerIds.any (fun id => g.hasSubtype (g.object! id) "Elf")
    if attackedWithElves then
      g := g.putControlledTriggers p .youAttackWithElves
    if attackerIds.size >= 2 then
      g := g.putControlledTriggers p .youAttackWithTwoOrMore
    if !attackerIds.isEmpty then
      g := g.putControlledTriggers p .youAttack
    return g

/-- Put becomes-blocked triggers for unique attackers in `assignments` (CR 509.5c). -/
def putBlockedTriggersOnStack (g : Game) (assignments : Array (ObjectId × ObjectId)) : Game :=
  Id.run do
    let mut g := g
    let mut seen : Array ObjectId := #[]
    for (_, attackerId) in assignments do
      if !seen.contains attackerId then
        seen := seen.push attackerId
        let o := g.object! attackerId
        match o.controller with
        | none => pure ()
        | some p =>
          g := g.putMatchingSourceTriggers p o .becomesBlocked
    return g

/-- Whether `host` is a legal Enchant-creature attachment (CR 303.4). -/
def isLegalAuraHost (host : GameObject) : Bool :=
  host.isOnBattlefield && host.isCreature

/-- Resolve an Aura spell, attaching it or putting it into the graveyard (CR 303.4, 608.3a). -/
def resolveAuraSpell (g : Game) (entry : StackEntry) (obj : GameObject) : Game :=
  let toGraveyard (g : Game) : Game :=
    g.moveToOwnerGraveyard obj s!"{obj.name} goes to the graveyard (illegal Aura target)"
  match entry.targets[0]? with
  | some (Target.permanent hostId) =>
    match g.findObject? hostId with
    | some host =>
      if isLegalAuraHost host then
        let (g, newId) := g.putOntoBattlefield obj.id entry.controller
          (attachedTo := some host.id)
        let o := g.object! newId
        let g := g.logMsg s!"{o.name} enters the battlefield attached to {host.name}"
        g.afterPermanentEnters (g.object! newId)
      else
        toGraveyard g
    | none => toGraveyard g
  | _ => toGraveyard g

/-- Resolve an Adventure: apply its effect, then exile the card and grant
permission to cast the permanent (CR 715.3d). -/
def resolveAdventureSpell (g : Game) (entry : StackEntry) (obj : GameObject) : Game :=
  let orig := obj.adventurerCard.getD obj.printed
  let g := g.setObject { obj with printed := orig, adventurerCard := none }
  let obj := g.object! obj.id
  let (g, newId) := g.move obj.id .exile none
  let o := g.object! newId
  let g := g.setObject { o with
    playPermission := some {
      player := entry.controller
      turnEndsRemaining := 0
      fromAdventure := true } }
  g.logMsg
    s!"{o.name} is exiled. {(g.player entry.controller).name} may cast it for as long as it remains exiled (CR 715.3d)"

def resolveTop (g : Game) : Game :=
  if g.stack.isEmpty then g
  else
    let entry := g.stack.back!
    let g := { g with stack := g.stack.pop }
    match g.findObject? entry.objectId with
    | none => g.logMsg "The spell left the stack unexpectedly"
    | some obj =>
      if let some e := obj.abilityEffect then
        let g := g.applyAbilityEffect entry.controller e entry.targets obj.sourceId
        -- CR 608.2m: after resolution the ability ceases to exist.
        g.ceaseToExist obj.id
      else if let some t := obj.triggeredAbility then
        let srcName := obj.printed.name.replace "'s ability" ""
        let g := g.applyTriggeredAbility entry.controller t obj.sourceId
          entry.targets entry.dividedDamage obj.lastKnownPower obj.lastKnownToughness srcName
        g.ceaseToExist obj.id
      else
        let g :=
          match spellEffectOf obj entry.chosenMode with
          | some e => g.applyEffect entry.controller e entry.targets
            (castFromGraveyard := obj.castFromGraveyard)
          | none => g
        if obj.isAdventureSpell then
          g.resolveAdventureSpell entry (g.object! obj.id)
        else if obj.printed.isAura then
          g.resolveAuraSpell entry obj
        else if obj.printed.isPermanentCard && !obj.printed.isLand then
          let sick := !obj.printed.keywords.haste
          let (g, newId) := g.putOntoBattlefield obj.id entry.controller
            (tapped := g.entersTapped entry.controller obj.printed) (summoningSick := sick)
          let o := g.object! newId
          let g := g.logMsg s!"{o.name} enters the battlefield"
          g.afterPermanentEnters (g.object! newId)
        else if obj.castFromGraveyard then
          let (g, _) := g.move obj.id .exile none
          g.logMsg s!"{obj.name} is exiled (flashback)"
        else
          g.moveToOwnerGraveyard obj s!"{obj.name} goes to the graveyard"

def declareAttackers (g : Game) (p : PlayerId) (ids : Array ObjectId) : Except String Game := do
  if g.pending != .declareAttackers || g.activePlayer != p then
    throw "Not time to declare attackers"
  let mut g := g
  for id in ids do
    let o := g.object! id
    if !g.canAttack o then
      throw s!"{o.name} cannot attack"
    g := g.setObject { o with status := { o.status with
      attacking := true
      tapped := o.status.tapped || !g.hasVigilance o } }
    g := g.logMsg s!"{g.player p |>.name} attacks with {o.name}"
  if ids.isEmpty then
    g := g.logMsg s!"{g.player p |>.name} does not attack"
  g := g.putAttackTriggersOnStack p ids
  g := { g with pending := .none }
  g := g.promptTriggerTargetsIfNeeded
  if g.pending != .none then
    return g
  return g.receivePriority p

def declareBlockers (g : Game) (p : PlayerId) (assignments : Array (ObjectId × ObjectId)) :
    Except String Game := do
  if g.pending != .declareBlockers then
    throw "Not time to declare blockers"
  if p != g.opponent g.activePlayer then
    throw "Only the defending player declares blockers"
  let mut g := g
  for (blockerId, attackerId) in assignments do
    let b := g.object! blockerId
    let a := g.object! attackerId
    if !g.canBlock b a then
      throw s!"{b.name} cannot block {a.name}"
    g := g.setObject { b with status := { b.status with blocking := #[attackerId] } }
    let aNow := g.object! attackerId
    g := g.setObject { aNow with status := { aNow.status with blocked := true } }
    g := g.logMsg s!"{b.name} blocks {a.name}"
  -- CR 509.1c / 702.111: a menace (or “except by N or more”) creature that is
  -- blocked must be blocked by at least that many creatures.
  for o in g.battlefield do
    if o.status.attacking then
      let need := g.minBlockersRequired o
      if need > 1 then
        let n := (g.blockersOf o.id).size
        if n > 0 && n < need then
          let word := if need == 2 then "two" else toString need
          throw s!"{o.name} can't be blocked except by {word} or more creatures"
  if assignments.isEmpty then
    g := g.logMsg s!"{g.player p |>.name} does not block"
  g := g.putBlockedTriggersOnStack assignments
  return { g with pending := .none } |>.receivePriority g.activePlayer

/-- Sum of combat damage this assignment sends to creatures. -/
def creatureDamageTotal (asgn : CreatureCombatAssignment) : Int :=
  asgn.toCreatures.foldl (fun acc (_, n) => acc + n) 0

/-- A legal default assignment for `source` (CR 510.1c–d, 702.19).
Without trample, all damage goes to the first remaining recipient — one
legal division under 510.1c/d. With trample, lethal is assigned to each
blocker before leftover goes to the defending player. -/
def defaultCombatAssignment (g : Game) (source : GameObject) (forAttackers : Bool)
    (already : Array CreatureCombatAssignment) : CreatureCombatAssignment :=
  let dmg := max (g.power source) 0
  if forAttackers then
    let blockers := g.blockersOf source.id
    if blockers.isEmpty then
      if source.status.blocked && !g.hasTrample source then
        { source := source.id }
      else
        { source := source.id, toPlayer := dmg }
    else if g.hasTrample source then
      Id.run do
        let mut remaining := dmg
        let mut toCreatures : Array (ObjectId × Int) := #[]
        let mut already := already
        for b in blockers do
          let need := g.lethalRemaining b already (fromDeathtouch := g.hasDeathtouch source)
          let amt := min remaining need
          toCreatures := toCreatures.push (b.id, amt)
          already := already.push { source := source.id, toCreatures := #[(b.id, amt)] }
          remaining := remaining - amt
        return { source := source.id, toCreatures := toCreatures, toPlayer := remaining }
    else
      { source := source.id, toCreatures := #[(blockers[0]!.id, dmg)] }
  else
    let targets := g.creaturesBlockedBy source
    if targets.isEmpty then { source := source.id }
    else { source := source.id, toCreatures := #[(targets[0]!.id, dmg)] }

/-- Fill in a default for every assigning creature not listed in `listed`. -/
def completeCombatAssignments (g : Game) (forAttackers : Bool)
    (listed : Array CreatureCombatAssignment) : Except String (Array CreatureCombatAssignment) := do
  let mut acc : Array CreatureCombatAssignment := #[]
  let mut seen : Array ObjectId := #[]
  let assigning := g.creaturesAssigningCombatDamage forAttackers
  for a in listed do
    if seen.contains a.source then
      throw "Duplicate combat damage source"
    if !assigning.any (fun o => o.id == a.source) then
      throw "That creature does not assign combat damage now"
    seen := seen.push a.source
    acc := acc.push a
  for o in assigning do
    if !seen.contains o.id then
      let asgn := g.defaultCombatAssignment o forAttackers acc
      acc := acc.push asgn
      seen := seen.push o.id
  return acc

/-- Check one creature's assignment against CR 510.1a–d and trample (702.19b).
`batch` is the complete assignment for this half of 510.1, so lethal can
include damage from other creatures (CR 510.1e / 702.19b). -/
def checkCombatAssignment (g : Game) (asgn : CreatureCombatAssignment) (forAttackers : Bool)
    (batch : Array CreatureCombatAssignment) : Except String Unit := do
  let some src := g.findObject? asgn.source | throw "no such object"
  if !src.isOnBattlefield then
    throw s!"{src.name} is not on the battlefield"
  let dmg := max (g.power src) 0
  if asgn.toPlayer < 0 || asgn.toCreatures.any (fun (_, n) => n < 0) then
    throw "Combat damage amounts cannot be negative"
  let mut seenTargets : Array ObjectId := #[]
  for (tid, _) in asgn.toCreatures do
    if seenTargets.contains tid then
      throw "Duplicate combat damage recipient"
    seenTargets := seenTargets.push tid
  let recipients := g.legalCombatDamageRecipients src forAttackers
  for (tid, _) in asgn.toCreatures do
    if !recipients.any (fun r => r.id == tid) then
      if forAttackers then
        throw s!"{src.name} must assign combat damage to the creatures blocking it (CR 510.1c)"
      else
        throw s!"{src.name} must assign combat damage to the creatures it's blocking (CR 510.1d)"
  let toCreatures := creatureDamageTotal asgn
  if forAttackers then
    if !src.status.attacking then
      throw s!"{src.name} is not attacking"
    if recipients.isEmpty then
      if asgn.toCreatures.size != 0 then
        throw s!"{src.name} has no blocking creatures to assign combat damage to"
      if src.status.blocked && !g.hasTrample src then
        if asgn.toPlayer != 0 then
          throw s!"{src.name} is blocked with no remaining blockers and assigns no combat damage (CR 510.1c)"
      else if asgn.toPlayer != dmg then
        throw s!"{src.name} must assign combat damage equal to its power (CR 510.1a)"
    else
      if toCreatures + asgn.toPlayer != dmg then
        throw s!"{src.name} must assign combat damage equal to its power (CR 510.1a)"
      if asgn.toPlayer > 0 then
        if !g.hasTrample src then
          throw s!"{src.name} cannot assign combat damage to the defending player"
        if recipients.any (fun b => g.lethalRemaining b batch > 0) then
          throw s!"{src.name} must assign lethal damage to each blocking creature before trampling (CR 702.19b)"
  else
    if src.status.blocking.isEmpty then
      throw s!"{src.name} is not blocking"
    if asgn.toPlayer != 0 then
      throw s!"{src.name} assigns combat damage to the creatures it's blocking (CR 510.1d)"
    if recipients.isEmpty then
      if toCreatures != 0 then
        throw s!"{src.name} is not blocking any creatures and assigns no combat damage (CR 510.1d)"
    else if toCreatures != dmg then
      throw s!"{src.name} must assign combat damage equal to its power (CR 510.1a)"

/-- CR 510.1e: the total assignment is legal only if every creature complies. -/
def checkCombatAssignmentBatch (g : Game) (forAttackers : Bool)
    (batch : Array CreatureCombatAssignment) : Except String Unit := do
  for a in batch do
    let _ ← checkCombatAssignment g a forAttackers batch
  let expected := (g.creaturesAssigningCombatDamage forAttackers).map (·.id)
  if batch.size != expected.size || !expected.all (fun id => batch.any (·.source == id)) then
    throw "Every attacking or blocking creature must assign combat damage (CR 510.1)"

/-- Apply assigned combat damage simultaneously (CR 510.2). -/
def dealAssignedCombatDamage (g : Game) : Game :=
  Id.run do
    let mut g := g
    let defn := g.opponent g.activePlayer
    for asgn in g.assignedCombatDamage do
      let src := g.object! asgn.source
      let mut totalDealt : Int := 0
      let recipients :=
        if src.status.attacking then g.blockersOf src.id else g.creaturesBlockedBy src
      if src.status.attacking && src.status.blocked && recipients.isEmpty &&
          asgn.toPlayer == 0 then
        g := g.logMsg
          s!"{src.name} is blocked with no remaining blockers and assigns no combat damage (CR 510.1c)"
      else if !src.status.blocking.isEmpty && recipients.isEmpty then
        g := g.logMsg
          s!"{src.name} is not blocking any creatures and assigns no combat damage (CR 510.1d)"
      for (tid, amt) in asgn.toCreatures do
        if amt > 0 then
          let t := g.object! tid
          g := g.markDamageOn t amt
            s!"{src.name} deals {amt} combat damage to {t.name}"
            (deathtouch := g.hasDeathtouch src)
          totalDealt := totalDealt + amt
      if asgn.toPlayer > 0 then
        let pl := g.player defn
        g := g.setPlayer { pl with life := pl.life - asgn.toPlayer }
        totalDealt := totalDealt + asgn.toPlayer
        if src.status.blocked then
          g := g.logMsg
            s!"{src.name} tramples for {asgn.toPlayer} to {pl.name} ({(g.player defn).life} life)"
        else
          g := g.logMsg
            s!"{src.name} deals {asgn.toPlayer} combat damage to {pl.name} ({(g.player defn).life} life)"
      if g.hasLifelink src && totalDealt > 0 then
        match src.controller with
        | some pid => g := g.gainLife pid totalDealt.toNat
        | none => pure ()
      if asgn.toPlayer > 0 then
        match src.controller with
        | some pid =>
          g := g.putMatchingSourceTriggers pid src .dealsCombatDamageToPlayer
        | none => pure ()
    let pendingRegular :=
      g.combatHasFirstStrike && !g.firstStrikeDamageDone
    g := { g with
      assignedCombatDamage := #[]
      pending := .none
      firstStrikeDamageDone := g.firstStrikeDamageDone || g.combatHasFirstStrike
      pendingRegularCombatDamage := pendingRegular }
    return g.receivePriority g.activePlayer

/-- Record a legal assignment batch and append it for later dealing. -/
def storeCombatAssignments (g : Game) (forAttackers : Bool)
    (listed : Array CreatureCombatAssignment) : Except String Game := do
  let batch ← g.completeCombatAssignments forAttackers listed
  let _ ← checkCombatAssignmentBatch g forAttackers batch
  return { g with assignedCombatDamage := g.assignedCombatDamage ++ batch }

/-- After attackers have assigned, the defending player assigns (CR 510.1d)
or damage is dealt if they have no division to announce. -/
def finishAttackerCombatAssignment (g : Game) : Game :=
  let defender := g.opponent g.activePlayer
  if g.needsCombatDamageChoice false then
    { g with pending := .assignCombatDamage defender false }
      |>.logMsg s!"{(g.player defender).name} assigns combat damage (CR 510.1d)"
  else
    match g.storeCombatAssignments false #[] with
    | .ok g' => g'.dealAssignedCombatDamage
    | .error e => g.logMsg s!"Combat damage assignment failed: {e}"

/-- Start CR 510.1: the active player assigns attacking creatures first. -/
def beginCombatDamageAssignment (g : Game) : Game :=
  let g := { g with assignedCombatDamage := #[], pending := .none }
  if g.needsCombatDamageChoice true then
    { g with pending := .assignCombatDamage g.activePlayer true }
      |>.logMsg s!"{(g.player g.activePlayer).name} assigns combat damage (CR 510.1c)"
  else
    match g.storeCombatAssignments true #[] with
    | .ok g' => g'.finishAttackerCombatAssignment
    | .error e => g.logMsg s!"Combat damage assignment failed: {e}"

/-- Assign and deal combat damage (CR 510.1–510.2). -/
def combatDamage (g : Game) : Game :=
  g.beginCombatDamageAssignment

/-- Announce how attacking or blocking creatures assign combat damage (CR 510.1). -/
def announceCombatDamage (g : Game) (p : PlayerId)
    (listed : Array CreatureCombatAssignment) : Except String Game := do
  match g.pending with
  | .assignCombatDamage q forAttackers =>
    if p != q then
      throw s!"Only {(g.player q).name} may assign combat damage (CR 510.1)"
    let g ← g.storeCombatAssignments forAttackers listed
    if forAttackers then
      return g.finishAttackerCombatAssignment
    else
      return g.dealAssignedCombatDamage
  | _ => throw "Not time to assign combat damage (CR 510.1)"

def clearCombat (g : Game) : Game :=
  Id.run do
    let mut g := { g with firstStrikeDamageDone := false, pendingRegularCombatDamage := false }
    for o in g.battlefield do
      if o.status.attacking || !o.status.blocking.isEmpty || o.status.blocked then
        g := g.setObject { o with
          status := { o.status with attacking := false, blocking := #[], blocked := false } }
    return g

def clearEOT (g : Game) : Game :=
  Id.run do
    let mut g := { g with creaturesWithoutFlyingCantBlock := false }
    for o in g.battlefield do
      if o.status.clearsAtCleanup then
        g := g.mapObjectStatus o Status.clearedAtCleanup
    return g

/-- Discard down to maximum hand size (CR 514.1). This turn-based action does
not use the stack; the engine discards from the back of the hand array. -/
def discardToMaxHandSize (g : Game) : Game :=
  let pl := g.player g.activePlayer
  let extra := pl.hand.size - pl.maxHandSize
  if extra == 0 then g
  else
    Id.run do
      let mut g := g
      for _ in [0:extra] do
        let pl := g.player g.activePlayer
        if let some last := pl.hand.back? then
          let card := g.object! last
          let (g', _) := g.move last (.graveyard pl.id) none
          g := g'.logMsg s!"{pl.name} discards {card.name} (cleanup)"
      return g

/-- Clear “once each turn” activation counts as a turn ends. -/
def clearTurnActivations (g : Game) : Game :=
  Id.run do
    let mut g := { g with creatureDiedThisTurn := false }
    for pl in g.players do
      if pl.cardsDrawnThisTurn != 0 then
        g := g.setPlayer { pl with
          cardsDrawnThisTurn := 0
          spellsCastThisTurn := 0
          noncreatureSpellsCastThisTurn := 0 }
    for o in g.battlefield do
      if o.status.activationsThisTurn != 0 || o.status.firedOnceEachTurn then
        g := g.setObject { o with status := { o.status with
          activationsThisTurn := 0
          firedOnceEachTurn := false } }
    return g

/-- Expire or decrement play-from-exile permissions as `endingPlayer`'s turn ends. -/
def expirePlayPermissions (g : Game) (endingPlayer : PlayerId) : Game :=
  Id.run do
    let mut g := g
    for o in g.objects do
      match o.playPermission with
      | none => pure ()
      | some perm =>
        if perm.fromAdventure || perm.whileExiled then
          pure ()
        else if perm.player == endingPlayer then
          if perm.turnEndsRemaining ≤ 1 then
            g := g.setObject { o with playPermission := none }
            if o.zone == .exile then
              g := g.logMsg s!"{o.name} can no longer be played from exile"
          else
            g := g.setObject { o with
              playPermission := some { perm with
                turnEndsRemaining := perm.turnEndsRemaining - 1 } }
    return g

/-- Advance to the next living player's turn after a cleanup step ends. -/
def startNextTurn (g : Game) : Game :=
  let ending := g.activePlayer
  let g := g.expirePlayPermissions ending |>.clearTurnActivations
  let nxt := g.nextLiving ending
  let g := { g with
    activePlayer := nxt
    turnNumber := g.turnNumber + 1
    isFirstTurn := false
    cleanupGivesPriority := false }
  g.logMsg s!"It is now {g.player nxt |>.name}'s turn {g.turnNumber}"

/-- `partial` because a silent cleanup (CR 514.3) immediately begins the next
turn, and a skipped draw step (CR 103.8a / 500.11) immediately begins
precombat main; both re-enter `beginStep`. -/
partial def beginStep (g : Game) (st : Step) : Game :=
  let g := { g with
    step := st
    pending := .none
    consecutivePasses := 0
    cleanupGivesPriority := false
    proposedSpell := none }
  let g := g.logMsg s!"— Turn {g.turnNumber}, {g.player g.activePlayer |>.name}: {st} —"
  match st with
  | .untap =>
    Id.run do
      let mut g := g
      let ap := g.activePlayer
      let apName := (g.player ap).name
      g := g.modifyPlayer ap (fun pl =>
        { pl with landsPlayedThisTurn := 0, additionalLandsThisTurn := 0 })
      for o in g.permanentsOf ap do
        -- CR 502.2: the active player untaps their permanents. Logging each
        -- previously tapped permanent makes the battlefield status change
        -- visible in the demo before the zone reprint.
        let skipUntap :=
          o.staticAbilities.any StaticAbility.doesntUntapUnlessEnduringStory? &&
            !g.hasEnduringStory ap
        if o.status.tapped && !skipUntap then
          g := g.logMsg s!"{apName} untaps {o.name}"
        let tapped := if skipUntap then o.status.tapped else false
        g := g.setObject { o with status := { o.status with tapped := tapped, summoningSick := false } }
      -- No priority (CR 502.4). Immediately continue.
      return g
  | .draw =>
    if g.skipsFirstDraw then
      -- CR 103.8a / 500.11 / 614.10: to skip a step is to proceed past it as
      -- though it didn't exist. Nothing happens during it — no turn-based
      -- draw, and no player receives priority.
      g.logMsg s!"{g.player g.activePlayer |>.name} skips their first draw step (CR 103.8a)"
        |>.beginStep .precombatMain
    else
      g.draw g.activePlayer |>.receivePriority g.activePlayer
  | .declareAttackers =>
    { g with pending := .declareAttackers }
  | .declareBlockers =>
    if (g.battlefield.filter (·.status.attacking)).isEmpty then
      g.logMsg "No attackers; skipping declare blockers and combat damage (CR 508.8)"
    else
      { g with pending := .declareBlockers }
  | .combatDamage =>
      g.beginCombatDamageAssignment
  | .upkeep =>
    let ap := g.activePlayer
    let g := g.putControlledTriggers ap .yourUpkeep
    g.receivePriority ap
  | .beginningOfCombat =>
    let ap := g.activePlayer
    let g := g.putControlledTriggers ap .yourBeginCombat
    g.receivePriority ap
  | .end =>
    let ap := g.activePlayer
    let g := g.putControlledTriggers ap .yourEndStep
    g.receivePriority ap
  | .cleanup =>
    -- Combatants leave combat; then CR 514.1–514.3.
    let g := g.clearCombat
    let g := g.discardToMaxHandSize
    let g := g.clearEOT
    -- CR 514.3 / 514.3a / 704.3: normally no priority. If state-based actions
    -- would be performed or triggered abilities are waiting, perform them,
    -- put the triggers on the stack, and the active player receives priority.
    let (g, sba) := g.checkSBACounted
    if g.over then g
    else if sba || g.hasWaitingTriggers then
      let g := { g with cleanupGivesPriority := true }
      let g := g.logMsg "Players receive priority during cleanup (CR 514.3a)"
      g.receivePriority g.activePlayer
    else
      -- The cleanup step ends (CR 500.3) and the turn ends.
      let g := g.emptyManaPools
      (g.startNextTurn).beginStep .untap |>.beginStep .upkeep
  | .precombatMain =>
    let ap := g.activePlayer
    let g := g.putControlledTriggers ap .yourFirstMain
    g.receivePriority ap
  | _ =>
    g.receivePriority g.activePlayer

def beginTurn (g : Game) : Game :=
  -- No player receives priority during untap (CR 502.4).
  (g.beginStep .untap).beginStep .upkeep

/-- Advance after both players pass with an empty stack (CR 500.2). -/
def advanceStep (g : Game) : Game :=
  let g := g.emptyManaPools
  match g.step.next? with
  | some st =>
    -- Skip declare blockers / combat damage when no attackers.
    let attackers := g.battlefield.filter (·.status.attacking)
    if g.step == .declareAttackers && attackers.isEmpty then
      g.beginStep .endOfCombat
    else if g.step == .declareBlockers && attackers.isEmpty then
      g.beginStep .endOfCombat
    else if g.step == .combatDamage && g.pendingRegularCombatDamage then
      { g with pendingRegularCombatDamage := false }.beginCombatDamageAssignment
    else
      g.beginStep st
  | none =>
    -- Leaving cleanup. If CR 514.3a granted priority this step, another
    -- cleanup step begins; otherwise the turn ends (CR 514.3 / 500.3).
    if g.cleanupGivesPriority then
      g.beginStep .cleanup
    else
      g.startNextTurn |>.beginTurn

/-- Pay the proposed spell or ability (CR 601.2h / 602.2b). If the cost
cannot be paid, the action is reversed (CR 733.1). -/
def pay (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .activateManaAbilities caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may pay (CR 601.2h)"
    g.finishProposedSpell
  | .chooseMode _ =>
    throw "Choose a mode first (CR 601.2b)"
  | .chooseTargets _ =>
    throw "Choose a target first (CR 601.2c)"
  | .chooseAdditionalCost _ =>
    throw "Choose an additional cost first (CR 601.2b)"
  | _ => throw "No spell or ability is waiting to be paid for (CR 601.2h)"

/-- Announce whether to pay extra generic mana or sacrifice an artifact or
creature as an additional cost (CR 601.2b), before targets (CR 601.2c). -/
def announceAdditionalCost (g : Game) (p : PlayerId) (payGeneric : Bool) :
    Except String Game := do
  match g.pending with
  | .chooseAdditionalCost q =>
    if p != q then
      throw s!"Only {(g.player q).name} may choose an additional cost (CR 601.2b)"
    let some prop := g.proposedSpell
      | throw "No spell is waiting for an additional cost (CR 601.2b)"
    let some spell := g.findObject? prop.spellId
      | throw "The spell left the stack"
    match spell.printed.additionalCostOrPayGeneric with
    | none => throw "That spell has no alternative additional cost"
    | some n =>
      if payGeneric then
        let prop := { prop with
          cost := prop.cost.addGeneric n
          needsSacrificeOther := false }
        let g := { g with proposedSpell := some prop }
        let g := g.logMsg
          s!"{(g.player p).name} chooses to pay \{{n}} as an additional cost (CR 601.2b)"
        return g.afterAdditionalCostAnnounced
      else
        if (g.sacrificeCreatureOrArtifactChoices p prop.spellId).isEmpty then
          throw s!"{spell.name} requires sacrificing an artifact or creature"
        let prop := { prop with needsSacrificeOther := true }
        let g := { g with proposedSpell := some prop }
        let g := g.logMsg
          s!"{(g.player p).name} chooses to sacrifice an artifact or creature (CR 601.2b)"
        return g.afterAdditionalCostAnnounced
  | _ => throw "Not time to choose an additional cost (CR 601.2b)"

def pass (g : Game) (p : PlayerId) : Except String Game := do
  if g.over then
    throw "The game is over"
  if g.pending != .none then
    throw "A required choice is still pending"
  if !g.playersReceivePriority then
    throw "No player receives priority right now (CR 117.3a / 514.3)"
  if g.priority != p then
    throw "You don't have priority"
  let g := g.logMsg s!"{g.player p |>.name} passes priority"
  let g := { g with consecutivePasses := g.consecutivePasses + 1 }
  if g.consecutivePasses ≥ g.livingPlayers.size then
    if !g.stack.isEmpty then
      let g := g.resolveTop
      if g.pending != .none then
        return g
      return g.receivePriority g.activePlayer
    else
      return g.advanceStep
  else
    return { g with priority := g.nextLiving p }

def concede (g : Game) (p : PlayerId) : Game :=
  let pl := g.player p
  let g := g.setPlayer { pl with lost := true }
  let g := g.logMsg s!"{pl.name} concedes (CR 104.3a)"
  g.checkSBA

/-- True while players are still keeping or taking mulligans (CR 103.5). -/
def openingHandsPending (g : Game) : Bool :=
  match g.pending with
  | .declareMulligan _ => true
  | .putOnBottom _ _ =>
    !g.mulliganToBottom.isEmpty || !g.mulliganToDeclare.isEmpty
  | _ => false

/-- Players who have not yet kept an opening hand, in turn order from the
starting player (CR 103.5). -/
def playersStillDecidingMulligan (g : Game) : Array PlayerId :=
  g.playersInOrderFrom g.startingPlayer (fun pl => !pl.lost && !pl.keptOpeningHand)

def promptMulligan (g : Game) (p : PlayerId) : Game :=
  { g with pending := .declareMulligan p }
    |>.logMsg s!"{g.player p |>.name} may keep or take a mulligan (CR 103.5)"

def promptBottom (g : Game) (p : PlayerId) : Game :=
  let n := (g.player p).mulligansTaken
  let cards := if n == 1 then "1 card" else s!"{n} cards"
  { g with pending := .putOnBottom p n }
    |>.logMsg s!"{g.player p |>.name} puts {cards} on the bottom of their library (CR 103.5)"

/-- After every remaining player has kept, the starting player takes their
first turn (CR 103.8). -/
def finishOpeningHands (g : Game) : Game :=
  let g := { g with
    pending := .none
    mulliganToDeclare := #[]
    willMulligan := #[]
    mulliganToBottom := #[] }
  let g := g.logMsg s!"{g.player g.startingPlayer |>.name} takes the first turn"
  g.beginTurn

/-- Start (or restart) a CR 103.5 round: eligible players declare in turn
order. When nobody remains, the game begins. -/
def beginMulliganRound (g : Game) : Game :=
  if g.over then g
  else
    let remaining := g.playersStillDecidingMulligan
    if remaining.isEmpty then
      g.finishOpeningHands
    else
      promptMulligan
        { g with
          mulliganToDeclare := remaining
          willMulligan := #[]
          mulliganToBottom := #[] }
        remaining[0]!

/-- Shuffle the cards in `p`'s hand back into their library (CR 103.5). -/
def returnHandToLibrary (g : Game) (p : PlayerId) : Game :=
  Id.run do
    let mut g := g
    let ids := (g.player p).hand
    for id in ids do
      let (g', _) := g.move id (.library p)
      g := g'
    return g

/-- A player may mulligan until that mulligan would leave a zero-card opening
hand, after which they may not take further mulligans (CR 103.5). -/
def canTakeMulligan (g : Game) (p : PlayerId) : Bool :=
  let pl := g.player p
  !g.over && !pl.keptOpeningHand && pl.mulligansTaken < pl.startingHandSize

/-- Perform one already-declared mulligan: shuffle, then draw a new starting
hand (CR 103.5). Bottoming is a later choice. -/
def executeOneMulligan (g : Game) (p : PlayerId) : Game :=
  let n := (g.player p).mulligansTaken + 1
  let size := (g.player p).startingHandSize
  let g := g.modifyPlayer p (fun pl => { pl with mulligansTaken := n })
  let g := g.logMsg s!"{g.player p |>.name} takes a mulligan ({n})"
  let g := g.returnHandToLibrary p
  let g := g.shuffleLibrary p
  g.draw p size

/-- After every remaining player has declared, those who chose to mulligan
do so at the same time (CR 103.5). -/
def resolveDeclaredMulligans (g : Game) : Game :=
  if g.willMulligan.isEmpty then
    g.beginMulliganRound
  else
    let order := g.playersStillDecidingMulligan.filter (fun p => g.willMulligan.contains p)
    let g := g.logMsg
      "Players who chose to mulligan do so at the same time (CR 103.5)"
    let g :=
      Id.run do
        let mut g := g
        for p in order do
          g := g.executeOneMulligan p
        return g
    if order.isEmpty then
      g.beginMulliganRound
    else
      promptBottom { g with willMulligan := #[], mulliganToBottom := order } order[0]!

/-- Remove `who` from a sequential CR 103.5 queue, then finish or prompt the
next player. -/
def advancePlayerQueue (g : Game) (who : PlayerId) (queue : Array PlayerId)
    (store : Game → Array PlayerId → Game) (whenEmpty : Game → Game)
    (prompt : Game → PlayerId → Game) : Game :=
  if g.over then g
  else
    let rest := queue.filter (fun q => q != who)
    let g := store g rest
    if rest.isEmpty then whenEmpty g else prompt g rest[0]!

/-- After `who` has declared keep or mulligan, the next declarer in this round
acts. When the round's declarations are complete, pending mulligans are taken
together. -/
def afterDeclaration (g : Game) (who : PlayerId) : Game :=
  g.advancePlayerQueue who g.mulliganToDeclare
    (fun g rest => { g with mulliganToDeclare := rest })
    (·.resolveDeclaredMulligans) (·.promptMulligan)

/-- After `who` has put cards on the bottom, the next such player acts, or a
new declaration round begins. -/
def afterBottom (g : Game) (who : PlayerId) : Game :=
  g.advancePlayerQueue who g.mulliganToBottom
    (fun g rest => { g with mulliganToBottom := rest })
    (·.beginMulliganRound) (·.promptBottom)

def uniqueObjectIds (ids : Array ObjectId) : Bool :=
  Id.run do
    let mut seen : Array ObjectId := #[]
    for id in ids do
      if seen.contains id then
        return false
      seen := seen.push id
    return true

def isPermutation (a b : Array ObjectId) : Bool :=
  a.size == b.size && uniqueObjectIds a && a.all (fun x => b.contains x)

/-- Finish scrying: put `bottom` on the bottom (first = new bottom) and `top`
on top (last = new top) of the library, each pile in the given order (CR 701.20). -/
def finishScry (g : Game) (p : PlayerId) (top bottom : Array ObjectId) :
    Except String Game := do
  match g.pending with
  | .scry q count =>
    if p != q then
      throw s!"Only {(g.player q).name} may scry"
    if !uniqueObjectIds (top ++ bottom) then
      throw "Duplicate card"
    let looked := g.scryLookedIds p count
    if !isPermutation (top ++ bottom) looked then
      throw "Scry must rearrange the cards you looked at (CR 701.20)"
    let pl := g.player p
    let lower := pl.library.extract 0 (pl.library.size - count)
    let mut g := g
    for id in bottom do
      g := g.logMsg
        s!"{(g.player p).name} puts {(g.object! id).name} on the bottom of their library"
    if top != looked then
      for id in top do
        g := g.logMsg
          s!"{(g.player p).name} puts {(g.object! id).name} on top of their library"
    g := g.setPlayer { (g.player p) with library := bottom ++ lower ++ top }
    g := { g with pending := .none }
    match g.pendingDrawAfterScry with
    | some (q, n) =>
      g := { g with pendingDrawAfterScry := none }
      g := g.draw q n
      return g.receivePriority g.activePlayer
    | none =>
      return g.receivePriority g.activePlayer
  | _ => throw "Not time to scry (CR 701.20)"

/-- Discard `id` from hand; if this finishes a pending “may discard, then draw”,
draw that many cards (CR 701.9). -/
def discardForDraw (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  match g.pending with
  | .mayDiscardDraw q n =>
    if p != q then
      throw s!"Only {(g.player q).name} may discard"
    let pl := g.player p
    if !pl.hand.contains id then
      throw "That card is not in your hand"
    let some card := g.findObject? id | throw "no such object"
    let g := g.logMsg s!"{(g.player p).name} discards {card.name}"
    let (g, _) := g.move id (.graveyard card.owner) none
    let g := g.draw p n
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | .chooseDiscardCard q remaining =>
    if p != q then
      throw s!"Only {(g.player q).name} may discard"
    let pl := g.player p
    if !pl.hand.contains id then
      throw "That card is not in your hand"
    let some card := g.findObject? id | throw "no such object"
    let g := g.logMsg s!"{(g.player p).name} discards {card.name}"
    let (g, _) := g.move id (.graveyard card.owner) none
    return g.beginDiscardCards remaining
  | .recruitDiscard q =>
    if p != q then
      throw s!"Only {(g.player q).name} may discard"
    let pl := g.player p
    if !pl.hand.contains id then
      throw "That card is not in your hand"
    let some card := g.findObject? id | throw "no such object"
    let wasLand := card.printed.isLand
    let g := g.logMsg s!"{(g.player p).name} discards {card.name}"
    let (g, _) := g.move id (.graveyard card.owner) none
    let g := { g with pending := .none }
    let g :=
      if wasLand then g
      else
        let (g, _) := g.createToken p humanSoldierToken
        g
    return g.receivePriority g.activePlayer
  | _ => throw "Not time to discard a card (CR 701.9)"

/-- Pay a pending generic-mana “you may pay” or “unless pays” cost. -/
def payGeneric (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .mayPayGeneric q n =>
    if p != q then
      throw s!"Only {(g.player q).name} may pay \{{n}}"
    if !(g.player p).manaPool.canPay (ManaCost.ofGeneric n) then
      throw s!"{(g.player p).name} cannot pay \{{n}}"
    let g ← g.payCost p (ManaCost.ofGeneric n)
    let g := g.logMsg s!"{(g.player p).name} pays \{{n}}"
    let g := { g with pending := .none }
    let g := g.draw p 1
    return g.receivePriority g.activePlayer
  | .payOrLetCounter q n _spellId =>
    if p != q then
      throw s!"Only {(g.player q).name} may pay \{{n}}"
    if !(g.player p).manaPool.canPay (ManaCost.ofGeneric n) then
      throw s!"{(g.player p).name} cannot pay \{{n}}"
    let g ← g.payCost p (ManaCost.ofGeneric n)
    let g := g.logMsg s!"{(g.player p).name} pays \{{n}}"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | _ => throw "Not time to pay generic mana"

/-- Put the pending card on top or bottom of its owner's library. -/
def chooseLibrarySide (g : Game) (p : PlayerId) (top : Bool) : Except String Game := do
  match g.pending with
  | .chooseLibraryPlacement q id =>
    if p != q then
      throw s!"Only {(g.player q).name} may choose top or bottom"
    let some o := g.findObject? id | throw "no such object"
    if !o.isOnBattlefield then
      throw s!"{o.name} is no longer on the battlefield"
    let dest := if top then Zone.library o.owner else Zone.library o.owner
    let side := if top then "top" else "bottom"
    let name := o.name
    let owner := o.owner
    let (g, newId) := g.move id dest none
    let pl := g.player owner
    let without := stripId pl.library newId
    let g :=
      if top then
        g.setPlayer { pl with library := without ++ #[newId] }
      else
        g.setPlayer { (g.player owner) with library := #[newId] ++ without }
    let g := g.logMsg s!"{(g.player owner).name} puts {name} on the {side} of their library"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | _ => throw "Not time to choose library placement"

/-- Attach Equipment, tap Humans, or put a +1/+1 counter, depending on pending. -/
def choosePermanents (g : Game) (p : PlayerId) (ids : Array ObjectId) :
    Except String Game := do
  match g.pending with
  | .mayAttachEquipment q hostId =>
    if p != q then
      throw s!"Only {(g.player q).name} may attach Equipment"
    if ids.size != 1 then
      throw "Choose one Equipment to attach"
    let some eq := g.findObject? ids[0]! | throw "no such object"
    if !(eq.isOnBattlefield && eq.printed.isEquipment && eq.controlledBy p) then
      throw s!"{eq.name} is not an Equipment you control"
    let some host := g.findObject? hostId | throw "The creature is no longer in play"
    if !host.isOnBattlefield then
      throw s!"{host.name} is no longer on the battlefield"
    let (g, ts) := g.bumpTime
    let g := g.setObject { eq with attachedTo := some host.id, timestamp := ts }
    let g := g.logMsg s!"{eq.name} attaches to {host.name}"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | .tapHumans q =>
    if p != q then
      throw s!"Only {(g.player q).name} may tap Humans"
    if !uniqueObjectIds ids then
      throw "Duplicate card"
    let mut g := g
    let mut n : Nat := 0
    for id in ids do
      let some o := g.findObject? id | throw "no such object"
      if !(o.isOnBattlefield && o.controlledBy p && g.hasSubtype o "Human" &&
          !o.status.tapped) then
        throw s!"{o.name} is not an untapped Human you control"
      g := g.applyPermanentAction o .tap
      n := n + 1
    g := { g with pending := .none }
    g := if n == 0 then g else g.draw p n
    return g.receivePriority g.activePlayer
  | .mayPlusOneCreature q =>
    if p != q then
      throw s!"Only {(g.player q).name} may put a +1/+1 counter"
    if ids.size != 1 then
      throw "Choose one creature"
    let some o := g.findObject? ids[0]! | throw "no such object"
    if !(o.isOnBattlefield && o.isCreature) then
      throw s!"{o.name} is not a creature on the battlefield"
    let g := g.addPlusOnePlusOneTo o 1
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | _ => throw "Not time to choose permanents"

/-- Decline an optional discard (CR 608.2d) or choose no target for an
“up to one” trigger (CR 601.2c / 115.1c). -/
def decline (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .mayDiscardDraw q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to discard"
    let g := g.logMsg s!"{(g.player p).name} declines to discard a card"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | .chooseTargets caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may choose targets (CR 601.2c)"
    let some obj := g.objectAwaitingTargets | throw "No spell is waiting for a target (CR 601.2c)"
    match obj.triggeredAbility with
    | some ab =>
      if !ab.allowsZeroTargets then
        throw "That ability requires a target (CR 601.2c)"
      let g := g.setStackEntryTargets obj.id #[]
      let g := g.logMsg
        s!"{(g.player p).name} chooses no target (CR 603.3d / 601.2c)"
      return g.afterTriggerTargetsChosen
    | none =>
      let allowZero :=
        match g.currentSpellEffect obj with
        | some e => e.allowsZeroTargets
        | none => false
      if allowZero then
        let g := g.setStackEntryTargets obj.id #[]
        let g := g.logMsg
          s!"{(g.player p).name} chooses no target (CR 603.3d / 601.2c)"
        if g.proposedSpell.isSome then
          return g.afterTargetsChosen
        return g.afterTriggerTargetsChosen
      else if g.canFinishOptionalTargets obj then
        let g := g.logMsg
          s!"{(g.player p).name} finishes choosing targets (CR 601.2c)"
        if g.proposedSpell.isSome then
          return g.afterTargetsChosen
        return g.afterTriggerTargetsChosen
      throw "That spell requires a target (CR 601.2c)"
  | .mayPayGeneric q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to pay"
    let g := g.logMsg s!"{(g.player p).name} declines to pay"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | .payOrLetCounter q _ spellId =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to pay"
    let g := g.logMsg s!"{(g.player p).name} does not pay"
    let g := { g with pending := .none }
    let g := g.counterStackSpell spellId
    return g.receivePriority g.activePlayer
  | .mayAttachEquipment q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to attach Equipment"
    let g := g.logMsg s!"{(g.player p).name} declines to attach Equipment"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | .tapHumans q =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to tap Humans"
    let g := g.logMsg s!"{(g.player p).name} taps no Humans"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | .mayPlusOneCreature q =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to put a +1/+1 counter"
    let g := g.logMsg s!"{(g.player p).name} declines to put a +1/+1 counter"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | _ => throw "Not time to decline"

def keepOpeningHand (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .declareMulligan q =>
    if p != q then
      throw "It's not your turn to declare a mulligan (CR 103.5)"
    let g := g.modifyPlayer p (fun pl => { pl with keptOpeningHand := true })
    let g := g.logMsg
      s!"{g.player p |>.name} keeps their opening hand of {(g.player p).hand.size}"
    return g.afterDeclaration p
  | _ => throw "Not time to keep an opening hand (CR 103.5)"

/-- Choose which legendary permanent to keep; the rest go to their owners'
graveyards (CR 704.5j). Then resume the CR 704.3 loop: recheck state-based
actions, put waiting triggers on the stack if none remain, and grant
priority only once that process is idle. -/
def keepLegend (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  match g.pending with
  | .chooseLegend q name ids =>
    if p != q then
      throw s!"Only {(g.player q).name} may choose which {name} to keep (CR 704.5j)"
    if !ids.contains id then
      throw s!"Choose one of the legendary permanents named {name} (CR 704.5j)"
    let some kept := g.findObject? id | throw "no such object"
    if !kept.isOnBattlefield then
      throw s!"{kept.name} is not on the battlefield"
    let mut g := g.logMsg
      s!"{(g.player p).name} keeps {kept.name} (legend rule, CR 704.5j)"
    for other in ids do
      if other != id then
        match g.findObject? other with
        | some o =>
          if o.isOnBattlefield then
            g := g.logMsg
              s!"{o.name} is put into its owner's graveyard (legend rule, CR 704.5j)"
            let (g', _) := g.move o.id (.graveyard o.owner) none
            g := g'
        | none => pure ()
    g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | _ => throw "Not time to apply the legend rule (CR 704.5j)"

/-- Put this player's waiting triggered abilities on the stack in the listed
source order (CR 603.3b). First listed is put first (farthest from the top). -/
def stackTriggers (g : Game) (p : PlayerId) (ids : Array ObjectId) : Except String Game := do
  match g.pending with
  | .chooseTriggerToStack q =>
    if p != q then
      throw s!"Only {(g.player q).name} may choose the order of triggered abilities (CR 603.3b)"
    let mine := g.waitingTriggersOf p
    if ids.size != mine.size then
      throw "List each waiting triggered ability's source once (CR 603.3b)"
    let mut remaining := mine
    let mut ordered : Array WaitingTrigger := #[]
    for id in ids do
      match remaining.findIdx? (fun wt => wt.source.id == id) with
      | none =>
        throw "That permanent has no waiting triggered ability to put on the stack (CR 603.3b)"
      | some i =>
        ordered := ordered.push remaining[i]!
        remaining := remaining.eraseIdx! i
    let g := { g with pending := .none }.logMsg
      s!"{(g.player p).name} chooses the order of triggered abilities (CR 603.3b)"
    let g := g.putTriggerBatch ordered
    if g.over || g.pending != .none then
      return g
    return g.receivePriority g.activePlayer false
  | _ => throw "Not time to choose triggered-ability order (CR 603.3b)"

/-- Record that this player will mulligan. The mulligan itself is taken only
after every remaining player has declared (CR 103.5). -/
def takeMulligan (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .declareMulligan q =>
    if p != q then
      throw "It's not your turn to declare a mulligan (CR 103.5)"
    if (g.player p).keptOpeningHand then
      throw "You already kept your opening hand (CR 103.5)"
    if !g.canTakeMulligan p then
      throw "A player may not take further mulligans after their opening hand would be zero cards (CR 103.5)"
    let g := { g with willMulligan := g.willMulligan.push p }
    let g := g.logMsg s!"{g.player p |>.name} will take a mulligan (CR 103.5)"
    return g.afterDeclaration p
  | _ => throw "Not time to take a mulligan (CR 103.5)"

/-- Place the listed cards on the bottom of `p`'s library. The first listed
card becomes the new bottom; later cards sit above it. -/
def putCardsOnBottom (g : Game) (p : PlayerId) (ids : Array ObjectId) : Except String Game := do
  match g.pending with
  | .putOnBottom q n =>
    if p != q then
      throw "Only the player who took a mulligan may put cards on the bottom (CR 103.5)"
    if ids.size != n then
      throw s!"Put exactly {n} card(s) on the bottom of your library (CR 103.5)"
    if !uniqueObjectIds ids then
      throw "Duplicate card"
    let pl := g.player p
    for id in ids do
      if (g.findObject? id).isNone then
        throw "no such object"
      if !pl.hand.contains id then
        throw "That card is not in your hand"
    let mut g := g
    let mut newBottom : Array ObjectId := #[]
    for id in ids do
      let card := g.object! id
      let ownerName := (g.player p).name
      let (g', newId) := g.move id (.library p)
      g := g'
      newBottom := newBottom.push newId
      g := g.logMsg s!"{ownerName} puts {card.name} on the bottom of their library"
    let plNow := g.player p
    let without := newBottom.foldl (fun lib id => stripId lib id) plNow.library
    g := g.setPlayer { plNow with library := newBottom ++ without }
    if g.mulliganToBottom.isEmpty then
      g := { g with pending := .none }
      return g.receivePriority g.activePlayer
    -- After a mulligan to zero, the player may not take further mulligans.
    if !g.canTakeMulligan p then
      g := g.modifyPlayer p (fun pl => { pl with keptOpeningHand := true })
      g := g.logMsg
        s!"{g.player p |>.name} keeps their opening hand of {(g.player p).hand.size}"
    return g.afterBottom p
  | _ => throw "Not time to put cards on the bottom (CR 103.5)"

def apply (g : Game) (p : PlayerId) : Action → Except String Game
  | .pass => g.pass p
  | .playLand id => g.playLand p id
  | .tapForMana id m => g.tapForMana p id m
  | .cast id => g.castSpell p id
  | .castAdventure id => g.castSpell p id true
  | .chooseMode idx => g.announceMode p idx
  | .target t => g.announceTarget p t
  | .targets ts => g.announceTargets p ts
  | .divideDamage as => g.announceDividedDamage p as
  | .activate id idx => g.activateAbility p id idx
  | .pay => g.pay p
  | .sacrifice id => g.sacrificeForActivation p id
  | .chooseAdditionalCost payGeneric => g.announceAdditionalCost p payGeneric
  | .declareAttackers ids => g.declareAttackers p ids
  | .declareBlockers as => g.declareBlockers p as
  | .assignCombatDamage asgns => g.announceCombatDamage p asgns
  | .keep => g.keepOpeningHand p
  | .keepLegend id => g.keepLegend p id
  | .stackTriggers ids => g.stackTriggers p ids
  | .takeMulligan => g.takeMulligan p
  | .putOnBottom ids => g.putCardsOnBottom p ids
  | .scry top bottom => g.finishScry p top bottom
  | .discard id => g.discardForDraw p id
  | .decline => g.decline p
  | .payGeneric => g.payGeneric p
  | .chooseTop => g.chooseLibrarySide p true
  | .chooseBottom => g.chooseLibrarySide p false
  | .choosePermanents ids => g.choosePermanents p ids
  | .concede => return g.concede p

def handObjects (g : Game) (p : PlayerId) : Array GameObject :=
  (g.player p).hand.filterMap (fun id => g.findObject? id)

/-- Who must act next? -/
def actor (g : Game) : Option PlayerId :=
  if g.over then none
  else
    match g.pending with
    | .declareAttackers => some g.activePlayer
    | .declareBlockers => some (g.opponent g.activePlayer)
    | .activateManaAbilities caster => some caster
    | .chooseMode p => some p
    | .chooseTargets p => some p
    | .sacrificePermanent p _ => some p
    | .sacrificeCreature p => some p
    | .declareMulligan p => some p
    | .putOnBottom p _ => some p
    | .scry p _ => some p
    | .mayDiscardDraw p _ => some p
    | .chooseAdditionalCost p => some p
    | .chooseSacrificeCreature p _ _ => some p
    | .chooseDiscardCard p _ => some p
    | .assignCombatDamage p _ => some p
    | .chooseLegend p _ _ => some p
    | .chooseTriggerToStack p => some p
    | .mayPayGeneric p _ => some p
    | .chooseLibraryPlacement p _ => some p
    | .mayAttachEquipment p _ => some p
    | .tapHumans p => some p
    | .payOrLetCounter p _ _ => some p
    | .mayPlusOneCreature p => some p
    | .recruitDiscard p => some p
    | .none =>
      if g.playersReceivePriority then some g.priority else none

end Game

namespace Start

def materializeSeat (g : Game) (seatIdx : Nat) (seat : Seat) : Except String Game := do
  if seat.deck.isEmpty then
    throw s!"{seat.name} has an empty deck"
  match validateDeck g.format seat.deck with
  | .error e => throw s!"{seat.name}: {e}"
  | .ok _ => pure ()
  let pid : PlayerId := ⟨seatIdx⟩
  let player : Player := {
    id := pid
    name := seat.name
    life := 20
    startingLife := 20
  }
  let g := { g with players := g.players.push player }
  return Id.run do
    let mut g := g
    for card in seat.deck do
      let (g', obj) := g.allocObject card pid (.library pid)
      g := g'
      g := g.modifyPlayer pid (fun pl => { pl with library := pl.library.push obj.id })
    return g

def start (cfg : StartConfig) : Except String Game := do
  if cfg.seats.size < 2 then
    throw "A game needs at least two players (CR 100.1)"
  let mut g : Game := { players := #[], objects := #[], rng := Rng.ofSeed cfg.seed, format := cfg.format }
  for i in [0:cfg.seats.size] do
    g ← materializeSeat g i cfg.seats[i]!
  -- Determine starting player (CR 103.1).
  let (g', startIdx) :=
    match cfg.startingPlayer with
    | some i => (g, i % g.players.size)
    | none =>
      let (rng, r) := g.rng.next
      ({ g with rng := rng }, r.toNat % g.players.size)
  g := g'
  let sp : PlayerId := ⟨startIdx⟩
  g := { g with startingPlayer := sp, activePlayer := sp, priority := sp }
  g := g.logMsg s!"Rules: {Mtg.Engine.Rules.identification}"
  g := g.logMsg s!"Starting player: {g.player sp |>.name}"
  for pl in g.players do
    g := g.shuffleLibrary pl.id
  -- Starting life (CR 103.4) already 20. Draw opening hands, then mulligan
  -- (CR 103.5). The first turn begins after every player has kept.
  for pl in g.players do
    g := g.draw pl.id (g.player pl.id).startingHandSize
  return g.beginMulliganRound

end Start

#guard Format.constructed.minDeckSize == 60

end Mtg.Engine
