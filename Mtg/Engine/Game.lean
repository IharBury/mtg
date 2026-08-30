import Mtg.Engine.Card
import Mtg.Engine.Deck
import Mtg.Engine.Mana
import Mtg.Engine.Rng
import Mtg.Engine.Rules
import Mtg.Engine.Turn
import Mtg.Engine.Zone

/-!
# Game state and rules engine

Encodes starting a game (CR 103), including the London mulligan (CR 103.5,
including the free first mulligan in multiplayer and Brawl, CR 103.5c),
ending a game (CR 104), a player leaving a multiplayer game (CR 800.4),
priority (CR 117), playing lands (CR 116.2a / 305),
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
dying this turn (CR 614.1 / 614.6 / 700.4), attack triggers (CR 508.2 / 603), including scrying, copying this
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
CR 702.15b), Saga lore counters and chapter abilities (CR 714), cleanup
(CR 514.3), and the state-based actions we implement
(CR 704.5, including deathtouch, CR 704.5h, the legend rule, CR 704.5j,
and sacrificing a Saga after its final chapter, CR 714.4),
and a player leaving a multiplayer game (CR 800.4 and 800.4a–p).
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
  /-- Player this creature is attacking (CR 508.1). Set with `attacking`. -/
  attackingWhom : Option PlayerId := none
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
  /-- If this creature would die this turn, exile it instead
  (CR 614.1 / 614.6). -/
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
  /-- Triggered abilities granted by a lasting effect (e.g. a Saga chapter
  that gives the Saga landfall). -/
  grantedTriggeredAbilities : Array TriggeredAbility := #[]
  /-- Objects granting this permanent hexproof while they remain. -/
  hexproofGrantedBy : Array ObjectId := #[]
  /-- Objects preventing damage this permanent would deal while they remain. -/
  preventDamageGrantedBy : Array ObjectId := #[]
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
  /-- Shadow counters. A permanent with a shadow counter has shadow. -/
  shadow : Nat := 0
  /-- Phased out (CR 702.26). Treated as though it does not exist. -/
  phasedOut : Bool := false
  /-- Host this Aura or Equipment phased out with. -/
  phasedWith : Option ObjectId := none
  /-- This creature is its controller's Ring-bearer. -/
  ringBearer : Bool := false
  /-- Alliance modes chosen this turn (0 = add GGG, 1 = +1/+1 each, 2 = scry
  then draw). Reset as the turn ends. -/
  allianceModesChosen : Array Nat := #[]
  /-- Shield counters. A shield counter is removed instead of taking damage
  or being destroyed (CR 122.1b / Marvel Super Heroes). -/
  shield : Nat := 0
  /-- Finality counters. A permanent with a finality counter that would go
  to a graveyard from the battlefield is exiled instead (MSH release notes). -/
  finality : Nat := 0
  /-- This creature was declared as an attacker this turn (boast, CR 702.111). -/
  declaredAsAttackerThisTurn : Bool := false
  /-- A boast ability of this creature has been activated this turn. -/
  boastUsedThisTurn : Bool := false
  /-- Plan counters on a Plan enchantment. -/
  plan : Nat := 0
  /-- A power-up ability of this permanent has been activated (CR 702.193). -/
  powerUpUsed : Bool := false
  /-- How many times a power-up ability of this permanent has been activated.
  Wonder Man raises the lifetime limit above one (MSH). -/
  powerUpActivations : Nat := 0
  /-- This permanent became tapped this turn (Captain America, Living Legend). -/
  becameTappedThisTurn : Bool := false
  /-- You put a +1/+1 counter on this creature this turn (Kid Loki). -/
  gotPlusOneThisTurn : Bool := false
  /-- Sources that stop this permanent becoming untapped while they remain
  (Spider-Woman; Frozen in Ice is attached separately). -/
  cantUntapGrantedBy : Array ObjectId := #[]
  /-- This permanent is a creature in addition to its other types until EOT
  (I Am Iron Man). -/
  additionalCreatureUntilEot : Bool := false
  /-- This permanent entered the battlefield this turn. -/
  enteredThisTurn : Bool := false
  /-- The Mind Stone (or similar) has been harnessed. -/
  harnessed : Bool := false
  /-- This permanent is currently showing its back face (MSH modal DFC). -/
  transformed : Bool := false
  /-- Entered back-face-up because it is night and the front has daybound
  (MSH 191). Transform is illegal. -/
  cantTransform : Bool := false
  /-- Sources that make this permanent lose its printed abilities while they
  remain (The Wondrous Wasp; MSH 145 / 190). Later granted abilities still
  apply. -/
  losesAbilitiesGrantedBy : Array ObjectId := #[]
  /-- Modes chosen for the object's lifetime (Gollum, Riddle Master). -/
  chosenModes : Array Nat := #[]
  /-- Odd/even choice (Gollum). `none` until chosen; `some true` is odd. -/
  chosenOdd : Option Bool := none
  /-- Lore counters on a Saga (CR 714). -/
  lore : Nat := 0
  /-- Indestructible counters. -/
  indestructibleCounters : Nat := 0
  /-- Lifelink counters (Arwen, Mortal Queen). -/
  lifelinkCounters : Nat := 0
  /-- Creature type chosen as this permanent entered (Unexpected Party). -/
  chosenCreatureType : Option String := none
  /-- Creatures this player controls cannot block this attacker this turn
  (The Black Gate). Cleared in cleanup. -/
  cantBeBlockedByPlayer : Option PlayerId := none
  /-- Until end of turn, this creature can be blocked only by creatures with
  haste (Speed, Young Avenger). -/
  cantBeBlockedExceptByHasteUntilEot : Bool := false
  /-- This permanent dealt damage this turn (Red Guardian; MSH 272). -/
  dealtDamageThisTurn : Bool := false
  /-- Until end of turn, these replace existing creature types and keep
  noncreature subtypes (Iron Man Armor; MSH 88). -/
  replacedCreatureTypesUntilEot : Option (Array String) := none
  /-- Until end of turn, this creature gets +1/+1 for each artifact you
  control (Iron Man Armor). -/
  pumpPerArtifactUntilEot : Bool := false
  /-- Influence counters (Palantír of Orthanc). -/
  influence : Nat := 0
  /-- This permanent is only a Food artifact (Supper for Spiders). -/
  onlyFoodArtifact : Bool := false
  /-- Burden counters (The One Ring). -/
  burden : Nat := 0
  /-- Quest counters (Last Light of Durin's Day). -/
  quest : Nat := 0
  /-- Trample counters (Beorn the Fierce). -/
  trampleCounters : Nat := 0
  /-- Until end of turn, combat damage to a player creates a Treasure. -/
  combatDamageCreatesTreasure : Bool := false
  /-- This permanent is an artifact and not a creature (Tom, Bert, and William). -/
  returnedAsArtifact : Bool := false
  /-- A control-changing effect lasts until end of turn (Act of Treason,
  Sauron, the Lidless Eye). Cleared in cleanup; ending it may exile (CR 800.4c). -/
  controlUntilEot : Bool := false
  /-- Instances of Iron Fist's granted tap ability this turn (MSH 106). -/
  ironFistTapGrants : Nat := 0
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
    fun s => { s with additionalArtifactUntilEot := false }⟩,
  ⟨fun s => s.additionalCreatureUntilEot,
    fun s => { s with additionalCreatureUntilEot := false }⟩,
  ⟨fun s => s.cantBeBlockedByPlayer.isSome,
    fun s => { s with cantBeBlockedByPlayer := none }⟩,
  ⟨fun s => s.cantBeBlockedExceptByHasteUntilEot,
    fun s => { s with cantBeBlockedExceptByHasteUntilEot := false }⟩,
  ⟨fun s => s.dealtDamageThisTurn,
    fun s => { s with dealtDamageThisTurn := false }⟩,
  ⟨fun s => s.replacedCreatureTypesUntilEot.isSome,
    fun s => { s with replacedCreatureTypesUntilEot := none }⟩,
  ⟨fun s => s.pumpPerArtifactUntilEot,
    fun s => { s with pumpPerArtifactUntilEot := false }⟩,
  ⟨fun s => s.ironFistTapGrants != 0,
    fun s => { s with ironFistTapGrants := 0 }⟩
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
  /-- Optional “up to one” slots that were skipped while announcing
  (CR 115.1c / 601.2c). The current instance index is
  `targets.size + skippedOptionalSlots`. -/
  skippedOptionalSlots : Nat := 0
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
  /-- The proposed spell will be kicked if this is true. -/
  kicked : Bool := false
  /-- Kicker has been announced (paid or declined). -/
  kickerAnnounced : Bool := false
  /-- Opponent chosen for a promised gift, if any. -/
  giftTo : Option PlayerId := none
  /-- Gift has been announced (promised or declined). -/
  giftAnnounced : Bool := false
  /-- The proposed spell will be cast using teamwork if this is true. -/
  teamworkPaid : Bool := false
  /-- Teamwork has been announced (paid or declined). -/
  teamworkAnnounced : Bool := false
  /-- Activated ability being paid, for extra costs. -/
  activation : Option ActivatedAbility := none
deriving Repr, Inhabited

/-- A random event the engine would otherwise resolve with `Rng`.
`--norandom` leaves it pending so a host (the demo) can supply the result. -/
inductive RandomRequest where
  /-- Shuffle this player's library. The result is a permutation
  (index 0 = bottom). An empty result keeps the current order. -/
  | shuffleLibrary (player : PlayerId)
  /-- Put these cards into `dest` in the supplied order (index 0 = first
  / bottom). An empty result keeps their current relative order. -/
  | orderInto (ids : Array ObjectId) (dest : Zone)
  /-- Choose one of these objects at random. -/
  | chooseObject (ids : Array ObjectId)
  /-- Choose a natural number `0 ≤ i < n` (a coin toss is `n = 2`). -/
  | chooseIndex (n : Nat)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Work that still belongs to an effect after a `--norandom` result is
applied. The RNG path runs the same work immediately. -/
inductive AfterRandom where
  | none
  /-- Draw `n` cards for `p`. -/
  | draw (p : PlayerId) (n : Nat)
  /-- `p` gains `n` life. -/
  | gainLife (p : PlayerId) (n : Nat)
  /-- Continue CR 103.3 opening shuffles from this seat index. -/
  | openingShuffles (next : Nat)
  /-- After this player's library is ordered, draw a new opening hand and
  continue simultaneous mulligans for `rest`. -/
  | mulliganQueue (drawn : PlayerId) (rest : Array PlayerId)
  /-- Seat `i` takes the first turn; then opening shuffles. -/
  | setStartingPlayer (i : Nat)
  /-- Put the chosen creature onto the battlefield for `controller`, then shuffle. -/
  | putCreatureThenShuffle (controller : PlayerId)
deriving DecidableEq, Repr, Inhabited, BEq

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
  /-- Discard a card for recruit; if it is not a land, create a Human Soldier. -/
  | recruitDiscard (player : PlayerId)
  /-- Announce whether to pay the optional kicker cost (CR 702.32 / 601.2b). -/
  | chooseKicker (player : PlayerId)
  /-- Announce whether to promise a gift to an opponent (CR 702.185 / 601.2b). -/
  | chooseGift (player : PlayerId)
  /-- Announce whether to pay the optional teamwork cost (CR 702.194 / 601.2b). -/
  | chooseTeamwork (player : PlayerId)
  /-- Choose creatures to tap for a teamwork cost (CR 702.194). -/
  | chooseTeamworkCreatures (player : PlayerId) (need : Nat)
  /-- Choose a creature you control as your Ring-bearer. -/
  | chooseRingBearer (player : PlayerId)
  /-- You may sacrifice another creature to Bolg's enters instruction. -/
  | maySacrificeAnotherBolg (player : PlayerId) (bolgId : ObjectId)
  /-- A random event must be resolved by supplying its result (`--norandom`). -/
  | resolveRandom (req : RandomRequest)
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
  /-- CR 800.4a has already been performed for this player. -/
  leftTheGame : Bool := false
  drewFromEmpty : Bool := false
  /-- Completed London mulligans this game (CR 103.5). The first may not
  count toward bottoming or the zero-card limit (CR 103.5c). -/
  mulligansTaken : Nat := 0
  /-- Set once this player declines further mulligans (CR 103.5). -/
  keptOpeningHand : Bool := false
  library : Array ObjectId := #[]
  hand : Array ObjectId := #[]
  graveyard : Array ObjectId := #[]
  /-- Cards drawn this turn (for “second card each turn” triggers). -/
  cardsDrawnThisTurn : Nat := 0
  /-- A Hero you control entered this turn (Avengers Assemble). -/
  heroEnteredThisTurn : Bool := false
  /-- You attacked with a Hero this turn (Avengers Assemble). -/
  attackedWithHeroThisTurn : Bool := false
  /-- Cards drawn during your current draw step (Bard, King of Dale). -/
  cardsDrawnThisDrawStep : Nat := 0
  /-- Spells cast this turn (for “second spell each turn” triggers). -/
  spellsCastThisTurn : Nat := 0
  /-- Noncreature spells cast this turn. -/
  noncreatureSpellsCastThisTurn : Nat := 0
  /-- Storied: enduring story for the rest of the game. -/
  enduringStory : Bool := false
  /-- Number of The Ring emblem abilities gained (0 = no emblem). Max 4. -/
  theRingAbilities : Nat := 0
  /-- Current Ring-bearer, if any. -/
  ringBearerId : Option ObjectId := none
  /-- Ascend: the city's blessing for the rest of the game. -/
  citysBlessing : Bool := false
  /-- Mana value of each spell this player has cast this turn. -/
  castManaValuesThisTurn : Array Nat := #[]
  /-- True when this player has a commander (Commander / Oathbreaker). -/
  hasCommander : Bool := false
  /-- Combined color identity of this player's commander(s). Empty when they
  have no commander or the commander is colorless (CR 903.4). -/
  commanderColorIdentity : ColorSet := {}
  /-- Times Belladonna Took's token-enters ability has resolved this turn. -/
  belladonnaResolvesThisTurn : Nat := 0
  /-- Protection from everything until this player's next turn
  (e.g. The One Ring). -/
  protectionFromEverything : Bool := false
  /-- Bird Soldier tokens to create at the beginning of the next upkeep
  (The Eagles Are Coming!). -/
  eaglesBirdsNextUpkeep : Nat := 0
  /-- Life gained this turn (The Gaffer and similar “if you gained” triggers). -/
  lifeGainedThisTurn : Nat := 0
  /-- Creature spells cast this turn (Radagast of Rhosgobel). -/
  creatureSpellsCastThisTurn : Nat := 0
  /-- Qualities beheld this game (Elven Passage and similar). A later zone
  change of the revealed card or chosen permanent does not un-behold. -/
  beheldQualities : Array String := #[]
  /-- Players can't cast spells this turn (Bilbo's Gambit). -/
  cantCastSpellsThisTurn : Bool := false
  /-- Delayed “whenever you attack this turn, pump per Plains” chapters
  still waiting to fire (Roads Go Ever, Ever On). -/
  attackPumpPerPlainsThisTurn : Nat := 0
  /-- This player's life total can't change (Platinum Emperion; MSH 292). -/
  lifeLocked : Bool := false
  /-- Cards discarded this turn (Misty Knight; MSH 375). -/
  cardsDiscardedThisTurn : Nat := 0
  /-- An artifact entered under this player's control this turn (Iron Man;
  MSH 242 / 323). Still true if that artifact later left or changed types. -/
  artifactEnteredThisTurn : Bool := false
  /-- Two-Headed Giant teammate (MSH 57 / 236). -/
  teammate : Option PlayerId := none
deriving Repr, Inhabited

/-- A seat at the table before objects are created. -/
structure Seat where
  name : String
  deck : Array CardDef
deriving Repr, Inhabited

structure StartConfig where
  seats : Array Seat
  format : Format := .constructed
  /-- CR 903.12 Brawl option. The first mulligan is free (CR 103.5c / 903.12g). -/
  brawl : Bool := false
  seed : UInt64 := 20260807
  /-- Index into `seats`. `none` means the RNG chooses. -/
  startingPlayer : Option Nat := none
  /-- When true, never shuffle or roll; leave a `Pending.resolveRandom`. -/
  norandom : Bool := false

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
  /-- `defender` is the destination when `each` is omitted or an entry is
  `none`. `each[i]` is the player `ids[i]` attacks (CR 508.1). -/
  | declareAttackers (ids : Array ObjectId) (defender : Option PlayerId := none)
      (each : Array (Option PlayerId) := #[])
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
  /-- Pay (`true`) or decline (`false`) the optional kicker cost. -/
  | announceKicker (kick : Bool)
  /-- Promise a gift to this opponent, or `none` to decline. -/
  | announceGift (to : Option PlayerId)
  /-- Pay (`true`) or decline (`false`) the optional teamwork cost. -/
  | announceTeamwork (pay : Bool)
  /-- Choose this creature as your Ring-bearer, or `none` if you control none. -/
  | chooseRingBearer (id : Option ObjectId)
  | concede
  /-- Supply the order or chosen object for a pending random event
  (`--norandom`). An empty list keeps the current order of a shuffle. -/
  | supplyOrder (ids : Array ObjectId)
  /-- Supply an index for a pending `chooseIndex` random event (`--norandom`). -/
  | supplyIndex (i : Nat)
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
  /-- When true, random events become `Pending.resolveRandom` instead of
  using `rng`. -/
  norandom : Bool := false
  /-- Continuation after a `--norandom` result is applied. -/
  afterRandom : AfterRandom := .none
  result : Option GameResult := none
  log : Array String := #[]
  format : Format := .constructed
  /-- CR 903.12 Brawl option (free first mulligan, CR 103.5c / 903.12g). -/
  brawl : Bool := false
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
  /-- Defending players who still must declare blockers, in APNAP order
  (CR 509.1 / 802). -/
  blockersQueue : Array PlayerId := #[]
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
  /-- Creatures that assigned first-strike combat damage this combat. They
  assign regular damage only if they have double strike (Okoye; MSH 173). -/
  firstStrikeAssignedThisCombat : Array ObjectId := #[]
  /-- It is night (CR 702.145). Used by Nick Fury / daybound (MSH 191). -/
  isNight : Bool := false
  /-- Draw these cards after the current scry finishes (e.g. Hithlain Knots). -/
  pendingDrawAfterScry : Option (PlayerId × Nat) := none
  /-- Snapshot of Head-of-the-Hunt-style replacements for one SBA death
  batch, so simultaneous deaths still see those sources (Gatherer).
  Objects are stored so a source that also dies still applies (CR 614.6). -/
  lockedDeathReplacements : Option (Array GameObject) := none
  /-- While an SBA death batch is applying, `move` skips per-object
  “other creatures die” triggers; the batch queues them only for creatures
  that actually die (CR 614.6). -/
  suppressOthersDie : Bool := false
  /-- While a simultaneous graveyard batch is applying, `move` skips
  per-object “creature cards to graveyard” triggers so “one or more”
  fires once (Robot Domination; MSH 138). -/
  suppressCreatureCardsToGy : Bool := false
  /-- Player most recently dealt combat damage by a creature whose
  combat-damage trigger is resolving (Cavern-Hoard Dragon). -/
  lastCombatDamagePlayer : Option PlayerId := none
  /-- True while a spell is being cast from the top of a library
  (Elven Chorus cannot show the new top until that finishes). -/
  castingFromTop : Bool := false
  /-- Creature cards that went from the battlefield to a graveyard this turn
  (Supper for Spiders). Cleared as the turn ends. -/
  battlefieldCreaturesToGyThisTurn : Array ObjectId := #[]
  /-- Most recent life loss amount, for “mills that many” triggers. -/
  lastLifeLost : Option (PlayerId × Nat) := none
  /-- Most recent noncombat damage marked on a permanent. -/
  lastNoncombatDamage : Option (ObjectId × Nat) := none
  /-- Cards in exile that return at the beginning of the next end step
  (Roll-Roll-Roll-Roll and similar delayed blinks). -/
  delayedEndStepReturns : Array ObjectId := #[]
  /-- Source of the current connive action, if any (MSH / CR 701.47). -/
  conniveSource : Option ObjectId := none
  /-- Most recent creature that became tapped (Captain America, Living Legend). -/
  lastBecameTapped : Option ObjectId := none
  /-- Extra combat phases still to begin after the current combat (Hulk enrage). -/
  additionalCombatPhases : Nat := 0
  /-- Enrage triggers that will grant an additional combat when they resolve. -/
  enrageGrantsAdditionalCombat : Nat := 0
  /-- The Sensational She-Hulk chose to deal damage this turn (MSH 95 / 142). -/
  sheHulkDamageUsedThisTurn : Bool := false
  /-- A pending MSH reflexive trigger: (controller, source, kind tag).
  Kind is `0` grant-indestructible, `1` deal-2, `2` Hawkeye modes (paid count
  in `pendingMshReflexivePaid`). -/
  pendingMshReflexive : Option (PlayerId × Option ObjectId × Nat) := none
  /-- Times Hawkeye paid for Trick Arrows (0–3). -/
  pendingMshReflexivePaid : Nat := 0
  /-- Player-controlling effect: (you, the player you control). Last created
  wins (MSH 259). -/
  playerControl : Option (PlayerId × PlayerId) := none
  /-- If the controlled player skips their next turn, control applies to the
  next turn they actually take (MSH 221). -/
  controlOnNextTakenTurn : Bool := false
  /-- Loki delayed copy: (controller, Loki's id if still known, last-known
  power). Compared at cast time (MSH 109). -/
  pendingLokiCopy : Option (PlayerId × Option ObjectId × Int) := none
  /-- Extort triggers waiting for a pay/don't-pay decision (MSH 371). -/
  pendingExtort : Nat := 0
  /-- Controller of the pending extort trigger. -/
  pendingExtortController : Option PlayerId := none
  /-- Until EOT, this player's creatures with toughness greater than power
  assign combat damage equal to toughness (The Kingpin of Crime; MSH 287). -/
  assignCombatDamageEqualToughness : Option PlayerId := none
  /-- Most recent attacking creature that died (new GY object id; Ares). -/
  lastDiedAttacker : Option ObjectId := none
  /-- World War Hulk chapter I: the next red or green creature spell this
  player casts this turn may be cast without paying its mana cost (MSH 343). -/
  pendingFreeRGCreature : Option PlayerId := none
  /-- Cards exiled to pay the current Zemo boast activation (MSH 227). -/
  zemoBoastExiles : Array ObjectId := #[]
  /-- Remaining discards for Thirst for Knowledge (MSH 344). An artifact
  card finishes the requirement early. -/
  thirstDiscardsLeft : Nat := 0
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
  if (g.player p).lifeLocked && life != (g.player p).life then
    g.logMsg s!"{(g.player p).name}'s life total can't change"
  else
    g.setPlayer { (g.player p) with life := life } |>.logMsg msg

def livingPlayers (g : Game) : Array Player :=
  g.players.filter (fun pl => !pl.lost)

/-- True while `p` has not lost and therefore has not left (CR 104 / 800.4). -/
def stillInGame (g : Game) (p : PlayerId) : Bool :=
  !(g.player p).lost

/-- Living opponents of `p` (CR 102.2). -/
def livingOpponents (g : Game) (p : PlayerId) : Array Player :=
  g.livingPlayers.filter (fun pl => pl.id != p)

/-- Apply `f` to each living opponent of `controller`. -/
def forEachOpponent (g : Game) (controller : PlayerId) (f : Game → PlayerId → Game) :
    Game :=
  g.livingOpponents controller |>.foldl (fun g pl => f g pl.id) g

/-- Player targets for every member of `ps` who does not have protection
from everything. -/
def playerTargets (ps : Array Player) : Array Target :=
  ps.filter (fun pl => !pl.protectionFromEverything) |>.map (fun pl =>
    Target.player pl.id)

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

/-- Player being attacked this combat (CR 508.1). Taken from an attacking
creature's `attackingWhom`, or the next opponent if none is recorded. -/
def defendingPlayer (g : Game) : PlayerId :=
  match g.blockersQueue[0]? with
  | some p => p
  | none =>
    match g.objects.find? (fun o => o.isOnBattlefield && o.status.attackingWhom.isSome) with
    | some o => o.status.attackingWhom.getD (g.opponent g.activePlayer)
    | none => g.opponent g.activePlayer

/-- Distinct players being attacked, in APNAP order (CR 508.1 / 101.4). -/
def defendingPlayers (g : Game) : Array PlayerId :=
  let attacked :=
    g.objects.filterMap (fun o =>
      if o.isOnBattlefield && o.status.attacking then o.status.attackingWhom else none)
  let n := g.players.size
  Id.run do
    let mut acc : Array PlayerId := #[]
    for k in [0:n] do
      let q : PlayerId := ⟨(g.activePlayer.idx + k) % n⟩
      if q != g.activePlayer && !(g.player q).lost && attacked.contains q then
        acc := acc.push q
    return acc

/-- Player who must declare blockers now. -/
def currentBlockersPlayer (g : Game) : PlayerId :=
  g.defendingPlayer

/-- Legal attack destination: a living opponent of `p` (CR 508.1). Omitted
means the next opponent in turn order. -/
def resolveAttackDestination (g : Game) (p : PlayerId) (defender : Option PlayerId) :
    Except String PlayerId :=
  match defender with
  | none => .ok (g.opponent p)
  | some d =>
    if d == p then throw "cannot attack yourself"
    else if (g.player d).lost then throw s!"{(g.player d).name} has already lost"
    else if !(g.livingOpponents p).any (fun pl => pl.id == d) then
      throw s!"{(g.player d).name} is not an opponent"
    else .ok d

def nextLiving (g : Game) (p : PlayerId) : PlayerId :=
  let n := g.players.size
  Id.run do
    for k in [1:n+1] do
      let q : PlayerId := ⟨(p.idx + k) % n⟩
      if !(g.player q).lost then
        return q
    return p

/-- Player who receives priority in place of `p` when `p` has left (CR 800.4j). -/
def priorityInstead (g : Game) (p : PlayerId) : PlayerId :=
  if (g.player p).lost then g.nextLiving p else p

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

/-- End a copy effect on `o`, restoring its original printed card (CR 707).
Does not cause the permanent to enter or leave the battlefield. -/
def restoreCopy (g : Game) (o : GameObject) : Game :=
  match o.copyRestore with
  | none => g
  | some card =>
    let copied := o.printed.name
    g.setObject { o with
      printed := card
      copyRestore := none
      copyUntilEot := false
      copyUntilNextTurn := false
      copyUntilSourceLeaves := none }
    |>.logMsg s!"{card.name} is no longer a copy of {copied}"

/-- Restore copy effects that last until end of turn. -/
def restoreCopiesUntilEot (g : Game) : Game :=
  g.battlefield.foldl (fun acc o =>
    if o.copyUntilEot then acc.restoreCopy o else acc) g

/-- Restore copy effects that last until `p`'s next turn. -/
def restoreCopiesUntilNextTurn (g : Game) (p : PlayerId) : Game :=
  g.battlefield.foldl (fun acc o =>
    if o.copyUntilNextTurn && o.controller == some p then acc.restoreCopy o
    else acc) g

/-- Restore copy effects that last until `srcId` leaves the battlefield. -/
def restoreCopiesUntilSourceLeaves (g : Game) (srcId : ObjectId) : Game :=
  g.battlefield.foldl (fun acc o =>
    if o.copyUntilSourceLeaves == some srcId then acc.restoreCopy o else acc) g

/-- Restore control-changing effects that last until `srcId` leaves
(Super Hero Civil War; MSH 143). -/
def restoreControlUntilSourceLeaves (g : Game) (srcId : ObjectId) : Game :=
  g.battlefield.foldl (fun acc o =>
    if o.controlUntilSourceLeaves == some srcId then
      let p := o.defaultController.getD o.owner
      if (acc.player p).lost then
        acc.logMsg s!"{o.name} does not change control (CR 800.4b)"
      else
        acc.setObject { o with
          controller := some p
          controlChanged := false
          controlUntilSourceLeaves := none }
          |>.logMsg s!"{o.name} returns to {(acc.player p).name}'s control"
    else acc) g

/-- Equipment attached to `o` (Whiplash last-known X). -/
def attachedEquipmentCount (g : Game) (o : GameObject) : Nat :=
  g.battlefield.filter (fun eq =>
    eq.printed.isEquipment && eq.attachedTo == some o.id) |>.size

/-- Last player-controlling effect wins (MSH 259). The controlled player
remains the active player on their turn (MSH 300) and still controls their
permanents (MSH 358). -/
def setPlayerControl (g : Game) (you them : PlayerId) : Game :=
  let g :=
    { g with playerControl := some (you, them), controlOnNextTakenTurn := false }
      |>.logMsg
        s!"{(g.player you).name} controls {(g.player them).name} during their next turn"
  match (g.player them).teammate with
  | some mate =>
    if mate == you then g
    else
      g.logMsg
        s!"{(g.player you).name} also controls {(g.player mate).name} (Two-Headed Giant team)"
  | none => g

/-- Whether `you` currently control `them`. In Two-Headed Giant, controlling
a player also controls their teammate (MSH 236). -/
def controlsPlayer (g : Game) (you them : PlayerId) : Bool :=
  match g.playerControl with
  | some (a, b) =>
    a == you && (b == them || (g.player b).teammate == some them)
  | none => false

/-- Resources used to pay `actingAs`'s costs: always that player's, even if
another player is making the choices (MSH 346). -/
def resourcesFor (g : Game) (actingAs : PlayerId) : PlayerId :=
  let _ := g
  actingAs

/-- You still make your own choices while controlling another player
(MSH 334) and you make all of that player's choices (MSH 336). -/
def decidesFor (g : Game) (actor whose : PlayerId) : Bool :=
  match g.playerControl with
  | some (you, them) =>
    if whose == them then actor == you else actor == whose
  | none => actor == whose

/-- You can see everything the controlled player can see (MSH 335). -/
def canSeeAs (g : Game) (viewer whose : PlayerId) : Bool :=
  viewer == whose || g.controlsPlayer viewer whose

/-- Cards in `whose` hand that `viewer` may look at. -/
def visibleHand (g : Game) (viewer whose : PlayerId) : Array GameObject :=
  if g.canSeeAs viewer whose then
    (g.player whose).hand.filterMap (fun id => g.findObject? id)
  else #[]

/-- Controlling a player does not let you look at their sideboard
(MSH 349). -/
def canLookAtSideboard (_g : Game) (viewer whose : PlayerId) : Bool :=
  viewer == whose

/-- You cannot have a player you're controlling choose a card from
outside the game (MSH 349). -/
def canChooseOutsideGame (g : Game) (actor whose : PlayerId) : Bool :=
  actor == whose && !g.controlsPlayer actor whose

/-- Tournament-rule decisions stay with the actual player (MSH 350). -/
def canMakeTournamentDecision (g : Game) (actor whose : PlayerId) : Bool :=
  actor == whose && !g.controlsPlayer actor whose

/-- You cannot make illegal choices for a player you control (MSH 351). -/
def canMakeIllegalDecision (_g : Game) (_actor _whose : PlayerId) : Bool :=
  false

/-- The controlling player cannot concede for the controlled player
(MSH 352). That player may still concede. -/
def canConcedeAs (_g : Game) (actor whose : PlayerId) : Bool :=
  actor == whose

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

/-- Grant a lasting player designation if `p` now qualifies. The designation
is never removed. Not a triggered ability. -/
def grantDesignationIfNeeded (g : Game) (p : PlayerId)
    (already : Player → Bool) (qualifies : Game → PlayerId → Bool)
    (set : Player → Player) (msg : String) : Game :=
  if already (g.player p) then g
  else if qualifies g p then
    g.modifyPlayer p set |>.logMsg s!"{(g.player p).name} {msg}"
  else g

/-- Grant an enduring story if `p` now qualifies. The designation is on the
player and is never removed. Not a triggered ability. -/
def grantEnduringStoryIfNeeded (g : Game) (p : PlayerId) : Game :=
  g.grantDesignationIfNeeded p (·.enduringStory)
    (fun g p => g.controlsStoried p && g.storiedPermanentCount p ≥ 3)
    (fun pl => { pl with enduringStory := true })
    "has an enduring story"

/-- Grant an enduring story to every player who now qualifies. -/
def refreshEnduringStory (g : Game) : Game :=
  g.players.foldl (fun g pl => g.grantEnduringStoryIfNeeded pl.id) g

/-- Whether `p` has an emblem named The Ring. -/
def hasTheRing (g : Game) (p : PlayerId) : Bool :=
  (g.player p).theRingAbilities > 0

/-- Number of The Ring abilities `p`'s emblem currently has. -/
def theRingAbilityCount (g : Game) (p : PlayerId) : Nat :=
  (g.player p).theRingAbilities

/-- Whether `o` is `p`'s Ring-bearer. -/
def isRingBearer (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  (g.player p).ringBearerId == some o.id && o.status.ringBearer

/-- Creatures `p` controls that can be chosen as Ring-bearer. -/
def ringBearerChoices (g : Game) (p : PlayerId) : Array GameObject :=
  (g.permanentsOf p).filter (fun o => o.isCreature)

/-- Clear Ring-bearer marks, then mark `chosen` if present. -/
def setRingBearer (g : Game) (p : PlayerId) (chosen : Option ObjectId) : Game :=
  let g :=
    g.objects.foldl (fun acc o =>
      if o.status.ringBearer && o.controlledBy p then
        acc.setObject { o with status := { o.status with ringBearer := false } }
      else acc) g
  match chosen with
  | none =>
    g.modifyPlayer p (fun pl => { pl with ringBearerId := none })
  | some id =>
    match g.findObject? id with
    | none => g.modifyPlayer p (fun pl => { pl with ringBearerId := none })
    | some o =>
      let g := g.setObject { o with status := { o.status with ringBearer := true } }
      g.modifyPlayer p (fun pl => { pl with ringBearerId := some id })

/-- Whether `p` currently has the city's blessing. -/
def hasCitysBlessing (g : Game) (p : PlayerId) : Bool :=
  (g.player p).citysBlessing

/-- Number of permanents `p` currently controls (phased-out objects do not
count). -/
def permanentCount (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).size

/-- Whether `p` controls a permanent with ascend, or a resolving spell with
ascend on the stack. -/
def controlsAscend (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o => o.printed.keywords.ascend) ||
    g.stack.any (fun e =>
      match g.findObject? e.objectId with
      | some o =>
        o.controller == some p && o.printed.keywords.ascend &&
          o.triggeredAbility.isNone && o.abilityEffect.isNone
      | none => false)

/-- Grant the city's blessing if `p` now qualifies. The designation is on the
player and is never removed. Not a triggered ability. -/
def grantCitysBlessingIfNeeded (g : Game) (p : PlayerId) : Game :=
  g.grantDesignationIfNeeded p (·.citysBlessing)
    (fun g p => g.controlsAscend p && g.permanentCount p ≥ 10)
    (fun pl => { pl with citysBlessing := true })
    "has the city's blessing"

/-- Grant the city's blessing to every player who now qualifies. -/
def refreshCitysBlessing (g : Game) : Game :=
  g.players.foldl (fun g pl => g.grantCitysBlessingIfNeeded pl.id) g

/-- Put a shadow counter on `o`. It has shadow and is a Wraith. -/
def putShadowCounter (g : Game) (o : GameObject) : Game :=
  let extra :=
    if o.status.additionalSubtypes.any (· == "Wraith") then o.status.additionalSubtypes
    else o.status.additionalSubtypes.push "Wraith"
  g.setObject { o with status := { o.status with
    shadow := o.status.shadow + 1
    additionalSubtypes := extra } }
    |>.logMsg s!"{o.name} gets a shadow counter"

/-- Attachments that should phase out or in with `host`. -/
def attachmentsOf (g : Game) (host : GameObject) : Array GameObject :=
  g.objects.filter (fun o =>
    o.zone == .battlefield && o.attachedTo == some host.id)

/-- Remove `o` from combat (CR 506.4). -/
def removeFromCombat (g : Game) (o : GameObject) : Game :=
  let g := g.setObject { o with status := { o.status with
    attacking := false
    attackingWhom := none
    blocking := #[] } }
  g.objects.foldl (fun acc x =>
    if x.status.blocking.any (· == o.id) then
      acc.setObject { x with status := { x.status with
        blocking := x.status.blocking.filter (· != o.id) } }
    else acc) g

/-- Phase `o` out, along with Auras and Equipment attached to it. Does not
trigger leaves-the-battlefield abilities. -/
def phaseOut (g : Game) (o : GameObject) : Game :=
  if o.status.phasedOut || o.zone != .battlefield then g
  else
    let g := g.removeFromCombat o
    let o := g.object! o.id
    let g := g.setObject { o with status := { o.status with
      phasedOut := true, phasedWith := none } }
    let g := g.logMsg s!"{o.name} phases out"
    (g.attachmentsOf o).foldl (fun acc att =>
      let att := acc.object! att.id
      let acc := acc.removeFromCombat att
      let att := acc.object! att.id
      acc.setObject { att with status := { att.status with
        phasedOut := true, phasedWith := some o.id } }
        |>.logMsg s!"{att.name} phases out attached to {o.name}") g

/-- Phase `o` in, along with anything that phased out attached to it.
Counters and “as this enters” choices are kept. Does not trigger enters. -/
def phaseIn (g : Game) (o : GameObject) : Game :=
  if !o.status.phasedOut then g
  else
    let g := g.setObject { o with status := { o.status with
      phasedOut := false, phasedWith := none, summoningSick := false } }
    let g := g.logMsg s!"{o.name} phases in"
    g.objects.foldl (fun acc att =>
      if att.status.phasedOut && att.status.phasedWith == some o.id then
        acc.setObject { att with status := { att.status with
          phasedOut := false, summoningSick := false } }
          |>.logMsg s!"{att.name} phases in still attached to {o.name}"
      else acc) g

/-- Phase in every phased-out permanent `p` controls (CR 502.1). -/
def phaseInControlled (g : Game) (p : PlayerId) : Game :=
  g.objects.foldl (fun acc o =>
    if o.zone == .battlefield && o.status.phasedOut && o.controlledBy p &&
        o.status.phasedWith.isNone then
      acc.phaseIn (acc.object! o.id)
    else acc) g

/-- Mana value of other spells `p` has cast this turn. Copies that were not
cast are not recorded. -/
def otherCastManaValueThisTurn (g : Game) (p : PlayerId) : Nat :=
  (g.player p).castManaValuesThisTurn.foldl (· + ·) 0

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

/-- True when `o` is Namor's characteristic-defining power (MSH ruling 289). -/
def hasNamorPowerCda (o : GameObject) : Bool :=
  o.printed.staticAbilities.any (fun
    | .msh .namorSPowerIsEqualToTheNumberOfMerfolk => true
    | _ => false)

/-- True when `o` is Super-Adaptoid's characteristic-defining power (MSH 290). -/
def hasSuperAdaptoidPowerCda (o : GameObject) : Bool :=
  o.printed.staticAbilities.any (fun
    | .msh .superAdaptoidSPowerIsEqualToTheNumberOf => true
    | _ => false)

def characteristicBasePT (g : Game) (o : GameObject) : Int × Int :=
  let power :=
    if g.hasCardsInHandPower o then
      -- Ms. Marvel (ruling 288): this set-P/T overwrites previous layer-7b sets.
      Int.ofNat (g.player o.you).hand.size
    else if hasNamorPowerCda o then
      let cda : Int :=
        Int.ofNat ((g.permanentsOf o.you).filter (fun p => p.hasSubtype "Merfolk") |>.size)
      if o.isOnBattlefield then o.status.setBasePower.getD cda else cda
    else if hasSuperAdaptoidPowerCda o then
      let cda : Int :=
        Int.ofNat ((g.permanentsOf o.you).filter (fun p =>
          p.isCreature && p.isLegendary) |>.size)
      if o.isOnBattlefield then o.status.setBasePower.getD cda else cda
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
    attachedTo,
    defaultController := if zone == .battlefield then controller else none
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

/-- A creature token. `color` is the color indicator (CR 202.2e). -/
def creatureToken (name : String) (subtypes : Array String)
    (power toughness : Int) (color : Option Color := none)
    (keywords : Keywords := Keywords.none)
    (types : Array CardType := #[.creature]) : CardDef := {
  name
  types
  subtypes
  power := some power
  toughness := some toughness
  colorIndicator := color.map ColorSet.singleton
  keywords
  isToken := true
}

/-- A 1/1 white Human Soldier creature token. -/
def humanSoldierToken : CardDef :=
  creatureToken "Human Soldier" #["Human", "Soldier"] 1 1 (some .white)

/-- Additional +1/+1 counters from Arwen, Weaver of Hope as `entering` enters.
Only weavers already on the battlefield before timestamp `asOf` apply
(simultaneous enters do not see each other). -/
def hopeCountersOnEnter (g : Game) (entering : GameObject) (asOf : Nat) : Nat :=
  match entering.controller with
  | none => 0
  | some p =>
    if !entering.isCreature then 0
    else
      (g.permanentsOf p).foldl (fun acc weaver =>
        if weaver.id == entering.id then acc
        else if !weaver.printed.othersEnterWithPlusOneEqualToughness then acc
        else if weaver.timestamp >= asOf then acc
        else acc + weaver.toughness.toNat) 0

/-- Put `n` additional +1/+1 counters on `o` as it enters from hope-weaver
replacements. -/
def applyHopeEnterCounters (g : Game) (o : GameObject) (asOf : Nat) : Game :=
  let n := g.hopeCountersOnEnter o asOf
  if n == 0 then g
  else
    let o := { o with status := o.status.addPlusOnePlusOne n }
    (g.setObject o).logMsg s!"{o.name} enters with {n} additional +1/+1 counter(s)"

/-- Create one token without replacement effects (CR 111.2 / 608.2c). Callers
that must let enters-the-battlefield triggers see the token (amass, recruit)
invoke `afterPermanentEnters` after this returns. -/
def createOneToken (g : Game) (controller : PlayerId) (printed : CardDef)
    (tapped := false) : Game × GameObject :=
  if (g.player controller).lost then
    (g.logMsg "no token is created (CR 800.4b)",
      { id := ⟨0⟩, printed := { printed with isToken := true },
        owner := controller, zone := .command })
  else
    let printed := { printed with isToken := true }
    let sick := printed.isCreature && !printed.keywords.haste
    let asOf := g.timestamp
    let (g, obj) := g.allocObject printed controller .battlefield (some controller)
      (status := { tapped := tapped, summoningSick := sick })
    let g := g.logMsg s!"{(g.player controller).name} creates {obj.name}"
    let g := g.applyHopeEnterCounters (g.object! obj.id) asOf
    -- Storied is not a trigger; an artifact token can be the third permanent.
    let g := g.refreshEnduringStory
    (g, g.object! obj.id)

/-- How many times a token-creating event is replaced (`2^n` for `n`
token-doublers such as Bard, King of Dale). -/
def tokenCreateMultiplier (g : Game) (controller : PlayerId) : Nat :=
  let n := (g.permanentsOf controller).filter (fun o => o.printed.tokenDoubling) |>.size
  Nat.pow 2 n

/-- Extra Treasures created alongside each Food (Bilbo, Fellow Conspirator). -/
def foodTreasureReplacements (g : Game) (controller : PlayerId) : Nat :=
  (g.permanentsOf controller).filter (fun o => o.printed.foodAlsoCreatesTreasure) |>.size

/-- Create a token under `controller`, applying token-doubling and
Food-and-Treasure replacement effects. -/
def createToken (g : Game) (controller : PlayerId) (printed : CardDef)
    (tapped := false) : Game × GameObject :=
  if (g.player controller).lost then
    g.createOneToken controller printed (tapped := tapped)
  else
    let copies := g.tokenCreateMultiplier controller
    let extraTreasure :=
      if printed.hasSubtype "Food" then g.foodTreasureReplacements controller else 0
    Id.run do
      let mut g := g
      let mut last : Option GameObject := none
      for _ in [0:copies] do
        let (g', obj) := g.createOneToken controller printed (tapped := tapped)
        g := g'
        last := some obj
      for _ in [0:copies * extraTreasure] do
        let (g', _) := g.createOneToken controller treasureToken (tapped := tapped)
        g := g'
      match last with
      | some obj => (g, g.object! obj.id)
      | none => (g, g.object! ⟨0⟩)

/-- Create `n` Treasure tokens, optionally tapped. -/
def createTreasureTokens (g : Game) (controller : PlayerId) (n : Nat)
    (tapped := false) : Game :=
  if (g.player controller).lost then
    if n == 0 then g else g.logMsg "no token is created (CR 800.4b)"
  else
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

def wolfToken : CardDef :=
  creatureToken "Wolf" #["Wolf"] 2 2 (some .green)

def dwarfToken : CardDef :=
  creatureToken "Dwarf" #["Dwarf"] 2 2 (some .red)

def bearToken : CardDef :=
  creatureToken "Bear" #["Bear"] 2 2 (some .green)

def elfToken : CardDef :=
  creatureToken "Elf" #["Elf"] 1 1 (some .green)

/-- A 1/1 white Spirit creature token with flying. -/
def spiritToken : CardDef :=
  creatureToken "Spirit" #["Spirit"] 1 1 (some .white) Keyword.flying

/-- A 4/4 white Bird Soldier creature token with flying. -/
def birdSoldierToken : CardDef :=
  creatureToken "Bird Soldier" #["Bird", "Soldier"] 4 4 (some .white) Keyword.flying

/-- A 6/6 red Dragon creature token with flying. -/
def dragonToken : CardDef :=
  creatureToken "Dragon" #["Dragon"] 6 6 (some .red) Keyword.flying

/-- A 3/1 colorless Wall artifact creature token with defender. -/
def wallToken : CardDef :=
  creatureToken "Stone Boulder" #["Wall"] 3 1 none Keyword.defender
    (types := #[.artifact, .creature])

/-- A colorless Equipment artifact token named Axe. -/
def axeToken : CardDef := {
  name := "Axe"
  types := #[.artifact]
  subtypes := #["Equipment"]
  staticAbilities := #[.equippedCreatureGets 1 0]
  activatedAbilities := #[
    { cost := { mana := ManaCost.ofGeneric 2 }
      effect := .attachToTargetCreatureYouControl
      onlyAsSorcery := true }
  ]
  isToken := true
}

/-- A Clue artifact token (CR 701.55). -/
def clueToken : CardDef := {
  name := "Clue"
  types := #[.artifact]
  subtypes := #["Clue"]
  oracleText := "{2}, Sacrifice this token: Draw a card."
  activatedAbilities := #[{
    cost := { mana := ManaCost.ofGeneric 2, sacrificeSource := true }
    effect := .draw 1
  }]
  isToken := true
}

/-- A 3/2 white Hero creature token with vigilance. -/
def hero32vigilanceToken : CardDef :=
  creatureToken "Hero" #["Hero"] 3 2 (some .white) Keyword.vigilance

/-- A 2/1 black Villain creature token with menace. -/
def villain21menaceToken : CardDef :=
  creatureToken "Villain" #["Villain"] 2 1 (some .black) Keyword.menace

/-- A 2/2 colorless Robot Villain artifact creature token. -/
def robotVillain22Token : CardDef :=
  creatureToken "Robot Villain" #["Robot", "Villain"] 2 2 none
    (types := #[.artifact, .creature])

/-- A 6/5 blue Leviathan creature token with hexproof. -/
def leviathan65hexproofToken : CardDef :=
  creatureToken "Leviathan" #["Leviathan"] 6 5 (some .blue) Keyword.hexproof

/-- A 1/1 white Soldier creature token. -/
def soldier11whiteToken : CardDef :=
  creatureToken "Soldier" #["Soldier"] 1 1 (some .white)

/-- A 1/1 green Squirrel creature token. -/
def squirrel11greenToken : CardDef :=
  creatureToken "Squirrel" #["Squirrel"] 1 1 (some .green)

/-- A 0/4 colorless Wall creature token with defender. -/
def wall04defenderToken : CardDef :=
  creatureToken "Wall" #["Wall"] 0 4 none Keyword.defender

/-- A 3/3 colorless Robot Villain artifact creature token named Doombot. -/
def doombotToken : CardDef :=
  creatureToken "Doombot" #["Robot", "Villain"] 3 3 none
    (types := #[.artifact, .creature])

/-- A 1/1 green Insect creature token. -/
def insect11greenToken : CardDef :=
  creatureToken "Insect" #["Insect"] 1 1 (some .green)

/-- A predefined Vibranium artifact token (MSH). Indestructible; `{T}: Add {C}`
that cannot be spent to cast a nonartifact spell. -/
def vibraniumToken : CardDef := {
  name := "Vibranium"
  types := #[.artifact]
  subtypes := #["Vibranium"]
  oracleText := "Indestructible\n{T}: Add {C}. This mana can't be spent to cast a nonartifact spell."
  keywords := Keyword.indestructible
  tapAddMana := #[.colorless]
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
  | .spirit => spiritToken
  | .birdSoldier => birdSoldierToken
  | .wall => wallToken
  | .dragon => dragonToken
  | .clue => clueToken
  | .hero32vigilance => hero32vigilanceToken
  | .villain21menace => villain21menaceToken
  | .robotVillain22 => robotVillain22Token
  | .leviathan65hexproof => leviathan65hexproofToken
  | .soldier11white => soldier11whiteToken
  | .squirrel11green => squirrel11greenToken
  | .wall04defender => wall04defenderToken
  | .doombot => doombotToken
  | .insect11green => insect11greenToken
  | .vibranium => vibraniumToken

/-- Create `n` tokens of `kind`. -/
def createKindTokens (g : Game) (controller : PlayerId) (kind : TokenKind)
    (n : Nat) (tapped := false) (attacking := false) : Game :=
  if (g.player controller).lost then
    if n == 0 then g else g.logMsg "no token is created (CR 800.4b)"
  else
  Id.run do
    let mut g := g
    let dest := if attacking then some g.defendingPlayer else none
    for _ in [0:n] do
      let (g', obj) := g.createToken controller (tokenPrinted kind) (tapped := tapped)
      g := g'
      if attacking then
        g := g.setObject { (g.object! obj.id) with
          status := { (g.object! obj.id).status with
            attacking := true
            attackingWhom := dest } }
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
        let subtypeOk :=
          match src.status.chosenCreatureType with
          | some t => g.hasSubtype target t
          | none => subtypes.isEmpty || subtypes.any (g.hasSubtype target)
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

/-- +P/+0 from `powerPerMountain` (e.g. Desert Were-Worm). -/
def mountainPowerBonus (g : Game) (o : GameObject) : Int :=
  if o.printed.powerPerMountain == 0 then 0
  else
    let n :=
      (g.permanentsOf o.you).filter (fun p => g.hasSubtype p "Mountain") |>.size
    Int.ofNat (o.printed.powerPerMountain * n)

/-- +P/+0 from graveyards with seven or more cards (Master's Councillors). -/
def fatGraveyardPowerBonus (g : Game) (o : GameObject) : Int :=
  o.staticAbilities.foldl (fun acc ab =>
    match ab with
    | .powerPerFatGraveyard p =>
      let n := g.players.filter (fun pl => pl.graveyard.size >= 7) |>.size
      acc + p * (n : Int)
    | _ => acc) 0

/-- +1/+1 for each artifact you control (Iron Man Armor until EOT). -/
def artifactCountPump (g : Game) (o : GameObject) : Int × Int :=
  if !o.status.pumpPerArtifactUntilEot || !o.isOnBattlefield then (0, 0)
  else
    let n : Int :=
      Int.ofNat ((g.permanentsOf o.you).filter (fun p => p.printed.isArtifact ||
        p.status.additionalArtifactUntilEot) |>.size)
    (n, n)

def snapshotPT (g : Game) (o : GameObject) : Int × Int :=
  let n : Int := o.status.plusOnePlusOne
  #[g.characteristicBasePT o, o.status.pump, (n, n), g.attachedStatBonus o,
      g.lordStatBonus o, g.enduringStorySelfBonus o, g.enduringStoryTeamBonus o,
      (g.mountainPowerBonus o, (0 : Int)),
      (g.fatGraveyardPowerBonus o, (0 : Int)),
      g.artifactCountPump o].foldl
    addStats (0, 0)

/-- Power of `o` as last known information (CR 113.7a / 208.2). -/
def snapshotPower (g : Game) (o : GameObject) : Int :=
  (g.snapshotPT o).1

/-- Toughness of `o` as last known information (CR 113.7a / 208.2). -/
def snapshotToughness (g : Game) (o : GameObject) : Int :=
  (g.snapshotPT o).2

/-- True when `o` replaces an opposing creature dying with exile. -/
def exilesOppDeath? (o : GameObject) : Bool :=
  o.printed.exileOppCreaturesInstead ||
    o.staticAbilities.any (fun
      | .exileOppDeathCreateWolf => true
      | _ => false)

/-- True when `o` also creates a Wolf after that replacement (Head of the Hunt). -/
def createsWolfOnOppExileDeath? (o : GameObject) : Bool :=
  o.staticAbilities.any (fun
    | .exileOppDeathCreateWolf => true
    | _ => false)

/-- Permanents that exile opposing creatures that would die. Uses the SBA
snapshot when one is locked so a simultaneous death of the source still
applies (CR 614.4 / 614.6). -/
def deathReplacementObjects (g : Game) : Array GameObject :=
  match g.lockedDeathReplacements with
  | some xs => xs
  | none => g.battlefield.filter exilesOppDeath?

/-- Controller of a Head-of-the-Hunt-style replacement, if `dying` is an
opposing creature that would go to a graveyard. -/
def exileInsteadSource? (g : Game) (dying : GameObject) : Option GameObject :=
  g.deathReplacementObjects.find? (fun o =>
    o.id != dying.id &&
      match o.controller, dying.controller with
      | some p, some q => p != q
      | _, _ => false)

/-- Controller of a Head-of-the-Hunt-style replacement, if `dying` is an
opposing creature that would go to a graveyard. -/
def exileInsteadController? (g : Game) (dying : GameObject) : Option PlayerId :=
  (g.exileInsteadSource? dying).bind (·.controller)

/-- CR 614.6: if this death would be replaced with exile, the die event
never happens. -/
def wouldExileInsteadOfDying (g : Game) (dying : GameObject) : Bool :=
  dying.status.untilEotExileIfDies || (g.exileInsteadSource? dying).isSome

/-- Dies triggers of a creature leaving the battlefield for a graveyard
(CR 700.4 / 603.6c). A replaced death never happens (CR 614.6), so this
is empty when `dest` is not a graveyard. -/
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
  let wouldGoToGy :=
    match dest with
    | .graveyard _ => true
    | _ => false
  -- Snapshot the replacement source before the object leaves so a
  -- simultaneous death of Head of the Hunt still applies (CR 614.6).
  let headSource :=
    if old.zone == .battlefield && old.isCreature && wouldGoToGy then
      g.exileInsteadSource? old
    else none
  let headExile := headSource.isSome
  let smiteExile :=
    old.zone == .battlefield && old.status.untilEotExileIfDies && wouldGoToGy
  let finalityExile :=
    old.zone == .battlefield && wouldGoToGy && old.status.finality > 0
  let exileInstead := headExile || smiteExile || finalityExile
  -- CR 614.6: the original move-to-graveyard event never happens.
  let dest := if exileInstead then Zone.exile else dest
  let g :=
    if finalityExile then
      g.logMsg s!"A finality counter exiles {old.name} instead of putting it into a graveyard"
    else g
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
    if died && !g.suppressOthersDie then
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
  let leavingPlay :=
    (old.zone == .battlefield || old.zone == .stack) &&
      dest != .battlefield && dest != .stack
  let printed :=
    if leavingPlay && old.status.transformed then
      match old.printed.otherFace with
      | some front =>
        { front with otherFace := some { old.printed with otherFace := none } }
      | none => old.printed
    else old.printed
  let fresh : GameObject := {
    id := newId
    printed
    owner := old.owner
    controller := controller
    defaultController := if dest == .battlefield then controller else none
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
  let gyLeave :=
    match old.zone, old.owner with
    | .graveyard owner, _ =>
      if old.printed.isCreature &&
          (match dest with | .graveyard _ => false | _ => true) then
        (g.permanentsOf owner).foldl (fun acc o =>
          acc ++ o.waitingTriggersFor owner .creatureCardLeavesYourGy) #[]
      else (#[] : Array WaitingTrigger)
    | _, _ => (#[] : Array WaitingTrigger)
  let nontokenDie :=
    if died && !old.printed.isToken then
      match old.controller with
      | some p =>
        g.battlefield.foldl (fun acc o =>
          if o.id == old.id then acc
          else
            match o.controller with
            | some q =>
              if q == p then
                acc ++ o.waitingTriggersFor q .nontokenYouControlDies
              else acc
            | none => acc) (#[] : Array WaitingTrigger)
      | none => (#[] : Array WaitingTrigger)
    else (#[] : Array WaitingTrigger)
  let goblinOrcArmyDie :=
    if died then
      match old.controller with
      | some p =>
        if g.hasSubtype old "Goblin" || g.hasSubtype old "Orc" ||
            g.hasSubtype old "Army" then
          g.battlefield.foldl (fun acc o =>
            if o.id == old.id then acc
            else
              match o.controller with
              | some q =>
                if q == p then
                  acc ++ o.waitingTriggersFor q .anotherGoblinOrcArmyDies
                else acc
              | none => acc) (#[] : Array WaitingTrigger)
        else (#[] : Array WaitingTrigger)
      | none => (#[] : Array WaitingTrigger)
    else (#[] : Array WaitingTrigger)
  let attackingDie :=
    if died && old.status.attacking then
      match old.controller with
      | some p =>
        let fromOthers :=
          g.battlefield.foldl (fun acc o =>
            match o.controller with
            | some q =>
              if q == p then
                acc ++ o.waitingTriggersFor q .attackingCreatureYouControlDies
              else acc
            | none => acc) (#[] : Array WaitingTrigger)
        fromOthers ++ old.waitingTriggersFor p .attackingCreatureYouControlDies
      | none => (#[] : Array WaitingTrigger)
    else (#[] : Array WaitingTrigger)
  -- After the object has left: sources still on the battlefield see
  -- creature cards going to a graveyard (Robot Domination; MSH 138).
  let creatureCardToGy :=
    if g.suppressCreatureCardsToGy then (#[] : Array WaitingTrigger)
    else
      match dest with
      | .graveyard owner =>
        if old.printed.isCreature && !old.printed.isToken then
          g.battlefield.foldl (fun acc o =>
            match o.controller with
            | some p =>
              if p == owner then
                acc ++ o.waitingTriggersFor p .creatureCardsPutIntoYourGy
              else acc
            | none => acc) (#[] : Array WaitingTrigger)
        else (#[] : Array WaitingTrigger)
      | _ => (#[] : Array WaitingTrigger)
  let g := { g with
    waitingTriggers :=
      g.waitingTriggers ++ dying ++ othersDie ++ leaving ++ gyLeave ++
        nontokenDie ++ goblinOrcArmyDie ++ attackingDie ++ creatureCardToGy
    creatureDiedThisTurn := g.creatureDiedThisTurn || died }
  let g :=
    if died then
      { g with battlefieldCreaturesToGyThisTurn :=
        g.battlefieldCreaturesToGyThisTurn.push newId }
    else g
  let g :=
    if died && old.status.attacking then
      { g with lastDiedAttacker := some newId }
    else g
  let g :=
    if exileInstead then
      g.logMsg s!"{old.name} is exiled instead of dying (CR 614.6)"
    else g
  let g :=
    if old.zone == .battlefield && !old.linkedExile.isEmpty then
      Id.run do
        let mut g := g
        for exId in old.linkedExile do
          match g.findObject? exId with
          | some o =>
            if o.zone == .exile then
              let name := o.name
              match o.returnToZone with
              | some (.hand p) =>
                let (g', _) := g.move o.id (.hand p) none
                g := g'
                g := g.logMsg s!"{name} returns to {(g.player p).name}'s hand"
              | some (.graveyard p) =>
                let (g', _) := g.move o.id (.graveyard p) none
                g := g'
                g := g.logMsg s!"{name} returns to {(g.player p).name}'s graveyard"
              | _ =>
              if o.printed.isAura then
                match g.battlefield.find? (fun h => h.isCreature) with
                | none =>
                  g := g.logMsg
                    s!"{name} remains in exile (can't be attached legally; CR 614.6)"
                | some host =>
                  let hostId := host.id
                  let (g', returnedId) := g.move o.id .battlefield (some o.owner)
                  g := g'
                  let returned := g.object! returnedId
                  g := g.setObject { returned with attachedTo := some hostId }
                  g := g.logMsg
                    s!"{name} returns attached to {host.name} (does not target)"
                  let returned := g.object! returnedId
                  match returned.controller with
                  | some p =>
                    g := { g with waitingTriggers :=
                      g.waitingTriggers ++ returned.waitingTriggersFor p .entering }
                  | none => pure ()
              else
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
  -- The modified exile event may include creating a Wolf (Head of the Hunt).
  -- Use the snapshot source: the original die event never happened (CR 614.6).
  let g :=
    match headSource with
    | some src =>
      if createsWolfOnOppExileDeath? src then
        match src.controller with
        | some p =>
          let (g, _) := g.createToken p wolfToken
          g.logMsg s!"{(g.player p).name} creates a Wolf (exiled instead of dying)"
        | none => g
      else g
    | none => g
  let g :=
    if old.zone == .battlefield then
      let g := g.restoreCopiesUntilSourceLeaves old.id
      g.restoreControlUntilSourceLeaves old.id
    else g
  let g :=
    match g.pendingLokiCopy with
    | some (p, some id, _) =>
      if id == old.id then
        { g with pendingLokiCopy := some (p, none, old.lastKnownPower.getD old.power) }
      else g
    | _ => g
  (g, newId)

/-- Move `o` to its owner's graveyard and log `reason`. Exile-if-dies
replacements are applied by `move` (CR 614.1 / 614.6). -/
def moveToOwnerGraveyard (g : Game) (o : GameObject) (reason : String) : Game :=
  let g := g.logMsg reason
  (g.move o.id (.graveyard o.owner) none).1

/-- Move several objects to their owners' graveyards as one event.
Sources that also leave do not see “creature cards put into your
graveyard” (Robot Domination; MSH 138). -/
def moveSimultaneousToGraveyard (g : Game) (ids : Array ObjectId) : Game :=
  let objs := ids.filterMap g.findObject?
  let leavingIds := objs.map (·.id)
  let gyOwners :=
    objs.foldl (fun acc o =>
      if o.printed.isCreature && !o.printed.isToken &&
          !acc.any (· == o.owner) then
        acc.push o.owner
      else acc) (#[] : Array PlayerId)
  let extra :=
    if gyOwners.isEmpty then (#[] : Array WaitingTrigger)
    else
      g.battlefield.foldl (fun acc o =>
        if leavingIds.any (· == o.id) then acc
        else
          match o.controller with
          | some p =>
            if gyOwners.any (· == p) then
              acc ++ o.waitingTriggersFor p .creatureCardsPutIntoYourGy
            else acc
          | none => acc) (#[] : Array WaitingTrigger)
  let g := { g with
    waitingTriggers := g.waitingTriggers ++ extra
    suppressCreatureCardsToGy := true }
  let g :=
    objs.foldl (fun g o =>
      match g.findObject? o.id with
      | some o => g.moveToOwnerGraveyard o s!"{o.name} is put into its owner's graveyard"
      | none => g) g
  { g with suppressCreatureCardsToGy := false }

/-- Put `id` onto the battlefield under `controller`, then set tap, sickness,
and optional attachment. `applyHope` applies Arwen-style enter-with-counters
using weavers that were already present. -/
def putOntoBattlefield (g : Game) (id : ObjectId) (controller : PlayerId)
    (tapped := false) (summoningSick := true)
    (attachedTo : Option ObjectId := none) (applyHope := true) : Game × ObjectId :=
  if (g.player controller).lost then
    let name := (g.object! id).name
    (g.logMsg s!"{name} remains in its current zone (CR 800.4b)", id)
  else
    let asOf := g.timestamp
    let (g, newId) := g.move id .battlefield (some controller)
    let o := g.object! newId
    let o := { o with
      status := { o.status with tapped := tapped, summoningSick := summoningSick } }
    let o :=
      match attachedTo with
      | some host => { o with attachedTo := some host }
      | none => o
    let g := g.setObject o
    let g := if applyHope then g.applyHopeEnterCounters (g.object! newId) asOf else g
    (g, newId)

/-- If 0 or 1 living players remain, set the game result (CR 104). -/
def decideGameIfFinished (g : Game) : Option Game :=
  let living := g.livingPlayers
  if living.size == 0 then
    some ({ g with result := some .draw } |>.logMsg "The game is a draw")
  else if living.size == 1 then
    let w := living[0]!
    some ({ g with result := some (.won w.id) } |>.logMsg s!"{w.name} wins the game")
  else none

/-- True when this stack object is a card (CR 800.4a). Activated and
triggered abilities, and copies of spells, are not represented by cards. -/
def representedByCard (o : GameObject) : Bool :=
  o.abilityEffect.isNone && o.triggeredAbility.isNone && !o.isCopy

/-- Change `o`'s controller unless that player has left (CR 800.4b). -/
def changeControl (g : Game) (o : GameObject) (p : PlayerId) : Game :=
  if (g.player p).lost then
    g.logMsg s!"{o.name} does not change control (CR 800.4b)"
  else if o.controlledBy p then g
  else
    g.setObject { o with controller := some p, controlChanged := true }
      |>.logMsg s!"{(g.player p).name} gains control of {o.name}"

/-- End a control-changing effect on `o` (CR 800.4a / 800.4c). -/
def endControlChangingEffect (g : Game) (o : GameObject) : Game :=
  match g.findObject? o.id with
  | none => g
  | some o =>
    if !o.controlChanged then
      g.setObject { o with status := { o.status with controlUntilEot := false } }
    else
      let dest := o.defaultController.getD o.owner
      if (g.player dest).lost then
        let name := o.name
        let (g, _) := g.move o.id .exile none
        g.logMsg s!"{name} is exiled (CR 800.4c)"
      else
        let g := g.setObject { o with
          controller := some dest
          controlChanged := false
          status := { o.status with controlUntilEot := false } }
        g.logMsg s!"{o.name} reverts to {(g.player dest).name}'s control"

/-- Gain control of `o` until end of turn (CR 611.2a). -/
def giveControlUntilEot (g : Game) (o : GameObject) (p : PlayerId) : Game :=
  if (g.player p).lost then
    g.logMsg s!"{o.name} does not change control (CR 800.4b)"
  else
    let g := g.changeControl o p
    match g.findObject? o.id with
    | none => g
    | some o =>
      g.setObject { o with status := { o.status with controlUntilEot := true } }

/-- Remove `o` from the game. Battlefield permanents use `move` so
until-leaves one-shots return (CR 610.3 / 800.4a). Ante stays (CR 800.4n). -/
def objectLeavesTheGame (g : Game) (o : GameObject) (leavingPlayer : PlayerId) : Game :=
  if o.zone == .ante then g
  else if o.zone == .battlefield then
    let (g, newId) := g.move o.id .exile none
    let g := { g with
      waitingTriggers :=
        g.waitingTriggers.filter (fun wt => wt.controller != leavingPlayer) }
    g.ceaseToExist newId
  else
    g.removeFromZoneList o.id o.zone |>.ceaseToExist o.id

/-- After `p` leaves, pending costs they would pay are not paid (CR 800.4f)
and other pending choices they would make are skipped or passed on
(CR 800.4g / 800.4h / 800.4j). Does not grant priority. -/
def redirectPendingAfterLeave (g : Game) (p : PlayerId) : Game :=
  match g.pending with
  | .none => g
  | .declareAttackers =>
    if g.activePlayer == p then
      { g with pending := .none }
        |>.logMsg "no active player declares attackers (CR 800.4j)"
    else g
  | .declareBlockers =>
    if g.currentBlockersPlayer == p then
      let rest := g.blockersQueue.extract 1 g.blockersQueue.size
      if rest.isEmpty then
        { g with pending := .none, blockersQueue := #[] }
          |>.logMsg "no active player remains to declare blockers (CR 800.4j)"
      else
        { g with pending := .declareBlockers, blockersQueue := rest }
    else g
  | .payOrLetCounter q _ spellId =>
    if q == p then
      let g := { g with pending := .none }
      let g := g.logMsg s!"{(g.player p).name} does not pay (CR 800.4f)"
      match g.findObject? spellId with
      | none => g
      | some o =>
        let g := g.removeFromZoneList o.id .stack |>.ceaseToExist o.id
        g.logMsg s!"{o.name} is countered"
    else g
  | .mayPayGeneric q _ =>
    if q == p then
      { g with pending := .none }
        |>.logMsg s!"{(g.player p).name} does not pay (CR 800.4f)"
    else g
  | .chooseSacrificeCreature q chosen remaining =>
    if q != p then g
    else
      match remaining.find? (fun r => g.stillInGame r) with
      | none => { g with pending := .none }
      | some np =>
        { g with
          pending := .chooseSacrificeCreature np chosen
            (remaining.filter (fun r => r != np && g.stillInGame r)) }
  | .chooseDiscardCard q remaining =>
    if q != p then g
    else
      match remaining.find? (fun r => g.stillInGame r) with
      | none => { g with pending := .none }
      | some np =>
        { g with
          pending := .chooseDiscardCard np
            (remaining.filter (fun r => r != np && g.stillInGame r)) }
  | .chooseTriggerToStack q =>
    if q == p then { g with pending := .none } else g
  | .chooseLegend q _ _ =>
    if q == p then { g with pending := .none } else g
  | .assignCombatDamage q forAttackers =>
    if q == p then
      { g with pending := .assignCombatDamage (g.nextLiving p) forAttackers }
        |>.logMsg
          s!"{(g.player (g.nextLiving p)).name} assigns combat damage (CR 800.4h)"
    else g
  | .activateManaAbilities q | .chooseMode q | .chooseTargets q
  | .chooseAdditionalCost q | .chooseKicker q | .chooseGift q
  | .chooseTeamwork q | .chooseTeamworkCreatures q _ =>
    if q == p then { g with pending := .none, proposedSpell := none } else g
  | .sacrificePermanent q _ | .sacrificeCreature q | .scry q _
  | .mayDiscardDraw q _ | .mayAttachEquipment q _ | .tapHumans q
  | .recruitDiscard q | .chooseRingBearer q | .chooseLibraryPlacement q _
  | .maySacrificeAnotherBolg q _ | .putOnBottom q _ | .declareMulligan q =>
    if q == p then { g with pending := .none } else g
  | .resolveRandom _ => g

/-- `p` loses and leaves the game (CR 800.4 / 800.4a). Owned objects leave
immediately (until-leaves one-shots return); control-changing effects that
gave them control end; their non-card stack objects cease; remaining objects
they control are exiled. This is not a state-based action. -/
def playerLeavesGame (g : Game) (p : PlayerId) : Game :=
  if (g.player p).leftTheGame then g
  else
    let g := g.setPlayer { (g.player p) with lost := true, leftTheGame := true }
    let g := g.logMsg s!"{(g.player p).name} leaves the game"
    let owned := g.objects.filter (fun o => o.owner == p && o.zone != .ante)
    let g :=
      owned.foldl (fun acc o =>
        match acc.findObject? o.id with
        | none => acc
        | some o => acc.objectLeavesTheGame o p) g
    let g :=
      (g.battlefield.filter (fun o => o.controlChanged && o.controlledBy p)).foldl
        (fun acc o =>
          match acc.findObject? o.id with
          | none => acc
          | some o => acc.endControlChangingEffect o) g
    let g :=
      g.objects.foldl (fun acc o =>
        if o.zone == .stack && o.controlledBy p && !representedByCard o then
          acc.removeFromZoneList o.id .stack |>.ceaseToExist o.id
        else acc) g
    let still := g.objects.filter (fun o => o.controlledBy p)
    let g :=
      still.foldl (fun acc o =>
        match acc.findObject? o.id with
        | none => acc
        | some o =>
          let name := o.name
          let (acc, _) := acc.move o.id .exile none
          acc.logMsg s!"{name} is exiled (CR 800.4a)") g
    let g := { g with
      waitingTriggers := g.waitingTriggers.filter (fun wt => wt.controller != p) }
    let g :=
      match g.proposedSpell with
      | some prop =>
        if prop.caster == p then { g with proposedSpell := none } else g
      | none => g
    let g :=
      if g.priority == p then { g with priority := g.nextLiving p } else g
    g.redirectPendingAfterLeave p

/-- Perform CR 800.4a for every player who has lost but has not yet left.
Skipped when the game has already ended (two-player games, CR 104.2a). -/
def leavePlayersWhoLost (g : Game) : Game :=
  if g.over then g
  else
    g.players.foldl (fun acc pl =>
      if pl.lost && !pl.leftTheGame then acc.playerLeavesGame pl.id else acc) g

def emptyManaPools (g : Game) : Game :=
  Id.run do
    let mut g := g
    for pl in g.players do
      if !pl.manaPool.isEmpty then
        g := g.logMsg s!"{pl.name} empties mana pool ({pl.manaPool})"
        g := g.setPlayer { pl with manaPool := ManaPool.empty }
    return g

/-- Draw one card with no replacement effects (CR 121). -/
def drawOneCard (g : Game) (p : PlayerId) : Game :=
  let pl := g.player p
  if pl.library.isEmpty then
    let g := g.setPlayer { pl with drewFromEmpty := true }
    g.logMsg s!"{pl.name} tries to draw from an empty library"
  else
    let top := pl.library.back!
    let cardName := (g.object! top).name
    let rest := pl.library.pop
    let g := g.setPlayer { pl with library := rest }
    let (g, _) := g.move top (.hand p) none
    let pl := g.player p
    let drawn := pl.cardsDrawnThisTurn + 1
    let drawStepDrawn :=
      if g.step == .draw && g.activePlayer == p then
        pl.cardsDrawnThisDrawStep + 1
      else pl.cardsDrawnThisDrawStep
    let g := g.setPlayer { pl with
      cardsDrawnThisTurn := drawn
      cardsDrawnThisDrawStep := drawStepDrawn }
    let g := g.logMsg s!"{pl.name} draws {cardName}"
    let firstOfTheirDrawStep :=
      g.step == .draw && g.activePlayer == p && drawStepDrawn == 1
    Id.run do
      let mut g := g
      for o in g.permanentsOf p do
        g := { g with waitingTriggers :=
          g.waitingTriggers ++ o.waitingTriggersFor p .youDraw }
        if drawn == 2 then
          g := { g with waitingTriggers :=
            g.waitingTriggers ++ o.waitingTriggersFor p .youDrawSecondCard }
      for opp in g.livingOpponents p do
        for o in g.permanentsOf opp.id do
          if !firstOfTheirDrawStep then
            g := { g with waitingTriggers :=
              g.waitingTriggers ++
                o.waitingTriggersFor opp.id .opponentDrawsExceptFirstDrawStep }
          if drawn == 2 then
            g := { g with waitingTriggers :=
              g.waitingTriggers ++
                o.waitingTriggersFor opp.id .opponentDrawsSecondCard }
      return g

/-- How many cards replace one draw (`2^n` Bard effects, except the first
card of your draw step). -/
def drawMultiplier (g : Game) (p : PlayerId) : Nat :=
  let pl := g.player p
  let firstOfYourDrawStep :=
    g.step == .draw && g.activePlayer == p && pl.cardsDrawnThisDrawStep == 0
  if firstOfYourDrawStep then 1
  else
    let n := (g.permanentsOf p).filter (fun o =>
      o.printed.drawTwoExceptFirstDrawStep) |>.size
    Nat.pow 2 n

def draw (g : Game) (p : PlayerId) (n : Nat := 1) : Game :=
  Id.run do
    let mut g := g
    for _ in [0:n] do
      let copies := g.drawMultiplier p
      for _ in [0:copies] do
        let pl := g.player p
        if pl.drewFromEmpty then
          return g
        g := g.drawOneCard p
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

/-- True when a `--norandom` result is still required. -/
def pendingRandom? (g : Game) : Option RandomRequest :=
  match g.pending with
  | .resolveRandom req => some req
  | _ => none

/-- Shuffle `p`'s library (CR 103.3 / 701.19). With `norandom`, a library
of two or more cards becomes `Pending.resolveRandom` instead of using `rng`. -/
def shuffleLibrary (g : Game) (p : PlayerId) : Game :=
  let pl := g.player p
  if g.norandom then
    if pl.library.size ≤ 1 then
      g.logMsg s!"{pl.name} shuffles their library"
    else
      { g with pending := .resolveRandom (.shuffleLibrary p) }
        |>.logMsg s!"{pl.name} shuffles their library"
  else
    let (rng, lib) := g.rng.shuffle pl.library
    { g with rng := rng } |>.setPlayer { pl with library := lib }
     |>.logMsg s!"{pl.name} shuffles their library"

/-- Record `after` and shuffle. If `--norandom` pauses, `after` stays on the
game until the host supplies an order. -/
def requestShuffle (g : Game) (p : PlayerId) (after : AfterRandom := .none) : Game :=
  { g with afterRandom := after }.shuffleLibrary p

/-- Move `ids` into `dest` in this order. For a library, first listed becomes
the new bottom of that group. -/
def moveIdsInOrder (g : Game) (ids : Array ObjectId) (dest : Zone) : Game :=
  match dest with
  | .library owner =>
    Id.run do
      let mut g := g
      let mut newBottom : Array ObjectId := #[]
      for id in ids do
        let (g', newId) := g.move id dest none
        g := g'
        newBottom := newBottom.push newId
      let pl := g.player owner
      let without := newBottom.foldl (fun lib id => lib.filter (· != id)) pl.library
      g.setPlayer { pl with library := newBottom ++ without }
  | _ =>
    ids.foldl (fun acc id => (acc.move id dest none).1) g

/-- Put `ids` into `dest` in a random order. With `norandom` and two or more
cards, becomes `Pending.resolveRandom`. -/
def requestOrderInto (g : Game) (ids : Array ObjectId) (dest : Zone)
    (log : String) : Game :=
  if ids.size ≤ 1 then
    g.moveIdsInOrder ids dest |>.logMsg log
  else if g.norandom then
    { g with pending := .resolveRandom (.orderInto ids dest) }.logMsg log
  else
    let (rng, ordered) := g.rng.shuffle ids
    { g with rng := rng }.moveIdsInOrder ordered dest |>.logMsg log

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

/-- Printed abilities still apply unless The Wondrous Wasp (or similar)
is making the permanent lose them (MSH 145 / 190). -/
def retainsPrintedAbilities (g : Game) (o : GameObject) : Bool :=
  !o.status.losesAbilitiesGrantedBy.any (fun id =>
    match g.findObject? id with
    | some src => src.isOnBattlefield
    | none => false)

def currentKeywords (g : Game) (o : GameObject) : Keywords :=
  let printedKw :=
    if g.retainsPrintedAbilities o then o.printed.keywords else Keywords.none
  let base :=
    Keywords.merge
      (Keywords.merge (Keywords.merge printedKw o.grantedUntilEot)
        (g.attachedGrantedKeywords o))
      (g.enduringStoryKeywords o)
  if o.status.shadow > 0 then { base with shadow := true } else base

/-- Whether `o` currently has shadow (printed, granted, or from a counter).
Multiple instances are redundant. -/
def hasShadow (g : Game) (o : GameObject) : Bool :=
  (g.currentKeywords o).shadow

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

/-- Okoye: attacking creature tokens you control have first strike. -/
def okoyeGrantsFirstStrike (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield && o.status.attacking && o.printed.isToken &&
    match o.controller with
    | none => false
    | some p =>
      (g.permanentsOf p).any (fun src =>
        src.staticAbilities.any (fun
          | .msh .attackingCreatureTokensYouControlHaveFirst => true
          | _ => false))

/-- Whether `o` has first strike, printed or granted (CR 702.7). -/
def hasFirstStrike (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.firstStrike) || g.hasKeyword o (·.doubleStrike) ||
    g.okoyeGrantsFirstStrike o

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

/-- Whether `o` has lifelink, printed, granted until end of turn, or from a
lifelink counter (CR 702.15). -/
def hasLifelink (g : Game) (o : GameObject) : Bool :=
  o.status.lifelinkCounters > 0 ||
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
  let defender :=
    match attacker.status.attackingWhom with
    | some pid => pid
    | none => g.defendingPlayer
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
    g.hasFlying blocker || (g.currentKeywords blocker).reach) &&
  (!(g.hasShadow attacker) || g.hasShadow blocker) &&
  (!(g.hasShadow blocker) || g.hasShadow attacker) &&
  !(match attacker.status.cantBeBlockedByPlayer with
    | some pid => blocker.controlledBy pid
    | none => false) &&
  !(attacker.status.cantBeBlockedExceptByHasteUntilEot && !g.hasHaste blocker)

/-- Whether `src` currently grants trample to `target` (CR 604.2). -/
def grantsTrampleTo (g : Game) (src target : GameObject) : Bool :=
  isLordOf src target &&
  src.staticAbilities.any (fun ab =>
    match ab.trampleSubtypes? with
    | some subtypes => subtypes.any (g.hasSubtype target)
    | none => false)

/-- Lore counters among Sagas `p` controls. -/
def loreAmongSagas (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).foldl (fun acc o =>
    if o.printed.saga.isSome then acc + o.status.lore else acc) 0

/-- True when `id` is the source of a chapter ability waiting or on the stack
(CR 714.4). -/
def sagaChapterPending (g : Game) (id : ObjectId) : Bool :=
  let waiting :=
    g.waitingTriggers.any (fun wt =>
      wt.source.id == id &&
        match wt.ability with
        | .sagaChapter _ _ => true
        | _ => false)
  let stacked :=
    g.stack.any (fun e =>
      match g.findObject? e.objectId with
      | some o =>
        o.sourceId == some id &&
          match o.triggeredAbility with
          | some (.sagaChapter _ _) => true
          | _ => false
      | none => false)
  waiting || stacked

/-- Whether `o` currently has hexproof and indestructible from Tom Bombadil's
lore-threshold static. -/
def loreThresholdProtection (g : Game) (o : GameObject) : Bool :=
  match o.printed.hexproofIndestructibleIfLore, o.controller with
  | some n, some p => g.loreAmongSagas p ≥ n
  | _, _ => false

/-- True when a grantor of hexproof or damage prevention is still on the
battlefield. -/
def grantorStillInPlay (g : Game) (id : ObjectId) : Bool :=
  match g.findObject? id with
  | some o => o.isOnBattlefield
  | none => false

def hasHexproof (g : Game) (o : GameObject) : Bool :=
  hasPrintedOrEot o (·.hexproof) || g.loreThresholdProtection o ||
    o.status.hexproofGrantedBy.any g.grantorStillInPlay ||
    (match o.controller with
     | none => false
     | some p =>
       (o.isCreature && o.status.gotPlusOneThisTurn &&
         (g.permanentsOf p).any (fun src =>
           src.printed.staticAbilities.any (fun
             | .msh .eachCreatureYouControlThatYouVePutOneOr => true
             | _ => false))) ||
       (g.permanentsOf p).any (fun src =>
         src.status.shield > 0 &&
           src.staticAbilities.any (fun
             | .youAndOtherSubtypeHaveHexproofIfShield subtype =>
               src.id == o.id ||
                 (o.id != src.id && g.hasSubtype o subtype) ||
                 -- "you and other Heroes" — the player has hexproof via a dummy check
                 false
             | _ => false)))

/-- True when damage that would be dealt by `src` is prevented (Old Fat
Spider chapter II). -/
def sourceDamagePrevented (g : Game) (src : GameObject) : Bool :=
  src.status.preventDamageGrantedBy.any g.grantorStillInPlay

/-- Whether `o` has deathtouch, printed or granted until end of turn (CR 702.2). -/
def hasDeathtouch (_g : Game) (o : GameObject) : Bool :=
  hasPrintedOrEot o (·.deathtouch)

/-- Whether `o` has indestructible (CR 702.12). An until-end-of-turn effect can
make it lose the keyword. -/
def hasIndestructible (g : Game) (o : GameObject) : Bool :=
  (o.printedOrUntilEot.indestructible ||
    o.status.indestructibleCounters > 0 ||
    g.loreThresholdProtection o) &&
  !(o.isOnBattlefield && o.status.untilEotLosesIndestructible)

/-- Mana value of `o` (CR 202.3). `{X}` is the chosen value while the object
is on the stack and 0 otherwise (rulings 178 / 185 / 186). -/
def objectManaValue (_g : Game) (o : GameObject) : Nat :=
  let printed := o.printed.manaValue
  if o.zone != .stack then printed
  else printed + o.chosenX.getD 0

/-- Whether `o` has trample, printed, granted until end of turn, or granted by
a static ability (CR 702.19, 604.2). -/
def hasTrample (g : Game) (o : GameObject) : Bool :=
  o.printedOrUntilEot.trample ||
  o.status.trampleCounters > 0 ||
  (o.isOnBattlefield && g.battlefield.any (fun src =>
    g.grantsTrampleTo src o ||
      (src.attachedTo == some o.id &&
        src.staticAbilities.any (fun
          | .equippedGetsTrampleAndCombatTreasures _ _ => true
          | _ => false))))

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
  if !g.combatHasFirstStrike && g.firstStrikeAssignedThisCombat.isEmpty then all
  else if !g.firstStrikeDamageDone then all.filter (g.hasFirstStrike)
  else
    all.filter (fun o =>
      if g.firstStrikeAssignedThisCombat.any (· == o.id) then
        g.hasDoubleStrike o
      else
        !g.hasFirstStrike o || g.hasDoubleStrike o)

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
    let amt :=
      match g.assignCombatDamageEqualToughness with
      | some pid =>
        if source.controlledBy pid && g.toughness source > g.power source then
          g.toughness source
        else g.power source
      | none => g.power source
    max amt 0

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
      -- Players losing (CR 704.5a–c). They leave after this SBA pass
      -- if the game continues (CR 800.4 / 800.4a).
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
      -- Snapshot exile-instead replacements first so a simultaneous death
      -- of Head of the Hunt still exiles opposing creatures.
      let snap := g.battlefield.filter exilesOppDeath?
      let victims :=
        g.battlefield.filterMap (fun o =>
          if !o.isCreature then none
          else
            let t := g.toughness o
            if t ≤ 0 then some (o, s!"{o.name} dies (toughness {t})")
            else if o.status.damage ≥ t && !g.hasIndestructible o then
              some (o, s!"{o.name} dies from lethal damage")
            else if o.status.dealtDeathtouch && !g.hasIndestructible o then
              some (o, s!"{o.name} dies from deathtouch")
            else none)
      if !victims.isEmpty then
        g := { g with
          lockedDeathReplacements := some snap
          suppressOthersDie := true }
        -- CR 614.6: a replaced death never happens, so only creatures that
        -- will actually go to a graveyard cause “die” triggers. A Bee that
        -- dies at the same time as another creature that *does* die still
        -- sees that event (ruling 139).
        let actualDeaths := victims.filter (fun pair =>
          !g.wouldExileInsteadOfDying pair.1)
        if !actualDeaths.isEmpty then
          for o in g.battlefield do
            if actualDeaths.any (fun pair => pair.1.id != o.id) then
              match o.controller with
              | some p =>
                g := { g with waitingTriggers :=
                  g.waitingTriggers ++
                    o.waitingTriggersFor p .oneOrMoreOtherCreaturesDie }
              | none => pure ()
          -- “One or more creature cards” fires once per source still on
          -- the battlefield (Robot Domination; MSH 138).
          let leavingIds := victims.map (fun pair => pair.1.id)
          let gyOwners :=
            actualDeaths.foldl (fun acc pair =>
              if pair.1.printed.isCreature && !pair.1.printed.isToken &&
                  !acc.any (· == pair.1.owner) then
                acc.push pair.1.owner
              else acc) (#[] : Array PlayerId)
          if !gyOwners.isEmpty then
            for o in g.battlefield do
              if !leavingIds.any (· == o.id) then
                match o.controller with
                | some p =>
                  if gyOwners.any (· == p) then
                    g := { g with waitingTriggers :=
                      g.waitingTriggers ++
                        o.waitingTriggersFor p .creatureCardsPutIntoYourGy }
                | none => pure ()
            g := { g with suppressCreatureCardsToGy := true }
      for pair in victims do
        let o := pair.1
        let reason := pair.2
        match g.findObject? o.id with
        | some o =>
          if o.isOnBattlefield && o.isCreature then
            g := g.moveToOwnerGraveyard o reason
            changed := true
        | none => pure ()
      g := { g with
        lockedDeathReplacements := none
        suppressOthersDie := false
        suppressCreatureCardsToGy := false }
      for o in g.battlefield do
        if o.isCreature && o.status.dealtDeathtouch && g.hasIndestructible o then
          g := g.setObject { o with status := { o.status with dealtDeathtouch := false } }
      -- Legend rule (CR 704.5j): pause so the controller chooses one to keep.
      match g.firstLegendRuleChoice? with
      | some (p, name, ids) =>
        g := { g with pending := .chooseLegend p name ids }
        g := g.logMsg
          s!"{(g.player p).name} chooses which {name} to keep (legend rule, CR 704.5j)"
        return (g, true)
      | none => pure ()
      -- Tokens in zones other than the battlefield cease to exist (CR 704.5d).
      for o in g.objects do
        if o.printed.isToken && o.zone != .battlefield then
          g := g.ceaseToExist o.id
          g := g.logMsg s!"{o.name} ceases to exist (token left the battlefield)"
          changed := true
      -- Saga with lore at or past its final chapter and no chapter on the
      -- stack is sacrificed (CR 714.4 / 704.5s).
      for o in g.battlefield do
        match o.printed.saga, o.controller with
        | some sdef, some _ =>
          if o.status.lore ≥ sdef.finalChapterNumber && sdef.finalChapterNumber > 0 &&
              !g.sagaChapterPending o.id then
            g := g.moveToOwnerGraveyard o
              s!"{o.name} is sacrificed (CR 714.4)"
            changed := true
        | _, _ => pure ()
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
  let g := (g.checkSBACounted).1
  if g.over then g
  else
    let g := g.leavePlayersWhoLost
    if g.over then g
    else (g.checkSBACounted).1

/-- Triggered abilities waiting to be put onto the stack (CR 603.3 / 603.3b,
514.3a). All triggered abilities wait until a player would receive priority. -/
def hasWaitingTriggers (g : Game) : Bool :=
  !g.waitingTriggers.isEmpty

/-- CR 100.1b: a multiplayer game begins with more than two players. -/
def isMultiplayer (g : Game) : Bool :=
  g.players.size > 2

/-- CR 103.8a: in a two-player game the starting player skips the draw step
of their first turn. Multiplayer games do not skip that draw (CR 103.8c). -/
def skipsFirstDraw (g : Game) : Bool :=
  g.isFirstTurn && !g.isMultiplayer && g.activePlayer == g.startingPlayer

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

/-- Extra land plays from permanents such as Thranduil's Company. Each such
permanent is cumulative with other extra-land effects (rulings 288 / 306). -/
def extraLandsFromPermanents (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).foldl (fun acc o =>
    match o.printed.extraLandIfOtherSubtype with
    | none => acc
    | some t =>
      if (g.permanentsOf p).any (fun other =>
        other.id != o.id && g.hasSubtype other t) then
        acc + 1
      else acc) 0

/-- How many lands `p` may play this turn (CR 305.2 / 305.2b). -/
def landPlaysAllowed (g : Game) (p : PlayerId) : Nat :=
  1 + (g.player p).additionalLandsThisTurn + g.extraLandsFromPermanents p

/-- Lands remaining this turn (CR 305.2 / 305.3 / 116.2a). -/
def canPlayLand (g : Game) (p : PlayerId) : Bool :=
  g.asSorcery? p && (g.player p).landsPlayedThisTurn < g.landPlaysAllowed p

/-- Whether `p` may play `o` from exile under a granted permission (CR 701.14 / 715.3d). -/
def mayPlayFromExile (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  o.zone == .exile &&
  match o.playPermission with
  | some perm =>
    perm.player == p &&
      (perm.fromAdventure || perm.whileExiled || perm.turnEndsRemaining > 0) &&
      (match perm.requireSubtype with
       | none => true
       | some t => g.controlsAnySubtype p #[t])
  | none => false

/-- Cards in exile that `p` currently may play. -/
def exiledPlayable (g : Game) (p : PlayerId) : Array GameObject :=
  g.objects.filter (fun o => g.mayPlayFromExile p o)

/-- Mole Man lets you play land cards from your graveyard (MSH 253 / 254).
Cycling and other activated abilities of those cards are still illegal. -/
def controlsPlayLandsFromGraveyard (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun x =>
    x.staticAbilities.any (fun
      | .msh .youMayPlayLandsFromYourGraveyard => true
      | _ => false))

def mayPlayFromGraveyard (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  o.zone == .graveyard p && o.owner == p &&
    (o.printed.flashback.isSome ||
      (o.printed.isLand && g.controlsPlayLandsFromGraveyard p))

/-- True when `p` controls a permanent that lets them look at the library top. -/
def controlsLookAtTop (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o => o.printed.mayLookAtTopAnytime)

/-- True when `p` may look at the top card of their library right now.
Elven Chorus does not reveal a new top while a spell from that top is
still being cast. -/
def canLookAtLibraryTop (g : Game) (p : PlayerId) : Bool :=
  g.controlsLookAtTop p && !g.castingFromTop

/-- True when `p` controls a permanent that lets them cast creatures from
the top of their library. Does not grant flash or change timing. -/
def controlsCastCreaturesFromTop (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o => o.printed.mayCastCreaturesFromTop)

/-- The top card of `p`'s library, if any. -/
def libraryTop? (g : Game) (p : PlayerId) : Option GameObject :=
  (g.player p).library.back?.bind g.findObject?

/-- True when `o` is the top card of `p`'s library and they may cast it as
a creature spell from there. Timing is still checked by `canCast`. -/
def controlsPlayLandsFromTop (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o => o.printed.mayPlayLandsFromTop)

def mayPlayFromLibraryTop (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  o.zone == .library p &&
    (g.player p).library.back? == some o.id &&
    ((o.printed.isCreature && g.controlsCastCreaturesFromTop p) ||
      (o.printed.isLand && g.controlsPlayLandsFromTop p))

def mayPlay (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  (g.player p).hand.contains o.id || g.mayPlayFromExile p o ||
    g.mayPlayFromGraveyard p o || g.mayPlayFromLibraryTop p o

def playZoneError (g : Game) (p : PlayerId) (o : GameObject) : String :=
  if o.zone == .exile && !g.mayPlayFromExile p o then
    "You may not play that card from exile"
  else if o.zone == .graveyard p && !g.mayPlayFromGraveyard p o then
    "You may not play that card from your graveyard"
  else if o.zone == .library p && !g.mayPlayFromLibraryTop p o then
    "You may not play that card from the top of your library"
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

/-- Whether this target is a spell on the stack that `p` controls. -/
def isOwnStackSpellTarget (g : Game) (p : PlayerId) : Target → Bool
  | .card oid =>
    (g.findObject? oid).any (fun o => o.zone == .stack && o.controlledBy p)
  | _ => false

/-- Whether this target is a spell on the stack an opponent of `p` controls. -/
def isOppStackSpellTarget (g : Game) (p : PlayerId) : Target → Bool
  | .card oid =>
    (g.findObject? oid).any (fun o =>
      o.zone == .stack && (g.livingOpponents p).any (fun pl => o.controlledBy pl.id))
  | _ => false

/-- Opponent-controlled spells currently on the stack. -/
def oppStackSpells (g : Game) (p : PlayerId) : Array GameObject :=
  g.stackSpells (fun o => (g.livingOpponents p).any (fun pl => o.controlledBy pl.id))

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
      o.controlledBy g.defendingPlayer)
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
  | .oppArtifact =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && o.printed.isArtifact &&
        (g.livingOpponents caster).any (fun pl => o.controlledBy pl.id))
  | .creatureCardInYourGraveyardMvAtMost n =>
    g.legalGraveyardCardTargets caster (fun o =>
      o.printed.isCreature && o.printed.manaValue ≤ n)
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
  | .twoPlayers => #[]
  | .upToOneCreatureThenPlayer => #[]
  | .attackingOrBlockingCreature =>
    g.legalCreatureTargets caster (fun o =>
      o.status.attacking || !o.status.blocking.isEmpty)
  | .creatureMvAtMost n =>
    g.legalCreatureTargets caster (fun o => o.printed.manaValue ≤ n)
  | .creatureToughnessAtLeast n =>
    g.legalCreatureTargets caster (fun o => g.toughness o >= n)
  | .enchantmentMvAtLeast n =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && o.printed.isEnchantment && o.printed.manaValue ≥ n)
  | .noncreatureArtifact =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && o.printed.isArtifact && !o.isCreature)

/-- Legal targets for a targeting shape (CR 115.1 / 601.2c / 603.3d).
`sourceId` excludes the source of an “another” creature. Shapes with
multiple instances of the word “target” read `spec.slots` instead of
restating each slot. -/
def legalTargetsForKind (g : Game) (caster : PlayerId) (kind : EffectTargetKind)
    (sourceId : Option ObjectId := none) : Array Target :=
  if kind.spec.slots.isEmpty then
    g.legalTargetsForAtomicKind caster kind sourceId
  else
    Id.run do
      let mut acc : Array Target := #[]
      let mut requiredMissing := false
      for i in [0:kind.spec.slots.size] do
        let part := g.legalTargetsForAtomicKind caster kind.spec.slots[i]! sourceId
        if part.isEmpty && !kind.isOptionalSlot i then
          requiredMissing := true
        acc := acc ++ part
      if requiredMissing then #[] else acc

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
  if (g.player controller).lost then g
  else
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
    (cause : Option GameObject := none) (source : Option GameObject := none) : Bool :=
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
  let lifeOk :=
    match ab.timing.gainedLifeAtLeast with
    | none => true
    | some n => (g.player controller).lifeGainedThisTurn ≥ n
  let hulklingOk :=
    match ab, cause, source with
    | .msh .wheneverAnotherCreatureYouControlEnters, some entered, some hulkling =>
      g.power entered > g.power hulkling || g.toughness entered > g.toughness hulkling
    | .msh .wheneverAnotherCreatureYouControlEnters, _, _ => false
    | _, _, _ => true
  powerOk && otherOk && lifeOk && hulklingOk

/-- Put `ab` on the stack for `event`, using that event's spec for the log label
and CR 603.3d check so a new event is not restated at every queue site. -/
def putQueuedTrigger (g : Game) (controller : PlayerId) (source : GameObject)
    (ab : TriggeredAbility) (event : TriggerEvent)
    (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none)
    (cause : Option GameObject := none) : Game :=
  if (g.player controller).lost then g
  else if !g.triggerConditionHolds controller ab cause (some source) then g
  else if event.checkTargets then
    g.putTriggerOrFizzle controller source ab event.label lastKnownPower lastKnownToughness
  else
    g.putTriggeredAbilityOnStack controller source ab event.label
      lastKnownPower lastKnownToughness

/-- Append waiting-trigger snapshots. -/
def enqueueWaitingTriggers (g : Game) (wts : Array WaitingTrigger) : Game :=
  if wts.isEmpty then g else { g with waitingTriggers := g.waitingTriggers ++ wts }

/-- Extra times a trigger of `source` fires from Bifur / Chief / Wizard's Staff
statics. Each such ability adds one additional instance; they stack. -/
def extraTriggerCopies (g : Game) (controller : PlayerId) (source : GameObject) : Nat :=
  let story := (g.player controller).enduringStory
  (g.permanentsOf controller).foldl (fun acc o =>
    o.staticAbilities.foldl (fun acc ab =>
      match ab with
      | .extraTriggerIfEnduringStorySubtype subtype =>
        if story && g.hasSubtype source subtype then acc + 1 else acc
      | .extraTriggerAnotherYouControl subtypes includeBattles =>
        if o.id == source.id then acc
        else
          let matchSubtype := subtypes.any (fun s => g.hasSubtype source s)
          let matchBattle := includeBattles && source.printed.isBattle
          if matchSubtype || matchBattle then acc + 1 else acc
      | .equippedTriggersAgain =>
        if o.attachedTo == some source.id then acc + 1 else acc
      | _ => acc) acc) 0

/-- Queue `ab` until a player would receive priority (CR 603.3 / 603.4). The
intervening condition is checked when the event occurs. -/
def queueTrigger (g : Game) (controller : PlayerId) (source : GameObject)
    (ab : TriggeredAbility) (event : TriggerEvent)
    (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none)
    (cause : Option GameObject := none) : Game :=
  if (g.player controller).lost then g
  else if !g.triggerConditionHolds controller ab cause (some source) then g
  else if ab.onceEachTurn && source.status.firedOnceEachTurn then g
  else
    let g :=
      if ab.onceEachTurn then
        match g.findObject? source.id with
        | some o => g.setObject { o with status := { o.status with firedOnceEachTurn := true } }
        | none => g
      else g
    let copies := g.extraTriggerCopies controller source + 1
    let wt : WaitingTrigger := {
      controller, source, ability := ab, event, lastKnownPower, lastKnownToughness }
    Id.run do
      let mut g := g
      for _ in [0:copies] do
        g := g.enqueueWaitingTriggers #[wt]
      return g

/-- Put one lore counter on `saga` and queue the matching chapter abilities
(CR 714.2 / 714.3). Counters are added one at a time. -/
def addOneLoreCounter (g : Game) (saga : GameObject) : Game :=
  match saga.controller, saga.printed.saga with
  | some p, some sdef =>
    match g.findObject? saga.id with
    | none => g
    | some saga =>
      if !saga.isOnBattlefield then g
      else
        let lore := saga.status.lore + 1
        let g := g.setObject { saga with status := { saga.status with lore } }
        let g := g.logMsg s!"{saga.name} gets a lore counter ({lore})"
        let saga := g.object! saga.id
        (sdef.chaptersForLore lore).foldl (fun g ch =>
          match ch.chapterEffect with
          | none => g
          | some ce =>
            g.queueTrigger p saga (.sagaChapter lore ce) .sagaChapter) g
  | _, _ => g

/-- Add `n` lore counters one at a time (CR 714.3c). -/
def addLoreCounters (g : Game) (saga : GameObject) (n : Nat) : Game :=
  Id.run do
    let mut g := g
    for _ in [0:n] do
      match g.findObject? saga.id with
      | some o => g := g.addOneLoreCounter o
      | none => pure ()
    return g

/-- As a Saga enters, put a lore counter on it (CR 714.2a). -/
def addLoreAsSagaEnters (g : Game) (o : GameObject) : Game :=
  if o.printed.saga.isSome then g.addOneLoreCounter o else g

/-- After the draw step / as first main begins, add a lore counter to each
Saga the active player controls (CR 714.2b). -/
def addLoreAfterDrawStep (g : Game) : Game :=
  (g.permanentsOf g.activePlayer).foldl (fun acc o =>
    if o.printed.saga.isSome then acc.addOneLoreCounter o else acc) g

/-- Queue each printed trigger of `source` that fires on `event` (CR 603.3). -/
def putMatchingSourceTriggers (g : Game) (controller : PlayerId) (source : GameObject)
    (event : TriggerEvent)
    (lastKnownPower : Option Int := none) (lastKnownToughness : Option Int := none)
    (cause : Option GameObject := none) : Game :=
  Id.run do
    let mut g := g
    for ab in source.matchingTriggers event do
      let skipInfinity :=
        match ab with
        | .msh .atTheBeginningOf => !source.status.harnessed
        | _ => false
      if !skipInfinity then
        g := g.queueTrigger controller source ab event lastKnownPower lastKnownToughness
          cause
    return g

/-- Apply `f` to each battlefield permanent matching `pred`. -/
def foldBattlefield (g : Game) (pred : GameObject → Bool)
    (f : Game → GameObject → Game) : Game :=
  Id.run do
    let mut g := g
    for o in g.battlefield do
      if pred o then
        g := f g o
    return g

/-- Apply `f` to each battlefield permanent `p` controls, optionally skipping one id. -/
def foldControlledPermanents (g : Game) (p : PlayerId)
    (excludeId : Option ObjectId := none) (f : Game → GameObject → Game) : Game :=
  g.foldBattlefield (fun o => o.controlledBy p && excludeId != some o.id) f

/-- Apply `f` to each creature `p` controls, optionally skipping one id. -/
def forEachControlledCreature (g : Game) (p : PlayerId)
    (f : Game → GameObject → Game) (excludeId : Option ObjectId := none) : Game :=
  g.foldControlledPermanents p excludeId fun g o =>
    if o.isCreature then f g o else g

/-- Put matching triggers of permanents `p` controls that fire on `event`. -/
def putControlledTriggers (g : Game) (p : PlayerId)
    (event : TriggerEvent) (excludeId : Option ObjectId := none) : Game :=
  g.foldControlledPermanents p excludeId fun g o =>
    g.putMatchingSourceTriggers p o event

/-- Queue “whenever you sacrifice a token” if `o` was a token when sacrificed. -/
def queueYouSacrificeToken (g : Game) (o : GameObject) : Game :=
  if !o.printed.isToken then g
  else
    match o.controller with
    | some p => g.putControlledTriggers p .youSacrificeToken
    | none => g.putControlledTriggers o.owner .youSacrificeToken

/-- Sacrifice `o` to its owner's graveyard and fire token-sacrifice triggers. -/
def sacrificeToGraveyard (g : Game) (o : GameObject) (reason : String) : Game :=
  let g := g.moveToOwnerGraveyard o reason
  g.queueYouSacrificeToken o

/-- Cards of `subtype` in `p`'s graveyard (Thranduil-style copies). -/
def graveyardCardsOfSubtype (g : Game) (p : PlayerId) (subtype : String) :
    Array GameObject :=
  (g.player p).graveyard.filterMap (fun id =>
    match g.findObject? id with
    | some card =>
      if card.printed.hasSubtype subtype then some card else none
    | none => none)

/-- Collect `sel` from graveyard cards named by `copyActivatedFromGySubtype`. -/
def copiedFromGy {α : Type} (g : Game) (o : GameObject) (sel : CardDef → Array α) :
    Array α :=
  if !o.isOnBattlefield then #[]
  else
    match o.controller with
    | none => #[]
    | some p =>
      o.staticAbilities.foldl (fun acc sa =>
        match sa with
        | .copyActivatedFromGySubtype subtype =>
          (g.graveyardCardsOfSubtype p subtype).foldl
            (fun acc card => acc ++ sel card.printed) acc
        | _ => acc) #[]

/-- Printed activated abilities plus those copied from the graveyard. -/
def activatedAbilitiesOf (g : Game) (o : GameObject) : Array ActivatedAbility :=
  o.printed.activatedAbilities ++ g.copiedFromGy o (·.activatedAbilities)

/-- Printed mana abilities plus those copied from the graveyard. -/
def manaAbilitiesOf (g : Game) (o : GameObject) : Array ManaType :=
  o.printed.manaAbilities ++ g.copiedFromGy o (·.manaAbilities)

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
  let p := g.priorityInstead p
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
      let g := g.putControlledTriggersWithPrompt landController .landYouControlEnters
      let g :=
        if g.hasSubtype land "Mountain" then
          g.putControlledTriggers landController .mountainYouControlEnters
        else g
      (g.player landController).graveyard.foldl (fun acc id =>
        match acc.findObject? id with
        | none => acc
        | some o =>
          acc.putMatchingSourceTriggers landController o .landYouControlEnters) g

/-- Put “whenever you cast an instant or sorcery” triggers onto the stack
(CR 601.2i / 603.3). -/
def putCastTriggersOnStack (g : Game) (caster : PlayerId) (spell : GameObject) : Game :=
  let pl := g.player caster
  let spells := pl.spellsCastThisTurn + 1
  let nonc :=
    if spell.printed.isCreature then pl.noncreatureSpellsCastThisTurn
    else pl.noncreatureSpellsCastThisTurn + 1
  let creat :=
    if spell.printed.isCreature then pl.creatureSpellsCastThisTurn + 1
    else pl.creatureSpellsCastThisTurn
  let g := g.modifyPlayer caster (fun p =>
    { p with
      spellsCastThisTurn := spells
      noncreatureSpellsCastThisTurn := nonc
      creatureSpellsCastThisTurn := creat
      castManaValuesThisTurn :=
        p.castManaValuesThisTurn.push (g.objectManaValue spell) })
  let g :=
    Id.run do
      let mut g := g
      for _ in [0:spell.printed.cascade] do
        g := g.putTriggeredAbilityOnStack caster spell .onCastCascade "cascade trigger"
      return g
  let g :=
    if spell.printed.isInstantOrSorcery then
      g.putControlledTriggers caster .youCastInstantOrSorcery
    else g
  let g :=
    if spell.printed.isCreature then
      g.foldControlledPermanents caster none fun g o =>
        g.putMatchingSourceTriggers caster o .youCastCreature
          (some (Int.ofNat (g.objectManaValue spell)))
    else g.putControlledTriggers caster .youCastNoncreature
  let g :=
    (g.livingOpponents caster).foldl (fun acc pl =>
      acc.putControlledTriggers pl.id .opponentCastsSpell) g
  let g :=
    if spells == 2 then
      g.putControlledTriggers caster .youCastSecondSpell
    else g
  let colors := spell.printed.colors
  let g :=
    Color.all.foldl (fun acc c =>
      if colors.contains c then
        acc.putControlledTriggers caster (.youCastColor c)
      else acc) g
  let mv := g.objectManaValue spell
  let g :=
    (g.livingOpponents caster).foldl (fun acc pl =>
      acc.foldControlledPermanents pl.id none fun acc o =>
        match o.status.chosenOdd with
        | none => acc
        | some odd =>
          let parityOk := if odd then mv % 2 == 1 else mv % 2 == 0
          if parityOk then
            acc.putMatchingSourceTriggers pl.id o .opponentCastsMatchingParity
          else acc) g
  let g :=
    if spells == 2 then
      g.livingPlayers.foldl (fun acc pl =>
        acc.putControlledTriggers pl.id .anyPlayerCastsSecondSpell) g
    else g
  let g :=
    g.putControlledTriggers caster .youCastSpell
  let extortN :=
    (g.permanentsOf caster).filter (fun o =>
      o.staticAbilities.any (fun
        | .msh .extort => true
        | _ => false)) |>.size
  let g :=
    if extortN == 0 then g
    else
      { g with
          pendingExtort := g.pendingExtort + extortN
          pendingExtortController := some caster }
        |>.logMsg "Extort triggers"
  let g :=
    match g.pendingFreeRGCreature with
    | some p =>
      if p == caster && spell.printed.isCreature &&
          (spell.printed.colors.contains .red ||
            spell.printed.colors.contains .green) then
        { g with pendingFreeRGCreature := none }
          |>.logMsg s!"World War Hulk's free-cast permission is used on {spell.name}"
      else g
    | none => g
  let g :=
    if spell.printed.hasSubtype "Villain" then
      g.putControlledTriggers caster .youCastVillain
    else g
  let targetsCreatureYouControl : Bool :=
    match g.stack.find? (fun e => e.objectId == spell.id) with
    | some e =>
      e.targets.any (fun t =>
        match t with
        | Target.permanent id =>
          match g.findObject? id with
          | some o => o.isCreature && o.controlledBy caster
          | none => false
        | _ => false)
    | none => false
  let g :=
    if targetsCreatureYouControl then
      g.putControlledTriggers caster .youCastTargetingCreatureYouControl
    else g
  let g :=
    if !spell.printed.isCreature && nonc == 1 then
      (g.livingOpponents caster).foldl (fun acc pl =>
        acc.putControlledTriggers pl.id .opponentCastsFirstNoncreature) g
    else g
  -- Loki (MSH 109): copy the next instant or sorcery whose mana value is
  -- ≤ Loki's power at cast time (last known if he already left).
  let pw? :=
    match g.pendingLokiCopy with
    | none => none
    | some (p, some id, fallback) =>
      if p != caster then none
      else
        match g.findObject? id with
        | some o =>
          if o.isOnBattlefield then some (g.power o) else some fallback
        | none => some fallback
    | some (p, none, fallback) =>
      if p == caster then some fallback else none
  match pw? with
  | some pw =>
    if spell.printed.isInstantOrSorcery && Int.ofNat mv <= pw then
      let (g, copy) := g.allocObject spell.printed caster .stack (some caster)
      let g := g.setObject { copy with
        chosenX := spell.chosenX
        isCopy := true }
      let g := g.putStackEntry caster copy.id
      { g with pendingLokiCopy := none }
        |>.logMsg s!"A copy of {spell.name} is created (Loki)"
    else g
  | none => g

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

/-- Extra counters Doc Samson puts on a permanent you control (MSH 165 / 238). -/
def extraCountersOn (g : Game) (controller : Option PlayerId) (n : Nat) : Nat :=
  if n == 0 then 0
  else
    match controller with
    | none => n
    | some p =>
      n + ((g.permanentsOf p).filter (fun o =>
        o.printed.staticAbilities.any (fun
          | .msh .ifYouWouldPutOneOrMoreCountersOnAPerma => true
          | _ => false))).size

/-- After a permanent enters, put its enters triggers and “another … enters”
triggers (CR 603.6a). -/
def afterPermanentEnters (g : Game) (o : GameObject) : Game :=
  -- Storied is granted as the permanent enters, before SBA (legend rule /
  -- 0 toughness) and before enters triggers use the stack.
  let g := g.refreshEnduringStory
  let g := g.refreshCitysBlessing
  let g :=
    if o.printed.entersWithIndestructibleCounter then
      let g := g.setObject { o with status :=
        { o.status with indestructibleCounters := o.status.indestructibleCounters + 1 } }
      g.logMsg s!"{o.name} enters with an indestructible counter"
    else g
  let o := g.object! o.id
  let g :=
    if o.printed.entersWithShield > 0 then
      let n := g.extraCountersOn (o.controller) o.printed.entersWithShield
      let g := g.setObject { o with status :=
        { o.status with shield := o.status.shield + n } }
      g.logMsg s!"{o.name} enters with {n} shield counter(s)"
    else g
  let o := g.object! o.id
  let g := g.setObject { o with status := { o.status with enteredThisTurn := true } }
  let o := g.object! o.id
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
  let g := g.addLoreAsSagaEnters o
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
    let entered := g.object! o.id
    let g :=
      if entered.printed.isToken then
        g.putControlledTriggers p .tokenYouControlEnters
      else g
    let g :=
      if entered.printed.isArtifact then
        let g := g.modifyPlayer p (fun pl =>
          { pl with artifactEnteredThisTurn := true })
        g.putControlledTriggersWithPrompt p .artifactYouControlEnters
      else g
    let g :=
      if entered.isCreature then
        g.putControlledTriggers p .creatureYouControlEnters
      else g
    let g :=
      entered.subtypes.foldl (fun acc sub =>
        acc.putControlledTriggers p (.subtypeYouControlEnters sub)) g
    let g :=
      if entered.isCreature && g.hasSubtype entered "Hero" then
        g.modifyPlayer p (fun pl => { pl with heroEnteredThisTurn := true })
      else g
    let g :=
      if entered.printed.isEquipment then
        g.putControlledTriggers p .equipmentYouControlEnters
      else g
    let g :=
      if g.hasSubtype entered "Villain" || entered.printed.isArtifact then
        g.putControlledTriggers p .anotherVillainOrArtifactEnters
          (excludeId := some entered.id)
      else g
    let g :=
      if g.hasSubtype entered "Villain" then
        g.putControlledTriggers p .anotherVillainEnters (excludeId := some entered.id)
      else g
    let g :=
      if entered.printed.isArtifact then
        g.putControlledTriggers p .anotherArtifactEnters
      else g
    let g :=
      if !entered.printed.isToken && g.hasSubtype entered "Hero" then
        g.putControlledTriggers p .anotherNontokenHeroEnters
      else g
    let g :=
      if !entered.printed.isToken && entered.printed.isArtifact then
        g.putControlledTriggers p .anotherNontokenArtifactEnters
      else g
    g
  | none => g

/-- After a land enters, put its enters triggers, Elf-enters triggers, and landfall. -/
def afterLandEnters (g : Game) (land : GameObject) : Game :=
  let g := g.afterPermanentEnters land
  g.putLandYouControlEntersTriggers (g.object! land.id)

/-- Nick Fury power-up: put a Hero, Equipment, or Vehicle onto the battlefield.
A daybound front face enters back-face-up at night and cannot transform
(MSH 191). Otherwise it enters front-face-up; you may then transform a DFC
(MSH 192). Front-face enters abilities trigger in either case before the
optional transform. -/
def enterFromNickFury (g : Game) (controller : PlayerId) (id : ObjectId) : Game :=
  match g.findObject? id with
  | none => g.logMsg "No card to put onto the battlefield"
  | some o =>
    let nightBack := g.isNight && o.printed.daybound && o.printed.otherFace.isSome
    let (g, newId) := g.putOntoBattlefield id controller
    let o := g.object! newId
    let g :=
      if nightBack then
        match o.printed.otherFace with
        | some back =>
          let shown := { back with otherFace := some { o.printed with otherFace := none } }
          let g := g.setObject { o with
            printed := shown
            status := { o.status with transformed := true, cantTransform := true } }
          g.logMsg s!"{shown.name} enters back face up (night / daybound)"
        | none => g
      else g
    g.afterPermanentEnters (g.object! newId)

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
    let types := g.manaAbilitiesOf o
    if types.isEmpty || o.status.tapped then none
    else if o.hasSummoningSickness then none
    else some (o, types))

/-- Permanents `p` currently controls with this subtype. -/
def countSubtype (g : Game) (p : PlayerId) (subtype : String) : Nat :=
  (g.permanentsOf p).filter (fun o => g.hasSubtype o subtype) |>.size

/-- Colors among legendary creatures and planeswalkers `p` controls (Mox Amber).
Colorless is not a color; a colorless legend contributes nothing. -/
def legendaryManaColors (g : Game) (p : PlayerId) : ColorSet :=
  (g.permanentsOf p).foldl (fun acc o =>
    if o.isLegendary && (o.isCreature || o.printed.isPlaneswalker) then
      ColorSet.union acc o.printed.colors
    else acc) ColorSet.empty

/-- Mana added by tapping `o` for `mana` (CR 106.4 / 605.3b). A
`tapAddManaForEach` ability counts permanents the controller currently
controls with the listed subtype. `tapAddAnyColorEqualToPower` adds this
creature's current power (CR 208.2). Mox Amber and Arcane Signet may
produce 0 when no matching color is available. -/
def manaFromTap (g : Game) (o : GameObject) (mana : ManaType) : Nat :=
  if o.printed.tapAddAnyColorEqualToPower then
    match mana with
    | .colored _ => (g.power o).toNat
    | .colorless => 0
  else if o.printed.tapAddAnyColorAmongLegendaries then
    match mana, o.controller with
    | .colored c, some p => if (g.legendaryManaColors p).contains c then 1 else 0
    | _, _ => 0
  else if o.printed.tapAddCommanderIdentity then
    match mana, o.controller with
    | .colored c, some p =>
      let pl := g.player p
      if pl.hasCommander && pl.commanderColorIdentity.contains c then 1 else 0
    | _, _ => 0
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
  if !(g.manaAbilitiesOf o).contains mana then
    throw s!"{o.name} cannot produce {mana}"
  let amount := g.manaFromTap o mana
  let elfRestricted := o.printed.tapAddAnyColorEqualToPower
  let instRestricted := o.printed.tapAddAnyColorForInstantOrSorcery
  let cantNonartifact := o.printed.hasSubtype "Vibranium" && mana == .colorless
  let g := g.setObject { o with status := { o.status with tapped := true } }
  let g :=
    if o.printed.tapSacrificeAddAnyColor then
      let o := g.object! o.id
      g.sacrificeToGraveyard o s!"{(g.player p).name} sacrifices {o.name}"
    else g
  let pool :=
    ManaPool.add (g.player p).manaPool mana amount
      (elfRestricted := elfRestricted)
      (instRestricted := instRestricted)
      (cantNonartifact := cantNonartifact)
  let g := g.modifyPlayer p (fun pl => { pl with manaPool := pool })
  let produced :=
    if amount == 0 then "no mana"
    else if amount == 1 then toString mana
    else s!"{mana} ×{amount}"
  let restrictNote :=
    if elfRestricted then " (Elf spells and abilities)"
    else if instRestricted then " (instant or sorcery spells)"
    else if cantNonartifact then " (not a nonartifact spell)"
    else ""
  let g :=
    if amount == 0 then
      g.logMsg s!"{g.player p |>.name} taps {o.name} but adds no mana"
    else
      g.logMsg s!"{g.player p |>.name} taps {o.name} for {produced}{restrictNote}"
  let g :=
    match g.proposedSpell with
    | some prop => { g with proposedSpell := some { prop with tapped := prop.tapped.push id } }
    | none => g
  -- Mana abilities don't use the stack (CR 605.3b), but they still activate
  -- and can cause Elrond-style triggers.
  let g :=
    if o.isCreature then
      g.putControlledTriggers p .youActivateCreatureAbility
    else g
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

/-- True when this mode can be announced: it needs no target, or a legal one
exists (CR 700.2d). -/
def spellModeIsChoosable (g : Game) (p : PlayerId) (e : SpellEffect) : Bool :=
  !e.requiresTarget || !(g.legalTargets p e).isEmpty

/-- Legal mode indices for a modal spell (CR 700.2d). Untargeted modes stay
choosable even when another mode has no legal target. -/
def legalModes (g : Game) (p : PlayerId) (o : GameObject) : Array Nat :=
  if !o.printed.isModal then #[]
  else
    Id.run do
      let mut acc : Array Nat := #[]
      for i in [0:o.printed.spellModes.size] do
        if g.spellModeIsChoosable p o.printed.spellModes[i]! then
          acc := acc.push i
      return acc

/-- True when `e` targets a stack spell an opponent of `p` controls. -/
def effectHasOppSpellTarget (g : Game) (p : PlayerId) (e : SpellEffect) : Bool :=
  e.targetKind.targetsStackSpell &&
    (g.legalTargetsForKind p e.targetKind).any (g.isOppStackSpellTarget p)

/-- Default mode: a preferred mode if that mode is legal, else the first legal
mode. Spell-counter modes are skipped unless an opponent's spell is a legal
target, so the demonstration agent does not counter its own spells. -/
def defaultMode (g : Game) (p : PlayerId) (spell : GameObject) : Option Nat :=
  let legal := g.legalModes p spell
  let avoidOwnCounter (i : Nat) : Bool :=
    match spell.printed.spellModes[i]? with
    | some e => e.targetKind.targetsStackSpell && !g.effectHasOppSpellTarget p e
    | none => false
  let usable := legal.filter (fun i => !avoidOwnCounter i)
  let pool := if usable.isEmpty then legal else usable
  let preferredIdx := pool.find? (fun i =>
    match spell.printed.spellModes[i]? with
    | some e => e.preferAsDefaultMode
    | none => false)
  match preferredIdx with
  | some i => some i
  | none => pool[0]?

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

/-- Current instance of the word “target” being announced (0-based).
Skipped optional slots count toward this index so the next instance is
the next “target” word in the card text (CR 601.2c). -/
def currentTargetSlot (g : Game) (obj : GameObject) : Nat :=
  match g.stackEntry? obj.id with
  | some e => e.targets.size + e.skippedOptionalSlots
  | none => 0

/-- Skip the current optional “up to one” instance without announcing a
target (CR 115.1c / 601.2c). -/
def skipOptionalTargetSlot (g : Game) (objectId : ObjectId) : Game :=
  match g.stack.findIdx? (fun e => e.objectId == objectId) with
  | none => g
  | some i =>
    { g with stack := g.stack.set! i { g.stack[i]! with
        skippedOptionalSlots := g.stack[i]!.skippedOptionalSlots + 1 } }

/-- True when the current instance of “target” is optional (“up to one”). -/
def canSkipCurrentOptionalSlot (g : Game) (obj : GameObject) : Bool :=
  let kind := (g.targetingOf obj).kind
  let i := g.currentTargetSlot obj
  !kind.spec.slots.isEmpty && i < kind.spec.slots.size && kind.isOptionalSlot i

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
  let slot := kind.slotKind (g.currentTargetSlot o)
  let legal := (g.legalTargetsForKind p slot o.sourceId).filter (fun t => !already.contains t)
  let legal :=
    match g.proposedSpell with
    | some prop =>
      if prop.spellId == o.id &&
          prop.kind == .activatedAbility &&
          (prop.activation.any (·.equipWorthy) ||
            prop.original.printed.hasEquipWorthy) then
        legal.filter (fun t =>
          match t with
          | Target.permanent id =>
            match g.findObject? id with
            | some c => c.printed.isWorthy
            | none => false
          | _ => false)
      else legal
    | none => legal
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
  if ab.equipWorthy then
    let worthy :=
      (g.legalTargetsForKind p .creatureYouControl).filter (fun t =>
        match t with
        | Target.permanent id =>
          match g.findObject? id with
          | some c => c.printed.isWorthy
          | none => false
        | _ => false)
    !worthy.isEmpty
  else
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
  let own := lastLegalTarget legal (fun t =>
    g.isOwnPermanentTarget p t || g.isOwnStackSpellTarget p t)
  let opp := lastLegalTarget legal (fun t =>
    g.isOppPermanentTarget p t || g.isOppStackSpellTarget p t)
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
an opposing artifact or land; counterspells prefer an opposing spell; Mirkwood Elk prefers an Elf
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

/-- Captain Mar-Vell: as though spells had flash while an opponent has
cast a spell this turn (MSH 105). The permanent need not have been on
the battlefield when that spell was cast. -/
def cosmicAwarenessFlash (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o =>
    o.staticAbilities.any (fun
      | .msh .cosmicAwarenessAsLongAsAnOpponentHasCa => true
      | _ => false)) &&
    (g.livingOpponents p).any (fun pl => pl.spellsCastThisTurn > 0)

/-- Timing check shared by beginning to cast a spell or an Adventure (CR 601.3). -/
def timingAllowsCast (g : Game) (p : PlayerId) (face : CardDef) : Bool :=
  let hasConditionalFlash :=
    match face.flashIfYouControlSubtype with
    | some t => g.controlsAnySubtype p #[t]
    | none => false
  let radagastFlash :=
    face.isCreature && (g.player p).creatureSpellsCastThisTurn == 0 &&
      (g.permanentsOf p).any (fun o => o.printed.firstCreatureHasFlash)
  g.hasPriority p &&
  (if face.hasSorcerySpeed && !hasConditionalFlash && !radagastFlash &&
      !g.cosmicAwarenessFlash p then
    g.asSorcery? p else true)

/-- Whether `p` may begin to cast `o` (CR 601.3). Having enough mana in the
pool is not required; mana abilities are activated at CR 601.2g. Additional
non-mana costs such as sacrificing a permanent must still be payable. -/
def canCast (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  !o.printed.isLand &&
  !(g.player p).cantCastSpellsThisTurn &&
  g.mayPlay p o &&
  (match o.playPermission with
   | some perm => perm.ignoreTiming || g.timingAllowsCast p o.printed
   | none => g.timingAllowsCast p o.printed) &&
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
    (match o.playPermission with
     | some perm => perm.ignoreTiming || g.timingAllowsCast p face
     | none => g.timingAllowsCast p face) &&
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

/-- Whether paying this proposed spell may spend legendary-restricted mana. -/
def proposedAllowsLegendaryRestricted (g : Game) (prop : ProposedSpell) : Bool :=
  match prop.kind with
  | .spell =>
    match g.findObject? prop.spellId with
    | some o => o.isLegendary
    | none => false
  | .activatedAbility => false

/-- Mana types `src` can produce that may be spent on `prop` (CR 106.10). -/
def usableManaTypesForProposed (g : Game) (src : GameObject) (types : Array ManaType)
    (prop : ProposedSpell) : Array ManaType :=
  let allowElf := g.proposedAllowsElfRestricted prop
  let allowInst := g.proposedAllowsInstRestricted prop
  let allowLeg := g.proposedAllowsLegendaryRestricted prop
  if src.printed.tapAddAnyColorEqualToPower && !allowElf then #[]
  else if src.printed.tapAddAnyColorForInstantOrSorcery && !allowInst then #[]
  else if src.printed.tapAddAnyColorForLegendary && !allowLeg then
    types.filter (fun t =>
      src.printed.simpleTapAddMana.contains t || src.printed.tapAddOneOf.contains t)
  else types

/-- Untapped mana sources `p` may activate while paying `prop` (CR 601.2g).
Sources reserved for `{T}`, or whose mana cannot be spent on this spell or
ability, are omitted. -/
def manaSourcesForProposed (g : Game) (p : PlayerId) (prop : ProposedSpell) :
    Array (GameObject × Array ManaType) :=
  (g.manaSources p).filterMap (fun (src, types) =>
    if prop.tapSource && prop.sourceId == some src.id then none
    else
      let usable := g.usableManaTypesForProposed src types prop
      if usable.isEmpty then none
      else some (src, usable))

/-- Whether tapping `src` for `t` covers more of `cost` than the current pool. -/
def typeHelpsPay (g : Game) (p : PlayerId) (src : GameObject) (t : ManaType)
    (cost : ManaCost) (allowElfRestricted : Bool) (allowInstRestricted : Bool) : Bool :=
  let amount := g.manaFromTap src t
  if amount == 0 then false
  else
    let pool := (g.player p).manaPool
    let before := pool.coveredMana cost allowElfRestricted allowInstRestricted
    let after :=
      pool.add t amount
        (elfRestricted := src.printed.tapAddAnyColorEqualToPower)
        (instRestricted := src.printed.tapAddAnyColorForInstantOrSorcery)
    after.coveredMana cost allowElfRestricted allowInstRestricted > before

/-- A mana type among `types` that helps pay remaining symbols of `cost`.
Prefers an unmet colored requirement, then colorless if it can be spent;
returns none when no type can be spent on the pending payment. -/
def preferredManaType (g : Game) (p : PlayerId) (src : GameObject)
    (types : Array ManaType) (cost : ManaCost) (allowElfRestricted : Bool)
    (allowInstRestricted : Bool := false) : Option ManaType :=
  let helpful := types.filter (fun t =>
    g.typeHelpsPay p src t cost allowElfRestricted allowInstRestricted)
  match helpful[0]? with
  | none => none
  | some first =>
    let pool := (g.player p).manaPool
    match Color.all.find? (fun c =>
      let req := cost.coloredCount c
      let held := pool.usable (.colored c) allowElfRestricted allowInstRestricted
      held < req && helpful.contains (.colored c)) with
    | some c => some (.colored c)
    | none =>
      if helpful.contains .colorless then some .colorless
      else some first

/-- Whether `(src, t)` is a better next tap than `(bestSrc, bestT)`: avoid
creatures when another source helps, then prefer colorless. Equal ranks keep
the earlier source. -/
def betterManaTap (src : GameObject) (t : ManaType)
    (bestSrc : GameObject) (bestT : ManaType) : Bool :=
  (!src.isCreature && bestSrc.isCreature) ||
    (src.isCreature == bestSrc.isCreature && t == .colorless && bestT != .colorless)

/-- Next source to tap for `prop`. Noncreatures are chosen before creatures
when both help, and colorless is preferred when that type can be spent. -/
def preferredManaTap (g : Game) (p : PlayerId) (prop : ProposedSpell) :
    Option (GameObject × ManaType) :=
  let allowElf := g.proposedAllowsElfRestricted prop
  let allowInst := g.proposedAllowsInstRestricted prop
  (g.manaSourcesForProposed p prop).foldl (fun acc (src, types) =>
    match g.preferredManaType p src types prop.cost allowElf allowInst with
    | none => acc
    | some t =>
      match acc with
      | none => some (src, t)
      | some (bestSrc, bestT) =>
        if betterManaTap src t bestSrc bestT then some (src, t) else acc) none

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
        proposedSpell := none
        castingFromTop := false }
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

/-- Queue “becomes the target” triggers once per unique targeted permanent
(CR 603.2 / 601.2c). A spell or ability that targets the same permanent
more than once still triggers only once. -/
def queueBecomesTargetTriggers (g : Game) (caster : PlayerId)
    (targets : Array Target) : Game :=
  Id.run do
    let mut g := g
    let mut seen : Array ObjectId := #[]
    for t in targets do
      match t with
      | Target.permanent oid =>
        if !seen.contains oid then
          seen := seen.push oid
          match g.findObject? oid with
          | some o =>
            if o.controller != some caster then
              match o.controller with
              | some c =>
                g := g.putMatchingSourceTriggers c o .becomesTarget
              | none => pure ()
          | none => pure ()
      | _ => pure ()
    return g

def becomeCast (g : Game) (p : PlayerId) (spell : GameObject) : Game :=
  let g := { g with castingFromTop := false }
  let g := g.logMsg s!"{(g.player p).name} casts {spell.name}"
  let g :=
    match g.stackEntry? spell.id with
    | some e =>
      let g := g.queueBecomesTargetTriggers p e.targets
      e.targets.foldl (fun (g : Game) (t : Target) =>
        match t with
        | Target.permanent oid =>
          match g.findObject? oid with
          | some o =>
            match o.controller with
            | some c => g.putMatchingSourceTriggers c o .spellTargetsSource
            | none => g
          | none => g
        | _ => g) g
    | none => g
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

/-- Choose new targets for a spell on the stack (Speedball; MSH 370).
Each slot that has no new legal target is left unchanged, even if the
current target is illegal. -/
def retargetStackSpell (g : Game) (spellId : ObjectId) (newTargets : Array Target) :
    Game :=
  match g.stack.findIdx? (fun e => e.objectId == spellId) with
  | none => g.logMsg "The spell is no longer on the stack"
  | some i =>
    let e := g.stack[i]!
    match g.findObject? spellId with
    | none => g.logMsg "The spell is no longer on the stack"
    | some spell =>
      let kind := (g.targetingOf spell).kind
      let legal := g.legalTargetsForKind e.controller kind (some spellId)
      let merged :=
        Id.run do
          let mut out := e.targets
          for j in [0:Nat.min out.size newTargets.size] do
            let neu := newTargets[j]!
            if legal.any (fun t => t == neu) then
              out := out.set! j neu
          return out
      { g with stack := g.stack.set! i { e with targets := merged } }
        |>.logMsg "New targets are chosen for the spell"

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
        let powerUp :=
          match g.proposedSpell.bind (·.activation) with
          | some ab => ab.powerUp
          | none =>
            src.printed.activatedAbilities.any (·.powerUp)
        let g := g.setObject { src with status := { src.status with
          activationsThisTurn := src.status.activationsThisTurn + 1
          powerUpUsed := src.status.powerUpUsed || powerUp
          powerUpActivations :=
            src.status.powerUpActivations + (if powerUp then 1 else 0) } }
        let src := g.object! sid
        if src.isCreature then
          g.putControlledTriggers p .youActivateCreatureAbility
        else g
      | none => g
  let g :=
    match g.stack.back? with
    | some e => g.queueBecomesTargetTriggers p e.targets
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

/-- Creatures `p` controls that are tied for least power. -/
def leastPowerCreatures (g : Game) (p : PlayerId) : Array GameObject :=
  let cs := g.sacrificeCreatureChoices p
  match cs[0]? with
  | none => #[]
  | some first =>
    let minP := cs.foldl (fun acc o => min acc (g.power o)) (g.power first)
    cs.filter (fun o => g.power o == minP)

/-- Sacrifice a least-power creature `p` controls. If several are tied and
`chosen` is none, the player still chooses (logged; no sacrifice yet). -/
def sacrificeLeastPowerCreature (g : Game) (p : PlayerId)
    (chosen : Option ObjectId := none) : Game :=
  let tied := g.leastPowerCreatures p
  if tied.isEmpty then
    g.logMsg s!"{(g.player p).name} controls no creatures to sacrifice"
  else
    let pick :=
      match chosen with
      | some id => tied.find? (fun o => o.id == id)
      | none => if tied.size == 1 then some tied[0]! else none
    match pick with
    | some o =>
      g.sacrificeToGraveyard o
        s!"{(g.player p).name} sacrifices {o.name} (least power)"
    | none =>
      g.logMsg
        s!"{(g.player p).name} chooses one of the creatures tied for least power to sacrifice"

/-- Unused Alliance modes on `src` (0 = add GGG, 1 = +1/+1 each, 2 = scry 2
then draw). -/
def unusedAllianceModes (_g : Game) (src : GameObject) : Array Nat :=
  #[0, 1, 2].filter (fun m => !src.status.allianceModesChosen.contains m)

/-- Apply one Alliance mode of `sourceId` if it has not been chosen this turn.
If every mode was already chosen, the ability is removed with no effect. -/
def applyAllianceMode (g : Game) (sourceId : ObjectId) (mode : Nat) : Game :=
  match g.findObject? sourceId with
  | none =>
    g.logMsg "The ability is removed from the stack with no effect"
  | some src =>
    if src.status.allianceModesChosen.size >= 3 ||
        (g.unusedAllianceModes src).isEmpty then
      g.logMsg
        "all three modes have been chosen this turn. The ability is removed from the stack with no effect"
    else if src.status.allianceModesChosen.contains mode then
      g.logMsg "That Alliance mode has already been chosen this turn"
    else
      let g := g.setObject { src with status :=
        { src.status with allianceModesChosen := src.status.allianceModesChosen.push mode } }
      match src.controller, mode with
      | some c, 0 =>
        let g := g.modifyPlayer c (fun pl =>
          { pl with manaPool :=
            pl.manaPool.add (.colored .green) 3 })
        g.logMsg ((g.player c).name ++ " adds {G}{G}{G}")
      | some c, 1 =>
        Id.run do
          let mut g := g
          for o in g.battlefield do
            if o.isCreature && o.controlledBy c then
              g := g.setObject { o with status := o.status.addPlusOnePlusOne 1 }
          return g.logMsg
            s!"{(g.player c).name} puts a +1/+1 counter on each creature they control"
      | some c, 2 =>
        (g.draw c 1).logMsg ((g.player c).name ++ " scries 2, then draws a card")
      | _, _ => g

/-- Unused Gollum modes on `src` (0 = +1/+1, 1 = drain, 2 = draw). Modes last
for the object's lifetime (ruling 164). -/
def unusedGollumModes (_g : Game) (src : GameObject) : Array Nat :=
  #[0, 1, 2].filter (fun m => !src.status.chosenModes.contains m)

/-- Apply one unused Gollum mode. If every mode was already chosen, the
ability is removed with no effect and Gollum remains. -/
def applyGollumMode (g : Game) (sourceId : ObjectId) (mode : Nat) : Game :=
  match g.findObject? sourceId with
  | none =>
    g.logMsg "The ability is removed from the stack with no effect"
  | some src =>
    if (g.unusedGollumModes src).isEmpty then
      g.logMsg
        "all three modes have been chosen. The ability is removed from the stack with no effect"
    else if src.status.chosenModes.contains mode then
      g.logMsg "That mode has already been chosen"
    else
      let g := g.setObject { src with status :=
        { src.status with chosenModes := src.status.chosenModes.push mode } }
      match src.controller, mode with
      | some _, 0 =>
        let src := g.object! sourceId
        let g := g.setObject { src with status := src.status.addPlusOnePlusOne 1 }
        g.logMsg s!"{src.name} gets a +1/+1 counter"
      | some c, 1 =>
        let g := g.forEachOpponent c (fun g pid =>
          let pl := g.player pid
          g.setLife pid (pl.life - 2)
            s!"{pl.name} loses 2 life ({pl.life - 2} life)")
        let pl := g.player c
        g.setLife c (pl.life + 2)
          s!"{pl.name} gains 2 life ({pl.life + 2} life)"
      | some c, 2 =>
        g.draw c 1
      | _, _ => g

/-- As Gollum enters, choose odd (`true`) or even (`false`). Zero is even. -/
def chooseGollumParity (g : Game) (sourceId : ObjectId) (odd : Bool) : Game :=
  match g.findObject? sourceId with
  | none => g
  | some src =>
    let g := g.setObject { src with status := { src.status with chosenOdd := some odd } }
    g.logMsg
      (if odd then s!"{src.name}: odd is chosen" else s!"{src.name}: even is chosen")

/-- Remove an indestructible counter as a cost (ruling 357). -/
def payRemoveIndestructibleCounter (g : Game) (o : GameObject) : Except String Game := do
  if o.status.indestructibleCounters == 0 then
    throw s!"{o.name} has no indestructible counter"
  let g := g.setObject { o with status :=
    { o.status with indestructibleCounters := o.status.indestructibleCounters - 1 } }
  return g.logMsg s!"{o.name} loses an indestructible counter"

/-- Resolve Arwen, Mortal Queen's activated ability. An illegal target means
no counters are put on Arwen or the target (ruling 189). -/
def resolveArwenShare (g : Game) (arwenId : ObjectId) (targetId : Option ObjectId) : Game :=
  match targetId.bind g.findObject? with
  | none =>
    g.logMsg "The target is no longer legal. The ability does nothing."
  | some o =>
    if !o.isOnBattlefield || !o.isCreature || o.id == arwenId then
      g.logMsg "The target is no longer legal. The ability does nothing."
    else
      let putCounters (g : Game) (oid : ObjectId) : Game :=
        match g.findObject? oid with
        | none => g
        | some x =>
          let g := g.setObject { x with status :=
            { x.status with
              plusOnePlusOne := x.status.plusOnePlusOne + 1
              lifelinkCounters := x.status.lifelinkCounters + 1 } }
          g.logMsg s!"{x.name} gets a +1/+1 counter and a lifelink counter"
      let g := g.setObject { o with status := o.status.grantUntilEot Keyword.indestructible }
      let g := g.logMsg s!"{o.name} gains indestructible until end of turn"
      let g := putCounters g o.id
      putCounters g arwenId

/-- Behold a quality: choose a matching permanent you control or reveal a
matching card from your hand. Later zone changes do not un-behold (117). -/
def beholdQuality (g : Game) (p : PlayerId) (quality : String) : Game :=
  let hasPerm := (g.permanentsOf p).any (fun o => g.hasSubtype o quality)
  let hasHand :=
    (g.player p).hand.any (fun id =>
      match g.findObject? id with
      | some o => o.printed.hasSubtype quality
      | none => false)
  if hasPerm || hasHand then
    let g := g.modifyPlayer p (fun pl =>
      { pl with beheldQualities := pl.beheldQualities.push quality })
    g.logMsg s!"{(g.player p).name} beholds a {quality}"
  else
    g.logMsg s!"{(g.player p).name} does not behold a {quality}"

/-- True when `p` has beheld `quality`, even if the card or permanent later left. -/
def qualityWasBeheld (g : Game) (p : PlayerId) (quality : String) : Bool :=
  (g.player p).beheldQualities.contains quality

/-- Choose a creature type as this permanent enters. The static pump applies
immediately; no player may act between the choice and the bonus. -/
def chooseCreatureTypeAsEnters (g : Game) (sourceId : ObjectId) (creatureType : String) :
    Game :=
  match g.findObject? sourceId with
  | none => g
  | some src =>
    let g := g.setObject { src with status :=
      { src.status with chosenCreatureType := some creatureType } }
    g.logMsg s!"{src.name}: {creatureType} is chosen as it enters"

/-- Draw one card for each graveyard with seven or more cards. -/
def drawPerSevenCardGraveyard (g : Game) (p : PlayerId) : Game :=
  let n := g.players.filter (fun pl => pl.graveyard.size >= 7) |>.size
  if n == 0 then
    g.logMsg s!"{(g.player p).name} draws no cards (no graveyard has seven cards)"
  else
    g.draw p n

/-- Discard the hand (zero cards is legal) and draw that many. The choice is
made during resolution; nothing happens between discard and draw. -/
def mayDiscardHandDrawThatMany (g : Game) (p : PlayerId) (doDiscard : Bool) : Game :=
  if !doDiscard then
    g.logMsg s!"{(g.player p).name} does not discard their hand"
  else
    let ids := (g.player p).hand
    let n := ids.size
    let g :=
      ids.foldl (fun acc id =>
        match acc.findObject? id with
        | none => acc
        | some o =>
          let (acc, _) := acc.move id (.graveyard o.owner) none
          acc) g
    let g := g.logMsg s!"{(g.player p).name} discards {n} card(s)"
    if n == 0 then g else g.draw p n

/-- Players currently tied for most life. -/
def playersWithMostLife (g : Game) : Array PlayerId :=
  let living := g.livingPlayers
  match living[0]? with
  | none => #[]
  | some first =>
    let best := living.foldl (fun acc pl => max acc pl.life) first.life
    living.filter (fun pl => pl.life == best) |>.map (·.id)

/-- The Black Gate: check most life as the ability resolves, then those
creatures (including later ones) cannot block the target this turn. -/
def applyBlackGateUnblockable (g : Game) (attackerId : ObjectId)
    (chosen : PlayerId) : Game :=
  if !(g.playersWithMostLife).contains chosen then
    g.logMsg "The chosen player does not have the most life. The ability does nothing."
  else
    match g.findObject? attackerId with
    | none => g.logMsg "The target is no longer legal"
    | some o =>
      if !o.isOnBattlefield then
        g.logMsg "The target is no longer legal"
      else
        let g := g.setObject { o with status :=
          { o.status with cantBeBlockedByPlayer := some chosen } }
        g.logMsg
          s!"{o.name} can't be blocked by creatures {(g.player chosen).name} controls this turn"

/-- Put the returned cards onto the battlefield as Food artifacts only.
They keep name, mana cost, mana value, abilities, and legendary. -/
def supperForSpidersReturn (g : Game) (controller : PlayerId)
    (ids : Array ObjectId) : Game :=
  ids.foldl (fun acc id =>
    match acc.findObject? id with
    | none => acc
    | some o =>
      if o.zone != .graveyard o.owner then acc
      else
        let (acc, newId) := acc.move id .battlefield (some controller)
        let o := acc.object! newId
        let acc := acc.setObject { o with status :=
          { o.status with onlyFoodArtifact := true, summoningSick := true } }
        acc.logMsg s!"{o.name} returns as a Food artifact") g

/-- Exile the top `n` cards face down. They may be played while exiled if you
control `subtype`. Timing and costs are unchanged. -/
def exileTopPlayIfYouControlSubtype (g : Game) (p : PlayerId) (n : Nat)
    (subtype : String) : Game :=
  Id.run do
    let mut g := g
    for _ in List.range n do
      let pl := g.player p
      if pl.library.isEmpty then
        g := g.logMsg s!"{pl.name} has no cards in their library to exile"
      else
        let top := pl.library.back!
        let cardName := (g.object! top).name
        let (g', newId) := g.move top .exile none
        g := g'
        let o := g.object! newId
        g := g.setObject { o with
          playPermission := some {
            player := p
            turnEndsRemaining := 0
            whileExiled := true
            requireSubtype := some subtype
            faceDown := true } }
        g := g.logMsg s!"{pl.name} exiles a card face down"
        let _ := cardName
    return g

/-- Exile cards from `victim`'s library until an instant or sorcery, face up.
An empty library becomes that player's library again. The found card may be
cast as this ability resolves, ignoring timing. Uncast cards go on the bottom
in a random order. -/
partial def grimaExileUntilInstantOrSorcery (g : Game) (controller victim : PlayerId)
    (castTheCard : Bool) : Game :=
  Id.run do
    let mut g := g
    let mut exiled : Array ObjectId := #[]
    let mut found : Option ObjectId := none
    while found.isNone && !(g.player victim).library.isEmpty do
      let top := (g.player victim).library.back!
      let name := (g.object! top).name
      let (g', newId) := g.move top .exile none
      g := g'
      let o := g.object! newId
      g := g.logMsg s!"{(g.player victim).name} exiles {name} face up"
      if o.printed.isInstantOrSorcery then
        found := some newId
      else
        exiled := exiled.push newId
    match found with
    | none =>
      return g.requestOrderInto exiled (.library victim)
        s!"{(g.player victim).name} randomizes the exiled cards; they become that player's library"
    | some instId =>
      if castTheCard then
        let o := g.object! instId
        let (g', _) := g.move instId .stack (some controller)
        g := g'.logMsg
          s!"{(g.player controller).name} casts {o.name} as the ability resolves"
      else
        let (g', _) := g.move instId (.library victim) none
        g := g'
      return g.requestOrderInto exiled (.library victim)
        s!"{(g.player victim).name} puts the remaining exiled cards on the bottom of their library in a random order"

/-- An uncast copy ceases the next time state-based actions are checked. -/
def ceaseUncastCopies (g : Game) : Game :=
  g.objects.foldl (fun acc o =>
    if o.isCopy && o.zone != .stack && o.zone != .battlefield then
      let acc := acc.ceaseToExist o.id
      acc.logMsg s!"{o.name} ceases to exist"
    else acc) g

/-- True when `p` can pay Saruman's ward (discard an enchantment, instant,
or sorcery card). -/
def canPaySarumanWard (g : Game) (p : PlayerId) : Bool :=
  (g.player p).hand.any (fun id =>
    match g.findObject? id with
    | some o => o.printed.isEnchantment || o.printed.isInstant || o.printed.isSorcery
    | none => false)

/-- Split the top four library cards into a face-up pile and a face-down pile.
A 4/0 split is legal. The face-down pile is not revealed if it is put into
hand. -/
def riddlesInTheDark (g : Game) (p : PlayerId) (faceUpCount : Nat)
    (chooseFaceDown : Bool) : Game :=
  let lib := (g.player p).library
  let n := min 4 lib.size
  let taken := lib.extract (lib.size - n) lib.size
  let faceUpN := min faceUpCount taken.size
  let faceUp := taken.extract (taken.size - faceUpN) taken.size
  let faceDown := taken.extract 0 (taken.size - faceUpN)
  let g := g.logMsg
    s!"{(g.player p).name} separates {faceUp.size} face-up and {faceDown.size} face-down"
  let toHand := if chooseFaceDown then faceDown else faceUp
  let toGy := if chooseFaceDown then faceUp else faceDown
  let g :=
    if chooseFaceDown then
      g.logMsg "The face-down pile is put into hand without being revealed"
    else
      g.logMsg "The face-up pile is put into hand"
  let g :=
    toHand.foldl (fun acc id =>
      (acc.move id (.hand p) none).1) g
  toGy.foldl (fun acc id =>
    (acc.move id (.graveyard p) none).1) g

/-- Linked activated abilities last only while the copier still has them. -/
def linkedAbilitiesStillLinked (stillHasThoseAbilities : Bool) : Bool :=
  stillHasThoseAbilities

/-- Treat a copied activated ability as referring to the copier's name. -/
def rewriteAbilityCardName (abilityText printedName copierName : String) : String :=
  abilityText.replace printedName copierName

/-- Must-attack-if-able may be declined when every legal attack would cost. -/
def mustAttackCanDeclineIfOnlyAttackCosts (onlyAttacksRequireCost : Bool) : Bool :=
  onlyAttacksRequireCost

/-- Ares and similar “attacks each combat if able” statics (MSH 130). -/
def hasAttacksIfAble (o : GameObject) : Bool :=
  o.staticAbilities.any (fun
    | .msh .aresAttacksEachCombatIfAble => true
    | _ => false) ||
    o.printed.oracleText.contains "attacks each combat if able"

/-- True when `o` must attack this combat. Summoning sickness, being tapped,
or an unpaid attack cost means it does not have to attack (MSH 130). -/
def mustAttackIfAble (g : Game) (o : GameObject) (attackRequiresCost := false) : Bool :=
  hasAttacksIfAble o && g.canAttack o &&
    !mustAttackCanDeclineIfOnlyAttackCosts attackRequiresCost

/-- Failed Adventure from Bilbo's graveyard ability is exiled by Bilbo, not
as an Adventure, so it cannot be cast as a permanent later. -/
def exileFailedAdventureFromBilbo (g : Game) (id : ObjectId) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    let name := o.name
    let (g, newId) := g.move id .exile none
    let o := g.object! newId
    let g := g.setObject { o with playPermission := none, adventurerCard := none }
    g.logMsg s!"{name} is exiled (Bilbo's replacement). It cannot be cast as a permanent"

/-- Tom Bombadil is on the battlefield as a final chapter finishes resolving,
so his last ability triggers (ruling 74). -/
def finishSagaFinalChapter (g : Game) (controller : PlayerId) : Game :=
  let g := g.logMsg "The final chapter ability is removed from the stack"
  match (g.permanentsOf controller).find? (fun o =>
    o.printed.hexproofIndestructibleIfLore.isSome) with
  | none => g
  | some tom =>
    g.putMatchingSourceTriggers controller tom .finalSagaChapterResolves
        |>.logMsg s!"{tom.name}'s last ability triggers"

/-- A token copy of a battlefield permanent. The copy is not kicked. -/
def copyBattlefieldPermanent (g : Game) (src : GameObject) (controller : PlayerId)
    : Game × GameObject :=
  let (g, tok) := g.createToken controller src.printed
  let tok := { tok with kicked := false }
  (g.setObject tok, tok)

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
    (discardSource : Bool := false)
    (ab : Option ActivatedAbility := none) : Except String Game := do
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
  match ab with
  | some a =>
    if a.cost.removeIndestructibleCounter then
      g := (← g.payRemoveIndestructibleCounter (g.object! sourceId))
    if a.cost.discardACard then
      match (g.player p).hand[0]? with
      | none => throw "No card to discard"
      | some hid =>
        let card := g.object! hid
        g := g.logMsg s!"{(g.player p).name} discards {card.name}"
        let (g', _) := g.move hid (.graveyard card.owner) none
        g := g'.modifyPlayer p (fun pl =>
          { pl with cardsDiscardedThisTurn := pl.cardsDiscardedThisTurn + 1 })
    if a.cost.discardLegendarySameName then
      let names :=
        (g.permanentsOf p).filterMap (fun o =>
          if o.isLegendary then some o.name else none)
      match (g.player p).hand.findSome? (fun hid =>
        match g.findObject? hid with
        | some o =>
          if o.isLegendary && names.contains o.name then some hid else none
        | none => none) with
      | none => throw "No legendary card of the same name to discard"
      | some hid =>
        let card := g.object! hid
        g := g.logMsg s!"{(g.player p).name} discards {card.name}"
        let (g', _) := g.move hid (.graveyard card.owner) none
        g := g'
    if a.cost.sacrificeLegendaryArtifact then
      match (g.permanentsOf p).find? (fun o =>
        o.printed.isArtifact && o.isLegendary &&
          !(sacrificeSource && o.id == sourceId)) with
      | none => throw "No legendary artifact to sacrifice"
      | some art =>
        g := g.sacrificeToGraveyard art
          s!"{(g.player p).name} sacrifices {art.name}"
    if a.cost.sacrificeArtifact then
      match (g.permanentsOf p).find? (fun o => o.printed.isArtifact) with
      | none => throw "No artifact to sacrifice"
      | some art =>
        g := g.sacrificeToGraveyard art
          s!"{(g.player p).name} sacrifices {art.name}"
    if let some t := a.cost.sacrificeAnotherSubtype then
      match (g.permanentsOf p).find? (fun o =>
        o.id != sourceId && g.hasSubtype o t) with
      | none => throw s!"No other {t} to sacrifice"
      | some o =>
        g := g.sacrificeToGraveyard o
          s!"{(g.player p).name} sacrifices {o.name}"
  | none => pure ()
  if sacrificeSource then
    match g.findObject? sourceId with
    | none => pure ()
    | some src =>
      g := g.sacrificeToGraveyard src
        s!"{(g.player p).name} sacrifices {src.name}"
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
        prop.payLife prop.discardSource prop.activation
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

/-- Starting mana cost of `face` before increases and reductions (CR 118.7). -/
def playCostStart (card : GameObject) (face : CardDef) : ManaCost :=
  if card.castFromGraveyard || card.zone == .graveyard card.owner then
    face.flashback.getD face.manaCost
  else face.manaCost

/-- Apply cost reductions to `start` (CR 118.7 / 601.2f). Increases such as
kicker must already be included in `start`. -/
def applyCastCostReductions (g : Game) (card : GameObject) (face : CardDef)
    (start : ManaCost) : ManaCost :=
  let caster := card.controller.getD card.owner
  let afterDied :=
    if face.costReductionIfCreatureDied > 0 && g.creatureDiedThisTurn then
      start.reduceGeneric face.costReductionIfCreatureDied
    else start
  let afterFly :=
    if face.costReductionEqualFlyingPower then
      let n :=
        (g.permanentsOf caster).foldl (fun acc o =>
          if o.isCreature && g.hasFlying o then acc + (g.power o).toNat else acc) 0
      afterDied.reduceGeneric n
    else afterDied
  let afterAff :=
    match face.affinityForSubtype with
    | some t =>
      let st := if t == "Elves" then "Elf" else t
      let n := (g.permanentsOf caster).filter (fun o => g.hasSubtype o st) |>.size
      afterFly.reduceGeneric n
    | none => afterFly
  let afterOpp :=
    if face.costReductionEqualOppArtifacts then
      let n :=
        g.players.foldl (fun acc pl =>
          if pl.id == caster || pl.lost then acc
          else
            let arts :=
              (g.permanentsOf pl.id).filter (fun o => o.printed.isArtifact) |>.size
            max acc arts) 0
      afterAff.reduceGeneric n
    else afterAff
  let afterSpell :=
    if face.isInstant || face.isSorcery then
      let n :=
        (g.permanentsOf caster).foldl (fun acc o =>
          let reduces :=
            o.staticAbilities.any (fun ab =>
              match ab with
              | .instantSorceryCostReductionEqualEquippedPower => true
              | _ => false)
          if !reduces then acc
          else
            match o.attachedTo.bind g.findObject? with
            | some host =>
              if host.isOnBattlefield then acc + (g.power host).toNat else acc
            | none => acc) 0
      afterOpp.reduceGeneric n
    else afterOpp
  let afterFirst :=
    if face.isCreature && (g.player caster).creatureSpellsCastThisTurn == 0 then
      let n :=
        (g.permanentsOf caster).foldl (fun acc o =>
          acc + o.printed.firstCreatureCostsLess) 0
      afterSpell.reduceGeneric n
    else afterSpell
  let notFromHand :=
    match card.zone with
    | .hand _ => 0
    | _ =>
      (g.permanentsOf caster).foldl (fun acc o =>
        acc + o.printed.costReductionNotFromHand) 0
  let afterNotHand := afterFirst.reduceGeneric notFromHand
  let witchLess :=
    if face.isInstant || face.isSorcery then
      let mv := face.manaValue + card.chosenX.getD 0
      if mv < 4 then 0
      else
        (g.permanentsOf caster).foldl (fun acc o =>
          let reduces :=
            o.staticAbilities.any (fun ab =>
              match ab with
              | .msh .instantAndSorcerySpellsYouCastWithManaVa => true
              | _ => false)
          if reduces then acc + (g.power o).toNat else acc) 0
    else 0
  let afterX :=
    match card.chosenX with
    | none => afterNotHand
    | some x =>
      { symbols := afterNotHand.symbols.foldl (fun acc s =>
          match s with
          | ManaSymbol.x =>
            if x == 0 then acc else acc.push (ManaSymbol.generic x)
          | _ => acc.push s) (#[] : Array ManaSymbol) }
  let afterWitch := afterX.reduceGeneric witchLess
  let subtypeLess :=
    (g.permanentsOf caster).foldl (fun acc o =>
      o.staticAbilities.foldl (fun acc ab =>
        match ab with
        | .subtypeSpellsCostLess subtype n =>
          if face.hasSubtype subtype then acc + n else acc
        | _ => acc) acc) 0
  afterWitch.reduceGeneric subtypeLess

/-- Mana to pay for `face` after alternative costs and pre-target reductions
(CR 118.7 / 601.2f). `withoutManaCost` and a reduction that removes every
mana symbol become `{0}`, not an unpayable empty cost (CR 107.4d / 202.1b).
Target-based reductions lock in after CR 601.2c. Cost increases (kicker)
are applied before these reductions. -/
def playManaCost (g : Game) (card : GameObject) (face : CardDef)
    (increase : ManaCost := ManaCost.empty) : ManaCost :=
  let start := playCostStart card face
  let afterIncrease := start.addCost increase
  let afterEquip := g.applyCastCostReductions card face afterIncrease
  let freeRG :=
    match g.pendingFreeRGCreature with
    | some p =>
      (card.controller == some p || card.owner == p) && face.isCreature &&
        (face.colors.contains .red || face.colors.contains .green)
    | none => false
  let cost :=
    if freeRG then
      g.applyCastCostReductions card face (ManaCost.empty.addCost increase)
    else
      match card.playPermission with
      | some perm =>
        if perm.withoutManaCost || perm.payLifeEqualManaValue then
          g.applyCastCostReductions card face (ManaCost.empty.addCost increase)
        else if perm.anyMana then ManaCost.ofGeneric afterEquip.manaValue
        else afterEquip
      | none => afterEquip
  ManaCost.afterReduction face.manaCost cost

/-- True when `face` has a mana cost that would not be paid to play `card`. -/
def playsWithoutPayingManaCost (g : Game) (card : GameObject)
    (face : CardDef := card.printed) : Bool :=
  face.manaCost.includesManaPayment && !(g.playManaCost card face).includesManaPayment

/-- Extra lifetime power-up activations granted by Wonder Man (MSH). -/
def grantsExtraPowerUp (o : GameObject) : Bool :=
  o.printed.staticAbilities.any (fun ab =>
    match ab with
    | .msh .eachPowerUpAbilityOfPermanentsYouControl => true
    | _ => false)

/-- Extra lifetime power-up activations granted by Wonder Man (MSH). -/
def powerUpActivationLimit (g : Game) (p : PlayerId) : Nat :=
  1 + ((g.permanentsOf p).filter grantsExtraPowerUp).size

/-- True when `o` is Hulk's generic power-up cost reduction. -/
def grantsHulkPowerUpReduction (o : GameObject) : Bool :=
  o.printed.staticAbilities.any (fun ab =>
    match ab with
    | .msh .powerUpAbilitiesOfOtherCreaturesYouContro => true
    | _ => false)

/-- Generic mana subtracted from other creatures' power-up costs by Hulk
(MSH ruling 127: only generic mana). -/
def hulkPowerUpGenericReduction (g : Game) (p : PlayerId) (sourceId : ObjectId) : Nat :=
  3 * ((g.permanentsOf p).filter (fun o =>
    o.id != sourceId && grantsHulkPowerUpReduction o)).size

def activationManaCost (g : Game) (p : PlayerId) (ab : ActivatedAbility)
    (source : Option GameObject := none) : ManaCost :=
  let cost :=
    if ab.powerUp then
      match source with
      | some o =>
        let afterEnter :=
          if o.status.enteredThisTurn then
            ab.cost.mana.reduceByCost o.printed.manaCost
          else ab.cost.mana
        afterEnter.reduceGeneric (g.hulkPowerUpGenericReduction p o.id)
      | none => ab.cost.mana
    else if ab.costReductionIfYouControlLegendary > 0 && g.controlsLegendaryCreature p then
      ab.cost.mana.reduceGeneric ab.costReductionIfYouControlLegendary
    else if ab.costReductionPerEquipment > 0 then
      let n := (g.permanentsOf p).filter (fun o => o.printed.isEquipment) |>.size
      ab.cost.mana.reduceGeneric (ab.costReductionPerEquipment * n)
    else ab.cost.mana
  ManaCost.afterReduction ab.cost.mana cost

/-- True when `ab` has a mana cost that `p` would not pay to activate it. -/
def activatesWithoutPayingManaCost (g : Game) (p : PlayerId) (ab : ActivatedAbility)
    (source : Option GameObject := none) : Bool :=
  ab.cost.mana.includesManaPayment && !(g.activationManaCost p ab source).includesManaPayment

/-- After proposing a spell or activated ability, announce modes and additional
costs (CR 601.2b), then targets (CR 601.2c), then mana abilities (CR 601.2g). -/
def enterProposalWindow (g : Game) (p : PlayerId) (pl : Player) (prop : ProposedSpell)
    (needsMode needsTarget : Bool) (modeCitation : String)
    (needsAdditionalCost : Bool := false) (needsKicker : Bool := false)
    (needsGift : Bool := false) (needsTeamwork : Bool := false) : Game :=
  if needsMode then
    let g := { g with pending := .chooseMode p, proposedSpell := some prop }
    g.logMsg s!"{pl.name} must choose a mode ({modeCitation})"
  else if needsAdditionalCost then
    let g := { g with pending := .chooseAdditionalCost p, proposedSpell := some prop }
    g.logMsg s!"{pl.name} must choose an additional cost (CR 601.2b)"
  else if needsKicker then
    let g := { g with pending := .chooseKicker p, proposedSpell := some prop }
    g.logMsg s!"{pl.name} may kick the spell (CR 702.32 / 601.2b)"
  else if needsGift then
    let g := { g with pending := .chooseGift p, proposedSpell := some prop }
    g.logMsg s!"{pl.name} may promise a gift (CR 702.185 / 601.2b)"
  else if needsTeamwork then
    let g := { g with pending := .chooseTeamwork p, proposedSpell := some prop }
    g.logMsg s!"{pl.name} may pay a teamwork cost (CR 702.194 / 601.2b)"
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
  if p != g.activePlayer &&
      (g.permanentsOf g.activePlayer).any (fun o =>
        o.staticAbilities.any (fun
          | .opponentsCantCastOnYourTurn => true
          | _ => false)) then
    throw "Opponents can't cast spells during that player's turn"
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
  if face.isModal then
    if !face.spellModes.any (g.spellModeIsChoosable p) && !face.allowsZeroTargets then
      throw s!"{face.name} requires a target"
  else if face.requiresTarget &&
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
  let fromTop :=
    original.zone == .library p && (g.player p).library.back? == some id
  let (g, newId) := g.move id .stack (some p)
  let g := { g with castingFromTop := fromTop || g.castingFromTop }
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
  let needsKicker := face.kicker.isSome
  let needsGift := face.giftTreasure
  let needsTeamwork := face.teamwork.isSome
  if !needsMode && !needsTarget && !cost.includesManaPayment && !needsSacrifice &&
      !needsAdditionalCostChoice && !needsKicker && !needsGift && !needsTeamwork then
    return g.becomeCast p (g.object! newId)
  let lifeInstead :=
    match original.playPermission with
    | some perm =>
      if perm.payLifeEqualManaValue then g.objectManaValue original else 0
    | none => 0
  let prop : ProposedSpell := {
    caster := p
    cost := cost
    spellId := newId
    original := original
    handBefore := handBefore
    stackBefore := stackBefore
    manaBefore := manaBefore
    needsSacrificeOther := needsSacrifice
    payLife := lifeInstead
  }
  let g := g.logMsg s!"{pl.name} begins casting {face.name}"
  return g.enterProposalWindow p pl prop needsMode needsTarget "CR 601.2b / 700.2"
    (needsAdditionalCost := needsAdditionalCostChoice)
    (needsKicker := needsKicker) (needsGift := needsGift)
    (needsTeamwork := needsTeamwork)

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
      if !g.spellModeIsChoosable p effect then
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

/-- Loki (MSH 247): when a player or permanent becomes the target of an
ability you control, those triggers wait on the stack above that ability. -/
def queueYouTargetTriggers (g : Game) (controller : PlayerId) (obj : GameObject) : Game :=
  if obj.abilityEffect.isSome || obj.triggeredAbility.isSome then
    g.putControlledTriggers controller .youTargetSomething
  else g

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
      g := g.queueYouTargetTriggers p obj
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
        g := g.queueYouTargetTriggers p obj
        return g.afterTriggerTargetsChosen
      if choices.size != 1 then
        throw "Choose each instance of the word \"target\" separately (CR 601.2c)"
      let t := choices[0]!.1
      if !(g.legalProposedTargets p obj).contains t then
        throw "Illegal target (CR 601.2c)"
      let g := g.setStackEntryTargets obj.id (e.targets.push t)
      let g := g.logMsg
        s!"{(g.player p).name} chooses {g.targetLogName t} as a target (CR 601.2c)"
      if g.currentTargetSlot obj < kind.spec.slots.size then
        return { g with pending := .chooseTargets p }
      if g.proposedSpell.isSome then
        return g.afterTargetsChosen
      let g := g.queueYouTargetTriggers p obj
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

/-- Shang-Chi: activate tap abilities as though creatures had haste
(MSH 280). Does not grant haste and does not allow attacking. -/
def activatesAsThoughHaste (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o =>
    o.staticAbilities.any (fun
      | .msh .youMayActivateAbilitiesOfCreaturesYouCont => true
      | _ => false))

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
  if ab.powerUp &&
      (Nat.max o.status.powerUpActivations (if o.status.powerUpUsed then 1 else 0)) ≥
        g.powerUpActivationLimit p then
    throw s!"{o.name}'s power-up ability can be activated only once"
  if ab.cost.tap && o.status.tapped then
    throw s!"{o.name} is already tapped"
  if ab.cost.tap && o.hasSummoningSickness && !g.activatesAsThoughHaste p then
    throw s!"{o.name} has summoning sickness (CR 302.6)"
  if ab.cost.sacrificeAnotherCreatureOrArtifact &&
      (g.sacrificeCreatureOrArtifactChoices p o.id).isEmpty then
    throw s!"{o.name}'s ability requires sacrificing another creature or artifact"
  if !g.canPayLife p ab.cost.payLife then
    throw s!"{(g.player p).name} cannot pay {ab.cost.payLife} life"
  match ab.effect with
  | .mshSpell .drawACardActivateOnlyIfYouControlACrea =>
    if !(g.permanentsOf p).any (fun x => x.isCreature && g.toughness x >= 4) then
      throw s!"{o.name}'s ability can be activated only if you control a creature with toughness 4 or greater"
  | .mshSpell .createATapped21BlackVillainCreatureToken =>
    let gy :=
      (g.player p).graveyard.filter (fun id =>
        match g.findObject? id with
        | some c => c.printed.isCreature
        | none => false) |>.size
    if gy < 2 then
      throw s!"{o.name}'s ability can be activated only if there are two or more creature cards in your graveyard"
  | _ => pure ()
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
  let abs := g.activatedAbilitiesOf o
  if abs.isEmpty then
    throw s!"{o.name} has no activated ability"
  let some ab := abs[abilityIdx]?
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
      ab.cost.payLife ab.cost.discardSource (some ab)
    return g.becomeActivated p o.name (some id)
  let manaCost := g.activationManaCost p ab (some o)
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
    activation := some ab
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
  g.nextActorWhere players (fun p =>
    g.stillInGame p && !(g.creaturesControlledBy p).isEmpty)

/-- First player in `players` who has a card in hand, plus those after them. -/
def nextActorWithHandCard (g : Game) (players : Array PlayerId) :
    Option (PlayerId × Array PlayerId) :=
  g.nextActorWhere players (fun p =>
    g.stillInGame p && !(g.player p).hand.isEmpty)

/-- Sacrifice the chosen creatures simultaneously, then give priority. -/
def finishChosenSacrifices (g : Game) (chosen : Array ObjectId) : Game :=
  Id.run do
    let mut g := { g with pending := .none }
    for id in chosen do
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield && o.isCreature then
          let who := o.controller.getD o.owner
          g := g.sacrificeToGraveyard o
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
    let g :=
      if g.conniveSource.isSome then
        { g with conniveSource := none }.logMsg
          "No card is discarded; the conniving creature does not receive a +1/+1 counter"
      else g
    { g with pending := .none, thirstDiscardsLeft := 0 }.receivePriority g.activePlayer
  | some (p, rest) =>
    { g with pending := .chooseDiscardCard p rest }
      |>.logMsg s!"{(g.player p).name} must discard a card"

/-- Draw, then discard. If a nonland is discarded and the source is still on
the battlefield, put a +1/+1 counter on it. The creature still connives if it
has left (MSH / CR 701.47). -/
def applyConnive (g : Game) (controller : PlayerId) (sourceId : Option ObjectId) : Game :=
  let g := { g with conniveSource := sourceId }
  let g := g.logMsg s!"{(g.player controller).name}'s creature connives"
  let g := g.draw controller 1
  if (g.player controller).hand.isEmpty then
    let g := { g with conniveSource := none }
    g.logMsg "No card is discarded; the conniving creature does not receive a +1/+1 counter"
  else
    g.beginDiscardCards #[controller]

/-- Finish a pending connive after a card is discarded. -/
def finishConniveDiscard (g : Game) (discarded : GameObject) : Game :=
  match g.conniveSource with
  | none => g
  | some sid =>
    let g := { g with conniveSource := none }
    if discarded.printed.isLand then
      g.logMsg "A land was discarded; the conniving creature does not receive a +1/+1 counter"
    else
      match g.findObject? sid with
      | some o =>
        if o.isOnBattlefield then
          let g := g.setObject { o with status := { o.status with
            plusOnePlusOne := o.status.plusOnePlusOne + 1 } }
          g.logMsg s!"{o.name} gets a +1/+1 counter"
        else
          g.logMsg "The conniving creature has left the battlefield; no +1/+1 counter is put"
      | none =>
        g.logMsg "The conniving creature has left the battlefield; no +1/+1 counter is put"

/-- After mana is paid, sacrifice an artifact or creature (CR 601.2h / 602.2b), or sacrifice a creature a resolved trigger requires (CR 608.2d / 701.17). -/
def sacrificeForActivation (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  match g.pending with
  | .sacrificePermanent caster sourceId =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may sacrifice"
    let some sac := g.findObject? id | throw "no such object"
    if !g.canSacrificeAsCreatureOrArtifact p sourceId sac then
      throw s!"Can't sacrifice {sac.name}"
    let g := g.sacrificeToGraveyard sac
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
    let g := g.sacrificeToGraveyard sac
      s!"{(g.player p).name} sacrifices {sac.name}"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | .maySacrificeAnotherBolg q bolgId =>
    if p != q then
      throw s!"Only {(g.player q).name} may sacrifice"
    let some sac := g.findObject? id | throw "no such object"
    if !sac.isOnBattlefield || !sac.isCreature || !sac.controlledBy p ||
        sac.id == bolgId then
      throw s!"Can't sacrifice {sac.name} to Bolg"
    let pw := g.power sac
    let g := g.sacrificeToGraveyard sac
      s!"{(g.player p).name} sacrifices {sac.name} (Bolg)"
    let g := { g with pending := .none }
    match g.findObject? bolgId with
    | none =>
      return g.receivePriority g.activePlayer
    | some bolg =>
      match bolg.controller with
      | none => return g.receivePriority g.activePlayer
      | some c =>
        let g := g.queueTrigger c bolg .onBolgDealSacrificedPower
          .bolgSacrificedForReflexive (lastKnownPower := some pw)
        return g.receivePriority g.activePlayer
  | _ => throw "Not time to sacrifice a permanent"

/-- Destroy a permanent (CR 701.7). Indestructible permanents aren't destroyed
(CR 702.12b / 701.7b). If it would die this turn under an exile replacement,
`move` sends it to exile instead of the graveyard (CR 614.1). -/
def destroyPermanent (g : Game) (o : GameObject) : Game :=
  if o.status.shield > 0 then
    let g := g.setObject { o with status := { o.status with shield := o.status.shield - 1 } }
    g.logMsg s!"A shield counter is removed from {o.name} instead of destroying it"
  else if g.hasIndestructible o then
    g.logMsg s!"{o.name} is indestructible and isn't destroyed"
  else
    g.moveToOwnerGraveyard o s!"{o.name} is destroyed"

/-- Update `o`'s status in place. -/
def mapObjectStatus (g : Game) (o : GameObject) (f : Status → Status) : Game :=
  g.setObject { o with status := f o.status }

/-- Queue “a creature you control is dealt damage” triggers (She-Hulk). -/
def queueCreatureYouControlDealtDamage (g : Game) (o : GameObject) (n : Int) : Game :=
  if n <= 0 || !o.isCreature then g
  else
    match o.controller with
    | none => g
    | some p =>
      g.foldControlledPermanents p (excludeId := none) (fun g src =>
        g.putMatchingSourceTriggers p src .creatureYouControlDealtDamage (some n))

/-- Deal `n` damage to a creature and log `msg`. `deathtouch` records that a
source with deathtouch dealt this damage (CR 702.2 / 704.5h). -/
def markDamageOn (g : Game) (o : GameObject) (n : Int) (msg : String)
    (deathtouch := false) (combat := false) (unpreventable := false) : Game :=
  let healsOther :=
    o.printed.staticAbilities.any (fun
      | .msh .ifDamageWouldBeDealtToWolverine => true
      | _ => false)
  let o :=
    if healsOther && n > 0 then
      { o with status := { o.status with damage := 0 } }
    else o
  let g := if healsOther && n > 0 then g.setObject o else g
  if n > 0 && o.status.shield > 0 && !unpreventable then
    let g := g.setObject { o with status := { o.status with shield := o.status.shield - 1 } }
    g.logMsg s!"A shield counter is removed from {o.name} instead of damage"
  else if n > 0 && o.status.shield > 0 && unpreventable then
    let g := g.setObject { o with status := { o.status with shield := o.status.shield - 1 } }
    let g := g.logMsg s!"A shield counter is removed from {o.name} (unpreventable damage)"
    let g := (g.mapObjectStatus (g.object! o.id) (fun s => s.addDamage n deathtouch)).logMsg msg
    g.queueCreatureYouControlDealtDamage (g.object! o.id) n
  else
  let g := (g.mapObjectStatus o (fun s => s.addDamage n deathtouch)).logMsg msg
  let g :=
    if n > 0 then
      match o.controller with
      | some p =>
        let already := g.waitingTriggers.any (fun t =>
          t.source.id == o.id && t.event == .sourceDealtDamage)
        let g :=
          if already then g
          else g.putMatchingSourceTriggers p (g.object! o.id) .sourceDealtDamage
        let hasEnrage :=
          o.printed.triggeredAbilities.any (fun ab =>
            match ab with
            | .msh .enrageWheneverTheIncredi => true
            | _ => false)
        if !already && hasEnrage && o.status.attacking then
          { g with enrageGrantsAdditionalCombat := g.enrageGrantsAdditionalCombat + 1 }
        else g
      | none => g
    else g
  let g := g.queueCreatureYouControlDealtDamage o n
  if n > 0 && !combat then
    match o.controller with
    | none => { g with lastNoncombatDamage := some (o.id, n.toNat) }
    | some p =>
      let g := { g with lastNoncombatDamage := some (o.id, n.toNat) }
      g.putMatchingSourceTriggers p o .sourceDealtNoncombatDamage
        (some n)
  else g

/-- Extra noncombat damage from Hawkeye, Young Avenger. X is his power at
the time the damage would be dealt (MSH 305). -/
def hawkeyeNoncombatBonus (g : Game) (sourceController : PlayerId) : Int :=
  (g.permanentsOf sourceController).foldl (fun acc o =>
    if o.staticAbilities.any (fun
      | .msh .ifASourceYouControlWouldDealNoncombatDam => true
      | _ => false) then
      acc + g.power o
    else acc) (0 : Int)

/-- Each attached Mjölnir doubles damage (two → ×4, three → ×8; MSH 237). -/
def mjolnirMultiplier (g : Game) (src : GameObject) : Nat :=
  let n :=
    (g.battlefield.filter (fun o =>
      o.attachedTo == some src.id &&
        o.staticAbilities.any (fun
          | .msh .doubleAllDamageEquippedCreatureWouldDeal => true
          | _ => false))).size
  if n == 0 then 1 else Nat.pow 2 n

/-- Apply Hawkeye then Mjölnir. If all damage is prevented, neither
replacement applies (MSH 177 / 178). Combat assignment happens first;
this multiplies the already-divided amounts (MSH 179). -/
def replacedDamageAmount (g : Game) (src : GameObject) (n : Int)
    (combat := false) : Int :=
  if g.sourceDamagePrevented src then 0
  else
    let extra :=
      if combat then (0 : Int)
      else
        match src.controller with
        | some p => g.hawkeyeNoncombatBonus p
        | none => (0 : Int)
    (n + extra) * Int.ofNat (g.mjolnirMultiplier src)

/-- Deal `n` damage to a creature and log the generic “is dealt” message. -/
def dealDamageToPermanent (g : Game) (o : GameObject) (n : Int) : Game :=
  g.markDamageOn o n s!"{o.name} is dealt {n} damage"

/-- Deal `n` damage from a named source (fight, dies trigger, blocked trigger). -/
def dealDamageFrom (g : Game) (sourceName : String) (o : GameObject) (n : Int)
    (deathtouch := false) (source : Option GameObject := none) : Game :=
  match source with
  | some src =>
    if g.sourceDamagePrevented src then
      g.logMsg s!"damage from {src.name} is prevented"
    else
      let n := g.replacedDamageAmount src n
      let g :=
        g.mapObjectStatus src (fun s => { s with dealtDamageThisTurn := true })
      g.markDamageOn o n s!"{sourceName} deals {n} damage to {o.name}" deathtouch
  | none =>
    g.markDamageOn o n s!"{sourceName} deals {n} damage to {o.name}" deathtouch

/-- Deal `n` damage to a player and log the resulting life total (CR 120). -/
def dealDamageToPlayer (g : Game) (pid : PlayerId) (n : Int)
    (preventable := true) (source : Option GameObject := none) : Game :=
  let n :=
    match source with
    | some src =>
      if g.sourceDamagePrevented src then (0 : Int)
      else g.replacedDamageAmount src n
    | none => n
  let pl := g.player pid
  if n == 0 && source.isSome then
    g.logMsg s!"damage from the source is prevented"
  else if preventable && pl.protectionFromEverything then
    g.logMsg s!"damage to {pl.name} is prevented (protection from everything)"
  else
    g.setLife pid (pl.life - n) s!"{pl.name} is dealt {n} damage ({pl.life - n} life)"

/-- Decrease `p`'s life total (CR 118.3a). Losing 0 life does nothing
(CR 118.9). Loss of life is not damage (CR 120.3). -/
def loseLife (g : Game) (p : PlayerId) (n : Nat) : Game :=
  if n == 0 then g
  else
    let pl := g.player p
    let g := g.setLife p (pl.life - (n : Int)) s!"{pl.name} loses {n} life ({pl.life - (n : Int)} life)"
    let g := { g with lastLifeLost := some (p, n) }
    g.livingPlayers.foldl (fun acc pl =>
      acc.putControlledTriggers pl.id .playerLosesLife) g

/-- Increase `p`'s life total (CR 118.2). Gaining 0 life does nothing (CR 118.9). -/
def gainLife (g : Game) (p : PlayerId) (n : Nat) : Game :=
  if n == 0 then g
  else
    let pl := g.player p
    let g := g.setLife p (pl.life + (n : Int))
      s!"{pl.name} gains {n} life ({pl.life + (n : Int)} life)"
    let g := g.modifyPlayer p (fun pl =>
      { pl with lifeGainedThisTurn := pl.lifeGainedThisTurn + n })
    g.putControlledTriggers p .youGainLife

/-- If a shuffle is waiting for a `--norandom` result, leave it. Otherwise
run a stored draw or life-gain after-action. -/
def continueIfShuffled (g : Game) : Game :=
  match g.pendingRandom? with
  | some _ => g
  | none =>
    let after := g.afterRandom
    let g := { g with afterRandom := .none }
    match after with
    | .draw p n => g.draw p n
    | .gainLife p n => g.gainLife p n
    | other => { g with afterRandom := other }

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

/-- Until-end-of-turn +P/+T on each creature `p` controls. -/
def pumpControlledCreatures (g : Game) (p : PlayerId) (pw tw : Int) : Game :=
  g.forEachControlledCreature p (fun g o => g.pumpPermanent o pw tw)

/-- Grant `kw` until end of turn to each creature `p` controls that matches `pred`. -/
def grantUntilEotToControlledCreatures (g : Game) (p : PlayerId) (kw : Keywords)
    (label : String) (pred : Game → GameObject → Bool := fun _ _ => true) : Game :=
  g.forEachControlledCreature p fun g o =>
    if pred g o then
      g.mapObjectStatus o (·.grantUntilEot kw)
        |>.logMsg s!"{o.name} gains {label} until end of turn"
    else g

/-- Move `id` to `to`'s hand and log the return. -/
def returnToHand (g : Game) (id : ObjectId) (to : PlayerId) : Game :=
  let name := (g.object! id).name
  let (g, _) := g.move id (.hand to) none
  g.logMsg s!"{name} is returned to {(g.player to).name}'s hand"

/-- Put `n` finality counters on `o` (MSH). Multiple counters are redundant. -/
def addFinalityTo (g : Game) (o : GameObject) (n : Nat := 1) : Game :=
  let n := g.extraCountersOn o.controller n
  let g := g.mapObjectStatus o (fun s => { s with finality := s.finality + n })
  g.logMsg s!"{o.name} gets a finality counter"

/-- Frozen in Ice or Spider-Woman prevents this permanent becoming untapped. -/
def hostCantBecomeUntapped (g : Game) (o : GameObject) : Bool :=
  let frozen :=
    g.battlefield.any (fun aura =>
      aura.attachedTo == some o.id &&
        aura.printed.staticAbilities.any (fun
          | .msh .enchantedCreatureLosesAllAbilitiesAndCant => true
          | _ => false))
  let granted :=
    o.status.cantUntapGrantedBy.any (fun sid =>
      match g.findObject? sid with
      | some src => src.isOnBattlefield
      | none => false)
  frozen || granted

/-- Timestamp-ordered maximum hand size (MSH 184 / 376). `10000` is "no maximum". -/
def grantsNoMaxHandSize (o : GameObject) : Bool :=
  o.printed.staticAbilities.any (fun
    | .msh .youHaveNoMaximumHandSize => true
    | _ => false)

def grantsMaxHandSizeTen (o : GameObject) : Bool :=
  o.printed.staticAbilities.any (fun
    | .msh .yourMaximumHandSizeIsTen => true
    | _ => false)

def effectiveMaxHandSize (g : Game) (p : PlayerId) : Nat :=
  let effects :=
    ((g.permanentsOf p).filter (fun o =>
      grantsNoMaxHandSize o || grantsMaxHandSizeTen o)).qsort
      (fun a b => decide (a.timestamp < b.timestamp))
  effects.foldl (fun acc o =>
    if grantsMaxHandSizeTen o then 10
    else if grantsNoMaxHandSize o then 10000
    else acc) (g.player p).maxHandSize

/-- Reduce generic mana in `cost` by `n` (improvise taps artifacts for {1}). -/
def improviseReduce (cost : ManaCost) (n : Nat) : ManaCost :=
  cost.reduceGeneric n

/-- Whether `face` has improvise, including from a granting permanent. -/
def spellHasImprovise (g : Game) (face : CardDef) (caster : PlayerId) : Bool :=
  face.hasImprovise ||
    (!face.isCreature &&
      (g.permanentsOf caster).any (fun o => o.printed.grantsImproviseToNoncreature))

/-- Tap untapped artifacts you control for improvise. Each pays {1}. -/
def tapArtifactsForImprovise (g : Game) (p : PlayerId) (ids : Array ObjectId) :
    Except String Game := do
  let mut g := g
  let mut seen : Array ObjectId := #[]
  for id in ids do
    if seen.contains id then
      throw "An artifact cannot be tapped twice for the same improvise payment"
    seen := seen.push id
    let some o := g.findObject? id | throw "no such object"
    if !(o.isOnBattlefield && o.printed.isArtifact && o.controlledBy p) then
      throw s!"{o.name} is not an artifact you control"
    if o.status.tapped then
      throw s!"{o.name} is already tapped"
    g := g.mapObjectStatus o (fun s => { s with tapped := true })
  return g.logMsg s!"{(g.player p).name} taps {ids.size} artifact(s) for improvise"

/-- True when a boast ability of `o` may be activated (MSH / CR 702.111). -/
def canActivateBoast (_g : Game) (o : GameObject) : Bool :=
  o.printed.hasBoast && o.status.declaredAsAttackerThisTurn && !o.status.boastUsedThisTurn

/-- Mark a boast activation used for the turn. -/
def markBoastUsed (g : Game) (o : GameObject) : Game :=
  g.mapObjectStatus o (fun s => { s with boastUsedThisTurn := true })
    |>.logMsg s!"{o.name}'s boast ability is activated"

/-- Legal only during the declare blockers step of the caster's turn. -/
def canCastForSneak (g : Game) (p : PlayerId) : Bool :=
  g.activePlayer == p && g.step == .declareBlockers

/-- Pay sneak: return an unblocked attacker you control to hand and mark
the spell. The creature enters tapped and attacking the same player. -/
def paySneak (g : Game) (p : PlayerId) (spellId : ObjectId) (attackerId : ObjectId) :
    Except String Game := do
  if !g.canCastForSneak p then
    throw "Sneak can be paid only during the declare blockers step on your turn"
  let some attacker := g.findObject? attackerId | throw "no such object"
  if !(attacker.isOnBattlefield && attacker.isCreature && attacker.controlledBy p) then
    throw s!"{attacker.name} is not a creature you control"
  if !attacker.status.attacking then
    throw s!"{attacker.name} is not attacking"
  if attacker.status.blocked then
    throw s!"{attacker.name} is blocked"
  let whom := attacker.status.attackingWhom
  let some _spell := g.findObject? spellId | throw "The spell left the stack"
  let g := g.returnToHand attackerId attacker.owner
  let g := g.setObject { (g.object! spellId) with
    sneakPaid := true, sneakAttackWhom := whom }
  return g.logMsg s!"{(g.player p).name} pays a sneak cost"

/-- Equip worthy may attach only to a legendary non-Villain red or white
creature. Other attach effects ignore this restriction. -/
def isWorthyPermanent (_g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield && o.isCreature && o.printed.isWorthy

/-- Put `n` +1/+1 counters on `o` (CR 122.1). -/
def addPlusOnePlusOneTo (g : Game) (o : GameObject) (n : Nat := 1) : Game :=
  let n := g.extraCountersOn o.controller n
  let g := g.mapObjectStatus o (fun s =>
    { (s.addPlusOnePlusOne n) with gotPlusOneThisTurn := s.gotPlusOneThisTurn || n > 0 })
  let g := g.logMsg s!"{o.name} gets {plusOnePlusOneCountersPhrase n}"
  match o.controller with
  | none => g
  | some p =>
    let g :=
      if n > 0 then g.putControlledTriggers p .youPutPlusOne else g
    if n > 0 &&
        (g.hasSubtype o "Goblin" || g.hasSubtype o "Orc" || g.hasSubtype o "Army") then
      g.putControlledTriggers p .youPutCountersOnGoblinOrcArmy
    else g

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
    (kind : String) (onFound : Game → ObjectId → Game) (find := true) : Game :=
  let pl := g.player p
  let g :=
    if !find then
      g.logMsg s!"{pl.name} chooses not to find a {kind}"
    else
      match g.findLibraryCard? p pred with
      | none => g.logMsg s!"{pl.name} searches their library and finds no {kind}"
      | some id => onFound g id
  g.shuffleLibrary p

/-- Search `p`'s library for a card matching `pred`, put it onto the battlefield
(tapped if `tapped`), then shuffle (CR 701.19). Picks the first matching card
in library order (bottom first). -/
def resolveSearchLibrary (g : Game) (p : PlayerId) (pred : CardDef → Bool)
    (tapped : Bool) (kind : String) (find := true) : Game :=
  g.resolveLibrarySearch p pred kind (find := find) fun g landId =>
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
def resolveSearchForest (g : Game) (p : PlayerId) (find := true) : Game :=
  g.resolveSearchLibrary p isForestCard false "Forest card" (find := find)

/-- Search `p`'s library for a card matching `pred`, reveal it, put it into
their hand, then shuffle. -/
def resolveLibrarySearchToHand (g : Game) (p : PlayerId)
    (pred : CardDef → Bool) (kind : String) : Game :=
  g.resolveLibrarySearch p pred kind fun g cardId =>
    let cardName := (g.object! cardId).name
    let (g, _) := g.move cardId (.hand p) none
    g.logMsg s!"{(g.player p).name} reveals {cardName} and puts it into their hand"

/-- Search `p`'s library for a card with land type `landType`, reveal it, put
it into their hand, then shuffle (CR 701.19 / 702.29). Picks the first matching
card in library order (bottom first). -/
def resolveSearchLandTypeToHand (g : Game) (p : PlayerId) (landType : String) : Game :=
  g.resolveLibrarySearchToHand p (fun c => c.hasSubtype landType) s!"{landType} card"

/-- Search `p`'s library for a basic land, put it into their hand, then shuffle. -/
def resolveSearchBasicLandToHand (g : Game) (p : PlayerId) : Game :=
  g.resolveLibrarySearchToHand p isBasicLandCard "basic land card"

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
      let first := !o.status.becameTappedThisTurn
      let g := g.mapObjectStatus o (fun s =>
        { s with tapped := true, becameTappedThisTurn := true })
      let g := g.logMsg s!"{o.name} becomes tapped"
      let g := { g with lastBecameTapped := some o.id }
      match o.controller with
      | some p =>
        if first && g.activePlayer == p then
          g.foldControlledPermanents p (excludeId := none) (fun g src =>
            g.putMatchingSourceTriggers p src .creatureYouControlTapped
              (cause := some (g.object! o.id)))
        else g
      | none => g
  | .untap =>
    if g.hostCantBecomeUntapped o then
      g.logMsg s!"{o.name} can't become untapped"
    else if !o.status.tapped then
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

/-- Mill `n`, then put matching milled cards from the graveyard into hand.
`maxPut` limits how many are returned (`none` means all matches). -/
def millThenPutFromGy (g : Game) (p : PlayerId) (n : Nat)
    (pred : GameObject → Bool) (maxPut : Option Nat := none) : Game :=
  let g := g.mill p n
  let gy := (g.player p).graveyard
  let take := gy.size.min n
  let milled := gy.extract (gy.size - take) gy.size
  Id.run do
    let mut g := g
    let mut left := maxPut.getD milled.size
    for id in milled do
      if left > 0 && pred (g.object! id) then
        let name := (g.object! id).name
        let (g', _) := g.move id (.hand p) none
        g := g'.logMsg s!"{(g.player p).name} puts {name} into their hand"
        left := left - 1
    return g

/-- Deal `n` damage to each non-Dragon creature. -/
def dealDamageToEachNonDragon (g : Game) (n : Nat) : Game :=
  g.foldBattlefield (fun o => o.isCreature && !g.hasSubtype o "Dragon")
    (fun g o => g.applyPermanentAction o (.dealDamage n))

/-- Palantír of Orthanc: an illegal target means no influence, scry, draw,
or mill. -/
def applyPalantir (g : Game) (sourceId : ObjectId) (target : Option PlayerId) : Game :=
  match target with
  | none =>
    g.logMsg
      "The target is no longer legal. No influence counter, scry, draw, or mill."
  | some pid =>
    if (g.player pid).lost then
      g.logMsg
        "The target is no longer legal. No influence counter, scry, draw, or mill."
    else
      match g.findObject? sourceId with
      | none =>
        g.logMsg
          "The target is no longer legal. No influence counter, scry, draw, or mill."
      | some src =>
        if !src.isOnBattlefield || pid == src.you then
          g.logMsg
            "The target is no longer legal. No influence counter, scry, draw, or mill."
        else
          let g := g.setObject { src with status :=
            { src.status with influence := src.status.influence + 1 } }
          let g := g.logMsg s!"{src.name} gets an influence counter"
          g.beginScry src.you 2

/-- Put a card onto the stack as an ability is resolving. Timing may be
ignored. The permission does not last after this ability finishes. -/
def castAsPartOfResolution (g : Game) (p : PlayerId) (id : ObjectId)
    (ignoreTiming := true) (withoutManaCost := true) : Game :=
  match g.findObject? id with
  | none => g.logMsg "There is no card to cast"
  | some o =>
    if !ignoreTiming && !g.timingAllowsCast p o.printed then
      g.logMsg s!"{o.name} cannot be cast now (timing)"
    else if !withoutManaCost &&
        !(g.player p).manaPool.canPay (g.playManaCost o o.printed) then
      g.logMsg s!"{o.name} cannot be cast (costs)"
    else
      let name := o.name
      let (g, newId) := g.move id .stack (some p)
      let g := g.putStackEntry p newId
      g.logMsg s!"{(g.player p).name} casts {name} as the ability resolves"

/-- Mill opponents, then a reflexive trigger exists only if cards were milled. -/
def millThenReflexive (g : Game) (opponents : Array PlayerId) (n : Nat) : Game × Bool :=
  let before :=
    opponents.foldl (fun acc pid => acc + (g.player pid).graveyard.size) 0
  let g := opponents.foldl (fun acc pid => acc.mill pid n) g
  let after :=
    opponents.foldl (fun acc pid => acc + (g.player pid).graveyard.size) 0
  (g, after > before)

/-- Put +1/+1 and lifelink until end of turn on a creature (Bard the Bowman). -/
def applyBardBowman (g : Game) (targetId : ObjectId) : Game :=
  match g.findObject? targetId with
  | none => g.logMsg "The target is no longer legal"
  | some o =>
    if !o.isOnBattlefield || !o.isCreature then
      g.logMsg "The target is no longer legal"
    else
      let g := g.addPlusOnePlusOneTo o 1
      let o := g.object! o.id
      let g := g.mapObjectStatus o (·.grantUntilEot Keyword.lifelink)
      g.logMsg s!"{o.name} gains lifelink until end of turn"

/-- Counter a spell on the stack. `exile` puts a permanent spell into exile
and may grant a free cast (CR 701.5 / Thranduil's Decree). -/
def counterStackSpell (g : Game) (spellId : ObjectId) (exilePermanent := false)
    (grantFreeCast := false) (controller : PlayerId := ⟨0⟩) : Game :=
  match g.findObject? spellId with
  | none => g.logMsg "The spell is no longer on the stack"
  | some o =>
    if o.zone != .stack then
      g.logMsg s!"{o.name} is no longer on the stack"
    else if o.printed.cantBeCountered || o.uncounterableThisCast then
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
  let fromZone := o.zone
  let (g, newId) := g.move o.id .exile none
  let o := g.object! newId
  let g := g.setObject { o with returnToZone := some fromZone }
  let g :=
    match sourceId.bind g.findObject? with
    | some src =>
      g.setObject { src with linkedExile := src.linkedExile.push newId }
    | none => g
  g.logMsg s!"{name} is exiled until the source leaves the battlefield"

/-- Exile `o` for a leave-the-battlefield trigger (Fiend Hunter). The card
does not return automatically when the source leaves. -/
def exileForLeaveTrigger (g : Game) (sourceId : Option ObjectId) (o : GameObject) :
    Game :=
  let name := o.name
  let (g, newId) := g.move o.id .exile none
  let g :=
    match sourceId.bind g.findObject? with
    | some src =>
      g.setObject { src with leaveTriggerExile := src.leaveTriggerExile.push newId }
    | none => g
  g.logMsg s!"{name} is exiled"

/-- Return one exiled id to the battlefield under its owner. Auras attach
without targeting; if they cannot attach, they remain in exile. -/
def returnExiledId (g : Game) (id : ObjectId) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    if o.zone != .exile then g
    else
      let name := o.name
      let owner := o.owner
      match o.returnToZone with
      | some (.hand p) =>
        let (g, _) := g.move id (.hand p) none
        g.logMsg s!"{name} returns to {(g.player p).name}'s hand"
      | some (.graveyard p) =>
        let (g, _) := g.move id (.graveyard p) none
        g.logMsg s!"{name} returns to {(g.player p).name}'s graveyard"
      | _ =>
        if o.printed.isAura then
          match g.battlefield.find? (fun h => h.isCreature) with
          | none =>
            g.logMsg s!"{name} remains in exile (can't be attached legally; CR 614.6)"
          | some host =>
            let hostId := host.id
            let hostName := host.name
            let (g, newId) := g.move id .battlefield (some owner)
            let o := g.object! newId
            let g := g.setObject { o with attachedTo := some hostId }
            let g := g.logMsg s!"{name} returns attached to {hostName} (does not target)"
            g.afterPermanentEnters (g.object! newId)
        else
          let (g, newId) := g.move id .battlefield (some owner)
          let o := g.object! newId
          let sick := !o.printed.keywords.haste
          let g := g.setObject { o with status := { o.status with summoningSick := sick } }
          let g := g.logMsg s!"{name} returns to the battlefield"
          g.afterPermanentEnters (g.object! newId)

/-- Return cards linked-exiled by `source` (leave-trigger list first, then
until-leaves). -/
def returnLinkedExile (g : Game) (source : GameObject) : Game :=
  (source.leaveTriggerExile ++ source.linkedExile).foldl
    (fun acc id => acc.returnExiledId id) g

/-- Named MSH tokens that carry extra rules text. -/
def zabuToken : CardDef :=
  { (creatureToken "Zabu" #["Cat"] 2 2 (some .green)) with
    supertypes := #[.legendary]
    triggeredAbilities := #[.onLandYouControlEntersPlusOnePlusOne] }

def theVoidToken : CardDef :=
  { (creatureToken "The Void" #["Horror", "Villain"] 5 5 (some .black)
      ((Keyword.flying).merge Keyword.indestructible)) with
    supertypes := #[.legendary]
    oracleText := "Flying, indestructible\nThe Void attacks each combat if able." }

def galactusToken : CardDef :=
  { (creatureToken "Galactus" #["Elder", "Alien"] 16 16 (some .black)
      ((Keyword.flying).merge Keyword.trample)) with
    supertypes := #[.legendary] }

def tigerGodToken : CardDef :=
  { (creatureToken "The Tiger God" #["Cat", "God"] 4 4 (some .green)) with
    supertypes := #[.legendary]
    staticAbilities := #[.cantBeBlockedExceptBy 2] }

def sturdyShieldToken : CardDef :=
  { name := "Sturdy Shield"
    types := #[.artifact]
    subtypes := #["Equipment"]
    staticAbilities := #[.equippedCreatureGets 1 2]
    activatedAbilities := #[
      { cost := { mana := ManaCost.ofGeneric 2 }
        effect := .attachToTargetCreatureYouControl
        onlyAsSorcery := true }]
    isToken := true }

def createNamedToken (g : Game) (controller : PlayerId) (printed : CardDef) : Game :=
  let (g, _) := g.createToken controller printed
  g

def withSourceOnBattlefield (g : Game) (sourceId : Option ObjectId)
    (f : Game → GameObject → Game)
    (missing := "The ability's source is no longer in play") : Game :=
  match sourceId.bind g.findObject? with
  | some o =>
    if o.isOnBattlefield then f g o
    else g.logMsg s!"{o.name} is no longer on the battlefield"
  | none =>
    g.logMsg missing

/-- Exile the top `n` cards of `p`'s library. They may be played this turn. -/
def exileTopPlayThisTurn (g : Game) (p : PlayerId) (n : Nat) : Game :=
  Id.run do
    let mut g := g
    for _ in [0:n] do
      let pl := g.player p
      if pl.library.isEmpty then
        g := g.logMsg s!"{pl.name} has no cards in their library to exile"
      else
        let top := pl.library.back!
        let cardName := (g.object! top).name
        let (g', newId) := g.move top .exile none
        g := g'
        let o := g.object! newId
        g := g.setObject { o with
          playPermission := some { player := p, turnEndsRemaining := 1 } }
        g := g.logMsg s!"{pl.name} exiles {cardName} and may play it this turn"
    return g

/-- Resolve one pending extort trigger. You may pay at most once (MSH 371).
Life gained equals life actually lost (MSH 292). Extort does not target
(MSH 296). -/
def applyExtort (g : Game) (pay : Bool) : Game :=
  match g.pendingExtortController with
  | none => g.logMsg "No extort trigger is pending"
  | some controller =>
    if g.pendingExtort == 0 then
      g.logMsg "No extort trigger is pending"
    else
      let g := { g with
        pendingExtort := g.pendingExtort - 1
        pendingExtortController :=
          if g.pendingExtort - 1 == 0 then none else some controller }
      if !pay then
        g.logMsg "Extort is not paid"
      else
        let (g, lost) :=
          (g.livingOpponents controller).foldl (fun (acc : Game × Nat) pl =>
            let before := (acc.1.player pl.id).life
            let g := acc.1.loseLife pl.id 1
            let after := (g.player pl.id).life
            let delta :=
              if before > after then (before - after).toNat else 0
            (g, acc.2 + delta)) (g, 0)
        g.gainLife controller lost |>.logMsg "Extort is paid"

/-- Queue a reflexive MSH trigger. The first ability has no targets; the
second is chosen after the "if you do" (MSH 359–369). -/
def queueMshReflexive (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (kind : Nat) (paid : Nat := 0) : Game :=
  { g with
      pendingMshReflexive := some (controller, sourceId, kind)
      pendingMshReflexivePaid := paid }
    |>.logMsg "A reflexive triggered ability triggers"

/-- Sacrifice the Plan if it is still on the battlefield. Queue the
reflexive second ability only if the sacrifice happened (MSH 360–362,
368–369). -/
def sacrificePlanThenQueueReflexive (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (kind : Nat) : Game :=
  match sourceId.bind g.findObject? with
  | some o =>
    if o.isOnBattlefield then
      let g := g.sacrificeToGraveyard o "the Plan is completed"
      g.queueMshReflexive controller sourceId kind
    else
      g.logMsg s!"{o.name} is no longer on the battlefield. The reflexive ability doesn't trigger."
  | none =>
    g.logMsg "The Plan is no longer on the battlefield. The reflexive ability doesn't trigger."

/-- Exile the top `n` cards of `fromPlayer`'s library. `caster` may play
them this turn (Doom Reigns Supreme). -/
def exileTopMayCast (g : Game) (fromPlayer caster : PlayerId) (n : Nat) : Game :=
  Id.run do
    let mut g := g
    for _ in [0:n] do
      let pl := g.player fromPlayer
      if pl.library.isEmpty then
        g := g.logMsg s!"{pl.name} has no cards in their library to exile"
      else
        let top := pl.library.back!
        let cardName := (g.object! top).name
        let (g', newId) := g.move top .exile none
        g := g'
        let o := g.object! newId
        g := g.setObject { o with
          playPermission := some { player := caster, turnEndsRemaining := 1 } }
        g := g.logMsg s!"{pl.name} exiles {cardName}; {(g.player caster).name} may cast it"
    return g

/-- Return a graveyard creature tapped and attacking with a finality
counter (Grim Reaper). -/
def returnFromGyTappedAttackingFinality (g : Game) (controller : PlayerId)
    (cardId : ObjectId) (attackingWhom : Option PlayerId := none) : Game :=
  match g.findObject? cardId with
  | none => g.logMsg "The target is no longer in the graveyard"
  | some o =>
    if !(o.printed.isCreature && o.zone == .graveyard controller) then
      g.logMsg "The target is no longer a creature card in your graveyard"
    else
      let whom :=
        match attackingWhom with
        | some pid => some pid
        | none =>
          match (g.livingOpponents controller)[0]? with
          | some pl => some pl.id
          | none => none
      let (g, newId) := g.putOntoBattlefield o.id controller (tapped := true)
      let o := g.object! newId
      let g := g.setObject { o with status := { o.status with
        attacking := true
        attackingWhom := whom } }
      let o := g.object! newId
      let g := g.addFinalityTo o
      let o := g.object! newId
      g.afterPermanentEnters o |>.logMsg s!"{o.name} enters tapped and attacking"

/-- Resolve the pending MSH reflexive trigger with the now-chosen targets.
If every target is illegal, nothing happens (MSH 125). -/
def applyMshReflexive (g : Game) (targets : Array Target := #[])
    (division : Array Nat := #[]) : Game :=
  match g.pendingMshReflexive with
  | none => g.logMsg "No reflexive triggered ability is pending"
  | some (controller, sourceId, kind) =>
    let paid := g.pendingMshReflexivePaid
    let g := { g with pendingMshReflexive := none, pendingMshReflexivePaid := 0 }
    if kind == 0 then
      g.withLegalKindPermanent controller .creatureYouControl targets
        (fun g o =>
          g.mapObjectStatus o (·.grantUntilEot Keyword.indestructible)
            |>.logMsg s!"{o.name} gains indestructible until end of turn")
        sourceId (some "The target is no longer legal")
    else if kind == 1 then
      g.withLegalKindTarget controller .playerOrCreature targets (fun g tgt =>
        match tgt with
        | Target.player pid => g.dealDamageToPlayer pid 2
        | Target.permanent id =>
          match g.findObject? id with
          | some o => g.dealDamageToPermanent o 2
          | none => g
        | _ => g) sourceId (some "The target is no longer legal")
    else if kind == 2 then
      if targets.isEmpty then
        let g := g.draw controller 1
        g.beginDiscardCards #[controller]
      else
        g.withLegalKindTarget controller .playerOrCreature targets (fun g tgt =>
          match tgt with
          | Target.player pid =>
            let _ := paid
            g.dealDamageToPlayer pid 2
          | Target.permanent id =>
            match g.findObject? id with
            | some o =>
              g.mapObjectStatus o (fun s =>
                { s with untilEotKeywords :=
                    Keywords.merge s.untilEotKeywords Keyword.cantBeBlocked })
            | none => g
          | _ => g) sourceId (some "The target is no longer legal")
    else if kind == 3 then
      g.withLegalKindPermanent controller .creatureYouControl targets
        (fun g o =>
          g.mapObjectStatus o (fun s =>
            { s with indestructibleCounters := s.indestructibleCounters + 1 })
            |>.logMsg s!"{o.name} gets an indestructible counter")
        sourceId (some "The target is no longer legal")
    else if kind == 4 then
      g.withLegalKindTarget controller .opponent targets (fun g tgt =>
        match tgt with
        | Target.player pid =>
          let g := g.setPlayerControl controller pid
          { g with controlOnNextTakenTurn := true }
        | _ => g) sourceId (some "The target is no longer legal")
    else if kind == 5 then
      g.withLegalKindTarget controller .opponent targets (fun g tgt =>
        match tgt with
        | Target.player pid => g.exileTopMayCast pid controller 5
        | _ => g) sourceId (some "The target is no longer legal")
    else if kind == 6 then
      match targets[0]? with
      | some (Target.card id) | some (Target.permanent id) =>
        g.returnFromGyTappedAttackingFinality controller id
      | _ => g.logMsg "The target is no longer legal"
    else if kind == 7 then
      g.withLegalKindPermanent controller .oppNonland targets
        (fun g o => g.destroyPermanent o) sourceId (some "The target is no longer legal")
    else if kind == 8 then
      let amt : Int := Int.ofNat paid
      g.withLegalKindTarget controller .playerOrCreature targets (fun g tgt =>
        match tgt with
        | Target.player pid => g.dealDamageToPlayer pid amt
        | Target.permanent id =>
          if sourceId == some id then
            g.logMsg "Red Hulk can't target himself"
          else
            match g.findObject? id with
            | some o => g.dealDamageToPermanent o amt
            | none => g
        | _ => g) sourceId (some "The target is no longer legal")
    else if kind == 9 then
      g.withLegalKindPermanent controller .creature targets
        (fun g o =>
          if g.hasHaste o then
            g.mapObjectStatus o (fun s =>
              { s with cantBeBlockedExceptByHasteUntilEot := true })
              |>.logMsg s!"{o.name} can't be blocked this turn except by creatures with haste"
          else
            g.logMsg s!"{o.name} doesn't have haste")
        sourceId (some "The target is no longer legal")
    else if kind == 10 then
      if targets.isEmpty then
        g.logMsg "No targets were chosen"
      else if targets.size > 2 then
        g.logMsg "Choose one or two targets"
      else
        let amounts :=
          if division.isEmpty then
            if targets.size == 1 then #[7] else #[4, 3]
          else division
        if amounts.size != targets.size then
          g.logMsg "Each target must be assigned a damage amount"
        else if amounts.any (· == 0) then
          g.logMsg "Each target must receive at least 1 damage"
        else if amounts.foldl (· + ·) 0 != 7 then
          g.logMsg "Must assign all 7 damage among the chosen targets"
        else
          Id.run do
            let mut g := g
            for i in [0:targets.size] do
              let tgt := targets[i]!
              let n := amounts[i]!
              g := g.withLegalKindTarget controller .playerOrCreature #[tgt]
                (fun g t => g.dealDamageToTarget t (Int.ofNat n))
                sourceId (some "The target is no longer legal")
            return g
    else if kind == 11 then
      targets.foldl (fun g tgt =>
        match tgt with
        | Target.card id | Target.permanent id =>
          match g.findObject? id with
          | some o =>
            if o.zone == .graveyard controller && o.printed.isInstantOrSorcery then
              g.returnToHand id controller
            else g
          | none => g
        | _ => g) g
    else
      g

/-- Merge subtype names without duplicates. -/
def mergeSubtypes (xs ys : Array String) : Array String :=
  ys.foldl (fun acc y => if acc.any (· == y) then acc else acc.push y) xs

/-- `o` becomes a copy of `src`'s copiable values. The permanent does not
enter or leave the battlefield (MSH 322 / 326 / 329 / 330). Counters,
attachments, and status are unchanged. If `src` is already a copy, `o`
copies whatever `src` copied (MSH 194 / 198 / 199 / 201). -/
def becomeCopyOf (g : Game) (o : GameObject) (src : GameObject)
    (untilEot := false) (untilNextTurn := false)
    (untilSourceLeaves : Option ObjectId := none)
    (exceptName : Option String := none)
    (forceLegendary := false) (notLegendary := false)
    (addCreature := false) (addSubtypes : Array String := #[])
    (setPT : Option (Int × Int) := none)
    (addVigilance := false) : Game :=
  let restore := o.copyRestore.getD o.printed
  let printed0 := src.printed
  let types :=
    if addCreature && !printed0.types.any (· == .creature) then
      printed0.types.push .creature
    else printed0.types
  let supertypes :=
    if notLegendary then printed0.supertypes.filter (· != .legendary)
    else if forceLegendary && !printed0.supertypes.any (· == .legendary) then
      printed0.supertypes.push .legendary
    else printed0.supertypes
  let printed : CardDef :=
    { printed0 with
      name := exceptName.getD printed0.name
      types
      subtypes := mergeSubtypes printed0.subtypes addSubtypes
      supertypes
      power :=
        match setPT with
        | some (p, _) => some p
        | none => printed0.power
      toughness :=
        match setPT with
        | some (_, t) => some t
        | none => printed0.toughness
      keywords :=
        if addVigilance then Keywords.merge printed0.keywords Keyword.vigilance
        else printed0.keywords }
  let g := g.setObject { o with
    printed
    copyRestore := some restore
    copyUntilEot := untilEot
    copyUntilNextTurn := untilNextTurn
    copyUntilSourceLeaves := untilSourceLeaves }
  g.logMsg s!"{restore.name} becomes a copy of {printed0.name}"

/-- Copy an activated or triggered ability on the stack. The copy is not
cast or activated (MSH 34 / 40 / 66) and uses the same source and X
(MSH 47 / 302 / 303). -/
def copyStackAbility (g : Game) (src : GameObject) (controller : PlayerId) : Game :=
  if (g.player controller).lost then
    g.logMsg s!"{src.name} remains in its current zone (CR 800.4b)"
  else
    let (g, copy) := g.allocObject src.printed controller .stack (some controller)
      (abilityEffect := src.abilityEffect)
      (triggeredAbility := src.triggeredAbility)
      (sourceId := src.sourceId)
      (lastKnownPower := src.lastKnownPower)
      (lastKnownToughness := src.lastKnownToughness)
    let g := g.setObject { copy with
      chosenX := src.chosenX
      isCopy := true
      teamworkPaid := src.teamworkPaid }
    let g := g.putStackEntry controller copy.id
    let g :=
      match g.stack.findIdx? (fun e => e.objectId == src.id) with
      | some i =>
        let orig := g.stack[i]!
        let last := g.stack.size - 1
        { g with stack := g.stack.set! last { g.stack[last]! with
          targets := orig.targets
          dividedDamage := orig.dividedDamage
          chosenMode := orig.chosenMode } }
      | none => g
    g.logMsg s!"A copy of {src.name} is created"

/-- Reveal `p`'s hand (Cloak and Dagger; MSH 132 / 225). -/
def revealHand (g : Game) (p : PlayerId) : Game :=
  let names :=
    (g.player p).hand.foldl (fun acc id =>
      match g.findObject? id with
      | some o => if acc == "" then o.name else s!"{acc}, {o.name}"
      | none => acc) ""
  g.logMsg s!"{(g.player p).name} reveals their hand ({names})"

/-- Worlds Within Worlds (MSH 96): exile creatures, put creature cards from
hands onto the battlefield, return the exiled cards to hands, exile the spell. -/
def applyWorldsWithinWorlds (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) : Game :=
  Id.run do
    let mut g := g
    let creatures := g.battlefield.filter (fun o => o.isCreature)
    let mut exiled : Array ObjectId := #[]
    for o in creatures do
      let name := o.name
      let (g', nid) := g.move o.id .exile none
      g := g'
      exiled := exiled.push nid
      g := g.logMsg s!"{name} is exiled"
    let order :=
      let apnap := g.apnapOrder
      if apnap.isEmpty then #[controller]
      else apnap
    for pid in order do
      let ids := (g.player pid).hand
      for id in ids do
        match g.findObject? id with
        | some o =>
          if o.printed.isCreature then
            let (g', _) := g.putOntoBattlefield o.id pid
            g := g'
            g := g.logMsg s!"{(g.player pid).name} puts {o.name} onto the battlefield"
          else g := g
        | none => pure ()
    for nid in exiled do
      match g.findObject? nid with
      | some o =>
        if o.zone == .exile then
          let (g', _) := g.move o.id (.hand o.owner) none
          g := g'.logMsg s!"{o.name} is returned to its owner's hand"
        else pure ()
      | none => pure ()
    match sourceId.bind g.findObject? with
    | some src =>
      let (g', _) := g.move src.id .exile none
      return g'.logMsg s!"{src.name} is exiled"
    | none =>
      return g

/-- Resolve a modeled MSH trigger. Performs the printed effect: tokens, draw,
damage, destroy, attach, exile, or pump. -/
def applyMshTrigger (g : Game) (controller : PlayerId) (t : MshTrigger)
    (sourceId : Option ObjectId) (targets : Array Target := #[])
    (sourceName : String := "This creature")
    (lastKnownPower : Option Int := none) : Game :=
  let text := t.toNotation
  match t with
  | .whenCloakAndDaggerEnter =>
    let opp? :=
      match targets[0]? with
      | some (Target.player pid) => some pid
      | _ =>
        match (g.livingOpponents controller)[0]? with
        | some pl => some pl.id
        | none => none
    match opp? with
    | none => g
    | some opp =>
      let g := g.revealHand opp
      match sourceId.bind g.findObject? with
      | some src =>
        if src.isOnBattlefield then
          match targets[1]? with
          | some (Target.permanent id) =>
            match g.findObject? id with
            | some o =>
              if o.controlledBy opp then
                g.exileUntilSourceLeaves sourceId o
              else
                g.logMsg "The creature is an illegal target. The ability may still resolve."
            | none => g
          | some (Target.card id) =>
            match g.findObject? id with
            | some o =>
              if o.zone == .hand opp && !o.printed.isLand then
                g.exileUntilSourceLeaves sourceId o
              else g
            | none => g
          | _ => g
        else
          g.logMsg "Cloak and Dagger have left the battlefield. Nothing is exiled."
      | none =>
        g.logMsg "Cloak and Dagger have left the battlefield. Nothing is exiled."
  | .whenThisAuraEnters2 =>
    match sourceId.bind g.findObject? with
    | some src =>
      if src.isOnBattlefield then
        match targets[0]? with
        | some (Target.permanent id) =>
          match g.findObject? id with
          | some tgt =>
            let host? := src.attachedTo.bind g.findObject?
            let g := g.exileUntilSourceLeaves sourceId tgt
            match host? with
            | some host =>
              match g.findObject? host.id with
              | some host =>
                g.becomeCopyOf host tgt (untilSourceLeaves := some src.id)
              | none => g
            | none => g
          | none => g.logMsg "The target is no longer legal"
        | _ => g
      else
        g.logMsg "The source has left the battlefield. Nothing is exiled."
    | none =>
      g.logMsg "The source has left the battlefield. Nothing is exiled."
  | .whenThisEnchantmentEnters =>
    match sourceId.bind g.findObject? with
    | some src =>
      if src.isOnBattlefield then
        match targets[0]? with
        | some (Target.permanent id) =>
          match g.findObject? id with
          | some o => g.exileUntilSourceLeaves sourceId o
          | none => g.logMsg "The target is no longer legal"
        | _ => g
      else
        g.logMsg "The source has left the battlefield. Nothing is exiled."
    | none =>
      g.logMsg "The source has left the battlefield. Nothing is exiled."
  | .atTheBeginningOfYourFirstMainPhase =>
    g.withSourceOnBattlefield sourceId (fun g src =>
      match targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some tgt =>
          g.becomeCopyOf src tgt (untilNextTurn := true)
            (exceptName := some "Absorbing Man")
            (forceLegendary := true) (addCreature := true)
            (addSubtypes := #["Human", "Villain"])
            (setPT := some (4, 4)) (addVigilance := true)
        | none => g
      | _ => g) "The source is no longer in play"
  | .photographicReflexesAtTheBeginningOf =>
    g.withSourceOnBattlefield sourceId (fun g src =>
      match targets[0]? with
      | some (Target.permanent id) | some (Target.card id) =>
        match g.findObject? id with
        | some tgt =>
          g.becomeCopyOf src tgt (untilNextTurn := true)
            (exceptName := some "Taskmaster, Mercenary Mimic")
            (forceLegendary := true) (addCreature := true)
            (addSubtypes := #["Human", "Mercenary", "Villain"])
        | none => g
      | _ => g) "The source is no longer in play"
  | .wheneverACreatureYouControlIsDealtDamage =>
    if g.sheHulkDamageUsedThisTurn then
      g.logMsg "The Sensational She-Hulk already dealt damage this turn. The ability has no effect."
    else
      let amt := lastKnownPower.getD 0
      let g :=
        g.withLegalKindTarget controller .playerOrCreature targets (fun g tgt =>
          match tgt with
          | Target.player pid => g.dealDamageToPlayer pid amt
          | Target.permanent id =>
            match g.findObject? id with
            | some o => g.dealDamageToPermanent o amt
            | none => g
          | _ => g) sourceId none
      { g with sheHulkDamageUsedThisTurn := true }
        |>.logMsg "The Sensational She-Hulk deals damage (only once each turn)"
  | .noOneDiesWhenSpiderManEnte =>
    match sourceId.bind g.findObject? with
    | some src =>
      if src.isOnBattlefield && !src.status.tapped then
        let g := g.applyPermanentAction src PermanentAction.tap
        g.queueMshReflexive controller sourceId 0
      else
        g.logMsg "Spider-Man is not tapped this way. The reflexive ability doesn't trigger."
    | none =>
      g.logMsg "Spider-Man is no longer on the battlefield. The reflexive ability doesn't trigger."
  | .whenBullseyeEnters =>
    g.queueMshReflexive controller sourceId 1
  | .trickArrowsWheneverHawkeyeBec =>
    let paid := (lastKnownPower.getD (0 : Int)).toNat
    if paid == 0 then
      g.logMsg "Hawkeye didn't pay. The reflexive ability doesn't trigger."
    else
      g.queueMshReflexive controller sourceId 2 paid
  | .wheneverWhiplashAttacks =>
    let x :=
      match sourceId.bind g.findObject? with
      | some o =>
        if o.isOnBattlefield then g.attachedEquipmentCount o
        else (lastKnownPower.getD (0 : Int)).toNat
      | none => (lastKnownPower.getD (0 : Int)).toNat
    if x == 0 then
      g.logMsg "Whiplash isn't equipped"
    else
      let g := g.forEachOpponent controller (fun g pid => g.loseLife pid x)
      g.gainLife controller x
  | .cyberneticSensesWheneverVivVision =>
    let pw : Int :=
      match sourceId.bind g.findObject? with
      | some o =>
        if o.isOnBattlefield then g.power o
        else lastKnownPower.getD (g.power o)
      | none => lastKnownPower.getD (0 : Int)
    if pw >= 4 then g.draw controller 1
    else g.logMsg "Viv Vision's power is not 4 or greater"
  | .atTheBeginningOfCombatOnYourTurn =>
    let x : Int :=
      match sourceId.bind g.findObject? with
      | some o =>
        if o.isOnBattlefield then g.power o
        else lastKnownPower.getD (g.power o)
      | none => lastKnownPower.getD (0 : Int)
    g.withLegalKindPermanent controller .creatureYouControl targets
      (fun g o => g.pumpPermanent o x 0) sourceId none
  | .wheneverAnotherCreatureYouControlEnters =>
    g.withSourceOnBattlefield sourceId (fun g hulkling =>
      let entered :=
        match targets[0]? with
        | some (Target.permanent id) => g.findObject? id
        | _ =>
          let cands := (g.permanentsOf controller).filter (fun (x : GameObject) =>
            x.isCreature && x.id != hulkling.id && x.status.enteredThisTurn)
          if cands.isEmpty then none
          else some (cands.foldl (fun (acc : GameObject) (x : GameObject) =>
            if x.timestamp > acc.timestamp then x else acc) cands[0]!)
      match entered with
      | none => g
      | some other =>
        let op := if other.isOnBattlefield then g.power other
          else other.lastKnownPower.getD (g.power other)
        let ot := if other.isOnBattlefield then g.toughness other
          else other.lastKnownToughness.getD (g.toughness other)
        if op > g.power hulkling || ot > g.toughness hulkling then
          g.addPlusOnePlusOneTo hulkling 1
        else g) "The source is no longer in play"
  | .wheneverACreatureYouControlBecomesTappedD =>
    match g.lastBecameTapped.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield && o.status.tapped then
        g.applyPermanentAction o .untap
      else g
    | none => g
  | .whenSpiderWomanEnters =>
    g.withLegalKindPermanent controller .oppCreature targets
      (fun g o =>
        let g := g.applyPermanentAction o .tap
        let o := g.object! o.id
        let sid := sourceId.getD ⟨0⟩
        g.mapObjectStatus o (fun s =>
          { s with cantUntapGrantedBy := s.cantUntapGrantedBy.push sid }))
      sourceId (some "The target is no longer legal")
  | .whenDoctorDoomEnters =>
    g.createKindTokens controller .doombot 2
  | .whenKaZarEnters =>
    g.createNamedToken controller zabuToken
  | .enrageWheneverTheIncredi =>
    let g :=
      g.withSourceOnBattlefield sourceId (fun g o =>
        let g := g.addPlusOnePlusOneTo o 1
        if o.status.attacking then
          g.applyPermanentAction o .untap
        else g) "The source is no longer in play"
    if g.enrageGrantsAdditionalCombat > 0 then
      { g with
          enrageGrantsAdditionalCombat := g.enrageGrantsAdditionalCombat - 1
          additionalCombatPhases := g.additionalCombatPhases + 1 }
        |>.logMsg "There is an additional combat phase after this phase"
    else g
  | .enrageWheneverRedHulkIs =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield then
        let g := g.addPlusOnePlusOneTo o 1
        let o := g.object! o.id
        g.queueMshReflexive controller sourceId 8 o.status.plusOnePlusOne
      else
        g.logMsg "Red Hulk is no longer on the battlefield. The reflexive ability doesn't trigger."
    | none =>
      g.logMsg "Red Hulk is no longer on the battlefield. The reflexive ability doesn't trigger."
  | .whenKillmongerEnters =>
    let others :=
      (g.permanentsOf controller).filter (fun o =>
        o.isCreature && some o.id != sourceId)
    match others[0]? with
    | none =>
      g.logMsg "No other creature was sacrificed. The reflexive ability doesn't trigger."
    | some victim =>
      let g := g.sacrificeToGraveyard victim "Killmonger"
      g.queueMshReflexive controller sourceId 7
  | .wheneverGrimReaperAttacks =>
    let paid := (lastKnownPower.getD (0 : Int)).toNat
    if paid == 0 then
      g.logMsg "Grim Reaper's cost wasn't paid. The reflexive ability doesn't trigger."
    else
      g.queueMshReflexive controller sourceId 6
  | .wheneverYouCastANoncreatureSpell5 =>
    let paid := (lastKnownPower.getD (0 : Int)).toNat
    if paid == 0 then
      g.logMsg "Speed's cost wasn't paid. The reflexive ability doesn't trigger."
    else
      g.queueMshReflexive controller sourceId 9
  | .wheneverAPlayerCastsASpellThatTargetsSpe =>
    g.withSourceOnBattlefield sourceId (fun g o => g.pumpPermanent o 2 2)
      "Speedball is no longer on the battlefield"
  | .wheneverYouAttack2 =>
    -- Daredevil: exile the top card. Hero-ness only affects the pump;
    -- the card may be played this turn either way (MSH 333).
    let pl := g.player controller
    if pl.library.isEmpty then
      g.logMsg s!"{pl.name} has no cards in their library to exile"
    else
      let top := pl.library.back!
      let card := g.object! top
      let isHero := card.hasSubtype "Hero"
      let (g, newId) := g.move top .exile none
      let o := g.object! newId
      let g := g.setObject { o with
        playPermission := some { player := controller, turnEndsRemaining := 1 } }
      let g := g.logMsg s!"{pl.name} exiles {card.name} and may play it this turn"
      if isHero then
        g.withSourceOnBattlefield sourceId (fun g src => g.pumpPermanent src 2 1)
          "Daredevil is no longer on the battlefield"
      else g
  | .wheneverYouAttack3 =>
    let paid := (lastKnownPower.getD (0 : Int)).toNat
    if paid == 0 then
      g.logMsg "The Kingpin's cost wasn't paid"
    else
      { g with assignCombatDamageEqualToughness := some controller }
        |>.logMsg "Creatures you control assign combat damage equal to their toughness"
  | .wheneverAnotherVillainYouControlEnters3 =>
    g.withSourceOnBattlefield sourceId (fun g o =>
      let g := g.addPlusOnePlusOneTo o 1
      g.forEachOpponent controller (fun g pid =>
        g.dealDamageToPlayer pid 2 (source := some (g.object! o.id))))
      "Crossbones is no longer on the battlefield"
  | .wheneverAnAttackingCreatureYouControlDies =>
    match g.lastDiedAttacker.bind g.findObject? with
    | none => g.logMsg "The attacking creature is no longer in the graveyard"
    | some o =>
      if o.printed.isToken then
        g.logMsg s!"{o.name} ceases to exist"
      else
        g.returnToHand o.id o.owner
  | .whenTheSentryEnters =>
    match targets[0]? with
    | some (Target.player pid) => g.createNamedToken pid theVoidToken
    | _ => g.createNamedToken controller theVoidToken
  | .whenUSAgentEnters =>
    let (g, shield) := g.createToken controller sturdyShieldToken
    match sourceId.bind g.findObject? with
    | some src => g.attachSourceTo (g.object! shield.id) src
    | none => g
  | .whenElektraEnters =>
    g.withLegalKindPermanent controller .oppCreature targets
      (fun g o => g.destroyPermanent o) sourceId (some "The target is no longer legal")
  | .whenRedGuardianEnters =>
    g.withLegalKindPermanent controller .oppCreature targets
      (fun g o =>
        if o.status.dealtDamageThisTurn then
          g.destroyPermanent o
        else
          g.logMsg s!"{o.name} didn't deal damage this turn")
      sourceId (some "The target is no longer legal")
  | .whenMjLnirEnters =>
    g.withLegalKindPermanent controller .creature targets
      (fun g o => g.dealDamageToPermanent o 4) sourceId none
  | .whenThisEquipmentEnters | .whenThisEquipmentEnters2 =>
    g.withLegalKindPermanent controller .creatureYouControl targets
      (fun g host =>
        g.withSourceOnBattlefield sourceId (fun g src =>
          let g := g.attachSourceTo src host
          match t with
          | .whenThisEquipmentEnters =>
            g.mapObjectStatus (g.object! host.id) (·.grantUntilEot Keyword.indestructible)
          | .whenThisEquipmentEnters2 =>
            g.applyPermanentAction (g.object! host.id) .untap
          | _ => g) "The Equipment is no longer in play")
      sourceId (some "The target is no longer legal")
  | .waspSStingWhenTheWondrousWa =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some tgt =>
        if !tgt.isOnBattlefield then g
        else
          let g := g.applyPermanentAction tgt .tap
          match sourceId.bind g.findObject? with
          | some src =>
            if src.isOnBattlefield then
              let tgt := g.object! id
              g.mapObjectStatus tgt (fun s =>
                { s with losesAbilitiesGrantedBy :=
                  s.losesAbilitiesGrantedBy.push src.id })
            else
              g.logMsg s!"The Wondrous Wasp has left. {tgt.name} is tapped but keeps its abilities."
          | none =>
            g.logMsg s!"The Wondrous Wasp has left. {tgt.name} is tapped but keeps its abilities."
      | none => g
    | _ => g
  | .whenThisCreatureEnters4 =>
    let g := g.draw controller 1
    let land? :=
      (g.player controller).hand.filterMap (fun id => g.findObject? id) |>.find?
        (fun o => o.printed.isLand)
    match land? with
    | none => g
    | some land =>
      let (g, newId) := g.putOntoBattlefield land.id controller
        (tapped := true) (summoningSick := false)
      g.afterLandEnters (g.object! newId)
  | .wheneverAnotherNontokenArtifactYouControlE =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some src =>
        if src.isOnBattlefield && src.printed.isArtifact && !src.printed.isToken then
          let (g, tok) := g.copyBattlefieldPermanent src controller
          let tok := g.object! tok.id
          let g := g.afterPermanentEnters tok
          let tok := g.object! tok.id
          if tok.isCreature then g
          else
            let printed :=
              { tok.printed with
                types :=
                  if tok.printed.types.any (· == .creature) then tok.printed.types
                  else tok.printed.types.push .creature
                subtypes := mergeSubtypes tok.printed.subtypes #["Robot", "Villain"]
                power := some 2
                toughness := some 2 }
            g.setObject { tok with printed }
              |>.logMsg s!"{printed.name} becomes a 2/2 Robot Villain creature after it enters"
        else g
      | none => g
    | _ => g
  | .wheneverAVillainYouControlDies =>
    match targets[0]? with
    | some (Target.card id) | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        if o.zone == .graveyard o.owner && g.hasSubtype o "Villain" then
          let owner := o.owner
          let (g, newId) := g.putOntoBattlefield id owner
          let o := g.object! newId
          let subtypes :=
            if o.printed.subtypes.any (· == "Hero") then o.printed.subtypes
            else o.printed.subtypes.push "Hero"
          let g := g.setObject { o with
            printed := { o.printed with subtypes }
            status := { o.status with finality := o.status.finality + 1 } }
          g.afterPermanentEnters (g.object! newId)
        else g
      | none => g
    | _ => g
  | .whenThisAuraEnters3 =>
    g.withSourceOnBattlefield sourceId (fun g src =>
      match src.attachedTo.bind g.findObject? with
      | some host => g.applyPermanentAction host .tap
      | none => g) "The Aura is no longer in play"
  | .whenThisAuraEnters =>
    g.withSourceOnBattlefield sourceId (fun g src =>
      match src.attachedTo.bind g.findObject? with
      | some host =>
        g.mapObjectStatus host (·.grantUntilEot Keyword.firstStrike)
      | none => g) "The Aura is no longer in play"
  | .whenThisLandEnters =>
    g.beginScry controller 1
  | .whenThisCreatureEnters8 =>
    g.beginScry controller 2
  | .whenThisCreatureEnters5 =>
    let g := g.draw controller 1
    if (g.permanentsOf controller).any (fun o =>
        g.hasSubtype o "Hero" && some o.id != sourceId) then
      g.gainLife controller 2
    else g
  | .whenThisCreatureEnters6 =>
    g.resolveExileTopPlayUntilEndOfNextTurn controller
  | .whenThisCreatureEnters2 =>
    g.createKindTokens controller .food 1
  | .whenThisCreatureEnters3 =>
    let gy := (g.player controller).graveyard.filter (fun id =>
      (g.object! id).printed.isCreature) |>.size
    if gy >= 2 then
      g.createKindTokens controller .villain21menace 1 (tapped := true)
    else
      g.mill controller 2
  | .whenThisEnchantmentEnters2 =>
    g.withLegalKindTarget controller .opponent targets (fun g tgt =>
      match tgt with
      | Target.player pid =>
        let g := g.beginDiscardCards #[pid]
        g.beginDiscardCards #[pid]
      | _ => g) sourceId none
  | .wheneverKangAttacks =>
    let g := g.draw controller 1
    g.beginDiscardCards #[controller]
  | .wheneverYouCastAVillainSpell =>
    g.createKindTokens controller .villain21menace 1
  | .doYouLikeSquirrelsWheneverTheUnbeata =>
    g.createKindTokens controller .squirrel11green 1
  | .wheneverYouPutA11CounterOnACreature =>
    g.createKindTokens controller .insect11green 1
  | .wheneverYouPutOneOrMore11CountersOnO =>
    g.createKindTokens controller .wall04defender 1
  | .wheneverYouDrawYourSecondCardEachTurn3 =>
    g.withSourceOnBattlefield sourceId (fun g o =>
      g.mapObjectStatus o (fun s =>
        { s with
          setBasePT := some (6, 6)
          untilEotKeywords := Keywords.merge s.untilEotKeywords Keyword.trample })
        |>.logMsg s!"{o.name}'s base power and toughness become 6/6")
      "The source is no longer in play"
  | .wheneverYouCastANoncreatureSpell2 =>
    match sourceId.bind g.findObject? with
    | some src =>
      if src.status.chosenModes.size >= 3 then
        g.logMsg "The Vision's ability is removed from the stack with no effect"
      else
        let mode := (lastKnownPower.getD 0).toNat
        let g := g.mapObjectStatus src (fun s =>
          { s with chosenModes := s.chosenModes.push mode })
        if mode == 0 then
          g.mapObjectStatus (g.object! src.id)
            (·.grantUntilEot Keyword.doubleStrike)
        else if mode == 1 then
          g.mapObjectStatus (g.object! src.id)
            (·.grantUntilEot Keyword.indestructible)
        else
          g.draw controller 1
    | none => g.logMsg "The Vision is no longer in play"
  | .wheneverYouCastASpellThatTargetsACreatur =>
    g.withSourceOnBattlefield sourceId (fun g o =>
      g.mapObjectStatus o (fun s =>
        { s with ironFistTapGrants := s.ironFistTapGrants + 1 })
        |>.logMsg s!"{o.name} gains a tap ability until end of turn")
      "The source is no longer in play"
  | .wheneverYouCastASpellThatTargetsACreatur4 =>
    let g := g.draw controller 1
    g.withSourceOnBattlefield sourceId (fun g o =>
      g.mapObjectStatus o (fun s =>
        { s with grantedStaticAbilities :=
            s.grantedStaticAbilities.push .powerEqualCardsInHand })
        |>.logMsg s!"{o.name}'s base power is the number of cards in your hand")
      "The source is no longer in play"
  | .atTheBeginningOfYourUpkeep =>
    let mode := (lastKnownPower.getD 0).toNat
    if mode == 0 then
      g.withSourceOnBattlefield sourceId (fun g o =>
        g.addPlusOnePlusOneTo o 1) "The source is no longer in play"
    else
      match targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some o =>
          if o.isOnBattlefield && o.controlledBy controller &&
              o.status.plusOnePlusOne > 0 then
            let g := g.mapObjectStatus o (fun s =>
              { s with plusOnePlusOne := s.plusOnePlusOne - 1 })
            g.draw controller 1
          else
            g.logMsg "You must remove a counter from a creature you control if you can"
        | none =>
          g.logMsg "You must remove a counter from a creature you control if you can"
      | _ =>
        if (g.permanentsOf controller).any (fun o =>
            o.isCreature && o.status.plusOnePlusOne > 0) then
          g.logMsg "You must remove a counter from a creature you control if you can"
        else g
  | .wheneverYouDrawACard =>
    if (g.permanentsOf controller).any (fun o =>
        g.hasSubtype o "Hero" && some o.id != sourceId) then
      g.withLegalKindTarget controller .opponent targets (fun g tgt =>
        match tgt with
        | Target.player pid => g.dealDamageToPlayer pid 1
        | _ => g) sourceId none
    else
      g.logMsg "Human Torch's ability has no effect"
  | .atTheBeginningOfYourEndStep =>
    let n := 10 - (g.player controller).hand.size
    if n > 0 then g.draw controller n
    else g.logMsg "You already have ten or more cards in hand"
  | .atTheBeginningOf =>
    match sourceId.bind g.findObject? with
    | some src =>
      if !src.status.harnessed then
        g.logMsg "The Mind Stone is not harnessed"
      else
        match targets[0]? with
        | some (Target.permanent id) =>
          match g.findObject? id with
          | some o =>
            if o.isOnBattlefield && o.id != src.id then
              let (g, newId) :=
                let g := g.exileUntilSourceLeaves sourceId o
                match g.objects.find? (fun x =>
                  x.name == o.name && x.zone == .exile) with
                | some ex => (g, ex.id)
                | none => (g, id)
              g.returnExiledId newId
            else g
          | none => g.logMsg "The target is no longer legal"
        | _ => g
    | none => g
  | .wheneverEnchantedCreatureAttacksOrBlocks =>
    match sourceId.bind g.findObject? with
    | some src =>
      match src.attachedTo.bind g.findObject? with
      | none =>
        g.logMsg "The enchanted creature has left. Equipment stays where it is."
      | some host =>
        targets.foldl (fun (g : Game) (t : Target) =>
          match t with
          | Target.permanent id =>
            match g.findObject? id with
            | some eq =>
              if eq.isOnBattlefield && eq.printed.isEquipment then
                g.attachSourceTo eq host
              else g
            | none => g
          | _ => g) g
    | none =>
      g.logMsg "The enchanted creature has left. Equipment stays where it is."
  | .wheneverAnotherVillainYouControlEnters2 =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent eqId), some (Target.permanent crId) =>
      match g.findObject? eqId, g.findObject? crId with
      | some eq, some cr =>
        if eq.isOnBattlefield && cr.isOnBattlefield && eq.printed.isEquipment then
          g.attachSourceTo eq cr
        else
          g.logMsg "The Equipment won't move"
      | _, _ => g.logMsg "The Equipment won't move"
    | _, _ => g.logMsg "The Equipment won't move"
  | .wheneverIronManAttacks =>
    if (g.player controller).artifactEnteredThisTurn then
      g.draw controller 1
    else
      g.logMsg "No artifact entered under your control this turn. Iron Man's ability doesn't trigger."
  | .sonicAttackWhenKlawEntersTa =>
    match targets[0]? with
    | some (Target.player pid) =>
      let n :=
        1 + ((g.player controller).graveyard.filter (fun id =>
          match g.findObject? id with
          | some o => o.printed.isCreature
          | none => false)).size
      let hand :=
        (g.player pid).hand.filterMap (fun id => g.findObject? id)
      let shown := if hand.size ≤ n then hand else hand.take n
      let g := g.revealHand pid
      g.logMsg
        s!"{(g.player pid).name} reveals {shown.size} card(s) (all, if fewer than {n})"
    | _ => g
  | .wheneverYouAttack =>
    let top :=
      (g.player controller).library.reverse.toList.take 6
    let ids := top.toArray
    match ids[0]? with
    | none => g.logMsg "No cards to look at"
    | some id =>
      g.castAsPartOfResolution controller id
        |>.logMsg "You may cast a spell from among the top six as this ability resolves"
  | .whenTheRuinousWreckingCrewEnters =>
    let modes :=
      match sourceId.bind g.findObject? with
      | some o => o.status.chosenModes
      | none => #[]
    Id.run do
      let mut g := g
      for m in modes do
        if m == 0 then
          g := g.draw controller 1
          g := g.beginDiscardCards #[controller]
        else if m == 1 then
          g := g.forEachOpponent controller (fun g pid => g.loseLife pid 2)
        else if m == 2 then
          match targets[0]? with
          | some (Target.permanent id) =>
            match g.findObject? id with
            | some o =>
              if o.isOnBattlefield && o.printed.isToken then
                g := g.destroyPermanent o
            | none => pure ()
          | _ => pure ()
        else if m == 3 then
          match targets[1]? with
          | some (Target.permanent id) =>
            match g.findObject? id with
            | some o =>
              if o.isOnBattlefield then
                g := (g.move id (.graveyard o.owner) none).1
                  |>.logMsg s!"{o.name} is sacrificed"
              else
                g := g.logMsg "The token was already destroyed and can't be sacrificed"
            | none =>
              g := g.logMsg "The token was already destroyed and can't be sacrificed"
          | _ =>
            g := g.logMsg "The token was already destroyed and can't be sacrificed"
      return g
  | _ =>
    if text.contains "create two 1/1 white Soldier" ||
        text.contains "create a 1/1 white Soldier" then
      g.createKindTokens controller .soldier11white
        (if text.contains "two" then 2 else 1)
    else if text.contains "Doombot" then
      g.createKindTokens controller .doombot 2
    else if text.contains "draw a card" && text.contains "lose 1 life" then
      let g := g.draw controller 1
      g.loseLife controller 1
    else if text.contains "draw a card" || text.contains "you draw" ||
        text.contains "draw cards" then
      g.draw controller 1
    else if text.contains "connive" then
      g.applyConnive controller sourceId
    else if text.contains "surveil" || text.contains "Scry" || text.contains "scry" then
      g.beginScry controller 1
    else if text.contains "destroy target" then
      g.withLegalKindPermanent controller .oppCreature targets
        (fun g o => g.destroyPermanent o) sourceId none
    else if text.contains "exile" && text.contains "leaves" then
      match sourceId.bind g.findObject? with
      | some src =>
        if src.isOnBattlefield then
          g.withLegalKindPermanent controller .oppNonland targets
            (fun g o => g.exileUntilSourceLeaves sourceId o) sourceId none
        else
          g.logMsg "The source has left the battlefield. Nothing is exiled."
      | none =>
        g.logMsg "The source has left the battlefield. Nothing is exiled."
    else if text.contains "+1/+1 counter" then
      match targets[0]? with
      | some (Target.permanent id) => g.addPlusOnePlusOneTo (g.object! id) 1
      | _ =>
        g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 1)
          "The source is no longer in play"
    else if text.contains "each opponent loses" then
      g.forEachOpponent controller (fun g pid => g.loseLife pid 1)
    else if text.contains "deals" && text.contains "damage" then
      g.withLegalKindTarget controller .playerOrCreature targets (fun g tgt =>
        match tgt with
        | Target.player pid => g.dealDamageToPlayer pid 1
        | Target.permanent id => g.dealDamageToPermanent (g.object! id) 1
        | _ => g) sourceId none
    else if text.contains "fights" then
      match sourceId, targets[0]? with
      | some sid, some (Target.permanent id) =>
        let src := g.object! sid
        g.dealDamageFrom src.name (g.object! id) (g.power src).toNat
      | _, _ => g
    else if text.contains "attach" then
      g.withLegalKindPermanent controller .creatureYouControl targets
        (fun g host =>
          g.withSourceOnBattlefield sourceId (fun g src => g.attachSourceTo src host)
            "The Equipment is no longer in play") sourceId none
    else
      g.withSourceOnBattlefield sourceId (fun g _ => g)
        s!"{sourceName} resolves"

/-- Resolve a modeled MSH spell. -/
def applyMshSpell (g : Game) (controller : PlayerId) (t : MshSpell)
    (targets : Array Target) (sourceId : Option ObjectId := none)
    (putOnBottom := false) : Game :=
  match t with
  | .thisSpellCosts2LessToCastIfItTargets =>
    g.withLegalKindPermanent controller .creature targets (fun g o =>
      let g := g.pumpPermanent o (-4) 0
      g.draw controller 1)
      sourceId (some "The target is no longer legal. You won't draw a card.")
  | .targetCreatureGets31UntilEndOfTurn =>
    g.withLegalKindPermanent controller .creature targets (fun g o =>
      let g := g.pumpPermanent o 3 1
      g.exileTopPlayThisTurn controller 1)
      sourceId (some "The target is no longer legal. No card will be exiled.")
  | .targetCreatureYouControlThatSAttackingAlo =>
    g.withLegalKindPermanent controller .creatureYouControl targets (fun g o =>
      let g := g.pumpPermanent o 1 0
      g.gainLife controller 1)
      sourceId (some "The target is no longer legal. You won't gain life.")
  | .targetArtifactYouControlBecomesACopyOfA =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent a), some (Target.permanent b) =>
      match g.findObject? a, g.findObject? b with
      | some dest, some src =>
        if dest.isOnBattlefield && src.isOnBattlefield &&
            dest.controlledBy controller && src.controlledBy controller &&
            dest.printed.isArtifact && src.printed.isArtifact then
          g.becomeCopyOf dest src (untilEot := true) (notLegendary := true)
        else
          g.logMsg "The target is no longer legal. The ability has no effect."
      | _, _ =>
        g.logMsg "The target is no longer legal. The ability has no effect."
    | _, _ =>
      g.logMsg "The target is no longer legal. The ability has no effect."
  | .whenYouNextCastAnInstantOrSorcerySpellW =>
    let pw :=
      match sourceId.bind g.findObject? with
      | some o =>
        if o.isOnBattlefield then g.power o else o.power
      | none => (0 : Int)
    { g with pendingLokiCopy := some (controller, sourceId, pw) }
      |>.logMsg s!"The next instant or sorcery with mana value {pw} or less will be copied"
  | .copyTargetActivatedOrTriggeredAbilityYouC =>
    match targets[0]? with
    | some (Target.card id) | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        if o.zone == .stack then g.copyStackAbility o controller
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    | _ => g
  | .exileAllCreaturesEachPlayerMayPutAnyNum =>
    g.applyWorldsWithinWorlds controller sourceId
  | .createX11GreenSquirrelCreatureTokensWhe =>
    let n :=
      (g.permanentsOf controller).filter (fun o => g.hasSubtype o "Squirrel") |>.size
    g.createKindTokens controller .squirrel11green n
  | .ifThisEquipmentIsnTACreatureItBecomesA =>
    match sourceId.bind g.findObject? with
    | some o =>
      if !o.isOnBattlefield then
        g.logMsg "The Equipment is no longer in play"
      else if o.isCreature then
        g.logMsg s!"{o.name} is already a creature"
      else
        let wasAttached := o.attachedTo.isSome
        let g :=
          if wasAttached then
            g.setObject { o with attachedTo := none }
              |>.logMsg s!"{o.name} becomes unattached"
          else g
        let o := g.object! o.id
        let g := g.mapObjectStatus o (fun s =>
          { s with
            setBasePT := some (0, 0)
            additionalCreatureUntilEot := true
            additionalArtifactUntilEot := true
            untilEotKeywords := Keywords.merge s.untilEotKeywords Keyword.flying
            replacedCreatureTypesUntilEot := some #["Construct", "Hero"]
            pumpPerArtifactUntilEot := true })
        g.logMsg s!"{o.name} becomes a 0/0 Construct Hero artifact creature"
    | none => g.logMsg "The Equipment is no longer in play"
  | .untilEndOfTurnReptilBecomesADinosaurHer =>
    g.withSourceOnBattlefield sourceId (fun g o =>
      g.mapObjectStatus o (fun s =>
        { s with
          setBasePT := some (3, 5)
          replacedCreatureTypesUntilEot := some #["Dinosaur", "Hero"]
          untilEotKeywords :=
            Keywords.merge (Keywords.merge s.untilEotKeywords Keyword.reach)
              Keyword.vigilance })
        |>.logMsg s!"{o.name} becomes a 3/5 Dinosaur Hero with reach and vigilance")
      "The source is no longer in play"
  | .theNextRedOrGreenCreatureSpellYouCastTh =>
    { g with pendingFreeRGCreature := some controller }
      |>.logMsg "The next red or green creature spell you cast this turn can be cast without paying its mana cost"
  | .drawACardActivateOnlyIfYouControlACrea =>
    g.draw controller 1
  | .createATapped21BlackVillainCreatureToken =>
    g.createKindTokens controller .villain21menace 1 (tapped := true)
  | .theOwnerOfTargetCreatureAnOpponentControl =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield then
          let owner := o.owner
          if putOnBottom then
            let (g, _) := g.move id (.library owner) none
            g.logMsg s!"{o.name} is put on the bottom of {(g.player owner).name}'s library"
          else
            let (g, newId) := g.move id (.library owner) none
            let pl := g.player owner
            let lib := pl.library
            let without := lib.filter (· != newId)
            let lib :=
              match without.back? with
              | none => #[newId]
              | some top => without.pop.push newId |>.push top
            g.setPlayer { pl with library := lib }
              |>.logMsg s!"{o.name} is put second from the top of {(g.player owner).name}'s library"
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | _ =>
  let text := t.toNotation
  if text.contains "finality" then
    match sourceId.bind g.findObject? with
    | some o =>
      if o.zone == .graveyard o.owner then
        let (g, newId) := g.putOntoBattlefield o.id controller
        let g := g.logMsg s!"{o.name} returns to the battlefield"
        g.addFinalityTo (g.object! newId) 1
      else g
    | none => g
  else if text.contains "connive" then
    match targets[0]? with
    | some (Target.permanent id) => g.applyConnive controller (some id)
    | _ => g.applyConnive controller none
  else if text.contains "Galactus" then
    g.createNamedToken controller galactusToken
  else if text.contains "Tiger God" then
    let g :=
      match targets[0]? with
      | some (Target.permanent id) => g.addPlusOnePlusOneTo (g.object! id) 1
      | _ => g
    g.createNamedToken controller tigerGodToken
  else if text.contains "Squirrel" then
    let n := (g.permanentsOf controller).filter (fun o => g.hasSubtype o "Squirrel") |>.size
    g.createKindTokens controller .squirrel11green (if n == 0 then 1 else n)
  else if text.contains "Treasure token for each Villain" then
    let n := (g.permanentsOf controller).filter (fun o => g.hasSubtype o "Villain") |>.size
    g.createKindTokens controller .treasure n
  else if text.contains "two 2/1 black Villain" then
    g.createKindTokens controller .villain21menace 2
  else if text.contains "2/1 black Villain" && text.contains "+1/+0" then
    let g := g.createKindTokens controller .villain21menace 1
    g.pumpControlledCreatures controller 1 0
  else if text.contains "Treasure token" then
    g.createKindTokens controller .treasure 1
  else if text.contains "0/4 colorless Wall" then
    g.createKindTokens controller .wall04defender 1
  else if text.contains "each opponent loses" then
    g.forEachOpponent controller (fun g pid => g.loseLife pid 2)
  else if text.contains "fights" then
    match targets[0]?, targets[1]? with
    | some (Target.permanent a), some (Target.permanent b) =>
      let src := g.object! a
      g.dealDamageFrom src.name (g.object! b) (g.power src).toNat
    | _, _ => g
  else if text.contains "draw" && text.contains "lose" then
    let g := g.draw controller 2
    g.loseLife controller 2
  else if text.contains "Draw" || text.contains "draw" then
    g.draw controller 1
  else if text.contains "deals" && text.contains "damage" then
    g.withLegalKindTarget controller .playerOrCreature targets (fun g tgt =>
      match tgt with
      | Target.player pid => g.dealDamageToPlayer pid 4
      | Target.permanent id => g.dealDamageToPermanent (g.object! id) 4
      | _ => g)
  else if text.contains "+1/+1 counter on each" then
    g.forEachControlledCreature controller (fun g o => g.addPlusOnePlusOneTo o 1)
  else if text.contains "+1/+1" then
    match targets[0]? with
    | some (Target.permanent id) => g.addPlusOnePlusOneTo (g.object! id) 1
    | _ => g
  else if text.startsWith "Add " || text.startsWith "Add" then
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .white) })
  else
    g

/-- Resolve a modeled MSH activation. -/
def applyMshAbility (g : Game) (controller : PlayerId) (t : MshAbility)
    (targets : Array Target) (sourceId : Option ObjectId)
    (lastKnownPower : Option Int := none) : Game :=
  if t == .n2TDiscardACard then
    g.draw controller (g.player controller).cardsDiscardedThisTurn
  else if t == .tyrannosaurusRex6UntilEndOfTu then
    g.withSourceOnBattlefield sourceId (fun g o =>
      g.mapObjectStatus o (fun s =>
        { s with
          setBasePT := some (6, 6)
          replacedCreatureTypesUntilEot := some #["Dinosaur", "Hero"]
          untilEotKeywords := Keywords.merge s.untilEotKeywords Keyword.trample })
        |>.logMsg s!"{o.name} becomes a 6/6 Dinosaur Hero with trample")
      "The source is no longer in play"
  else if t == .tPutAStunCounterOnJessicaJones then
    let x :=
      match sourceId.bind g.findObject? with
      | some o =>
        if o.isOnBattlefield then (g.power o).toNat
        else (lastKnownPower.getD (g.power o)).toNat
      | none => (lastKnownPower.getD (0 : Int)).toNat
    g.exileTopPlayThisTurn controller x
  else
  let text := t.toNotation
  if t == .harnessTheMindStone then
    g.withSourceOnBattlefield sourceId (fun g o =>
      let g := g.mapObjectStatus o (fun s => { s with harnessed := true })
      g.logMsg s!"{o.name} is harnessed") "The source is no longer in play"
  else if text.contains "connive" then
    g.applyConnive controller sourceId
  else if text.contains "draws four" || text.contains "Draw four" then
    g.draw controller 4
  else if text.contains "Draw two cards" || text.contains "Draw a card" then
    g.draw controller (if text.contains "two" then 2 else 1)
  else if text.contains "Add " && text.contains "Hero" then
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool :=
        pl.manaPool.add (.colored .white) 1 (heroRestricted := true) })
  else if text.contains "Add " && text.contains "Villain" then
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool :=
        pl.manaPool.add (.colored .black) 1 (villainRestricted := true) })
  else if text.contains "can't be spent to cast a nonartifact" ||
      text.contains "This mana can't be spent to cast a Nona" then
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool :=
        pl.manaPool.add (.colored .blue) 1 (cantNonartifact := true) })
  else if text.contains "Add X mana" then
    let x :=
      match sourceId.bind g.findObject? with
      | some o => (g.power o).toNat
      | none => 0
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .green) x })
  else if text.contains "Add " then
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .white) })
  else if text.contains "Tiger God" then
    g.createNamedToken controller tigerGodToken
  else if text.contains "Hero creature token" || text.contains "create the Hero" then
    g.createKindTokens controller .soldier11white 1
  else if text.contains "Robot Villain" then
    g.createKindTokens controller .villain21menace 1
  else if text.contains "each opponent" && text.contains "discard" then
    g.beginDiscardCards ((g.livingOpponents controller).map (·.id))
  else if text.contains "Doombot" then
    g.createKindTokens controller .doombot 1
  else if text.contains "Insect" then
    g.createKindTokens controller .insect11green 1
  else if text.contains "deals" && text.contains "damage" then
    g.withLegalKindTarget controller .playerOrCreature targets (fun g tgt =>
      match tgt with
      | Target.player pid => g.dealDamageToPlayer pid 2
      | Target.permanent id => g.dealDamageToPermanent (g.object! id) 2
      | _ => g)
  else if text.contains "-4/-4" then
    g.withLegalKindPermanent controller .creature targets
      (fun g o => g.pumpPermanent o (-4) (-4)) sourceId none
  else if text.contains "+1/+1" then
    g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 1)
      "The source is no longer in play"
  else
    g.draw controller 1

/-- Resolve a modeled MSH Saga chapter. -/
def applyMshChapter (g : Game) (controller : PlayerId) (t : MshChapter)
    (targets : Array Target) (sourceId : Option ObjectId) : Game :=
  let text := t.toNotation
  if text.contains "damage" then
    g.withLegalKindTarget controller .opponent targets (fun g tgt =>
      match tgt with
      | Target.player pid => g.dealDamageToPlayer pid 2
      | _ => g)
  else if text.contains "next red or green" then
    { g with pendingFreeRGCreature := some controller }
      |>.logMsg "The next red or green creature spell you cast this turn can be cast without paying its mana cost"
  else if text.contains "gain control" || text.contains "Gain control" then
    match sourceId.bind g.findObject? with
    | some src =>
      if src.isOnBattlefield then
        targets.foldl (fun (g : Game) (t : Target) =>
          match t with
          | Target.permanent id =>
            match g.findObject? id with
            | some o =>
              if o.isOnBattlefield then
                let g :=
                  if (g.player controller).lost then
                    g.logMsg s!"{o.name} does not change control (CR 800.4b)"
                  else
                    g.setObject { o with
                      controller := some controller
                      controlChanged := true
                      controlUntilSourceLeaves := some src.id }
                g.logMsg s!"{(g.player controller).name} gains control of {o.name}"
              else g
            | none => g
          | _ => g) g
      else
        g.logMsg "The Super Hero Civil War has left the battlefield. You won't gain control."
    | none =>
      g.logMsg "The Super Hero Civil War has left the battlefield. You won't gain control."
  else
    g.createKindTokens controller .treasure 1

/-- Avengers Disassembled: if the land mode was chosen and that target is
illegal, the spell does not resolve — even the untargeted damage mode
(MSH 207). If the land is legal but indestructible, its controller still
searches. -/
def applyAvengersDisassembled (g : Game) (_controller : PlayerId)
    (choseDamage choseLand : Bool) (landId : Option ObjectId) : Game :=
  let landOk :=
    match landId.bind g.findObject? with
    | some o => o.isOnBattlefield && o.printed.isLand
    | none => false
  if choseLand && !landOk then
    g.logMsg "The target is no longer legal. Avengers Disassembled doesn't resolve."
  else
    let g :=
      if choseDamage then
        g.foldBattlefield (fun o => o.isCreature) (fun g o =>
          g.dealDamageToPermanent o 3)
      else g
    if choseLand then
      match landId.bind g.findObject? with
      | some o =>
        let owner := o.owner
        let g := g.destroyPermanent o
        g.logMsg s!"{(g.player owner).name} may search for a basic land"
      | none => g
    else g

/-- Black mana symbols among `ids` for Zemo's boast, counting hybrid symbols
that include black (MSH 128). -/
def zemoBoastBlackSymbols (g : Game) (ids : Array ObjectId) : Nat :=
  ids.foldl (fun n id =>
    match g.findObject? id with
    | some o => n + o.printed.manaCost.symbolsIncludingColor .black
    | none => n) 0

/-- True when `ids` are black cards in `p`'s graveyard whose mana costs have
fifteen or more black mana symbols, including `{B/x}` hybrids (MSH 128). -/
def canPayZemoBoast (g : Game) (p : PlayerId) (ids : Array ObjectId) : Bool :=
  !ids.isEmpty &&
    ids.all (fun id =>
      match g.findObject? id with
      | some o =>
        o.zone == .graveyard p && o.printed.colors.contains .black
      | none => false) &&
    g.zemoBoastBlackSymbols ids >= 15

/-- Baron Helmut Zemo boast: copy only the cards exiled to this activation
(MSH 227). Copies are cast while the ability is resolving (MSH 353). -/
def applyZemoBoast (g : Game) (controller : PlayerId) (exileIds : Array ObjectId)
    (castN : Nat := 0) : Game :=
  Id.run do
    let mut g := g
    let mut copied : Array ObjectId := #[]
    for id in exileIds do
      match g.findObject? id with
      | some o =>
        if o.zone == .graveyard controller then
          let (g', newId) := g.move id .exile none
          g := g'
          copied := copied.push newId
      | none => pure ()
    g := { g with zemoBoastExiles := copied }
    g := g.logMsg s!"Zemo copies {copied.size} card(s) exiled to this activation"
    for id in copied.take castN do
      g := g.castAsPartOfResolution controller id
    return g

/-- Cast up to `n` cards that currently have a free-cast exile permission,
as the ability resolves (Cosmic Cube / Doom Reigns; MSH 356 / 357). -/
def castExiledAsResolves (g : Game) (p : PlayerId) (n : Nat) : Game :=
  let ids :=
    (g.objects.filter (fun o =>
      o.zone == .exile &&
        match o.playPermission with
        | some perm => perm.player == p && perm.withoutManaCost
        | none => false)).map (·.id)
  ids.take n |>.foldl (fun acc id =>
    acc.castAsPartOfResolution p id) g

def applyEffect (g : Game) (controller : PlayerId) (effect : SpellEffect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0) : Game :=
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
    g.foldBattlefield (fun o => o.isCreature) (fun g o => g.pumpPermanent o p t)
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
        g.pumpControlledCreatures pid pw tw
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
    let legal := g.legalTargetsForKind controller effect.targetKind
    match targets[0]? with
    | some t =>
      if legal.contains t then
        let g := g.applyOnPermanent controller effect.targetKind targets .tap
        let g := { g with pendingDrawAfterScry := some (controller, drawN) }
        let g := g.beginScry controller scryN
        if g.pendingDrawAfterScry.isSome &&
            (match g.pending with | .scry _ _ => false | _ => true) then
          let g := { g with pendingDrawAfterScry := none }
          g.draw controller drawN
        else g
      else
        g.logMsg "The spell doesn't resolve"
    | none => g.logMsg "The spell doesn't resolve"
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
          let g :=
            match cb with
            | some p => g.changeControl oa p
            | none => g.setObject { oa with controller := none }
          let g :=
            match ca with
            | some p => g.changeControl (g.object! b) p
            | none => g.setObject { (g.object! b) with controller := none }
          g.logMsg s!"{oa.name} and {ob.name} exchange control"
        else g.logMsg "The target is no longer legal"
      | _, _ => g.logMsg "The target is no longer legal"
    | _, _ => g.logMsg "The target is no longer legal"
  | .plusOneAndPlayerGainsLife n =>
    Id.run do
      let creatureLegal := g.legalTargetsForAtomicKind controller .creature none
      let playerLegal := g.legalTargetsForAtomicKind controller .player none
      let mut g := g
      for t in targets do
        match t with
        | Target.permanent oid =>
          if creatureLegal.contains t then
            match g.findObject? oid with
            | some o => g := g.addPlusOnePlusOneTo o 1
            | none => g := g.logMsg "The target is no longer in play"
          else
            g := g.illegalAbilityTarget t
        | Target.player pid =>
          if playerLegal.contains t then
            if n != 0 then
              let pl := g.player pid
              g := g.setLife pid (pl.life + (n : Int))
                s!"{pl.name} gains {n} life ({pl.life + (n : Int)} life)"
          else
            g := g.illegalAbilityTarget t
        | Target.card _ =>
          g := g.illegalAbilityTarget t
      return g
  | .returnSpellDraw =>
    let g :=
      match targets[0]? with
      | some (Target.card id) => g.returnStackSpell id
      | _ => g.logMsg "The target is no longer legal"
    g.draw controller 1
  | .creaturesYouControlPump pw tw =>
    g.pumpControlledCreatures controller pw tw
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
          g.returnToHand o.id controller
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
          g.forEachControlledCreature controller
            (fun g c => g.addPlusOnePlusOneTo c 1) (some oid)
    | _ => g.logMsg "The target is no longer legal"
  | .drawIfFromGy n fromGy =>
    g.draw controller (if castFromGraveyard then fromGy else n)
  | .amassGoblinsOrFromGy n fromGy =>
    g.amassGoblins controller (if castFromGraveyard then fromGy else n)
  | .searchLegendaryCreatureToHand =>
    g.resolveLibrarySearchToHand controller (fun c =>
      c.isCreature && c.hasSupertype .legendary) "legendary creature card"
  | .dealDamageToEachOppCreature n =>
    g.foldBattlefield (fun o => o.isCreature && !o.controlledBy controller)
      (fun g o => g.applyPermanentAction o (.dealDamage n))
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
    g.dealDamageToEachNonDragon n
  | .chooseTypeReturnOthers =>
    let chosen :=
      (g.battlefield.find? (fun o => o.isCreature && o.controlledBy controller)
        |>.bind (fun o => o.printed.subtypes[0]?)).getD "Elf"
    g.foldBattlefield (fun o => o.isCreature && !g.hasSubtype o chosen)
      (fun g o => g.returnToHand o.id o.owner)
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
    g.millThenPutFromGy controller n
      (fun o => o.printed.isInstant || o.printed.isSorcery) (some 1)
  | .millThenPutLands n max =>
    g.millThenPutFromGy controller n (fun o => o.printed.isLand) (some max)
  | .dealDamageToEachNonDragonThenAddDragonMana n =>
    let g := g.dealDamageToEachNonDragon n
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .red) 4 })
      |>.logMsg
        s!"{(g.player controller).name} adds four mana that can be spent only on Dragon spells"
  | .millThenPutAllInstantsOrSorceries n =>
    g.millThenPutFromGy controller n
      (fun o => o.printed.isInstant || o.printed.isSorcery)
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
  | .exileTopPlayIfYouControlSubtype n subtype =>
    g.exileTopPlayIfYouControlSubtype controller n subtype
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
  | .returnSpellCantCastIfGift =>
    let g :=
      match targets[0]? with
      | some (Target.card sid) => g.returnStackSpell sid
      | _ => g.logMsg "The target is no longer legal"
    if giftPromised then
      g.players.foldl (fun acc pl =>
        acc.setPlayer { pl with cantCastSpellsThisTurn := true }) g
        |>.logMsg "Players can't cast spells this turn"
    else g
  | .exileTopXOppPlayForLife =>
    match targets[0]? with
    | some (Target.player pid) =>
      Id.run do
        let mut g := g
        for _ in List.range chosenX do
          let pl := g.player pid
          if pl.library.isEmpty then
            g := g.logMsg s!"{pl.name} has no cards in their library to exile"
          else
            let top := pl.library.back!
            let name := (g.object! top).name
            let (g', newId) := g.move top .exile none
            g := g'
            let o := g.object! newId
            g := g.setObject { o with
              playPermission := some {
                player := controller
                turnEndsRemaining := 1
                whileExiled := true
                payLifeEqualManaValue := true } }
            g := g.logMsg s!"{(g.player controller).name} exiles {name}"
        return g
    | _ => g.logMsg "The target is no longer legal"
  | .riddlesInTheDark =>
    g.riddlesInTheDark controller 2 false
  | .supperForSpiders =>
    let ids :=
      g.battlefieldCreaturesToGyThisTurn.filter (fun id =>
        match g.findObject? id with
        | some o =>
          o.zone == .graveyard o.owner && o.owner != controller
        | none => false)
    g.supperForSpidersReturn controller ids
  | .eaglesAreComing =>
    let ids :=
      targets.filterMap (fun
        | Target.permanent id => some id
        | _ => none)
    Id.run do
      let mut g := g
      let mut n : Nat := 0
      for id in ids do
        match g.findObject? id with
        | none => pure ()
        | some o =>
          if o.isOnBattlefield && o.isCreature && o.owner == controller then
            let name := o.name
            let owner := o.owner
            let (g', _) := g.move o.id (.hand owner) none
            g := g'.logMsg s!"{name} is returned to {(g'.player owner).name}'s hand"
            n := n + 1
      if n > 0 then
        g := g.modifyPlayer controller (fun pl =>
          { pl with eaglesBirdsNextUpkeep := pl.eaglesBirdsNextUpkeep + n })
        g := g.logMsg
          s!"At the beginning of the next upkeep, {n} Bird Soldier token(s) will be created"
      return g
  | .lookAtTopLandsGainLife n life =>
    Id.run do
      let mut g := g
      let pl := g.player controller
      let take := min n pl.library.size
      let ids := pl.library.extract (pl.library.size - take) pl.library.size
      for id in ids do
        match g.findObject? id with
        | some o =>
          if o.printed.isLand then
            let name := o.name
            let (g', newId) := g.putOntoBattlefield id controller (tapped := true)
            g := g'
            g := g.setObject { (g.object! newId) with
              status := { (g.object! newId).status with tapped := true } }
            g := g.logMsg s!"{name} enters tapped"
            g := g.afterLandEnters (g.object! newId)
          else pure ()
        | none => pure ()
      g := g.requestShuffle controller (.gainLife controller life)
      return g.continueIfShuffled
  | .gainControlOppArtifacts =>
    Id.run do
      let mut g := g
      for t in targets do
        match t with
        | Target.permanent oid =>
          match g.findObject? oid with
          | none => pure ()
          | some o =>
            if o.isOnBattlefield && o.printed.isArtifact && !o.controlledBy controller then
              g := g.changeControl o controller
        | _ => pure ()
      return g
  | .damageOppCreaturesEqualOtherSpellsMv =>
    let xs := (g.player controller).castManaValuesThisTurn
    let n : Nat := (xs.extract 0 xs.size.pred).foldl (fun a b => a + b) 0
    g.foldBattlefield (fun o => o.isCreature && !o.controlledBy controller)
      (fun g o => g.dealDamageToPermanent o (Int.ofNat n))
      |>.logMsg s!"deals {n} damage to each opposing creature"
  | .phaseOutKicker =>
    if kicked then
      match targets[0]? with
      | some (Target.player pid) =>
        (g.permanentsOf pid).foldl (fun acc o =>
          if o.isCreature then acc.phaseOut o else acc) g
      | some (Target.permanent oid) =>
        match g.findObject? oid with
        | some o =>
          let pid := o.controller.getD controller
          (g.permanentsOf pid).foldl (fun acc x =>
            if x.isCreature then acc.phaseOut x else acc) g
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "The target is no longer legal"
    else
      match targets[0]? with
      | some (Target.permanent oid) =>
        match g.findObject? oid with
        | some o => g.phaseOut o
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "The target is no longer legal"
  | .dealDamageTeamwork n teamworkN =>
    let amt := if g.stack.back?.any (fun e =>
        (g.findObject? e.objectId).any (·.teamworkPaid)) then teamworkN else n
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      g.dealDamageToPermanent o amt)
  | .dealDamageThenControllerIfTeamwork n extra =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.dealDamageToPermanent o n
      if g.stack.back?.any (fun e =>
          (g.findObject? e.objectId).any (·.teamworkPaid)) then
        match o.controller with
        | some pid => g.dealDamageToPlayer pid extra
        | none => g
      else g)
  | .grantDoubleStrikeTeamworkTrample =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.mapObjectStatus o (·.grantUntilEot Keyword.doubleStrike)
      if g.stack.back?.any (fun e =>
          (g.findObject? e.objectId).any (·.teamworkPaid)) then
        g.mapObjectStatus (g.object! o.id) (·.grantUntilEot Keyword.trample)
      else g)
  | .counterUnlessPaysTeamwork n teamworkN =>
    let amt := if g.stack.back?.any (fun e =>
        (g.findObject? e.objectId).any (·.teamworkPaid)) then teamworkN else n
    match targets[0]? with
    | some (Target.card id) =>
      match g.findObject? id with
      | some o =>
        let ctrl := o.controller.getD o.owner
        { g with pending := .payOrLetCounter ctrl amt id }.logMsg
          s!"{(g.player ctrl).name} may pay \{{amt}} or {o.name} is countered"
      | none => g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | .exileCreatureMvAtMostOrAnyIfTeamwork _n life =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let (g, _) := g.move o.id .exile none
      if g.stack.back?.any (fun e =>
          (g.findObject? e.objectId).any (·.teamworkPaid)) then
        g.modifyPlayer controller (fun pl => { pl with life := pl.life + (life : Int) })
      else g)
  | .returnGyCreatureMvAtMostOrAny _n =>
    match targets[0]? with
    | some (Target.card id) =>
      match g.findObject? id with
      | some _ =>
        let (g, _) := g.putOntoBattlefield id controller
        g
      | none => g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | .revealTopPutCreatures n =>
    Id.run do
      let mut g := g
      let lib := (g.player controller).library
      let top := lib.extract (lib.size - n.min lib.size) lib.size
      let teamwork := g.stack.back?.any (fun e =>
        (g.findObject? e.objectId).any (·.teamworkPaid))
      let mut putOne := false
      for id in top do
        let o := g.object! id
        if o.printed.isCreature && (teamwork || !putOne) then
          let (g', _) := g.putOntoBattlefield id controller
          g := g'
          putOne := true
        else
          let (g', _) := g.move id (.graveyard o.owner) none
          g := g'
      return g
  | .createTokens kind n =>
    g.createKindTokens controller kind n
  | .exileTarget =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      (g.move o.id .exile none).1)
  | .returnOneOrTwoNonlands =>
    targets.foldl (fun g t =>
      match t with
      | Target.permanent oid =>
        match g.findObject? oid with
        | some o => (g.move o.id (.hand o.owner) none).1
        | none => g
      | _ => g) g
  | .targetPlayerCreatesTokens kind n =>
    let pid :=
      match targets[0]? with
      | some (Target.player p) => p
      | _ => controller
    g.createKindTokens pid kind n
  | .destroyCreatureSurveil =>
    let stillLegal :=
      match targets[0]? with
      | some t => (g.legalTargetsForKind controller effect.targetKind).contains t
      | none => false
    if stillLegal then
      let g := g.withLegalKindPermanent controller effect.targetKind targets
        (fun g o => g.destroyPermanent o)
      g.beginScry controller 1
    else
      g.logMsg "The target is no longer legal. You won't surveil."
  | .investigatePumpFlyingUntap =>
    let g := (g.createToken controller clueToken).1
    g.withLegalKindPermanent controller .creature targets (fun g o =>
      let g := g.mapObjectStatus o (·.grantUntilEot Keyword.flying)
      let o := g.object! o.id
      let g := g.applyPermanentAction o .untap
      g.applyPermanentAction (g.object! o.id) (.pump 1 0))
  | .plusOneLifelinkIndestructible =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.mapObjectStatus o (fun s =>
        { s with plusOnePlusOne := s.plusOnePlusOne + 1 })
      let o := g.object! o.id
      let g := g.mapObjectStatus o (·.grantUntilEot Keyword.lifelink)
      g.mapObjectStatus (g.object! o.id) (·.grantUntilEot Keyword.indestructible))
  | .dealDamageToEachCreature n =>
    g.foldBattlefield (fun o => o.isCreature) (fun g o => g.dealDamageToPermanent o (n : Int))
  | .destroyLandSearchBasic =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let owner := o.owner
      let g := g.destroyPermanent o
      g.logMsg s!"{(g.player owner).name} may search for a basic land")
  | .doublePowerAndToughness =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let p := g.power o
      let t := g.toughness o
      g.applyPermanentAction o (.pump p t))
  | .returnGySubtypeToHand _subtype =>
    match targets[0]? with
    | some (Target.card id) =>
      match g.findObject? id with
      | some o => (g.move o.id (.hand o.owner) none).1
      | none => g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | .grantVigilanceUnblockable =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.mapObjectStatus o (·.grantUntilEot Keyword.vigilance)
      let g := g.mapObjectStatus (g.object! o.id) (·.grantUntilEot Keyword.cantBeBlocked)
      g.draw controller 1)
      none (some "The target is no longer legal. You won't draw a card.")
  | .becomeArtifactCreature44Flying =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.mapObjectStatus o (fun s =>
        { s with
          setBasePT := some (4, 4)
          additionalArtifactUntilEot := true
          additionalCreatureUntilEot := true
          untilEotKeywords := Keywords.merge s.untilEotKeywords Keyword.flying })
      g.logMsg s!"{o.name} becomes a 4/4 artifact creature with flying until end of turn")
  | .drawThreeDiscardUnlessArtifact =>
    let g := g.draw controller 3
    let g := { g with thirstDiscardsLeft := 2 }
    g.beginDiscardCards #[controller]
  | .eachOpponentLosesLife n =>
    g.forEachOpponent controller (fun g pid => g.loseLife pid n)
  | .fightUpToOne =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent srcId), some (Target.permanent destId) =>
      let src := g.object! srcId
      g.dealDamageFrom src.name (g.object! destId) (g.power src).toNat
    | some (Target.permanent srcId), none =>
      g.logMsg s!"{(g.object! srcId).name} has nothing to fight"
    | _, _ => g.logMsg "The target is no longer legal"
  | .plusOneOnEachYouControl =>
    g.forEachControlledCreature controller (fun g o => g.addPlusOnePlusOneTo o 1)
  | .plusOneOnCreatureN n =>
    g.withLegalKindPermanent controller .creatureYouControl targets
      (fun g o => g.addPlusOnePlusOneTo o n)
  | .msh t =>
    g.applyMshSpell controller t targets none

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
      g.returnToHand o.id o.owner
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
    (targets : Array Target) (sourceId : Option ObjectId := none)
    (lastKnownPower : Option Int := none) : Game :=
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
          g.attachSourceTo src host)
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
    g.pumpControlledCreatures controller pw tw
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
      g.requestShuffle owner (.draw owner n) |>.continueIfShuffled
  | .returnFromGyAttach =>
    match sourceId.bind g.findObject? with
    | none => g.logMsg "The source is no longer in the graveyard"
    | some src =>
      g.withLegalKindPermanent controller effect.targetKind targets (fun g host =>
        let (g, newId) := g.putOntoBattlefield src.id controller
          (attachedTo := some host.id)
        let o := g.object! newId
        let g := g.logMsg s!"{o.name} enters the battlefield attached to {host.name}"
        g.afterPermanentEnters (g.object! newId))
        sourceId (some "The target is no longer legal. Eagle's Rescue remains in the graveyard.")
  | .addMana types =>
    let g := g.modifyPlayer controller (fun pl =>
      { pl with manaPool :=
        types.foldl (fun pool t => pool.add t) pl.manaPool })
    g.logMsg s!"{(g.player controller).name} adds mana"
  | .searchBasicLandToHand =>
    g.resolveSearchBasicLandToHand controller
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
    let g := g.pumpControlledCreatures controller p t
    g.forEachOpponent controller (fun g pid => g.loseLife pid life)
  | .goblinsAndOrcsGainMenace =>
    g.grantUntilEotToControlledCreatures controller Keyword.menace "menace"
      (fun g o => g.hasSubtype o "Goblin" || g.hasSubtype o "Orc")
  | .exileThenReturnNextEnd =>
    Id.run do
      let mut g := g
      for t in targets do
        match t with
        | Target.permanent oid =>
          match g.findObject? oid with
          | none => pure ()
          | some o =>
            if o.controlledBy controller && !o.printed.isLand && some o.id != sourceId then
              let name := o.name
              let owner := o.owner
              let (g', newId) := g.move oid .exile none
              g := g'
              let o := g.object! newId
              g := g.setObject { o with
                playPermission := none
                linkedExile := #[] }
              -- Return immediately for this engine (next end step is modeled
              -- as a delayed return at the next end step via eagles-style
              -- bookkeeping: bounce now, then put back tapped next end).
              let (g'', retId) := g.move newId .battlefield (some owner)
              g := g''
              let ret := g.object! retId
              let sick := !ret.printed.keywords.haste
              g := g.setObject { ret with status := { ret.status with summoningSick := sick } }
              g := g.logMsg s!"{name} is exiled, then returned"
              g := g.afterPermanentEnters (g.object! retId)
        | _ => pure ()
      return g
  | .searchBasicBeholdElfUntap =>
    let g := g.resolveSearchBasicLandTapped controller
    let g := g.beholdQuality controller "Elf"
    if g.qualityWasBeheld controller "Elf" then
      match (g.permanentsOf controller).find? (fun o => o.printed.isLand && o.status.tapped) with
      | none => g
      | some land => g.applyPermanentAction land .untap
    else g
  | .twoPlayersDraw =>
    match targets[0]?, targets[1]? with
    | some (Target.player a), some (Target.player b) =>
      if a == b then g.logMsg "Two target players must be different"
      else g.draw a 1 |>.draw b 1
    | _, _ => g.logMsg "The targets are no longer legal"
  | .discardLegendarySameNameDraw =>
    g.draw controller 2
  | .dealDamageToAny n =>
    g.applyEffect controller (.dealDamage n) targets
  | .drawEqualSacrificedPowerThenDiscard =>
    let n :=
      match sourceId.bind g.findObject? with
      | some src => (g.power src).toNat
      | none => 1
    let g := g.draw controller (max n 1)
    g.beginDiscardCards #[controller]
  | .arwenShare =>
    match sourceId, targets[0]? with
    | some sid, some (Target.permanent tid) => g.resolveArwenShare sid (some tid)
    | some sid, _ => g.resolveArwenShare sid none
    | _, _ => g.logMsg "The ability's source is no longer in play"
  | .grantCombatDamageCreateTreasure =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.mapObjectStatus o (fun s => { s with combatDamageCreatesTreasure := true })
      g.logMsg
        s!"{o.name} gains \"Whenever this creature deals combat damage to a player, create a Treasure token\"")
      sourceId (some "The target is no longer legal")
  | .putShadowCounter =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      g.putShadowCounter o) sourceId (some "The target is no longer legal")
  | .damageEachOpponent n =>
    g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid n)
  | .chooseTwoDestroyRest =>
    let keep :=
      targets.filterMap (fun | Target.permanent id => some id | _ => none)
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.isCreature && !keep.contains o.id then
          g := g.destroyPermanent o
      return g.logMsg "Chosen creatures are kept; the rest are destroyed"
  | .blackGateUnblockable =>
    match targets[0]? with
    | some (Target.permanent oid) =>
      match g.playersWithMostLife[0]? with
      | some pid => g.applyBlackGateUnblockable oid pid
      | none => g
    | _ => g.logMsg "The target is no longer legal"
  | .burdenThenDraw =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let g := g.setObject { o with status := { o.status with burden := o.status.burden + 1 } }
      let n := (g.object! o.id).status.burden
      let g := g.logMsg s!"{o.name} gets a burden counter ({n})"
      g.draw controller n
  | .teamGainDoubleStrike =>
    g.grantUntilEotToControlledCreatures controller Keyword.doubleStrike
      "double strike"
  | .sourceGainsIndestructibleTap =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let g := g.mapObjectStatus o (·.grantUntilEot Keyword.indestructible)
      let o := g.object! o.id
      let g := g.setObject { o with status := { o.status with tapped := true } }
      g.logMsg s!"{o.name} gains indestructible until end of turn and becomes tapped"
  | .plusOneOnEachOtherSubtype subtype n =>
    g.foldBattlefield (fun o =>
        o.controlledBy controller && o.id != sourceId.getD ⟨0⟩ && g.hasSubtype o subtype)
      (fun g o => g.mapObjectStatus o (fun s =>
        { s with plusOnePlusOne := s.plusOnePlusOne + n }))
  | .plusOneAndIndestructibleCounter =>
    g.withSourceOnBattlefield sourceId fun g o =>
      g.setObject { o with status := { o.status with
        plusOnePlusOne := o.status.plusOnePlusOne + 1
        indestructibleCounters := o.status.indestructibleCounters + 1 } }
  | .plusOneAndDraw plus cards =>
    let g :=
      match sourceId.bind g.findObject? with
      | some o =>
        if o.isOnBattlefield then
          g.setObject { o with status := { o.status with
            plusOnePlusOne := o.status.plusOnePlusOne + plus } }
        else g
      | none => g
    g.draw controller cards
  | .plusOneAndExtraTurn =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let g := g.setObject { o with status := { o.status with
        plusOnePlusOne := o.status.plusOnePlusOne + 1 } }
      g.logMsg s!"{(g.player controller).name} takes an extra turn after this one"
  | .plusOneX =>
    let x :=
      match sourceId.bind g.findObject? with
      | some o => o.chosenX.getD 0
      | none => 0
    g.withSourceOnBattlefield sourceId fun g o =>
      g.setObject { o with status := { o.status with
        plusOnePlusOne := o.status.plusOnePlusOne + x } }
  | .eachOppDiscardThenPlusOne =>
    let g :=
      (g.livingOpponents controller).foldl (fun acc pl =>
        acc.beginDiscardCards #[pl.id]) g
    g.withSourceOnBattlefield sourceId fun g o =>
      g.setObject { o with status := { o.status with
        plusOnePlusOne := o.status.plusOnePlusOne + 1 } }
  | .lookAtTopPutHeroEquipVehicle n =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let g := g.setObject { o with status := { o.status with
        plusOnePlusOne := o.status.plusOnePlusOne + 2 } }
      g.logMsg s!"{(g.player controller).name} looks at the top {n} cards"
  | .transform =>
    g.withSourceOnBattlefield sourceId fun g o =>
      if o.status.cantTransform then
        g.logMsg s!"{o.name} can't transform (entered back face up at night)"
      else
        match o.printed.otherFace with
        | none => g.logMsg s!"{o.name} has no other face"
        | some face =>
          let back := { face with otherFace := some { o.printed with otherFace := none } }
          let g := g.setObject { o with
            printed := back
            status := { o.status with transformed := !o.status.transformed } }
          g.logMsg s!"{o.name} transforms into {back.name}"
  | .drawX =>
    let x :=
      match sourceId.bind g.findObject? with
      | some o => o.chosenX.getD 0
      | none => 0
    g.draw controller x
  | .lookAtTopRevealArtifact n =>
    g.logMsg s!"{(g.player controller).name} looks at the top {n} cards"
  | .connive =>
    g.applyConnive controller sourceId
  | .msh t =>
    g.applyMshAbility controller t targets sourceId lastKnownPower
  | .mshSpell t =>
    g.applyMshSpell controller t targets sourceId

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

/-- Queue “whenever the Ring tempts you” and “whenever you choose a
Ring-bearer” triggers for `p`. -/
def putRingTemptTriggers (g : Game) (p : PlayerId) (choseBearer : Bool) : Game :=
  let g := g.putControlledTriggers p .theRingTemptsYou
  if choseBearer then g.putControlledTriggers p .youChooseRingBearer else g

/-- As the Ring tempts `p`: get The Ring emblem if needed, gain its next
ability, then choose a Ring-bearer if `p` controls a creature. Re-choosing
the same creature still counts as choosing it. -/
def temptWithTheRing (g : Game) (p : PlayerId) (chosen : Option ObjectId := none) : Game :=
  let pl := g.player p
  let nextAbilities := min 4 (pl.theRingAbilities + 1)
  let gainedEmblem := pl.theRingAbilities == 0
  let g := g.modifyPlayer p (fun pl => { pl with theRingAbilities := nextAbilities })
  let g :=
    if gainedEmblem then
      g.logMsg s!"{(g.player p).name} gets an emblem named The Ring"
    else g
  let g := g.logMsg
    s!"{(g.player p).name}'s emblem named The Ring gains its next ability ({nextAbilities})"
  let choices := g.ringBearerChoices p
  let pick :=
    match chosen with
    | some id =>
      if choices.any (fun o => o.id == id) then some id else choices[0]?.map (·.id)
    | none => choices[0]?.map (·.id)
  let g := g.setRingBearer p pick
  let g :=
    match pick with
    | some id =>
      g.logMsg s!"{(g.player p).name} chooses {(g.object! id).name} as their Ring-bearer"
    | none =>
      g.logMsg s!"{(g.player p).name} controls no creature to become Ring-bearer"
  g.putRingTemptTriggers p pick.isSome

/-- A targeted spell or ability that would tempt only does so if it resolves. -/
def resolveTargetedTempt (g : Game) (p : PlayerId) (kind : EffectTargetKind)
    (targets : Array Target) : Game :=
  if kind != .none && targets.isEmpty then
    g.logMsg "The spell doesn't resolve. The Ring won't tempt you."
  else
    g.withLegalKindTarget p kind targets (fun g _ => g.temptWithTheRing p)
      (missing := some "The spell doesn't resolve. The Ring won't tempt you.")

/-- Give the promised gift (a Treasure) to `to` before other effects. -/
def givePromisedGift (g : Game) (to : PlayerId) : Game :=
  let (g, _) := g.createToken to treasureToken
  g.logMsg s!"{(g.player to).name} is given a Treasure (gift)"

/-- Copy a spell on the stack. The copy is also kicked / has the same
promised gift. It is not cast. -/
def copyStackSpell (g : Game) (src : GameObject) (controller : PlayerId) : Game :=
  if (g.player controller).lost then
    g.logMsg s!"{src.name} remains in its current zone (CR 800.4b)"
  else
    let (g, copy) := g.allocObject src.printed controller .stack (some controller)
    let g := g.setObject { copy with
      kicked := src.kicked
      giftPromisedTo := src.giftPromisedTo
      teamworkPaid := src.teamworkPaid
      sneakPaid := src.sneakPaid
      sneakAttackWhom := src.sneakAttackWhom
      chosenX := src.chosenX
      isCopy := true
      adventurerCard := src.adventurerCard }
    let g := g.putStackEntry controller copy.id
    g.logMsg s!"A copy of {src.name} is created"

/-- Exile from the top until a nonland with mana value less than `maxMv`.
The resulting spell must also have lesser mana value. Casting is optional. -/
def resolveCascade (g : Game) (p : PlayerId) (maxMv : Nat) : Game :=
  Id.run do
    let mut g := g
    let mut exiled : Array ObjectId := #[]
    let mut found : Option GameObject := none
    while found.isNone && !(g.player p).library.isEmpty do
      match (g.player p).library.back? with
      | none => pure ()
      | some id =>
        let (g', newId) := g.move id .exile none
        g := g'
        exiled := exiled.push newId
        let card := g.object! newId
        if !card.printed.isLand && card.printed.manaCost.manaValue < maxMv then
          found := some card
    g := g.logMsg s!"{(g.player p).name} exiles cards for cascade (less than {maxMv})"
    match found with
    | none =>
      if g.norandom && exiled.size > 1 then
        return g.requestOrderInto exiled (.library p)
          s!"{(g.player p).name} puts the exiled cards on the bottom of their library in a random order"
      for id in exiled.reverse do
        let (g', _) := g.move id (.library (g.object! id).owner) none
        g := g'
      return g.logMsg "No cheaper nonland card was exiled"
    | some card =>
      let others := exiled.filter (· != card.id)
      if g.norandom && others.size > 1 then
        let g2 :=
          if card.printed.manaCost.manaValue < maxMv then
            g.logMsg
              s!"{(g.player p).name} may cast {card.name} without paying its mana cost (cascade)"
          else
            let (g', _) := g.move card.id (.library card.owner) none
            g'.logMsg
              s!"{card.name}'s resulting spell does not have lesser mana value"
        return g2.requestOrderInto others (.library p)
          s!"{(g.player p).name} puts the remaining exiled cards on the bottom of their library in a random order"
      for id in others.reverse do
        let (g', _) := g.move id (.library (g.object! id).owner) none
        g := g'
      if card.printed.manaCost.manaValue < maxMv then
        return g.logMsg
          s!"{(g.player p).name} may cast {card.name} without paying its mana cost (cascade)"
      else
        let (g', _) := g.move card.id (.library card.owner) none
        return g'.logMsg
          s!"{card.name}'s resulting spell does not have lesser mana value"

/-- Cast `cardId` from exile without paying its mana cost (cascade). -/
def castCascadeCard (g : Game) (p : PlayerId) (cardId : ObjectId) (maxMv : Nat) :
    Except String Game := do
  let some card := g.findObject? cardId | throw "no such card"
  if card.printed.isLand then
    throw "A land cannot be cast"
  if card.printed.manaCost.manaValue >= maxMv then
    throw "The resulting spell must have lesser mana value than the cascade spell"
  let (g, newId) := g.move cardId .stack (some p)
  let o := g.object! newId
  let g := g.setObject { o with
    playPermission := some {
      player := p
      turnEndsRemaining := 0
      withoutManaCost := true } }
  let g := g.putStackEntry p newId
  return g.becomeCast p (g.object! newId)

/-- Mark the proposed spell kicked and add the kicker cost. Cannot kick twice. -/
def applyKickerToProposed (g : Game) (kick : Bool) : Except String Game := do
  let some prop := g.proposedSpell | throw "No spell is waiting for kicker"
  if prop.kicked && kick then
    throw "The kicker ability doesn't let you pay a kicker cost more than once"
  if !kick then
    return { g with proposedSpell := some { prop with
      kicked := false, kickerAnnounced := true } }
  let some spell := g.findObject? prop.spellId | throw "The spell left the stack"
  match spell.printed.kicker with
  | none => throw "That spell has no kicker"
  | some kicker =>
    let g := g.setObject { spell with kicked := true }
    let face := spell.printed
    let start :=
      if !prop.cost.includesManaPayment && (playCostStart spell face).includesManaPayment then
        ManaCost.empty
      else playCostStart spell face
    let cost :=
      ManaCost.afterReduction face.manaCost
        (g.applyCastCostReductions spell face (start.addCost kicker))
    return { g with proposedSpell := some { prop with
      kicked := true
      kickerAnnounced := true
      cost } }

/-- Promise a gift to `to`. Cannot promise more than once. -/
def applyGiftToProposed (g : Game) (to : Option PlayerId) : Except String Game := do
  let some prop := g.proposedSpell | throw "No spell is waiting for a gift"
  if prop.giftTo.isSome && to.isSome then
    throw "You can't pay a gift cost more than once"
  let some spell := g.findObject? prop.spellId | throw "The spell left the stack"
  let g := g.setObject { spell with giftPromisedTo := to }
  return { g with proposedSpell := some { prop with
    giftTo := to, giftAnnounced := true } }

/-- Continue the proposal window after kicker / gift announcements. -/
def afterOptionalAdditionalCost (g : Game) (p : PlayerId) : Game :=
  match g.proposedSpell, g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) with
  | some prop, some spell =>
    if spell.printed.giftTreasure && !prop.giftAnnounced then
      let g := { g with pending := .chooseGift p }
      g.logMsg s!"{(g.player p).name} may promise a gift (CR 702.185)"
    else if spell.printed.teamwork.isSome && !prop.teamworkAnnounced then
      let g := { g with pending := .chooseTeamwork p }
      g.logMsg s!"{(g.player p).name} may pay a teamwork cost (CR 702.194)"
    else if g.proposedNeedsTarget prop then
      let g := { g with pending := .chooseTargets p }
      g.logMsg s!"{(g.player p).name} must choose a target (CR 601.2c)"
    else
      g.afterTargetsChosen
  | _, _ => g

def announceKicker (g : Game) (p : PlayerId) (kick : Bool) : Except String Game := do
  match g.pending with
  | .chooseKicker caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may announce kicker"
    let g ← g.applyKickerToProposed kick
    let g := g.logMsg
      (if kick then s!"{(g.player p).name} kicks the spell"
       else s!"{(g.player p).name} does not kick the spell")
    return g.afterOptionalAdditionalCost p
  | _ => throw "Not time to announce kicker"

def announceGift (g : Game) (p : PlayerId) (to : Option PlayerId) : Except String Game := do
  match g.pending with
  | .chooseGift caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may promise a gift"
    if let some opp := to then
      if opp == p then throw "You must promise the gift to an opponent"
    let g ← g.applyGiftToProposed to
    let g :=
      match to with
      | some opp =>
        g.logMsg s!"{(g.player p).name} promises a gift to {(g.player opp).name}"
      | none =>
        g.logMsg s!"{(g.player p).name} does not promise a gift"
    return g.afterOptionalAdditionalCost p
  | _ => throw "Not time to promise a gift"

def announceTeamwork (g : Game) (p : PlayerId) (pay : Bool) : Except String Game := do
  match g.pending with
  | .chooseTeamwork caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may announce teamwork"
    let some prop := g.proposedSpell | throw "No spell is waiting for teamwork"
    if !pay then
      let g := { g with proposedSpell := some { prop with
        teamworkPaid := false, teamworkAnnounced := true } }
      let g := g.logMsg s!"{(g.player p).name} does not pay a teamwork cost"
      return g.afterOptionalAdditionalCost p
    match prop.original.printed.teamwork.orElse (fun () =>
        (g.findObject? prop.spellId).bind (fun o => o.printed.teamwork)) with
    | none => throw "That spell has no teamwork"
    | some need =>
      let g := { g with
        pending := .chooseTeamworkCreatures p need
        proposedSpell := some { prop with teamworkAnnounced := true } }
      return g.logMsg
        s!"{(g.player p).name} chooses creatures to tap for teamwork {need}"
  | _ => throw "Not time to announce teamwork"

def payTeamworkCreatures (g : Game) (p : PlayerId) (ids : Array ObjectId) :
    Except String Game := do
  match g.pending with
  | .chooseTeamworkCreatures caster need =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may tap creatures for teamwork"
    let some prop := g.proposedSpell | throw "No spell is waiting for teamwork"
    let mut total : Int := 0
    let mut seen : Array ObjectId := #[]
    for id in ids do
      if seen.contains id then
        throw "A creature cannot be tapped twice for the same teamwork cost"
      seen := seen.push id
      let some o := g.findObject? id | throw "no such object"
      if !(o.isOnBattlefield && o.isCreature && o.controlledBy p) then
        throw s!"{o.name} is not a creature you control"
      if o.status.tapped then
        throw s!"{o.name} is already tapped"
      total := total + g.power o
    if total < (need : Int) then
      throw s!"Tapped creatures must have total power {need} or more"
    let mut g := g
    for id in ids do
      match g.findObject? id with
      | none => pure ()
      | some o =>
        g := g.applyPermanentAction o .tap
        g := g.putMatchingSourceTriggers p (g.object! id) .tappedForTeamwork
    let some spell := g.findObject? prop.spellId | throw "The spell left the stack"
    g := g.setObject { spell with teamworkPaid := true }
    g := { g with
      pending := .none
      proposedSpell := some { prop with teamworkPaid := true, teamworkAnnounced := true } }
    g := g.logMsg s!"{(g.player p).name} pays a teamwork cost"
    return g.afterOptionalAdditionalCost p
  | _ => throw "Not time to tap creatures for teamwork"

def announceRingBearer (g : Game) (p : PlayerId) (id : Option ObjectId) : Except String Game := do
  match g.pending with
  | .chooseRingBearer caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may choose a Ring-bearer"
    let choices := g.ringBearerChoices p
    if id.isNone && !choices.isEmpty then
      throw "You must choose a creature if you control one"
    let g := { g with pending := .none }
    return g.temptWithTheRing p id
  | _ => throw "Not time to choose a Ring-bearer"

/-- Search for up to `max` basic Plains, exile them linked to `sourceId`,
shuffle, and gain `life`. -/
def resolveSearchBasicPlainsExile (g : Game) (p : PlayerId)
    (sourceId : Option ObjectId) (max life : Nat) : Game :=
  Id.run do
    let mut g := g
    for _ in [0:max] do
      match g.findLibraryCard? p (fun c => isBasicLandCard c && c.hasSubtype "Plains") with
      | none => pure ()
      | some id =>
        let name := (g.object! id).name
        let (g', newId) := g.move id .exile none
        g := g'
        match sourceId.bind g.findObject? with
        | some src =>
          g := g.setObject { src with linkedExile := src.linkedExile.push newId }
        | none => pure ()
        g := g.logMsg s!"{(g.player p).name} exiles {name}"
    g := g.requestShuffle p (.gainLife p life)
    return g.continueIfShuffled

/-- Target opponent reveals their hand; you discard a nonland of your choice. -/
def discardNonlandFrom (g : Game) (controller victim : PlayerId) : Game :=
  let names :=
    (g.player victim).hand.filterMap (fun id =>
      (g.findObject? id).map (·.name))
  let g :=
    if names.isEmpty then
      g.logMsg s!"{(g.player victim).name} reveals an empty hand"
    else
      g.logMsg
        s!"{(g.player victim).name} reveals {String.intercalate ", " names.toList}"
  match (g.player victim).hand.findSome? (fun id =>
      match g.findObject? id with
      | some o => if !o.printed.isLand then some o else none
      | none => none) with
  | none => g.logMsg s!"{(g.player victim).name} has no nonland card to discard"
  | some o =>
    let (g, _) := g.move o.id (.graveyard o.owner) none
    g.logMsg s!"{(g.player controller).name} chooses {o.name}. {(g.player victim).name} discards it"

/-- Exile `o` and return it at the beginning of the next end step. -/
def exileUntilNextEndStep (g : Game) (o : GameObject) : Game :=
  let name := o.name
  let (g, newId) := g.move o.id .exile none
  let g := { g with delayedEndStepReturns := g.delayedEndStepReturns.push newId }
  g.logMsg s!"{name} is exiled until the beginning of the next end step"

/-- Resolve a printed Saga chapter (CR 714.3 / 608). -/
def applyChapterEffect (g : Game) (controller : PlayerId) (e : ChapterEffect)
    (sourceId : Option ObjectId) (targets : Array Target) : Game :=
  match e with
  | .dealDamageToOppCreature n =>
    g.withLegalKindPermanent controller .oppCreature targets (fun g o =>
      g.dealDamageToPermanent o n) sourceId (some "The target is no longer legal")
  | .destroyOppArtifact =>
    g.withLegalKindPermanent controller .oppArtifact targets (fun g o =>
      g.destroyPermanent o) sourceId (some "The target is no longer legal")
  | .addMana mana =>
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add mana })
      |>.logMsg s!"{(g.player controller).name} adds {mana}"
  | .searchBasicLandToHand =>
    g.resolveSearchBasicLandToHand controller
  | .gainLandfallCreateElf =>
    match sourceId.bind g.findObject? with
    | some src =>
      if !src.isOnBattlefield then g
      else
        let landfall : TriggeredAbility :=
          .onLandYouControlEntersCreateTokens TokenKind.elf 1
        let g := g.mapObjectStatus src (fun s =>
          { s with grantedTriggeredAbilities :=
            s.grantedTriggeredAbilities.push landfall })
        g.logMsg s!"{src.name} gains landfall"
    | none => g
  | .elvesGetVigilance p =>
    g.forEachControlledCreature controller fun g o =>
      if g.hasSubtype o "Elf" then
        let g := g.pumpPermanent o p 0
        g.mapObjectStatus (g.object! o.id) (·.grantUntilEot Keyword.vigilance)
          |>.logMsg s!"{o.name} gets {signedStat p}/+0 and gains vigilance until end of turn"
      else g
  | .opponentDiscardsNonland =>
    g.withLegalKindTarget controller .opponent targets (fun g t =>
      match t with
      | Target.player pid => g.discardNonlandFrom controller pid
      | _ => g.logMsg "The target is no longer legal")
      sourceId (some "The target is no longer legal")
  | .amassGoblins n =>
    g.amassGoblins controller n
  | .opponentLosesYouGain n =>
    g.withLegalKindTarget controller .opponent targets (fun g t =>
      match t with
      | Target.player pid => g.loseLife pid n |>.gainLife controller n
      | _ => g.logMsg "The target is no longer legal")
      sourceId (some "The target is no longer legal")
  | .grantHexproofWhileRemains =>
    match sourceId with
    | none => g
    | some sid =>
      g.withLegalKindPermanent controller .creatureYouControl targets (fun g o =>
        let g := g.mapObjectStatus o (fun s =>
          { s with hexproofGrantedBy := s.hexproofGrantedBy.push sid })
        g.logMsg s!"{o.name} gains hexproof for as long as the Saga remains")
        sourceId (some "The target is no longer legal")
  | .preventDamageWhileRemains =>
    match sourceId with
    | none => g
    | some sid =>
      g.withLegalKindPermanent controller .creature targets (fun g o =>
        let g := g.mapObjectStatus o (fun s =>
          { s with preventDamageGrantedBy := s.preventDamageGrantedBy.push sid })
        g.logMsg s!"damage that would be dealt by {o.name} is prevented while the Saga remains")
        sourceId none
  | .draw n =>
    g.draw controller n
  | .searchBasicPlainsExileGainLife max life =>
    g.resolveSearchBasicPlainsExile controller sourceId max life
  | .returnLinkedExileToHand =>
    match sourceId.bind g.findObject? with
    | none => g.logMsg "The Saga is no longer in play"
    | some src =>
      match src.linkedExile[0]? with
      | none => g.logMsg "No card is exiled with this Saga"
      | some eid =>
        match g.findObject? eid with
        | none => g.logMsg "The exiled card is no longer there"
        | some card =>
          let owner := card.owner
          let name := card.name
          let (g, _) := g.move eid (.hand owner) none
          let src := g.object! src.id
          let g := g.setObject { src with
            linkedExile := src.linkedExile.filter (· != eid) }
          g.logMsg s!"{name} is put into {(g.player owner).name}'s hand"
  | .grantAttackPumpPerPlainsThisTurn =>
    g.modifyPlayer controller (fun pl =>
      { pl with attackPumpPerPlainsThisTurn := pl.attackPumpPerPlainsThisTurn + 1 })
      |>.logMsg
        s!"Whenever {(g.player controller).name} attacks this turn, a creature they control gets +1/+1 for each Plains they control"
  | .blinkUntilEndStep =>
    g.withLegalKindPermanent controller .creatureOrLandYouControl targets
      (fun g o => g.exileUntilNextEndStep o) sourceId none
  | .treasureThenDragonIfFour =>
    let g := g.createTreasureTokens controller 1
    match sourceId.bind g.findObject? with
    | none => g
    | some src =>
      if !src.isOnBattlefield then g
      else if g.countSubtype controller "Treasure" < 4 then g
      else
        let name := src.name
        let g := g.sacrificeToGraveyard src s!"{name} is sacrificed"
        let (g, tok) := g.createToken controller dragonToken
        g.logMsg s!"{tok.name} enters the battlefield" |>.afterPermanentEnters (g.object! tok.id)
  | .recruit =>
    g.beginRecruit controller
  | .returnCreatureFromGyMvAtMost n =>
    g.withLegalKindTarget controller (.creatureCardInYourGraveyardMvAtMost n) targets
      (fun g t =>
        match t with
        | Target.card oid =>
          match g.findObject? oid with
          | none => g.logMsg "The target is no longer in the graveyard"
          | some o =>
            let name := o.name
            let (g, newId) := g.putOntoBattlefield oid controller
            g.logMsg s!"{name} returns to the battlefield"
              |>.afterPermanentEnters (g.object! newId)
        | _ => g.logMsg "The target is no longer legal")
      sourceId (some "The target is no longer legal")
  | .plusOneUpToOne =>
    g.withLegalKindPermanent controller .creature targets (fun g o =>
      g.addPlusOnePlusOneTo o 1) sourceId none
  | .msh t =>
    g.applyMshChapter controller t targets sourceId
  | .spell e =>
    g.applyEffect controller e targets

/-- Intervening “if” conditions rechecked on resolution (CR 608.2a).
“While you control” attack triggers are not rechecked. -/
def interveningStillHolds (g : Game) (controller : PlayerId)
    (ab : TriggeredAbility) : Bool :=
  let lifeOk :=
    match ab.timing.gainedLifeAtLeast with
    | none => true
    | some n => (g.player controller).lifeGainedThisTurn ≥ n
  let beginCombatFerocious :=
    match ab with
    | .onYourBeginCombatFerociousPlusOne =>
      g.greatestPowerAmongCreatures controller ≥ 4
    | _ => true
  lifeOk && beginCombatFerocious

def applyTriggeredAbility (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target := #[])
    (dividedDamage : Array Nat := #[]) (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none)
    (sourceName : String := "This creature") : Game :=
  if !g.interveningStillHolds controller ab then
    g.logMsg "The intervening condition is no longer true. The ability doesn't resolve."
  else
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
          let g := g.returnToHand oid controller
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
    g.forEachControlledCreature controller fun g o =>
      let g := g.pumpPermanent o pw 0
      let o := g.object! o.id
      g.mapObjectStatus o (·.grantUntilEot Keyword.firstStrike)
        |>.logMsg s!"{o.name} gains first strike until end of turn"
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
  | .exileTarget =>
    g.withLegalKindPermanent controller ab.targetKind targets (fun g o =>
      g.exileForLeaveTrigger sourceId o) sourceId (some "The target is no longer legal")
  | .exileUntilLeaves =>
    match sourceId.bind g.findObject? with
    | some src =>
      if src.isOnBattlefield then
        g.withLegalKindPermanent controller ab.targetKind targets (fun g o =>
          g.exileUntilSourceLeaves sourceId o) sourceId (some "The target is no longer legal")
      else
        g.logMsg "The source has left the battlefield. Nothing is exiled."
    | none =>
      g.logMsg "The source has left the battlefield. Nothing is exiled."
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
    g.forEachControlledCreature controller (fun g o => g.addPlusOnePlusOneTo o 1)
  | .sourceGetsAndTeamTrample p =>
    let g := g.applyOnTriggerSource sourceId (.pump p 0)
    g.grantUntilEotToControlledCreatures controller Keyword.trample "trample"
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
    g.resolveSearchBasicLandToHand controller
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
    let others :=
      g.battlefield.filter (fun o =>
        o.isCreature && o.controlledBy controller && some o.id != sourceId)
    let g := others.foldl (fun acc o => acc.addPlusOnePlusOneTo o 1) g
    if others.isEmpty then g else g.gainLife controller others.size
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
    let defn := g.opponent controller
    let chosen :=
      match targets[0]? with
      | some (Target.permanent id) => some id
      | _ => none
    g.sacrificeLeastPowerCreature defn chosen
  | .createAxe =>
    let (g, _) := g.createToken controller axeToken
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
  | .lookAtTopRevealTypes n types =>
    Id.run do
      let mut g := g
      let pl := g.player controller
      let take := min n pl.library.size
      let ids := pl.library.extract (pl.library.size - take) pl.library.size
      g := g.logMsg s!"{(g.player controller).name} looks at the top {n} cards"
      let picked :=
        ids.find? (fun id =>
          match g.findObject? id with
          | some o =>
            types.any (fun t =>
              t == "permanent" && o.printed.isPermanentCard ||
                o.printed.hasSubtype t ||
                (t == "creature" && o.printed.isCreature))
          | none => false)
      match picked with
      | none => pure ()
      | some id =>
        let name := (g.object! id).name
        let (g', _) := g.move id (.hand controller) none
        g := g'.logMsg s!"{name} is put into {(g'.player controller).name}'s hand"
      return g.shuffleLibrary controller
  | .pumpAndDamageOpponents n =>
    g.applyOnTriggerSource sourceId (.pump 1 1)
      |>.forEachOpponent controller (fun g pid => g.loseLife pid n)
  | .createTappedTreasuresEqualOppArtifacts =>
    let n :=
      g.battlefield.filter (fun o =>
        o.printed.isArtifact && !o.controlledBy controller) |>.size
    g.createTreasureTokens controller n (tapped := true)
  | .gainControlOppUntilEot =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let g := g.giveControlUntilEot o controller
      let g := g.applyPermanentAction (g.object! o.id) .untap
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
  | .cascade =>
    let maxMv :=
      match sourceId with
      | some sid =>
        match g.findObject? sid with
        | some src => src.printed.manaCost.manaValue
        | none => 0
      | none => 0
    g.resolveCascade controller maxMv
  | .belladonnaTokenReward =>
    let n := (g.player controller).belladonnaResolvesThisTurn + 1
    let g := g.modifyPlayer controller (fun pl =>
      { pl with belladonnaResolvesThisTurn := n })
    if n == 1 then
      g.gainLife controller 1
    else if n == 2 then
      g.draw controller 1
    else if n == 3 then
      g.forEachControlledCreature controller (fun g o => g.addPlusOnePlusOneTo o 1)
        |>.logMsg
          s!"{(g.player controller).name} puts a +1/+1 counter on each creature they control"
    else
      g.logMsg
        s!"Belladonna Took's ability has no effect (resolved {n} times this turn)"
  | .bolgMaySacrifice =>
    match sourceId with
    | some sid =>
      { g with pending := .maySacrificeAnotherBolg controller sid }.logMsg
        s!"{(g.player controller).name} may sacrifice another creature (Bolg reflexive trigger)"
    | none => g.logMsg "Bolg is no longer in play"
  | .bolgDealSacrificedPower =>
    let amt := lastKnownPower.getD 0
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let remain := g.toughness o - o.status.damage
      let raw := amt - remain
      let excess : Nat := if raw > 0 then raw.toNat else 0
      let g := g.dealDamageFrom sourceName o amt
      if excess > 0 then
        g.amassGoblins controller excess |>.logMsg
          s!"excess damage {excess} — amass Goblins {excess}"
      else g) "The target is no longer legal"
  | .createSpiritsForEquipped =>
    match sourceId.bind g.findObject? with
    | none => g.logMsg "The Equipment is no longer in play"
    | some eq =>
      let hostOk :=
        match eq.attachedTo.bind g.findObject? with
        | some host =>
          host.isOnBattlefield && host.isLegendary &&
            host.controller == some controller
        | none => false
      let attacking := hostOk
      let g :=
        g.createKindTokens controller .spirit 2 (tapped := true) (attacking := attacking)
      if attacking then
        g.logMsg
          s!"{(g.player controller).name} creates two tapped and attacking Spirit tokens"
      else
        g.logMsg
          s!"{(g.player controller).name} creates two tapped Spirit tokens"
  | .createTreasuresEqualDamagedPlayerArtifacts =>
    let pid := g.lastCombatDamagePlayer.getD (g.opponent controller)
    let n :=
      g.battlefield.filter (fun o =>
        o.printed.isArtifact && o.controlledBy pid) |>.size
    g.createTreasureTokens controller n |>.logMsg
      s!"{(g.player controller).name} creates {n} Treasure token(s) (artifacts that player controls)"
  | .deal1ThenAmassOrcs =>
    let g := g.applyEffect controller (.dealDamage 1) targets
    g.amassOrcs controller 1
  | .untapAttackersExtraCombat =>
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.status.attacking then
          g := g.applyPermanentAction o .untap
      return g.logMsg
        "Attacking creatures untap. An additional combat phase will occur"
  | .eaglesCreateBirds =>
    let n := lastKnownPower.getD 0
    g.createKindTokens controller .birdSoldier n.toNat |>.logMsg
      s!"{(g.player controller).name} creates {n} Bird Soldier token(s)"
  | .allianceMode =>
    match sourceId with
    | none =>
      g.logMsg "The ability is removed from the stack with no effect"
    | some sid =>
      match g.findObject? sid with
      | none =>
        g.logMsg "The ability is removed from the stack with no effect"
      | some src =>
        match (g.unusedAllianceModes src)[0]? with
        | none =>
          g.logMsg
            "all three modes have been chosen this turn. The ability is removed from the stack with no effect"
        | some mode =>
          g.applyAllianceMode sid mode
  | .gollumMode =>
    match sourceId with
    | none =>
      g.logMsg "The ability is removed from the stack with no effect"
    | some sid =>
      match g.findObject? sid with
      | none =>
        g.logMsg "The ability is removed from the stack with no effect"
      | some src =>
        match (g.unusedGollumModes src)[0]? with
        | none =>
          g.logMsg
            "all three modes have been chosen. The ability is removed from the stack with no effect"
        | some mode =>
          g.applyGollumMode sid mode
  | .destroyOtherAmassControllerPower =>
    match targets[0]? with
    | none =>
      g.logMsg
        "No target was chosen. Its controller is undefined and no player amasses Goblins."
    | some (Target.permanent oid) =>
      match g.findObject? oid with
      | none =>
        g.logMsg "The target is no longer legal"
      | some o =>
        if !o.isOnBattlefield then
          g.logMsg "The target is no longer legal"
        else
          let pw := lastKnownPower.getD (g.power o)
          let ctrl := o.controller
          let youControlled := ctrl == some controller
          let g := g.destroyPermanent o
          match ctrl with
          | none => g
          | some pid =>
            let n := if pw > 0 then pw.toNat else 0
            let g := g.amassGoblins pid n
            if youControlled then g.draw controller 1 else g
    | _ =>
      g.logMsg "No target was chosen. Its controller is undefined and no player amasses Goblins."
  | .returnCreatureFromGyToHand =>
    g.withLegalTriggerTarget controller ab sourceId targets fun g t =>
      match t with
      | Target.card oid =>
        match g.findObject? oid with
        | none => g.logMsg "The target is no longer in the graveyard"
        | some o =>
          let name := o.name
          let (g, _) := g.move oid (.hand controller) none
          g.logMsg s!"{name} is returned to {(g.player controller).name}'s hand"
      | _ => g.logMsg "The target is no longer legal"
  | .discardHandDrawDamageIfStory =>
    let n := (g.player controller).hand.size
    let g := g.mayDiscardHandDrawThatMany controller true
    if g.hasEnduringStory controller then
      g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid n)
    else g
  | .plusOneAndLifelink =>
    match targets[0]? with
    | some (Target.permanent oid) => g.applyBardBowman oid
    | _ => g.logMsg "The target is no longer legal"
  | .wolfPlusOneOrTreasure =>
    match targets[0]? with
    | some (Target.permanent oid) =>
      match g.findObject? oid with
      | some o =>
        if g.hasSubtype o "Wolf" then g.addPlusOnePlusOneTo o 1
        else g.createTreasureTokens controller 1
      | none => g.createTreasureTokens controller 1
    | _ => g.createTreasureTokens controller 1
  | .trampleCounterBecomeBear =>
    let g :=
      match targets[0]? with
      | some (Target.permanent oid) =>
        match g.findObject? oid with
        | some o =>
          let extra :=
            if g.hasSubtype o "Bear" then o.status.additionalSubtypes
            else o.status.additionalSubtypes.push "Bear"
          let g := g.setObject { o with status :=
            { o.status with
              trampleCounters := o.status.trampleCounters + 1
              additionalSubtypes := extra } }
          g.logMsg s!"{o.name} gets a trample counter and becomes a Bear"
        | none => g
      | _ => g
    if g.countSubtype controller "Bear" >= 3 then g.draw controller 2 else g
  | .castFromGyArtifactInstantSorcery =>
    match (g.player controller).graveyard.findSome? (fun id =>
      match g.findObject? id with
      | some o =>
        if o.printed.isArtifact || o.printed.isInstantOrSorcery then some id
        else none
      | none => none) with
    | none => g.logMsg s!"{(g.player controller).name} has no artifact, instant, or sorcery in the graveyard"
    | some id => g.castAsPartOfResolution controller id
  | .millThenSubtypeToHand n subtype =>
    let before := (g.player controller).graveyard
    let g := g.mill controller n
    let after := (g.player controller).graveyard
    let newIds := after.filter (fun id => !before.contains id)
    newIds.foldl (fun acc id =>
      match acc.findObject? id with
      | some o =>
        if o.printed.hasSubtype subtype then
          let name := o.name
          let (acc, _) := acc.move id (.hand controller) none
          acc.logMsg s!"{name} is put into {(acc.player controller).name}'s hand"
        else acc
      | none => acc) g
  | .exileOppNonlandEachUntilLeaves =>
    match sourceId.bind g.findObject? with
    | none => g.logMsg "The source has left the battlefield. Nothing is exiled."
    | some src =>
      if !src.isOnBattlefield then
        g.logMsg "The source has left the battlefield. Nothing is exiled."
      else
        targets.foldl (fun acc t =>
          match t with
          | Target.permanent oid =>
            match acc.findObject? oid with
            | some o => acc.exileUntilSourceLeaves sourceId o
            | none => acc
          | _ => acc) g
  | .plusOneEqualLastKnownMv =>
    let n := (lastKnownPower.getD 0).toNat
    g.applyOnPermanent controller ab.targetKind targets (.plusOne n) sourceId
      (some "The target is no longer legal")
  | .createAxeAttach =>
    let (g, tok) := g.createToken controller axeToken
    g.withLegalKindPermanent controller .creatureYouControl targets (fun g host =>
      g.attachSourceTo tok host) sourceId (some "No creature was chosen")
  | .equippedAttackersGainDoubleStrike =>
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.status.attacking && o.attachedTo.isSome ||
            (o.status.attacking &&
              g.battlefield.any (fun eq => eq.attachedTo == some o.id)) then
          if o.isCreature && o.status.attacking &&
              g.battlefield.any (fun eq => eq.attachedTo == some o.id) then
            g := g.mapObjectStatus o (·.grantUntilEot Keyword.doubleStrike)
            g := g.logMsg s!"{o.name} gains double strike until end of turn"
      return g
  | .tapEnchantedRemoveCounters =>
    match sourceId.bind g.findObject? with
    | none => g
    | some src =>
      match src.attachedTo.bind g.findObject? with
      | none => g.logMsg "Nothing is enchanted"
      | some host =>
        let g := g.applyPermanentAction host .tap
        let host := g.object! host.id
        let g := g.setObject { host with status :=
          { host.status with
            plusOnePlusOne := 0
            hope := 0
            hone := 0
            shadow := 0
            burden := 0
            quest := 0
            trampleCounters := 0
            influence := 0
            lore := 0
            indestructibleCounters := 0
            lifelinkCounters := 0 } }
        g.logMsg s!"counters are removed from {host.name}"
  | .revealTopPutRandomCreature n =>
    Id.run do
      let mut g := g
      let pl := g.player controller
      let take := min n pl.library.size
      let ids := pl.library.extract (pl.library.size - take) pl.library.size
      let creatures :=
        ids.filter (fun id =>
          match g.findObject? id with
          | some o => o.printed.isCreature
          | none => false)
      if g.norandom && creatures.size > 1 then
        return { g with
          pending := .resolveRandom (.chooseObject creatures)
          afterRandom := .putCreatureThenShuffle controller }
          |>.logMsg
            s!"{(g.player controller).name} reveals the top {n} cards and puts a random creature onto the battlefield"
      match creatures[0]? with
      | none =>
        g := g.logMsg "No creature card was revealed"
      | some cid =>
        let name := (g.object! cid).name
        let (g', _) := g.putOntoBattlefield cid controller
        g := g'.logMsg s!"{name} enters the battlefield"
        g := g.afterPermanentEnters (g.object! cid)
      for id in ids do
        if creatures[0]? != some id then
          match g.findObject? id with
          | some o =>
            if o.zone == .library controller then
              let (g', _) := g.move id (.library controller) none
              g := g'
          | none => pure ()
      return g.shuffleLibrary controller
  | .beginCombatIfDrawnTwoPump =>
    if (g.player controller).cardsDrawnThisTurn < 2 then g
    else
      g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
        let g := g.pumpPermanent o 3 0
        let o := g.object! o.id
        let g := g.mapObjectStatus o (·.grantUntilEot Keyword.firstStrike)
        g.logMsg s!"{o.name} gains first strike until end of turn")
        "The target is no longer legal"
  | .mountainQuestDragon =>
    g.withTriggerSource sourceId fun g src =>
      let g := g.setObject { src with status :=
        { src.status with quest := src.status.quest + 1 } }
      let src := g.object! src.id
      let g := g.logMsg s!"{src.name} gets a quest counter ({src.status.quest})"
      if src.status.quest >= 6 then
        let name := src.name
        let (g, _) := g.move src.id (.graveyard src.owner) none
        let g := g.logMsg s!"{name} is sacrificed"
        match (g.player controller).hand.findSome? (fun id =>
          match g.findObject? id with
          | some o => if o.printed.hasSubtype "Dragon" then some id else none
          | none => none) with
        | some id =>
          let (g, _) := g.putOntoBattlefield id controller
          g.afterPermanentEnters (g.object! id)
        | none =>
          g.resolveLibrarySearch controller (fun c => c.hasSubtype "Dragon")
            "Dragon card" fun g cardId =>
              let (g, _) := g.putOntoBattlefield cardId controller
              g.afterPermanentEnters (g.object! cardId)
      else g
  | .millPlayer n =>
    g.withLegalTriggerTarget controller ab sourceId targets (fun g t =>
      match t with
      | Target.player pid => g.mill pid n
      | _ => g.logMsg "The target is no longer legal")
  | .treasuresPerChosenType =>
    let n := (g.permanentsOf controller).filter (·.isCreature) |>.size
    g.createTreasureTokens controller n
  | .revealUntilCreature =>
    Id.run do
      let mut g := g
      let mut found : Option ObjectId := none
      let mut rest : Array ObjectId := #[]
      while found.isNone && !(g.player controller).library.isEmpty do
        let top := (g.player controller).library.back!
        let o := g.object! top
        g := g.logMsg s!"{(g.player controller).name} reveals {o.name}"
        if o.printed.isCreature then
          found := some top
        else
          let (g', newId) := g.move top .exile none
          g := g'
          rest := rest.push newId
      match found with
      | none =>
        return rest.foldl (fun acc id => (acc.move id (.library controller) none).1) g
      | some cid =>
        let o := g.object! cid
        let lands := g.landsYouControl controller
        let (g', newId) :=
          if o.printed.manaValue <= lands then
            g.putOntoBattlefield cid controller
          else
            g.move cid (.hand controller) none
        g := g'
        g := g.logMsg s!"{o.name} is put into play or hand"
        if o.printed.manaValue <= lands then
          g := g.afterPermanentEnters (g.object! newId)
        return rest.foldl (fun acc id => (acc.move id (.library controller) none).1) g
  | .attackSacPlusOneEqualPower =>
    match (g.permanentsOf controller).find? (fun o =>
      o.isCreature && some o.id != sourceId) with
    | none => g.logMsg "No other creature to sacrifice"
    | some sac =>
      let pw := g.power sac
      let (g, _) := g.move sac.id (.graveyard sac.owner) none
      g.applyOnTriggerSource sourceId (.plusOne pw.toNat)
  | .amassGoblinsEqualPower =>
    let n := (lastKnownPower.getD 0).toNat
    g.amassGoblins controller n
  | .payReturnFromGy =>
    g.returnSourceFromGraveyard sourceId controller (toHand := true)
  | .lootLandEntersTapped =>
    let g := g.draw controller 1
    g.beginDiscardCards #[controller]
  | .honePerOppAttach =>
    let opp :=
      match targets[0]? with
      | some (Target.player pid) => pid
      | some (Target.permanent _) => g.opponent controller
      | _ => g.opponent controller
    let n := (g.permanentsOf opp).filter (·.isCreature) |>.size
    let g :=
      g.withTriggerSource sourceId fun g src =>
        g.mapObjectStatus src (fun s => { s with hone := s.hone + n })
          |>.logMsg s!"{src.name} gets {n} hone counter(s)"
    match targets[1]?, targets[0]? with
    | some (Target.permanent hid), _
    | none, some (Target.permanent hid) =>
      match g.findObject? hid, sourceId.bind g.findObject? with
      | some host, some src =>
        if host.isCreature then g.attachSourceTo src host else g
      | _, _ => g
    | _, _ => g
  | .damageTargetOpponent n =>
    g.withLegalTriggerTarget controller ab sourceId targets (fun g t =>
      match t with
      | Target.player pid => g.dealDamageToPlayer pid n
      | _ => g.logMsg "The target is no longer legal")
  | .millThatManyLost =>
    match g.lastLifeLost with
    | some (pid, n) => g.mill pid n
    | none => g
  | .drawPerFatGraveyard =>
    g.drawPerSevenCardGraveyard controller
  | .copySelfNonlegendary =>
    match sourceId.bind g.findObject? with
    | none => g
    | some src =>
      if src.printed.isToken then g
      else
        let face := { src.printed with
          isToken := true
          supertypes := src.printed.supertypes.filter (· != .legendary) }
        let (g, _) := g.createToken controller face
        let (g, _) := g.createToken controller face
        g.logMsg s!"two nonlegendary tokens that are copies of {src.name} are created"
  | .maySacDrawTreasure =>
    match (g.permanentsOf controller).find? (fun o =>
      (o.isCreature || o.printed.isArtifact) && some o.id != sourceId) with
    | none => g.logMsg "Nothing to sacrifice"
    | some sac =>
      let g := g.sacrificeToGraveyard sac
        s!"{(g.player controller).name} sacrifices {sac.name}"
      let g := g.draw controller 1
      g.createTreasureTokens controller 1
  | .targetOpponentLosesLife n =>
    g.withLegalTriggerTarget controller ab sourceId targets (fun g t =>
      match t with
      | Target.player pid => g.loseLife pid n
      | _ => g.logMsg "The target is no longer legal")
  | .attachEquipmentThenFight =>
    match targets[0]? with
    | some (Target.permanent hid) =>
      match g.findObject? hid with
      | none => g.logMsg "The target is no longer legal"
      | some host =>
        let eqs :=
          (g.permanentsOf controller).filter (fun o => o.printed.isEquipment)
        let g := eqs.foldl (fun acc eq => acc.attachSourceTo eq host) g
        let host := g.object! host.id
        let pw := g.power host
        match (g.battlefield.find? (fun o =>
          o.isCreature && !o.controlledBy controller)) with
        | none => g
        | some opp => g.dealDamageFrom host.name opp pw
    | _ => g.logMsg "The target is no longer legal"
  | .plusOneVigilance n =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let g := g.addPlusOnePlusOneTo o n
      let o := g.object! o.id
      g.mapObjectStatus o (·.grantUntilEot Keyword.vigilance)
        |>.logMsg s!"{o.name} gains vigilance until end of turn")
  | .drawThenDiscardN n =>
    let g := g.draw controller n
    g.beginDiscardCards #[controller]
  | .returnAsArtifact =>
    match sourceId.bind g.findObject? with
    | none => g
    | some src =>
      if src.zone != .graveyard src.owner then g
      else
        let (g, newId) := g.putOntoBattlefield src.id controller
        let o := g.object! newId
        let g := g.setObject { o with status :=
          { o.status with additionalCreature := false, onlyFoodArtifact := false } }
        let o := g.object! newId
        -- Force artifact-only by using additionalArtifact and clearing creature
        -- via onlyFoodArtifact-style flag is too strong; grant artifact type.
        let g := g.mapObjectStatus o (fun s => { s with returnedAsArtifact := true })
        g.logMsg s!"{o.name} returns as an artifact"
  | .mayDrawXDiscard2 =>
    let n := (lastKnownPower.getD 0).toNat
    let g := g.draw controller n
    let g := g.beginDiscardCards #[controller]
    g.beginDiscardCards #[controller]
  | .plusOneEachIfCityBlessing =>
    let n := if (g.player controller).citysBlessing then 2 else 1
    (g.permanentsOf controller).foldl (fun acc o =>
      if o.isCreature then acc.addPlusOnePlusOneTo o n else acc) g
  | .castInstantSorceryFromHand =>
    let wizards :=
      (g.permanentsOf controller).filter (fun o =>
        o.isLegendary && g.hasSubtype o "Wizard") |>.size
    let maxMv := wizards * 2
    match (g.player controller).hand.findSome? (fun id =>
      match g.findObject? id with
      | some o =>
        if o.printed.isInstantOrSorcery && o.printed.manaValue <= maxMv then some id
        else none
      | none => none) with
    | none => g.logMsg "No instant or sorcery to cast"
    | some id => g.castAsPartOfResolution controller id
  | .drawPlusOneSource =>
    let g := g.draw controller 1
    g.applyOnTriggerSource sourceId (.plusOne 1)
  | .exileLandsThenReturnTapped =>
    Id.run do
      let mut g := g
      for t in targets do
        match t with
        | Target.permanent oid =>
          match g.findObject? oid with
          | none => pure ()
          | some o =>
            if o.controlledBy controller && o.printed.isLand then
              let owner := o.owner
              let name := o.name
              let (g', newId) := g.move oid .exile none
              let (g'', retId) := g'.move newId .battlefield (some owner)
              g := g''
              g := g.setObject { (g.object! retId) with
                status := { (g.object! retId).status with tapped := true } }
              g := g.logMsg s!"{name} is exiled, then returned tapped"
              g := g.afterLandEnters (g.object! retId)
        | _ => pure ()
      return g
  | .castInstantSorceryMvAtMost =>
    let maxMv := (lastKnownPower.getD 0).toNat
    match (g.player controller).hand.findSome? (fun id =>
      match g.findObject? id with
      | some o =>
        if o.printed.isInstantOrSorcery && o.printed.manaValue <= maxMv then some id
        else none
      | none => none) with
    | none => g.logMsg "No instant or sorcery to cast"
    | some id => g.castAsPartOfResolution controller id
  | .grimaImpulse =>
    let victim := g.lastCombatDamagePlayer.getD (g.opponent controller)
    g.grimaExileUntilInstantOrSorcery controller victim true
  | .palantir =>
    let tgt :=
      match targets[0]? with
      | some (Target.player pid) => some pid
      | _ => none
    match sourceId with
    | none => g.logMsg "The source is no longer in play"
    | some sid =>
      let g := g.applyPalantir sid tgt
      match tgt with
      | none => g
      | some _ =>
        -- Opponent declines the optional draw; mill and lose life.
        match g.findObject? sid with
        | none => g
        | some src =>
          let n := src.status.influence
          let before := (g.player controller).graveyard.size
          let g := g.mill controller n
          let milled := (g.player controller).graveyard.size - before
          let mv :=
            (g.player controller).graveyard.extract
              ((g.player controller).graveyard.size - milled)
              (g.player controller).graveyard.size
            |>.foldl (fun acc id =>
              acc + (g.object! id).printed.manaValue) 0
          match tgt with
          | some pid => g.loseLife pid mv
          | none => g
  | .millThenCopy =>
    let opps := (g.livingOpponents controller).map (·.id)
    let (g, milled) := g.millThenReflexive opps 2
    if !milled then g
    else
      match (opps.foldl (fun acc pid =>
        acc ++ (g.player pid).graveyard) #[]).findSome? (fun id =>
          match g.findObject? id with
          | some o =>
            if o.printed.isEnchantment || o.printed.isInstant || o.printed.isSorcery then
              some id
            else none
          | none => none) with
      | none => g
      | some id =>
        let o := g.object! id
        let (g, newId) := g.move id .exile none
        let g := g.logMsg s!"{o.name} is exiled"
        g.castAsPartOfResolution controller newId
  | .amassOrcs n =>
    g.amassOrcs controller n
  | .ringTempts =>
    g.temptWithTheRing controller
  | .mayDiscardHandDraw n =>
    let g := g.mayDiscardHandDrawThatMany controller true
    if (g.player controller).hand.size == 0 && n > 0 then
      g.draw controller n
    else g
  | .treasuresEqualLastKnown =>
    let n := (lastKnownPower.getD 0).toNat
    g.createTreasureTokens controller n
  | .protectionEverything =>
    g.modifyPlayer controller (fun pl => { pl with protectionFromEverything := true })
      |>.logMsg s!"{(g.player controller).name} gains protection from everything"
  | .loseLifePerBurden =>
    match sourceId.bind g.findObject? with
    | none => g
    | some src => g.loseLife controller src.status.burden
  | .revealSaga =>
    Id.run do
      let mut g := g
      let mut found : Option ObjectId := none
      let mut rest : Array ObjectId := #[]
      while found.isNone && !(g.player controller).library.isEmpty do
        let top := (g.player controller).library.back!
        let o := g.object! top
        g := g.logMsg s!"{(g.player controller).name} reveals {o.name}"
        if o.printed.saga.isSome then found := some top
        else
          let (g', newId) := g.move top .exile none
          g := g'
          rest := rest.push newId
      match found with
      | none =>
        return rest.foldl (fun acc id => (acc.move id (.library controller) none).1) g
      | some sid =>
        let (g', newId) := g.putOntoBattlefield sid controller
        g := g'.afterPermanentEnters (g.object! newId)
        return rest.foldl (fun acc id => (acc.move id (.library controller) none).1) g
  | .sacDamagersRingTempts =>
    let g :=
      (g.livingOpponents controller).foldl (fun acc pl =>
        acc.beginSacrificeCreature pl.id) g
    g.temptWithTheRing controller
  | .chapter e =>
    g.applyChapterEffect controller e sourceId targets
  | .pumpTargetPerPlains =>
    let n :=
      (g.permanentsOf controller).filter (fun o => g.hasSubtype o "Plains") |>.size
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      g.pumpPermanent o n n)
      "No target was chosen"
  | .investigate =>
    let (g, _) := g.createToken controller clueToken
    g.logMsg s!"{(g.player controller).name} investigates"
  | .plusOneOnSourceAndDraw =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let g := g.setObject { o with status := { o.status with
        plusOnePlusOne := o.status.plusOnePlusOne + 1 } }
      g.draw controller 1
  | .connive =>
    g.applyConnive controller sourceId
  | .targetConnive =>
    match targets[0]? with
    | some (Target.permanent id) => g.applyConnive controller (some id)
    | _ => g.applyConnive controller sourceId
  | .pumpCause p t =>
    match (g.battlefield.find? (fun o => o.status.attacking && o.controlledBy controller)) with
    | some o => g.pumpPermanent o p t
    | none => g
  | .othersOfSubtypeGetEqualSourceToughness subtype =>
    let (x, srcId?) :=
      match sourceId.bind g.findObject? with
      | some src =>
        if src.isOnBattlefield then (g.toughness src, some src.id)
        else (lastKnownToughness.getD (g.toughness src), some src.id)
      | none => (lastKnownToughness.getD (0 : Int), none)
    g.foldBattlefield (fun o =>
        o.controlledBy controller &&
          (match srcId? with
           | some sid => o.id != sid
           | none => true) &&
          g.hasSubtype o subtype)
      (fun g o => g.pumpPermanent o x x)
  | .drawIfAttackedOrEnteredSubtype subtype =>
    let pl := g.player controller
    if (subtype == "Hero" && (pl.attackedWithHeroThisTurn || pl.heroEnteredThisTurn)) ||
        (g.battlefield.any (fun o =>
          o.controlledBy controller && g.hasSubtype o subtype &&
            (o.status.attacking || o.status.enteredThisTurn))) then
      g.draw controller 1
    else g
  | .scryAndPlan n =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let g := g.setObject { o with status := { o.status with plan := o.status.plan + 1 } }
      let o := g.object! o.id
      let g := g.putMatchingSourceTriggers controller o (.nthPlanCounter o.status.plan)
      g.beginScry controller n
  | .lootAndPlan =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let g := g.setObject { o with status := { o.status with plan := o.status.plan + 1 } }
      let o := g.object! o.id
      let g := g.putMatchingSourceTriggers controller o (.nthPlanCounter o.status.plan)
      let g := g.draw controller 1
      g.beginDiscardCards #[controller]
  | .createVillainAndPlan =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let g := g.setObject { o with status := { o.status with plan := o.status.plan + 1 } }
      let o := g.object! o.id
      let g := g.putMatchingSourceTriggers controller o (.nthPlanCounter o.status.plan)
      let (g, _) := g.createToken controller villain21menaceToken
      g
  | .drainAndPlan n =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let g := g.setObject { o with status := { o.status with plan := o.status.plan + 1 } }
      let o := g.object! o.id
      let g := g.putMatchingSourceTriggers controller o (.nthPlanCounter o.status.plan)
      let g := (g.livingOpponents controller).foldl (fun acc pl =>
        acc.loseLife pl.id n) g
      g.modifyPlayer controller (fun pl => { pl with life := pl.life + (n : Int) })
  | .drawLoseLifeAndPlan =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let g := g.setObject { o with status := { o.status with plan := o.status.plan + 1 } }
      let o := g.object! o.id
      let g := g.putMatchingSourceTriggers controller o (.nthPlanCounter o.status.plan)
      let g := g.draw controller 1
      g.loseLife controller 1
  | .treasureTappedAndPlan =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let g := g.setObject { o with status := { o.status with plan := o.status.plan + 1 } }
      let o := g.object! o.id
      let g := g.putMatchingSourceTriggers controller o (.nthPlanCounter o.status.plan)
      let (g, _) := g.createToken controller treasureToken (tapped := true)
      g
  | .plusOneOnTargetAndPlan =>
    g.withSourceOnBattlefield sourceId fun g src =>
      g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
        let src := g.object! src.id
        let g := g.setObject { src with status :=
          { src.status with plan := src.status.plan + 1 } }
        let src := g.object! src.id
        let g := g.putMatchingSourceTriggers controller src
          (.nthPlanCounter src.status.plan)
        g.mapObjectStatus o (fun s => { s with plusOnePlusOne := s.plusOnePlusOne + 1 }))
        "The target is no longer legal. You won't put counters on anything."
  | .planFinishDrawPlusOneEach =>
    let g :=
      match sourceId.bind g.findObject? with
      | some o =>
        if o.isOnBattlefield then g.sacrificeToGraveyard o "the Plan is completed"
        else g.logMsg s!"{o.name} is no longer on the battlefield"
      | none =>
        g.logMsg "The Plan is no longer on the battlefield"
    let g := g.draw controller 1
    g.foldBattlefield (fun c => c.controlledBy controller && c.isCreature)
      (fun g c => g.mapObjectStatus c (fun s =>
        { s with plusOnePlusOne := s.plusOnePlusOne + 1 }))
  | .planFinishReturnInstants =>
    g.sacrificePlanThenQueueReflexive controller sourceId 11
  | .planFinishControlOpponent =>
    g.sacrificePlanThenQueueReflexive controller sourceId 4
  | .planFinishExileTopCast =>
    g.sacrificePlanThenQueueReflexive controller sourceId 5
  | .planFinishCreateRobots n =>
    let g :=
      match sourceId.bind g.findObject? with
      | some o =>
        if o.isOnBattlefield then g.sacrificeToGraveyard o "the Plan is completed"
        else g.logMsg s!"{o.name} is no longer on the battlefield"
      | none =>
        g.logMsg "The Plan is no longer on the battlefield"
    Id.run do
      let mut g := g
      for _ in [0:n] do
        let (g', _) := g.createToken controller robotVillain22Token
        g := g'
      return g
  | .planFinishDividedDamage _n =>
    g.sacrificePlanThenQueueReflexive controller sourceId 10
  | .planFinishIndestructibleOnTarget =>
    g.sacrificePlanThenQueueReflexive controller sourceId 3
  | .drawAndLoseLife1 =>
    let g := g.draw controller 1
    g.loseLife controller 1
  | .msh t =>
    g.applyMshTrigger controller t sourceId targets sourceName lastKnownPower

/-- Put attack-triggered abilities of `attackerIds` onto the stack (CR 508.2),
including “whenever you attack with one or more Elves” (once if any Elf attacks). -/
def putAttackTriggersOnStack (g : Game) (p : PlayerId) (attackerIds : Array ObjectId) : Game :=
  Id.run do
    let mut g := g
    for id in attackerIds do
      let o := g.object! id
      let skipIronMan :=
        o.printed.triggeredAbilities.any (fun
          | .msh .wheneverIronManAttacks =>
            !(g.player p).artifactEnteredThisTurn
          | _ => false)
      if !skipIronMan then
        g := g.putMatchingSourceTriggers p o .attacking
          (some (g.snapshotPower o)) (some (g.snapshotToughness o))
    let attackedWithElves := attackerIds.any (fun id => g.hasSubtype (g.object! id) "Elf")
    if attackedWithElves then
      g := g.putControlledTriggers p .youAttackWithElves
    let attacksSamePlayer :=
      attackerIds.any (fun id =>
        match (g.object! id).status.attackingWhom with
        | none => attackerIds.size >= 2
        | some d =>
          (attackerIds.filter (fun id' =>
            (g.object! id').status.attackingWhom == some d)).size >= 2)
    if attacksSamePlayer then
      g := g.putControlledTriggers p .youAttackWithTwoOrMore
    if !attackerIds.isEmpty then
      if attackerIds.any (fun id => g.hasSubtype (g.object! id) "Hero") then
        g := g.modifyPlayer p (fun pl => { pl with attackedWithHeroThisTurn := true })
      let merfolkDefenders :=
        attackerIds.foldl (fun acc id =>
          let o := g.object! id
          if !g.hasSubtype o "Merfolk" then acc
          else
            let d := o.status.attackingWhom.getD g.defendingPlayer
            if acc.any (· == d) then acc else acc.push d)
          (#[] : Array PlayerId)
      for _ in merfolkDefenders do
        g := g.putControlledTriggers p .merfolkAttackPlayer
      for id in attackerIds do
        let o := g.object! id
        if g.battlefield.any (fun eq =>
            eq.printed.isEquipment && eq.attachedTo == some o.id &&
              eq.controlledBy p) then
          g := g.putControlledTriggers p .equippedCreatureYouControlAttacks
      g := g.putControlledTriggers p .youAttack
      let pumps := (g.player p).attackPumpPerPlainsThisTurn
      if pumps > 0 then
        let src :=
          match (g.permanentsOf p).find? (fun o => o.printed.saga.isSome) with
          | some o => o
          | none =>
            { printed := { name := "Roads Go Ever, Ever On", types := #[.enchantment] }
              id := ⟨0⟩, owner := p, controller := some p, zone := .battlefield }
        for _ in [0:pumps] do
          g := g.queueTrigger p src .onYouAttackPumpTargetPerPlains .youAttack
    -- Destination does not matter: two attackers at different players
    -- still are not attacking alone (MSH 223).
    let attackingNow :=
      (g.permanentsOf p).filter (fun o => o.isCreature && o.status.attacking)
    if attackingNow.size == 1 then
      let attacker := attackingNow[0]!
      let aid := attacker.id
      for o in g.permanentsOf p do
        g := g.putMatchingSourceTriggers p o .creatureYouControlAttacksAlone
          (cause := some attacker)
        if o.attachedTo == some aid then
          g := g.putMatchingSourceTriggers p o .equippedAttacksAlone
    let totalPower :=
      attackerIds.foldl (fun acc id => acc + g.snapshotPower (g.object! id)) 0
    if totalPower >= 12 then
      g := g.putControlledTriggers p .youAttackWithTotalPower
    for id in attackerIds do
      for eq in g.battlefield do
        if eq.attachedTo == some id then
          match eq.controller with
          | some c =>
            g := g.putMatchingSourceTriggers c eq .equippedAttacks
          | none => pure ()
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
          obj.lastKnownPower
        -- CR 608.2m: after resolution the ability ceases to exist.
        g.ceaseToExist obj.id
      else if let some t := obj.triggeredAbility then
        let srcName := obj.printed.name.replace "'s ability" ""
        let g := g.applyTriggeredAbility entry.controller t obj.sourceId
          entry.targets entry.dividedDamage obj.lastKnownPower obj.lastKnownToughness srcName
        let g := g.ceaseToExist obj.id
        match t with
        | .sagaChapter n _ =>
          match obj.sourceId.bind g.findObject? with
          | some src =>
            match src.printed.saga, src.controller with
            | some s, some p =>
              if n == s.finalChapterNumber then g.finishSagaFinalChapter p else g
            | _, _ => g
          | none => g
        | _ => g
      else
        let g :=
          match obj.giftPromisedTo, obj.printed.isInstantOrSorcery with
          | some to, true => g.givePromisedGift to
          | _, _ => g
        let g :=
          match spellEffectOf obj entry.chosenMode with
          | some e => g.applyEffect entry.controller e entry.targets
            (castFromGraveyard := obj.castFromGraveyard)
            (kicked := obj.kicked)
            (giftPromised := obj.giftPromisedTo.isSome)
            (chosenX := obj.chosenX.getD 0)
          | none => g
        if obj.isAdventureSpell then
          g.resolveAdventureSpell entry (g.object! obj.id)
        else if obj.printed.isAura then
          g.resolveAuraSpell entry obj
        else if obj.printed.isPermanentCard && !obj.printed.isLand then
          let sick := !obj.printed.keywords.haste
          let sneak := obj.sneakPaid
          let sneakWhom := obj.sneakAttackWhom
          let (g, newId) := g.putOntoBattlefield obj.id entry.controller
            (tapped := sneak || g.entersTapped entry.controller obj.printed)
            (summoningSick := sick)
          let o := g.object! newId
          let g :=
            if sneak then
              g.setObject { o with status := { o.status with
                attacking := true
                attackingWhom := sneakWhom } }
            else g
          let o := g.object! newId
          let g := g.logMsg s!"{o.name} enters the battlefield"
          g.afterPermanentEnters (g.object! newId)
        else if obj.castFromGraveyard then
          let (g, _) := g.move obj.id .exile none
          g.logMsg s!"{obj.name} is exiled (flashback)"
        else
          g.moveToOwnerGraveyard obj s!"{obj.name} goes to the graveyard"

def declareAttackers (g : Game) (p : PlayerId) (ids : Array ObjectId)
    (defender : Option PlayerId := none) (each : Array (Option PlayerId) := #[]) :
    Except String Game := do
  if g.pending != .declareAttackers || g.priorityInstead g.activePlayer != p then
    throw "Not time to declare attackers"
  let mut g := g
  for i in [0:ids.size] do
    let id := ids[i]!
    let o := g.object! id
    if !g.canAttack o then
      throw s!"{o.name} cannot attack"
    let want :=
      match each[i]? with
      | some (some d) => some d
      | some none => defender
      | none => defender
    let dest ← g.resolveAttackDestination p want
    g := g.setObject { o with status := { o.status with
      attacking := true
      attackingWhom := some dest
      declaredAsAttackerThisTurn := true
      tapped := o.status.tapped || !g.hasVigilance o } }
    g := g.logMsg
      s!"{g.player p |>.name} attacks {(g.player dest).name} with {o.name}"
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
  if p != g.currentBlockersPlayer then
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
  let rest := g.blockersQueue.extract 1 g.blockersQueue.size
  if rest.isEmpty then
    return { g with pending := .none, blockersQueue := #[] } |>.receivePriority g.activePlayer
  else
    return { g with pending := .declareBlockers, blockersQueue := rest }

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
  let defender := source.status.attackingWhom.getD g.defendingPlayer
  let playerDmg := if (g.player defender).lost then 0 else dmg
  if forAttackers then
    let blockers := g.blockersOf source.id
    if blockers.isEmpty then
      if source.status.blocked && !g.hasTrample source then
        { source := source.id }
      else
        { source := source.id, toPlayer := playerDmg }
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
        let toPlayer := if (g.player defender).lost then 0 else remaining
        return { source := source.id, toCreatures := toCreatures, toPlayer := toPlayer }
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
  let defender := src.status.attackingWhom.getD g.defendingPlayer
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
      else if (g.player defender).lost then
        if asgn.toPlayer != 0 then
          throw s!"combat damage isn't assigned to a player who has left the game (CR 800.4e)"
      else if asgn.toPlayer != dmg then
        throw s!"{src.name} must assign combat damage equal to its power (CR 510.1a)"
    else
      if (g.player defender).lost then
        if asgn.toPlayer != 0 then
          throw s!"combat damage isn't assigned to a player who has left the game (CR 800.4e)"
        if toCreatures > dmg then
          throw s!"{src.name} must assign combat damage equal to its power (CR 510.1a)"
      else if toCreatures + asgn.toPlayer != dmg then
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
    for asgn in g.assignedCombatDamage do
      let src := g.object! asgn.source
      let defn :=
        match src.status.attackingWhom with
        | some pid => pid
        | none => g.defendingPlayer
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
      if g.sourceDamagePrevented src then
        g := g.logMsg s!"combat damage from {src.name} is prevented"
      else
        for (tid, amt) in asgn.toCreatures do
          if amt > 0 then
            let amt := g.replacedDamageAmount src amt (combat := true)
            let t := g.object! tid
            g := g.markDamageOn t amt
              s!"{src.name} deals {amt} combat damage to {t.name}"
              (deathtouch := g.hasDeathtouch src) (combat := true)
            totalDealt := totalDealt + amt
      if !g.sourceDamagePrevented src && asgn.toPlayer > 0 &&
          !(g.player defn).lost then
        let toPlayer := g.replacedDamageAmount src asgn.toPlayer (combat := true)
        let pl := g.player defn
        g := g.setPlayer { pl with life := pl.life - toPlayer }
        totalDealt := totalDealt + toPlayer
        if src.status.blocked then
          g := g.logMsg
            s!"{src.name} tramples for {toPlayer} to {pl.name} ({(g.player defn).life} life)"
        else
          g := g.logMsg
            s!"{src.name} deals {toPlayer} combat damage to {pl.name} ({(g.player defn).life} life)"
      if g.hasLifelink src && totalDealt > 0 then
        match src.controller with
        | some pid => g := g.gainLife pid totalDealt.toNat
        | none => pure ()
      if asgn.toPlayer > 0 && !(g.player defn).lost then
        match src.controller with
        | some pid =>
          g := { g with lastCombatDamagePlayer := some defn }
          g := g.putMatchingSourceTriggers pid src .dealsCombatDamageToPlayer
          g := g.putMatchingSourceTriggers pid src .dealsCombatDamageToPlayerOrBattle
          if src.isCreature then
            for o in g.permanentsOf pid do
              for ab in o.printed.triggeredAbilities do
                match ab with
                | TriggeredAbility.onSubtypeYouControlCombatDamageCreateTokens
                    subtype _ _ =>
                  if o.id != src.id && g.hasSubtype src subtype then
                    g := g.queueTrigger pid o ab .dealsCombatDamageToPlayerOrBattle
                | _ => pure ()
          if g.hasSubtype src "Army" then
            g := g.putControlledTriggers pid .armyYouControlCombatDamage
          for eq in g.battlefield do
            if eq.attachedTo == some src.id then
              match eq.controller with
              | some c =>
                g := g.putMatchingSourceTriggers c eq
                  .equippedDealsCombatDamageToPlayer
                  (some asgn.toPlayer)
              | none => pure ()
          if src.status.combatDamageCreatesTreasure then
            g := g.createTreasureTokens pid asgn.toPlayer.toNat
          g := g.putControlledTriggers defn .combatDamageToYou
          g := { g with lastLifeLost := some (defn, asgn.toPlayer.toNat) }
          g := g.livingPlayers.foldl (fun acc pl =>
            acc.putControlledTriggers pl.id .playerLosesLife) g
        | none => pure ()
    let pendingRegular :=
      g.combatHasFirstStrike && !g.firstStrikeDamageDone
    let assignedFs :=
      if pendingRegular then
        g.firstStrikeAssignedThisCombat ++ g.assignedCombatDamage.map (·.source)
      else g.firstStrikeAssignedThisCombat
    g := { g with
      assignedCombatDamage := #[]
      pending := .none
      firstStrikeDamageDone := g.firstStrikeDamageDone || g.combatHasFirstStrike
      pendingRegularCombatDamage := pendingRegular
      firstStrikeAssignedThisCombat := assignedFs }
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
  let defender := g.defendingPlayer
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
    let mut g := { g with
      firstStrikeDamageDone := false
      pendingRegularCombatDamage := false
      firstStrikeAssignedThisCombat := #[]
      blockersQueue := #[] }
    for o in g.battlefield do
      if o.status.attacking || !o.status.blocking.isEmpty || o.status.blocked then
        g := g.setObject { o with
          status := { o.status with
            attacking := false
            attackingWhom := none
            blocking := #[]
            blocked := false } }
    return g

def clearEOT (g : Game) : Game :=
  Id.run do
    let mut g := { g with
      creaturesWithoutFlyingCantBlock := false
      assignCombatDamageEqualToughness := none }
    g := g.restoreCopiesUntilEot
    for o in g.battlefield do
      if o.status.controlUntilEot then
        g := g.endControlChangingEffect (g.object! o.id)
      if (g.object! o.id).status.clearsAtCleanup then
        g := g.mapObjectStatus (g.object! o.id) Status.clearedAtCleanup
    return g

/-- Discard down to maximum hand size (CR 514.1). This turn-based action does
not use the stack; the engine discards from the back of the hand array. -/
def discardToMaxHandSize (g : Game) : Game :=
  let pl := g.player g.activePlayer
  let extra := pl.hand.size - g.effectiveMaxHandSize g.activePlayer
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
    let mut g := { g with
      creatureDiedThisTurn := false
      battlefieldCreaturesToGyThisTurn := #[]
      lastLifeLost := none
      lastNoncombatDamage := none
      sheHulkDamageUsedThisTurn := false
      pendingFreeRGCreature := none
      zemoBoastExiles := #[] }
    for pl in g.players do
      if pl.lost then
        -- Keep last-known this-turn info until that turn would have begun
        -- (CR 800.4i).
        pure ()
      else if pl.cardsDrawnThisTurn != 0 || pl.belladonnaResolvesThisTurn != 0 ||
          pl.lifeGainedThisTurn != 0 || pl.creatureSpellsCastThisTurn != 0 ||
          pl.spellsCastThisTurn != 0 || pl.attackPumpPerPlainsThisTurn != 0 ||
          pl.cardsDiscardedThisTurn != 0 then
        g := g.setPlayer { pl with
          cardsDrawnThisTurn := 0
          cardsDrawnThisDrawStep := 0
          spellsCastThisTurn := 0
          noncreatureSpellsCastThisTurn := 0
          creatureSpellsCastThisTurn := 0
          castManaValuesThisTurn := #[]
          belladonnaResolvesThisTurn := 0
          lifeGainedThisTurn := 0
          cantCastSpellsThisTurn := false
          attackPumpPerPlainsThisTurn := 0
          heroEnteredThisTurn := false
          attackedWithHeroThisTurn := false
          cardsDiscardedThisTurn := 0
          artifactEnteredThisTurn := false }
    for o in g.battlefield do
      if o.status.activationsThisTurn != 0 || o.status.firedOnceEachTurn ||
          !o.status.allianceModesChosen.isEmpty || o.status.enteredThisTurn ||
          o.status.declaredAsAttackerThisTurn || o.status.boastUsedThisTurn ||
          o.status.becameTappedThisTurn || o.status.gotPlusOneThisTurn then
        g := g.setObject { o with status := { o.status with
          activationsThisTurn := 0
          firedOnceEachTurn := false
          allianceModesChosen := #[]
          enteredThisTurn := false
          declaredAsAttackerThisTurn := false
          boastUsedThisTurn := false
          becameTappedThisTurn := false
          gotPlusOneThisTurn := false } }
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

/-- Expire effects that last until `p`'s next turn (CR 800.4m) and clear
that player's last-turn information (CR 800.4i). -/
def expireUntilNextTurnEffects (g : Game) (p : PlayerId) : Game :=
  let g :=
    if (g.player p).protectionFromEverything then
      g.setPlayer { (g.player p) with protectionFromEverything := false }
        |>.logMsg
          s!"{(g.player p).name}'s protection from everything ends (CR 800.4m)"
    else g
  let g := g.restoreCopiesUntilNextTurn p
  let g := g.expirePlayPermissions p
  g.setPlayer { (g.player p) with
    cardsDrawnThisTurn := 0
    cardsDrawnThisDrawStep := 0
    spellsCastThisTurn := 0
    noncreatureSpellsCastThisTurn := 0
    creatureSpellsCastThisTurn := 0
    castManaValuesThisTurn := #[]
    belladonnaResolvesThisTurn := 0
    lifeGainedThisTurn := 0
    cantCastSpellsThisTurn := false
    attackPumpPerPlainsThisTurn := 0 }

/-- Advance to the next living player's turn after a cleanup step ends.
A player who has left does not begin a turn (CR 800.4k); effects that last
until that turn expire when it would have begun (CR 800.4m). -/
def startNextTurn (g : Game) : Game :=
  let ending := g.activePlayer
  let g := g.expirePlayPermissions ending |>.clearTurnActivations
  let n := g.players.size
  Id.run do
    let mut g := g
    for k in [1:n+1] do
      let q : PlayerId := ⟨(ending.idx + k) % n⟩
      if (g.player q).lost then
        g := g.expireUntilNextTurnEffects q
      else
        g := { g with
          activePlayer := q
          turnNumber := g.turnNumber + 1
          isFirstTurn := false
          cleanupGivesPriority := false }
        return g.logMsg s!"It is now {g.player q |>.name}'s turn {g.turnNumber}"
    return g

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
      -- CR 502.1: phased-out permanents phase in before the player untaps.
      g := g.phaseInControlled ap
      g := g.modifyPlayer ap (fun pl =>
        { pl with landsPlayedThisTurn := 0, additionalLandsThisTurn := 0 })
      for o in g.permanentsOf ap do
        -- CR 502.2: the active player untaps their permanents. Logging each
        -- previously tapped permanent makes the battlefield status change
        -- visible in the demo before the zone reprint.
        let skipUntap :=
          (o.staticAbilities.any StaticAbility.doesntUntapUnlessEnduringStory? &&
            !g.hasEnduringStory ap) ||
          g.hostCantBecomeUntapped o
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
      let queue :=
        let ps := g.defendingPlayers
        if ps.isEmpty then #[g.opponent g.activePlayer] else ps
      { g with pending := .declareBlockers, blockersQueue := queue }
  | .combatDamage =>
      g.beginCombatDamageAssignment
  | .upkeep =>
    let ap := g.activePlayer
    let g := Id.run do
      let mut g := g
      for pl in g.players do
        if pl.eaglesBirdsNextUpkeep > 0 then
          let n := pl.eaglesBirdsNextUpkeep
          g := g.setPlayer { pl with eaglesBirdsNextUpkeep := 0 }
          if g.stillInGame pl.id then
            g := g.createKindTokens pl.id .birdSoldier n
          g := g.logMsg
            s!"{pl.name}'s delayed triggered ability creates {n} Bird Soldier token(s)"
      return g
    let g := g.putControlledTriggers ap .yourUpkeep
    g.receivePriority ap
  | .beginningOfCombat =>
    let ap := g.activePlayer
    let g := g.putControlledTriggers ap .yourBeginCombat
    g.receivePriority ap
  | .end =>
    let ap := g.activePlayer
    let g :=
      Id.run do
        let mut g := g
        let ids := g.delayedEndStepReturns
        g := { g with delayedEndStepReturns := #[] }
        for id in ids do
          match g.findObject? id with
          | none => pure ()
          | some o =>
            if o.zone == .exile then
              let owner := o.owner
              if (g.player owner).lost then
                g := g.logMsg
                  s!"{o.name} remains in its current zone (CR 800.4b)"
              else
                let name := o.name
                let sick := !o.printed.keywords.haste
                let (g', newId) := g.putOntoBattlefield id owner (summoningSick := sick)
                g := g'.logMsg
                  s!"{name} returns to the battlefield (beginning of end step)"
                g := g.afterPermanentEnters (g.object! newId)
        return g
    let g :=
      g.livingPlayers.foldl (fun acc pl =>
        acc.putControlledTriggers pl.id .eachEndStep) g
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
    let g := g.addLoreAfterDrawStep
    let g := g.putControlledTriggers ap .yourFirstMain
    g.receivePriority ap
  | _ =>
    g.receivePriority g.activePlayer

def beginTurn (g : Game) : Game :=
  let p := g.activePlayer
  let g := g.restoreCopiesUntilNextTurn p
  let g :=
    if (g.player p).protectionFromEverything then
      g.setPlayer { (g.player p) with protectionFromEverything := false }
        |>.logMsg s!"{(g.player p).name}'s protection from everything ends"
    else g
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
    else if g.step == .endOfCombat && g.additionalCombatPhases > 0 then
      let g := g.clearCombat
      let g := { g with additionalCombatPhases := g.additionalCombatPhases - 1 }
      g.logMsg "An additional combat phase begins"
        |>.beginStep .beginningOfCombat
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
  if (g.player p).lost then g
  else
    let pl := g.player p
    let g := g.setPlayer { pl with lost := true }
    let g := g.logMsg s!"{pl.name} concedes (CR 104.3a)"
    match g.decideGameIfFinished with
    | some finished => finished
    | none => g.playerLeavesGame p |>.checkSBA

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

/-- CR 103.5c / 903.12g: the first mulligan does not count in a multiplayer
game or in any Brawl game. -/
def freeFirstMulligan (g : Game) : Bool :=
  g.isMultiplayer || g.brawl

/-- Mulligans that count toward bottoming and the zero-card limit
(CR 103.5, 103.5c). -/
def countedMulligans (g : Game) (p : PlayerId) : Nat :=
  let n := (g.player p).mulligansTaken
  if g.freeFirstMulligan then n - 1 else n

def promptBottom (g : Game) (p : PlayerId) : Game :=
  let n := g.countedMulligans p
  let cards := if n == 1 then "1 card" else s!"{n} cards"
  { g with pending := .putOnBottom p n }
    |>.logMsg s!"{g.player p |>.name} puts {cards} on the bottom of their library (CR 103.5)"

/-- Cards that may begin the game on the battlefield from an opening hand
(Quicksilver; MSH 84). -/
def beginsOnBattlefieldFromOpeningHand (o : GameObject) : Bool :=
  o.staticAbilities.any (fun
    | .msh .ifQuicksilver => true
    | _ => false)

/-- After mulligans, the starting player takes opening-hand actions first,
then each other player in turn order (MSH 84). -/
def applyOpeningHandActions (g : Game) : Game :=
  Id.run do
    let mut g := g
    let order := g.playersInOrderFrom g.startingPlayer (fun pl => !pl.lost)
    for pid in order do
      let ids := (g.player pid).hand
      for id in ids do
        match g.findObject? id with
        | some o =>
          if beginsOnBattlefieldFromOpeningHand o then
            let name := o.name
            let (g', _) := g.move o.id .battlefield (some pid)
            g := g'
            g := g.logMsg s!"{name} begins the game on the battlefield"
        | none => pure ()
    return g

/-- After every remaining player has kept, opening-hand actions resolve,
then the starting player takes their first turn (CR 103.8 / MSH 84). -/
def finishOpeningHands (g : Game) : Game :=
  let g := { g with
    pending := .none
    mulliganToDeclare := #[]
    willMulligan := #[]
    mulliganToBottom := #[] }
  let g := g.applyOpeningHandActions
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
hand, after which they may not take further mulligans (CR 103.5). The first
mulligan in multiplayer or Brawl does not count toward that limit (CR 103.5c). -/
def canTakeMulligan (g : Game) (p : PlayerId) : Bool :=
  let pl := g.player p
  !g.over && !pl.keptOpeningHand && g.countedMulligans p < pl.startingHandSize

/-- Perform one already-declared mulligan: shuffle, then draw a new starting
hand (CR 103.5). Bottoming is a later choice. -/
def executeOneMulligan (g : Game) (p : PlayerId) : Game :=
  let n := (g.player p).mulligansTaken + 1
  let size := (g.player p).startingHandSize
  let g := g.modifyPlayer p (fun pl => { pl with mulligansTaken := n })
  let g := g.logMsg s!"{g.player p |>.name} takes a mulligan ({n})"
  let g := g.returnHandToLibrary p
  g.requestShuffle p (.draw p size) |>.continueIfShuffled

/-- Players whose first mulligan is free put no cards on the bottom
(CR 103.5c). -/
def skipFreeMulliganBottoms (g : Game) : Game :=
  Id.run do
    let mut g := g
    let mut need : Array PlayerId := #[]
    for p in g.mulliganToBottom do
      if g.countedMulligans p == 0 then
        g := g.logMsg
          s!"{g.player p |>.name} puts no cards on the bottom of their library (CR 103.5c)"
      else
        need := need.push p
    return { g with mulliganToBottom := need }

/-- Take remaining declared mulligans, pausing if `--norandom` needs a
library order. `mulliganToBottom` is the original simultaneous group. -/
partial def executeMulliganQueue (g : Game) (rest : Array PlayerId) : Game :=
  match rest[0]? with
  | none =>
    let g := g.skipFreeMulliganBottoms
    if g.mulliganToBottom.isEmpty then
      g.beginMulliganRound
    else
      promptBottom g g.mulliganToBottom[0]!
  | some p =>
    let more := rest.extract 1 rest.size
    let g := g.executeOneMulligan p
    match g.pendingRandom? with
    | some _ =>
      { g with afterRandom := .mulliganQueue p more }
    | none =>
      executeMulliganQueue g more

/-- After every remaining player has declared, those who chose to mulligan
do so at the same time (CR 103.5). -/
def resolveDeclaredMulligans (g : Game) : Game :=
  if g.willMulligan.isEmpty then
    g.beginMulliganRound
  else
    let order := g.playersStillDecidingMulligan.filter (fun p => g.willMulligan.contains p)
    let g := g.logMsg
      "Players who chose to mulligan do so at the same time (CR 103.5)"
    if order.isEmpty then
      g.beginMulliganRound
    else
      let g := { g with willMulligan := #[], mulliganToBottom := order }
      executeMulliganQueue g order

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
    let g := g.modifyPlayer p (fun pl =>
      { pl with cardsDiscardedThisTurn := pl.cardsDiscardedThisTurn + 1 })
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
    let g := g.modifyPlayer p (fun pl =>
      { pl with cardsDiscardedThisTurn := pl.cardsDiscardedThisTurn + 1 })
    let g := g.finishConniveDiscard card
    if g.thirstDiscardsLeft > 0 then
      let left := if card.printed.isArtifact then 0 else g.thirstDiscardsLeft - 1
      let g := { g with thirstDiscardsLeft := left }
      if left == 0 then
        return { g with pending := .none }.receivePriority g.activePlayer
      else
        return g.beginDiscardCards #[p]
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

/-- Attach Equipment or tap Humans, depending on pending. -/
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
  | .chooseTeamworkCreatures _ _ =>
    g.payTeamworkCreatures p ids
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
      else if g.canSkipCurrentOptionalSlot obj then
        let g := g.skipOptionalTargetSlot obj.id
        let g := g.logMsg
          s!"{(g.player p).name} chooses no target (CR 603.3d / 601.2c)"
        if g.currentTargetSlot obj < (g.targetingOf obj).kind.spec.slots.size then
          return { g with pending := .chooseTargets p }
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
  | .maySacrificeAnotherBolg q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to sacrifice"
    let g := g.logMsg
      s!"{(g.player p).name} declines to sacrifice a creature to Bolg"
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

/-- CR 103.3: shuffle remaining libraries, then draw opening hands. -/
partial def continueOpeningShuffles (g : Game) (next : Nat) : Game :=
  if next >= g.players.size then
    Id.run do
      let mut g := { g with afterRandom := .none, pending := .none }
      for pl in g.players do
        g := g.draw pl.id (g.player pl.id).startingHandSize
      return g.beginMulliganRound
  else
    let p : PlayerId := ⟨next⟩
    let g := g.requestShuffle p (.openingShuffles (next + 1))
    match g.pendingRandom? with
    | some _ => g
    | none =>
      let g := { g with afterRandom := .none }
      continueOpeningShuffles g (next + 1)

/-- Run the stored after-action. `grantPriority` is true when the host just
supplied a `--norandom` result (the original caller is no longer on the
stack). -/
partial def finishAfterRandom (g : Game) (grantPriority : Bool) : Game :=
  let after := g.afterRandom
  let g := { g with afterRandom := .none }
  let g :=
    match after with
    | .none => g
    | .draw p n => g.draw p n
    | .gainLife p n => g.gainLife p n
    | .openingShuffles next => continueOpeningShuffles g next
    | .mulliganQueue p rest =>
      let g := g.draw p (g.player p).startingHandSize
      executeMulliganQueue g rest
    | .setStartingPlayer i =>
      let n := g.players.size
      let i := if n == 0 then 0 else i % n
      let sp : PlayerId := ⟨i⟩
      let g := { g with startingPlayer := sp, activePlayer := sp, priority := sp }
      let g := g.logMsg s!"Starting player: {(g.player sp).name}"
      continueOpeningShuffles g 0
    | .putCreatureThenShuffle _ => g
  if grantPriority && g.pending == .none && !g.openingHandsPending && !g.over
      && !g.players.isEmpty then
    g.receivePriority g.activePlayer
  else g

/-- Apply a `--norandom` permutation or chosen object. -/
def supplyOrder (g : Game) (ids : Array ObjectId) : Except String Game := do
  match g.pending with
  | .resolveRandom req =>
    match req with
    | .shuffleLibrary p =>
      let pl := g.player p
      let ids := if ids.isEmpty then pl.library else ids
      if !isPermutation ids pl.library then
        throw "Shuffle must list each library card once (bottom first), or omit the ids to keep the current order"
      let g := { g with pending := .none }
      let g := g.setPlayer { (g.player p) with library := ids }
      return g.finishAfterRandom true
    | .orderInto expected dest =>
      let ids := if ids.isEmpty then expected else ids
      if !isPermutation ids expected then
        throw "Order must list each of those cards once, or omit the ids to keep their current order"
      let g := { g with pending := .none }
      let g := g.moveIdsInOrder ids dest
      return g.finishAfterRandom true
    | .chooseObject choices =>
      match ids[0]?, ids.size with
      | some id, 1 =>
        if !choices.contains id then
          throw "That is not one of the random choices"
        match g.afterRandom with
        | .putCreatureThenShuffle controller =>
          let some o := g.findObject? id | throw "no such object"
          let name := o.name
          let (g, newId) := g.putOntoBattlefield id controller
          let g := g.logMsg s!"{name} enters the battlefield"
          let g := g.afterPermanentEnters (g.object! newId)
          let g := { g with pending := .none, afterRandom := .none }
          let g := g.shuffleLibrary controller
          match g.pendingRandom? with
          | some _ => return g
          | none => return g.finishAfterRandom true
        | _ =>
          let g := { g with pending := .none }
          return g.finishAfterRandom true
      | _, _ => throw "Pick exactly one of the listed objects"
    | .chooseIndex _ =>
      throw "Supply an index (random <n> or flip heads/tails)"
  | _ => throw "No random event is waiting for a result"

/-- Apply a `--norandom` index (starting player, coin toss). -/
def supplyIndex (g : Game) (i : Nat) : Except String Game := do
  match g.pending with
  | .resolveRandom (.chooseIndex n) =>
    if i >= n then
      throw s!"Choose a number from 0 to {n - 1}"
    let g := { g with pending := .none }
    match g.afterRandom with
    | .setStartingPlayer _ =>
      return finishAfterRandom { g with afterRandom := .setStartingPlayer i } true
    | _ =>
      return g.finishAfterRandom true
  | .resolveRandom _ =>
    throw "This random event needs an order or a chosen object, not an index"
  | _ => throw "No random event is waiting for a result"

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
  | .declareAttackers ids defender each => g.declareAttackers p ids defender each
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
  | .announceKicker kick => g.announceKicker p kick
  | .announceGift to => g.announceGift p to
  | .announceTeamwork pay => g.announceTeamwork p pay
  | .chooseRingBearer id => g.announceRingBearer p id
  | .concede => return g.concede p
  | .supplyOrder ids => g.supplyOrder ids
  | .supplyIndex i => g.supplyIndex i

def handObjects (g : Game) (p : PlayerId) : Array GameObject :=
  (g.player p).hand.filterMap (fun id => g.findObject? id)

/-- Who must act next? -/
def actor (g : Game) : Option PlayerId :=
  if g.over then none
  else
    let who (p : PlayerId) : Option PlayerId :=
      if (g.player p).lost then some (g.nextLiving p) else some p
    match g.pending with
    | .declareAttackers => who g.activePlayer
    | .declareBlockers => who g.currentBlockersPlayer
    | .activateManaAbilities caster => who caster
    | .chooseMode p => who p
    | .chooseTargets p => who p
    | .sacrificePermanent p _ => who p
    | .sacrificeCreature p => who p
    | .declareMulligan p => who p
    | .putOnBottom p _ => who p
    | .scry p _ => who p
    | .mayDiscardDraw p _ => who p
    | .chooseAdditionalCost p => who p
    | .chooseSacrificeCreature p _ _ => who p
    | .chooseDiscardCard p _ => who p
    | .assignCombatDamage p _ => who p
    | .chooseLegend p _ _ => who p
    | .chooseTriggerToStack p => who p
    | .mayPayGeneric p _ => who p
    | .chooseLibraryPlacement p _ => who p
    | .mayAttachEquipment p _ => who p
    | .tapHumans p => who p
    | .payOrLetCounter p _ _ => who p
    | .recruitDiscard p => who p
    | .chooseKicker p => who p
    | .chooseGift p => who p
    | .chooseTeamwork p => who p
    | .chooseTeamworkCreatures p _ => who p
    | .chooseRingBearer p => who p
    | .maySacrificeAnotherBolg p _ => who p
    | .resolveRandom req =>
      match req with
      | .shuffleLibrary p => some p
      | .orderInto _ dest =>
        match dest with
        | .library p | .hand p | .graveyard p => some p
        | _ =>
          if g.players.isEmpty then none else some g.startingPlayer
      | .chooseObject _ | .chooseIndex _ =>
        if g.players.isEmpty then none else some g.startingPlayer
    | .none =>
      if g.playersReceivePriority then some g.priority else none

/-- Return owned creatures to hand and schedule that many Bird Soldiers
for the next upkeep (The Eagles Are Coming!). Tokens returned this way
are counted; they later cease in hand (CR 704.5d). -/
def returnOwnedCreaturesScheduleBirds (g : Game) (p : PlayerId)
    (ids : Array ObjectId) : Game :=
  Id.run do
    let mut g := g
    let mut n : Nat := 0
    for id in ids do
      match g.findObject? id with
      | none => pure ()
      | some o =>
        if o.isOnBattlefield && o.isCreature && o.owner == p then
          let name := o.name
          let owner := o.owner
          let (g', _) := g.move o.id (.hand owner) none
          g := g'.logMsg s!"{name} is returned to {(g'.player owner).name}'s hand"
          n := n + 1
    if n > 0 then
      g := g.modifyPlayer p (fun pl =>
        { pl with eaglesBirdsNextUpkeep := pl.eaglesBirdsNextUpkeep + n })
      g := g.logMsg
        s!"At the beginning of the next upkeep, {n} Bird Soldier token(s) will be created"
    return g

/-- Choose up to two creatures (they are not targets) and destroy the rest
(Mount Doom). Shroud and hexproof do not stop the choice. -/
def chooseCreaturesDestroyRest (g : Game) (keep : Array ObjectId) : Game :=
  Id.run do
    let mut g := g
    for o in g.battlefield do
      if o.isCreature && !keep.contains o.id then
        g := g.destroyPermanent o
    return g.logMsg "Chosen creatures are kept; the rest are destroyed"

/-- Two different players each draw a card (Gleaming Splendor). The same
player cannot be chosen twice. -/
def twoPlayersEachDraw (g : Game) (a b : PlayerId) : Except String Game := do
  if a == b then
    throw "Two target players must be different"
  let g := g.draw a 1
  return g.draw b 1

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
  let mut g : Game := {
    players := #[]
    objects := #[]
    rng := Rng.ofSeed cfg.seed
    format := cfg.format
    brawl := cfg.brawl
    norandom := cfg.norandom
  }
  for i in [0:cfg.seats.size] do
    g ← materializeSeat g i cfg.seats[i]!
  -- Determine starting player (CR 103.1).
  match cfg.startingPlayer with
  | none =>
    if cfg.norandom then
      g := g.logMsg s!"Rules: {Mtg.Engine.Rules.identification}"
      g := { g with
        pending := .resolveRandom (.chooseIndex g.players.size)
        afterRandom := .setStartingPlayer 0 }
      return g.logMsg
        "Choose who takes the first turn (CR 103.1); the engine will not roll"
    else
      let (rng, r) := g.rng.next
      let startIdx := r.toNat % g.players.size
      let sp : PlayerId := ⟨startIdx⟩
      g := { g with rng := rng, startingPlayer := sp, activePlayer := sp, priority := sp }
      g := g.logMsg s!"Rules: {Mtg.Engine.Rules.identification}"
      g := g.logMsg s!"Starting player: {g.player sp |>.name}"
      for pl in g.players do
        g := g.shuffleLibrary pl.id
      for pl in g.players do
        g := g.draw pl.id (g.player pl.id).startingHandSize
      return g.beginMulliganRound
  | some i =>
    let startIdx := i % g.players.size
    let sp : PlayerId := ⟨startIdx⟩
    g := { g with startingPlayer := sp, activePlayer := sp, priority := sp }
    g := g.logMsg s!"Rules: {Mtg.Engine.Rules.identification}"
    g := g.logMsg s!"Starting player: {g.player sp |>.name}"
    if cfg.norandom then
      return g.continueOpeningShuffles 0
    else
      for pl in g.players do
        g := g.shuffleLibrary pl.id
      for pl in g.players do
        g := g.draw pl.id (g.player pl.id).startingHandSize
      return g.beginMulliganRound

end Start

#guard Format.constructed.minDeckSize == 60

end Mtg.Engine
