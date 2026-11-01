import Mtg.Engine.Card.Counter
import Mtg.Engine.Card.TriggerEvent
import Mtg.Engine.Game.Player
import Mtg.Engine.Turn
import Mtg.Engine.TypeLine
import Mtg.Engine.Zone

/-!
# Game events (CR 603.2 / 614.1)

Every change to the game state is one `GameEvent`. The log on `Game` is
those changes, oldest first, for the whole game. A condition asks the log
whether an action happened. A triggered ability matches the change that
happened. A replacement effect matches the change that would happen, before
it is recorded; a replaced change is not recorded (CR 614.6).
-/

namespace Mtg.Engine

/-- Later steps of a trigger `sequence`, waiting until the pending choice
opened by an earlier step finishes. They run before any player receives
priority, so they stay part of that resolution. -/
structure TriggerSequenceRest where
  controller : PlayerId
  ability : TriggeredAbility
  sourceId : Option ObjectId := none
  targets : Array Target := #[]
  dividedDamage : Array Nat := #[]
  lastKnownPower : Option Int := none
  lastKnownToughness : Option Int := none
  sourceName : String := "This creature"
  cardPower : Option Nat := none
  steps : List TriggeredAbility.TriggerResolution := []
deriving Repr, Inhabited, BEq

/-- A pending `TriggerResolution.or`. The controller chooses one alternative,
then that step resolves with this ability context. -/
structure TriggerOrRest where
  controller : PlayerId
  ability : TriggeredAbility
  sourceId : Option ObjectId := none
  targets : Array Target := #[]
  dividedDamage : Array Nat := #[]
  lastKnownPower : Option Int := none
  lastKnownToughness : Option Int := none
  sourceName : String := "This creature"
  cardPower : Option Nat := none
  alternatives : Array TriggeredAbility.TriggerResolution := #[]
deriving Repr, Inhabited, BEq

/-- A pending `TriggerResolution.chooseModes` that asks for one unused mode.
The chosen index resolves with this ability context. -/
structure ChooseModesRest where
  controller : PlayerId
  ability : TriggeredAbility
  sourceId : Option ObjectId := none
  targets : Array Target := #[]
  dividedDamage : Array Nat := #[]
  lastKnownPower : Option Int := none
  lastKnownToughness : Option Int := none
  sourceName : String := "This creature"
  cardPower : Option Nat := none
  modes : List TriggeredAbility.TriggerResolution := []
  how : TriggeredAbility.TriggerModeHow := .oneUnused
deriving Repr, Inhabited, BEq

/-- One non-rules engine metadata change on a `GameObject` (CR 109 / 607). -/
inductive ObjectChange where
  | abilityEffect (v : Option Effect)
  | linkedExile (v : Array ObjectId)
  | pushLinkedExile (id : ObjectId)
  | returnToZone (v : Option Zone)
  | pushLeaveTriggerExile (id : ObjectId)
  | exiledBy (v : Option ObjectId)
deriving Repr, Inhabited, BEq

/-- One pregame or format-setup change on a `Player` (CR 102 / 103). -/
inductive PlayerChange where
  | mulligansTaken (v : Nat)
  | keptOpeningHand (v : Bool)
  | sideboard (v : Array CardDef)
deriving Repr, Inhabited, BEq

/-- One change to a `ProposedSpell` (CR 601.2f–h / 602.2b). -/
inductive ProposalChange where
  | cost (v : ManaCost)
  | addGenericCost (n : Nat)
  | reduceCostBy (c : ManaCost)
  | tapped (v : Array ObjectId)
  | pushTapped (id : ObjectId)
  | needsSacrificeOther (v : Bool)
  | needsDiscardCard (v : Bool)
  | kicked (v : Bool)
  | kickerAnnounced (v : Bool)
  | giftTo (v : Option PlayerId)
  | giftAnnounced (v : Bool)
  | teamworkPaid (v : Bool)
  | teamworkAnnounced (v : Bool)
deriving Repr, Inhabited, BEq

/-- Priority tiers for choosing among multiple applicable replacement or
prevention effects on the same event (CR 616.1a–e). -/
inductive ReplacementTier where
  /-- CR 616.1a: Self-replacement effects. -/
  | self
  /-- CR 616.1b: Effects modifying under whose control an object enters the battlefield. -/
  | control
  /-- CR 616.1c: Effects making an object become a copy as it enters the battlefield. -/
  | copy
  /-- CR 616.1d: Effects causing an object to enter the battlefield with its back face up. -/
  | backFaceUp
  /-- CR 616.1e: Any other applicable replacement or prevention effect. -/
  | other
deriving DecidableEq, Repr, Inhabited, BEq

/-- Numeric priority rank for `ReplacementTier` (CR 616.1a–e): smaller ranks
apply first. -/
def ReplacementTier.rank : ReplacementTier → Nat
  | .self => 0
  | .control => 1
  | .copy => 2
  | .backFaceUp => 3
  | .other => 4

/-- The kind of replacement effect (CR 614 / 616.1a–e). -/
inductive ReplacementKind where
  /-- CR 616.1a: Intrinsic enters-tapped replacement on `object`. -/
  | entersTappedSelf (object : ObjectId)
  /-- CR 616.1a / 614.12: Pay `life` life as `object` enters so it doesn't enter tapped. -/
  | entersUntappedPayLife (object : ObjectId) (life : Nat)
  /-- CR 616.1a / 614.12: Decline to pay life as `object` enters, so it enters tapped. -/
  | entersTappedDeclinePayLife (object : ObjectId)
  /-- CR 616.1a / 614.12: Behold `beholdId` of `subtype` as `object` enters so it doesn't enter tapped. -/
  | entersUntappedBehold (object beholdId : ObjectId) (subtype : CardSubtype)
  /-- CR 616.1a / 614.12: Decline to behold as `object` enters, so it enters tapped. -/
  | entersTappedDeclineBehold (object : ObjectId)
  /-- CR 616.1a / 614.12: Choose `color` as `object` enters. -/
  | asEntersChooseColor (object : ObjectId) (color : Color)
  /-- CR 616.1a / 614.12: Choose creature `subtype` as `object` enters. -/
  | asEntersChooseCreatureType (object : ObjectId) (subtype : CardSubtype)
  /-- CR 616.1a / 614.12: Choose odd (`true`) or even (`false`) as `object` enters. -/
  | asEntersChooseOdd (object : ObjectId) (odd : Bool)
  /-- CR 616.1a / 614.12: Name nonland card `name` as `object` enters. -/
  | asEntersChooseCardName (object : ObjectId) (name : String)
  /-- CR 616.1a / 614.12: Choose `cardType` as `object` enters. -/
  | asEntersChooseCardType (object : ObjectId) (cardType : CardType)
  /-- CR 616.1a / 614.12: Choose `anchor` as `object` enters. -/
  | asEntersChooseAnchor (object : ObjectId) (anchor : String)
  /-- CR 616.1a: Intrinsic enters-with-counters replacement on `object`. -/
  | entersWithCountersSelf (object : ObjectId) (kind : CounterKind) (amount : Nat)
  /-- CR 616.1b: Modifies under whose control `object` enters the battlefield. -/
  | entersUnderControl (object : ObjectId) (newController : PlayerId)
  /-- CR 616.1c / 707.5: Makes `object` enter the battlefield as a copy of `template`. -/
  | entersAsCopy (object : ObjectId) (template : CardDef)
  /-- CR 616.1c / 614.1c / 614.12: Optional enter-as-copy of `targetId` until EOT with haste. -/
  | entersAsCopyCreatureUntilEot (object targetId : ObjectId)
  /-- CR 616.1c / 614.1c / 614.12: Decline optional enter-as-copy. -/
  | declineEntersAsCopy (object : ObjectId)
  /-- CR 616.1d / 702.145b / 712.14: Causes `object` to enter the battlefield with its back face up. -/
  | entersBackFaceUp (object : ObjectId)
  /-- CR 616.1e: External static effect causing `object` to enter the battlefield tapped. -/
  | entersTappedExternal (object : ObjectId)
  /-- CR 616.1e: External effect causing `object` to enter with additional `kind` counters. -/
  | entersWithExtraCounters (object : ObjectId) (kind : CounterKind) (amount : Nat)
  /-- CR 616.1e / 122.6: Modifies the number of counters put on `object` (`count * mult + add`). -/
  | modifyCountersPut (object : ObjectId) (kind : Option CounterKind) (add : Nat := 0) (mult : Nat := 1)
  /-- CR 616.1a / 702.34a: Exiles `object` when leaving the stack instead of going elsewhere. -/
  | exileInsteadOfStackLeave (object : ObjectId)
  /-- CR 616.1e / 614.1a: Exiles `object` instead of putting it into a graveyard (optionally queueing a reflexive Wolf trigger). -/
  | exileInsteadOfGraveyard (object : ObjectId) (createsWolf : Bool := false)
  /-- CR 616.1e / 122.1c: Removes a shield counter from `object` instead of destroying it. -/
  | shieldCounterDestroy (object : ObjectId)
  /-- CR 616.1e / 121.2: Replaces a card draw by `player` with `factor` card draws. -/
  | replaceDraw (player : PlayerId) (factor : Nat := 2) (exceptFirstDrawStep : Bool := true)
  /-- CR 616.1e / 701.50: Replaces connive by `player`'s creature with drawing `n` cards, then conniving. -/
  | extraDrawOnConnive (player : PlayerId) (n : Nat := 1)
  /-- CR 616.1e / 614.1a: Adds `bonus` to noncombat damage dealt by `source`. -/
  | addNoncombatDamage (source : ObjectId) (bonus : Nat)
  /-- CR 616.1e / 614.1a: Multiplies damage dealt by `source` by `factor`. -/
  | multiplyDamage (source : ObjectId) (factor : Nat := 2)
  /-- CR 616.1e / 119: Modifies life gained by `player` (`amount * mult + add`). -/
  | modifyLifeGain (player : PlayerId) (add : Nat := 0) (mult : Nat := 1)
  /-- CR 616.1e / 111: Creates an extra `extraToken` alongside each Food token created by `player`. -/
  | createExtraTokenWithFood (player : PlayerId) (extraToken : CardDef)
  /-- CR 616.1e / 111: Replaces artifact tokens created under `player`'s control with `newToken`. -/
  | artifactTokensBecome (player : PlayerId) (newToken : CardDef)
  /-- CR 616.1e / 111: Multiplies the number of tokens created under `player`'s control by `factor`. -/
  | multiplyTokenCreation (player : PlayerId) (factor : Nat := 2)
  /-- CR 616.1e / 122.1d: Removes a stun counter from `object` instead of untapping it. -/
  | stunCounterUntap (object : ObjectId)
deriving Repr, Inhabited, BEq

/-- Priority tier of a `ReplacementKind` under CR 616.1a–e. -/
def ReplacementKind.tier : ReplacementKind → ReplacementTier
  | .entersTappedSelf _ => .self
  | .entersUntappedPayLife .. => .self
  | .entersTappedDeclinePayLife _ => .self
  | .entersUntappedBehold .. => .self
  | .entersTappedDeclineBehold _ => .self
  | .asEntersChooseColor .. => .self
  | .asEntersChooseCreatureType .. => .self
  | .asEntersChooseOdd .. => .self
  | .asEntersChooseCardName .. => .self
  | .asEntersChooseCardType .. => .self
  | .asEntersChooseAnchor .. => .self
  | .entersWithCountersSelf .. => .self
  | .exileInsteadOfStackLeave _ => .self
  | .entersUnderControl .. => .control
  | .entersAsCopy .. => .copy
  | .entersAsCopyCreatureUntilEot .. => .copy
  | .declineEntersAsCopy _ => .copy
  | .entersBackFaceUp _ => .backFaceUp
  | _ => .other

/-- A replacement effect specification (CR 614). -/
structure ReplacementSpec where
  id : ReplacementId
  source : Option ObjectId := none
  controller : Option PlayerId := none
  affectedPlayer : PlayerId := ⟨0⟩
  kind : ReplacementKind
  tier : ReplacementTier := kind.tier
deriving Repr, Inhabited, BEq

/-- The kind of prevention effect (CR 615). -/
inductive PreventionKind where
  /-- CR 615: Prevent all damage that would be dealt to `target`. -/
  | preventAllDamageToPermanent (target : ObjectId)
  /-- CR 615: Prevent all damage that would be dealt by `source`. -/
  | preventAllDamageFromSource (source : ObjectId)
  /-- CR 702.16e: Protection on `protectedObject` prevents all damage from `damageSource`. -/
  | protectionPreventDamage (protectedObject : ObjectId) (damageSource : ObjectId)
  /-- CR 702.16j: Protection from everything on `player` prevents all damage to `player`. -/
  | protectionFromEverythingPlayer (player : PlayerId)
  /-- CR 122.1c: Shield counter on `object` prevents damage that would be dealt to it and removes a shield counter. -/
  | shieldCounterPreventDamage (object : ObjectId)
deriving Repr, Inhabited, BEq

/-- A prevention effect specification (CR 615). -/
structure PreventionSpec where
  id : ReplacementId
  source : Option ObjectId := none
  controller : Option PlayerId := none
  affectedPlayer : PlayerId := ⟨0⟩
  kind : PreventionKind
deriving Repr, Inhabited, BEq

/-- Unified replacement or prevention effect (CR 614–616). -/
inductive ReplacementOrPrevention where
  | replacement (spec : ReplacementSpec)
  | prevention (spec : PreventionSpec)
deriving Repr, Inhabited, BEq

/-- Priority tier of a replacement or prevention effect under CR 616.1a–e. -/
def ReplacementOrPrevention.tier : ReplacementOrPrevention → ReplacementTier
  | .replacement s => s.tier
  | .prevention _ => .other

/-- The `ReplacementId` of a `ReplacementOrPrevention` effect (CR 614.5). -/
def ReplacementOrPrevention.replacementId : ReplacementOrPrevention → ReplacementId
  | .replacement s => s.id
  | .prevention s => s.id

/-- An applicable replacement or prevention effect candidate in the CR 616.1 loop. -/
structure ReplacementCandidate where
  id : ReplacementId
  spec : ReplacementOrPrevention
  affectedPlayer : PlayerId
  tier : ReplacementTier := spec.tier
deriving Repr, Inhabited, BEq

/-- Construct a `ReplacementCandidate` from a `ReplacementOrPrevention` (CR 616.1). -/
def ReplacementOrPrevention.toCandidate : ReplacementOrPrevention → ReplacementCandidate
  | .replacement s => { id := s.id, spec := .replacement s, affectedPlayer := s.affectedPlayer, tier := s.tier }
  | .prevention s => { id := s.id, spec := .prevention s, affectedPlayer := s.affectedPlayer, tier := .other }

/-- Step or phase anchor for `EffectDuration` (CR 500.4 / 500.5). -/
inductive StepOrPhase where
  | step (s : Step)
  | phase (p : Phase)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Duration of a continuous effect (CR 611.2a–b / 514.2). -/
inductive EffectDuration where
  /-- Ends in the cleanup step of the current turn (CR 514.2 / 703.4p). -/
  | untilEndOfTurn
  /-- Ends at the end of the combat phase (CR 511.2). -/
  | untilEndOfCombat
  /-- Ends at the end of step or phase `s` (CR 500.5). -/
  | untilEndOfStepOrPhase (s : StepOrPhase)
  /-- Expires as step or phase `s` begins (CR 500.4). -/
  | untilStepOrPhase (s : StepOrPhase)
  /-- Expires as `p`'s next turn begins (CR 611.2a). -/
  | untilNextTurnOf (p : PlayerId)
  /-- Ends in cleanup of `p`'s first turn that began after creation (CR 611.2a). -/
  | untilEndOfNextTurnOf (p : PlayerId)
  /-- Lasts for as long as `src` remains on the battlefield (CR 611.2b / 702.26f). -/
  | whileSourceOnBattlefield (src : ObjectId)
  /-- Lasts until `src` leaves the battlefield (CR 611.2a / 702.26d). Unlike
  `.whileSourceOnBattlefield`, phasing `src` out does not end or suppress it. -/
  | untilSourceLeaves (src : ObjectId)
  /-- Lasts for as long as `src` has at least one `k` counter (CR 611.2b). -/
  | whileSourceHasCounter (src : ObjectId) (k : CounterKind)
  /-- Lasts for as long as `obj` remains in `z` (CR 611.2b / 400.7). -/
  | whileInZone (obj : ObjectId) (z : Zone)
  /-- Lasts indefinitely (until the affected object leaves its zone, CR 400.7 / 611.2a). -/
  | indefinite
deriving DecidableEq, Repr, Inhabited, BEq

/-- Closed-data scope of a layered continuous effect (CR 611.2c / 611.3). -/
inductive ObjectScope where
  /-- Specific object(s) locked in when the effect was created (CR 611.2c). -/
  | objects (ids : Array ObjectId)
  /-- Creatures controlled by `p` (CR 611.3). -/
  | creaturesControlledBy (p : PlayerId)
  /-- Creatures without keywords `k` (CR 611.3). -/
  | creaturesWithout (k : Keywords)
  /-- Permanents of subtype `s` controlled by `p` (CR 611.3). -/
  | permanentsOfSubtype (p : PlayerId) (s : CardSubtype)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Mode for Layer 4 (types) and Layer 5 (colors) continuous effects (CR 205.1a–b / 613.1d–e). -/
inductive SetOrAdd where
  /-- Replace existing types/subtypes/colors with the given set (CR 205.1a). -/
  | set
  /-- Add the given types/subtypes/colors in addition to existing ones (CR 205.1b). -/
  | add
  /-- Add the given subtypes in addition to existing ones, deduplicating if already present. -/
  | addDedup
  /-- Replace existing creature subtypes with the given subtypes while keeping noncreature subtypes (CR 205.1a). -/
  | setAndKeepNoncreatureSubtypes
  /-- Become an artifact and lose the creature card type (Tom, Bert, and William). -/
  | addArtifactRemoveCreature
  /-- Lose the creature card type (Impending, CR 702.176). -/
  | removeCreature
  /-- Become an artifact creature with subtype Construct (Puppet Crafting). -/
  | addConstruct55
deriving DecidableEq, Repr, Inhabited, BEq

/-- Layer 3 text-changing effect (CR 612 / 613.1c). -/
inductive TextChange where
  | replaceCreatureType (fromSub toSub : CardSubtype)
  | replaceColorWord (fromCol toCol : Color)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Abilities added by a Layer 6 effect (CR 613.1f). -/
structure AbilitySet where
  keywords : Keywords := {}
  firstStrikeOnYourTurn : Bool := false
  staticAbilities : Array StaticAbility := #[]
  triggeredAbilities : Array TriggeredAbility := #[]
  ironFistTapGrants : Nat := 0
deriving Repr, Inhabited, BEq

/-- Abilities removed by a Layer 6 effect (CR 613.1f). -/
inductive AbilityRemoval where
  | none
  | all
  | loseIndestructible
deriving DecidableEq, Repr, Inhabited, BEq

/-- Layer 7a characteristic-defining ability or dynamic P/T effect (CR 604.3 / 613.4a). -/
inductive PtCda where
  | cardsInHandPower
  | pumpPerArtifact
deriving DecidableEq, Repr, Inhabited, BEq

/-- Layered characteristic-modifying effect in CR 613.1 / 613.4 order. -/
inductive LayerEffect where
  | copy (values : CardDef)                                            -- Layer 1 (CR 613.1a / 707)
  | control (p : PlayerId)                                             -- Layer 2 (CR 613.1b)
  | text (change : TextChange)                                         -- Layer 3 (CR 613.1c / 612)
  | types (mode : SetOrAdd) (types : Array CardType)
      (subtypes : Array CardSubtype) (supertypes : Array Supertype)    -- Layer 4 (CR 613.1d)
  | colors (mode : SetOrAdd) (colors : ColorSet)                       -- Layer 5 (CR 613.1e)
  | abilities (add : AbilitySet) (remove : AbilityRemoval)             -- Layer 6 (CR 613.1f)
  | ptCda (cda : PtCda)                                                -- Layer 7a–7c dynamic P/T (CR 613.4a–c)
  | ptSet (power toughness : Int)                                      -- Layer 7b (CR 613.4b)
  | ptModify (power toughness : Int)                                   -- Layer 7c (CR 613.4c)
  | ptSwitch                                                           -- Layer 7d (CR 613.4d)
deriving Repr, Inhabited, BEq

/-- Continuous rule or cost/restriction effect affecting a player (CR 611.2c / 613.11). -/
inductive PlayerRule where
  | additionalLands (n : Nat := 1)
  | protectionFromEverything
  | lifeCantChange
  | lifeLocked
  | cantCastSpells
  | typeSpellCostLess (cardType : CardType) (n : Nat)
  | supertypeSpellCostLess (supertype : Supertype) (n : Nat)
  | jaceLoyaltyAtInstantSpeed
  | legendRuleOff
  | mountainExtraRed (n : Nat := 1)
  | nextSpellCantBeCountered
  | cantAttackJaces
  | assignCombatDamageEqualToughness
  | pendingFreeRGCreature
  | controlsPlayer (controlled : PlayerId) (onNextTurn : Bool := false)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Continuous rule or restriction effect affecting game rules or objects (CR 611.2c / 613.11). -/
inductive GameRule where
  | creaturesWithoutFlyingCantBlock
  | powerUpsForbidden
  | cantUntap (object : ObjectId) (source : ObjectId)
  | cantBeBlockedByPlayer (object : ObjectId) (player : PlayerId)
  | cantBeBlockedExceptByHaste (object : ObjectId)
  | cantBlock (object : ObjectId)
  | uncounterable (object : ObjectId)
  | fraEmblem (object : ObjectId)
deriving Repr, Inhabited, BEq

/-- Continuous permission to play or cast an object or spend mana on it (CR 611.2 / 701.18). -/
inductive PlayPermissionSpec where
  | playFromExile (object : ObjectId) (perm : PlayPermission)
  | freeCastFromGraveyard (object : ObjectId)
  | flashback (object : ObjectId)
  | colorlessGrant (object : ObjectId) (card : ObjectId)
deriving Repr, Inhabited, BEq

/-- Specification of a continuous effect (CR 611 / 613). -/
inductive ContinuousEffectSpec where
  | layered (scope : ObjectScope) (e : LayerEffect) (d : EffectDuration)
  | playerRule (p : PlayerId) (r : PlayerRule) (d : EffectDuration)
  | gameRule (r : GameRule) (d : EffectDuration)
  | replacement (r : ReplacementSpec) (d : EffectDuration := .untilEndOfTurn)
  | prevention (r : PreventionSpec) (d : EffectDuration := .untilEndOfTurn)
  | permission (p : PlayerId) (r : PlayPermissionSpec) (d : EffectDuration)
deriving Repr, Inhabited, BEq

abbrev ContinuousEffect := ContinuousEffectSpec

namespace ContinuousEffectSpec

/-- An Aura's static ability setting `object` to a 5/5 Construct artifact creature (CR 611.3). -/
@[inline] def auraConstruct55 (object : ObjectId) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.types .addConstruct55 #[.artifact, .creature] #[.construct] #[]) .indefinite

/-- `object` gets `power`/`toughness` until end of turn (CR 611.2 / 613.4c). -/
@[inline] def pump (object : ObjectId) (power toughness : Int) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.ptModify power toughness) .untilEndOfTurn

/-- `object` gets `power`/`toughness` until `player`'s next turn (CR 611.2 / 613.4c). -/
@[inline] def untilTurnOfPump (object : ObjectId) (player : PlayerId) (power toughness : Int) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.ptModify power toughness) (.untilNextTurnOf player)

/-- `object` gets +1/+1 for each artifact its controller controls until end of turn (CR 611.2). -/
@[inline] def pumpPerArtifactUntilEot (object : ObjectId) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.ptCda .pumpPerArtifact) .untilEndOfTurn

/-- `object` gains `keywords` until end of turn (CR 611.2 / 613.1f). -/
@[inline] def keywordsUntilEot (object : ObjectId) (keywords : Keywords) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.abilities { keywords := keywords } .none) .untilEndOfTurn

/-- `object` has first strike as long as it's its controller's turn (CR 611.2 / 613.1f). -/
@[inline] def firstStrikeOnYourTurn (object : ObjectId) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.abilities { firstStrikeOnYourTurn := true } .none) .untilEndOfTurn

/-- `object` loses indestructible until end of turn (CR 611.2 / 613.1f). -/
@[inline] def loseIndestructibleUntilEot (object : ObjectId) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.abilities {} .loseIndestructible) .untilEndOfTurn

/-- If `object` would die this turn, exile it instead (CR 611.2 / 614.1a). -/
@[inline] def exileIfDiesUntilEot (object : ObjectId) : ContinuousEffectSpec :=
  .replacement
    { id := { kind := .untilEotExileIfDies, object := some object }
      source := some object
      kind := .exileInsteadOfGraveyard object false }
    .untilEndOfTurn

/-- `object` has base power and toughness `pt` until end of turn (CR 611.2 / 613.4b). -/
@[inline] def setBasePTUntilEot (object : ObjectId) (pt : Int × Int) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.ptSet pt.1 pt.2) .untilEndOfTurn

/-- `object`'s power and toughness are each equal to cards in its controller's hand until end of turn (CR 611.2 / 613.4a). -/
@[inline] def cardsInHandPowerUntilEot (object : ObjectId) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.ptCda .cardsInHandPower) .untilEndOfTurn

/-- `object` becomes a creature in addition to its other types (CR 611.2 / 613.1d). -/
@[inline] def additionalCreature (object : ObjectId) (untilEot : Bool := false) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.types .add #[.creature] #[] #[])
    (if untilEot then .untilEndOfTurn else .indefinite)

/-- `object` becomes an artifact in addition to its other types until end of turn (CR 611.2 / 613.1d). -/
@[inline] def additionalArtifactUntilEot (object : ObjectId) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.types .add #[.artifact] #[] #[]) .untilEndOfTurn

/-- `object` gains `subtype` in addition to its other types (CR 611.2 / 613.1d). -/
@[inline] def additionalSubtype (object : ObjectId) (subtype : CardSubtype) (dedup : Bool := false) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.types (if dedup then .addDedup else .add) #[] #[subtype] #[]) .indefinite

/-- `object`'s creature types are replaced by `subtypes` until end of turn (CR 611.2 / 613.1d). -/
@[inline] def replacedCreatureTypesUntilEot (object : ObjectId) (subtypes : Array CardSubtype) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.types .setAndKeepNoncreatureSubtypes #[] subtypes #[]) .untilEndOfTurn

/-- `object` is a Food artifact and loses all other card types and subtypes (CR 611.2 / 613.1d). -/
@[inline] def onlyFoodArtifact (object : ObjectId) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.types .set #[.artifact] #[.food] #[]) .indefinite

/-- `object` is an artifact and not a creature (CR 611.2 / 613.1d). -/
@[inline] def returnedAsArtifact (object : ObjectId) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.types .addArtifactRemoveCreature #[.artifact] #[] #[]) .indefinite

/-- `object` isn't a creature (CR 611.2 / 702.176). -/
@[inline] def notACreature (object : ObjectId) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.types .removeCreature #[] #[] #[]) .indefinite

/-- `object` gains static ability `ability` (CR 611.2 / 613.1f). -/
@[inline] def grantedStatic (object : ObjectId) (ability : StaticAbility) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.abilities { staticAbilities := #[ability] } .none) .indefinite

/-- `object` gains triggered ability `ability` (CR 611.2 / 613.1f). -/
@[inline] def grantedTriggered (object : ObjectId) (ability : TriggeredAbility) (untilEot : Bool := false) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.abilities { triggeredAbilities := #[ability] } .none)
    (if untilEot then .untilEndOfTurn else .indefinite)

/-- `object` gains Iron Fist tap ability `n` times until end of turn (CR 611.2 / 613.1f). -/
@[inline] def ironFistTapUntilEot (object : ObjectId) (n : Nat := 1) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.abilities { ironFistTapGrants := n } .none) .untilEndOfTurn

/-- `object` gains combat-damage-creates-Treasure trigger until end of turn (CR 611.2 / 613.1f). -/
@[inline] def combatDamageCreatesTreasureUntilEot (object : ObjectId) : ContinuousEffectSpec :=
  grantedTriggered object
    (.triggered .combatDamageToPlayer (Effect.ofTrigger (.createTokens .treasure 1))) true

/-- `object` loses all abilities until end of turn (CR 611.2 / 613.1f). -/
@[inline] def losesAbilitiesUntilEot (object : ObjectId) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.abilities {} .all) .untilEndOfTurn

/-- `object` loses all abilities for as long as `source` remains on the battlefield (CR 611.2b / 613.1f). -/
@[inline] def losesAbilitiesWhileSource (object : ObjectId) (source : ObjectId) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.abilities {} .all) (.whileSourceOnBattlefield source)

/-- `object` has hexproof for as long as `source` remains on the battlefield (CR 611.2b / 613.1f). -/
@[inline] def hexproofWhileSource (object : ObjectId) (source : ObjectId) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.abilities { keywords := { hexproof := true } } .none) (.whileSourceOnBattlefield source)

/-- Prevent all damage that would be dealt by `object` for as long as `source` remains on the battlefield (CR 611.2b / 615). -/
@[inline] def preventDamageWhileSource (object : ObjectId) (source : ObjectId) : ContinuousEffectSpec :=
  .prevention
    { id := { kind := .preventDamageGrantedBy, object := some object, grantor := some source }
      source := some source
      kind := .preventAllDamageFromSource object }
    (.whileSourceOnBattlefield source)

/-- `object` doesn't untap during its controller's untap step for as long as `source` remains on the battlefield (CR 611.2b). -/
@[inline] def cantUntapWhileSource (object : ObjectId) (source : ObjectId) : ContinuousEffectSpec :=
  .gameRule (.cantUntap object source) (.whileSourceOnBattlefield source)

/-- `player`'s creatures can't block `object` this turn (CR 611.2). -/
@[inline] def cantBeBlockedByPlayerUntilEot (object : ObjectId) (player : PlayerId) : ContinuousEffectSpec :=
  .gameRule (.cantBeBlockedByPlayer object player) .untilEndOfTurn

/-- `object` can't be blocked except by creatures with haste this turn (CR 611.2). -/
@[inline] def cantBeBlockedExceptByHasteUntilEot (object : ObjectId) : ContinuousEffectSpec :=
  .gameRule (.cantBeBlockedExceptByHaste object) .untilEndOfTurn

/-- `object` can't block this turn (CR 611.2). -/
@[inline] def cantBlockUntilEot (object : ObjectId) : ContinuousEffectSpec :=
  .gameRule (.cantBlock object) .untilEndOfTurn

/-- `object` gains `{T}: Add {C}{C}` until `card` is cast from exile (CR 611.2, ruling 729). -/
@[inline] def colorlessGrantUntilCast (object : ObjectId) (card : ObjectId) : ContinuousEffectSpec :=
  .permission ⟨0⟩ (.colorlessGrant object card) .indefinite

/-- `object` may be cast from the graveyard without paying its mana cost this turn (CR 611.2). -/
@[inline] def freeCastFromGraveyardUntilEot (object : ObjectId) : ContinuousEffectSpec :=
  .permission ⟨0⟩ (.freeCastFromGraveyard object) .untilEndOfTurn

/-- `object` gains flashback until end of turn (CR 611.2). -/
@[inline] def flashbackUntilEot (object : ObjectId) : ContinuousEffectSpec :=
  .permission ⟨0⟩ (.flashback object) .untilEndOfTurn

/-- If `object` would be put into a graveyard from the stack, exile it instead (CR 611.2 / 614.1a). -/
@[inline] def exileInstantSorceryInstead (object : ObjectId) : ContinuousEffectSpec :=
  .replacement
    { id := { kind := .exileInstantSorceryInstead, object := some object }
      source := some object
      kind := .exileInsteadOfGraveyard object false }
    (.whileInZone object .stack)

/-- `object` can't be countered as a spell (CR 611.2). -/
@[inline] def uncounterableThisCast (object : ObjectId) : ContinuousEffectSpec :=
  .gameRule (.uncounterable object) (.whileInZone object .stack)

/-- `object` may be played from exile under `perm` with duration `d` (CR 611.2 / 701.18). -/
@[inline] def playPermission (object : ObjectId) (perm : PlayPermission)
    (turnEnds : Nat := 1)
    (d : EffectDuration :=
      if perm.fromAdventure || perm.whileExiled || turnEnds == 0 then .whileInZone object .exile
      else if turnEnds >= 2 then .untilEndOfNextTurnOf perm.player
      else .untilEndOfTurn) : ContinuousEffectSpec :=
  .permission perm.player (.playFromExile object perm) d

/-- `object` (an emblem) lasts until `player`'s next turn (CR 611.2). -/
@[inline] def fraEmblemUntilTurnOf (object : ObjectId) (player : PlayerId) : ContinuousEffectSpec :=
  .gameRule (.fraEmblem object) (.untilNextTurnOf player)

/-- `object` becomes a copy with `printed` characteristics (CR 611.2, 707 / 613.1a). -/
@[inline] def copy (object : ObjectId) (printed : CardDef)
    (untilEot : Bool := false) (untilNextTurn : Bool := false)
    (untilSourceLeaves : Option ObjectId := none)
    (nextTurnOf : Option PlayerId := none) : ContinuousEffectSpec :=
  let d : EffectDuration :=
    match untilSourceLeaves with
    | some src => .untilSourceLeaves src
    | none =>
      if untilEot then .untilEndOfTurn
      else if untilNextTurn then .untilNextTurnOf (nextTurnOf.getD ⟨0⟩)
      else .indefinite
  .layered (.objects #[object]) (.copy printed) d

/-- `controller` gains control of `object` (CR 611.2 / 613.1b). -/
@[inline] def control (object : ObjectId) (controller : PlayerId)
    (untilEot : Bool := false) (turnEndsLeft : Nat := 0)
    (untilSourceLeaves : Option ObjectId := none) : ContinuousEffectSpec :=
  let d : EffectDuration :=
    match untilSourceLeaves with
    | some src => .untilSourceLeaves src
    | none =>
      if untilEot || turnEndsLeft == 1 then .untilEndOfTurn
      else if turnEndsLeft >= 2 then .untilEndOfNextTurnOf controller
      else .indefinite
  .layered (.objects #[object]) (.control controller) d

/-- `controller` gains control of `object` for as long as `source` remains on
the battlefield (CR 611.2b / 613.1b / 702.26f). -/
@[inline] def controlWhileSource (object : ObjectId) (controller : PlayerId)
    (source : ObjectId) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.control controller) (.whileSourceOnBattlefield source)

/-- `player` may play `n` additional lands this turn (CR 611.2). -/
@[inline] def additionalLandsThisTurn (player : PlayerId) (n : Nat := 1) : ContinuousEffectSpec :=
  .playerRule player (.additionalLands n) (.untilStepOrPhase (.step .untap))

/-- `player` has protection from everything until their next turn (CR 611.2 / 702.16j). -/
@[inline] def protectionFromEverything (player : PlayerId) : ContinuousEffectSpec :=
  .playerRule player .protectionFromEverything (.untilNextTurnOf player)

/-- `player`'s life total can't change until their next turn (CR 611.2). -/
@[inline] def lifeCantChange (player : PlayerId) : ContinuousEffectSpec :=
  .playerRule player .lifeCantChange (.untilNextTurnOf player)

/-- `player`'s life total can't change this turn (CR 611.2). -/
@[inline] def lifeLocked (player : PlayerId) : ContinuousEffectSpec :=
  .playerRule player .lifeLocked .untilEndOfTurn

/-- `player` can't cast spells this turn (CR 611.2). -/
@[inline] def cantCastSpellsThisTurn (player : PlayerId) : ContinuousEffectSpec :=
  .playerRule player .cantCastSpells .untilEndOfTurn

/-- Spells of `cardType` `player` casts cost `n` less this turn (CR 611.2). -/
@[inline] def typeSpellCostLessThisTurn (player : PlayerId) (cardType : CardType) (n : Nat) : ContinuousEffectSpec :=
  .playerRule player (.typeSpellCostLess cardType n) .untilEndOfTurn

/-- Spells of `supertype` `player` casts cost `n` less this turn (CR 611.2). -/
@[inline] def supertypeSpellCostLessThisTurn (player : PlayerId) (supertype : Supertype) (n : Nat) : ContinuousEffectSpec :=
  .playerRule player (.supertypeSpellCostLess supertype n) .untilEndOfTurn

/-- `player` may activate loyalty abilities of Jace planeswalkers at instant speed this turn (CR 611.2). -/
@[inline] def jaceLoyaltyAtInstantSpeedThisTurn (player : PlayerId) : ContinuousEffectSpec :=
  .playerRule player .jaceLoyaltyAtInstantSpeed .untilEndOfTurn

/-- The "legend rule" doesn't apply to permanents `player` controls this turn (CR 611.2). -/
@[inline] def legendRuleOffThisTurn (player : PlayerId) : ContinuousEffectSpec :=
  .playerRule player .legendRuleOff .untilEndOfTurn

/-- Whenever `player` taps a Mountain for mana this turn, add an additional {R} (CR 611.2). -/
@[inline] def mountainExtraRedThisTurn (player : PlayerId) (n : Nat := 1) : ContinuousEffectSpec :=
  .playerRule player (.mountainExtraRed n) .untilEndOfTurn

/-- The next spell `player` casts this turn can't be countered (CR 611.2). -/
@[inline] def nextSpellCantBeCounteredThisTurn (player : PlayerId) : ContinuousEffectSpec :=
  .playerRule player .nextSpellCantBeCountered .untilEndOfTurn

/-- Creatures can't attack `player` or Jace planeswalkers `player` controls this turn (CR 611.2). -/
@[inline] def cantAttackJacesThisTurn (player : PlayerId) : ContinuousEffectSpec :=
  .playerRule player .cantAttackJaces .untilEndOfTurn

/-- Creatures without flying can't block this turn (CR 611.2). -/
@[inline] def creaturesWithoutFlyingCantBlockUntilEot : ContinuousEffectSpec :=
  .gameRule .creaturesWithoutFlyingCantBlock .untilEndOfTurn

/-- Creatures `player` controls assign combat damage equal to their toughness this turn (CR 611.2). -/
@[inline] def assignCombatDamageEqualToughnessUntilEot (player : PlayerId) : ContinuousEffectSpec :=
  .playerRule player .assignCombatDamageEqualToughness .untilEndOfTurn

/-- The next red or green creature spell `player` casts this turn costs {0} (CR 611.2). -/
@[inline] def pendingFreeRGCreatureThisTurn (player : PlayerId) : ContinuousEffectSpec :=
  .playerRule player .pendingFreeRGCreature .untilEndOfTurn

/-- `controller` controls `controlled` during their turn (CR 611.2, 723). -/
@[inline] def playerControl (controller controlled : PlayerId) (onNextTurn : Bool := false) : ContinuousEffectSpec :=
  .playerRule controller (.controlsPlayer controlled onNextTurn) .indefinite

/-- Creatures can't get +X/+Y from spells or abilities this turn (CR 611.2). -/
@[inline] def powerUpsForbiddenThisTurn : ContinuousEffectSpec :=
  .gameRule .powerUpsForbidden .untilEndOfTurn

/-- Duration of this continuous effect specification (CR 611.2). -/
def duration : ContinuousEffectSpec → EffectDuration
  | .layered _ _ d => d
  | .playerRule _ _ d => d
  | .gameRule _ d => d
  | .replacement _ d => d
  | .prevention _ d => d
  | .permission _ _ d => d

end ContinuousEffectSpec

/-- Continuous-effect creation and expiration events (CR 611). -/
inductive ContinuousEffectEvent where
  | created (id : EffectId) (spec : ContinuousEffectSpec)
  | expired (id : EffectId)
deriving Repr, Inhabited, BEq

/-- Who or what receives or loses counters (CR 122.1). Players carry poison
counters (`Player.poison`, CR 122.1f) as well as other counter kinds
(`Player.counters`, CR 122.1). -/
inductive CounterTarget where
  | object (o : EventObject)
  | player (p : PlayerId)
deriving Repr, Inhabited, BEq

/-- Whether counters are put on or removed from a target (CR 122.1). -/
inductive CounterDelta where
  | put (count : Nat)
  | removed (count : Nat)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Designations a permanent can have on the battlefield (CR 400.7 / 701.15b / 701.54b). -/
inductive PermanentDesignation where
  | ringBearer                 -- 701.54a
  | goaded (byPlayer : PlayerId) (untilNextTurn : Bool := true) -- 701.15b
  | prepared                   -- set mechanic
  | harnessed                  -- set mechanic
deriving DecidableEq, Repr, Inhabited, BEq

/-- Permanent status, counter, attachment, control, and designation events
(CR 110.5, 122, 701.3, 701.26, 702.26, 708, 712). -/
inductive PermanentEvent where
  | tapped (object : EventObject) (duringControllersTurn : Bool := false)    -- 701.26a
  | untapped (object : EventObject)                                          -- 701.26b
  | phasedOut (object : EventObject) (indirectly : Bool := false)            -- 702.26b / 702.26g
  | phasedIn (object : EventObject) (indirectly : Bool := false)             -- 702.26c / 702.26g
  | transformed (object : EventObject) (nowBackFace : Bool)                  -- 701.27a / 712.18
  | turnedFaceUp (object : EventObject)                                      -- 116.2b / 708.8
  | turnedFaceDown (object : EventObject)                                    -- 708.2
  | counters
      (target : CounterTarget)
      (kind : CounterKind)
      (delta : CounterDelta)
      (actor : Option PlayerId := none)                                      -- 122.1
  | attached (attachment : EventObject) (host : ObjectId)
      (previous : Option ObjectId := none)                                   -- 701.3a / 303.4 / 301.5
  | unattached (attachment : EventObject) (fromHost : ObjectId)              -- 701.3d / 704.5n / 704.5p
  | designation (object : EventObject) (d : PermanentDesignation) (gained : Bool)
deriving Repr, Inhabited, BEq

/-- Who or what receives damage (CR 120.1 / 120.2). -/
inductive DamageRecipient where
  | permanent (object : EventObject)
  | player (player : PlayerId)
  | battle (object : EventObject)
deriving Repr, Inhabited, BEq

/-- One packet of damage dealt by a source to a recipient (CR 120.3 / 120.4b).
Keywords such as deathtouch and lifelink are read from `source`. -/
structure DamagePacket where
  source : EventObject
  recipient : DamageRecipient
  amount : Nat
  combat : Bool := false
deriving Repr, Inhabited, BEq

/-- Damage facts and damage results (CR 120.3 / 120.4b). -/
inductive DamageEvent where
  /-- The fact that damage was dealt (CR 120.2 / 120.4b). Marked damage, life
  loss, loyalty removal, and poison are recorded in the accompanying result
  events. -/
  | dealt (packets : Array DamagePacket)
  /-- Result of damage to a creature (CR 120.3e): damage marked on `object`. -/
  | marked (object : ObjectId) (amount : Nat)
  /-- Result of cleanup (CR 514.2 / 703.4p) or regeneration (CR 701.19a): clears
  marked damage on `objects`. -/
  | markedCleared (objects : Array ObjectId)
  /-- Damage that was prevented (CR 615.1 / 615.6). -/
  | prevented (source : EventObject) (recipient : DamageRecipient) (amount : Nat)
deriving Repr, Inhabited, BEq

/-- Life gain and life loss events (CR 119.2 / 119.3). -/
inductive LifeEvent where
  /-- Result of lifelink (CR 120.3f) or a "gain N life" instruction (CR 119.3):
  increases `Player.life`. -/
  | gained (player : PlayerId) (amount : Nat)
  /-- Result of damage to a player (CR 119.2 / 120.3a), "lose N life" (CR 119.3), or
  "pay N life" (CR 119.4): decreases `Player.life`. -/
  | lost (player : PlayerId) (amount : Nat)
      (fromDamage : Bool := false) (combat : Bool := false)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Why an object moved between zones (CR 400.6, 121.1, 701.8, 701.9, 701.17, 701.21). -/
inductive ZoneVerb where
  | cast
  | draw (nth : Nat) (firstOfOwnDrawStep : Bool := false)
  | discard
  | mill
  | sacrifice
  | destroy
  | exile
  | counter
  | resolve
  | put
  | returnToHand
  | shuffleIntoLibrary
  | playLand
deriving DecidableEq, Repr, Inhabited, BEq

/-- Where an object is placed in a library when moving to `.library _` (CR 401). -/
inductive LibraryPosition where
  | top
  | bottom
  | fromTop (offset : Nat)
  | shuffledIn
deriving DecidableEq, Repr, Inhabited, BEq

/-- Zone-change, token/copy creation, and cease-to-exist events (CR 400.6, 400.7, 111.10, 704.5d–e). -/
inductive ZoneEvent where
  | moved
      (before : EventObject)
      (after : EventObject)
      (fromZone toZone : Zone)
      (verb : ZoneVerb := .put)
      (actor : Option PlayerId := none)
      (entersWith : CounterBag := #[])
      (libraryPosition : Option LibraryPosition := none)
  | created
      (object : EventObject)
      (controller : PlayerId)
  | ceasedToExist
      (object : EventObject)
deriving Repr, Inhabited, BEq

/-- Lasting player designations (CR 702.131). -/
inductive PlayerDesignation where
  | citysBlessing
  | enduringStory
deriving DecidableEq, Repr, Inhabited, BEq

/-- Why a player lost the game (CR 104.3 / 704.5a–c). -/
inductive LossReason where
  | lifeZeroOrLess
  | decked
  | poison
  | conceded
  | effect
deriving DecidableEq, Repr, Inhabited, BEq

/-- Player-level actions that don't mutate a single object's zone, status, life,
or damage (CR 104, 106.4, 500.5, 701.4, 701.20–25, 701.34, 701.54, 702.131, 725, 800.4a). -/
inductive PlayerEvent where
  /-- `player` added `units` of mana to their mana pool (CR 106.4). -/
  | manaAdded (player : PlayerId) (units : Array ManaUnit)
  /-- `player` spent `units` of mana for `forObject` (CR 118.3 / 601.2h). -/
  | manaSpent (player : PlayerId) (units : Array ManaUnit) (forObject : ObjectId)
  /-- `player`'s mana pool emptied (CR 500.5 / 703.4q). `units` is the mana
  that was in the pool; `keptColorless` is true when unspent mana became
  colorless instead of emptying. -/
  | manaEmptied (player : PlayerId) (units : Array ManaUnit := #[]) (keptColorless : Bool := false)
  /-- `player` scried `asked` cards (CR 701.22). `lookedAt` cards were looked at,
  putting `top` on top and `bottom` on the bottom. -/
  | scried (player : PlayerId) (top : Array ObjectId := #[])
      (bottom : Array ObjectId := #[])
      (lookedAt : Nat := 0)
      (asked : Nat := 0)
  /-- `player` surveilled `asked` cards (CR 701.25). `lookedAt` cards were looked
  at; cards put into the graveyard also emit `ZoneEvent.moved` events. -/
  | surveilled (player : PlayerId) (top : Array ObjectId := #[])
      (graveyard : Array ObjectId := #[])
      (lookedAt : Nat := 0)
      (asked : Nat := 0)
  /-- `player` looked at `cards` (for "look at", not scry/surveil). -/
  | lookedAt (player : PlayerId) (cards : Array ObjectId)
  /-- `player` revealed `cards` (CR 701.20). -/
  | revealed (player : PlayerId) (cards : Array ObjectId)
  /-- `player` searched `libraryOwner`'s library, finding `found` (CR 701.23). -/
  | searched (player : PlayerId) (libraryOwner : PlayerId) (found : Array ObjectId)
  /-- `libraryOwner`'s library was shuffled into `newOrder` (CR 701.24). -/
  | shuffled (libraryOwner : PlayerId) (newOrder : Array ObjectId)
  /-- `player` proliferated (CR 701.34). Each counter added also emits its own
  `PermanentEvent.counters` event. -/
  | proliferated (player : PlayerId) (permanents : Array ObjectId := #[])
      (players : Array PlayerId := #[])
  /-- The Ring tempted `player` at `stage` with `bearer` (CR 701.54). -/
  | ringTempted (player : PlayerId) (bearer : Option ObjectId) (stage : Nat)
  /-- `player` beheld `quality` (CR 701.4). Later zone changes do not undo it. -/
  | beheld (player : PlayerId) (quality : CardSubtype)
  /-- `player` chose to have The Sensational She-Hulk deal damage. Once each turn. -/
  | sheHulkDealtDamage (player : PlayerId)
  /-- `player` chose the optional once-each-turn action of `source` (MSH 69). -/
  | optionalOnceActed (player : PlayerId) (source : ObjectId)
  /-- `player` attempted to draw a card from an empty library (CR 121.4 / 704.5b). -/
  | drawFromEmptyAttempted (player : PlayerId)
  /-- `player` became the monarch (CR 725). -/
  | becameMonarch (player : PlayerId) (previous : Option PlayerId := none)
  /-- `player` gained lasting designation `d` (CR 702.131). -/
  | gainedDesignation (player : PlayerId) (d : PlayerDesignation)
  /-- `player` lost the game (CR 104.3 / 704.5a–c). -/
  | lost (player : PlayerId) (reason : LossReason := .lifeZeroOrLess)
  /-- `player` left the game (CR 104.5 / 800.4a). -/
  | leftGame (player : PlayerId)
  /-- The game ended with `result` (CR 104). -/
  | gameEnded (result : GameResult)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Turn, phase, and step transitions and extra-turn/phase/step insertion (CR 500). -/
inductive TurnEvent where
  | turnBegan (player : PlayerId) (extra : Bool)
  | phaseBegan (phase : Phase)
  | stepBegan (step : Step) (active : PlayerId := ⟨0⟩)
  | stepEnded (step : Step)
  | phaseEnded (phase : Phase)
  | turnEnded (player : PlayerId)
  | dayNightChanged (night : Bool)                                -- 731.2 (non-goal today)
  | extraTurnAdded (player : PlayerId) (after : TurnRef := .current) -- 500.7
  | extraPhaseAdded (phase : Phase) (afterPhase : PhaseRef := .current) -- 500.8
  | extraStepAdded (step : Step) (anchor : StepAnchor)            -- 500.9
deriving DecidableEq, Repr, Inhabited, BEq

/-- How a spell was proposed to be cast (CR 601.2a). -/
inductive CastWay where
  | normal
  | alternative (name : String)          -- flashback, sneak, impending, prepare, miracle, cascade, free copy, etc.
deriving DecidableEq, Repr, Inhabited, BEq

/-- An additional or alternative cost choice recorded during announcement (CR 601.2b). -/
inductive AdditionalCostChoice where
  | kicker
  | morph
  | gift (recipient : PlayerId)
  | teamwork (tapped : Array ObjectId)
  | behold (chosen : ObjectId)
  | sacrifice (sacrificed : ObjectId)
  | discard (discarded : ObjectId)
  | impending (timeCounters : Nat)
  | sneak (returned : ObjectId) (attackTarget : Option AttackTarget := none)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Whether an activated ability is a non-mana or mana ability (CR 602.2b / 605.3b). -/
inductive ActivationKind where
  | nonMana (loyalty : Option Int) (equip : Bool) (powerUp : Bool) (boast : Bool)
      (abilityIdx : Option Nat := none) (exhaust : Bool := false)
  | mana (abilityIdx : Option Nat := none)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Casting and activation lifecycle events (CR 601.2 / 602.2 / 605.3b). -/
inductive CastEvent where
  | proposed (obj : ObjectId) (player : PlayerId) (fromZone : Zone) (way : CastWay)  -- 601.2a
  | announced (obj : ObjectId) (modes : Array Nat) (x : Option Nat)
      (costs : Array AdditionalCostChoice)                                         -- 601.2b
  | targeted (obj : ObjectId) (targets : Array Target) (division : Array Nat)      -- 601.2c–d
  | spellCast (spell : EventObject) (player : PlayerId) (fromZone : Zone)          -- 601.2i
  | abilityActivated (ability : ObjectId) (source : EventObject) (player : PlayerId)
      (kind : ActivationKind)                                                       -- 602.2b; mana abilities 605.3b
deriving Repr, Inhabited, BEq

/-- Stack-entry and ability-metadata payload for `TriggerQueueEvent.putOnStack` (CR 603.3 / 603.12). -/
structure StackTriggerSpec where
  triggeredAbility : Option TriggeredAbility := none
  abilityEffect : Option Effect := none
  reflexiveResolution : Option TriggeredAbility.TriggerResolution := none
  sourceId : Option ObjectId := none
  abilityName : Option String := none
  delayedTrigger : Option (DelayedTriggerKind × EventCause) := none
  lastKnownPower : Option Int := none
  lastKnownToughness : Option Int := none
  fraCauseId : Option ObjectId := none
  fraCauseController : Option PlayerId := none
  fraCausePower : Option Int := none
  fraCauseStatus : Option Status := none
deriving Repr, Inhabited, BEq

/-- Triggered ability queueing and stack placement events (CR 603.2 / 603.3). -/
inductive TriggerQueueEvent where
  | triggered (source : EventObject) (controller : PlayerId) (ability : TriggeredAbility)
      (origin : BatchId)                                                            -- 603.2
  | putOnStack (stackObj : ObjectId) (source : EventObject) (controller : PlayerId)
      (spec : StackTriggerSpec := {})                                               -- 603.3
  | modeChosen (source : ObjectId) (mode : Nat) (lifetime : Bool := false)          -- 603.3c / 700.2
deriving Repr, Inhabited, BEq

/-- Stack-object events (CR 608 / 707.10). -/
inductive StackObjectEvent where
  /-- `original` was copied on the stack as `copy` under `controller`'s control (CR 707.10). -/
  | copied (original : ObjectId) (copy : EventObject) (controller : PlayerId)
  /-- `obj` resolved (`nth` counted resolution for this ability on `turn`, or `0` for uncounted CR 608.2n / 608.3 stack resolution). -/
  | resolved (obj : EventObject) (nth : Nat := 1)
      (sourceId : Option ObjectId := none)
      (ability : Option TriggeredAbility := none)
  /-- `obj` was removed from the stack on resolution because all its targets were illegal (CR 608.2b). -/
  | removedOnResolution (obj : EventObject)
deriving Repr, Inhabited, BEq

/-- Combat declaration, state transitions, damage assignment, and removal events (CR 506–511). -/
inductive CombatEvent where
  | attackersDeclared (player : PlayerId) (decls : Array (EventObject × AttackTarget))
  | becameAttacking (creature : EventObject) (target : AttackTarget)
  | blockersDeclared (player : PlayerId) (decls : Array (EventObject × ObjectId))
  | becameBlocked (attacker : EventObject) (blockers : Array ObjectId)
  | remainedUnblocked (attacker : EventObject)
  | damageAssigned (firstStrike : Bool) (forAttackers : Bool)
      (assignments : Array CreatureCombatAssignment)
  | removedFromCombat (object : EventObject)
deriving Repr, Inhabited, BEq

/-- Lifecycle events for CR 603.7 delayed triggered abilities. -/
inductive DelayedTriggerEvent where
  | created (dt : DelayedTrigger)
  | consumed (dt : DelayedTrigger)
  | expired (dt : DelayedTrigger)
deriving Repr, Inhabited, BEq

/-- A rules-level occurrence in the game (CR 603.2 / 610 / 611 / 614). -/
inductive RulesEvent where
  /-- Zone-change, token/copy creation, and cease-to-exist events. -/
  | zone (e : ZoneEvent)
  /-- Permanent status, counter, attachment, control, and designation events. -/
  | permanent (e : PermanentEvent)
  /-- Damage facts and damage results. -/
  | damage (e : DamageEvent)
  /-- Life gain and life loss events. -/
  | life (e : LifeEvent)
  /-- Player-level keyword actions (scry, surveil, behold, proliferate). -/
  | player (e : PlayerEvent)
  /-- Turn, phase, and step transitions and extra-turn/phase/step insertion. -/
  | turn (e : TurnEvent)
  /-- Casting and activation lifecycle events. -/
  | cast (e : CastEvent)
  /-- Triggered ability queueing and stack placement events. -/
  | triggerQueue (e : TriggerQueueEvent)
  /-- Stack-object copy, resolution, and fizzle events. -/
  | stackObject (e : StackObjectEvent)
  /-- Combat declaration, state transitions, damage assignment, and removal events. -/
  | combat (e : CombatEvent)
  /-- Continuous-effect creation and expiration events (CR 611). -/
  | continuousEffect (e : ContinuousEffectEvent)
  /-- Delayed triggered ability creation, consumption, and expiration events (CR 603.7). -/
  | delayedTrigger (e : DelayedTriggerEvent)
deriving Repr, Inhabited, BEq

/-- One batch of identical tokens in a proposed token-creation event, tracked
through the CR 616.1 replacement loop. -/
structure ProposedTokenBatch where
  controller : PlayerId
  printed : CardDef
  count : Nat := 1
  tapped : Bool := false
  attacking : Bool := false
  attackingTarget : Option AttackTarget := none
  extraCounters : CounterBag := #[]
  cause : Option EventCause := none
deriving Repr, Inhabited, BEq

/-- One pending graveyard move determined during a single CR 704.3 state-based
action check (`checkSBACounted`). -/
structure SbaGraveyardMove where
  objectId : ObjectId
  reason : String
  verb : Option ZoneVerb := none
  actor : Option PlayerId := none
  sba : StateBasedAction
deriving Repr, Inhabited, BEq

/-- Continuation stored while waiting for a player to answer `Pending.chooseReplacement`
when multiple replacement or prevention effects compete in the same CR 616.1a–e tier. -/
inductive PendingReplacement where
  | seq (first rest : PendingReplacement)
  | dealDamageToPlayer (p : PlayerId) (n : Nat) (msg : String)
      (source : Option EventObject) (combat : Bool) (unpreventable : Bool)
      (cause : Option EventCause)
  | dealDamageToPlayers (players : Array PlayerId) (n : Nat)
      (source : Option EventObject) (cause : Option EventCause)
  | dealDamageFrom (sourceName : String) (source : EventObject) (targetId : ObjectId)
      (n : Nat) (deathtouch : Bool) (combat : Bool) (unpreventable : Bool)
      (cause : Option EventCause)
  | dealFightDamage (sourceId targetId : ObjectId) (cause : Option EventCause)
  | dealDamageToPermanent (targetId : ObjectId) (n : Nat)
      (source : Option EventObject) (combat : Bool) (unpreventable : Bool)
      (cause : Option EventCause)
  | markDamageOn (targetId : ObjectId) (n : Nat) (msg : String)
      (deathtouch : Bool) (source : Option EventObject) (combat : Bool)
      (unpreventable : Bool) (cause : Option EventCause)
  | dealAssignedCombatDamage (applied : Array ReplacementId := #[]) (startIdx : Nat := 0)
  | gainLife (p : PlayerId) (n : Nat) (msg : String) (cause : Option EventCause)
  | addPlusOnePlusOneTo (targetId : ObjectId) (n : Nat) (entersWith : Bool)
      (byPlayer : Option PlayerId) (cause : Option EventCause)
  | addCounters (targetId : ObjectId) (kind : CounterKind) (n : Nat)
      (entersWith : Bool) (byPlayer : Option PlayerId) (cause : Option EventCause)
  | recordPutCounters (targetId : ObjectId) (kind : CounterKind) (n : Nat)
      (byPlayer : Option PlayerId) (cause : Option EventCause)
  | move (id : ObjectId) (dest : Zone) (controller : Option PlayerId)
      (sacrificed : Bool) (discarded : Bool) (verb : Option ZoneVerb)
      (actor : Option PlayerId) (faceDown : Bool) (tapped : Bool)
      (attacking : Bool) (attackingTarget : Option AttackTarget)
      (transformed : Bool) (returnedAsArtifact : Bool) (onlyFoodArtifact : Bool)
      (extraEntersWith : CounterBag) (libraryPosition : Option LibraryPosition)
      (fromStackTime : Nat) (applyHope : Bool)
      (preBattlefield : Option (Array GameObject) := none)
      (isCopy : Option Bool := none)
      (overridePrinted : Option CardDef := none)
      (adventurerCard : Option CardDef := none)
      (summoningSick : Bool := true)
      (attachedTo : Option ObjectId := none)
      (enterMods : Array TriggeredAbility.TriggerEnterWith := #[])
      (cause : Option EventCause)
  | moveSimultaneousToGraveyard (ids : Array ObjectId)
      (preBattlefield : Option (Array GameObject))
      (cause : Option EventCause)
  | destroyPermanent (targetId : ObjectId) (cause : Option EventCause)
      (preBattlefield : Option (Array GameObject) := none)
  | createToken (controller : PlayerId) (card : CardDef) (tapped : Bool)
      (attacking : Bool) (attackingTarget : Option AttackTarget)
      (applyFoodBonus : Bool) (extraCounters : CounterBag)
      (recordRecent : Bool := false) (cause : Option EventCause)
  | createTokenBatches (batches : Array ProposedTokenBatch)
      (attacking : Bool) (attackingTarget : Option AttackTarget)
      (extraCounters : CounterBag) (recordRecent : Bool)
      (cause : Option EventCause)
  | createTreasureTokens (controller : PlayerId) (n : Nat) (tapped : Bool)
      (cause : Option EventCause)
  | createKindTokens (controller : PlayerId) (kind : TokenKind) (n : Nat)
      (tapped : Bool) (attacking : Bool) (attackingTarget : Option AttackTarget)
      (resetRecent : Bool) (cause : Option EventCause)
  | createAndMarkTokensAttacking (controller : PlayerId) (kind : TokenKind)
      (n : Nat) (tapped holds : Bool) (sourceId : Option ObjectId)
  | commitEnteringAttackItems (chosen : Array (EnteringAttackItem × Option AttackTarget))
      (cause : Option EventCause) (resetRecent : Bool)
  | finishEnteringAttackCard (newId : Option ObjectId) (effectController : PlayerId)
      (cardName : String) (mods : List TriggeredAbility.TriggerEnterWith)
      (logKind : EnteringAttackLog) (cause : Option EventCause)
  | afterLastPermanentEnters (fromId : Option ObjectId := none) (isPlayLand : Bool := false)
  | addExtraCombatDamageStep
  | finishFraChoice
  | shuffleThen (player : PlayerId) (onDone : AfterRandom)
  | draw (p : PlayerId) (n : Nat) (drawStepFirst : Bool) (cause : Option EventCause)
  | drawOne (p : PlayerId) (applied : Array ReplacementId) (drawStepFirst : Bool)
      (cause : Option EventCause)
  | drawSubDraws (p : PlayerId) (remaining : Nat) (applied : Array ReplacementId)
      (cause : Option EventCause)
  | connive (controller : PlayerId) (sourceId : Option ObjectId)
  | finishSbaSweep (moves : Array SbaGraveyardMove) (preBattlefield : Array GameObject)
      (stage : Nat)
  | untapPermanent (targetId : ObjectId) (cause : Option EventCause)
  | untapStepPermanents (ids : Array ObjectId)
  | beginStepAfterUntap
  | addLoreCounters (sagaId : ObjectId) (n : Nat) (cause : Option EventCause)
  | addLoreAfterDrawStep (sagaIds : Array ObjectId)
  | copyNontokenCreatures (controller : PlayerId) (snapshots : Array CardDef)
      (cause : Option EventCause)
  | copyPermanentTokens (controller : PlayerId) (card : CardDef) (remaining : Nat)
      (cause : Option EventCause)
  | finishArtifactCopyToken (sourceName : String)
  | finishManaAbilityMountainTrigger (player : PlayerId) (sourceId : ObjectId)
  | restorePending (p : Pending)
  | closeBatch (batchId : BatchId) (startIdx : Nat)
  | checkSBA
  | receivePriority (p : PlayerId)
  | completeActivation (hadOuterReplacement hadOpenContinuation : Bool)
  | finishBecomeActivated (caster : PlayerId) (sourceName : String)
      (sourceId : Option ObjectId) (activation : Option ActivatedAbility)
      (abilityId : Option ObjectId)
      (sourceSnapshot : Option EventObject) (sourceOriginal : Option GameObject)
      (hadOuterReplacement hadOpenContinuation : Bool)
  | finishBecomeCast (caster : PlayerId) (spellId : ObjectId) (grantPriority : Bool)
      (hadOuterReplacement hadOpenContinuation : Bool)
  | finishPostCast (caster : PlayerId) (grantPriority : Bool)
      (hadOuterReplacement hadOpenContinuation : Bool)
  | endProposalAction
  | payCostPickItems (p : PlayerId) (abilityId sourceId : ObjectId) (pick : CostPick)
      (remainingIds : Array ObjectId)
  | finishActivationExtraCosts (p : PlayerId) (sourceId : ObjectId)
      (forObject : Option ObjectId) (removePlusOnes : Nat)
      (sacrificeSource exileSource : Bool) (stage : Nat := 0)
  | finishPostLoyaltyActivated (caster : PlayerId) (sourceName : String)
      (sourceId : Option ObjectId) (activation : Option ActivatedAbility)
      (abilityId : Option ObjectId)
      (sourceSnapshot : Option EventObject) (sourceOriginal : Option GameObject)
      (hadOuterReplacement hadOpenContinuation : Bool)
  | finishActivateManaAbilityPicks (p : PlayerId) (id : ObjectId) (oname : String)
      (mana : Array ManaType) (remainingPicks : Array CostPick)
      (remainingCostIds : Array ObjectId) (tap sacrificeSelf : Bool)
      (activatedIdx : Option Nat) (restriction : ManaRestriction)
      (damageYou : Nat) (isMountain : Bool) (prevPending : Pending)
  | finishActivateManaAbilityPostSac (p : PlayerId) (id : ObjectId) (oname : String)
      (srcSnap : EventObject) (mana : Array ManaType) (tap : Bool)
      (activatedIdx : Option Nat) (restriction : ManaRestriction)
      (damageYou : Nat) (isMountain : Bool) (prevPending : Pending)
  | finishBeginRecruit (p : PlayerId)
  | finishDrawThenBeginDiscard (p : PlayerId) (discardRounds : Nat)
  | finishConniveDraws (controller : PlayerId)
      (extraDraws : Array (Nat × ReplacementId))
      (conniveDrawCause : Option EventCause) (stage : Nat := 0)
  | finishFreshAmass (controller : PlayerId) (subtype : CardSubtype) (n : Nat)
      (attach : Option ObjectId) (cause : Option EventCause)
  | finishDealDamageLoseIndestructibleExile (targetId : ObjectId) (targetName : String)
      (n : Nat) (cause : EventCause)
  | finishPlaceSearched (p : PlayerId) (fromId : ObjectId) (name : String)
      (tapped : Bool) (cause : Option EventCause)
  | placeSearchedBatch (p : PlayerId) (remainingIds : Array ObjectId) (tapped : Bool)
      (cause : Option EventCause)
  | finishSearchAfterPlace (p : PlayerId) (fromId : Option ObjectId)
      (dest : SearchDest) (after : Option FraNext) (fromLibrary : Bool)
      (handRest : Array ObjectId := #[]) (cause : Option EventCause := none)
  | finishSurveilPostMove (p : PlayerId) (card : GameObject) (fromId : ObjectId)
      (remainingGy : Array ObjectId) (cause : Option EventCause)
  | finishLibraryLook
  | finishProliferateEachKind (controller : PlayerId) (targetId : ObjectId)
      (remainingKinds : Array CounterKind) (hasPlusOne : Bool)
      (effCause : EventCause)
  | finishProliferateTarget (p : PlayerId) (targetId : ObjectId)
      (remainingKinds : Array CounterKind) (hasPlusOne : Bool)
      (remainingTargets : Array Target) (permIds : Array ObjectId)
      (playerIds : Array PlayerId) (chosenEmpty : Bool)
      (remainingRounds : Nat) (cause : Option EventCause)
  | finishProliferateLoop (p : PlayerId) (remainingTargets : Array Target)
      (permIds : Array ObjectId) (playerIds : Array PlayerId)
      (chosenEmpty : Bool) (remainingRounds : Nat) (cause : Option EventCause)
  | finishDiscardForDrawMay (p : PlayerId) (n : Nat)
  | finishSacArtifactOrDiscardDraw (p : PlayerId) (n : Nat)
  | finishChooseDiscardCard (p : PlayerId) (card : GameObject)
      (remaining : Array PlayerId)
  | finishRecruitDiscard (p : PlayerId) (isLand : Bool)
  | finishPutLandFromHand (fromId : ObjectId)
  | finishBeginOnBattlefield (fromId : ObjectId) (remainingIds : Array ObjectId)
deriving Repr, Inhabited, BEq

/-- Whether a `PendingReplacement` continuation ends with `.finishFraChoice`. -/
def PendingReplacement.endsWithFinishFra : PendingReplacement → Bool
  | .finishFraChoice => true
  | .seq _ b => b.endsWithFinishFra
  | _ => false

/-- Ensure a `PendingReplacement` continuation ends with `.finishFraChoice`
without appending a duplicate `.finishFraChoice` when already present. -/
def PendingReplacement.ensureEndsWithFinishFra : PendingReplacement → PendingReplacement
  | .finishFraChoice => .finishFraChoice
  | .seq a b => .seq a b.ensureEndsWithFinishFra
  | other => .seq other .finishFraChoice

/-- Deferred library-bottoming or CR 704.5e copy cleanup run once a mid-resolution
proposed spell finishes casting (`becomeCast`) or is reversed (`reverseProposedSpell?`). -/
inductive PostCastCleanup where
  | cascadeBottom (caster : PlayerId) (cardId : ObjectId) (others : Array ObjectId)
  | grimaBottom (victim : PlayerId) (cardId : ObjectId) (others : Array ObjectId)
  | copyCeaseToExist (copyId : ObjectId)
  | lookedBottom (caster : PlayerId) (cardId : ObjectId) (allLooked : Array ObjectId)
deriving Repr, Inhabited, BEq

/-- Action boundary marker within a proposal slice so `reverseToProposalCheckpoint?`
can reverse or retain discrete mana abilities and cost actions as whole CR 733.1
actions. -/
inductive ProposalActionKind where
  | manaAbility (source : Option ObjectId := none)
  | costAction
deriving DecidableEq, Repr, Inhabited, BEq

/-- Final CR 608.2n / 608.2p / 608.3 step run when a resolving stack object's
`ContinuationFrame` completes all `Pending` and `resolveRandom` pauses. -/
inductive ResolutionFinish where
  | ability (objId : ObjectId) (snap : EventObject) (controller : PlayerId)
      (sourceId : Option ObjectId := none) (sagaChapter : Option Nat := none)
  | spell (entry : StackEntry) (snap : EventObject) (fromGy : Bool)
deriving Repr, Inhabited, BEq

/-- One frame of mid-resolution continuation state (CR 608.2). Grouping the
per-step/per-card registers plus `resolvingContext`, `resolvingSpell`,
`resolvingAbility`, `resolvingDivision`, `afterRandom`, `resolutionFinish`, and
`pendingReplacement` into a frame on `Game.continuations` prevents nested
resolution choices (reflexive triggers, replacement choices,
cast-during-resolution) from clobbering outer frames. -/
structure ContinuationFrame where
  /-- Draw these cards after the current scry finishes (e.g. Hithlain Knots). -/
  pendingDrawAfterScry : Option (PlayerId × Nat) := none
  /-- Card discarded while a later `.put .discardedLand (how := .tapped)`
  may put that land onto the battlefield tapped (Silvan Reveler). -/
  discardedCardThisWay : Option (PlayerId × ObjectId) := none
  /-- After Palantír of Orthanc finishes scrying, this opponent may have
  the controller draw. Stores controller, opponent, and the Palantír. -/
  palantirAfterScry : Option (PlayerId × PlayerId × ObjectId) := none
  /-- Tokens created by the most recent `createKindTokens` call, so a following
  sequence step can haste them or leave them out of a plus-one. -/
  recentTokenIds : Array ObjectId := #[]
  /-- Work left after the pending scry or surveil finishes (Eye of Jace):
  its controller, source, and what to do. -/
  fraAfterLook : Option (PlayerId × Option ObjectId × FraNext) := none
  /-- Copies a player may still cast without paying their mana costs as an
  ability resolves, with the mana value left (Uldaros Theorix). -/
  pendingFreeCopies : Option (PlayerId × Array ObjectId × Nat × Nat) := none
  /-- Spells exiled by a resolving ability that may still be cast without
  paying their mana costs, and how many casts remain (Doom Reigns Supreme). -/
  pendingMayCastFromExile : Option (PlayerId × Array ObjectId × Nat) := none
  /-- Remaining exiled cards queued to be cast one at a time as an ability resolves
  (Doom Reigns `castExiledAsResolves`). -/
  pendingCastExiledQueue : Option (PlayerId × Array ObjectId) := none
  /-- Deferred post-cast cleanup (Cascade / Gríma / Cosmic Cube library bottoming
  or CR 704.5e copy cease-to-exist) run when the proposed cast completes or reverses. -/
  postCastCleanup : Option PostCastCleanup := none
  /-- Paying the pending “you may pay” cost also puts a +1/+1 counter on this
  permanent (Proft, Consulting Detective). -/
  mayPayAlsoPlusOneOn : Option ObjectId := none
  /-- Humans chosen for the current “tap any number of Humans” step. -/
  humansTappedThisWay : Nat := 0
  /-- Permanents destroyed by `.destroy .oppArtifactsEnchantments (note := .countDestroyed)`. -/
  permanentsDestroyedThisWay : Nat := 0
  /-- A hope counter was removed by the current `removeCounters .hope .source` step. -/
  removedHopeThisWay : Bool := false
  /-- The permanent marked by the current `dealDamage` step when it notes `.markedPermanent`. -/
  permanentDealtDamageThisWay : Option ObjectId := none
  /-- A permanent was returned to its owner's hand by the current `returnToHand` step. -/
  returnedPermanentThisWay : Bool := false
  /-- Ordinal recorded by the current `noteResolveThisTurn` step. -/
  nthResolveThisWay : Option Nat := none
  /-- The current sequence step asked the rest of the sequence not to run. -/
  skipTriggerSequenceRest : Bool := false
  /-- Excess damage noted by `dealDamage` with `.excess` for the following amass step. -/
  excessDamageThisWay : Nat := 0
  /-- `.destroy .target (note := .forAmass)` chose a legal target. -/
  destroyedForAmassThisWay : Bool := false
  amassControllerThisWay : Option PlayerId := none
  amassAmountThisWay : Nat := 0
  amassYouControlledThisWay : Bool := false
  /-- Cards milled by `.mill` when it notes `.milledCards`. -/
  milledIdsThisWay : Array ObjectId := #[]
  /-- Cards `revealLibrary` just showed. -/
  revealedIdsThisWay : Array ObjectId := #[]
  /-- `.mill` noted `.opponentsMilled`: an opponent milled at least one card. -/
  opponentsMilledThisWay : Bool := false
  /-- Palantír finished putting an influence counter; the following step offers
  the opponent's draw choice. -/
  palantirChoiceReady : Option (PlayerId × PlayerId × ObjectId) := none
  /-- `revealLibrary .untilInstantOrSorcery (.exile .top .forLater .impulse) .damagedPlayer`
  stored the impulse. -/
  grimaImpulseReady : Bool := false
  grimaImpulseVictim : Option PlayerId := none
  grimaImpulseFound : Option ObjectId := none
  grimaImpulseOthers : Array ObjectId := #[]
  /-- `sacrifice .you .plan .forReflexive` sacrificed the Plan. -/
  planWasSacrificed : Bool := false
  /-- `sacrifice .you .source .noted` sacrificed the source. -/
  sourceWasSacrificed : Bool := false
  /-- Lands exiled by `exile .landsYouControl .forLater .lands`. -/
  exiledIdsThisWay : Array ObjectId := #[]
  /-- Creature exiled by `exile .target .untilSourceLeaves .copyAndHost`, copied by the next step. -/
  notedCopyObject : Option GameObject := none
  notedHostId : Option ObjectId := none
  /-- Cards discarded by accepting `.discard .hand`. `none` means declined. -/
  handDiscardedThisWay : Option Nat := none
  /-- Source of the Balin ability, for the damage step after the discard. -/
  notedSourceThisWay : Option ObjectId := none
  /-- Creature that received Equipment from `attach .anyYouControl .target`. -/
  equipmentAttachedHost : Option ObjectId := none
  /-- A count captured before a later step could change it. -/
  notedCountThisWay : Nat := 0
  /-- Token created for the following attach or counter step. -/
  createdTokenThisWay : Option ObjectId := none
  /-- Artifact put from hand by `.put .artifactFromHand (note := .forAttach)`. -/
  putArtifactThisWay : Option (ObjectId × ObjectId) := none
  /-- Card exiled by `exile .graveyardCard .forLater .playCard`. -/
  playExiledThisWay : Option ObjectId := none
  /-- The following `surveil` returns a card with mana value at most the life gained this turn. -/
  armSurveilReturn : Bool := false
  /-- Later steps of a trigger `sequence`, waiting on the pending choice an earlier step opened. -/
  triggerSequenceRest : Option TriggerSequenceRest := none
  /-- Flattened steps of the `mayThen` conditional waiting in `triggerSequenceRest`. -/
  mayThenDrop : Nat := 0
  /-- After an optional `mayThen` action cannot be performed, the sequence fold skips this many steps. -/
  mayThenSkip : Nat := 0
  /-- Conditional of the `mayThen` currently offered. -/
  mayThenConditional : Option TriggeredAbility.TriggerResolution := none
  /-- Accepting `Pending.mayResolve` applies this trigger resolution. -/
  mayOnAccept : Option TriggeredAbility.TriggerResolution := none
  /-- Declining `Pending.mayResolve` applies this trigger resolution instead of `mayOnAccept`. -/
  mayOnDecline : Option TriggeredAbility.TriggerResolution := none
  /-- Ability context for `mayOnAccept` and `mayOnDecline`. -/
  mayContext : Option TriggerSequenceRest := none
  /-- Power of the creature sacrificed for `putCounters .plusOneSacrificedPower`. -/
  sacrificedPowerThisWay : Option Nat := none
  /-- An artifact-or-discard cost accepted a `mayThen`. -/
  mayThenResume : Bool := false
  /-- Alternatives for a pending `TriggerResolution.or`. -/
  triggerOr : Option TriggerOrRest := none
  /-- Context for a pending Alliance or Gollum mode choice. -/
  chooseModesRest : Option ChooseModesRest := none
  /-- Declining `payOrLetCounter` resolves this effect instead of countering. -/
  unlessPaysInstead : Option Effect := none
  unlessPaysController : PlayerId := ⟨0⟩
  unlessPaysTargets : Array Target := #[]
  /-- The payer left without paying (CR 800.4f). -/
  unlessPaysDue : Bool := false
  /-- Accepting `mayResolve` resolves this effect. -/
  mayEffect : Option Effect := none
  mayController : PlayerId := ⟨0⟩
  mayTargets : Array Target := #[]
  /-- Alternatives for a pending `SpellResolution.or`. -/
  spellOr : Array Effect := #[]
  spellOrController : PlayerId := ⟨0⟩
  spellOrTargets : Array Target := #[]
  /-- `chooseTop` and `chooseBottom` name the library side, not list order. -/
  spellOrLibrary : Bool := false
  /-- After the pending surveil, a card with mana value at most this put into the graveyard goes to hand. -/
  surveilReturnMvAtMost : Option Nat := none
  /-- A noncreature, nonland card put into the graveyard by the pending surveil goes to hand. -/
  surveilReturnNoncreatureNonland : Bool := false
  /-- Continuation for an event paused on `Pending.chooseReplacement` (CR 616.1). -/
  pendingReplacement : Option PendingReplacement := none
  /-- Source of the current connive action, if any (MSH / CR 701.50). -/
  conniveSource : Option ObjectId := none
  /-- Put a +1/+1 counter on this permanent after the current discard choices finish. -/
  plusOneAfterDiscards : Option ObjectId := none
  /-- After the current library search shuffles, put a +1/+1 counter on this creature. -/
  plusOneAfterSearch : Option ObjectId := none
  /-- Remaining discards for Thirst for Knowledge (MSH 344). -/
  thirstDiscardsLeft : Nat := 0
  /-- Discarding a card of this type finishes `thirstDiscardsLeft` early. -/
  thirstDiscardType : CardType := .artifact
  /-- Remaining discards for a required multi-card discard. -/
  pendingDiscardsLeft : Nat := 0
  /-- After the current search, untap the land if its controller has this many lands. -/
  untapSearchedIfLands : Option Nat := none
  /-- Active resolving source object id and controller across pending resolution
  choices and delayed triggered abilities (CR 608 / 610.1). -/
  resolvingContext : Option (Option ObjectId × PlayerId) := none
  /-- Active one-shot `EventCause` carried across a multi-step resolution choice
  before the chosen cards move (CR 608.2c). -/
  stashedCause : Option EventCause := none
  /-- The spell whose effect is currently resolving (CR 608.2). -/
  resolvingSpell : Option ObjectId := none
  /-- The activated or triggered ability currently resolving (CR 608.2). -/
  resolvingAbility : Option ObjectId := none
  /-- Damage assigned to each target of the resolving divided-damage ability (CR 601.2d). -/
  resolvingDivision : Array Nat := #[]
  /-- Resolution-scoped continuation after a `--norandom` result is applied. -/
  afterRandom : AfterRandom := .none
  /-- Deferred CR 608.2n / 608.2p / 608.3 completion step for the resolving stack object. -/
  resolutionFinish : Option ResolutionFinish := none
  /-- Deferred `StackObjectEvent.resolved` payload waiting on an ETB replacement
  or as-enters choice opened during `resolutionFinish`. -/
  pendingResolvedEvent : Option (EventObject × PlayerId × EventCause) := none
deriving Repr, Inhabited, BEq

/-- Mutations to the top frame of `Game.continuations`. -/
inductive ContinuationChange where
  | pendingDrawAfterScry (v : Option (PlayerId × Nat))
  | discardedCardThisWay (v : Option (PlayerId × ObjectId))
  | palantirAfterScry (v : Option (PlayerId × PlayerId × ObjectId))
  | recentTokenIds (v : Array ObjectId)
  | fraAfterLook (v : Option (PlayerId × Option ObjectId × FraNext))
  | pendingFreeCopies (v : Option (PlayerId × Array ObjectId × Nat × Nat))
  | pendingMayCastFromExile (v : Option (PlayerId × Array ObjectId × Nat))
  | pendingCastExiledQueue (v : Option (PlayerId × Array ObjectId))
  | postCastCleanup (v : Option PostCastCleanup)
  | mayPayAlsoPlusOneOn (v : Option ObjectId)
  | humansTappedThisWay (v : Nat)
  | permanentsDestroyedThisWay (v : Nat)
  | removedHopeThisWay (v : Bool)
  | permanentDealtDamageThisWay (v : Option ObjectId)
  | returnedPermanentThisWay (v : Bool)
  | nthResolveThisWay (v : Option Nat)
  | skipTriggerSequenceRest (v : Bool)
  | excessDamageThisWay (v : Nat)
  | destroyedForAmassThisWay (v : Bool)
  | amassControllerThisWay (v : Option PlayerId)
  | amassAmountThisWay (v : Nat)
  | amassYouControlledThisWay (v : Bool)
  | milledIdsThisWay (v : Array ObjectId)
  | revealedIdsThisWay (v : Array ObjectId)
  | opponentsMilledThisWay (v : Bool)
  | palantirChoiceReady (v : Option (PlayerId × PlayerId × ObjectId))
  | grimaImpulseReady (v : Bool)
  | grimaImpulseVictim (v : Option PlayerId)
  | grimaImpulseFound (v : Option ObjectId)
  | grimaImpulseOthers (v : Array ObjectId)
  | planWasSacrificed (v : Bool)
  | sourceWasSacrificed (v : Bool)
  | exiledIdsThisWay (v : Array ObjectId)
  | pushExiledIdThisWay (id : ObjectId)
  | notedCopyObject (v : Option GameObject)
  | notedHostId (v : Option ObjectId)
  | handDiscardedThisWay (v : Option Nat)
  | notedSourceThisWay (v : Option ObjectId)
  | equipmentAttachedHost (v : Option ObjectId)
  | notedCountThisWay (v : Nat)
  | createdTokenThisWay (v : Option ObjectId)
  | putArtifactThisWay (v : Option (ObjectId × ObjectId))
  | playExiledThisWay (v : Option ObjectId)
  | armSurveilReturn (v : Bool)
  | triggerSequenceRest (v : Option TriggerSequenceRest)
  | setTriggerSequenceRestSteps (steps : List TriggeredAbility.TriggerResolution)
  | setTriggerSequenceRestFromMay (steps : List TriggeredAbility.TriggerResolution)
  | mayThenDrop (v : Nat)
  | mayThenSkip (v : Nat)
  | mayThenConditional (v : Option TriggeredAbility.TriggerResolution)
  | mayOnAccept (v : Option TriggeredAbility.TriggerResolution)
  | mayOnDecline (v : Option TriggeredAbility.TriggerResolution)
  | mayContext (v : Option TriggerSequenceRest)
  | sacrificedPowerThisWay (v : Option Nat)
  | mayThenResume (v : Bool)
  | triggerOr (v : Option TriggerOrRest)
  | chooseModesRest (v : Option ChooseModesRest)
  | unlessPaysInstead (v : Option Effect)
  | unlessPaysController (v : PlayerId)
  | unlessPaysTargets (v : Array Target)
  | unlessPaysDue (v : Bool)
  | mayEffect (v : Option Effect)
  | mayController (v : PlayerId)
  | mayTargets (v : Array Target)
  | spellOr (v : Array Effect)
  | spellOrController (v : PlayerId)
  | spellOrTargets (v : Array Target)
  | spellOrLibrary (v : Bool)
  | surveilReturnMvAtMost (v : Option Nat)
  | surveilReturnNoncreatureNonland (v : Bool)
  | pendingReplacement (v : Option PendingReplacement)
  | conniveSource (v : Option ObjectId)
  | plusOneAfterDiscards (v : Option ObjectId)
  | plusOneAfterSearch (v : Option ObjectId)
  | thirstDiscardsLeft (v : Nat)
  | thirstDiscardType (v : CardType)
  | pendingDiscardsLeft (v : Nat)
  | untapSearchedIfLands (v : Option Nat)
  | stashedCause (v : Option EventCause)
  | resolvingSpell (v : Option ObjectId)
  | resolvingAbility (v : Option ObjectId)
  | resolvingDivision (v : Array Nat)
  | afterRandom (v : AfterRandom)
  | resolutionFinish (v : Option ResolutionFinish)
  | pendingResolvedEvent (v : Option (EventObject × PlayerId × EventCause))
deriving Repr, Inhabited, BEq

/-- Internal engine state mutations that are not rules-level occurrences. -/
inductive EngineChange where
  /-- Update a player's pregame/format state. -/
  | player (p : PlayerId) (c : PlayerChange)
  | addPlayer (pl : Player)
  /-- Materialize a non-token `GameObject` directly into `g.objects` and its zone
  (pregame deck/sideboard cards, CR 114 command-zone emblems/effect objects,
  CR 602.2a proposed stack abilities, and test fixtures). -/
  | materializeObject (obj : GameObject) (libraryPosition : Option LibraryPosition := none)
  /-- Update an object's non-rules engine metadata. -/
  | object (id : ObjectId) (c : ObjectChange)
  /-- Update the stack. -/
  | removeStackEntry (objectId : ObjectId)
  | pushStack (e : StackEntry)
  | popStack
  | setStackEntryAt (idx : Nat) (e : StackEntry)
  /-- Update or checkpoint the proposed spell or ability (CR 601.2 / 602.2 / 733.1). -/
  | proposedSpell (v : Option ProposedSpell)
  | proposal (c : ProposalChange)
  | proposalChanges (cs : Array ProposalChange)
  | saveProposalCheckpoint
  | clearProposalCheckpoint
  | beginProposalAction (kind : ProposalActionKind)
  | endProposalAction
  /-- Journal or clear an open rules-event batch paused on a player choice (CR 616.1). -/
  | pauseBatch (batchId : BatchId) (cause : Option EventCause)
      (objects : Array GameObject) (players : Array Player)
      (effects : Array (EffectId × ContinuousEffectSpec)) (pending : Pending)
  | clearPausedBatch
  /-- Update the continuation frame stack. -/
  | pushContinuationFrame (frame : ContinuationFrame := {})
  | popContinuationFrame
  | continuation (c : ContinuationChange)
  /-- Update game fields. -/
  | priority (v : PlayerId)
  | startingPlayer (v : PlayerId)
  | pending (v : Pending)
  | nextEffectId (v : Nat)
  | pregameRandom (v : PregameRandom)
  | log (v : Array String)
  | logMsg (msg : String)
  | format (v : Format)
  | brawl (v : Bool)
  | consecutivePasses (v : Nat)
  | cleanupGivesPriority (v : Bool)
  | awaitingOpeningBegin (v : Bool)
  | mulliganToDeclare (v : Array PlayerId)
  | willMulligan (v : Array PlayerId)
  | pushWillMulligan (p : PlayerId)
  | mulliganToBottom (v : Array PlayerId)
  | blockersQueue (v : Array PlayerId)
  | waitingTriggers (v : Array WaitingTrigger)
  | enqueueWaitingTriggers (wts : Array WaitingTrigger)
  | replacementOrder (ids : Array ReplacementId)
  | castingFromTop (v : Bool)
  | sbaChecked
deriving Repr, Inhabited, BEq

namespace EngineChange
@[inline] def pendingDrawAfterScry (v : Option (PlayerId × Nat)) : EngineChange := .continuation (.pendingDrawAfterScry v)
@[inline] def discardedCardThisWay (v : Option (PlayerId × ObjectId)) : EngineChange := .continuation (.discardedCardThisWay v)
@[inline] def palantirAfterScry (v : Option (PlayerId × PlayerId × ObjectId)) : EngineChange := .continuation (.palantirAfterScry v)
@[inline] def recentTokenIds (v : Array ObjectId) : EngineChange := .continuation (.recentTokenIds v)
@[inline] def fraAfterLook (v : Option (PlayerId × Option ObjectId × FraNext)) : EngineChange := .continuation (.fraAfterLook v)
@[inline] def pendingFreeCopies (v : Option (PlayerId × Array ObjectId × Nat × Nat)) : EngineChange := .continuation (.pendingFreeCopies v)
@[inline] def pendingMayCastFromExile (v : Option (PlayerId × Array ObjectId × Nat)) : EngineChange := .continuation (.pendingMayCastFromExile v)
@[inline] def pendingCastExiledQueue (v : Option (PlayerId × Array ObjectId)) : EngineChange := .continuation (.pendingCastExiledQueue v)
@[inline] def postCastCleanup (v : Option PostCastCleanup) : EngineChange := .continuation (.postCastCleanup v)
@[inline] def mayPayAlsoPlusOneOn (v : Option ObjectId) : EngineChange := .continuation (.mayPayAlsoPlusOneOn v)
@[inline] def humansTappedThisWay (v : Nat) : EngineChange := .continuation (.humansTappedThisWay v)
@[inline] def permanentsDestroyedThisWay (v : Nat) : EngineChange := .continuation (.permanentsDestroyedThisWay v)
@[inline] def removedHopeThisWay (v : Bool) : EngineChange := .continuation (.removedHopeThisWay v)
@[inline] def permanentDealtDamageThisWay (v : Option ObjectId) : EngineChange := .continuation (.permanentDealtDamageThisWay v)
@[inline] def returnedPermanentThisWay (v : Bool) : EngineChange := .continuation (.returnedPermanentThisWay v)
@[inline] def nthResolveThisWay (v : Option Nat) : EngineChange := .continuation (.nthResolveThisWay v)
@[inline] def skipTriggerSequenceRest (v : Bool) : EngineChange := .continuation (.skipTriggerSequenceRest v)
@[inline] def excessDamageThisWay (v : Nat) : EngineChange := .continuation (.excessDamageThisWay v)
@[inline] def destroyedForAmassThisWay (v : Bool) : EngineChange := .continuation (.destroyedForAmassThisWay v)
@[inline] def amassControllerThisWay (v : Option PlayerId) : EngineChange := .continuation (.amassControllerThisWay v)
@[inline] def amassAmountThisWay (v : Nat) : EngineChange := .continuation (.amassAmountThisWay v)
@[inline] def amassYouControlledThisWay (v : Bool) : EngineChange := .continuation (.amassYouControlledThisWay v)
@[inline] def milledIdsThisWay (v : Array ObjectId) : EngineChange := .continuation (.milledIdsThisWay v)
@[inline] def revealedIdsThisWay (v : Array ObjectId) : EngineChange := .continuation (.revealedIdsThisWay v)
@[inline] def opponentsMilledThisWay (v : Bool) : EngineChange := .continuation (.opponentsMilledThisWay v)
@[inline] def palantirChoiceReady (v : Option (PlayerId × PlayerId × ObjectId)) : EngineChange := .continuation (.palantirChoiceReady v)
@[inline] def grimaImpulseReady (v : Bool) : EngineChange := .continuation (.grimaImpulseReady v)
@[inline] def grimaImpulseVictim (v : Option PlayerId) : EngineChange := .continuation (.grimaImpulseVictim v)
@[inline] def grimaImpulseFound (v : Option ObjectId) : EngineChange := .continuation (.grimaImpulseFound v)
@[inline] def grimaImpulseOthers (v : Array ObjectId) : EngineChange := .continuation (.grimaImpulseOthers v)
@[inline] def planWasSacrificed (v : Bool) : EngineChange := .continuation (.planWasSacrificed v)
@[inline] def sourceWasSacrificed (v : Bool) : EngineChange := .continuation (.sourceWasSacrificed v)
@[inline] def exiledIdsThisWay (v : Array ObjectId) : EngineChange := .continuation (.exiledIdsThisWay v)
@[inline] def pushExiledIdThisWay (id : ObjectId) : EngineChange := .continuation (.pushExiledIdThisWay id)
@[inline] def notedCopyObject (v : Option GameObject) : EngineChange := .continuation (.notedCopyObject v)
@[inline] def notedHostId (v : Option ObjectId) : EngineChange := .continuation (.notedHostId v)
@[inline] def handDiscardedThisWay (v : Option Nat) : EngineChange := .continuation (.handDiscardedThisWay v)
@[inline] def notedSourceThisWay (v : Option ObjectId) : EngineChange := .continuation (.notedSourceThisWay v)
@[inline] def equipmentAttachedHost (v : Option ObjectId) : EngineChange := .continuation (.equipmentAttachedHost v)
@[inline] def notedCountThisWay (v : Nat) : EngineChange := .continuation (.notedCountThisWay v)
@[inline] def createdTokenThisWay (v : Option ObjectId) : EngineChange := .continuation (.createdTokenThisWay v)
@[inline] def putArtifactThisWay (v : Option (ObjectId × ObjectId)) : EngineChange := .continuation (.putArtifactThisWay v)
@[inline] def playExiledThisWay (v : Option ObjectId) : EngineChange := .continuation (.playExiledThisWay v)
@[inline] def armSurveilReturn (v : Bool) : EngineChange := .continuation (.armSurveilReturn v)
@[inline] def triggerSequenceRest (v : Option TriggerSequenceRest) : EngineChange := .continuation (.triggerSequenceRest v)
@[inline] def setTriggerSequenceRestSteps (steps : List TriggeredAbility.TriggerResolution) : EngineChange := .continuation (.setTriggerSequenceRestSteps steps)
@[inline] def setTriggerSequenceRestFromMay (steps : List TriggeredAbility.TriggerResolution) : EngineChange := .continuation (.setTriggerSequenceRestFromMay steps)
@[inline] def mayThenDrop (v : Nat) : EngineChange := .continuation (.mayThenDrop v)
@[inline] def mayThenSkip (v : Nat) : EngineChange := .continuation (.mayThenSkip v)
@[inline] def mayThenConditional (v : Option TriggeredAbility.TriggerResolution) : EngineChange := .continuation (.mayThenConditional v)
@[inline] def mayOnAccept (v : Option TriggeredAbility.TriggerResolution) : EngineChange := .continuation (.mayOnAccept v)
@[inline] def mayOnDecline (v : Option TriggeredAbility.TriggerResolution) : EngineChange := .continuation (.mayOnDecline v)
@[inline] def mayContext (v : Option TriggerSequenceRest) : EngineChange := .continuation (.mayContext v)
@[inline] def sacrificedPowerThisWay (v : Option Nat) : EngineChange := .continuation (.sacrificedPowerThisWay v)
@[inline] def mayThenResume (v : Bool) : EngineChange := .continuation (.mayThenResume v)
@[inline] def triggerOr (v : Option TriggerOrRest) : EngineChange := .continuation (.triggerOr v)
@[inline] def chooseModesRest (v : Option ChooseModesRest) : EngineChange := .continuation (.chooseModesRest v)
@[inline] def unlessPaysInstead (v : Option Effect) : EngineChange := .continuation (.unlessPaysInstead v)
@[inline] def unlessPaysController (v : PlayerId) : EngineChange := .continuation (.unlessPaysController v)
@[inline] def unlessPaysTargets (v : Array Target) : EngineChange := .continuation (.unlessPaysTargets v)
@[inline] def unlessPaysDue (v : Bool) : EngineChange := .continuation (.unlessPaysDue v)
@[inline] def mayEffect (v : Option Effect) : EngineChange := .continuation (.mayEffect v)
@[inline] def mayController (v : PlayerId) : EngineChange := .continuation (.mayController v)
@[inline] def mayTargets (v : Array Target) : EngineChange := .continuation (.mayTargets v)
@[inline] def spellOr (v : Array Effect) : EngineChange := .continuation (.spellOr v)
@[inline] def spellOrController (v : PlayerId) : EngineChange := .continuation (.spellOrController v)
@[inline] def spellOrTargets (v : Array Target) : EngineChange := .continuation (.spellOrTargets v)
@[inline] def spellOrLibrary (v : Bool) : EngineChange := .continuation (.spellOrLibrary v)
@[inline] def surveilReturnMvAtMost (v : Option Nat) : EngineChange := .continuation (.surveilReturnMvAtMost v)
@[inline] def surveilReturnNoncreatureNonland (v : Bool) : EngineChange := .continuation (.surveilReturnNoncreatureNonland v)
@[inline] def pendingReplacement (v : Option PendingReplacement) : EngineChange := .continuation (.pendingReplacement v)
@[inline] def conniveSource (v : Option ObjectId) : EngineChange := .continuation (.conniveSource v)
@[inline] def plusOneAfterDiscards (v : Option ObjectId) : EngineChange := .continuation (.plusOneAfterDiscards v)
@[inline] def plusOneAfterSearch (v : Option ObjectId) : EngineChange := .continuation (.plusOneAfterSearch v)
@[inline] def thirstDiscardsLeft (v : Nat) : EngineChange := .continuation (.thirstDiscardsLeft v)
@[inline] def thirstDiscardType (v : CardType) : EngineChange := .continuation (.thirstDiscardType v)
@[inline] def pendingDiscardsLeft (v : Nat) : EngineChange := .continuation (.pendingDiscardsLeft v)
@[inline] def untapSearchedIfLands (v : Option Nat) : EngineChange := .continuation (.untapSearchedIfLands v)
@[inline] def stashedCause (v : Option EventCause) : EngineChange := .continuation (.stashedCause v)
@[inline] def resolvingSpell (v : Option ObjectId) : EngineChange := .continuation (.resolvingSpell v)
@[inline] def resolvingAbility (v : Option ObjectId) : EngineChange := .continuation (.resolvingAbility v)
@[inline] def resolvingDivision (v : Array Nat) : EngineChange := .continuation (.resolvingDivision v)
@[inline] def afterRandom (v : AfterRandom) : EngineChange := .continuation (.afterRandom v)
@[inline] def resolutionFinish (v : Option ResolutionFinish) : EngineChange := .continuation (.resolutionFinish v)
@[inline] def pendingResolvedEvent (v : Option (EventObject × PlayerId × EventCause)) : EngineChange := .continuation (.pendingResolvedEvent v)
end EngineChange

/-- One change to the game, without the turn number. -/
inductive GameChange where
  | rules (e : RulesEvent)
  | engine (c : EngineChange)
deriving Repr, Inhabited, BEq

/-- A game state change on a given turn (CR 500). `Game.events` records each
one that happens. Every `RulesEvent` carries an explicit `EventCause`;
internal `EngineChange` mutations are cause-free. -/
inductive GameEvent where
  | rules (turn : Nat) (e : RulesEvent) (cause : EventCause) (batch : BatchId := ⟨0⟩)
  | engine (turn : Nat) (c : EngineChange) (batch : BatchId := ⟨0⟩)
deriving Repr, Inhabited, BEq

namespace GameEvent

/-- Turn number on which `e` occurred. -/
@[inline] def turn : GameEvent → Nat
  | .rules t .. | .engine t .. => t

/-- Batch identifier of `e` (`⟨0⟩` for engine changes or unbatched events). -/
@[inline] def batch : GameEvent → BatchId
  | .rules _ _ _ b | .engine _ _ b => b

/-- Return `e` stamped with `b`. -/
@[inline] def withBatch (e : GameEvent) (b : BatchId) : GameEvent :=
  match e with
  | .rules t r c _ => .rules t r c b
  | .engine t c _ => .engine t c b

/-- Return `e` with its `RulesEvent` payload replaced, preserving turn, cause, and batch. -/
@[inline] def withRules (e : GameEvent) (r : RulesEvent) : GameEvent :=
  match e with
  | .rules t _ c b => .rules t r c b
  | .engine .. => e

/-- Return `e` with its `EventCause` replaced (no-op on `.engine`). -/
@[inline] def withCause (e : GameEvent) (c : EventCause) : GameEvent :=
  match e with
  | .rules t r _ b => .rules t r c b
  | .engine .. => e

/-- Tagged rules/engine payload of `e`. -/
@[inline] def change : GameEvent → GameChange
  | .rules _ r .. => .rules r
  | .engine _ c .. => .engine c

/-- `some cause` for a `RulesEvent`, or `none` for a cause-free `EngineChange`. -/
@[inline] def cause? : GameEvent → Option EventCause
  | .rules _ _ c _ => some c
  | .engine .. => none

/-- `object` moved from `fromZone` to `toZone` (CR 400.6 / 400.7). -/
def moved (turn : Nat) (before : EventObject) (fromZone toZone : Zone)
    (sacrificed : Bool := false) (discarded : Bool := false)
    (after : Option EventObject := none)
    (verb : Option ZoneVerb := none)
    (actor : Option PlayerId := none)
    (entersWith : CounterBag := #[])
    (libraryPosition : Option LibraryPosition := none)
    (cause : EventCause) : GameEvent :=
  let v :=
    match verb with
    | some v => v
    | none =>
      if sacrificed then .sacrifice
      else if discarded then .discard
      else if toZone == .exile then .exile
      else if toZone == .stack then .cast
      else .put
  let beforeObj := { before with zone := fromZone }
  let afterObj :=
    match after with
    | some a => { a with zone := toZone }
    | none =>
      { before with
        zone := toZone
        controller := if toZone == .battlefield || toZone == .stack then before.controller else none
        tapped := false
        attacking := false
        blocking := false
        attachedTo := none
        counters := if toZone == .battlefield then entersWith else #[] }
  let actor' :=
    match actor with
    | some a => some a
    | none =>
      if sacrificed || v == .sacrifice then before.controller.orElse (fun _ => some before.owner)
      else if discarded || v == .discard then
        match fromZone with
        | .hand p => some p
        | _ => some before.owner
      else none
  rules turn
    (.zone (.moved beforeObj afterObj fromZone toZone v actor' entersWith libraryPosition))
    cause

/-- `player` drew `card` as the `nth` card this turn (CR 121.1 / 400.7). -/
def drew (turn : Nat) (player : PlayerId) (card : ObjectId) (nth : Nat)
    (firstOfOwnDrawStep : Bool := false)
    (before : Option EventObject := none)
    (after : Option EventObject := none)
    (cause : EventCause) : GameEvent :=
  let b := before.getD { id := some card, owner := player, zone := .library player }
  let a := after.getD { b with id := some card, owner := player, zone := .hand player }
  rules turn
    (.zone (.moved b a (.library player) (.hand player) (.draw nth firstOfOwnDrawStep) (some player)))
    cause

/-- `player` gained or lost life (CR 119.2 / 119.3). -/
def life (turn : Nat) (player : PlayerId) (amount : Nat)
    (gained : Bool := false) (fromDamage : Bool := false) (combat : Bool := false)
    (cause : EventCause) : GameEvent :=
  let ev :=
    if gained then LifeEvent.gained player amount
    else .lost player amount fromDamage combat
  rules turn (.life ev) cause

/-- Damage was dealt to an object (CR 120.3 / 120.4b). -/
def damaged (turn : Nat) (source : EventObject) (object : EventObject)
    (amount : Nat) (combat : Bool := false)
    (cause : EventCause) : GameEvent :=
  rules turn (.damage (.dealt #[{
    source := source
    recipient := .permanent object
    amount := amount
    combat := combat }])) cause

/-- Damage was dealt to a player (CR 120.3a / 120.4b). -/
def damagedPlayer (turn : Nat) (source : EventObject) (player : PlayerId)
    (amount : Nat) (combat : Bool := false)
    (cause : EventCause) : GameEvent :=
  rules turn (.damage (.dealt #[{
    source := source
    recipient := .player player
    amount := amount
    combat := combat }])) cause

/-- Result of damage to a creature (CR 120.3e): marks `amount` damage on `object`. -/
def damageMarked (turn : Nat) (object : ObjectId) (amount : Nat)
    (cause : EventCause) : GameEvent :=
  rules turn (.damage (.marked object amount)) cause

/-- Result of cleanup (CR 514.2) or regeneration (CR 701.19a): clears marked damage. -/
def damageMarkedCleared (turn : Nat) (objects : Array ObjectId)
    (cause : EventCause) : GameEvent :=
  rules turn (.damage (.markedCleared objects)) cause

/-- Damage that was prevented (CR 615.1 / 615.6). -/
def damagePrevented (turn : Nat) (source : EventObject)
    (recipient : DamageRecipient) (amount : Nat)
    (cause : EventCause) : GameEvent :=
  rules turn (.damage (.prevented source recipient amount)) cause

/-- Combat damage was assigned by attacking (`forAttackers`) or blocking
creatures (CR 510.1 / 510.4 / 703.4k). -/
def combatDamageAssigned (turn : Nat) (forAttackers : Bool)
    (assignments : Array CreatureCombatAssignment)
    (firstStrike : Bool := false)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.combat (.damageAssigned firstStrike forAttackers assignments))
    (cause.getD (.turnBased (.assignCombatDamage firstStrike)))

/-- `player` proposed casting `obj` from `fromZone` (CR 601.2a). -/
def proposed (turn : Nat) (obj : ObjectId) (player : PlayerId)
    (fromZone : Zone) (way : CastWay := .normal)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.cast (.proposed obj player fromZone way))
    (cause.getD (.gameRule .spellCast))

/-- `obj` had its modes, X value, and/or additional costs announced (CR 601.2b). -/
def announced (turn : Nat) (obj : ObjectId) (modes : Array Nat := #[])
    (x : Option Nat := none) (costs : Array AdditionalCostChoice := #[])
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.cast (.announced obj modes x costs))
    (cause.getD (.gameRule .spellCast))

/-- `obj` had its targets and/or damage division chosen (CR 601.2c–d). -/
def targeted (turn : Nat) (obj : ObjectId) (targets : Array Target)
    (division : Array Nat := #[])
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.cast (.targeted obj targets division))
    (cause.getD (.gameRule .spellCast))

/-- `player` cast `spell` from `fromZone` (CR 601.2i). -/
def spellCast (turn : Nat) (player : PlayerId) (spell : EventObject) (fromZone : Zone)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.cast (.spellCast spell player fromZone))
    (cause.getD (.gameRule .spellCast))

/-- `player` cast `spell` (CR 601.2i). -/
def cast (turn : Nat) (player : PlayerId) (spell : EventObject) (fromZone : Zone)
    (manaValue : Nat := 0) (cause : Option EventCause := none) : GameEvent :=
  let spell' := if manaValue > 0 && spell.manaValue == 0 then { spell with manaValue := manaValue } else spell
  rules turn (.cast (.spellCast spell' player fromZone))
    (cause.getD (.gameRule .spellCast))

/-- `player` declared `decls` as attackers (CR 508.1k / 508.3d). -/
def attackersDeclared (turn : Nat) (player : PlayerId)
    (decls : Array (EventObject × AttackTarget))
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.combat (.attackersDeclared player decls))
    (cause.getD (.turnBased .declareAttackers))

/-- `creature` entered the battlefield attacking or was made attacking by an effect (CR 508.4). -/
def becameAttacking (turn : Nat) (creature : EventObject) (target : AttackTarget)
    (cause : EventCause) : GameEvent :=
  rules turn (.combat (.becameAttacking creature target)) cause

/-- `player` declared `decls` as blockers (CR 509.1g). -/
def blockersDeclared (turn : Nat) (player : PlayerId)
    (decls : Array (EventObject × ObjectId))
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.combat (.blockersDeclared player decls))
    (cause.getD (.turnBased .declareBlockers))

/-- `attacker` became blocked by `blockers` (CR 509.1h / 509.3c). -/
def becameBlocked (turn : Nat) (attacker : EventObject) (blockers : Array ObjectId)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.combat (.becameBlocked attacker blockers))
    (cause.getD (.turnBased .declareBlockers))

/-- `attacker` remained unblocked after blockers were declared (CR 509.1h / 509.3g). -/
def remainedUnblocked (turn : Nat) (attacker : EventObject)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.combat (.remainedUnblocked attacker))
    (cause.getD (.turnBased .declareBlockers))

/-- `player` attacked `whom` with `attacker` (CR 508.1). -/
def attacked (turn : Nat) (player : PlayerId) (attacker : EventObject) (whom : PlayerId)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.combat (.attackersDeclared player #[(attacker, .player whom)]))
    (cause.getD (.turnBased .declareAttackers))

/-- `object` became tapped or untapped by a tap action (CR 701.26a). `nowTapped` is the result. -/
def tapped (turn : Nat) (object : EventObject) (nowTapped : Bool := true)
    (duringControllersTurn : Bool := false)
    (cause : EventCause) : GameEvent :=
  if nowTapped then
    rules turn (.permanent (.tapped object duringControllersTurn)) cause
  else
    rules turn (.permanent (.untapped object)) cause

/-- Counters were put on or removed from `object` (CR 122.1). -/
def counters (turn : Nat) (player : Option PlayerId) (object : EventObject)
    (kind : CounterKind) (n : Nat) (removed : Bool := false)
    (cause : EventCause) : GameEvent :=
  let delta := if removed then CounterDelta.removed n else .put n
  rules turn (.permanent (.counters (.object object) kind delta player)) cause

/-- `player` scried or surveilled (CR 701.22 / 701.25 / 610.1). `n` cards were looked at. `asked` is the
printed number; it defaults to `n`. -/
def looked (turn : Nat) (player : PlayerId) (n : Nat) (surveil : Bool := false)
    (asked : Nat := n) (id : Option EffectId := none)
    (top : Array ObjectId := #[]) (rest : Array ObjectId := #[])
    (cause : Option EventCause := none) : GameEvent :=
  let ev : PlayerEvent :=
    if surveil then .surveilled player top rest n asked
    else .scried player top rest n asked
  rules turn (.player ev) (cause.getD (.oneShotEffect id none (some player)))

/-- `player` sacrificed `object` (CR 701.21 / 400.7). -/
def sacrificed (turn : Nat) (player : PlayerId) (object : EventObject)
    (cause : EventCause) : GameEvent :=
  let before := { object with zone := .battlefield }
  let after := { object with zone := .graveyard object.owner, controller := none }
  rules turn
    (.zone (.moved before after .battlefield (.graveyard object.owner) .sacrifice (some player)))
    cause

/-- `player` created `object` (CR 111 / 701.7 / 707.10). -/
def created (turn : Nat) (player : PlayerId) (object : EventObject)
    (cause : EventCause) : GameEvent :=
  rules turn (.zone (.created object player)) cause

/-- `object` ceased to exist (CR 704.5d / 704.5e / 111.7). -/
def ceasedToExist (turn : Nat) (object : EventObject)
    (cause : EventCause) : GameEvent :=
  rules turn (.zone (.ceasedToExist object)) cause

/-- `player` began a turn (CR 500.1 / 500.7). -/
def turnBegan (turn : Nat) (player : PlayerId) (extra : Bool := false)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.turn (.turnBegan player extra))
    (cause.getD (.gameRule .stepAdvance))

/-- `phase` began (CR 500.1). -/
def phaseBegan (turn : Nat) (phase : Phase)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.turn (.phaseBegan phase))
    (cause.getD (.gameRule .stepAdvance))

/-- `step` began on `active`'s turn (CR 500.1). -/
def stepBegan (turn : Nat) (step : Step) (active : PlayerId := ⟨0⟩)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.turn (.stepBegan step active))
    (cause.getD (.gameRule .stepAdvance))

/-- `step` ended (CR 500.1). -/
def stepEnded (turn : Nat) (step : Step)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.turn (.stepEnded step))
    (cause.getD (.gameRule .stepAdvance))

/-- `phase` ended (CR 500.1). -/
def phaseEnded (turn : Nat) (phase : Phase)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.turn (.phaseEnded phase))
    (cause.getD (.gameRule .stepAdvance))

/-- `player`'s turn ended (CR 500.1 / 514). -/
def turnEnded (turn : Nat) (player : PlayerId)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.turn (.turnEnded player))
    (cause.getD (.gameRule .stepAdvance))

/-- `player` was granted an extra turn after `after` (CR 500.7). -/
def extraTurnAdded (turn : Nat) (player : PlayerId) (after : TurnRef := .current)
    (cause : EventCause) : GameEvent :=
  rules turn (.turn (.extraTurnAdded player after)) cause

/-- An extra `phase` was added after `afterPhase` (CR 500.8). -/
def extraPhaseAdded (turn : Nat) (phase : Phase) (afterPhase : PhaseRef := .current)
    (cause : EventCause) : GameEvent :=
  rules turn (.turn (.extraPhaseAdded phase afterPhase)) cause

/-- An extra `step` was added at `anchor` (CR 500.9). -/
def extraStepAdded (turn : Nat) (step : Step) (anchor : StepAnchor)
    (cause : EventCause) : GameEvent :=
  rules turn (.turn (.extraStepAdded step anchor)) cause

/-- The step or phase changed (CR 500.1). -/
def stepped (turn : Nat) (step : Step) (active : PlayerId)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.turn (.stepBegan step active)) (cause.getD (.gameRule .stepAdvance))

/-- `player` activated an ability `ability` of `source` (CR 602.2b / 605.3b). -/
def abilityActivated (turn : Nat) (ability : ObjectId) (source : EventObject)
    (player : PlayerId) (kind : ActivationKind)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.cast (.abilityActivated ability source player kind))
    (cause.getD (.gameRule .abilityActivated))

/-- `player` activated an ability of `source` (CR 602.2). `equip` is set when the
activation has been completed, so a proposal still being paid does not count. -/
def activated (turn : Nat) (player : PlayerId) (source : EventObject)
    (loyalty : Bool := false) (equip : Bool := false)
    (ability : ObjectId := source.id.getD ⟨0⟩)
    (loyaltyDelta : Option Int := if loyalty then some 0 else none)
    (powerUp : Bool := false) (boast : Bool := false)
    (abilityIdx : Option Nat := none) (exhaust : Bool := false)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.cast (.abilityActivated ability source player
      (.nonMana loyaltyDelta equip powerUp boast abilityIdx exhaust)))
    (cause.getD (.gameRule .abilityActivated))

/-- `ability` on `source` triggered for `controller` from batch `origin` (CR 603.2). -/
def triggered (turn : Nat) (source : EventObject) (controller : PlayerId)
    (ability : TriggeredAbility) (origin : BatchId)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.triggerQueue (.triggered source controller ability origin))
    (cause.getD (.gameRule .triggeredAbility))

/-- A triggered ability of `source` was put on the stack as `stackObj` (CR 603.3). -/
def triggerPutOnStack (turn : Nat) (stackObj : ObjectId) (source : EventObject)
    (controller : PlayerId) (spec : StackTriggerSpec := {})
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.triggerQueue (.putOnStack stackObj source controller spec))
    (cause.getD (.gameRule .triggeredAbility))

/-- Mode `mode` of a modal triggered ability on `source` was chosen (CR 603.3c / 700.2). -/
def triggerModeChosen (turn : Nat) (source : ObjectId) (mode : Nat)
    (lifetime : Bool := false)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.triggerQueue (.modeChosen source mode lifetime))
    (cause.getD (.gameRule .triggeredAbility))

/-- `original` on the stack was copied as `copy` under `controller`'s control (CR 707.10). -/
def stackObjectCopied (turn : Nat) (original : ObjectId) (copy : EventObject)
    (controller : PlayerId)
    (cause : EventCause) : GameEvent :=
  rules turn (.stackObject (.copied original copy controller)) cause

/-- `obj` was removed from the stack on resolution because all its targets were illegal (CR 608.2b). -/
def removedOnResolution (turn : Nat) (obj : EventObject)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.stackObject (.removedOnResolution obj))
    (cause.getD (.gameRule .abilityFinishedResolving))

/-- `obj` resolved (`nth` counted resolution for this ability on `turn`, or `0`
for uncounted CR 608.2n / 608.3 stack resolution; CR 608 / 610.1). -/
def resolved (turn : Nat) (player : PlayerId) (nth : Nat) (obj : EventObject)
    (id : Option EffectId := none)
    (sourceId : Option ObjectId := none)
    (ability : Option TriggeredAbility := none)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.stackObject (.resolved obj nth sourceId ability))
    (cause.getD (.oneShotEffect id (sourceId.orElse (fun _ => obj.id)) (some player)))

/-- `attachment` became attached to `host` (CR 701.3a / 303.4 / 301.5). -/
def attached (turn : Nat) (attachment : EventObject) (host : ObjectId)
    (previous : Option ObjectId := none)
    (cause : EventCause) : GameEvent :=
  rules turn (.permanent (.attached attachment host previous)) cause

/-- `attachment` became unattached from `fromHost` (CR 701.3d / 704.5n / 704.5p). -/
def unattached (turn : Nat) (attachment : EventObject) (fromHost : ObjectId)
    (cause : EventCause) : GameEvent :=
  rules turn (.permanent (.unattached attachment fromHost)) cause

/-- `object` gained or lost designation `d` (CR 400.7 / 701.15b / 701.54b / 903.3). -/
def designation (turn : Nat) (object : EventObject) (d : PermanentDesignation)
    (gained : Bool := true) (cause : EventCause) : GameEvent :=
  rules turn (.permanent (.designation object d gained)) cause

/-- `object` phased out (CR 702.26b / 702.26g). -/
def phasedOut (turn : Nat) (object : EventObject) (indirectly : Bool := false)
    (cause : EventCause) : GameEvent :=
  rules turn (.permanent (.phasedOut object indirectly)) cause

/-- `object` phased in (CR 702.26c / 702.26g). -/
def phasedIn (turn : Nat) (object : EventObject) (indirectly : Bool := false)
    (cause : EventCause) : GameEvent :=
  rules turn (.permanent (.phasedIn object indirectly)) cause

/-- `object` transformed (CR 701.27a / 712.18). -/
def transformed (turn : Nat) (object : EventObject) (nowBackFace : Bool)
    (cause : EventCause) : GameEvent :=
  rules turn (.permanent (.transformed object nowBackFace)) cause

/-- `object` was turned face up (CR 116.2b / 708.8). -/
def turnedFaceUp (turn : Nat) (object : EventObject)
    (cause : EventCause) : GameEvent :=
  rules turn (.permanent (.turnedFaceUp object)) cause

/-- `object` was turned face down (CR 708.2). -/
def turnedFaceDown (turn : Nat) (object : EventObject)
    (cause : EventCause) : GameEvent :=
  rules turn (.permanent (.turnedFaceDown object)) cause

/-- `player` beheld `quality` (CR 701.4). -/
def beheld (turn : Nat) (player : PlayerId) (quality : CardSubtype)
    (cause : EventCause) : GameEvent :=
  rules turn (.player (.beheld player quality)) cause

/-- `player` added `units` of mana to their mana pool (CR 106.4 / 605.3b). -/
def manaAdded (turn : Nat) (player : PlayerId) (units : Array ManaUnit)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.manaAdded player units))
    (cause.getD (.gameRule .abilityActivated))

/-- `player` spent `units` of mana for `forObject` (CR 118.3 / 601.2h). -/
def manaSpent (turn : Nat) (player : PlayerId) (units : Array ManaUnit)
    (forObject : ObjectId := ⟨0⟩)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.manaSpent player units forObject))
    (cause.getD (.costPayment .mana player (some forObject)))

/-- `player` spent mana (CR 118.3). -/
def spentMana (turn : Nat) (player : PlayerId) (amount : Nat)
    (forObject : Option ObjectId := none)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn
    (.player (.manaSpent player (Array.replicate amount { mana := .colorless }) (forObject.getD ⟨0⟩)))
    (cause.getD (.costPayment .mana player forObject))

/-- `player` looked at `cards`. -/
def lookedAt (turn : Nat) (player : PlayerId) (cards : Array ObjectId)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.lookedAt player cards))
    (cause.getD (.oneShotEffect none none (some player)))

/-- `player` revealed `cards` (CR 701.20). -/
def revealed (turn : Nat) (player : PlayerId) (cards : Array ObjectId)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.revealed player cards))
    (cause.getD (.oneShotEffect none none (some player)))

/-- `player` searched `libraryOwner`'s library, finding `found` (CR 701.23). -/
def searched (turn : Nat) (player : PlayerId) (libraryOwner : PlayerId)
    (found : Array ObjectId := #[])
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.searched player libraryOwner found))
    (cause.getD (.oneShotEffect none none (some player)))

/-- `libraryOwner`'s library was shuffled into `newOrder` (CR 701.24). -/
def shuffled (turn : Nat) (libraryOwner : PlayerId) (newOrder : Array ObjectId)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.shuffled libraryOwner newOrder))
    (cause.getD (.oneShotEffect none none (some libraryOwner)))

/-- `player` became the monarch (CR 725). -/
def becameMonarch (turn : Nat) (player : PlayerId) (previous : Option PlayerId := none)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.becameMonarch player previous))
    (cause.getD (.oneShotEffect none none (some player)))

/-- `player` gained lasting designation `d` (CR 702.131). -/
def gainedDesignation (turn : Nat) (player : PlayerId) (d : PlayerDesignation)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.gainedDesignation player d))
    (cause.getD (.gameRule .staticAbility))

/-- The game ended with `result` (CR 104). -/
def gameEnded (turn : Nat) (result : GameResult)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.gameEnded result))
    (cause.getD (.gameRule .playerLeftGame))

/-- `player` got poison counters (CR 122.1f). -/
def poisoned (turn : Nat) (player : PlayerId) (n : Nat)
    (byPlayer : Option PlayerId := none)
    (cause : EventCause) : GameEvent :=
  rules turn (.permanent (.counters (.player player) .poison (.put n) byPlayer)) cause

/-- `player` proliferated (CR 701.34 / 610.1). -/
def proliferated (turn : Nat) (player : PlayerId)
    (id : Option EffectId := none)
    (permanents : Array ObjectId := #[]) (players : Array PlayerId := #[])
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.proliferated player permanents players))
    (cause.getD (.oneShotEffect id none (some player)))

/-- The Ring tempted `player` at `stage` with `bearer` (CR 701.54). -/
def ringTempted (turn : Nat) (player : PlayerId) (bearer : Option ObjectId)
    (stage : Nat) (id : Option EffectId := none)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.ringTempted player bearer stage))
    (cause.getD (.oneShotEffect id none (some player)))

/-- `player` chose to have The Sensational She-Hulk deal damage (CR 610.1). -/
def sheHulkDealtDamage (turn : Nat) (player : PlayerId)
    (id : Option EffectId := none) (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.sheHulkDealtDamage player))
    (cause.getD (.oneShotEffect id none (some player)))

/-- `player` chose the optional once-each-turn action of `source` (MSH 69). -/
def optionalOnceActed (turn : Nat) (player : PlayerId) (source : ObjectId)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.optionalOnceActed player source))
    (cause.getD (.oneShotEffect none (some source) (some player)))

/-- `player` attempted to draw a card from an empty library (CR 121.4 / 704.5b). -/
def drawFromEmptyAttempted (turn : Nat) (player : PlayerId)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.drawFromEmptyAttempted player))
    (cause.getD (.turnBased .drawStepDraw))

/-- `object` untapped (CR 701.26b). -/
def untapped (turn : Nat) (object : EventObject) (cause : EventCause) : GameEvent :=
  rules turn (.permanent (.untapped object)) cause

/-- `object` was removed from combat (CR 506.4 / 511.3 / 702.26b). -/
def removedFromCombat (turn : Nat) (object : EventObject)
    (cause : EventCause) : GameEvent :=
  rules turn (.combat (.removedFromCombat object)) cause

/-- `player`'s mana pool emptied (CR 500.5 / 703.4q). -/
def manaEmptied (turn : Nat) (player : PlayerId)
    (units : Array ManaUnit := #[]) (keptColorless : Bool := false)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.manaEmptied player units keptColorless))
    (cause.getD (.turnBased .emptyManaPools))

/-- `player` lost the game (CR 104.3 / 704.5a–c). -/
def playerLost (turn : Nat) (player : PlayerId)
    (reason : LossReason := .lifeZeroOrLess)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.lost player reason))
    (cause.getD (.stateBased .lifeZeroOrLess))

/-- `player` left the game (CR 104.5 / 800.4a). -/
def playerLeftGame (turn : Nat) (player : PlayerId)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.leftGame player))
    (cause.getD (.gameRule .playerLeftGame))

/-- A continuous effect begins (CR 611). -/
def effectCreated (turn : Nat) (id : EffectId) (spec : ContinuousEffectSpec)
    (cause : EventCause) : GameEvent :=
  rules turn (.continuousEffect (.created id spec)) cause

/-- A continuous effect ends (CR 611). -/
def effectExpired (turn : Nat) (id : EffectId) (_spec : Option ContinuousEffectSpec := none)
    (cause : EventCause) : GameEvent :=
  rules turn (.continuousEffect (.expired id)) cause

/-- Delayed triggered ability `dt` was created (CR 603.7). -/
def delayedTriggerCreated (turn : Nat) (dt : DelayedTrigger)
    (cause : EventCause := dt.cause) (batch : BatchId := ⟨0⟩) : GameEvent :=
  rules turn (.delayedTrigger (.created dt)) cause batch

/-- One-shot delayed triggered ability `dt` triggered and was consumed (CR 603.7b). -/
def delayedTriggerConsumed (turn : Nat) (dt : DelayedTrigger)
    (cause : EventCause := .gameRule .triggeredAbility) (batch : BatchId := ⟨0⟩) : GameEvent :=
  rules turn (.delayedTrigger (.consumed dt)) cause batch

/-- Duration-scoped delayed triggered ability `dt` expired (CR 603.7b / 514.2 / 800.4i). -/
def delayedTriggerExpired (turn : Nat) (dt : DelayedTrigger)
    (cause : EventCause) (batch : BatchId := ⟨0⟩) : GameEvent :=
  rules turn (.delayedTrigger (.expired dt)) cause batch

/-- Same event, sent to `toZone` instead. Used after a zone replacement (CR 614.6). -/
def withDestination (e : GameEvent) (toZone : Zone) (discarded : Bool) : GameEvent :=
  match e.change with
  | .rules (.zone (.moved before after fromZone origTo verb actor entersWith libPos)) =>
    let verb' :=
      if verb == .sacrifice then .sacrifice
      else if discarded || verb == .discard then .discard
      else if verb == .mill then .mill
      else if toZone != origTo && toZone == .exile then .exile
      else verb
    let after' := { after with
      zone := toZone
      controller := if toZone == .battlefield || toZone == .stack then after.controller else none
      tapped := if toZone == .battlefield then after.tapped else false
      counters := if toZone == .battlefield then after.counters else #[] }
    let entersWith' := if toZone == .battlefield then entersWith else #[]
    e.withRules (.zone (.moved before after' fromZone toZone verb' actor entersWith' libPos))
  | _ => e

/-- A creature moved from the battlefield to a graveyard (CR 700.4). -/
def isCreatureToGraveyard (e : GameEvent) : Bool :=
  match e.change with
  | .rules (.zone (.moved before _ .battlefield (.graveyard _) _ _ _ _)) => before.creature
  | _ => false

/-- A permanent moved from the battlefield to a graveyard. -/
def isPermanentToGraveyard (e : GameEvent) : Bool :=
  match e.change with
  | .rules (.zone (.moved _ _ .battlefield (.graveyard _) _ _ _ _)) => true
  | _ => false

/-- An object left the stack for another zone. -/
def leavesStack (e : GameEvent) : Bool :=
  match e.change with
  | .rules (.zone (.moved _ _ .stack toZone _ _ _ _)) => toZone != .stack
  | _ => false

/-- An instant or sorcery moved from the stack to its owner's graveyard. -/
def entersOwnGraveyardFromStack (e : GameEvent) : Bool :=
  match e.change with
  | .rules (.zone (.moved before _ .stack (.graveyard owner) _ _ _ _)) =>
    before.instantOrSorcery && owner == before.owner
  | _ => false

/-- A permanent entered the battlefield. -/
def enteredBattlefield (e : GameEvent) : Bool :=
  match e.change with
  | .rules (.zone (.moved _ _ _ .battlefield _ _ _ _)) => true
  | _ => false

/-- The kind of event a replacement effect watches (CR 614.1). -/
inductive ReplacementWatch where
  /-- A creature would die. -/
  | wouldDie
  /-- A permanent would move from the battlefield to a graveyard. -/
  | wouldEnterGraveyardFromBattlefield
  /-- An object would leave the stack. -/
  | wouldLeaveStack
  /-- An instant or sorcery would go from the stack to its owner's graveyard. -/
  | wouldEnterGraveyardFromStack
  /-- A player would draw a card. -/
  | wouldDraw
  /-- A player would gain life. -/
  | wouldGainLife
  /-- Damage would be dealt. -/
  | wouldDealDamage
  /-- A permanent would enter the battlefield. -/
  | wouldEnterBattlefield
  /-- A token would be created. -/
  | wouldCreateToken
  /-- Counters would be put on an object. -/
  | wouldPutCounter
  /-- A permanent would untap. -/
  | wouldUntap
deriving Repr, Inhabited, BEq, DecidableEq

/-- Whether this change is one `watch` replaces or modifies. -/
def watches (e : GameEvent) (watch : ReplacementWatch) : Bool :=
  match watch with
  | .wouldDie => e.isCreatureToGraveyard
  | .wouldEnterGraveyardFromBattlefield => e.isPermanentToGraveyard
  | .wouldLeaveStack => e.leavesStack
  | .wouldEnterGraveyardFromStack => e.entersOwnGraveyardFromStack
  | .wouldDraw =>
    match e.change with
    | .rules (.zone (.moved _ _ _ _ (.draw _ _) _ _ _)) => true
    | _ => false
  | .wouldGainLife =>
    match e.change with
    | .rules (.life (.gained _ _)) => true
    | _ => false
  | .wouldDealDamage =>
    match e.change with
    | .rules (.damage (.dealt _)) => true
    | _ => false
  | .wouldEnterBattlefield => e.enteredBattlefield
  | .wouldCreateToken =>
    match e.change with
    | .rules (.zone (.created object _)) => object.zone == .battlefield && object.token
    | _ => false
  | .wouldPutCounter =>
    match e.change with
    | .rules (.permanent (.counters _ _ (.put n) _)) => n > 0
    | .rules (.zone (.moved _ _ _ .battlefield _ _ entersWith _)) =>
      entersWith.any (fun (_, n) => n > 0)
    | _ => false
  | .wouldUntap =>
    match e.change with
    | .rules (.permanent (.untapped _)) => true
    | _ => false

/-- `listener`'s ability on `sourceId` triggers from this change.
“This” abilities require `sourceId` to be the object that changed.
“You” abilities require `listener` to be the player who did it.
An event this change does not describe does not match. -/
def matchesTrigger (e : GameEvent) (listener : PlayerId) (sourceId : ObjectId)
    (te : TriggerEvent) : Bool :=
  let you (p : PlayerId) : Bool := p == listener
  let this (o : EventObject) : Bool := o.id == some sourceId
  let yours (o : EventObject) : Bool := o.controller == some listener
  let other (o : EventObject) : Bool := o.id.any (· != sourceId)
  match e.change with
  | .engine _ => false
  | .rules r =>
    match r, te with
    | .zone (.moved _ _ _ _ (.draw _ _) (some p) _ _), .youDraw => you p
    | .zone (.moved _ _ _ _ (.draw nth _) (some p) _ _), .youDrawSecondCard => you p && nth == 2
    | .zone (.moved _ _ _ _ (.draw nth _) _ _ _), .anyPlayerDrawsSecond => nth == 2
    | .zone (.moved _ _ _ _ (.draw _ first) (some p) _ _), .opponentDrawsExceptFirstDrawStep => !you p && !first
    | .zone (.moved _ _ _ _ (.draw nth _) (some p) _ _), .opponentDrawsSecondCard => !you p && nth == 2
    | .life (.gained p _), .youGainLife => you p
    | .life (.lost _ _ _ _), .playerLosesLife => true
    | .damage (.dealt pkts), .sourceDealtDamage =>
      pkts.any (fun pkt => match pkt.recipient with | .permanent o | .battle o => this o | .player _ => false)
    | .damage (.dealt pkts), .sourceDealtNoncombatDamage =>
      pkts.any (fun pkt => !pkt.combat && match pkt.recipient with | .permanent o | .battle o => this o | .player _ => false)
    | .damage (.dealt pkts), .creatureYouControlDealtDamage =>
      pkts.any (fun pkt => match pkt.recipient with | .permanent o => yours o && o.creature | _ => false)
    | .damage (.dealt pkts), .dealsCombatDamageToPlayer =>
      pkts.any (fun pkt => pkt.combat && match pkt.recipient with | .player _ => true | _ => false)
    | .damage (.dealt pkts), .fra .dealsCombatDamageToPlayerOrPlaneswalker =>
      pkts.any (fun pkt =>
        pkt.combat &&
          match pkt.recipient with
          | .player _ => true
          | .permanent o => o.planeswalker
          | .battle _ => false)
    | .damage (.dealt pkts), .dealsCombatDamageToPlayerOrBattle =>
      pkts.any (fun pkt => pkt.combat && match pkt.recipient with | .player _ | .battle _ => true | _ => false)
    | .damage (.dealt pkts), .combatDamageToYou =>
      pkts.any (fun pkt => pkt.combat && match pkt.recipient with | .player p => you p | _ => false)
    | .damage (.dealt pkts), .opponentsDealtCombatDamageYourTurn =>
      pkts.any (fun pkt => pkt.combat && pkt.amount > 0 && match pkt.recipient with | .player p => !you p | _ => false)
    | .damage (.dealt pkts), .fra .opponentsDealtNoncombatDamage =>
      pkts.any (fun pkt => !pkt.combat && pkt.amount > 0 && match pkt.recipient with | .player p => !you p | _ => false)
    | .damage (.dealt pkts), .heroesDealDamageToPlayer =>
      pkts.any (fun pkt =>
        match pkt.recipient with
        | .player _ => yours pkt.source && pkt.source.hero
        | _ => false)
    | .zone (.moved before _ .battlefield (.graveyard _) _ _ _ _), .dying =>
      this before && before.creature
    | .zone (.moved before _ .battlefield _ _ _ _ _), .leaving => this before
    | .zone (.ceasedToExist before), .leaving => before.zone == .battlefield && this before
    | .zone (.moved before after _ .battlefield _ _ _ _), .entering => this after || this before
    | .zone (.created object _), .entering => object.zone == .battlefield && this object
    | .zone (.moved _ after _ .battlefield _ _ _ _), .landYouControlEnters =>
      yours after && after.land
    | .zone (.created object controller), .landYouControlEnters =>
      object.zone == .battlefield && you controller && object.land
    | .zone (.moved _ after _ .battlefield _ _ _ _), .forestYouControlEnters =>
      yours after && after.forest
    | .zone (.created object controller), .forestYouControlEnters =>
      object.zone == .battlefield && you controller && object.forest
    | .zone (.moved _ after _ .battlefield _ _ _ _), .mountainYouControlEnters =>
      yours after && after.mountain
    | .zone (.created object controller), .mountainYouControlEnters =>
      object.zone == .battlefield && you controller && object.mountain
    | .zone (.moved _ after _ .battlefield _ _ _ _), .artifactYouControlEnters =>
      yours after && after.artifact
    | .zone (.created object controller), .artifactYouControlEnters =>
      object.zone == .battlefield && you controller && object.artifact
    | .zone (.moved _ after _ .battlefield _ _ _ _), .creatureYouControlEnters =>
      yours after && after.creature
    | .zone (.created object controller), .creatureYouControlEnters =>
      object.zone == .battlefield && you controller && object.creature
    | .zone (.moved _ after _ .battlefield _ _ _ _), .anotherCreatureYouControlEnters =>
      yours after && other after && after.creature
    | .zone (.created object controller), .anotherCreatureYouControlEnters =>
      object.zone == .battlefield && you controller && other object && object.creature
    | .zone (.moved _ after _ .battlefield _ _ _ _), .anotherElfYouControlEnters =>
      yours after && other after && after.elf
    | .zone (.created object controller), .anotherElfYouControlEnters =>
      object.zone == .battlefield && you controller && other object && object.elf
    | .zone (.moved _ after _ .battlefield _ _ _ _), .tokenYouControlEnters =>
      yours after && after.token
    | .zone (.created object controller), .tokenYouControlEnters =>
      object.zone == .battlefield && you controller && object.token
    | .zone (.moved _ after _ .battlefield _ _ _ _), .equipmentYouControlEnters =>
      yours after && after.equipment
    | .zone (.created object controller), .equipmentYouControlEnters =>
      object.zone == .battlefield && you controller && object.equipment
    | .zone (.moved _ after _ .battlefield _ _ _ _), .anotherArtifactEnters =>
      yours after && other after && after.artifact
    | .zone (.created object controller), .anotherArtifactEnters =>
      object.zone == .battlefield && you controller && other object && object.artifact
    | .zone (.moved _ after _ .battlefield _ _ _ _), .anotherVillainEnters =>
      yours after && other after && after.villain
    | .zone (.created object controller), .anotherVillainEnters =>
      object.zone == .battlefield && you controller && other object && object.villain
    | .zone (.moved _ after _ .battlefield _ _ _ _), .anotherVillainOrArtifactEnters =>
      yours after && other after && (after.villain || after.artifact)
    | .zone (.created object controller), .anotherVillainOrArtifactEnters =>
      object.zone == .battlefield && you controller && other object && (object.villain || object.artifact)
    | .zone (.moved _ after _ .battlefield _ _ _ _), .anotherNontokenHeroEnters =>
      yours after && other after && !after.token && after.hero
    | .zone (.created object controller), .anotherNontokenHeroEnters =>
      object.zone == .battlefield && you controller && other object && !object.token && object.hero
    | .zone (.moved _ after _ .battlefield _ _ _ _), .anotherNontokenArtifactEnters =>
      yours after && other after && !after.token && after.artifact
    | .zone (.created object controller), .anotherNontokenArtifactEnters =>
      object.zone == .battlefield && you controller && other object && !object.token && object.artifact
    | .zone (.moved before _ .battlefield (.graveyard _) _ _ _ _), .creatureYouControlDies =>
      yours before && before.creature
    | .zone (.moved before _ .battlefield (.graveyard _) _ _ _ _), .nontokenYouControlDies =>
      yours before && before.creature && !before.token
    | .zone (.moved before _ .battlefield (.graveyard _) _ _ _ _), .anotherGoblinOrcArmyDies =>
      yours before && other before && before.creature && before.goblinOrcArmy
    | .zone (.moved before _ .battlefield (.graveyard _) _ _ _ _), .villainYouControlDies =>
      yours before && other before && before.creature && before.villain
    | .zone (.moved before _ .battlefield (.graveyard _) _ _ _ _), .attackingCreatureYouControlDies =>
      yours before && before.creature && before.attacking
    | .zone (.moved before _ .battlefield (.graveyard _) _ _ _ _), .oneOrMoreOtherCreaturesDie =>
      other before && before.creature
    | .zone (.moved before _ .battlefield (.hand _) _ _ _ _), .anotherNonlandReturned =>
      yours before && other before && !before.land
    | .zone (.moved before _ (.graveyard owner) _ _ _ _ _), .creatureCardLeavesYourGy =>
      you owner && before.creature
    | .zone (.moved before _ _ (.graveyard owner) _ _ _ _), .creatureCardsPutIntoYourGy =>
      you owner && before.creature && !before.token
    | .zone (.moved _ _ (.hand p) toZone .discard _ _ _), .youDiscard =>
      you p && toZone != .hand p
    | .zone (.moved before after (.hand p) toZone .discard _ _ _), .fra .youDiscardThis =>
      you p && toZone != .hand p && (this before || this after)
    | .zone (.moved before after (.hand p) toZone .discard _ _ _), .fra .youCycle =>
      you p && toZone != .hand p && (this before || this after) &&
        match e.cause? with | some (.costPayment .cycle _ _) => true | _ => false
    | .zone (.moved _ _ (.hand p) toZone .discard _ _ _), .fra .youDiscardOne =>
      you p && toZone != .hand p
    | .zone (.moved _ _ (.hand p) toZone .discard _ _ _), .fra .playerDiscards =>
      toZone != .hand p
    | .zone (.moved before _ .battlefield (.graveyard _) _ _ _ _), .fra .enchantedDies =>
      before.creature
    | .zone (.moved before _ .battlefield (.graveyard _) _ _ _ _), .fra .nontokenCreatureYouControlDies =>
      yours before && before.creature && !before.token
    | .zone (.moved before _ .battlefield (.graveyard _) _ _ _ _), .fra .anotherCreatureOrPlaneswalkerYouControlDies =>
      yours before && other before && (before.creature || before.planeswalker)
    | .zone (.moved before _ .battlefield _ _ _ _ _), .fra .creatureYouControlLeaves =>
      yours before && other before && before.creature
    | .zone (.ceasedToExist before), .fra .creatureYouControlLeaves =>
      before.zone == .battlefield && yours before && other before && before.creature
    | .zone (.moved _ after _ .battlefield _ _ _ _), .subtypeYouControlEnters sub =>
      yours after && after.hasSubtype sub
    | .zone (.created object controller), .subtypeYouControlEnters sub =>
      object.zone == .battlefield && you controller && object.hasSubtype sub
    | .zone (.moved before after _ .battlefield _ _ entersWith _), .sagaChapter =>
      (this after || this before) && entersWith.count .lore > 0
    | .zone (.created object _), .sagaChapter =>
      object.zone == .battlefield && this object && object.counters.count .lore > 0
    | .zone (.moved before after _ .battlefield _ _ entersWith _), .nthPlanCounter _ =>
      (this after || this before) && entersWith.count .plan > 0
    | .zone (.created object _), .nthPlanCounter _ =>
      object.zone == .battlefield && this object && object.counters.count .plan > 0
    | .zone (.moved _ after _ .battlefield _ actor entersWith _), .youPutPlusOne =>
      let p := actor.orElse (fun _ => after.controller)
      p.any you && entersWith.count .plusOnePlusOne > 0 && after.creature
    | .zone (.created object controller), .youPutPlusOne =>
      object.zone == .battlefield && you controller && object.counters.count .plusOnePlusOne > 0 && object.creature
    | .zone (.moved _ after _ .battlefield _ actor entersWith _), .youPutCountersOnGoblinOrcArmy =>
      let p := actor.orElse (fun _ => after.controller)
      p.any you && yours after && entersWith.any (fun (_, n) => n > 0) && after.goblinOrcArmy
    | .zone (.created object controller), .youPutCountersOnGoblinOrcArmy =>
      object.zone == .battlefield && you controller && yours object && object.counters.any (fun (_, n) => n > 0) && object.goblinOrcArmy
    | .zone (.moved _ after _ .battlefield _ actor entersWith _), .fra .youPutLoyaltyCounters =>
      let p := actor.orElse (fun _ => after.controller)
      p.any you && entersWith.count .loyalty > 0 && after.planeswalker
    | .zone (.created object controller), .fra .youPutLoyaltyCounters =>
      object.zone == .battlefield && you controller && object.counters.count .loyalty > 0 && object.planeswalker
    | .cast (.spellCast spell p _), .youCastInstantOrSorcery =>
      you p && spell.instantOrSorcery
    | .cast (.spellCast spell p _), .youCastNoncreature =>
      you p && !spell.creature
    | .cast (.spellCast spell p _), .youCastCreature =>
      you p && spell.creature
    | .cast (.spellCast _ p _), .youCastSpell => you p
    | .cast (.spellCast _ p _), .youCastColor _ => you p
    | .cast (.spellCast _ p (.hand _)), .youCastColorFromHand _ => you p
    | .cast (.spellCast _ p _), .youCastGreen => you p
    | .cast (.spellCast spell p _), .youCastVillain => you p && spell.villain
    | .cast (.spellCast _ p _), .opponentCastsSpell => !you p
    | .cast (.spellCast spell p _), .youCastFirstNoncreature => you p && !spell.creature
    | .cast (.spellCast _ p _), .youCastSecondSpell => you p
    | .cast (.spellCast _ _ _), .anyPlayerCastsSecondSpell => true
    | .cast (.spellCast _ p _), .opponentCastsFirstNoncreature => !you p
    | .cast (.spellCast spell p _), .fra .castThis => you p && this spell
    | .combat (.attackersDeclared p decls), .attacking =>
      you p && decls.any (fun (attacker, _) => this attacker)
    | .combat (.attackersDeclared p decls), .youAttack =>
      you p && !decls.isEmpty
    | .combat (.attackersDeclared p decls), .youAttackWithElves =>
      you p && decls.any (fun (attacker, _) => attacker.elf)
    | .combat (.attackersDeclared p decls), .youAttackWithTwoOrMore =>
      you p && !decls.isEmpty
    | .combat (.attackersDeclared p decls), .creatureYouControlAttacksAlone =>
      you p && decls.any (fun (attacker, _) => attacker.creature)
    | .combat (.attackersDeclared p decls), .equippedAttacks =>
      you p && !decls.isEmpty
    | .combat (.attackersDeclared p decls), .equippedCreatureYouControlAttacks =>
      you p && decls.any (fun (attacker, _) => attacker.creature)
    | .combat (.attackersDeclared p decls), .merfolkAttackPlayer =>
      you p && decls.any (fun (attacker, _) => attacker.merfolk)
    | .combat (.attackersDeclared p decls), .fra .creatureYouControlAttacks =>
      you p && decls.any (fun (attacker, _) => attacker.creature)
    | .combat (.becameBlocked attacker _), .becomesBlocked =>
      this attacker
    | .permanent (.tapped object _), .sourceBecomesTapped => this object
    | .permanent (.tapped object _), .creaturesYouControlBecomeTapped =>
      yours object && object.creature
    | .permanent (.tapped object _), .equippedBecomesTapped => object.creature
    | .permanent (.tapped object during), .creatureYouControlTapped =>
      yours object && object.creature && during
    | .permanent (.tapped object _), .tappedForTeamwork =>
      this object && match e.cause? with | some (.costPayment .teamwork _ _) => true | _ => false
    | .player (.scried p _ _ _ asked), .youScry => you p && asked > 0
    | .player (.scried p _ _ _ asked), .youScryOrSurveil => you p && asked > 0
    | .player (.surveilled p _ _ _ asked), .youScryOrSurveil => you p && asked > 0
    | .player (.proliferated p _ _), .fra .youProliferate => you p
    | .player (.ringTempted p _ _), .theRingTemptsYou => you p
    | .player (.ringTempted p (some _) _), .youChooseRingBearer => you p
    | .stackObject (.resolved obj nth _ _), .finalSagaChapterResolves =>
      nth == 0 && yours obj && obj.types.isEmpty && obj.hasSubtype .saga
    | .permanent (.counters (.object object) .plusOnePlusOne (.put n) (some p)), .youPutPlusOne =>
      you p && n > 0 && object.creature
    | .permanent (.counters (.object object) _ (.put n) (some p)), .youPutCountersOnGoblinOrcArmy =>
      you p && yours object && n > 0 && object.goblinOrcArmy
    | .permanent (.counters (.object object) .loyalty (.put n) (some p)), .fra .youPutLoyaltyCounters =>
      you p && n > 0 && object.planeswalker
    | .permanent (.counters (.object object) .plan (.put n) _), .nthPlanCounter _ =>
      this object && n > 0
    | .permanent (.counters (.object object) .lore (.put n) _), .sagaChapter =>
      this object && n > 0
    | .turn (.stepBegan .upkeep active), .yourUpkeep => you active
    | .turn (.stepBegan .upkeep _), .eachUpkeep => true
    | .turn (.stepBegan .upkeep _), .fra .eachUpkeepFromGraveyard => true
    | .turn (.stepBegan .end active), .yourEndStep => you active
    | .turn (.stepBegan .end _), .eachEndStep => true
    | .turn (.stepBegan .beginningOfCombat active), .yourBeginCombat => you active
    | .turn (.stepBegan .beginningOfCombat active), .fra .yourBeginCombatFromGraveyard => you active
    | .turn (.stepBegan .beginningOfCombat _), .eachBeginCombat => true
    | .turn (.stepBegan .beginningOfCombat active), .fra .opponentBeginCombat => !you active
    | .turn (.stepBegan .precombatMain active), .yourFirstMain => you active
    | .turn (.stepBegan .draw active), .eachOpponentDrawStep => !you active
    | .turn (.stepBegan .upkeep _), .eaglesCreateBirds => true
    | .turn (.stepBegan .upkeep active), .enchantedControllerUpkeep => you active
    | .zone (.moved before _ .battlefield toZone .sacrifice actor _ _), .youSacrificeToken =>
      let p := actor.getD (before.controller.getD before.owner)
      you p && before.token && toZone != .battlefield
    | .cast (.abilityActivated _ _ p (.nonMana (some _) ..)), .youActivateLoyaltyAbility => you p
    | .cast (.abilityActivated _ source p _), .youActivateCreatureAbility =>
      you p && source.creature
    | .cast (.abilityActivated _ _ p (.nonMana (some _) ..)), .fra .opponentActivatesLoyaltyAbility => !you p
    | .cast (.targeted _ targets _), .becomesTarget =>
      targets.any (fun t => match t with | .permanent oid => oid == sourceId | _ => false)
    | .zone (.created object p), .fra .youCreateCreatureTokens =>
      object.zone == .battlefield && object.token && you p && object.creature
    | _, _ => false

/-- Counters put on objects in `e` (CR 122.1 / 122.6), including counters
placed as an object enters the battlefield via `ZoneEvent.moved.entersWith`
or `ZoneEvent.created`. -/
def countersPutInEvent (e : GameEvent) : Array (EventObject × CounterKind × Nat × Option PlayerId) :=
  match e.change with
  | .rules (.permanent (.counters (.object o) kind (.put n) actor)) =>
    if n > 0 then #[(o, kind, n, actor)] else #[]
  | .rules (.zone (.moved _ after _ .battlefield _ actor entersWith _)) =>
    entersWith.foldl (fun acc (kind, n) =>
      if n > 0 then acc.push (after, kind, n, actor.orElse (fun _ => after.controller)) else acc) #[]
  | .rules (.zone (.created object controller)) =>
    if object.zone != .battlefield then #[]
    else
      object.counters.foldl (fun acc (kind, n) =>
        if n > 0 then acc.push (object, kind, n, some controller) else acc) #[]
  | _ => #[]

/-- All counters put on objects in `events` (CR 122.1 / 122.6), including
`entersWith` counters on entering permanents. -/
def countersPut (events : Array GameEvent) : Array (EventObject × CounterKind × Nat × Option PlayerId) :=
  events.foldl (fun acc e => acc ++ e.countersPutInEvent) #[]

/-- Cards `p` drew on `turn` in `events`. -/
def draws (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.zone (.moved _ _ _ _ (.draw _ _) (some q) _ _)) => if q == p then n + 1 else n
      | _ => n) 0

/-- Life `p` gained on `turn`. -/
def lifeGained (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.life (.gained q amount)) => if q == p then n + amount else n
      | _ => n) 0

/-- Creatures that died on `turn`. -/
def creatureDeaths (events : Array GameEvent) (turn : Nat) : Nat :=
  events.foldl (fun n e =>
    if e.turn == turn && e.isCreatureToGraveyard then n + 1 else n) 0

/-- Spells `p` cast on `turn`. -/
def spellsCast (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.cast (.spellCast _ q _)) => if q == p then n + 1 else n
      | _ => n) 0

/-- `p` scried at least one card on `turn`. -/
def scried (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .rules (.player (.scried q _ _ _ asked)) => q == p && asked > 0
      | _ => false

/-- `p` surveilled on `turn`. Surveil 0 does not count. -/
def surveilled (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .rules (.player (.surveilled q _ _ _ asked)) => q == p && asked > 0
      | _ => false

/-- An artifact entered under `p`'s control on `turn`. -/
def artifactEntered (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .rules (.zone (.moved _ after _ .battlefield _ _ _ _)) =>
        after.controller == some p && after.artifact
      | .rules (.zone (.created object q)) =>
        object.zone == .battlefield && q == p && object.artifact
      | _ => false

/-- `p` attacked with a permanent of `subtype` on `turn`. -/
def attackedWithSubtype (events : Array GameEvent) (turn : Nat) (p : PlayerId)
    (subtype : CardSubtype) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .rules (.combat (.attackersDeclared q decls)) =>
        q == p && decls.any (fun (attacker, _) => attacker.hasSubtype subtype)
      | _ => false

/-- A permanent of `subtype` entered under `p`'s control on `turn`. -/
def subtypeEntered (events : Array GameEvent) (turn : Nat) (p : PlayerId)
    (subtype : CardSubtype) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .rules (.zone (.moved _ after _ .battlefield _ _ _ _)) =>
        after.controller == some p && after.hasSubtype subtype
      | .rules (.zone (.created object q)) =>
        object.zone == .battlefield && q == p && object.hasSubtype subtype
      | _ => false

/-- `p` activated a loyalty ability on `turn`. -/
def activatedLoyalty (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .rules (.cast (.abilityActivated _ _ q (.nonMana (some _) ..))) => q == p
      | _ => false

/-- `p` was dealt noncombat damage on `turn`. -/
def dealtNoncombat (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .rules (.damage (.dealt pkts)) =>
        pkts.any (fun pkt => !pkt.combat && pkt.recipient == .player p)
      | .rules (.life (.lost q _ true false)) => q == p
      | _ => false

/-- Mana recorded for `spell` when it was cast, if the log has that payment. -/
def manaSpentOn (events : Array GameEvent) (spell : ObjectId) : Nat :=
  events.foldl (fun n e =>
    match e.change, e.cause? with
    | .rules (.player (.manaSpent _ units forObj)), some (.costPayment .mana _ oid?) =>
      if forObj == spell || oid? == some spell then max n units.size else n
    | .rules (.player (.manaSpent _ units forObj)), _ =>
      if forObj == spell then max n units.size else n
    | _, _ => n) 0

/-- Whether `srcId` was recorded as a Treasure permanent when its mana ability was activated. -/
private def isTreasureSourceInLog (events : Array GameEvent) (srcId : ObjectId) : Bool :=
  events.any fun e =>
    match e.change with
    | .rules (.cast (.abilityActivated id snap _ _)) =>
      id == srcId && snap.subtypes.contains .treasure
    | _ => false

/-- Whether `u` came from a Treasure source (via spending restriction or `source` provenance). -/
private def isTreasureManaUnit (events : Array GameEvent) (u : ManaUnit) : Bool :=
  u.restriction == some (.fra .fromTreasure) || u.source.any (isTreasureSourceInLog events)

/-- Whether mana from a Treasure was spent to cast `spell` (CR 106.6). -/
def treasureManaSpentOn (events : Array GameEvent) (spell : ObjectId) : Bool :=
  events.any fun e =>
    match e.change, e.cause? with
    | .rules (.player (.manaSpent _ units forObj)), some (.costPayment .mana _ oid?) =>
      (forObj == spell || oid? == some spell) &&
        units.any (isTreasureManaUnit events)
    | .rules (.player (.manaSpent _ units forObj)), _ =>
      forObj == spell && units.any (isTreasureManaUnit events)
    | _, _ => false

/-- Whether legendary-restricted mana (Delighted Halfling) was spent to cast `spell` (CR 106.6). -/
def legendaryManaSpentOn (events : Array GameEvent) (spell : ObjectId) : Bool :=
  events.any fun e =>
    match e.change, e.cause? with
    | .rules (.player (.manaSpent _ units forObj)), some (.costPayment .mana _ oid?) =>
      (forObj == spell || oid? == some spell) &&
        units.any (·.restriction == some (.fra .legendarySpell))
    | .rules (.player (.manaSpent _ units forObj)), _ =>
      forObj == spell && units.any (·.restriction == some (.fra .legendarySpell))
    | _, _ => false

/-- Creature spells `p` cast on `turn`. -/
def creatureSpells (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.cast (.spellCast spell q _)) => if q == p && spell.creature then n + 1 else n
      | _ => n) 0

/-- Noncreature spells `p` cast on `turn`. -/
def noncreatureSpells (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.cast (.spellCast spell q _)) => if q == p && !spell.creature then n + 1 else n
      | _ => n) 0

/-- Creatures `p` attacked with on `turn`. -/
def attacks (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.combat (.attackersDeclared q decls)) => if q == p then n + decls.size else n
      | _ => n) 0

/-- Cards that moved from `p`'s library to `p`'s graveyard on `turn`. -/
def milled (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.zone (.moved _ _ (.library owner) (.graveyard q) _ _ _ _)) =>
        if owner == p && q == p then n + 1 else n
      | _ => n) 0

/-- `p` has already drawn the first card of their draw step on `turn`. -/
def drewFirstOfDrawStep (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .rules (.zone (.moved _ _ _ _ (.draw _ true) (some q) _ _)) => q == p
      | _ => false

/-- Equip abilities `p` completed on `turn`. -/
def equipActivations (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.cast (.abilityActivated _ _ q (.nonMana _ true ..))) => if q == p then n + 1 else n
      | _ => n) 0

/-- Mana values of spells `p` cast on `turn`, oldest first. Copies are absent. -/
def castManaValues (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Array Nat :=
  events.foldl (fun acc e =>
    if e.turn != turn then acc
    else
      match e.change with
      | .rules (.cast (.spellCast spell q _)) => if q == p then acc.push spell.manaValue else acc
      | _ => acc) #[]

/-- Cards `p` discarded on `turn` (CR 701.9c, including replacement redirects). -/
def discards (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.zone (.moved _ _ (.hand q) toZone .discard _ _ _)) =>
        if q == p && toZone != .hand q then n + 1 else n
      | _ => n) 0

/-- Life `p` lost on `turn`, including life lost to damage. -/
def lifeLost (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.life (.lost q amount _ _)) => if q == p then n + amount else n
      | _ => n) 0

/-- Counted resolutions for `p` on `turn` (optionally filtered to a specific
`sourceId` and/or `ability` for per-ability resolution counting). -/
def resolutions (events : Array GameEvent) (turn : Nat) (p : PlayerId)
    (sourceId : Option ObjectId := none)
    (ability : Option TriggeredAbility := none) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.stackObject (.resolved obj nth sId ab?)) =>
        let ctrlMatch := (obj.controller.getD obj.owner) == p
        let srcMatch :=
          match sourceId with
          | some sid => sId == some sid
          | none => true
        let abMatch :=
          match ability with
          | some ab => ab? == some ab
          | none => true
        if nth > 0 && ctrlMatch && srcMatch && abMatch then n + 1 else n
      | _ => n) 0

/-- `ab` on `sourceId` has already triggered on `turn` in `events` (CR 603.2h). -/
def abilityTriggeredThisTurn (events : Array GameEvent) (turn : Nat)
    (sourceId : ObjectId) (ab : TriggeredAbility) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .rules (.triggerQueue (.triggered source _ ability _)) =>
        source.id == some sourceId && ability == ab
      | _ => false

/-- An ability on `sourceId` has triggered on `turn` in `events` (CR 603.2h). -/
def sourceTriggeredThisTurn (events : Array GameEvent) (turn : Nat)
    (sourceId : ObjectId) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .rules (.triggerQueue (.triggered source _ _ _)) =>
        source.id == some sourceId
      | _ => false

/-- Lands `p` played on `turn` (CR 305.1). -/
def landsPlayed (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.zone (.moved _ _ _ _ .playLand (some q) _ _)) => if q == p then n + 1 else n
      | _ => n) 0

/-- Graveyard ids of creatures that moved from the battlefield to a graveyard
on `turn`. The id is the one the card has after it arrives (CR 400.7). -/
def creaturesToGraveyard (events : Array GameEvent) (turn : Nat) : Array ObjectId :=
  events.foldl (fun acc e =>
    if e.turn != turn then acc
    else
      match e.change with
      | .rules (.zone (.moved before after .battlefield (.graveyard _) _ _ _ _)) =>
        if before.creature then
          match after.id with
          | some id => acc.push id
          | none => acc
        else acc
      | _ => acc) #[]

/-- Graveyard id of the most recent attacking creature that died. -/
def lastDiedAttacker (events : Array GameEvent) : Option ObjectId :=
  events.foldl (fun acc e =>
    match e.change with
    | .rules (.zone (.moved before after .battlefield (.graveyard _) _ _ _ _)) =>
      if before.creature && before.attacking then after.id <|> acc else acc
    | _ => acc) none

/-- Id of the permanent that most recently became tapped. -/
def lastBecameTapped (events : Array GameEvent) : Option ObjectId :=
  events.foldl (fun acc e =>
    match e.change with
    | .rules (.permanent (.tapped object _)) => object.id <|> acc
    | _ => acc) none

/-- Player most recently dealt combat damage. -/
def lastCombatDamagePlayer (events : Array GameEvent) : Option PlayerId :=
  events.foldl (fun acc e =>
    match e.change with
    | .rules (.damage (.dealt pkts)) =>
      pkts.foldl (fun acc pkt =>
        match pkt.combat, pkt.recipient with
        | true, .player p => some p
        | _, _ => acc) acc
    | _ => acc) none

/-- Someone chose to have The Sensational She-Hulk deal damage on `turn`. -/
def sheHulkDealtDamageThisTurn (events : Array GameEvent) (turn : Nat) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .rules (.player (.sheHulkDealtDamage _)) => true
      | _ => false

/-- `id` entered the battlefield on `turn`. -/
def objectEntered (events : Array GameEvent) (turn : Nat) (id : ObjectId) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .rules (.zone (.moved _ after _ .battlefield _ _ _ _)) => after.id == some id
      | .rules (.zone (.created object _)) => object.zone == .battlefield && object.id == some id
      | _ => false

/-- If `id` is a permanent that entered the battlefield from the stack (or later
left the battlefield), return the stack `ObjectId` it resolved from (CR 400.7d);
otherwise `id`. -/
def stackSpellIdOf (events : Array GameEvent) (id : ObjectId) : ObjectId :=
  events.foldr (fun e cur =>
    match e.change with
    | .rules (.zone (.moved before after .stack .battlefield ..)) =>
      if after.id == some cur then before.id.getD cur else cur
    | .rules (.zone (.moved before after .battlefield _ ..)) =>
      if after.id == some cur then before.id.getD cur else cur
    | _ => cur) id

/-- Resolve `spell` back through `ZoneEvent.moved` (`.stack → .battlefield`) and
`StackObjectEvent.copied` to the root spell id on the stack (CR 400.7d / 707.10). -/
def rootCopiedSpellId (events : Array GameEvent) (spell : ObjectId) : ObjectId :=
  let sid := stackSpellIdOf events spell
  events.foldr (fun e cur =>
    match e.change with
    | .rules (.stackObject (.copied original copy _)) =>
      if copy.id == some cur then original else cur
    | _ => cur) sid

/-- Whether `id` (or the spell it resolved from, CR 400.7d) was cast and is not
a stack copy (CR 707.10). -/
def wasCast (events : Array GameEvent) (id : ObjectId) (isCopy : Bool := false) : Bool :=
  if isCopy then false
  else
    let sid := stackSpellIdOf events id
    events.any fun e =>
      match e.change with
      | .rules (.cast (.spellCast s _ _)) => s.id == some sid || s.id == some id
      | .rules (.cast (.proposed obj _ _ _)) => obj == sid || obj == id
      | .rules (.zone (.moved before after .stack .battlefield ..)) =>
        (after.id == some id || after.id == some sid) && !before.isCopy && !after.isCopy
      | .rules (.zone (.moved _ after _ .stack .cast ..)) =>
        after.id == some sid || after.id == some id
      | _ => false

/-- The cast of `spell` (or the spell `spell` resolved from, CR 400.7d) was from a graveyard. -/
def castFromGraveyard (events : Array GameEvent) (spell : ObjectId) (isCopy : Bool := false) : Bool :=
  if isCopy then false
  else
    let sid := stackSpellIdOf events spell
    events.any fun e =>
      match e.change with
      | .rules (.cast (.spellCast s _ (.graveyard _))) => s.id == some sid || s.id == some spell
      | .rules (.cast (.proposed obj _ (.graveyard _) _)) => obj == sid || obj == spell
      | .rules (.cast (.proposed obj _ _ (.alternative "flashback"))) => obj == sid || obj == spell
      | .rules (.zone (.moved _ after (.graveyard _) .stack .cast ..)) =>
        after.id == some sid || after.id == some spell
      | _ => false

/-- The cast of `spell` (or the spell `spell` resolved from, CR 400.7d) was from a hand. -/
def castFromHand (events : Array GameEvent) (spell : ObjectId) (isCopy : Bool := false) : Bool :=
  if isCopy then false
  else
    let sid := stackSpellIdOf events spell
    events.any fun e =>
      match e.change with
      | .rules (.cast (.spellCast s _ (.hand _))) => s.id == some sid || s.id == some spell
      | .rules (.cast (.proposed obj _ (.hand _) _)) => obj == sid || obj == spell
      | .rules (.zone (.moved _ after (.hand _) .stack .cast ..)) =>
        after.id == some sid || after.id == some spell
      | _ => false

/-- `spell` was proposed as a prepared spell copy (`way == .alternative "prepare"`). -/
def isPreparedSpell (events : Array GameEvent) (spell : ObjectId) : Bool :=
  let sid := stackSpellIdOf events spell
  events.any fun e =>
    match e.change with
    | .rules (.cast (.proposed obj _ _ (.alternative "prepare"))) => obj == sid || obj == spell
    | _ => false

/-- `spell` was proposed for its flashback cost (`way == .alternative "flashback"`, CR 702.34a). -/
def castWithFlashback (events : Array GameEvent) (spell : ObjectId) : Bool :=
  let sid := stackSpellIdOf events spell
  events.any fun e =>
    match e.change with
    | .rules (.cast (.proposed obj _ _ (.alternative "flashback"))) => obj == sid || obj == spell
    | _ => false

/-- Pre-cast `ObjectId` that moved onto `.stack` to become `spell` (CR 400.7), or `spell` itself. -/
def castOriginIdOf (events : Array GameEvent) (spell : ObjectId) : ObjectId :=
  let sid := stackSpellIdOf events spell
  events.foldr (fun e cur =>
    match e.change with
    | .rules (.zone (.moved before after _ .stack ..)) =>
      if after.id == some cur then before.id.getD cur else cur
    | _ => cur) sid

/-- `spell` was kicked (or copied from a kicked spell, CR 707.10 / 400.7d). -/
def wasKicked (events : Array GameEvent) (spell : ObjectId) : Bool :=
  let sid := stackSpellIdOf events spell
  let root := rootCopiedSpellId events spell
  events.any fun e =>
    match e.change with
    | .rules (.cast (.announced obj _ _ costs)) =>
      (obj == spell || obj == sid || obj == root) &&
        costs.any (fun | .kicker => true | _ => false)
    | _ => false

/-- Recipient promised a gift as `spell` was cast (or copied, CR 707.10 / 400.7d). -/
def giftPromisedTo? (events : Array GameEvent) (spell : ObjectId) : Option PlayerId :=
  let sid := stackSpellIdOf events spell
  let root := rootCopiedSpellId events spell
  events.findSomeRev? fun e =>
    match e.change with
    | .rules (.cast (.announced obj _ _ costs)) =>
      if obj == spell || obj == sid || obj == root then
        costs.findSome? (fun | .gift p => some p | _ => none)
      else none
    | _ => none

/-- A gift was promised as `spell` was cast (or copied, CR 707.10). -/
def giftPromised (events : Array GameEvent) (spell : ObjectId) : Bool :=
  (giftPromisedTo? events spell).isSome

/-- `spell` was cast using teamwork (or copied from a teamwork spell, CR 707.10). -/
def teamwork (events : Array GameEvent) (spell : ObjectId) : Bool :=
  let sid := stackSpellIdOf events spell
  let root := rootCopiedSpellId events spell
  events.any fun e =>
    match e.change with
    | .rules (.cast (.announced obj _ _ costs)) =>
      (obj == spell || obj == sid || obj == root) &&
        costs.any (fun | .teamwork _ => true | _ => false)
    | _ => false

/-- Sneak attack target recorded when `spell` was cast (or copied, CR 707.10).
Returns `some atkTarget?` when sneak was paid, or `none` when sneak was not paid. -/
def sneakAttackTarget? (events : Array GameEvent) (spell : ObjectId) : Option (Option AttackTarget) :=
  let sid := stackSpellIdOf events spell
  let root := rootCopiedSpellId events spell
  events.findSomeRev? fun e =>
    match e.change with
    | .rules (.cast (.announced obj _ _ costs)) =>
      if obj == spell || obj == sid || obj == root then
        costs.findSome? (fun | .sneak _ atk => some atk | _ => none)
      else none
    | _ => none

/-- Value of X announced for `id` (or the spell `id` resolved/moved/copied from, CR 107.3a / 400.7d / 707.10). -/
def chosenXOf? (events : Array GameEvent) (id : ObjectId) : Option Nat :=
  let moveOrigin :=
    events.foldr (fun e cur =>
      match e.change with
      | .rules (.zone (.moved before after .stack _ ..)) =>
        if after.id == some cur then before.id.getD cur else cur
      | _ => cur) id
  let root := rootCopiedSpellId events moveOrigin
  events.findSomeRev? fun e =>
    match e.change with
    | .rules (.cast (.announced obj _ (some x) _)) =>
      if obj == id || obj == moveOrigin || obj == root then some x else none
    | .rules (.zone (.moved before after .stack _ ..)) =>
      if after.id == some id || before.id == some moveOrigin || before.id == some root then
        before.chosenX.orElse (fun _ => after.chosenX)
      else none
    | .rules (.stackObject (.copied orig copy _)) =>
      if copy.id == some id || orig == moveOrigin || orig == root then copy.chosenX else none
    | _ => none

/-- Cards exiled from a graveyard to pay the boast activation cost of `abilityId` (MSH 227). -/
def boastExiledOf (events : Array GameEvent) (abilityId : ObjectId) : Array ObjectId :=
  events.foldl (fun acc e =>
    match e.change, e.cause? with
    | .rules (.zone (.moved _ after _ .exile ..)), some (.costPayment .exile _ (some aid)) =>
      if aid == abilityId then
        match after.id with
        | some id => acc.push id
        | none => acc
      else acc
    | _, _ => acc) #[]

/-- Last-known `before` snapshot for `id` from `ZoneEvent.moved` (CR 113.7a / 608.2h).
Traces non-battlefield moves backward to find the snapshot when the object left `.battlefield`. -/
def lastKnownBefore? (events : Array GameEvent) (id : ObjectId) : Option EventObject :=
  let bfId :=
    events.foldr (fun e cur =>
      match e.change with
      | .rules (.zone (.moved before after fromZone _ ..)) =>
        if fromZone != .battlefield && after.id == some cur then before.id.getD cur else cur
      | _ => cur) id
  (events.findSomeRev? fun e =>
    match e.change with
    | .rules (.zone (.moved before after .battlefield _ ..)) =>
      if before.id == some bfId || after.id == some bfId || before.id == some id || after.id == some id then
        some before
      else none
    | _ => none).orElse fun _ =>
    events.findSomeRev? fun e =>
      match e.change with
      | .rules (.zone (.moved before after ..)) =>
        if before.id == some id || after.id == some id then some before else none
      | _ => none

/-- `id` entered from a spell cast for its impending cost (CR 702.176,
ruling 970). -/
def castForImpending (events : Array GameEvent) (id : ObjectId) : Bool :=
  events.any fun e =>
    match e.change with
    | .rules (.continuousEffect (.created _ eff)) => eff == .notACreature id
    | _ => false

/-- All rules events caused by a one-shot effect in `events`, paired with their
`EffectId`s, in chronological order (CR 610). -/
def oneShotEffectsWithId (events : Array GameEvent) : Array (EffectId × RulesEvent) :=
  events.foldl (fun acc e =>
    match e.cause?.bind EventCause.oneShotEffectId?, e.change with
    | some id, .rules r =>
      match r with
      | .continuousEffect .. | .delayedTrigger .. => acc
      | _ => acc.push (id, r)
    | _, _ => acc) #[]

/-- All continuous effects created in `events` with their `EffectId`s, in chronological order (CR 611). -/
def createdEffectsWithId (events : Array GameEvent) : Array (EffectId × ContinuousEffectSpec) :=
  events.foldl (fun acc e =>
    match e.change with
    | .rules (.continuousEffect (.created id eff)) => acc.push (id, eff)
    | _ => acc) #[]

/-- All continuous effects created in `events`, in chronological order (CR 611). -/
def createdEffects (events : Array GameEvent) : Array ContinuousEffectSpec :=
  events.foldl (fun acc e =>
    match e.change with
    | .rules (.continuousEffect (.created _ eff)) => acc.push eff
    | _ => acc) #[]

/-- All continuous effects that expired in `events` with their `EffectId`s, in chronological order (CR 611). -/
def expiredEffectsWithId (events : Array GameEvent) : Array (EffectId × ContinuousEffectSpec) :=
  events.foldl (fun acc e =>
    match e.change with
    | .rules (.continuousEffect (.expired id)) =>
      match events.findSomeRev? (fun ev =>
        match ev.change with
        | .rules (.continuousEffect (.created cid eff)) =>
          if cid == id then some eff else none
        | _ => none) with
      | some eff => acc.push (id, eff)
      | none => acc
    | _ => acc) #[]

/-- All continuous effects that expired in `events`, in chronological order (CR 611). -/
def expiredEffects (events : Array GameEvent) : Array ContinuousEffectSpec :=
  (expiredEffectsWithId events).map (·.2)

end GameEvent

end Mtg.Engine
