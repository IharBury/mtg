import Mtg.Engine.Card.Counter
import Mtg.Engine.Card.TriggerPattern
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

/-- One non-rules engine metadata change on a `GameObject` (CR 109 / 607). -/
inductive ObjectChange where
  | abilityEffect (v : Option Effect)
  | linkedExile (v : Array ObjectId)
  | pushLinkedExile (id : ObjectId)
  | returnToZone (v : Option Zone)
  | leaveTriggerExile (v : Array ObjectId)
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
  | teamworkCreatures (v : Array ObjectId)
  | additionalGeneric (n : Nat)
  | needsBehold (v : Option CardSubtype)
  | payLife (n : Nat)
  | alternativeCost (v : Bool)
  | loyaltyPaid (v : Bool)
  | choiceCostPaid (v : Bool)
deriving Repr, Inhabited, BEq

/-- The kind of replacement effect (CR 614 / 616.1a–e). -/
inductive ReplacementKind where
  /-- CR 616.1e / 614.1c / 614.12: Intrinsic enters-tapped replacement on `object`. -/
  | entersTappedSelf (object : ObjectId)
  /-- CR 616.1e / 614.1c / 614.12: Pay `life` life as `object` enters so it doesn't enter tapped. -/
  | entersUntappedPayLife (object : ObjectId) (life : Nat)
  /-- CR 616.1e / 614.1c / 614.12: Decline to pay life as `object` enters, so it enters tapped. -/
  | entersTappedDeclinePayLife (object : ObjectId)
  /-- CR 616.1e / 614.1c / 614.12: Behold `beholdId` of `subtype` as `object` enters so it doesn't enter tapped. -/
  | entersUntappedBehold (object beholdId : ObjectId) (subtype : CardSubtype)
  /-- CR 616.1e / 614.1c / 614.12: Decline to behold as `object` enters, so it enters tapped. -/
  | entersTappedDeclineBehold (object : ObjectId)
  /-- CR 616.1e / 614.1c / 614.12: Choose `color` as `object` enters. -/
  | asEntersChooseColor (object : ObjectId) (color : Color)
  /-- CR 616.1e / 614.1c / 614.12: Choose creature `subtype` as `object` enters. -/
  | asEntersChooseCreatureType (object : ObjectId) (subtype : CardSubtype)
  /-- CR 616.1e / 614.1c / 614.12: Choose odd (`true`) or even (`false`) as `object` enters. -/
  | asEntersChooseOdd (object : ObjectId) (odd : Bool)
  /-- CR 616.1e / 614.1c / 614.12: Name nonland card `name` as `object` enters. -/
  | asEntersChooseCardName (object : ObjectId) (name : String)
  /-- CR 616.1e / 614.1c / 614.12: Choose `cardType` as `object` enters. -/
  | asEntersChooseCardType (object : ObjectId) (cardType : CardType)
  /-- CR 616.1e / 614.1c / 614.12: Choose `anchor` as `object` enters. -/
  | asEntersChooseAnchor (object : ObjectId) (anchor : String)
  /-- CR 616.1e / 614.1c / 614.12: Intrinsic enters-with-counters replacement on `object`. -/
  | entersWithCountersSelf (object : ObjectId) (kind : CounterKind) (amount : Nat)
  /-- CR 616.1b: Modifies under whose control `object` enters the battlefield. -/
  | entersUnderControl (object : Option ObjectId) (newController : PlayerId)
  /-- CR 616.1c / 707.5: Makes `object` enter the battlefield as a copy of `template`. -/
  | entersAsCopy (object : Option ObjectId) (template : CardDef)
  /-- CR 616.1c / 614.1c / 614.12: Optional enter-as-copy of `targetId` until EOT with haste. -/
  | entersAsCopyCreatureUntilEot (object targetId : ObjectId)
  /-- CR 616.1c / 614.1c / 614.12: Decline optional enter-as-copy. -/
  | declineEntersAsCopy (object : ObjectId)
  /-- CR 616.1d / 702.145b / 712.14: Causes `object` to enter the battlefield with its back face up. -/
  | entersBackFaceUp (object : Option ObjectId)
  /-- CR 303.4f–g / 614.12: Attach non-cast Aura `object` to `hostId` as it enters. -/
  | asEntersAttachAura (object hostId : ObjectId)
  /-- CR 616.1e: External effect causing `object` to enter with additional `kind` counters. -/
  | entersWithExtraCounters (object : Option ObjectId) (kind : CounterKind) (amount : Nat)
  /-- CR 616.1e / 122.6: Modifies the number of counters put on `object` (`count * mult + add`). -/
  | modifyCountersPut (object : Option ObjectId) (kind : Option CounterKind) (add : Nat := 0) (mult : Nat := 1)
  /-- CR 616.1e / 702.34a: Exiles `object` when leaving the stack instead of going elsewhere. -/
  | exileInsteadOfStackLeave (object : Option ObjectId)
  /-- CR 616.1e / 614.1a: Exiles `object` instead of putting it into a graveyard (optionally queueing a reflexive Wolf trigger). -/
  | exileInsteadOfGraveyard (object : Option ObjectId) (createsWolf : Bool := false)
  /-- CR 616.1e / 122.1c: Removes a shield counter from `object` instead of destroying it. -/
  | shieldCounterDestroy (object : ObjectId)
  /-- CR 616.1e / 121.2: Replaces a card draw by `player` with `factor` card draws. -/
  | replaceDraw (player : PlayerId) (factor : Nat := 2) (exceptFirstDrawStep : Bool := true)
  /-- CR 616.1e / 701.50: Replaces connive by `player`'s creature with drawing `n` cards, then conniving. -/
  | extraDrawOnConnive (player : PlayerId) (n : Nat := 1)
  /-- CR 616.1e / 614.1a: Adds `bonus` to noncombat damage dealt by `source`. -/
  | addNoncombatDamage (source : Option ObjectId) (bonus : Nat)
  /-- CR 616.1e / 614.1a: Multiplies damage dealt by `source` by `factor`. -/
  | multiplyDamage (source : Option ObjectId) (factor : Nat := 2)
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
  | .entersUnderControl .. => .control
  | .entersAsCopy .. => .copy
  | .entersAsCopyCreatureUntilEot .. => .copy
  | .declineEntersAsCopy _ => .copy
  | .entersBackFaceUp _ => .backFaceUp
  | .asEntersAttachAura .. => .auraHost
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

/-- Whether this duration is a resolving-effect timed or `untilSourceLeaves`
duration whose affected set is locked in when created (CR 611.2b–c / 702.26b,d,e). -/
def EffectDuration.isTimedResolvingDuration : EffectDuration → Bool
  | .untilEndOfTurn | .untilEndOfCombat | .untilEndOfStepOrPhase _ | .untilStepOrPhase _
  | .untilNextTurnOf _ | .untilEndOfNextTurnOf _ | .untilSourceLeaves _ => true
  | .whileSourceOnBattlefield _ | .whileSourceHasCounter _ _ | .whileInZone _ _
  | .indefinite => false

/-- Closed-data scope of a layered continuous effect (CR 611.2c / 611.3). -/
inductive ObjectScope where
  /-- Specific object(s) locked in when the effect was created (CR 611.2c). -/
  | objects (ids : Array ObjectId)
  /-- Creatures controlled by `p` (CR 611.3). -/
  | creaturesControlledBy (p : PlayerId)
  /-- Creatures without keywords `k` (CR 611.3). -/
  | creaturesWithout (k : Array KeywordAbility)
  /-- Permanents of subtype `s` controlled by `p` (CR 611.3). -/
  | permanentsOfSubtype (p : PlayerId) (s : CardSubtype)
deriving Repr, Inhabited, BEq

/-- Abilities added by a Layer 6 effect (CR 613.1f). -/
structure AbilitySet where
  keywords : Array KeywordAbility := #[]
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
      (subtypes : Array CardSubtype) (supertypes : Array Supertype)
      (removeTypes : Array CardType := #[])
      (removeSubtypes : Array CardSubtype := #[])
      (removeSupertypes : Array Supertype := #[])                      -- Layer 4 (CR 613.1d)
  | colors (mode : SetOrAdd) (colors : ColorSet)
      (removeColors : ColorSet := ColorSet.empty)                      -- Layer 5 (CR 613.1e)
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
  | cantAttackJaces (jaceController : PlayerId)
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
  | commandEmblem (object : ObjectId)
deriving Repr, Inhabited, BEq

/-- Continuous permission to play or cast an object or spend mana on it (CR 611.2 / 701.18). -/
inductive PlayPermissionSpec where
  | playFromExile (object : ObjectId) (perm : PlayPermission)
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
  | permission (p : Option PlayerId) (r : PlayPermissionSpec) (d : EffectDuration)
deriving Repr, Inhabited, BEq

abbrev ContinuousEffect := ContinuousEffectSpec

namespace ContinuousEffectSpec

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
@[inline] def keywordsUntilEot (object : ObjectId) (keywords : Array KeywordAbility) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.abilities { keywords := keywords } .none) .untilEndOfTurn

/-- `object` can't be blocked this turn (CR 509.1b / 611.2 / 613.1f). -/
@[inline] def cantBeBlockedUntilEot (object : ObjectId) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.abilities { staticAbilities := #[.cantBeBlocked] } .none) .untilEndOfTurn

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
      kind := .exileInsteadOfGraveyard (some object) false }
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
  .layered (.objects #[object]) (.types .add #[.artifact] #[] #[] #[.creature]) .indefinite

/-- `object` isn't a creature (CR 611.2 / 702.176). -/
@[inline] def notACreature (object : ObjectId) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.types .add #[] #[] #[] #[.creature]) .indefinite

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
    (TriggeredAbility.mkTrigger .thisDealsCombatDamageToPlayer (Effect.triggerCreateTokens .treasure 1)) true

/-- `object` loses all abilities until end of turn (CR 611.2 / 613.1f). -/
@[inline] def losesAbilitiesUntilEot (object : ObjectId) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.abilities {} .all) .untilEndOfTurn

/-- `object` loses all abilities for as long as `source` remains on the battlefield (CR 611.2b / 613.1f). -/
@[inline] def losesAbilitiesWhileSource (object : ObjectId) (source : ObjectId) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.abilities {} .all) (.whileSourceOnBattlefield source)

/-- `object` has hexproof for as long as `source` remains on the battlefield (CR 611.2b / 613.1f). -/
@[inline] def hexproofWhileSource (object : ObjectId) (source : ObjectId) : ContinuousEffectSpec :=
  .layered (.objects #[object]) (.abilities { keywords := #[Keyword.hexproof] } .none) (.whileSourceOnBattlefield source)

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
  .permission none (.colorlessGrant object card) .indefinite

/-- `object` gains flashback until end of turn (CR 611.2). -/
@[inline] def flashbackUntilEot (object : ObjectId) : ContinuousEffectSpec :=
  .permission none (.flashback object) .untilEndOfTurn

/-- If `object` would be put into a graveyard from the stack, exile it instead (CR 611.2 / 614.1a). -/
@[inline] def exileInstantSorceryInstead (object : ObjectId) : ContinuousEffectSpec :=
  .replacement
    { id := { kind := .exileInstantSorceryInstead, object := some object }
      source := some object
      kind := .exileInsteadOfGraveyard (some object) false }
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
  .permission (some perm.player) (.playFromExile object perm) d

/-- `object` (an emblem) lasts until `player`'s next turn (CR 611.2). -/
@[inline] def commandEmblemUntilTurnOf (object : ObjectId) (player : PlayerId) : ContinuousEffectSpec :=
  .gameRule (.commandEmblem object) (.untilNextTurnOf player)

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
      else if untilNextTurn then
        match nextTurnOf with
        | some p => .untilNextTurnOf p
        | none => .untilEndOfTurn
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
  .playerRule player (.additionalLands n) .untilEndOfTurn

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

/-- `player`'s creatures can't attack Jace planeswalkers `jaceController` controls this turn (CR 611.2). -/
@[inline] def cantAttackJacesThisTurn (player jaceController : PlayerId) : ContinuousEffectSpec :=
  .playerRule player (.cantAttackJaces jaceController) .untilEndOfTurn

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
  .playerRule controller (.controlsPlayer controlled onNextTurn)
    (if onNextTurn then .indefinite else .untilEndOfTurn)

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
  | expired (id : EffectId) (spec? : Option ContinuousEffectSpec := none)
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
  | manaSpent (player : PlayerId) (units : Array ManaUnit) (forObject : Option ObjectId)
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
  | genericMana (amount : Nat)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Whether an activated ability is a non-mana or mana ability (CR 602.2b / 605.3b). -/
inductive ActivationKind where
  | nonMana (loyalty : Option Int) (equip : Bool) (powerUp : Bool) (boast : Bool)
      (abilityIdx : Option Nat := none) (exhaust : Bool := false)
  | mana (abilityIdx : Option Nat := none) (powerUp : Bool := false) (exhaust : Bool := false)
deriving DecidableEq, Repr, Inhabited, BEq

def ActivationKind.abilityIdx? : ActivationKind → Option Nat
  | .nonMana _ _ _ _ idx _ => idx
  | .mana idx _ _ => idx

/-- Casting and activation lifecycle events (CR 601.2 / 602.2 / 605.3b). -/
inductive CastEvent where
  | proposed (obj : ObjectId) (player : PlayerId) (fromZone : Zone) (way : CastWay)  -- 601.2a
  | announced (obj : ObjectId) (modes : Array Nat) (x : Option Nat)
      (costs : Array AdditionalCostChoice)                                         -- 601.2b
  | targeted (obj : ObjectId) (targets : Array Target) (division : Array Nat)
      (skippedOptionalSlots : Array Nat := #[])                                   -- 601.2c–d
  | spellCast (spell : EventObject) (player : PlayerId) (fromZone : Zone)          -- 601.2i
  | abilityActivated (ability : ObjectId) (source : EventObject) (player : PlayerId)
      (kind : ActivationKind)                                                       -- 602.2b; mana abilities 605.3b
deriving Repr, Inhabited, BEq

/-- Stack-entry and ability-metadata payload for `TriggerQueueEvent.putOnStack` (CR 603.3 / 603.12). -/
structure StackTriggerSpec where
  triggeredAbility : Option TriggeredAbility := none
  abilityEffect : Option Effect := none
  isReflexive : Bool := false
  sourceId : Option ObjectId := none
  abilityName : Option String := none
  delayedTrigger : Option (DelayedTriggerKind × EventCause) := none
  lastKnownPower : Option Int := none
  lastKnownToughness : Option Int := none
  triggerCauseId : Option ObjectId := none
  triggerCauseIds : Array ObjectId := #[]
  triggerCauseController : Option PlayerId := none
  triggerCausePower : Option Int := none
  triggerCauseStatus : Option Status := none
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
  /-- `obj` was removed from the stack on resolution because its intervening “if” condition failed or all its targets were illegal (CR 603.4 / 608.2a / 608.2b). -/
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
  isBonus : Bool := false
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

/-- How `Game.logPutCounterDelta` formats the post-replacement log for `kind`
counters put on a permanent. -/
inductive PutCounterLog where
  /-- `"A(n) <kind> counter is put on <name>"` / `"<k> <kind> counters are put on <name>"`. -/
  | isPutOn
  /-- `"<name> gets a(n) <kind> counter"` / `"<name> gets <k> <kind> counters"`. -/
  | gets
  /-- `"<name> gets a(n) <kind> counter (<total>)"` / `"<name> gets <k> <kind> counters (<total>)"`. -/
  | getsWithTotal
  /-- `"<name> gets <k> <kind> counter(s)"`. -/
  | getsCount
  /-- `"<k> <kind> counter(s) are put on <name>"`. -/
  | countArePutOn
  /-- `"<player> puts a(n) <kind> counter on <name>"` / `"<player> puts <k> <kind> counters on <name>"`. -/
  | playerPutsOn (player : PlayerId)
  /-- `"<name> received a(n) <kind> counter"` / `"<name> received <k> <kind> counters"`. -/
  | received
deriving DecidableEq, Repr, Inhabited, BEq

/-- Post-entry log mode for `Choices.putToBattlefieldLoop` once arrival on
`.battlefield` completes. -/
inductive PutBattlefieldEntryLog where
  | none
  | enters
  | entersTapped
deriving DecidableEq, Repr, Inhabited, BEq

/-- Deferred post-step continuation (`Decisions.runPostStep`) resumed after a CR 616.1
`Pending.chooseReplacement` pause finishes. -/
inductive PostStep where
  | putArtifactOntoBattlefield (p : PlayerId) (cardId : ObjectId) (hostId : Option ObjectId)
  | continueDiscardTwo (controller : PlayerId) (rest : Array PlayerId) (draws : Nat)
      (chosen : Array (PlayerId × Array ObjectId) := #[])
  | finishDiscardTwoDraws (controller : PlayerId) (baseDraws : Nat)
      (oppIds : Array PlayerId) (startIdx : Nat)
  | enteredBattlefieldPutRestBottomRandom (p : PlayerId) (cardId : ObjectId)
      (rest : Array ObjectId) (cause : Option EventCause)
  | hawkeyeArrows (controller : PlayerId) (modes : Array Nat) (targets : Array Target)
      (targetIdx : Nat) (sourceId : Option ObjectId)
  | enteredBattlefieldSilent (cardId : ObjectId) (isLand : Bool := false)
  | returnedBattlefieldEndStep (cardId : ObjectId) (isLand : Bool)
  | returnedToBattlefield (cardId : ObjectId) (isLand : Bool)
  | putOntoBattlefieldHasteAtFour (p : PlayerId) (cardId : ObjectId) (x : Nat) (shuffle : Bool)
  | revealPutCreaturesStep (p : PlayerId) (remaining put enteredFromIds : Array ObjectId)
      (cause : Option EventCause)
  | shuffleThenGainLife (p : PlayerId) (life : Nat)
  | dealDamageToEachOpponent (p : PlayerId) (amount : Nat) (sourceId : Option ObjectId)
      (cause : Option EventCause) (startEventIdx : Option Nat := none)
  | discardCleanupIds (p : PlayerId) (remainingIds : Array ObjectId)
      (justDiscarded : Option (ObjectId × PlayerId) := none)
  | postSbaCleanup (sba : Bool)
  | cleanupStepAfterDiscard
  | wheelDrawThenOfferNext (p : PlayerId) (cards : Nat) (rest : Array PlayerId := #[])
  | wheelOfferNext (cards : Nat) (rest : Array PlayerId) (accepted : Array PlayerId := #[])
  | wheelDrawsLoop (cards : Nat) (remainingPlayers : Array PlayerId)
  | searchLibraryPlaneswalker (p : PlayerId)
  | searchLibrarySphinx (p : PlayerId)
  | drawOneThenPlusOnesForDiscards (p : PlayerId) (sourceId : Option ObjectId)
  | addPlusOnesForLoggedDiscards (p : PlayerId) (sourceId : Option ObjectId)
  | queueTapAndStunReflexive (p : PlayerId) (nonlandCount : Nat) (sourceId : Option ObjectId)
  | nickFuryMayTransformOrBottom (p : PlayerId) (cardId : ObjectId) (rest : Array ObjectId)
      (cause : Option EventCause)
  | checkDrawThenOpponentsDraw (p : PlayerId) (beforeDraws : Nat)
  | opponentsDrawOneLoop (drawer : PlayerId) (remainingOpponents : Array PlayerId)
      (cause : Option EventCause)
  | loseLifeForMilledManaValue (p : PlayerId) (tops : Array ObjectId)
      (cause : Option EventCause)
  | addPlusOnesToSource (sourceId : ObjectId) (count : Nat)
  | beginDiscardCardsStep (players : Array PlayerId)
  | continueAfterDiscardStep (remaining : Array PlayerId) (samePlayer : Bool := false)
      (count : Nat := 1)
  | discardHandIdsLoop (p : PlayerId) (ids : Array ObjectId) (logEach : Bool)
      (cause : Option EventCause)
  | discardMultiHandIdsLoop (remaining : Array (PlayerId × ObjectId)) (logEach : Bool)
      (cause : Option EventCause)
  | closeDiscardBatchStep
  | finishSurveilHandMove (p : PlayerId) (fromId : ObjectId) (cardName : String)
      (remainingGy : Array ObjectId) (cause : Option EventCause)
  | logPutsIntoHand (revealer : PlayerId) (fromId : ObjectId) (cardName : String)
  | logInfluenceThenScryTwo (sourceId : ObjectId) (beforeInfluence : Nat)
  | logCreatedTokensSummary (controller : PlayerId) (startEventIdx : Nat)
  | putRestOnBottomRandom (p : PlayerId) (rest : Array ObjectId) (cause : Option EventCause)
  | millSourceInfluenceCount (controller : PlayerId) (sourceId : ObjectId)
  | continueOpeningBegin (remainingIds : Array ObjectId)
  | resumeChooseModeAfterLeave (p : PlayerId)
  | resumeChooseTargetsAfterLeave (p : PlayerId)
  | resumeTriggerModesAfterLeave (p : PlayerId) (objectId : ObjectId) (remaining : Nat)
      (chosen : Array Nat)
  | resumeUpToTriggerModesAfterLeave (p : PlayerId) (objectId : ObjectId) (remaining : Nat)
      (chosen : Array Nat)
  | resumeHawkeyeModesAfterLeave (p : PlayerId) (objectId : ObjectId) (left : Nat)
      (chosen : Array Nat)
  | resumeProposalCostAfterLeave (p : PlayerId) (savedP : Pending)
  | runAfterRandom (after : AfterRandom)
  | grantLifelinkUntilEot (cardId : ObjectId) (cause : Option EventCause)
  | endTurnAfterCleanupStepEnded
  | startNextTurnAndBegin
  | advanceAfterStepEnded
  | recordUntapStepEnded
  | beginStepAfterPhaseBegan (st : Step)
  | beginStepBody (st : Step)
  | exileZemoBoastCards (p : PlayerId) (abilityId : ObjectId) (remainingIds : Array ObjectId)
  | grantAdventureExilePermission (controller : PlayerId) (cardId : ObjectId)
      (cause : Option EventCause)
  | exileSearchedLinkedLoop (p : PlayerId) (remainingIds : Array ObjectId)
      (sourceId : Option ObjectId) (cause : Option EventCause)
      (pendingFromId : Option ObjectId := none)
  | grantPlayUntilEndOfNextTurn (p : PlayerId) (cardId : ObjectId) (cause : Option EventCause)
  | finishExileUntilSourceLeaves (sourceId : Option ObjectId) (fromId : ObjectId)
  | finishExileForLeaveTrigger (sourceId : Option ObjectId) (fromId : ObjectId)
  | exileTopForPlayLoop (fromPlayer caster : PlayerId) (remaining : Nat) (mayCastStyle : Bool)
      (cause : Option EventCause) (pendingFromId : Option ObjectId := none)
  | exileTopPlayIfYouControlSubtypeLoop (p : PlayerId) (subtype : CardSubtype)
      (remaining : Nat) (cause : Option EventCause) (movedId : Option ObjectId := none)
  | exileTopMayCastUpToLoop (fromPlayer caster : PlayerId) (remaining casts : Nat)
      (cause : Option EventCause) (exiled : Array ObjectId)
      (pendingFromId : Option ObjectId := none)
  | offerMayCastUpToFromExile (caster : PlayerId) (preIds : Array ObjectId) (casts : Nat)
  | finishExileUntilNextEndStep (controller : PlayerId) (fromId : ObjectId) (cause : EventCause)
  | logDiscardedCount (p : PlayerId) (preDiscards : Nat)
  | logGiftTreasureGiven (recipient : PlayerId)
  | logDelayedBirdSoldiersCreated (controller : PlayerId) (startEventIdx : Nat)
  | resolveCascadeLoop (p : PlayerId) (maxMv : Nat) (cause : EventCause)
      (exiled : Array ObjectId := #[]) (pendingFromId : Option ObjectId := none)
  | exileUntilInstantOrSorceryLoop (victim controller : PlayerId) (castTheCard : Bool)
      (cause : Option EventCause) (others : Array ObjectId := #[])
      (pendingFromId : Option ObjectId := none)
  | finishGrimaDirectCast (controller victim : PlayerId) (fromId : ObjectId)
      (others : Array ObjectId) (cause : Option EventCause)
  | exileFromRevealedHandAfterMove (p victim : PlayerId) (fromId : ObjectId)
      (cardName : String) (sourceId : Option ObjectId)
  | logExiledIfInExile (fromId : ObjectId) (msg : String)
  | logExpiredPlayFromExile (ids : Array ObjectId) (startEventIdx : Nat := 0)
  | recordCostSacrificedPower (abilityId : Option ObjectId) (fromId : ObjectId) (pw : Int)
  | logReturnedToHand (fromId : ObjectId) (to : PlayerId) (cardName : String)
  | finishPaySneak (p : PlayerId) (spellId attackerId : ObjectId)
      (atkTarget : AttackTarget) (cause : Option EventCause)
  | finishMoveToOwnerGraveyardLog (fromId : ObjectId) (fromZone : Zone) (owner : PlayerId)
      (cardName reason : String) (verb : Option ZoneVerb)
  | logPutOnOwnerLibrary (fromId : ObjectId) (owner : PlayerId) (cardName : String)
      (top : Bool) (msgOverride : Option String := none)
  | finishZemoBoastExileLogs (p : PlayerId) (sourceId : ObjectId) (preIds : Array ObjectId)
  | markNonManaCostPaid
  | moveIdsInOrderLoop (ids : Array ObjectId) (dest : Zone) (log : String)
      (cause : Option EventCause) (placedCount : Nat := 0)
      (prevMoved : Option (ObjectId × Zone) := none)
  | incrementPlanSource (controller : PlayerId) (sourceId : Option ObjectId)
  | millOpponentsOnly (opponents : Array PlayerId) (n : Nat) (cause : Option EventCause)
  | conniveTricksterTarget (caster : PlayerId) (connive : Option ObjectId)
      (sourceId : Option ObjectId)
  | topOrBottomDamageFollowup (fromId : ObjectId) (owner : PlayerId) (cardName : String)
      (top : Bool) (damage : Nat) (sourceId : Option ObjectId)
  | gainLifePlayer (p : PlayerId) (amount : Nat) (cause : Option EventCause := none)
  | drawCardsPlayer (p : PlayerId) (amount : Nat) (cause : Option EventCause := none)
  | sheHulkAfterDamage (p : PlayerId) (startIdx : Nat)
  | damageUpToOneAndPlayerLoop (controller : PlayerId) (kind : TargetSpec)
      (remaining : Array (Nat × Target)) (n : Nat) (srcName : String)
      (sourceId : Option ObjectId) (cause : Option EventCause)
      (startEventIdx : Option Nat := none)
  | applyAggregatedLifelink (startEventIdx : Nat) (cause : Option EventCause)
  | dealDamageLoseIndestructibleExileTo (targetId : ObjectId) (n : Nat) (source : EventObject)
  | dealDamageToEachNonSubtypeAndOpponents (controller : PlayerId) (n : Nat)
      (subtype : CardSubtype) (sourceId : Option ObjectId) (cause : Option EventCause)
  | movePublicCardsToHandLoop (p : PlayerId) (remainingIds : Array ObjectId)
      (maxLeft : Nat) (playerPutsStyle : Bool) (cause : Option EventCause)
      (pendingCard : Option (ObjectId × String) := none)
      (requirePublicZone : Bool := true)
  | exileOpponentLibrariesLoop (remainingOpps : Array PlayerId)
      (curOpp : Option PlayerId := none) (curIds : Array ObjectId := #[])
      (movedAnyForCur : Bool := false) (pendingId : Option ObjectId := none)
  /-- Log `msg` only if `cardId` arrived in `owner`'s graveyard (CR 614.6); also
  used for the CR 303.4g stack-Aura graveyard log. -/
  | logDiscardIfInGraveyard (cardId : ObjectId) (owner : PlayerId) (msg : String)
  /-- Resume `chooseCardsToHandLoop`; `pendingCard` is the card whose
  owner's-hand arrival (CR 400.3 / 614.6) is still to be logged. -/
  | chooseCardsToHandLoop (p : PlayerId) (remainingIds : Array ObjectId)
      (cause : Option EventCause)
      (pendingCard : Option (ObjectId × PlayerId × String) := none)
  /-- Log `msg` only if some counter kind on `targetId` increased over `before`
  (CR 122.1 / 614.6). -/
  | logIfCountersIncreased (targetId : ObjectId) (before : CounterBag) (msg : String)
  | afterTriggerTargetsChosen
  | finishAbilityResolution (snap : EventObject) (controller : PlayerId)
      (sourceId : Option ObjectId) (sagaChapter : Option Nat)
      (ab? : Option TriggeredAbility) (alreadyResolved : Bool)
  | untapStepAfterPhaseIn
deriving Inhabited, BEq

/-- Stage of `StateBasedActions.finishSbaSweep` across `Pending.chooseReplacement` pauses. -/
inductive SbaSweepStage where
  | dyingCreatures
  | planeswalkersAndLegend
  | finalChapterSagas
  | illegalAttachments
deriving DecidableEq, Repr, Inhabited, BEq

/-- Stage of `ActivationCosts.finishActivationExtraCosts` across `Pending.chooseReplacement` pauses. -/
inductive ActivationExtraCostStage where
  | stunAndSacrifice
  | sacrificeAndExile
  | exileOnly
deriving DecidableEq, Repr, Inhabited, BEq

/-- Stage of `SacrificeDiscard.finishConniveDraws` across `Pending.chooseReplacement` pauses. -/
inductive ConniveDrawStage where
  | draws
  | discardOnly
deriving DecidableEq, Repr, Inhabited, BEq

/-- Stage of `Pumps.finishAmassOn` across `Pending.chooseReplacement` pauses. -/
inductive AmassStage where
  | putCounters
  | postCounters
deriving DecidableEq, Repr, Inhabited, BEq

/-- Stage of `Tokens.empowerJaceStep` across `Pending.chooseReplacement` pauses. -/
inductive EmpowerJaceStage where
  | initial
  | afterTokenCreate
  | afterPutCounters (prevLoyalty : Nat)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Stage of `ResolutionHelpers.resumeFlickerLoop` across `Pending.chooseReplacement` pauses. -/
inductive FlickerStage where
  | beforeExileBatch
  | exileBatch
  | startReturnBatch
  | returnBatch
  | postReturn
deriving DecidableEq, Repr, Inhabited, BEq

/-- Sequential cost-payment stage of `Decisions.finishProposedSpellCosts`
across `Pending.chooseReplacement` pauses (CR 601.2h). -/
inductive ProposedSpellCostStage where
  | teamwork
  | behold
  | sneak
  | finalize
deriving DecidableEq, Repr, Inhabited, BEq

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

/-- Structured mutation to a `StackEntry` identified by `objectId`. -/
inductive StackEntryChange where
  | skipOptionalSlot (slot : Nat)
  | targetsAnnounced (done : Bool)
  | lastKnownPT (power toughness : Option Int)
  | clearChosenModes
deriving Repr, Inhabited, BEq

/-- Execution context for the unified Phase-8 `Instruction` interpreter (CR 608.2). -/
structure InterpCtx where
  controller : PlayerId := ⟨0⟩
  sourceId : Option ObjectId := none
  sourceSnapshot : Option EventObject := none
  targets : Array Target := #[]
  targetSlots : Array (Array Target) := #[]
  targetSpec : TargetSpec := .none
  triggerSubjectId : Option ObjectId := none
  triggerSubjectIds : Array ObjectId := #[]
  triggerSubjectSnapshot : Option EventObject := none
  triggerPlayers : Array (TriggerPlayerRole × PlayerId) := #[]
  chosenX : Nat := 0
  castFromGraveyard : Bool := false
  kicked : Bool := false
  giftPromised : Bool := false
  lastKnownPower : Option Int := none
  lastKnownToughness : Option Int := none
  skippedOptionalSlots : Array Nat := #[]
  /-- Active one-shot effect ID for CR 614.6 event-slice outcome summarization. -/
  oneShotEffectId : EffectId := ⟨0⟩
deriving Repr, Inhabited, BEq

/-- One suspended continuation frame inside the unified `Instruction` interpreter. -/
inductive InterpCont where
  /-- Remaining instructions in a `.seq` block. -/
  | seqRest (rest : Array Instruction)
  /-- Close a `.bind v step body` scope once `step` completes: summarize events
  since `startEventIdx` filtered by `stepEffectId`, bind `v`, then run `body`. -/
  | bindClose (v : VarId) (startEventIdx : Nat) (stepEffectId : EffectId)
      (body : Instruction) (extraOverride? : Option StepOutcome := none)
  /-- Remaining players in `.forEach (.eachPlayer ..)` (APNAP order), bound to `v`. -/
  | forEachPlayerRest (v : VarId) (players : Array PlayerId) (body : Instruction)
  /-- Remaining objects in `.forEach (.eachObject ..)`, bound to `v`. -/
  | forEachObjectRest (v : VarId) (objects : Array ObjectId) (body : Instruction)
  /-- Remaining iterations in `.forEach (.repeatTimes ..)`. -/
  | repeatRest (remaining : Nat) (body : Instruction)
  /-- Run `onYes` or `onNo` after a `.optional` choice (reading `choiceVar` from `stepEnv`). -/
  | branchOnChoice (onYes onNo : Instruction)
  /-- Run the chosen branch after `Pending.chooseLibraryPlacement` or `Pending.chooseTriggerOr`. -/
  | chooseBranch (branches : Array Instruction) (isLibrary : Bool := false)
  /-- Run `ifUnpaid` unless `payer` paid in `Pending.payOrLetCounter` (incl. CR 800.4f departure). -/
  | unlessPays (payer : PlayerId) (ifUnpaid : Instruction)
  /-- After an optional cost prompt resolves, bind `cost.bindVar?` (if any) from events since
  `startEventIdx` and run `onYes` (optionally re-offering up to `maxExtra` more times) or `onNo`. -/
  | afterOptionalCost (who : PlayerExpr) (cost : CostSpec) (onYes onNo : Instruction)
      (startEventIdx : Nat) (maxExtra : Nat := 0)
  /-- Re-offer an `.optional` instruction up to `remaining` additional times after `onYes` finishes. -/
  | repeatOptional (who : PlayerExpr) (cost? : Option CostSpec) (onYes : Instruction)
      (remaining : Nat)
  /-- Post-entry follow-up for a single permanent moved onto the battlefield. -/
  | afterPutToBattlefield (fromId : ObjectId) (fromGyOrExile : Bool)
      (mods : MoveMods) (cause : EventCause)
  /-- Post-exile follow-up for exile-and-return-immediately flicker effects. -/
  | afterExileReturnBriefly (dstP : PlayerId) (fromId : ObjectId) (cardName : String)
      (returnable : Bool) (cause : EventCause)
  /-- Post-return follow-up for returning a permanent tapped and exiling it at end step. -/
  | afterReturnTappedEndStepExile (dstP : PlayerId) (fromId : ObjectId)
      (cardName : String) (cause : EventCause)
  /-- Log `msg` if any counter kind on `targetId` increased over `before` (CR 122.1 / 614.6). -/
  | logIfCountersIncreased (targetId : ObjectId) (before : CounterBag) (msg : String)
  /-- Apply aggregated lifelink gain for damage dealt since `startEventIdx`. -/
  | applyAggregatedLifelink (startEventIdx : Nat) (cause : EventCause)
  /-- Post-move log after Explore puts a revealed land into hand (CR 701.44a). -/
  | exploreAfterLandMove (controller : PlayerId) (cardId : ObjectId)
      (destOwner : PlayerId) (cardName : String)
  /-- Offer the Explore optional graveyard move after putting a +1/+1 counter (CR 701.44a). -/
  | exploreOfferGraveyard (controller : PlayerId) (cardId : ObjectId)
  /-- Put non-matching revealed cards on the bottom (and optionally apply Dack hits). -/
  | afterRevealUntil (p : PlayerId) (rest : Array ObjectId) (shuffle : Bool)
      (dackTargets : Array ObjectId) (cause : EventCause)
  /-- Continue moving remaining cards from a distinct-name library search. -/
  | afterDistinctSearchMove (p : PlayerId) (remainingIds : Array ObjectId) (cause : EventCause)
  /-- After milling, offer a milled permanent to hand or gain `life`. -/
  | afterMillOfferPermanentOrGainLife (p : PlayerId) (preIds : Array ObjectId) (life : Nat)
  /-- After drawing, begin `count` discards followed by stun/counter follow-up. -/
  | afterDrawBeginDiscardThenStun (p : PlayerId) (count : Nat)
  /-- After drawing, arm +1/+1 counters per discarded card on `targetId?`. -/
  | afterDrawAddPlusOnesForDiscards (p : PlayerId) (targetId? : Option ObjectId)
  /-- Post-entry token modifiers (haste, sacrifice/exile at end step, counters, attach) for
  tokens created since `startEventIdx`. -/
  | afterTokensEnter (startEventIdx : Nat) (p : PlayerId) (mods : EnterMods) (cause : EventCause)
  /-- Worlds Within Worlds: collect each player's chosen exiled creature in turn order. -/
  | worldsCollectPlayers (exiledVar : VarId) (rest : Array PlayerId) (chosen : Array ObjectId)
  /-- Worlds Within Worlds: after putting chosen creatures onto the battlefield, return unchosen. -/
  | worldsAfterPut (exiledVar : VarId) (validChosen : Array (ObjectId × PlayerId × String))
  /-- Remaining objects in a multi-object zone move loop. -/
  | afterMoveLoop (remainingIds : Array ObjectId) (dest : DestZoneSpec)
      (verb : ZoneVerb) (mods : MoveMods) (cause : EventCause)
  /-- Remaining permanents in a multi-permanent damage loop with aggregated lifelink. -/
  | afterDamagePermanentsLoop (remainingIds : Array ObjectId) (amt : Nat) (srcName : String)
      (srcSnap? : Option EventObject) (oppOnlyCtrl? : Option PlayerId)
      (startEventIdx : Nat) (cause : EventCause)
  /-- Remaining targets in a divided-damage loop with mid-pause CR 608.2b legality recheck and aggregated lifelink. -/
  | afterDividedDamageLoop (remaining : Array (Nat × Target × Nat)) (srcName : String)
      (srcSnap? : Option EventObject) (startEventIdx : Nat) (cause : EventCause)
deriving Repr, Inhabited, BEq

/-- Complete resumable state of the unified `Instruction` interpreter. -/
structure InterpState where
  ctx : InterpCtx := {}
  queue : Array Instruction := #[]
  stack : Array InterpCont := #[]
deriving Repr, Inhabited, BEq

mutual

/-- Continuation stored while waiting for a player to answer `Pending.chooseReplacement`
when multiple replacement or prevention effects compete in the same CR 616.1a–e tier. -/
inductive PendingReplacement where
  | seq (first rest : PendingReplacement)
  | dealDamageToPlayer (p : PlayerId) (n : Nat)
      (source : Option EventObject) (unpreventable : Bool)
      (cause : Option EventCause) (suppressLifelink : Bool := false)
  | dealDamageToPlayers (players : Array PlayerId) (n : Nat)
      (source : Option EventObject) (cause : Option EventCause)
      (startEventIdx : Option Nat := none) (suppressLifelink : Bool := false)
  | dealDamageFrom (sourceName : String) (source : EventObject) (targetId : ObjectId)
      (n : Nat) (deathtouch : Bool)
      (cause : Option EventCause) (suppressLifelink : Bool := false)
  | dealFightDamage (sourceId targetId : ObjectId) (cause : Option EventCause)
      (amount : Option Nat := none)
  | dealDamageToPermanent (targetId : ObjectId) (n : Nat)
      (source : Option EventObject)
      (cause : Option EventCause) (suppressLifelink : Bool := false)
  | markDamageOn (targetId : ObjectId) (n : Nat) (msg : String)
      (deathtouch : Bool) (source : Option EventObject) (combat : Bool)
      (unpreventable : Bool) (cause : Option EventCause)
  | dealAssignedCombatDamage (startIdx : Nat := 0)
  | gainLife (p : PlayerId) (n : Nat) (cause : Option EventCause)
  | addPlusOnePlusOneTo (targetId : ObjectId) (n : Nat) (entersWith : Bool)
      (byPlayer : Option PlayerId) (cause : Option EventCause)
  | addCounters (targetId : ObjectId) (kind : CounterKind) (n : Nat)
      (entersWith : Bool) (byPlayer : Option PlayerId) (cause : Option EventCause)
  | recordPutCounters (targetId : ObjectId) (kind : CounterKind) (n : Nat)
      (byPlayer : Option PlayerId) (cause : Option EventCause)
  | putCountersDeferredLog (targetId : ObjectId) (kind : CounterKind) (n : Nat)
      (byPlayer : Option PlayerId) (logKind : PutCounterLog) (cause : Option EventCause)
  | logPutCounterDelta (targetId : ObjectId) (kind : CounterKind) (before : Nat)
      (logKind : PutCounterLog)
  | move (id : ObjectId) (dest : Zone) (controller : Option PlayerId)
      (verb : Option ZoneVerb)
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
      (enterMods : Array EnterMod := #[])
      (cause : Option EventCause)
      (lkiController? : Option PlayerId := none)
      (skipUnattachIds : Array ObjectId := #[])
  | moveSimultaneousToGraveyard (ids : Array ObjectId)
      (preBattlefield : Option (Array GameObject))
      (cause : Option EventCause)
      (deferPlayFromExileLogs : Bool := false)
      (fromEventIdx? : Option Nat := none)
  | destroyPermanent (targetId : ObjectId) (cause : Option EventCause)
      (preBattlefield : Option (Array GameObject) := none)
      (reason : Option String := none)
  | createToken (controller : PlayerId) (card : CardDef) (tapped : Bool)
      (attacking : Bool) (attackingTarget : Option AttackTarget)
      (applyFoodBonus : Bool) (extraCounters : CounterBag)
      (recordRecent : Bool := false) (cause : Option EventCause)
      (count : Nat := 1)
  | createTokenBatches (batches : Array ProposedTokenBatch)
      (attacking : Bool) (attackingTarget : Option AttackTarget)
      (extraCounters : CounterBag) (recordRecent : Bool)
      (cause : Option EventCause)
  | createTreasureTokens (controller : PlayerId) (n : Nat) (tapped : Bool)
      (cause : Option EventCause)
  | createKindTokens (controller : PlayerId) (kind : TokenSpec) (n : Nat)
      (tapped : Bool) (attacking : Bool) (attackingTarget : Option AttackTarget)
      (resetRecent : Bool) (cause : Option EventCause)
      (copyEnv : StoredEvalEnv := {})
  | createAndMarkTokensAttacking (controller : PlayerId) (kind : TokenSpec)
      (n : Nat) (tapped holds : Bool) (sourceId : Option ObjectId)
      (cause : Option EventCause := none)
      (copyEnv : StoredEvalEnv := {})
  | commitEnteringAttackItems (chosen : Array (EnteringAttackItem × Option AttackTarget))
      (cause : Option EventCause) (resetRecent : Bool)
      (postEntries : Array (ObjectId × PlayerId × String × List EnterMod × EnteringAttackLog) := #[])
      (preBattlefield : Option (Array GameObject) := none)
  | finishEnteringAttackCards
      (postEntries : Array (ObjectId × PlayerId × String × List EnterMod × EnteringAttackLog))
      (cause : Option EventCause)
  | finishEnteringAttackCard (newId : Option ObjectId) (effectController : PlayerId)
      (cardName : String) (mods : List EnterMod)
      (logKind : EnteringAttackLog) (cause : Option EventCause)
  | afterLastPermanentEnters (fromId : Option ObjectId := none) (isPlayLand : Bool := false)
      (attachedToHost : Option ObjectId := none)
  | addExtraCombatDamageStep
  | finishResolutionChoice
  | shuffleThen (player : PlayerId) (onDone : AfterRandom)
  | draw (p : PlayerId) (n : Nat) (cause : Option EventCause)
  | drawOne (p : PlayerId) (applied : Array ReplacementId) (drawStepFirst : Bool)
      (cause : Option EventCause)
  | drawSubDraws (p : PlayerId) (remaining : Nat) (applied : Array ReplacementId)
      (cause : Option EventCause)
  | connive (controller : PlayerId) (sourceId : Option ObjectId)
  | finishSbaSweep (moves : Array SbaGraveyardMove) (preBattlefield : Array GameObject)
      (stage : SbaSweepStage) (pwMoves : Array SbaGraveyardMove := #[])
      (sagaMoves : Array SbaGraveyardMove := #[])
      (tokensOutsideBf : Array ObjectId := #[])
      (copiesOutside : Array ObjectId := #[])
      (illegalAuras : Array ObjectId := #[])
      (illegalEquips : Array (ObjectId × ObjectId) := #[])
      (illegalCreatureAtts : Array (ObjectId × ObjectId) := #[])
      (legendGroups : Array (PlayerId × String × Array ObjectId) := #[])
      (deferPlayFromExileLogs : Bool := false)
  | untapPermanent (targetId : ObjectId) (duringUntapStep : Bool := false)
      (logUntap : Bool := true) (cause : Option EventCause := none)
  | untapStepPermanents (ids : Array ObjectId)
  | addLoreCounters (sagaId : ObjectId) (n : Nat) (cause : Option EventCause)
  | addLoreAfterDrawStep (sagaIds : Array ObjectId)
  | copyNontokenCreatures (controller : PlayerId) (snapshots : Array CardDef)
      (cause : Option EventCause)
  | copyPermanentTokens (controller : PlayerId) (card : CardDef) (remaining : Nat)
      (cause : Option EventCause) (priorRecentCount : Nat := 0) (pushedFrame : Bool := false)
  | finishArtifactCopyToken
  | finishManaAbilityMountainTrigger (player : PlayerId) (sourceId : ObjectId)
  | restorePending (p : Pending) (popOuter : Bool := false)
      (promptLog : Option String := none) (departed : Array PlayerId := #[])
      (rewindProposal : Option Bool := none)
  | closeBatch (batchId : BatchId) (startIdx : Nat)
  | restorePausedBatch (batchId : BatchId) (startIdx : Nat) (wasDiscard : Bool)
      (cause : Option EventCause) (objects : Array GameObject)
      (players : Array Player) (effects : Array (EffectId × ContinuousEffectSpec))
      (pending : Pending) (stack : Array StackEntry := #[])
      (closeIfOrphaned : Bool := true) (queuedLinkedExile : Array ObjectId := #[])
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
  | finishProposedSpellCosts (stage : ProposedSpellCostStage)
      (grantPriority hadOuterReplacement hadOpenContinuation : Bool)
  | finishTurnFaceUp (caster : PlayerId) (spellId : ObjectId)
      (hadOuterReplacement : Bool := false)
  | endProposalAction (clearCkpt : Bool := false)
  | payCostPickItems (p : PlayerId) (abilityId sourceId : Option ObjectId) (pick : CostPick)
      (remainingIds : Array ObjectId)
  | finishActivationExtraCosts (p : PlayerId) (sourceId : ObjectId)
      (forObject : Option ObjectId) (sacrificeSource exileSource : Bool)
      (stage : ActivationExtraCostStage := .sacrificeAndExile)
      (sinceIdx : Nat := 0)
  | finishPostLoyaltyActivated (caster : PlayerId) (sourceName : String)
      (sourceId : Option ObjectId) (activation : Option ActivatedAbility)
      (abilityId : Option ObjectId)
      (sourceSnapshot : Option EventObject) (sourceOriginal : Option GameObject)
      (hadOuterReplacement hadOpenContinuation : Bool)
  | finishActivateManaAbilityPicks (p : PlayerId) (id : ObjectId) (oname : String)
      (mana : Array ManaType) (remainingPicks : Array CostPick)
      (remainingCostIds : Array ObjectId) (tap sacrificeSelf : Bool)
      (activatedIdx : Option Nat) (restriction : Option ManaSpendRestriction)
      (damageYou : Nat) (isMountain : Bool) (prevPending : Pending)
      (exileSelf : Bool := false) (powerUp : Bool := false) (exhaust : Bool := false)
      (riders : Array SpellRiderSpec := #[])
      (exileFromZone? : Option ZoneKind := none) (discardSelf : Bool := false)
      (exileSymIds : Array ObjectId := #[]) (extraEffect? : Option Effect := none)
  | finishActivateManaAbilityPostSac (p : PlayerId) (id : ObjectId) (oname : String)
      (srcSnap : EventObject) (mana : Array ManaType) (tap : Bool)
      (activatedIdx : Option Nat) (restriction : Option ManaSpendRestriction)
      (damageYou : Nat) (isMountain : Bool) (prevPending : Pending)
      (powerUp : Bool := false) (exhaust : Bool := false)
      (riders : Array SpellRiderSpec := #[])
      (extraEffect? : Option Effect := none)
  | runModalManaEffect (p : PlayerId) (sourceId : ObjectId) (effect : Effect)
  | finishBeginRecruit (p : PlayerId)
  | finishDrawThenBeginDiscard (p : PlayerId) (discardRounds : Nat)
  | finishConniveDraws (controller : PlayerId)
      (extraDraws : Array (Nat × ReplacementId))
      (conniveDrawCause : Option EventCause) (stage : ConniveDrawStage := .draws)
  | amass (controller : PlayerId) (subtype : CardSubtype) (n : Nat)
      (attach : Option ObjectId := none) (cause : Option EventCause := none)
  | finishAmassOn (controller : PlayerId) (armyId : ObjectId) (subtype : CardSubtype)
      (n : Nat) (attach : Option ObjectId := none) (stage : AmassStage := .putCounters)
      (cause : Option EventCause := none)
  | finishFreshAmass (controller : PlayerId) (subtype : CardSubtype) (n : Nat)
      (attach : Option ObjectId) (cause : Option EventCause) (startEventIdx : Nat := 0)
  | finishDealDamageLoseIndestructibleExile (targetId : ObjectId) (targetName : String)
      (n : Nat) (cause : EventCause)
  | finishPlaceSearched (p : PlayerId) (fromId : ObjectId) (name : String)
      (tapped : Bool) (cause : Option EventCause)
  | placeSearchedBatch (p : PlayerId) (remainingIds : Array ObjectId) (tapped : Bool)
      (cause : Option EventCause)
      (entered : Array (ObjectId × String) := #[])
      (preBattlefield : Option (Array GameObject) := none)
  | finishSearchAfterPlace (p : PlayerId) (fromId : Option ObjectId)
      (dest : SearchDest) (after : Option Instruction) (fromLibrary : Bool)
      (handRest : Array ObjectId := #[]) (cause : Option EventCause := none)
  | surveilMoveLoop (p : PlayerId) (remainingGy : Array ObjectId) (cause : Option EventCause)
  | finishSurveilPostMove (p : PlayerId) (card : GameObject) (fromId : ObjectId)
      (remainingGy : Array ObjectId) (cause : Option EventCause)
  | finishLibraryLook
  | requestOrderInto (ids : Array ObjectId) (dest : Zone) (log : String)
      (cause : Option EventCause)
  | finishProliferateEachKind (controller : PlayerId) (targetId : ObjectId)
      (remainingKinds : Array CounterKind) (hasPlusOne : Bool)
      (effCause : EventCause)
  | finishProliferateTarget (p : PlayerId) (targetId : ObjectId)
      (remainingKinds : Array CounterKind) (hasPlusOne : Bool)
      (remainingTargets : Array Target) (permIds : Array ObjectId)
      (playerIds : Array PlayerId) (chosenEmpty : Bool)
      (remainingRounds : Nat) (cause : Option EventCause)
  | finishDiscardForDrawMay (p : PlayerId) (n : Nat)
  | finishSacArtifactOrDiscardDraw (p : PlayerId) (n : Nat)
  | finishChooseDiscardCard (p : PlayerId) (card : GameObject)
      (remaining : Array PlayerId)
  | finishRecruitDiscard (p : PlayerId) (isLand : Bool)
  | finishPutLandFromHand (fromId : ObjectId)
  | finishBeginOnBattlefield (fromId : ObjectId) (remainingIds : Array ObjectId)
  | addFinalityTo (targetId : ObjectId) (n : Nat) (byPlayer : Option PlayerId)
      (entersWith : Bool) (cause : Option EventCause)
  | loseLifeAfterDraw (p : PlayerId) (life : Nat) (cause : Option EventCause)
  | continueSpellModes (controller : PlayerId) (modeEffects : Array Effect)
      (remainingTargets : Array Target)
      (castFromGraveyard kicked giftPromised : Bool) (chosenX : Option Nat := none)
      (sourceId : Option ObjectId := none)
      (skippedOptionalSlots : Array Nat := #[])
      (lastKnownPower : Option Int := none)
      (lastKnownToughness : Option Int := none)
  | empowerJace (controller : PlayerId) (n : Nat) (stage : EmpowerJaceStage := .initial)
      (targetId : Option ObjectId := none) (cause : Option EventCause := none)
  | continueConnives (controller : PlayerId) (remainingIds : Array ObjectId)
  | dealDamageToEachCreatureMatching (remainingIds : Array ObjectId) (n : Nat)
      (onlyNonSubtype : Option CardSubtype := none)
      (exceptControllerTokens : Option PlayerId := none)
      (onlyOpponentsOf : Option PlayerId := none)
      (source : Option EventObject := none) (cause : Option EventCause := none)
      (startEventIdx : Option Nat := none) (suppressLifelink : Bool := false)
  | destroyPermanentsLoop (remainingIds : Array ObjectId)
      (allCandidates : Array ObjectId := #[]) (countNote : Bool := false)
      (obGainLifeFor : Option PlayerId := none)
      (logMsgAfter : Option String := none)
      (preBattlefield : Option (Array GameObject) := none)
      (cause : Option EventCause := none)
  | sacrificePermanentsLoop (remaining : Array (PlayerId × ObjectId))
      (preBattlefield : Option (Array GameObject) := none)
      (cause : Option EventCause := none)
      (createBeastFor : Option PlayerId := none)
      (passiveLog : Bool := false)
  | putToBattlefieldLoop (controller : PlayerId) (remainingIds : Array ObjectId)
      (enteredFromIds : Array ObjectId := #[]) (useCardOwner : Bool := false)
      (haste : Bool := false) (tapped : Bool := false)
      (isLandEnters : Bool := false) (onlyFoodArtifact : Bool := false)
      (entryLog : PutBattlefieldEntryLog := .none)
      (cause : Option EventCause := none)
      (preBattlefield : Option (Array GameObject) := none)
  | returnLinkedExileLoop (remainingIds : Array ObjectId)
      (cause : Option EventCause := none)
      (enteredFromIds : Array ObjectId := #[])
      (preBattlefield : Option (Array GameObject) := none)
      (pendingLog : Option (ObjectId × Zone) := none)
  | putShadowCounter (targetId : ObjectId)
  | finishShadowCounter (targetId : ObjectId) (before : Nat)
  | finishLinkedExileMove (remainingIds : Array ObjectId)
      (preBattlefield : Option (Array GameObject) := none)
      (pendingLog : Option (ObjectId × Zone) := none)
      (enteredFromIds : Array ObjectId := #[])
  | untapPermanentsLoop (remainingIds : Array ObjectId)
      (cause : Option EventCause := none)
  | millCardsLoop (p : PlayerId) (remainingIds : Array ObjectId)
      (emptyTail : Bool := false) (cause : Option EventCause := none)
      (logCard : Option String := none) (freshCount : Option Nat := none)
  | exilePermanentsLoop (remainingIds : Array ObjectId) (logExile : Bool := true)
      (cause : Option EventCause := none) (logCard : Option (ObjectId × String) := none)
  | flickerLoop (remainingIds : Array ObjectId)
      (exiledPreIds : Array ObjectId := #[])
      (enteredFromIds : Array ObjectId := #[])
      (logText : String := "is exiled, then returned to the battlefield")
      (stage : FlickerStage := .exileBatch) (tapped : Bool := false) (onlyLandTapped : Bool := false)
      (clearExileFields : Bool := false) (cause : Option EventCause := none)
      (preBattlefield : Option (Array GameObject) := none)
  | finishMillChooseForHand (p : PlayerId) (preIds : Array ObjectId)
      (types : Array CardType) (matchedPreIds : Array ObjectId)
      (max : Nat) (mustOne : Bool) (allMatches : Bool := false)
      (maxPut : Option Nat := none) (cause : Option EventCause := none)
  | finishPostStep (step : PostStep)
  | setLife (p : PlayerId) (life : Int) (msg : String) (cause : Option EventCause)
  | logMessage (msg : String)
  | counterStackSpell (spellId : ObjectId) (exilePermanent grantFreeCast : Bool)
      (ctrl : Option PlayerId) (cause : Option EventCause)
      (postMove : Bool := false) (name : String := "")
  | returnStackSpell (spellId : ObjectId) (owner : PlayerId) (name : String)
      (postMove : Bool := false)
  | leavePlayersWhoLost (savedPending : Option Pending := none) (popOuter : Bool := false)
      (departed : Array PlayerId := #[]) (rewindProposal : Option Bool := none)
      (fromEventIdx? : Option Nat := none)
  | endControlExileLoop (remaining : Array (ObjectId × String × Option PlayerId))
      (cause : Option EventCause := none)
      (pendingLog : Option (ObjectId × String) := none)
      (extraSkipIds : Array ObjectId := #[])
      (fromEventIdx? : Option Nat := none)
  | beginStepCont (step : Step)
  | finishCleanupAfterClearEot
  | continueStartNextTurn (nextP : PlayerId) (remainingDeparted : Array PlayerId)
      (runBeginTurn : Bool := false) (alreadyExpired : Array PlayerId := #[])
  | beginTurnAfterStartExpiry
  | moveCardsToGraveyardLoop (ids : Array ObjectId) (cause : Option EventCause := none)
      (fromEventIdx? : Option Nat := none)
  | placeSearchedGraveyardLoop (ids : Array ObjectId) (cause : Option EventCause := none)
      (pendingLog : Option (ObjectId × PlayerId × String) := none)
  | finishConcede (wasIdlePriority : Bool) (savedPendingPrio : Option PlayerId)
      (wasAssigningCombatDamage : Option Bool := none)
      (savedPending : Option Pending := none) (popOuter : Bool := false)
      (departed : Array PlayerId := #[]) (rewindProposal : Option Bool := none)
      (fromEventIdx? : Option Nat := none)
  | concedePlayersLoop (remaining : Array PlayerId)
      (wasPregame midResolutionOrBatch wasIdlePriority : Bool)
      (savedPendingPrio : Option PlayerId)
      (wasAssigningCombatDamage : Option Bool := none)
      (savedPending : Option Pending := none) (popOuter : Bool := false)
      (departed : Array PlayerId := #[]) (rewindProposal : Option Bool := none)
      (fromEventIdx? : Option Nat := none)
  | afterWardResolved
  | runPostCastCleanup (cleanup : PostCastCleanup)
  | continueCheckpointReplay (remainingStream fullKeptStream : Array (Bool × GameEvent))
      (revMap : Array (ObjectId × ObjectId))
      (liveObjMap : Array (ObjectId × ObjectId) := #[])
      (effRevMap : Array (EffectId × EffectId) := #[])
      (minPostCkptEffId : Nat := 0)
      (suppressInteractive : Bool := false)
      (keptOrigNextEffs : Array Nat := #[])
  | phaseOutPermanentsLoop (remainingIds : Array ObjectId)
      (cause : Option EventCause := none)
      (preSnaps : Array (ObjectId × EventObject) := #[])
      (startEventIdx : Option Nat := none)
      (reconcile : Bool := true)
  | phaseInControlled (p : PlayerId) (includeTeammates : Bool := false)
  | phaseInControlledLoop (remainingIds : Array ObjectId)
      (cause : Option EventCause := none)
      (startEventIdx : Option Nat := none)
      (reconcile : Bool := true)
      (allowDirectSingle : Bool := false)
  /-- Resume the unified `Instruction` interpreter after a CR 616.1
  replacement choice completes (CR 608.2c / 614.6). -/
  | continueInterpreter (state : InterpState)
deriving Inhabited

/-- One frame of mid-resolution continuation state (CR 608.2). Grouping the
active resolution registers plus `resolvingContext`, `resolvingSpell`,
`resolvingAbility`, `resolvingDivision`, `afterRandom`, `resolutionFinish`,
`pendingReplacement`, `stepEnv`, and `interpWait?` into a frame on
`Game.continuations` prevents nested resolution choices (reflexive triggers,
replacement choices, cast-during-resolution) from clobbering outer frames. -/
structure ContinuationFrame where
  /-- Draw these cards after the current scry finishes (e.g. Hithlain Knots). -/
  pendingDrawAfterScry : Option (PlayerId × Nat) := none
  /-- Tokens created by the most recent `createKindTokens` call, so a following
  step can haste them or exclude them from a counter/pump effect. -/
  recentTokenIds : Array ObjectId := #[]
  /-- Copies a player may still cast without paying their mana costs as an
  ability resolves, with the mana value left (Uldaros Theorix). -/
  pendingFreeCopies : Option (PlayerId × Array ObjectId × Nat × Nat) := none
  /-- Spells exiled by a resolving ability that may still be cast without
  paying their mana costs, and how many casts remain (Doom Reigns Supreme). -/
  pendingMayCastFromExile : Option (PlayerId × Array ObjectId × Nat) := none
  /-- Deferred post-cast cleanup (Cascade / Gríma / Cosmic Cube library bottoming
  or CR 704.5e copy cease-to-exist) run when the proposed cast completes or reverses. -/
  postCastCleanup : Option PostCastCleanup := none
  /-- After the pending surveil, a card with mana value at most this put into the graveyard goes to hand. -/
  surveilReturnMvAtMost : Option Nat := none
  /-- Continuation for an event paused on `Pending.chooseReplacement` (CR 616.1). -/
  pendingReplacement : Option PendingReplacement := none
  /-- Outer `pendingReplacement` continuations saved while an interactive choice
  handler runs so inner CR 616.1 pauses cannot overwrite them. -/
  outerPendingReplacements : Array PendingReplacement := #[]
  /-- Source of the current connive action, if any (MSH / CR 701.50). -/
  conniveSource : Option ObjectId := none
  /-- Remaining discards for Thirst for Knowledge (MSH 344). -/
  thirstDiscardsLeft : Nat := 0
  /-- Discarding a card of this type finishes `thirstDiscardsLeft` early. -/
  thirstDiscardType : CardType := .artifact
  /-- Remaining discards for a required multi-card discard. -/
  pendingDiscardsLeft : Nat := 0
  /-- Per-player discard count for a multi-player `beginDiscardCards` instruction. -/
  discardCountPerPlayer : Nat := 0
  /-- Shared `(batchId, startEventIdx)` kept open across non-Thirst multi-card /
  multi-player `beginDiscardCards` prompts (CR 603.2c / 701.9b). -/
  discardBatch : Option (BatchId × Nat) := none
  /-- Pre-replaced single-token `ProposedTokenBatch`es staged across entering-attacking
  target choices (`createAndMarkTokensAttacking` -> `commitEnteringAttackItems`). -/
  stagedAttackTokenBatches : Array ProposedTokenBatch := #[]
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
  /-- Modes announced when the resolving stack ability was put onto the stack (CR 603.3c / 700.2). -/
  resolvingModes : Option (Array Nat) := none
  /-- Damage assigned to each target of the resolving divided-damage ability (CR 601.2d). -/
  resolvingDivision : Array Nat := #[]
  /-- Optional target-slot indices skipped when announcing the resolving spell or ability (CR 601.2c / 608.2b). -/
  resolvingSkippedSlots : Array Nat := #[]
  /-- Resolution-scoped continuation after a `--norandom` result is applied. -/
  afterRandom : AfterRandom := .none
  /-- Deferred CR 608.2n / 608.2p / 608.3 completion step for the resolving stack object. -/
  resolutionFinish : Option ResolutionFinish := none
  /-- Deferred `StackObjectEvent.resolved` payload waiting on an ETB replacement
  or as-enters choice opened during `resolutionFinish`. -/
  pendingResolvedEvent : Option (EventObject × PlayerId × EventCause) := none
  /-- Lexical `stepEnv` bindings from bound `Instruction.bind` steps and interactive choices (CR 608.2c / 614.6). -/
  stepEnv : Array (VarId × StepOutcome) := #[]
  /-- Suspended unified `Instruction` interpreter state waiting on an
  interactive `Pending` choice or `AfterRandom.continueInterpreter`. -/
  interpWait? : Option InterpState := none
deriving Inhabited

/-- Mutations to the top frame of `Game.continuations`. -/
inductive ContinuationChange where
  | pendingDrawAfterScry (v : Option (PlayerId × Nat))
  | recentTokenIds (v : Array ObjectId)
  | pendingFreeCopies (v : Option (PlayerId × Array ObjectId × Nat × Nat))
  | pendingMayCastFromExile (v : Option (PlayerId × Array ObjectId × Nat))
  | postCastCleanup (v : Option PostCastCleanup)
  | surveilReturnMvAtMost (v : Option Nat)
  | pendingReplacement (v : Option PendingReplacement)
  | pushOuterPendingReplacement (v : PendingReplacement)
  | popOuterPendingReplacement
  | conniveSource (v : Option ObjectId)
  | thirstDiscardsLeft (v : Nat)
  | thirstDiscardType (v : CardType)
  | pendingDiscardsLeft (v : Nat)
  | discardCountPerPlayer (v : Nat)
  | discardBatch (v : Option (BatchId × Nat))
  | stagedAttackTokenBatches (v : Array ProposedTokenBatch)
  | stashedCause (v : Option EventCause)
  | resolvingSpell (v : Option ObjectId)
  | resolvingAbility (v : Option ObjectId)
  | resolvingDivision (v : Array Nat)
  | resolvingSkippedSlots (v : Array Nat)
  | afterRandom (v : AfterRandom)
  | resolutionFinish (v : Option ResolutionFinish)
  | pendingResolvedEvent (v : Option (EventObject × PlayerId × EventCause))
  | stepEnv (v : Array (VarId × StepOutcome))
  | bindStepOutcome (v : VarId) (o : StepOutcome)
  | interpWait? (v : Option InterpState)
deriving Inhabited

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
  | stackEntry (objectId : ObjectId) (c : StackEntryChange)
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
      (stack : Array StackEntry := #[])
  | setPausedBatchCause (cause : Option EventCause)
  | clearPausedBatch
  /-- Update the continuation frame stack. -/
  | pushContinuationFrame (frame : ContinuationFrame)
  | popContinuationFrame
  | continuation (c : ContinuationChange)
  /-- Update game fields. -/
  | priority (v : PlayerId)
  | pendingPriority (v : Option PlayerId)
  | pendingBlockerAssignments (v : Array CreatureCombatAssignment)
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
  | queueLinkedExile (ids : Array ObjectId)
  | clearQueuedLinkedExile
  | replacementOrder (ids : Array ReplacementId)
  | castingFromTop (v : Bool)
  | sbaChecked
deriving Inhabited

/-- One change to the game, without the turn number. -/
inductive GameChange where
  | rules (e : RulesEvent)
  | engine (c : EngineChange)
deriving Inhabited

/-- A game state change on a given turn (CR 500). `Game.events` records each
one that happens. Every `RulesEvent` carries an explicit `EventCause`;
internal `EngineChange` mutations are cause-free. -/
inductive GameEvent where
  | rules (turn : Nat) (e : RulesEvent) (cause : EventCause) (batch : Option BatchId := none)
  | engine (turn : Nat) (c : EngineChange) (batch : Option BatchId := none)
deriving Inhabited

end

-- Derive the 6-way mutual `BEq` tuple once instead of emitting six identical
-- copies across `PendingReplacement`..`GameEvent` (`Repr` is unused on game state).
deriving instance BEq for PendingReplacement

instance : BEq ContinuationFrame := ⟨instBEqPendingReplacement.beq_2⟩
instance : BEq ContinuationChange := ⟨instBEqPendingReplacement.beq_3⟩
instance : BEq EngineChange := ⟨instBEqPendingReplacement.beq_4⟩
instance : BEq GameChange := ⟨instBEqPendingReplacement.beq_5⟩
instance : BEq GameEvent := ⟨instBEqPendingReplacement.beq_6⟩

/-- Whether `pr` is a pure post-log continuation (emitting only log messages
without altering prompts, priority, or control flow) that is transparent to
trailing priority-grant checks. -/
def PendingReplacement.isPurePostLog : PendingReplacement → Bool
  | .finishPostStep (.logExpiredPlayFromExile ..)
  | .logMessage _ => true
  | .seq a b => a.isPurePostLog && b.isPurePostLog
  | _ => false

/-- Whether a `PendingReplacement` continuation ends with `.finishResolutionChoice`
(ignoring pure post-log tails). -/
def PendingReplacement.endsWithFinishResolutionChoice : PendingReplacement → Bool
  | .finishResolutionChoice => true
  | .seq a b =>
    if b.isPurePostLog then a.endsWithFinishResolutionChoice
    else b.endsWithFinishResolutionChoice
  | _ => false

/-- Whether a `PendingReplacement` continuation contains a suppressed checkpoint replay. -/
def PendingReplacement.hasSuppressedCheckpointReplay : PendingReplacement → Bool
  | .continueCheckpointReplay _ _ _ _ _ _ suppressInteractive _ => suppressInteractive
  | .seq a b => a.hasSuppressedCheckpointReplay || b.hasSuppressedCheckpointReplay
  | _ => false

/-- Whether a `PendingReplacement` continuation contains any checkpoint replay. -/
def PendingReplacement.hasCheckpointReplay : PendingReplacement → Bool
  | .continueCheckpointReplay .. => true
  | .seq a b => a.hasCheckpointReplay || b.hasCheckpointReplay
  | _ => false

/-- Whether `st` unconditionally grants priority (either directly or after
silent cleanup turn advancement) without opening a non-replacement prompt. -/
def PendingReplacement.stepAlwaysGrantsPriority : Step → Bool
  | .upkeep | .draw | .precombatMain | .beginningOfCombat
  | .endOfCombat | .postcombatMain | .end | .cleanup => true
  | .untap | .declareAttackers | .declareBlockers | .combatDamage => false

/-- Update `hasQueuedPending` across a `PendingReplacement` tree without `Game`
state: clears to `false` on draining leaves and preserves on neutral leaves. -/
def PendingReplacement.nextQueuedPending (hasQueuedPending : Bool := false) :
    PendingReplacement → Bool
  | .seq a1 a2 => a2.nextQueuedPending (a1.nextQueuedPending hasQueuedPending)
  | .receivePriority _ | .finishResolutionChoice | .afterWardResolved
  | .runPostCastCleanup _
  | .beginTurnAfterStartExpiry
  | .finishCleanupAfterClearEot
  | .finishPostStep .startNextTurnAndBegin
  | .finishPostStep .endTurnAfterCleanupStepEnded
  | .finishPostStep .cleanupStepAfterDiscard
  | .finishPostStep (.postSbaCleanup _) => false
  | .finishConcede _ _ wc .. => if wc.isNone then false else hasQueuedPending
  | .beginStepCont st
  | .finishPostStep (.beginStepBody st)
  | .finishPostStep (.beginStepAfterPhaseBegan st) =>
    if stepAlwaysGrantsPriority st then false else hasQueuedPending
  | .concedePlayersLoop _ wp mid _ _ wc .. =>
    if !wp && !mid && wc.isNone then false else hasQueuedPending
  | .finishPostCast _ _ hadOuter _
  | .finishBecomeCast _ _ _ hadOuter _
  | .finishProposedSpellCosts _ _ hadOuter _
  | .completeActivation hadOuter _
  | .finishBecomeActivated _ _ _ _ _ _ _ hadOuter _
  | .finishPostLoyaltyActivated _ _ _ _ _ _ _ hadOuter _
  | .finishTurnFaceUp _ _ hadOuter =>
    if !hadOuter then false else hasQueuedPending
  | .finishActivateManaAbilityPicks _ _ _ _ _ _ _ _ _ _ _ _ prevPending ..
  | .finishActivateManaAbilityPostSac _ _ _ _ _ _ _ _ _ _ prevPending .. =>
    if prevPending == .none then false else hasQueuedPending
  | _ => hasQueuedPending

/-- Whether a `PendingReplacement` continuation already ends by granting
priority (`.receivePriority` / `.finishResolutionChoice` / `.finishPostCast` /
`.finishBecomeCast` with `grantPriority == true` / `.finishConcede` /
mana-ability completions with `prevPending == .none`), ignoring pure post-log tails. -/
def PendingReplacement.endsWithPriorityGrant (pr : PendingReplacement)
    (hasQueuedPending : Bool := false) : Bool :=
  match pr with
  | .receivePriority _ | .finishResolutionChoice | .afterWardResolved
  | .beginTurnAfterStartExpiry
  | .finishCleanupAfterClearEot
  | .finishPostStep .startNextTurnAndBegin
  | .finishPostStep .endTurnAfterCleanupStepEnded
  | .finishPostStep .cleanupStepAfterDiscard
  | .finishPostStep (.postSbaCleanup _) => true
  | .finishConcede _ _ wc .. => wc.isNone
  | .beginStepCont st
  | .finishPostStep (.beginStepBody st)
  | .finishPostStep (.beginStepAfterPhaseBegan st) =>
    stepAlwaysGrantsPriority st
  | .concedePlayersLoop _ wp mid _ _ wc .. => !wp && !mid && wc.isNone
  | .finishPostCast _ _ hadOuter _ => !hadOuter
  | .finishBecomeCast _ _ grantPriority hadOuter _ =>
    grantPriority && !hadOuter
  | .finishProposedSpellCosts _ grantPriority hadOuter _ =>
    grantPriority && !hadOuter
  | .completeActivation hadOuter _
  | .finishBecomeActivated _ _ _ _ _ _ _ hadOuter _
  | .finishPostLoyaltyActivated _ _ _ _ _ _ _ hadOuter _
  | .finishTurnFaceUp _ _ hadOuter =>
    !hadOuter || hasQueuedPending
  | .finishActivateManaAbilityPicks _ _ _ _ _ _ _ _ _ _ _ _ prevPending ..
  | .finishActivateManaAbilityPostSac _ _ _ _ _ _ _ _ _ _ prevPending .. =>
    prevPending == .none
  | .seq a b =>
    if b.isPurePostLog then a.endsWithPriorityGrant hasQueuedPending
    else b.endsWithPriorityGrant (a.nextQueuedPending hasQueuedPending)
  | _ => false

/-- Whether a `PendingReplacement` continuation ends with a non-proposal priority
grant (`.receivePriority`, `.finishResolutionChoice`, `.finishConcede`,
`.afterWardResolved`, an idle `.concedePlayersLoop`, or an unconditionally
priority-granting step/turn/cleanup continuation), excluding
proposal-completion continuations and ignoring pure post-log tails. -/
def PendingReplacement.endsWithNonProposalPriorityGrant : PendingReplacement → Bool
  | .receivePriority _ | .finishResolutionChoice | .afterWardResolved
  | .beginTurnAfterStartExpiry
  | .finishCleanupAfterClearEot
  | .finishPostStep .startNextTurnAndBegin
  | .finishPostStep .endTurnAfterCleanupStepEnded
  | .finishPostStep .cleanupStepAfterDiscard
  | .finishPostStep (.postSbaCleanup _) => true
  | .finishConcede _ _ wc .. => wc.isNone
  | .beginStepCont st
  | .finishPostStep (.beginStepBody st)
  | .finishPostStep (.beginStepAfterPhaseBegan st) =>
    stepAlwaysGrantsPriority st
  | .concedePlayersLoop _ wp mid _ _ wc .. => !wp && !mid && wc.isNone
  | .seq a b =>
    if b.isPurePostLog then a.endsWithNonProposalPriorityGrant
    else b.endsWithNonProposalPriorityGrant
  | _ => false

/-- Whether `pr` is a pure trailing priority-granting leaf before which deferred
`.logExpiredPlayFromExile` post-steps should be inserted so expiry logs emit
before `PriorityEvent.received` (CR 117.3 / 611.2). -/
def PendingReplacement.isPurePriorityGrantLeaf : PendingReplacement → Bool
  | .receivePriority _ | .finishResolutionChoice | .afterWardResolved
  | .beginTurnAfterStartExpiry
  | .finishCleanupAfterClearEot
  | .finishPostStep .startNextTurnAndBegin
  | .finishPostStep .endTurnAfterCleanupStepEnded
  | .finishPostStep .cleanupStepAfterDiscard
  | .finishPostStep (.postSbaCleanup _) => true
  | .finishConcede _ _ wc .. => wc.isNone
  | .beginStepCont st
  | .finishPostStep (.beginStepBody st)
  | .finishPostStep (.beginStepAfterPhaseBegan st) =>
    stepAlwaysGrantsPriority st
  | .concedePlayersLoop _ wp mid _ _ wc .. => !wp && !mid && wc.isNone
  | _ => false

/-- Insert `postStep` immediately before any trailing pure priority-grant leaf
(or before a pure post-log tail sitting after one) in `pr`, or at the end of
`pr` when `pr` does not end with a pure priority-grant leaf. -/
def PendingReplacement.insertBeforeTrailingPriorityGrant
    (pr postStep : PendingReplacement) : PendingReplacement :=
  match pr with
  | .seq a b =>
    if b.isPurePriorityGrantLeaf || (b.isPurePostLog && a.endsWithNonProposalPriorityGrant) then
      .seq (a.insertBeforeTrailingPriorityGrant postStep) b
    else
      .seq a (b.insertBeforeTrailingPriorityGrant postStep)
  | leaf =>
    if leaf.isPurePriorityGrantLeaf then .seq postStep leaf
    else .seq leaf postStep

/-- Ensure a `PendingReplacement` continuation ends with a priority grant
without appending `.finishResolutionChoice` onto a continuation that already grants priority. -/
def PendingReplacement.ensureEndsWithFinishResolutionChoice (pr : PendingReplacement) : PendingReplacement :=
  if pr.endsWithPriorityGrant then pr
  else
    match pr with
    | .finishResolutionChoice => .finishResolutionChoice
    | .seq a b => .seq a b.ensureEndsWithFinishResolutionChoice
    | other => .seq other .finishResolutionChoice

/-- Whether `pr` already contains a deferred `.finishPostStep (.logExpiredPlayFromExile ids _)`
covering `oid`. -/
def PendingReplacement.containsDeferredPlayFromExile (oid : ObjectId) : PendingReplacement → Bool
  | .finishPostStep (.logExpiredPlayFromExile ids _) => ids.contains oid
  | .seq a b => a.containsDeferredPlayFromExile oid || b.containsDeferredPlayFromExile oid
  | _ => false

/-- Record that `p` left the game on any nested `.restorePending`,
`.leavePlayersWhoLost`, `.finishConcede`, or `.concedePlayersLoop`
continuation so `.restorePending` re-runs `redirectPendingAfterLeave`
once the replacement pause finishes (CR 616.1 / 800.4). -/
def PendingReplacement.appendDeparted (p : PlayerId) : PendingReplacement → PendingReplacement
  | .restorePending pend popOuter promptLog dep rw =>
    .restorePending pend popOuter promptLog (if dep.contains p then dep else dep.push p) rw
  | .leavePlayersWhoLost saved popOuter dep rw fromIdx? =>
    .leavePlayersWhoLost saved popOuter (if dep.contains p then dep else dep.push p) rw fromIdx?
  | .finishConcede wasIdle prio wasCombat saved popOuter dep rw fromIdx? =>
    .finishConcede wasIdle prio wasCombat saved popOuter (if dep.contains p then dep else dep.push p) rw fromIdx?
  | .concedePlayersLoop rem wp mid wasIdle prio wasCombat saved popOuter dep rw fromIdx? =>
    .concedePlayersLoop rem wp mid wasIdle prio wasCombat saved popOuter
      (if dep.contains p then dep else dep.push p) rw fromIdx?
  | .seq a b => .seq (a.appendDeparted p) (b.appendDeparted p)
  | other => other

def PendingReplacement.appendDepartedMany (dep : Array PlayerId) (cont : PendingReplacement) :
    PendingReplacement :=
  dep.foldl (fun c p => c.appendDeparted p) cont

/-- Collect any departed players already recorded on a `PendingReplacement` tree. -/
def PendingReplacement.collectDeparted : PendingReplacement → Array PlayerId
  | .restorePending _ _ _ dep _ => dep
  | .leavePlayersWhoLost _ _ dep _ _ => dep
  | .finishConcede _ _ _ _ _ dep _ _ => dep
  | .concedePlayersLoop _ _ _ _ _ _ _ _ dep _ _ => dep
  | .seq a b =>
    b.collectDeparted.foldl (fun acc p => if acc.contains p then acc else acc.push p) a.collectDeparted
  | _ => #[]

/-- Strip recorded `departed` lists to `#[]` across a `PendingReplacement` tree so
checkpoint continuations can be compared modulo post-checkpoint departures. -/
def PendingReplacement.withoutDeparted : PendingReplacement → PendingReplacement
  | .restorePending pend popOuter promptLog _ rw =>
    .restorePending pend popOuter promptLog #[] rw
  | .leavePlayersWhoLost saved popOuter _ rw fromIdx? =>
    .leavePlayersWhoLost saved popOuter #[] rw fromIdx?
  | .finishConcede wasIdle prio wasCombat saved popOuter _ rw fromIdx? =>
    .finishConcede wasIdle prio wasCombat saved popOuter #[] rw fromIdx?
  | .concedePlayersLoop rem wp mid wasIdle prio wasCombat saved popOuter _ rw fromIdx? =>
    .concedePlayersLoop rem wp mid wasIdle prio wasCombat saved popOuter #[] rw fromIdx?
  | .seq a b => .seq a.withoutDeparted b.withoutDeparted
  | other => other

private def PendingReplacement.toSeqLeaves : PendingReplacement → Array PendingReplacement
  | .seq a b => a.toSeqLeaves ++ b.toSeqLeaves
  | other => #[other]

private def PendingReplacement.ofSeqLeaves? (leaves : Array PendingReplacement) :
    Option PendingReplacement :=
  match leaves[0]? with
  | none => none
  | some first =>
    some ((leaves.extract 1 leaves.size).foldl (fun acc x => .seq acc x) first)

private def PendingReplacement.containsSubtreeBase (targetBase : PendingReplacement) :
    PendingReplacement → Bool
  | .seq a b =>
    (PendingReplacement.seq a b).withoutDeparted == targetBase ||
      PendingReplacement.containsSubtreeBase targetBase a ||
      PendingReplacement.containsSubtreeBase targetBase b
  | other => other.withoutDeparted == targetBase

/-- Whether `cur` contains `target` modulo `withoutDeparted` (including across
`.seq` reassociation such as `ensureEndsWithFinishResolutionChoice`). -/
def PendingReplacement.containsModDeparted (target : PendingReplacement)
    (cur : PendingReplacement) : Bool :=
  let targetBase := target.withoutDeparted
  if PendingReplacement.containsSubtreeBase targetBase cur then true
  else
    let tLeaves := targetBase.toSeqLeaves
    if tLeaves.size <= 1 then false
    else
      let cLeaves := cur.withoutDeparted.toSeqLeaves
      if cLeaves.size < tLeaves.size then false
      else
        Id.run do
          for i in [0 : cLeaves.size - tLeaves.size + 1] do
            if cLeaves.extract i (i + tLeaves.size) == tLeaves then
              return true
          return false

private def PendingReplacement.dropSubtreeBase (targetBase : PendingReplacement) :
    PendingReplacement → Option PendingReplacement
  | .seq a b =>
    if (PendingReplacement.seq a b).withoutDeparted == targetBase then none
    else
      match PendingReplacement.dropSubtreeBase targetBase a,
            PendingReplacement.dropSubtreeBase targetBase b with
      | none, none => none
      | some a', none => some a'
      | none, some b' => some b'
      | some a', some b' => some (.seq a' b')
  | other =>
    if other.withoutDeparted == targetBase then none else some other

/-- Remove occurrences of `target` modulo `withoutDeparted` from `cur`. -/
def PendingReplacement.dropTargetModDeparted (target : PendingReplacement)
    (cur : PendingReplacement) : Option PendingReplacement :=
  let targetBase := target.withoutDeparted
  if PendingReplacement.containsSubtreeBase targetBase cur then
    PendingReplacement.dropSubtreeBase targetBase cur
  else
    let tLeaves := targetBase.toSeqLeaves
    if tLeaves.size <= 1 then some cur
    else
      let origLeaves := cur.toSeqLeaves
      let baseLeaves := origLeaves.map (·.withoutDeparted)
      if baseLeaves.size < tLeaves.size then some cur
      else
        Id.run do
          let mut out : Array PendingReplacement := #[]
          let mut i : Nat := 0
          while i < origLeaves.size do
            if i + tLeaves.size <= origLeaves.size &&
                baseLeaves.extract i (i + tLeaves.size) == tLeaves then
              i := i + tLeaves.size
            else
              out := out.push origLeaves[i]!
              i := i + 1
          return PendingReplacement.ofSeqLeaves? out

namespace EngineChange
@[inline] def pendingDrawAfterScry (v : Option (PlayerId × Nat)) : EngineChange := .continuation (.pendingDrawAfterScry v)
@[inline] def recentTokenIds (v : Array ObjectId) : EngineChange := .continuation (.recentTokenIds v)
@[inline] def pendingFreeCopies (v : Option (PlayerId × Array ObjectId × Nat × Nat)) : EngineChange := .continuation (.pendingFreeCopies v)
@[inline] def pendingMayCastFromExile (v : Option (PlayerId × Array ObjectId × Nat)) : EngineChange := .continuation (.pendingMayCastFromExile v)
@[inline] def postCastCleanup (v : Option PostCastCleanup) : EngineChange := .continuation (.postCastCleanup v)
@[inline] def surveilReturnMvAtMost (v : Option Nat) : EngineChange := .continuation (.surveilReturnMvAtMost v)
@[inline] def pendingReplacement (v : Option PendingReplacement) : EngineChange := .continuation (.pendingReplacement v)
@[inline] def pushOuterPendingReplacement (v : PendingReplacement) : EngineChange := .continuation (.pushOuterPendingReplacement v)
@[inline] def popOuterPendingReplacement : EngineChange := .continuation .popOuterPendingReplacement
@[inline] def conniveSource (v : Option ObjectId) : EngineChange := .continuation (.conniveSource v)
@[inline] def thirstDiscardsLeft (v : Nat) : EngineChange := .continuation (.thirstDiscardsLeft v)
@[inline] def thirstDiscardType (v : CardType) : EngineChange := .continuation (.thirstDiscardType v)
@[inline] def pendingDiscardsLeft (v : Nat) : EngineChange := .continuation (.pendingDiscardsLeft v)
@[inline] def discardCountPerPlayer (v : Nat) : EngineChange := .continuation (.discardCountPerPlayer v)
@[inline] def discardBatch (v : Option (BatchId × Nat)) : EngineChange := .continuation (.discardBatch v)
@[inline] def stagedAttackTokenBatches (v : Array ProposedTokenBatch) : EngineChange := .continuation (.stagedAttackTokenBatches v)
@[inline] def stashedCause (v : Option EventCause) : EngineChange := .continuation (.stashedCause v)
@[inline] def resolvingSpell (v : Option ObjectId) : EngineChange := .continuation (.resolvingSpell v)
@[inline] def resolvingAbility (v : Option ObjectId) : EngineChange := .continuation (.resolvingAbility v)
@[inline] def resolvingDivision (v : Array Nat) : EngineChange := .continuation (.resolvingDivision v)
@[inline] def resolvingSkippedSlots (v : Array Nat) : EngineChange := .continuation (.resolvingSkippedSlots v)
@[inline] def afterRandom (v : AfterRandom) : EngineChange := .continuation (.afterRandom v)
@[inline] def resolutionFinish (v : Option ResolutionFinish) : EngineChange := .continuation (.resolutionFinish v)
@[inline] def pendingResolvedEvent (v : Option (EventObject × PlayerId × EventCause)) : EngineChange := .continuation (.pendingResolvedEvent v)
@[inline] def stepEnv (v : Array (VarId × StepOutcome)) : EngineChange := .continuation (.stepEnv v)
@[inline] def bindStepOutcome (v : VarId) (o : StepOutcome) : EngineChange := .continuation (.bindStepOutcome v o)
@[inline] def interpWait? (v : Option InterpState) : EngineChange := .continuation (.interpWait? v)
end EngineChange

namespace GameEvent

/-- Turn number on which `e` occurred. -/
@[inline] def turn : GameEvent → Nat
  | .rules t .. | .engine t .. => t

/-- Batch identifier of `e` (`none` for unstamped engine changes or unbatched/proposed events). -/
@[inline] def batch : GameEvent → Option BatchId
  | .rules _ _ _ b | .engine _ _ b => b

/-- Return `e` stamped with `b`. -/
@[inline] def withBatch (e : GameEvent) (b : BatchId) : GameEvent :=
  match e with
  | .rules t r c _ => .rules t r c (some b)
  | .engine t c _ => .engine t c (some b)

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
    (skippedOptionalSlots : Array Nat := #[])
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.cast (.targeted obj targets division skippedOptionalSlots))
    (cause.getD (.gameRule .spellCast))

/-- `player` cast `spell` from `fromZone` (CR 601.2i). -/
def spellCast (turn : Nat) (player : PlayerId) (spell : EventObject) (fromZone : Zone)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.cast (.spellCast spell player fromZone))
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

/-- `obj` was removed from the stack on resolution because its intervening “if” condition failed or all its targets were illegal (CR 603.4 / 608.2a / 608.2b). -/
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
    (forObject : Option ObjectId := none)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.manaSpent player units forObject))
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

/-- `player` got or lost `kind` counters (CR 122.1). -/
def playerCounters (turn : Nat) (player : PlayerId) (kind : CounterKind)
    (delta : CounterDelta) (byPlayer : Option PlayerId := none)
    (cause : EventCause) : GameEvent :=
  rules turn (.permanent (.counters (.player player) kind delta byPlayer)) cause

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
def effectExpired (turn : Nat) (id : EffectId) (spec : Option ContinuousEffectSpec := none)
    (cause : EventCause) : GameEvent :=
  rules turn (.continuousEffect (.expired id spec)) cause

/-- Delayed triggered ability `dt` was created (CR 603.7). -/
def delayedTriggerCreated (turn : Nat) (dt : DelayedTrigger)
    (cause : EventCause := dt.cause) (batch : Option BatchId := none) : GameEvent :=
  rules turn (.delayedTrigger (.created dt)) cause batch

/-- One-shot delayed triggered ability `dt` triggered and was consumed (CR 603.7b). -/
def delayedTriggerConsumed (turn : Nat) (dt : DelayedTrigger)
    (cause : EventCause := .gameRule .triggeredAbility) (batch : Option BatchId := none) : GameEvent :=
  rules turn (.delayedTrigger (.consumed dt)) cause batch

/-- Duration-scoped delayed triggered ability `dt` expired (CR 603.7b / 514.2 / 800.4i). -/
def delayedTriggerExpired (turn : Nat) (dt : DelayedTrigger)
    (cause : EventCause) (batch : Option BatchId := none) : GameEvent :=
  rules turn (.delayedTrigger (.expired dt)) cause batch

/-- A creature moved from the battlefield to a graveyard (CR 700.4). -/
def isCreatureToGraveyard (e : GameEvent) : Bool :=
  match e.change with
  | .rules (.zone (.moved before _ .battlefield (.graveyard _) _ _ _ _)) =>
    !before.phasedOut && before.creature
  | _ => false

/-- A permanent moved from the battlefield to a graveyard. -/
def isPermanentToGraveyard (e : GameEvent) : Bool :=
  match e.change with
  | .rules (.zone (.moved before _ .battlefield (.graveyard _) _ _ _ _)) => !before.phasedOut
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
  | .rules (.zone (.moved _ after fromZone .battlefield _ _ _ _)) =>
    fromZone != .battlefield && !after.phasedOut
  | .rules (.zone (.created obj _)) => obj.zone == .battlefield && !obj.phasedOut
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
    | .rules (.zone (.created object _)) =>
      object.zone == .battlefield && !object.phasedOut && object.token
    | _ => false
  | .wouldPutCounter =>
    match e.change with
    | .rules (.permanent (.counters (.object object) _ (.put n) _)) =>
      !object.phasedOut && n > 0
    | .rules (.permanent (.counters (.player _) _ (.put n) _)) => n > 0
    | .rules (.zone (.moved _ after _ .battlefield _ _ entersWith _)) =>
      !after.phasedOut && entersWith.any (fun (_, n) => n > 0)
    | .rules (.zone (.created object _)) =>
      object.zone == .battlefield && !object.phasedOut && !object.counters.isEmpty &&
        object.counters.any (fun (_, n) => n > 0)
    | _ => false
  | .wouldUntap =>
    match e.change with
    | .rules (.permanent (.untapped _)) => true
    | _ => false

/-- True when player `p` satisfies `pf` relative to `listener` and `isTeammate`. -/
@[inline] private def matchesEventPlayer (listener : PlayerId) (isTeammate : PlayerId → Bool)
    (pf : PlayerFilter) (p : PlayerId) : Bool :=
  match pf.relation with
  | .you => p == listener
  | .opponent => p != listener && !isTeammate p
  | .teammate => isTeammate p
  | .anyPlayer => true

/-- True when `z` satisfies `spec` relative to `listener` and `isTeammate`. -/
private def matchesZoneEndpoint (listener : PlayerId) (isTeammate : PlayerId → Bool)
    (spec : ZoneEndpointSpec) (z : Zone) : Bool :=
  let (zk, owner?) : ZoneKind × Option PlayerId :=
    match z with
    | .library p => (.library, some p)
    | .hand p => (.hand, some p)
    | .battlefield => (.battlefield, none)
    | .graveyard p => (.graveyard, some p)
    | .stack => (.stack, none)
    | .exile => (.exile, none)
    | .command => (.command, none)
    | .ante => (.ante, none)
    | .outside p => (.outside, some p)
  match spec with
  | .any => true
  | .notIn k => zk != k
  | .inZones zs =>
    zs.zones.contains zk &&
      match zs.owner with
      | .any => true
      | .matching pf => owner?.any (matchesEventPlayer listener isTeammate pf)
      | .ofPlayer .you => owner? == some listener
      | .ofPlayer _ => true

/-- Evaluate a static `ObjectPred` against an `EventObject` snapshot (CR 603.10a). -/
@[noinline] private partial def evalEventObjPred (listener : PlayerId) (sourceId : Option ObjectId)
    (isTeammate : PlayerId → Bool) (attachedHostId? : Option ObjectId)
    (o : EventObject) : ObjectPred → Bool
  | .all ps => ps.all (evalEventObjPred listener sourceId isTeammate attachedHostId? o)
  | .any ps => ps.any (evalEventObjPred listener sourceId isTeammate attachedHostId? o)
  | .not p => !(evalEventObjPred listener sourceId isTeammate attachedHostId? o p)
  | .sameAs .this => sourceId.isSome && o.id == sourceId
  | .sameAs .attachedHost =>
    match attachedHostId? with
    | some hid => o.id == some hid
    | none => true
  | .sameAs _ => true
  | .otherThan .this =>
    match sourceId with
    | some sid => o.id.any (· != sid)
    | none => true
  | .otherThan _ => true
  | .hasType ty => o.types.contains ty
  | .hasSupertype st => o.supertypes.contains st
  | .hasSubtype (.literal sub) => o.hasSubtype sub
  | .hasSubtype _ => !o.subtypes.isEmpty
  | .hasColor (.literal col) => o.colors.contains col
  | .hasColor _ => !o.colors.isColorless
  | .colorCount op n => op.eval (Int.ofNat o.colors.count) (Int.ofNat n)
  | .named _ => true
  | .hasKeyword kw => KeywordAbility.hasTag o.keywords kw
  | .stat .power op (.const n) => o.power.any (op.eval · n)
  | .stat .toughness op (.const n) => o.toughness.any (op.eval · n)
  | .stat .manaValue op (.const n) => op.eval (Int.ofNat o.manaValue) n
  | .stat _ _ _ => true
  | .statParity _ _ => true
  | .isToken v => o.token == v
  | .isFaceDown v => o.faceDown == v
  | .isCopy v => o.isCopy == v
  | .isCommander => o.isCommander
  | .isKind .card => !o.token && !o.isCopy && !o.types.isEmpty
  | .isKind .permanentCard => !o.token && !o.isCopy && o.types.any CardType.isPermanentType
  | .isKind .spell => !o.types.isEmpty
  | .tapped v => o.tapped == v
  | .phasedOut v => o.phasedOut == v
  | .combatRole .attacking => o.attacking
  | .combatRole .blocking => o.blocking
  | .combatRole _ => true
  | .hasDesignation _ => true
  | .counterCount k? op (.const n) =>
    let cnt := match k? with | some k => o.counters.count k | none => o.counters.foldl (fun a (_, c) => a + c) 0
    op.eval (Int.ofNat cnt) n
  | .counterCount _ _ _ => true
  | .controlledBy pf =>
    o.controller.any (matchesEventPlayer listener isTeammate pf)
  | .ownedBy pf => matchesEventPlayer listener isTeammate pf o.owner
  | .attachedTo _ | .hasAttachment _ | .targets _ | .shares _ _
  | .wasCast | .castFrom _ | .enteredThisTurn | .attackedThisTurn
  | .dealtDamageThisTurn .. | .wasDealtDamageThisTurn | .receivedCounterThisTurn ..
  | .putIntoGraveyardFromBattlefieldThisTurn | .chosenAnchorIs _ => true

@[noinline] private def matchesPatternZone (ze : ZoneEvent) (cause? : Option EventCause)
    (listener : PlayerId) (sourceId : Option ObjectId) (pat : TriggerPattern)
    (limit : TriggerLimit) (isTeammate : PlayerId → Bool)
    (attachedHostId? : Option ObjectId) : Bool :=
  let objMatches (o : EventObject) (pred : ObjectPred) : Bool :=
    evalEventObjPred listener sourceId isTeammate attachedHostId? o pred
  let playerMatches (pf : PlayerFilter) (p : PlayerId) : Bool :=
    matchesEventPlayer listener isTeammate pf p
  match ze with
  | .moved before after fromZone toZone verb actor entersWith _ =>
    match pat with
    | .drawCard who exceptFirst =>
      match verb, actor with
      | .draw nth isFirst, some p =>
        playerMatches who p &&
          (!exceptFirst || !isFirst) &&
          (match limit with | .nthEachTurn k => nth == k | _ => true)
      | _, _ => false
    | .discard who cardPred mustBeCycle =>
      match fromZone, verb with
      | .hand p, .discard =>
        playerMatches who p && toZone != .hand p &&
          (!mustBeCycle || match cause? with | some (.costPayment .cycle _ _) => true | _ => false) &&
          (objMatches before cardPred || objMatches after cardPred)
      | _, _ => false
    | .sacrifice who subj =>
      match fromZone, verb with
      | .battlefield, .sacrifice =>
        let p := actor.getD (before.controller.getD before.owner)
        !before.phasedOut && toZone != .battlefield && playerMatches who p && objMatches before subj
      | _, _ => false
    | .zoneChange subj fromZ toZ verb? actor? =>
      let verbOk := verb?.all (· == verb)
      let actorOk := actor?.all (fun pf => actor.any (playerMatches pf))
      let zOk :=
        matchesZoneEndpoint listener isTeammate fromZ fromZone &&
          matchesZoneEndpoint listener isTeammate toZ toZone
      if !verbOk || !actorOk || !zOk then false
      else if toZone == .battlefield && fromZone != .battlefield then
        !after.phasedOut &&
          (objMatches after subj ||
            (subj == .sameAs .this && objMatches before subj))
      else if pat.usesLookBack then
        (fromZone != .battlefield || !before.phasedOut) && objMatches before subj
      else if (match toZone with | .graveyard _ => true | _ => false) then
        objMatches after subj
      else
        objMatches before subj
    | .putCounters putter? kind? subj =>
      if toZone != .battlefield || fromZone == .battlefield || after.phasedOut then false
      else
        let p := actor.orElse (fun _ => after.controller)
        let putterOk := putter?.all (fun pf => p.any (playerMatches pf))
        let ctrOk :=
          match kind? with
          | some k => entersWith.count k > 0
          | none => entersWith.any (fun (_, n) => n > 0)
        putterOk && ctrOk &&
          (objMatches after subj || (subj == .sameAs .this && objMatches before subj))
    | .spellCountered spellPred =>
      fromZone == .stack && verb == .counter && objMatches before spellPred
    | _ => false
  | .created object controller =>
    if object.zone != .battlefield || object.phasedOut then false
    else
      let enterCtrl := object.controller.getD controller
      let objWithCtrl := { object with controller := some enterCtrl }
      match pat with
      | .createTokens who tokenPred =>
        object.token && playerMatches who controller && objMatches objWithCtrl tokenPred
      | .zoneChange subj fromZ toZ none none =>
        matchesZoneEndpoint listener isTeammate fromZ .stack &&
          matchesZoneEndpoint listener isTeammate toZ .battlefield &&
          objMatches objWithCtrl subj
      | .putCounters putter? kind? subj =>
        let putterOk := putter?.all (fun pf => playerMatches pf enterCtrl)
        let ctrOk :=
          match kind? with
          | some k => object.counters.count k > 0
          | none => object.counters.any (fun (_, n) => n > 0)
        putterOk && ctrOk && objMatches objWithCtrl subj
      | _ => false
  | .ceasedToExist before =>
    if before.zone != .battlefield || before.phasedOut then false
    else
      match pat with
      | .zoneChange subj fromZ toZ none none =>
        matchesZoneEndpoint listener isTeammate fromZ .battlefield &&
          matchesZoneEndpoint listener isTeammate toZ .exile &&
          objMatches before subj
      | _ => false

@[noinline] private def matchesPatternDamage (de : DamageEvent)
    (listener : PlayerId) (sourceId : Option ObjectId) (pat : TriggerPattern)
    (isTeammate : PlayerId → Bool) (attachedHostId? : Option ObjectId)
    (isYourTurn? : Option Bool := none) : Bool :=
  let objMatches (o : EventObject) (pred : ObjectPred) : Bool :=
    evalEventObjPred listener sourceId isTeammate attachedHostId? o pred
  let playerMatches (pf : PlayerFilter) (p : PlayerId) : Bool :=
    matchesEventPlayer listener isTeammate pf p
  match de, pat with
  | .dealt pkts, .damageDealt srcPred recipFilter combatOnly noncombatOnly onlyYourTurn =>
    (!onlyYourTurn || isYourTurn? == some true) &&
      pkts.any fun pkt =>
        pkt.amount > 0 &&
          (!combatOnly || pkt.combat) &&
          (!noncombatOnly || !pkt.combat) &&
          (srcPred == .anyObject ||
            (sourceId.isNone && srcPred == .sameAs .this) ||
            (pkt.source.id.isNone && srcPred == .sameAs .this) ||
            objMatches pkt.source srcPred) &&
          match recipFilter, pkt.recipient with
          | .any, _ => true
          | .player pf, .player p => playerMatches pf p
          | .object f, .permanent o | .object f, .battle o => objMatches o f.pred
          | .playerOrObject pf _, .player p => playerMatches pf p
          | .playerOrObject _ f, .permanent o | .playerOrObject _ f, .battle o => objMatches o f.pred
          | _, _ => false
  | _, _ => false

@[noinline] private def matchesPatternCast (ce : CastEvent) (cause? : Option EventCause)
    (listener : PlayerId) (sourceId : Option ObjectId) (pat : TriggerPattern)
    (limit : TriggerLimit) (isTeammate : PlayerId → Bool)
    (attachedHostId? : Option ObjectId)
    (castOrdinal? : Option Nat := none)
    (manaSpentOk? : Option Bool := none)
    (targetsOk? : Option Bool := none)
    (targetingSourceIsAbility? : Option Bool := none) : Bool :=
  let objMatches (o : EventObject) (pred : ObjectPred) : Bool :=
    evalEventObjPred listener sourceId isTeammate attachedHostId? o pred
  let playerMatches (pf : PlayerFilter) (p : PlayerId) : Bool :=
    matchesEventPlayer listener isTeammate pf p
  match ce, pat with
  | .spellCast spell p fromZone,
      .castSpell caster spellPred fromZ? manaSpent? mustBePrepared nthFilter? targets? =>
    let fzOk := fromZ?.all (fun zk => matchesZoneEndpoint listener isTeammate (.inZones { zones := #[zk], owner := .any }) fromZone)
    let manaOk := manaSpent?.all (fun _ => manaSpentOk? == some true)
    let prepOk := !mustBePrepared || (spell.isCopy && fromZone == .exile)
    let effNth? :=
      nthFilter?.orElse fun _ =>
        match limit with | .nthEachTurn n => some n | _ => none
    let nthOk := effNth?.all (fun n => castOrdinal? == some n)
    let tgtOk := targets?.all (fun _ => targetsOk? == some true)
    let spOk :=
      (sourceId.isNone && spellPred == .sameAs .this) || objMatches spell spellPred
    playerMatches caster p && fzOk && manaOk && prepOk && nthOk && tgtOk && spOk
  | .abilityActivated _ src p kind, .activateAbility activator srcPred actKind =>
    let kindOk :=
      match actKind, kind with
      | .any, _ => true
      | .loyalty minRem, .nonMana (some k) .. =>
        let removed := if k < 0 then (-k).toNat else 0
        removed ≥ minRem
      | .manaAbility, .mana .. => true
      | .nonMana, .nonMana .. => true
      | _, _ => false
    playerMatches activator p && kindOk && objMatches src srcPred
  | .targeted _ targets _ _, .becomesTarget subj byCtrl srcKind =>
    let kindOk :=
      match srcKind with
      | .spellOrAbility => true
      | .spell => targetingSourceIsAbility? == some false
      | .ability => targetingSourceIsAbility? == some true
    let causeOk :=
      match cause? with
      | some (.costPayment _ p _) | some (.oneShotEffect _ _ (some p)) => playerMatches byCtrl p
      | _ => true
    kindOk && causeOk &&
      match subj with
      | .playerOrPermanent =>
        targets.any fun | .permanent _ | .player _ => true | _ => false
      | .object (.sameAs .this) =>
        sourceId.isSome && targets.any fun | .permanent oid => some oid == sourceId | _ => false
      | .object _ =>
        targets.any fun | .permanent _ => true | _ => false
  | _, _ => false

@[noinline] private def matchesPatternCombat (ce : CombatEvent)
    (listener : PlayerId) (sourceId : Option ObjectId) (pat : TriggerPattern)
    (isTeammate : PlayerId → Bool) (attachedHostId? : Option ObjectId) : Bool :=
  let objMatches (o : EventObject) (pred : ObjectPred) : Bool :=
    evalEventObjPred listener sourceId isTeammate attachedHostId? o pred
  let playerMatches (pf : PlayerFilter) (p : PlayerId) : Bool :=
    matchesEventPlayer listener isTeammate pf p
  let targetMatches (tf : AttackTargetFilter) (t : AttackTarget) : Bool :=
    match tf, t with
    | .any, _ => true
    | .player pf, .player d => playerMatches pf d
    | .playerOrPlaneswalker pf, .player d => playerMatches pf d
    | .playerOrPlaneswalker _, .planeswalker _ => true
    | _, _ => false
  match ce, pat with
  | .attackersDeclared attackingPlayer decls, .attacks attPred tgtFilter alone minAtk minPower? _ =>
    let attackerTeamOk :=
      match tgtFilter with
      | .player pf | .playerOrPlaneswalker pf =>
        if pf.relation == .you then playerMatches .opponent attackingPlayer else true
      | .any => true
    if !attackerTeamOk then false
    else
    let matched := decls.filter fun (a, tgt) => objMatches a attPred && targetMatches tgtFilter tgt
    if matched.size < minAtk then false
    else if alone then
      match tgtFilter with
      | .player _ =>
        matched.any fun (a, tgt) =>
          match tgt with
          | .player d => !decls.any fun (a', tgt') => a'.id != a.id && tgt' == .player d
          | _ => false
      | _ => decls.size == 1 && matched.size == 1
    else
      match minPower? with
      | some minP =>
        let tot := matched.foldl (fun acc (a, _) => acc + a.power.getD 0) 0
        tot ≥ minP
      | none =>
        if minAtk ≥ 2 then
          match tgtFilter with
          | .player _ =>
            matched.any fun (_, tgt) =>
              match tgt with
              | .player d => (matched.filter fun (_, t') => t' == .player d).size ≥ minAtk
              | _ => false
          | _ => true
        else true
  | .blockersDeclared _ decls, .blocks blkPred =>
    decls.any fun (b, _) => objMatches b blkPred
  | .becameBlocked attacker _, .becomesBlocked attPred =>
    objMatches attacker attPred
  | _, _ => false

@[noinline] private def matchesPatternPermanent (pe : PermanentEvent) (cause? : Option EventCause)
    (listener : PlayerId) (sourceId : Option ObjectId) (pat : TriggerPattern)
    (isTeammate : PlayerId → Bool) (attachedHostId? : Option ObjectId) : Bool :=
  let objMatches (o : EventObject) (pred : ObjectPred) : Bool :=
    evalEventObjPred listener sourceId isTeammate attachedHostId? o pred
  let playerMatches (pf : PlayerFilter) (p : PlayerId) : Bool :=
    matchesEventPlayer listener isTeammate pf p
  match pe, pat with
  | .tapped object during, .becomesTapped subj onlyYourTurn _ costKind? =>
    !object.phasedOut &&
      (!onlyYourTurn || during) &&
      costKind?.all (fun ck =>
        match cause? with | some (.costPayment k _ _) => k == ck | _ => false) &&
      objMatches object subj
  | .untapped object, .becomesUntapped subj =>
    !object.phasedOut && objMatches object subj
  | .phasedOut object _, .phasesOut subj =>
    objMatches object subj
  | .unattached att _, .becomesUnattached attPred _ =>
    objMatches att attPred
  | .counters (.object object) kind (.put n) actor, .putCounters putter? kind? subj =>
    object.zone == .battlefield && !object.phasedOut && n > 0 &&
      kind?.all (· == kind) &&
      putter?.all (fun pf => actor.any (playerMatches pf)) &&
      objMatches object subj
  | _, _ => false

/-- Pure single-`GameEvent` matcher against a `TriggerPattern` (CR 603.2).
Constraints that depend on full-game history or stack state (`manaSpent?`,
`nthOfFilter?` / `TriggerLimit.nthEachTurn` on casts, `targets?`,
`becomesTarget` source kind, `onlyYourTurn` damage) require the corresponding
optional context arguments and return `false` when unsatisfied or omitted;
full game-state trigger matching runs through `Game.matchTriggers`. -/
partial def matchesTriggerPattern (e : GameEvent) (listener : PlayerId)
    (sourceId : Option ObjectId := none) (pat : TriggerPattern)
    (limit : TriggerLimit := .unlimited)
    (isTeammate : PlayerId → Bool := fun _ => false)
    (attachedHostId? : Option ObjectId := none)
    (castOrdinal? : Option Nat := none)
    (manaSpentOk? : Option Bool := none)
    (targetsOk? : Option Bool := none)
    (targetingSourceIsAbility? : Option Bool := none)
    (isYourTurn? : Option Bool := none) : Bool :=
  match pat with
  | .whenCond inner _ =>
    matchesTriggerPattern e listener sourceId inner limit isTeammate attachedHostId?
      castOrdinal? manaSpentOk? targetsOk? targetingSourceIsAbility? isYourTurn?
  | .or l r =>
    matchesTriggerPattern e listener sourceId l limit isTeammate attachedHostId?
      castOrdinal? manaSpentOk? targetsOk? targetingSourceIsAbility? isYourTurn? ||
      matchesTriggerPattern e listener sourceId r limit isTeammate attachedHostId?
        castOrdinal? manaSpentOk? targetsOk? targetingSourceIsAbility? isYourTurn?
  | _ =>
    let playerMatches (pf : PlayerFilter) (p : PlayerId) : Bool :=
      matchesEventPlayer listener isTeammate pf p
    let objMatches (o : EventObject) (pred : ObjectPred) : Bool :=
      evalEventObjPred listener sourceId isTeammate attachedHostId? o pred
    match e.change with
    | .engine _ => false
    | .rules r =>
      match r with
      | .zone ze =>
        matchesPatternZone ze e.cause? listener sourceId pat limit isTeammate attachedHostId?
      | .damage de =>
        matchesPatternDamage de listener sourceId pat isTeammate attachedHostId? isYourTurn?
      | .cast ce =>
        matchesPatternCast ce e.cause? listener sourceId pat limit isTeammate attachedHostId?
          castOrdinal? manaSpentOk? targetsOk? targetingSourceIsAbility?
      | .combat ce =>
        matchesPatternCombat ce listener sourceId pat isTeammate attachedHostId?
      | .permanent pe =>
        matchesPatternPermanent pe e.cause? listener sourceId pat isTeammate attachedHostId?
      | .life le =>
        match le, pat with
        | .gained p amount, .gainLife who => amount > 0 && playerMatches who p
        | .lost p amount _ _, .loseLife who => amount > 0 && playerMatches who p
        | _, _ => false
      | .player pe =>
        match pe, pat with
        | .scried p _ _ _ asked, .playerAction who .scry => asked > 0 && playerMatches who p
        | .surveilled p _ _ _ asked, .playerAction who .surveil => asked > 0 && playerMatches who p
        | .proliferated p _ _, .playerAction who .proliferate => playerMatches who p
        | .ringTempted p _ _, .playerAction who .ringTempts => playerMatches who p
        | .ringTempted p (some _) _, .playerAction who .chooseRingBearer => playerMatches who p
        | .manaAdded p units, .playerAction who .manaAdded => !units.isEmpty && playerMatches who p
        | .lost p _, .playerAction who .losesGame => playerMatches who p
        | _, _ => false
      | .stackObject se =>
        match se, pat with
        | .resolved obj nth _ _, .stackObjectResolves pred finalSagaOnly =>
          (!finalSagaOnly || (nth == 0 && obj.types.isEmpty && obj.hasSubtype .saga)) &&
            objMatches obj pred
        | _, _ => false
      | .turn (.stepBegan step active) =>
        match pat with
        | .stepBegins s ownerSpec =>
          s == step &&
            match ownerSpec with
            | .player pf =>
              match pf.relation with
              | .you => active == listener || isTeammate active
              | _ => playerMatches pf active
            | .controllerOf _ => active == listener
        | _ => false
      | .triggerQueue (.triggered src _ _ _) =>
        match pat with
        | .abilityTriggers srcPred => objMatches src srcPred
        | _ => false
      | _ => false

/-- Counters put on objects in `e` (CR 122.1 / 122.6), including counters
placed as an object enters the battlefield via `ZoneEvent.moved.entersWith`
or `ZoneEvent.created`. -/
def countersPutInEvent (e : GameEvent) : Array (EventObject × CounterKind × Nat × Option PlayerId) :=
  match e.change with
  | .rules (.permanent (.counters (.object o) kind (.put n) actor)) =>
    if o.zone == .battlefield && !o.phasedOut && n > 0 then #[(o, kind, n, actor)] else #[]
  | .rules (.zone (.moved _ after fromZone .battlefield _ actor entersWith _)) =>
    if fromZone == .battlefield || after.phasedOut then #[]
    else
      entersWith.foldl (fun acc (kind, n) =>
        if n > 0 then acc.push (after, kind, n, actor.orElse (fun _ => after.controller)) else acc) #[]
  | .rules (.zone (.created object controller)) =>
    if object.zone != .battlefield || object.phasedOut then #[]
    else
      let enterCtrl := object.controller.getD controller
      object.counters.foldl (fun acc (kind, n) =>
        if n > 0 then acc.push (object, kind, n, some enterCtrl) else acc) #[]
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
      | .rules (.zone (.moved _ after fromZone .battlefield _ _ _ _)) =>
        fromZone != .battlefield && !after.phasedOut && after.controller == some p && after.artifact
      | .rules (.zone (.created object q)) =>
        object.zone == .battlefield && !object.phasedOut && (object.controller.getD q) == p && object.artifact
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
      | .rules (.zone (.moved _ after fromZone .battlefield _ _ _ _)) =>
        fromZone != .battlefield && !after.phasedOut && after.controller == some p && after.hasSubtype subtype
      | .rules (.zone (.created object q)) =>
        object.zone == .battlefield && !object.phasedOut && (object.controller.getD q) == p && object.hasSubtype subtype
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
        pkts.any (fun pkt => !pkt.combat && pkt.amount > 0 && pkt.recipient == .player p)
      | .rules (.life (.lost q amt true false)) => q == p && amt > 0
      | _ => false

/-- Index of the `CastEvent.spellCast` event for `spell`, `0` when `events`
identifies `spell` as a non-spell stack ability, uncast stack copy, or
battlefield permanent (CR 400.7 / 707.10), or `events.size` when `spell` is a
spell that has not yet finished casting (CR 601.2h–i). -/
def castEventBound (events : Array GameEvent) (spell : ObjectId) : Nat :=
  match events.findIdx? (fun e =>
    match e.change with
    | .rules (.cast (.spellCast s ..)) => s.id == some spell
    | _ => false) with
  | some idx => idx
  | none =>
    let hasSpellProposal :=
      events.any fun e =>
        match e.change with
        | .rules (.cast (.proposed obj ..)) => obj == spell
        | .rules (.zone (.moved _ after _ .stack .cast ..)) => after.id == some spell
        | _ => false
    let isNonSpellOrBattlefieldPerm :=
      events.any fun e =>
        match e.change with
        | .rules (.cast (.abilityActivated ab ..)) => ab == spell
        | .rules (.triggerQueue (.putOnStack stObj ..)) => stObj == spell
        | .rules (.stackObject (.copied _ copy _)) => copy.id == some spell
        | .engine (.materializeObject obj _) =>
          obj.id == spell &&
            (obj.abilityEffect.isSome || obj.triggeredAbility.isSome || obj.zone == .battlefield)
        | .rules (.zone (.moved _ after _ .battlefield ..)) =>
          after.id == some spell
        | .rules (.zone (.created eo _)) =>
          eo.zone == .battlefield && eo.id == some spell
        | _ => false
    if !hasSpellProposal && isNonSpellOrBattlefieldPerm then 0 else events.size

/-- Mana recorded for `spell` when it was cast, if the log has that payment. -/
def manaSpentOn (events : Array GameEvent) (spell : ObjectId) : Nat :=
  let preCast := events.extract 0 (castEventBound events spell)
  preCast.foldl (fun n e =>
    match e.change, e.cause? with
    | .rules (.player (.manaSpent _ units forObj)), some (.costPayment .mana _ oid?) =>
      if forObj == some spell || oid? == some spell then max n units.size else n
    | .rules (.player (.manaSpent _ units forObj)), _ =>
      if forObj == some spell then max n units.size else n
    | _, _ => n) 0

/-- Whether `srcId` was recorded as a Treasure permanent at its latest battlefield snapshot, departure, activation, or trigger (CR 109.2 / 608.2h / 702.26b). -/
def isTreasureSourceInLog (events : Array GameEvent) (srcId : ObjectId) : Bool := Id.run do
  let mut phasedOutFallback : Option Bool := none
  let mut i := events.size
  while i > 0 do
    i := i - 1
    match events[i]!.change with
    | .rules (.permanent (.phasedIn snap _)) =>
      if snap.id == some srcId then
        return phasedOutFallback.getD false
    | .rules (.permanent (.phasedOut snap _)) =>
      if snap.zone == .battlefield && snap.id == some srcId then
        if !snap.phasedOut then
          return snap.subtypes.contains .treasure
        else
          phasedOutFallback := phasedOutFallback.orElse (fun _ => some (snap.subtypes.contains .treasure))
    | .rules (.zone (.moved before after fromZ toZ ..)) =>
      if fromZ == .battlefield && before.id == some srcId then
        if !before.phasedOut then
          return before.subtypes.contains .treasure
        else
          phasedOutFallback := phasedOutFallback.orElse (fun _ => some (before.subtypes.contains .treasure))
      if toZ == .battlefield && after.zone == .battlefield && after.id == some srcId then
        if !after.phasedOut then
          return after.subtypes.contains .treasure
        else
          phasedOutFallback := phasedOutFallback.orElse (fun _ => some (after.subtypes.contains .treasure))
    | .rules (.zone (.ceasedToExist snap)) =>
      if snap.zone == .battlefield && snap.id == some srcId then
        if !snap.phasedOut then
          return snap.subtypes.contains .treasure
        else
          phasedOutFallback := phasedOutFallback.orElse (fun _ => some (snap.subtypes.contains .treasure))
    | .rules (.zone (.created snap _)) =>
      if snap.zone == .battlefield && snap.id == some srcId then
        if !snap.phasedOut then
          return snap.subtypes.contains .treasure
        else
          phasedOutFallback := phasedOutFallback.orElse (fun _ => some (snap.subtypes.contains .treasure))
    | .rules (.cast (.abilityActivated id snap _ _)) =>
      if snap.zone == .battlefield && (id == srcId || snap.id == some srcId) then
        if !snap.phasedOut then
          return snap.subtypes.contains .treasure
        else
          phasedOutFallback := phasedOutFallback.orElse (fun _ => some (snap.subtypes.contains .treasure))
    | .rules (.triggerQueue (.triggered snap _ _ _)) =>
      if snap.zone == .battlefield && snap.id == some srcId then
        if !snap.phasedOut then
          return snap.subtypes.contains .treasure
        else
          phasedOutFallback := phasedOutFallback.orElse (fun _ => some (snap.subtypes.contains .treasure))
    | .rules (.triggerQueue (.putOnStack _ snap _ spec)) =>
      if snap.zone == .battlefield && (snap.id == some srcId || spec.sourceId == some srcId) then
        if !snap.phasedOut then
          return snap.subtypes.contains .treasure
        else
          phasedOutFallback := phasedOutFallback.orElse (fun _ => some (snap.subtypes.contains .treasure))
    | _ => pure ()
  return phasedOutFallback.getD false

/-- Whether `u` came from a Treasure source (CR 111.10a provenance). -/
private def isTreasureManaUnit (u : ManaUnit) : Bool :=
  u.fromTreasure

/-- Whether mana from a Treasure was spent to cast `spell` (CR 106.6). -/
def treasureManaSpentOn (events : Array GameEvent) (spell : ObjectId) : Bool :=
  let preCast := events.extract 0 (castEventBound events spell)
  preCast.any fun e =>
    match e.change, e.cause? with
    | .rules (.player (.manaSpent _ units forObj)), some (.costPayment .mana _ oid?) =>
      (forObj == some spell || oid? == some spell) &&
        units.any isTreasureManaUnit
    | .rules (.player (.manaSpent _ units forObj)), _ =>
      forObj == some spell && units.any isTreasureManaUnit
    | _, _ => false

/-- Whether mana carrying spell rider `rider` was spent to cast `spell`
(CR 106.6 / 106.12). -/
def riderManaSpentOn (events : Array GameEvent) (spell : ObjectId) (rider : SpellRiderSpec) : Bool :=
  let preCast := events.extract 0 (castEventBound events spell)
  preCast.any fun e =>
    match e.change, e.cause? with
    | .rules (.player (.manaSpent _ units forObj)), some (.costPayment .mana _ oid?) =>
      (forObj == some spell || oid? == some spell) &&
        units.any (·.hasRider rider)
    | .rules (.player (.manaSpent _ units forObj)), _ =>
      forObj == some spell && units.any (·.hasRider rider)
    | _, _ => false

/-- Total number of additional +1/+1 counters granted by mana carrying
`.entersWithPlusOneCounters n` riders spent to cast `spell` (CR 106.6 / 614.1c). -/
def plusOneCounterManaRidersSpentOn (events : Array GameEvent) (spell : ObjectId) : Nat :=
  let preCast := events.extract 0 (castEventBound events spell)
  let countUnit (u : ManaUnit) : Nat :=
    u.allRiders.foldl (fun acc r =>
      match r with
      | .entersWithPlusOneCounters n => acc + n
      | _ => acc) 0
  preCast.foldl (fun acc e =>
    match e.change, e.cause? with
    | .rules (.player (.manaSpent _ units forObj)), some (.costPayment .mana _ oid?) =>
      if forObj == some spell || oid? == some spell then
        acc + units.foldl (fun s u => s + countUnit u) 0
      else acc
    | .rules (.player (.manaSpent _ units forObj)), _ =>
      if forObj == some spell then
        acc + units.foldl (fun s u => s + countUnit u) 0
      else acc
    | _, _ => acc) 0

/-- Whether mana carrying a `.cantBeCountered` spell rider (e.g. Delighted Halfling)
was spent to cast `spell` (CR 106.6 / 106.12). -/
def legendaryManaSpentOn (events : Array GameEvent) (spell : ObjectId) : Bool :=
  riderManaSpentOn events spell .cantBeCountered

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

/-- Cards `p` milled on `turn` (CR 701.17a / 701.17c, including replacement redirects). -/
def milled (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.zone (.moved _ _ (.library owner) toZone .mill _ _ _)) =>
        if owner == p && toZone != .library p then n + 1 else n
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
        if !before.phasedOut && before.creature then
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
      if !before.phasedOut && before.creature && before.attacking then after.id <|> acc else acc
    | _ => acc) none

/-- Id of the permanent that most recently became tapped. -/
def lastBecameTapped (events : Array GameEvent) : Option ObjectId :=
  events.foldl (fun acc e =>
    match e.change with
    | .rules (.permanent (.tapped object _)) =>
      if !object.phasedOut then object.id <|> acc else acc
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
      | .rules (.zone (.moved _ after fromZone .battlefield _ _ _ _)) =>
        fromZone != .battlefield && !after.phasedOut && after.id == some id
      | .rules (.zone (.created object _)) =>
        object.zone == .battlefield && !object.phasedOut && object.id == some id
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

/-- Last known targets of stack object `oid` from `events`, walking backward through
`CastEvent.targeted` and `StackObjectEvent.copied` ancestry so copied stack spells
retain their inherited (or retargeted) targets after leaving the stack
(CR 608.2h / 707.10c). -/
def lastKnownTargetsOf? (events : Array GameEvent) (oid : ObjectId) : Option (Array Target) :=
  if oid == noSourceSentinelId then none
  else Id.run do
    let mut curId := oid
    for revIdx in [0:events.size] do
      let idx := events.size - 1 - revIdx
      match events[idx]!.change with
      | .rules (.cast (.targeted tid ts _ _)) =>
        if tid == curId then return some ts
      | .rules (.stackObject (.copied original copy _)) =>
        if copy.id == some curId then
          curId := original
      | _ => pure ()
    return none

/-- Whether `id` (or the spell `id` resolved from, CR 400.7d) is an uncast stack
copy created directly on `.stack` via `StackObjectEvent.copied` (CR 707.10), as
opposed to a cast card-copy (`CR 707.12` / Ruling 742). -/
def isUncastStackCopy (events : Array GameEvent) (id : ObjectId) : Bool :=
  let sid := stackSpellIdOf events id
  let createdViaStackCopy :=
    events.any fun e =>
      match e.change with
      | .rules (.stackObject (.copied _ copy _)) =>
        copy.id == some sid || copy.id == some id
      | .rules (.zone (.moved _ after _ .stack ..)) =>
        after.isCopy && (after.id == some sid || after.id == some id)
      | _ => false
  let hasCastEvent :=
    events.any fun e =>
      match e.change with
      | .rules (.cast (.spellCast s _ _)) => s.id == some sid || s.id == some id
      | .rules (.cast (.proposed obj _ _ _)) => obj == sid || obj == id
      | _ => false
  createdViaStackCopy && !hasCastEvent

/-- Whether `id` (or the spell it resolved from, CR 400.7d) was cast and is not
an uncast stack copy (CR 707.10 / 707.12). -/
def wasCast (events : Array GameEvent) (id : ObjectId) (isCopy : Bool := false) : Bool :=
  if isCopy || isUncastStackCopy events id then false
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
  if isCopy || isUncastStackCopy events spell then false
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
  if isCopy || isUncastStackCopy events spell then false
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

/-- Last-known `before` snapshot for `id` from `ZoneEvent.moved`,
`ZoneEvent.ceasedToExist`, or `PermanentEvent.phasedOut` (CR 113.7a / 608.2h /
702.26b). Stops at `PermanentEvent.phasedIn` (so stale pre-phase-out LKI is
never returned after phasing back in), prefers a prior `!before.phasedOut`
`PermanentEvent.phasedOut` snapshot over a phased-out `.moved`/`.ceasedToExist`
`before` snapshot, and matches `before.id == some id` only so post-departure
moves under a new `ObjectId` never overwrite an earlier life's departure
snapshot (CR 400.7). -/
def lastKnownBefore? (events : Array GameEvent) (id : ObjectId) : Option EventObject := Id.run do
  let mut phasedOutFallback? : Option EventObject := none
  let mut i := events.size
  while i > 0 do
    i := i - 1
    match events[i]!.change with
    | .rules (.permanent (.phasedIn eo _)) =>
      if eo.id == some id then
        return phasedOutFallback?
    | .rules (.zone (.moved before _ ..)) =>
      if before.id == some id then
        if before.zone == .battlefield && before.phasedOut then
          phasedOutFallback? := phasedOutFallback?.orElse (fun _ => some before)
        else
          return some before
    | .rules (.zone (.ceasedToExist before)) =>
      if before.id == some id then
        if before.zone == .battlefield && before.phasedOut then
          phasedOutFallback? := phasedOutFallback?.orElse (fun _ => some before)
        else
          return some before
    | .rules (.permanent (.phasedOut before _)) =>
      if before.id == some id then
        if !before.phasedOut then
          return some before
        else
          phasedOutFallback? := phasedOutFallback?.orElse (fun _ => some before)
    | _ => pure ()
  return phasedOutFallback?

/-- `id` entered from a spell cast for its impending cost (or a copy of one on
the stack, CR 702.176 / 707.10, ruling 970). -/
def castForImpending (events : Array GameEvent) (id : ObjectId) : Bool :=
  let announcedImpending (spellId : ObjectId) : Bool :=
    let rootId := rootCopiedSpellId events spellId
    events.any fun e =>
      match e.change with
      | .rules (.cast (.announced oid _ _ costs)) =>
        (oid == spellId || oid == rootId) && costs.any (fun | .impending _ => true | _ => false)
      | _ => false
  events.any fun e =>
    match e.change with
    | .rules (.continuousEffect (.created _ eff)) => eff == .notACreature id
    | .rules (.zone (.moved before after .stack .battlefield ..)) =>
      after.id == some id && before.id.any announcedImpending
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
    | .rules (.continuousEffect (.expired id spec?)) =>
      let eff? := spec?.orElse fun _ =>
        events.findSomeRev? (fun ev =>
          match ev.change with
          | .rules (.continuousEffect (.created cid eff)) =>
            if cid == id then some eff else none
          | _ => none)
      match eff? with
      | some eff => acc.push (id, eff)
      | none => acc
    | _ => acc) #[]

/-- All continuous effects that expired in `events`, in chronological order (CR 611). -/
def expiredEffects (events : Array GameEvent) : Array ContinuousEffectSpec :=
  (expiredEffectsWithId events).map (·.2)

end GameEvent

end Mtg.Engine
