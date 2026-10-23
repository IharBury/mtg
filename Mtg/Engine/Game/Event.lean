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

/-- The object a `GameEvent` is about, as it existed when the change happened
(CR 113.7a). Subtypes include those granted at that moment. -/
structure EventObject where
  id : ObjectId
  controller : Option PlayerId := none
  owner : PlayerId := ⟨0⟩
  token : Bool := false
  attacking : Bool := false
  changeling : Bool := false
  supertypes : Array Supertype := #[]
  types : Array CardType := #[]
  subtypes : Array CardSubtype := #[]
  keywords : Keywords := {}
  toxic : Nat := 0
deriving Repr, Inhabited, BEq

namespace EventObject

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

/-- `s` is one of this object's types, including changeling creature types
(CR 702.72). -/
def hasSubtype (o : EventObject) (s : CardSubtype) : Bool :=
  o.subtypes.any (· == s) || (o.changeling && !s.isNoncreature)

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

/-- This object as it is now, for a `GameEvent` (CR 113.7a). -/
def GameObject.asEvent (o : GameObject) : EventObject :=
  { id := o.id
    controller := o.controller
    owner := o.owner
    token := o.printed.isToken
    attacking := o.status.attacking
    changeling := o.printed.keywords.changeling
    supertypes := o.supertypes
    types := o.types
    subtypes := o.subtypes
    keywords := o.printedOrUntilEot
    toxic := o.printed.toxic }

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

/-- One change to a permanent's `Status` (CR 110.5). -/
inductive StatusChange where
  | set (s : Status)
  | reset
  | addDamage (n : Int) (deathtouch : Bool := false)
  | withoutCounters
  | proliferatedExceptPlusOne (extra : Nat := 0)
  | addCountersExceptPlusOne («from» : Status) (extra : Nat := 0)
  | addPump (p t : Int)
  | addPlusOnePlusOne (n : Nat := 1)
  | addCounters (kind : CounterKind) (n : Nat)
  | removeCounters (kind : CounterKind) (n : Nat := 1)
  | grantUntilEot (k : Keywords)
  | clearedAtCleanup
  | clearCombat
  | addBlocking (attackerId : ObjectId)
  | removeBlocking (attackerId : ObjectId)
  | pushAbilitiesActivated (idx : Nat)
  | incActivationsThisTurn
  | pushGrantedStatic (sa : StaticAbility)
  | pushGrantedTriggered (ta : TriggeredAbility)
  | pushGrantedTriggerUntilEot (ta : TriggeredAbility)
  | pushHexproofGrantedBy (id : ObjectId)
  | removeHexproofGrantedBy (id : ObjectId)
  | pushPreventDamageGrantedBy (id : ObjectId)
  | removePreventDamageGrantedBy (id : ObjectId)
  | pushCantUntapGrantedBy (id : ObjectId)
  | removeCantUntapGrantedBy (id : ObjectId)
  | pushLosesAbilitiesGrantedBy (id : ObjectId)
  | removeLosesAbilitiesGrantedBy (id : ObjectId)
  | addAdditionalSubtype (sub : CardSubtype)
  | pushAdditionalSubtype (sub : CardSubtype)
  | pushChosenMode (m : Nat)
  | pushModeChosenThisTurn (m : Nat)
  | pushAllianceModeChosen (m : Nat)
  | pushUntilTurnOfPump (p : PlayerId) (dp dt : Int)
  | clearUntilTurnOfPumpFor (p : PlayerId)
  | pushColorlessGrantUntilCast (id : ObjectId)
  | removeColorlessGrantUntilCast (id : ObjectId)
  | addCombatDamageToPlayer (p : PlayerId)
  | resetPerTurnFlags
  | tapped (v : Bool)
  | damage (v : Int)
  | summoningSick (v : Bool)
  | pump (v : Int × Int)
  | attacking (v : Bool)
  | attackingWhom (v : Option PlayerId)
  | attackingPlaneswalker (v : Option ObjectId)
  | blocking (v : Array ObjectId)
  | blocked (v : Bool)
  | activationsThisTurn (v : Nat)
  | abilitiesActivatedThisTurn (v : Array Nat)
  | plusOnePlusOne (v : Nat)
  | minusOneMinusOne (v : Nat)
  | loyaltyCounters (v : Nat)
  | loyaltyActivatedThisTurn (v : Bool)
  | prepared (v : Bool)
  | untilEotKeywords (v : Keywords)
  | untilEotLosesIndestructible (v : Bool)
  | untilEotExileIfDies (v : Bool)
  | setBasePT (v : Option (Int × Int))
  | additionalCreature (v : Bool)
  | additionalSubtypes (v : Array CardSubtype)
  | grantedStaticAbilities (v : Array StaticAbility)
  | grantedTriggeredAbilities (v : Array TriggeredAbility)
  | hexproofGrantedBy (v : Array ObjectId)
  | preventDamageGrantedBy (v : Array ObjectId)
  | dealtDeathtouch (v : Bool)
  | hope (v : Nat)
  | charge (v : Nat)
  | stun (v : Nat)
  | firedOnceEachTurn (v : Bool)
  | optionalOnceUsed (v : Bool)
  | additionalArtifactUntilEot (v : Bool)
  | hone (v : Nat)
  | shadow (v : Nat)
  | phasedOut (v : Bool)
  | phasedWith (v : Option ObjectId)
  | ringBearer (v : Bool)
  | allianceModesChosen (v : Array Nat)
  | shield (v : Nat)
  | finality (v : Nat)
  | declaredAsAttackerThisTurn (v : Bool)
  | boastUsedThisTurn (v : Bool)
  | plan (v : Nat)
  | powerUpUsed (v : Bool)
  | powerUpActivations (v : Nat)
  | becameTappedThisTurn (v : Bool)
  | gotPlusOneThisTurn (v : Bool)
  | cantUntapGrantedBy (v : Array ObjectId)
  | additionalCreatureUntilEot (v : Bool)
  | harnessed (v : Bool)
  | transformed (v : Bool)
  | cantTransform (v : Bool)
  | losesAbilitiesGrantedBy (v : Array ObjectId)
  | losesAbilitiesUntilEot (v : Bool)
  | chosenModes (v : Array Nat)
  | modesChosenThisTurn (v : Array Nat)
  | cardsInHandPowerUntilEot (v : Bool)
  | chosenOdd (v : Option Bool)
  | lore (v : Nat)
  | indestructibleCounters (v : Nat)
  | lifelinkCounters (v : Nat)
  | chosenCreatureType (v : Option CardSubtype)
  | cantBeBlockedByPlayer (v : Option PlayerId)
  | cantBeBlockedExceptByHasteUntilEot (v : Bool)
  | cantBlockUntilEot (v : Bool)
  | manaSpentToCast (v : Nat)
  | dealtDamageThisTurn (v : Bool)
  | replacedCreatureTypesUntilEot (v : Option (Array CardSubtype))
  | pumpPerArtifactUntilEot (v : Bool)
  | influence (v : Nat)
  | onlyFoodArtifact (v : Bool)
  | burden (v : Nat)
  | quest (v : Nat)
  | invasion (v : Nat)
  | trampleCounters (v : Nat)
  | keywordCounters (v : KeywordCounters)
  | combatDamageCreatesTreasure (v : Bool)
  | returnedAsArtifact (v : Bool)
  | controlUntilEot (v : Bool)
  | controlTurnEndsLeft (v : Nat)
  | ironFistTapGrants (v : Nat)
  | untilTurnOfPump (v : Array (PlayerId × Int × Int))
  | grantedTriggersUntilEot (v : Array TriggeredAbility)
  | exhaustUsed (v : Bool)
  | colorlessGrantUntilCast (v : Array ObjectId)
  | chosenColor (v : Option Color)
  | dealtCombatDamage (v : Bool)
  | combatDamageToPlayers (v : Array PlayerId)
  | animatedConstruct55 (v : Bool)
  | chosenName (v : Option String)
  | faceDown (v : Bool)
  | goaded (v : Bool)
  | story (v : Nat)
  | time (v : Nat)
  | notACreature (v : Bool)
  | windcragMardu (v : Bool)
  | chosenCardType (v : Option CardType)
  | freeCastFromGraveyard (v : Bool)
  | isCommander (v : Bool)
  | firstStrikeOnYourTurn (v : Bool)
deriving Repr, Inhabited, BEq

/-- One change to a `GameObject` (CR 109). -/
inductive ObjectChange where
  | status (c : StatusChange)
  | statuses (cs : Array StatusChange)
  | printed (v : CardDef)
  | owner (v : PlayerId)
  | controller (v : Option PlayerId)
  | lastController (v : Option PlayerId)
  | defaultController (v : Option PlayerId)
  | controlChanged (v : Bool)
  | zone (v : Zone)
  | timestamp (v : Nat)
  | abilityEffect (v : Option Effect)
  | triggeredAbility (v : Option TriggeredAbility)
  | reflexiveResolution (v : Option TriggeredAbility.TriggerResolution)
  | sourceId (v : Option ObjectId)
  | lastKnownPower (v : Option Int)
  | lastKnownToughness (v : Option Int)
  | playPermission (v : Option PlayPermission)
  | decrementPlayTurnEnds
  | attachedTo (v : Option ObjectId)
  | adventurerCard (v : Option CardDef)
  | linkedExile (v : Array ObjectId)
  | pushLinkedExile (id : ObjectId)
  | returnToZone (v : Option Zone)
  | leaveTriggerExile (v : Array ObjectId)
  | pushLeaveTriggerExile (id : ObjectId)
  | castFromGraveyard (v : Bool)
  | exileInstantSorceryInstead (v : Bool)
  | castFromHand (v : Bool)
  | wasCast (v : Bool)
  | isPreparedSpell (v : Bool)
  | fraCauseId (v : Option ObjectId)
  | fraCauseController (v : Option PlayerId)
  | fraCausePower (v : Option Int)
  | fraCauseStatus (v : Option Status)
  | exiledBy (v : Option ObjectId)
  | fraEffectUntilTurnOf (v : Option PlayerId)
  | flashbackUntilEot (v : Bool)
  | kicked (v : Bool)
  | teamworkPaid (v : Bool)
  | sneakPaid (v : Bool)
  | sneakAttackWhom (v : Option PlayerId)
  | giftPromisedTo (v : Option PlayerId)
  | isCopy (v : Bool)
  | uncounterableThisCast (v : Bool)
  | boastExiled (v : Array ObjectId)
  | enterProcessed (v : Bool)
  | treasureManaSpent (v : Bool)
  | chosenX (v : Option Nat)
  | copyRestore (v : Option CardDef)
  | copyUntilEot (v : Bool)
  | copyUntilNextTurn (v : Bool)
  | copyUntilSourceLeaves (v : Option ObjectId)
  | controlUntilSourceLeaves (v : Option ObjectId)
  | restoreCopy
deriving Repr, Inhabited, BEq

/-- One change to a `Player` (CR 102). -/
inductive PlayerChange where
  | name (v : String)
  | life (v : Int)
  | startingLife (v : Int)
  | maxHandSize (v : Nat)
  | startingHandSize (v : Nat)
  | manaPool (v : ManaPool)
  | addMana (t : ManaType) (n : Nat := 1) (elfRestricted : Bool := false)
      (instRestricted : Bool := false) (heroRestricted : Bool := false)
      (villainRestricted : Bool := false) (cantNonartifact : Bool := false)
      (creatureRestricted : Bool := false) (fra : Option FraManaUse := none)
  | emptyManaPool (becomesColorless : Bool := false)
  | additionalLandsThisTurn (v : Nat)
  | addAdditionalLandsThisTurn (n : Nat := 1)
  | poison (v : Nat)
  | addPoison (n : Nat)
  | lost (v : Bool)
  | leftTheGame (v : Bool)
  | drewFromEmpty (v : Bool)
  | mulligansTaken (v : Nat)
  | incMulligansTaken
  | keptOpeningHand (v : Bool)
  | library (v : Array ObjectId)
  | pushLibrary (id : ObjectId)
  | prependLibrary (ids : Array ObjectId)
  | appendLibrary (ids : Array ObjectId)
  | stripLibrary (id : ObjectId)
  | hand (v : Array ObjectId)
  | pushHand (id : ObjectId)
  | stripHand (id : ObjectId)
  | graveyard (v : Array ObjectId)
  | pushGraveyard (id : ObjectId)
  | stripGraveyard (id : ObjectId)
  | enduringStory (v : Bool)
  | theRingAbilities (v : Nat)
  | ringBearerId (v : Option ObjectId)
  | citysBlessing (v : Bool)
  | hasCommander (v : Bool)
  | commanderColorIdentity (v : ColorSet)
  | protectionFromEverything (v : Bool)
  | eaglesBirdsNextUpkeep (v : Nat)
  | addEaglesBirdsNextUpkeep (n : Nat)
  | beheldQualities (v : Array CardSubtype)
  | pushBeheldQuality (q : CardSubtype)
  | cantCastSpellsThisTurn (v : Bool)
  | attackPumpPerPlainsThisTurn (v : Nat)
  | addAttackPumpPerPlainsThisTurn (n : Nat := 1)
  | lifeLocked (v : Bool)
  | typeSpellCostLessThisTurn (v : Array (CardType × Nat))
  | pushTypeSpellCostLess (t : CardType) (n : Nat)
  | supertypeSpellCostLessThisTurn (v : Array (Supertype × Nat))
  | pushSupertypeSpellCostLess (s : Supertype) (n : Nat)
  | jaceLoyaltyAtInstantSpeed (v : Bool)
  | legendRuleOffThisTurn (v : Bool)
  | copyNextInstantSorceryThisTurn (v : Nat)
  | addCopyNextInstantSorceryThisTurn (n : Nat := 1)
  | decCopyNextInstantSorceryThisTurn
  | sideboard (v : Array CardDef)
  | removeSideboardAt (idx : Nat)
  | mountainExtraRedThisTurn (v : Nat)
  | addMountainExtraRedThisTurn (n : Nat := 1)
  | nextSpellCantBeCountered (v : Bool)
  | teammate (v : Option PlayerId)
  | isMonarch (v : Bool)
  | lifeCantChange (v : Bool)
  | cantAttackJaces (v : Bool)
  | commanderCreatureTypes (v : Array CardSubtype)
  | resetPerTurnFlags
deriving Repr, Inhabited, BEq

/-- One change to a `StackEntry` on the stack (CR 405). -/
inductive StackEntryChange where
  | targets (v : Array Target)
  | pushTarget (t : Target)
  | pushTargets (ts : Array Target)
  | setTargetAt (idx : Nat) (t : Target)
  | dividedDamage (v : Array Nat)
  | pushDividedDamage (n : Nat)
  | targetsAnnounced (v : Bool)
  | chosenMode (v : Option Nat)
  | extraModes (v : Array Nat)
  | pushExtraMode (m : Nat)
  | skippedOptionalSlots (v : Nat)
  | incSkippedOptionalSlots
deriving Repr, Inhabited, BEq

/-- One change to a `ProposedSpell` (CR 601.2f–h / 602.2b). -/
inductive ProposalChange where
  | cost (v : ManaCost)
  | addGenericCost (n : Nat)
  | addManaCost (c : ManaCost)
  | reduceCostBy (c : ManaCost)
  | substituteX (x : Nat)
  | tapped (v : Array ObjectId)
  | pushTapped (id : ObjectId)
  | tapSource (v : Bool)
  | sacrificeSource (v : Bool)
  | needsSacrificeOther (v : Bool)
  | needsDiscardCard (v : Bool)
  | payLife (v : Nat)
  | discardSource (v : Bool)
  | abilityModes (v : Array Effect)
  | targetKindOverride (v : Option EffectTargetKind)
  | kicked (v : Bool)
  | kickerAnnounced (v : Bool)
  | giftTo (v : Option PlayerId)
  | giftAnnounced (v : Bool)
  | teamworkPaid (v : Bool)
  | teamworkAnnounced (v : Bool)
  | activation (v : Option ActivatedAbility)
  | loyaltyX (v : Bool)
  | removePlusOneX (v : Bool)
  | sneakAttacker (v : Option ObjectId)
deriving Repr, Inhabited, BEq

/-- A continuous effect (CR 611), generated either by the resolution of a spell
or ability (CR 611.2) or by a static ability (CR 611.3). -/
inductive ContinuousEffect where
  /-- A continuous effect generated by a static ability of `source` (CR 611.3). -/
  | staticAbility (source : ObjectId) (ability : StaticAbility)
  /-- An Aura's static ability setting `object` to a 5/5 Construct artifact creature (CR 611.3). -/
  | auraConstruct55 (object : ObjectId)
  /-- `object` gets `power`/`toughness` until end of turn (CR 611.2). -/
  | pump (object : ObjectId) (power toughness : Int)
  /-- `object` gets `power`/`toughness` until `player`'s next turn (CR 611.2). -/
  | untilTurnOfPump (object : ObjectId) (player : PlayerId) (power toughness : Int)
  /-- `object` gets +1/+1 for each artifact its controller controls until end of turn (CR 611.2). -/
  | pumpPerArtifactUntilEot (object : ObjectId)
  /-- `object` gains `keywords` until end of turn (CR 611.2). -/
  | keywordsUntilEot (object : ObjectId) (keywords : Keywords)
  /-- `object` has first strike as long as it's its controller's turn (CR 611.2). -/
  | firstStrikeOnYourTurn (object : ObjectId)
  /-- `object` loses indestructible until end of turn (CR 611.2). -/
  | loseIndestructibleUntilEot (object : ObjectId)
  /-- If `object` would die this turn, exile it instead (CR 611.2). -/
  | exileIfDiesUntilEot (object : ObjectId)
  /-- `object` has base power and toughness `pt` until end of turn (CR 611.2). -/
  | setBasePTUntilEot (object : ObjectId) (pt : Int × Int)
  /-- `object`'s power and toughness are each equal to cards in its controller's hand until end of turn (CR 611.2). -/
  | cardsInHandPowerUntilEot (object : ObjectId)
  /-- `object` becomes a creature in addition to its other types (CR 611.2). -/
  | additionalCreature (object : ObjectId) (untilEot : Bool := false)
  /-- `object` becomes an artifact in addition to its other types until end of turn (CR 611.2). -/
  | additionalArtifactUntilEot (object : ObjectId)
  /-- `object` gains `subtype` in addition to its other types (CR 611.2). -/
  | additionalSubtype (object : ObjectId) (subtype : CardSubtype) (dedup : Bool := false)
  /-- `object`'s creature types are replaced by `subtypes` until end of turn (CR 611.2). -/
  | replacedCreatureTypesUntilEot (object : ObjectId) (subtypes : Array CardSubtype)
  /-- `object` is a Food artifact and loses all other card types and subtypes (CR 611.2). -/
  | onlyFoodArtifact (object : ObjectId)
  /-- `object` is an artifact and not a creature (CR 611.2). -/
  | returnedAsArtifact (object : ObjectId)
  /-- `object` isn't a creature (CR 611.2). -/
  | notACreature (object : ObjectId)
  /-- `object` gains static ability `ability` (CR 611.2). -/
  | grantedStatic (object : ObjectId) (ability : StaticAbility)
  /-- `object` gains triggered ability `ability` (CR 611.2). -/
  | grantedTriggered (object : ObjectId) (ability : TriggeredAbility) (untilEot : Bool := false)
  /-- `object` gains Iron Fist tap ability `n` times until end of turn (CR 611.2). -/
  | ironFistTapUntilEot (object : ObjectId) (n : Nat := 1)
  /-- `object` gains combat-damage-creates-Treasure trigger until end of turn (CR 611.2). -/
  | combatDamageCreatesTreasureUntilEot (object : ObjectId)
  /-- `object` loses all abilities until end of turn (CR 611.2). -/
  | losesAbilitiesUntilEot (object : ObjectId)
  /-- `object` loses all abilities for as long as `source` remains on the battlefield (CR 611.2b). -/
  | losesAbilitiesWhileSource (object : ObjectId) (source : ObjectId)
  /-- `object` has hexproof for as long as `source` remains on the battlefield (CR 611.2b). -/
  | hexproofWhileSource (object : ObjectId) (source : ObjectId)
  /-- Prevent all damage that would be dealt to `object` for as long as `source` remains on the battlefield (CR 611.2b). -/
  | preventDamageWhileSource (object : ObjectId) (source : ObjectId)
  /-- `object` doesn't untap during its controller's untap step for as long as `source` remains on the battlefield (CR 611.2b). -/
  | cantUntapWhileSource (object : ObjectId) (source : ObjectId)
  /-- `player`'s creatures can't block `object` this turn (CR 611.2). -/
  | cantBeBlockedByPlayerUntilEot (object : ObjectId) (player : PlayerId)
  /-- `object` can't be blocked except by creatures with haste this turn (CR 611.2). -/
  | cantBeBlockedExceptByHasteUntilEot (object : ObjectId)
  /-- `object` can't block this turn (CR 611.2). -/
  | cantBlockUntilEot (object : ObjectId)
  /-- `object` is goaded until its controller's next turn (CR 611.2, 701.15). -/
  | goaded (object : ObjectId)
  /-- `card` may be cast spending mana as though it were mana of any color while `object` grants it (CR 611.2). -/
  | colorlessGrantUntilCast (object : ObjectId) (card : ObjectId)
  /-- `object` may be cast from the graveyard without paying its mana cost this turn (CR 611.2). -/
  | freeCastFromGraveyardUntilEot (object : ObjectId)
  /-- `object` gains flashback until end of turn (CR 611.2). -/
  | flashbackUntilEot (object : ObjectId)
  /-- If `object` would be put into a graveyard from the stack, exile it instead (CR 611.2). -/
  | exileInstantSorceryInstead (object : ObjectId)
  /-- `object` can't be countered as a spell (CR 611.2). -/
  | uncounterableThisCast (object : ObjectId)
  /-- `object` may be played from exile under `perm` (CR 611.2). -/
  | playPermission (object : ObjectId) (perm : PlayPermission)
  /-- `object` (an emblem) lasts until `player`'s next turn (CR 611.2). -/
  | fraEmblemUntilTurnOf (object : ObjectId) (player : PlayerId)
  /-- `object` becomes a copy with `printed` characteristics (CR 611.2, 707). -/
  | copy (object : ObjectId) (printed : CardDef) (restore : Option CardDef)
      (untilEot : Bool := false) (untilNextTurn : Bool := false)
      (untilSourceLeaves : Option ObjectId := none)
  /-- `controller` gains control of `object` (CR 611.2). -/
  | control (object : ObjectId) (controller : PlayerId)
      (untilEot : Bool := false) (turnEndsLeft : Nat := 0)
      (untilSourceLeaves : Option ObjectId := none)
  /-- `player` may play `n` additional lands this turn (CR 611.2). -/
  | additionalLandsThisTurn (player : PlayerId) (n : Nat := 1)
  /-- `player` has protection from everything until their next turn (CR 611.2). -/
  | protectionFromEverything (player : PlayerId)
  /-- `player`'s life total can't change until their next turn (CR 611.2). -/
  | lifeCantChange (player : PlayerId)
  /-- `player`'s life total can't change this turn (CR 611.2). -/
  | lifeLocked (player : PlayerId)
  /-- `player` can't cast spells this turn (CR 611.2). -/
  | cantCastSpellsThisTurn (player : PlayerId)
  /-- Attacking creatures `player` controls get +1/+1 per Plains this turn (CR 611.2). -/
  | attackPumpPerPlainsThisTurn (player : PlayerId) (n : Nat := 1)
  /-- Spells of `cardType` `player` casts cost `n` less this turn (CR 611.2). -/
  | typeSpellCostLessThisTurn (player : PlayerId) (cardType : CardType) (n : Nat)
  /-- Spells of `supertype` `player` casts cost `n` less this turn (CR 611.2). -/
  | supertypeSpellCostLessThisTurn (player : PlayerId) (supertype : Supertype) (n : Nat)
  /-- `player` may activate loyalty abilities of Jace planeswalkers at instant speed this turn (CR 611.2). -/
  | jaceLoyaltyAtInstantSpeedThisTurn (player : PlayerId)
  /-- The "legend rule" doesn't apply to permanents `player` controls this turn (CR 611.2). -/
  | legendRuleOffThisTurn (player : PlayerId)
  /-- When `player` casts their next instant or sorcery spell this turn, copy it (CR 611.2). -/
  | copyNextInstantSorceryThisTurn (player : PlayerId) (n : Nat := 1)
  /-- Whenever `player` taps a Mountain for mana this turn, add an additional {R} (CR 611.2). -/
  | mountainExtraRedThisTurn (player : PlayerId) (n : Nat := 1)
  /-- The next spell `player` casts this turn can't be countered (CR 611.2). -/
  | nextSpellCantBeCounteredThisTurn (player : PlayerId)
  /-- Creatures can't attack `player` or Jace planeswalkers `player` controls this turn (CR 611.2). -/
  | cantAttackJacesThisTurn (player : PlayerId)
  /-- Creatures without flying can't block this turn (CR 611.2). -/
  | creaturesWithoutFlyingCantBlockUntilEot
  /-- Creatures `player` controls assign combat damage equal to their toughness this turn (CR 611.2). -/
  | assignCombatDamageEqualToughnessUntilEot (player : PlayerId)
  /-- The next red or green creature spell `player` casts this turn costs {0} (CR 611.2). -/
  | pendingFreeRGCreatureThisTurn (player : PlayerId)
  /-- `player`'s next instant or sorcery spell this turn is copied `power` times (CR 611.2). -/
  | pendingLokiCopy (player : PlayerId) (source : Option ObjectId) (power : Int)
  /-- `controller` controls `controlled` during their turn (CR 611.2, 720). -/
  | playerControl (controller controlled : PlayerId) (onNextTurn : Bool := false)
  /-- Creatures can't get +X/+Y from spells or abilities this turn (CR 611.2). -/
  | powerUpsForbiddenThisTurn
deriving Repr, Inhabited, BEq

/-- A game rule that causes an event directly (CR 103.5, 304.2, 307.2, 701.3d, 800.4a). -/
inductive GameRuleKind where
  | openingHandDraw
  | mulligan
  | instantOrSorceryFinishedResolving
  | unattachOnHostLeave
  | playerLeftGame
deriving DecidableEq, Repr, Inhabited, BEq

/-- A turn-based action (CR 703.4). -/
inductive TurnBasedAction where
  | phaseInOut          -- 502.1 / 703.4a
  | dayNightCheck       -- 502.2 / 703.4b
  | untapAll            -- 502.3 / 703.4c
  | drawStepDraw        -- 504.1 / 703.4d
  | sagaLoreOnMain      -- 714.3b / 703.4f
  | declareAttackers    -- 508.1 / 703.4h
  | declareBlockers     -- 509.1 / 703.4i
  | assignCombatDamage (firstStrike : Bool)  -- 510.1 / 510.4 / 703.4j
  | dealCombatDamage   (firstStrike : Bool)  -- 510.2 / 510.4 / 703.4k
  | removeFromCombatAtEndOfCombat            -- 511.3 / 703.4m
  | cleanupDiscard      -- 514.1 / 703.4n
  | cleanupClear        -- 514.2 / 703.4p (damage + until-EOT effects)
  | emptyManaPools      -- 500.4 / 703.4q
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
  | oneShotEffect (id : EffectId) (source : Option ObjectId := none)
      (controller : Option PlayerId := none)
  /-- A replacement effect (614) or prevention effect (615) modified a prior
  proposed event. `original` is the cause of the event that was replaced. -/
  | replaced (replacement : ReplacementId) (original : EventCause)
  /-- Migration-only: a call site not yet classified. Excluded from trigger
  matching that depends on cause; must reach zero uses for rules events by the
  end of Phase 3. -/
  | unclassified
deriving DecidableEq, Repr, Inhabited, BEq

/-- Who or what receives or loses counters (CR 122.1). Players in `Mtg.Engine`
only carry poison counters (`Player.poison`, CR 122.1f). -/
inductive CounterTarget where
  | object (o : EventObject)
  | player (p : PlayerId)
deriving Repr, Inhabited, BEq

/-- Whether counters are put on or removed from a target (CR 122.1). -/
inductive CounterDelta where
  | put (count : Nat)
  | removed (count : Nat)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Designations a permanent can have on the battlefield (CR 110.6 / 701.15b / 701.54a / 903.3). -/
inductive PermanentDesignation where
  | ringBearer                 -- 701.54a
  | commander                  -- 903.3
  | goaded (byPlayer : PlayerId) -- 701.15b
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
  | turnedFaceUp (object : EventObject)                                      -- 701.40b / 708.8
  | turnedFaceDown (object : EventObject)                                    -- 701.40f / 708.2
  | counters
      (target : CounterTarget)
      (kind : CounterKind)
      (delta : CounterDelta)
      (actor : Option PlayerId := none)                                      -- 122.1
  | attached (attachment : EventObject) (host : ObjectId)
      (previous : Option ObjectId := none)                                   -- 701.3a / 303.4 / 301.5
  | unattached (attachment : EventObject) (fromHost : ObjectId)              -- 701.3d / 704.5n / 704.5p
  | controlChanged (object : EventObject) (fromPlayer toPlayer : PlayerId)   -- 110.2 / 613.1b
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
  /-- Result of lifelink (CR 120.3f) or a "gain N life" instruction (CR 119.2):
  increases `Player.life`. -/
  | gained (player : PlayerId) (amount : Nat)
  /-- Result of damage to a player (CR 120.3a), "lose N life" (CR 119.3), or
  "pay N life" (CR 119.4): decreases `Player.life`. -/
  | lost (player : PlayerId) (amount : Nat)
      (fromDamage : Bool := false) (combat : Bool := false)
deriving DecidableEq, Repr, Inhabited, BEq

/-- A one-shot effect (CR 610) that does something just once and has no duration.
Kept during migration as a temporary constructor that lowers to the durable
`RulesEvent` constructors. -/
inductive OneShotEffect where
  /-- `object` moved from `fromZone` to `toZone` (CR 610.1 / 610.3).
  A creature moving from the battlefield to a graveyard died (CR 700.4).
  A card moving from its owner's hand to that player's graveyard was
  discarded when `discarded`. `sacrificed` is set when the move was a
  sacrifice that was not replaced. -/
  | moved (object : EventObject) (fromZone toZone : Zone)
      (sacrificed discarded : Bool := false)
  /-- `player` drew `card` (CR 121.1 / 610.1). `nth` is how many cards that
  player has drawn this turn, including this one. `firstOfOwnDrawStep` is the
  first card of that player's own draw step (CR 121.2). -/
  | drew (player : PlayerId) (card : ObjectId) (nth : Nat) (firstOfOwnDrawStep : Bool)
  /-- `player` gained or lost `amount` life (CR 119 / 610.1). Gaining is `gained`.
  Life lost because of damage has `fromDamage`. Combat damage has `combat`. -/
  | life (player : PlayerId) (amount : Nat) (gained fromDamage combat : Bool := false)
  /-- `amount` damage was dealt to `object` (CR 120 / 610.1). `combat` is combat damage. -/
  | damaged (source : Option ObjectId) (object : EventObject) (amount : Nat) (combat : Bool)
  /-- `amount` damage was dealt to `player` (CR 120 / 610.1). -/
  | damagedPlayer (source : Option ObjectId) (player : PlayerId) (amount : Nat) (combat : Bool)
  /-- `object` became tapped (`nowTapped`) or the tap was the change (CR 701.26a / 610.1).
  `duringControllersTurn` is true on that object's controller's turn. -/
  | tapped (object : EventObject) (nowTapped duringControllersTurn : Bool)
  /-- `object` untapped (CR 701.26b / 610.1). `replacedByStun` means a stun
  counter was removed instead, so the untap did not happen (CR 122.1d). -/
  | untapped (object : EventObject) (replacedByStun : Bool := false)
  /-- `n` counters of `kind` were put on or removed from `object` (CR 122 / 610.1).
  `removed` is a removal. -/
  | counters (player : Option PlayerId) (object : EventObject) (kind : CounterKind)
      (n : Nat) (removed : Bool := false)
  /-- `player` looked at `n` cards by scrying, or by surveilling when `surveil` (CR 701.22 / 701.25 / 610.1).
  `asked` is the printed number. Scry 0 is not recorded. Scrying a positive
  number still happens when the library has fewer cards (CR 701.22). -/
  | looked (player : PlayerId) (n : Nat) (surveil : Bool := false) (asked : Nat := n)
  /-- `player` sacrificed `object`, and the sacrifice was not replaced (CR 701.21 / 610.1). -/
  | sacrificed (player : PlayerId) (object : EventObject)
  /-- `player` created `object` (CR 111 / 701.7 / 610.1). -/
  | created (player : PlayerId) (object : EventObject)
  /-- `object` changed controller from `fromPlayer` to `toPlayer`. -/
  | control (object : ObjectId) (fromPlayer toPlayer : PlayerId)
  /-- The `nth` time `player` resolved the ability that counts its own
  resolutions this turn (CR 610.1). -/
  | resolved (player : PlayerId) (nth : Nat)
  /-- `object` became attached to `host` (CR 701.3 / 610.1). -/
  | attached (object host : ObjectId)
  /-- `player` beheld `quality` (CR 701.62 / 610.1). Later zone changes do not undo it. -/
  | beheld (player : PlayerId) (quality : CardSubtype)
  /-- `player` got `n` poison counters (CR 122.1c / 610.1). -/
  | poisoned (player : PlayerId) (n : Nat)
  /-- `player` proliferated (CR 701.34 / 610.1). -/
  | proliferated (player : PlayerId)
  /-- `player` chose to have The Sensational She-Hulk deal damage. Once each turn. -/
  | sheHulkDealtDamage (player : PlayerId)
deriving Repr, Inhabited, BEq

/-- A rules-level occurrence in the game (CR 603.2 / 610 / 611 / 614). -/
inductive RulesEvent where
  /-- Permanent status, counter, attachment, control, and designation events. -/
  | permanent (e : PermanentEvent)
  /-- Damage facts and damage results. -/
  | damage (e : DamageEvent)
  /-- Life gain and life loss events. -/
  | life (e : LifeEvent)
  /-- `player` cast `spell` from `fromZone`. `manaSpent` is the mana paid. -/
  | cast (player : PlayerId) (spell : EventObject) (fromZone : Zone)
      (manaValue manaSpent : Nat) (fromGraveyard teamwork gift : Bool := false)
  /-- `player` attacked with `attacker`. -/
  | attacked (player : PlayerId) (attacker : EventObject) (whom : PlayerId)
  /-- The game entered `step` on `active`'s turn. A skipped step is not recorded
  (CR 614.10). -/
  | stepped (step : Step) (active : PlayerId)
  /-- `player` activated an ability of `source`. `loyalty` is a loyalty ability.
  `equip` is an equip ability, recorded when the activation is completed. -/
  | activated (player : PlayerId) (source : EventObject) (loyalty equip : Bool)
  /-- `player` spent `amount` mana. -/
  | spentMana (player : PlayerId) (amount : Nat)
  /-- `player` played `land` as a land drop (CR 305.1). Putting a land onto
  the battlefield another way is not a play. -/
  | playedLand (player : PlayerId) (land : EventObject)
  /-- A one-shot effect is applied (CR 610). Kept only for variants not yet
  migrated to durable `RulesEvent` constructors. -/
  | effectApplied (id : EffectId) (effect : OneShotEffect)
  /-- A continuous effect begins (CR 611). -/
  | effectCreated (id : EffectId) (effect : ContinuousEffect)
  /-- A continuous effect ends (CR 611). -/
  | effectExpired (id : EffectId) (effect : ContinuousEffect)
  /-- Bookkeeping on an existing continuous effect `id` (a decremented turn
  counter, or last-known information after its source left), keeping the same
  `EffectId`. This neither creates nor ends an effect (CR 611). -/
  | effectUpdated (id : EffectId) (effect : ContinuousEffect)
deriving Repr, Inhabited, BEq

namespace OneShotEffect

/-- Lower a `OneShotEffect` to its durable `RulesEvent` constructor. -/
def toRulesEvent (id : EffectId) : OneShotEffect → RulesEvent
  | .tapped object true during => .permanent (.tapped object during)
  | .tapped object false _ => .permanent (.untapped object)
  | .untapped object false => .permanent (.untapped object)
  | .untapped object true => .permanent (.counters (.object object) .stun (.removed 1) none)
  | .counters actor object kind n false =>
    .permanent (.counters (.object object) kind (.put n) actor)
  | .counters actor object kind n true =>
    .permanent (.counters (.object object) kind (.removed n) actor)
  | .poisoned player n =>
    .permanent (.counters (.player player) .poison (.put n) none)
  | .attached object host =>
    .permanent (.attached { id := object } host none)
  | .control object fromP toP =>
    .permanent (.controlChanged { id := object } fromP toP)
  | .life player amount true _ _ =>
    .life (.gained player amount)
  | .life player amount false fromDamage combat =>
    .life (.lost player amount fromDamage combat)
  | .damaged source object amount combat =>
    .damage (.dealt #[{
      source := { id := source.getD ⟨0⟩ }
      recipient := .permanent object
      amount := amount
      combat := combat }])
  | .damagedPlayer source player amount combat =>
    .damage (.dealt #[{
      source := { id := source.getD ⟨0⟩ }
      recipient := .player player
      amount := amount
      combat := combat }])
  | eff => .effectApplied id eff

end OneShotEffect

/-- Internal engine state mutations that are not rules-level occurrences. -/
inductive EngineChange where
  /-- Update a player's state. -/
  | player (p : PlayerId) (c : PlayerChange)
  | playerChanges (p : PlayerId) (cs : Array PlayerChange)
  | players (v : Array Player)
  | setPlayer (pl : Player)
  /-- Update an object's state. -/
  | object (id : ObjectId) (c : ObjectChange)
  | objectChanges (id : ObjectId) (cs : Array ObjectChange)
  | objects (v : Array GameObject)
  | setObject (o : GameObject)
  | removeObject (id : ObjectId)
  | replaceObject (oldId : ObjectId) (fresh : GameObject)
  /-- Update the stack. -/
  | stack (v : Array StackEntry)
  | pushStack (e : StackEntry)
  | popStack
  | removeFromStack (objectId : ObjectId)
  | setStackEntryAt (idx : Nat) (e : StackEntry)
  | stackEntry (idx : Nat) (c : StackEntryChange)
  | stackEntryById (objectId : ObjectId) (c : StackEntryChange)
  /-- Update the proposed spell or ability. -/
  | proposedSpell (v : Option ProposedSpell)
  | proposal (c : ProposalChange)
  | proposalChanges (cs : Array ProposalChange)
  /-- Update game fields. -/
  | activePlayer (v : PlayerId)
  | priority (v : PlayerId)
  | step (v : Step)
  | turnNumber (v : Nat)
  | startingPlayer (v : PlayerId)
  | isFirstTurn (v : Bool)
  | pending (v : Pending)
  | nextObjectId (v : Nat)
  | nextEffectId (v : Nat)
  | activeEffects (v : Array (EffectId × ContinuousEffect))
  | timestamp (v : Nat)
  | afterRandom (v : AfterRandom)
  | result (v : Option GameResult)
  | log (v : Array String)
  | logMsg (msg : String)
  | format (v : Format)
  | brawl (v : Bool)
  | consecutivePasses (v : Nat)
  | cleanupGivesPriority (v : Bool)
  | creaturesWithoutFlyingCantBlock (v : Bool)
  | awaitingOpeningBegin (v : Bool)
  | mulliganToDeclare (v : Array PlayerId)
  | willMulligan (v : Array PlayerId)
  | pushWillMulligan (p : PlayerId)
  | mulliganToBottom (v : Array PlayerId)
  | assignedCombatDamage (v : Array CreatureCombatAssignment)
  | blockersQueue (v : Array PlayerId)
  | waitingTriggers (v : Array WaitingTrigger)
  | enqueueWaitingTriggers (wts : Array WaitingTrigger)
  | pushWaitingTrigger (wt : WaitingTrigger)
  | removeWaitingTriggersOf (p : PlayerId)
  | removeWaitingTriggersForEvent (ev : TriggerEvent)
  | removeWaitingTriggersForPlayerSource (p : PlayerId) (sourceId : ObjectId) (part2 : Bool)
  | eraseFirstWaitingTriggerForPlayerSource (p : PlayerId) (sourceId : ObjectId) (part2 : Bool)
  | addSourceDealtDamagePower (sourceId : ObjectId) (n : Int)
  | firstStrikeDamageDone (v : Bool)
  | pendingRegularCombatDamage (v : Bool)
  | firstStrikeAssignedThisCombat (v : Array ObjectId)
  | isNight (v : Bool)
  | pendingDrawAfterScry (v : Option (PlayerId × Nat))
  | discardedCardThisWay (v : Option (PlayerId × ObjectId))
  | palantirAfterScry (v : Option (PlayerId × PlayerId × ObjectId))
  | lastKnownStatus (v : Array (ObjectId × Status))
  | recordLastKnownStatus (id : ObjectId) (s : Status)
  | resolvingSpell (v : Option ObjectId)
  | resolvingAbility (v : Option ObjectId)
  | movedTo (v : Array (ObjectId × ObjectId))
  | recordMovedTo (oldId newId : ObjectId)
  | recentTokenIds (v : Array ObjectId)
  | pushRecentTokenId (id : ObjectId)
  | fraAfterLook (v : Option (PlayerId × Option ObjectId × FraNext))
  | pendingFreeCopies (v : Option (PlayerId × Array ObjectId × Nat × Nat))
  | pendingMayCastFromExile (v : Option (PlayerId × Array ObjectId × Nat))
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
  | pushMilledIdThisWay (id : ObjectId)
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
  | lockedDeathReplacements (v : Option (Array GameObject))
  | suppressOthersDie (v : Bool)
  | suppressCreatureCardsToGy (v : Bool)
  | castingFromTop (v : Bool)
  | delayedEndStepReturns (v : Array ObjectId)
  | pushDelayedEndStepReturn (id : ObjectId)
  | extraTurns (v : Array PlayerId)
  | pushExtraTurn (p : PlayerId)
  | powerUpsForbidden (v : Bool)
  | delayedEndStepExiles (v : Array ObjectId)
  | pushDelayedEndStepExile (id : ObjectId)
  | conniveSource (v : Option ObjectId)
  | plusOneAfterDiscards (v : Option ObjectId)
  | additionalCombatPhases (v : Nat)
  | enrageGrantsAdditionalCombat (v : Nat)
  | resolvingDivision (v : Array Nat)
  | pendingTokenEnters (v : Array ObjectId)
  | pushPendingTokenEnter (id : ObjectId)
  | playerControl (v : Option (PlayerId × PlayerId))
  | controlOnNextTakenTurn (v : Bool)
  | pendingLokiCopy (v : Option (PlayerId × Option ObjectId × Int))
  | assignCombatDamageEqualToughness (v : Option PlayerId)
  | pendingFreeRGCreature (v : Option PlayerId)
  | plusOneAfterSearch (v : Option ObjectId)
  | thirstDiscardsLeft (v : Nat)
  | thirstDiscardType (v : CardType)
  | pendingDiscardsLeft (v : Nat)
  | wardQueue (v : Array WardObligation)
  | enqueueWard (ws : Array WardObligation)
  | delayedEndStepSacrifices (v : Array ObjectId)
  | pushDelayedEndStepSacrifice (id : ObjectId)
  | delayedGraveReturns (v : Array (ObjectId × PlayerId))
  | pushDelayedGraveReturn (id : ObjectId) (p : PlayerId)
  | delayedSynthetic (v : Array (PlayerId × Nat))
  | pushDelayedSynthetic (p : PlayerId) (n : Nat)
  | untapSearchedIfLands (v : Option Nat)
  | pendingCreatureTokenCreators (v : Array PlayerId)
  | pushPendingCreatureTokenCreator (p : PlayerId)
  | ancestryLandsTapped (v : Array ObjectId)
  | pushAncestryLandTapped (id : ObjectId)
  | removeAncestryLandTapped (id : ObjectId)
  | sbaChecked
  | clearEvents
deriving Repr, Inhabited, BEq

/-- One change to the game, without the turn number. `GameEvent` stores the turn,
batch, and cause. -/
inductive GameChange where
  | rules (e : RulesEvent)
  | engine (c : EngineChange)
deriving Repr, Inhabited, BEq

/-- A game state change on a given turn (CR 500). `Game.events` records each
one that happens. -/
structure GameEvent where
  turn : Nat
  batch : BatchId := ⟨0⟩
  cause : EventCause
  change : GameChange
deriving Repr, Inhabited, BEq

namespace GameEvent

/-- Migration helper for sites that have not yet classified their `EventCause`. -/
def unclassified (turn : Nat) (change : GameChange) (batch : BatchId := ⟨0⟩) : GameEvent :=
  { turn, batch, cause := .unclassified, change }

/-- Construct a `GameEvent` from a `RulesEvent` with an explicit `EventCause`. -/
def rules (turn : Nat) (e : RulesEvent) (cause : EventCause)
    (batch : BatchId := ⟨0⟩) : GameEvent :=
  { turn, batch, cause, change := .rules e }

/-- Route a `RulesEvent` with an optional `EventCause` through `rules` when
classified, or `unclassified` during Phase 1 migration. -/
def rulesOrUnclassified (turn : Nat) (e : RulesEvent)
    (cause : Option EventCause := none) (batch : BatchId := ⟨0⟩) : GameEvent :=
  match cause with
  | some c => rules turn e c batch
  | none => unclassified turn (.rules e) batch

/-- Construct an internal `EngineChange` event. -/
def engine (turn : Nat) (c : EngineChange) (batch : BatchId := ⟨0⟩) : GameEvent :=
  unclassified turn (.engine c) batch

/-- A one-shot effect is applied (CR 610). Lowers to the durable `RulesEvent`
constructors. -/
def effectApplied (turn : Nat) (id : EffectId) (effect : OneShotEffect) : GameEvent :=
  rules turn (effect.toRulesEvent id) (.oneShotEffect id)

/-- `object` moved from `fromZone` to `toZone` (CR 610.1 / 610.3). -/
def moved (turn : Nat) (object : EventObject) (fromZone toZone : Zone)
    (sacrificed : Bool := false) (discarded : Bool := false)
    (id : EffectId := ⟨0⟩) : GameEvent :=
  effectApplied turn id (.moved object fromZone toZone sacrificed discarded)

/-- `player` drew `card` as the `nth` card this turn (CR 610.1). -/
def drew (turn : Nat) (player : PlayerId) (card : ObjectId) (nth : Nat)
    (firstOfOwnDrawStep : Bool := false) (id : EffectId := ⟨0⟩) : GameEvent :=
  effectApplied turn id (.drew player card nth firstOfOwnDrawStep)

/-- `player` gained or lost life (CR 119.2 / 119.3). -/
def life (turn : Nat) (player : PlayerId) (amount : Nat)
    (gained : Bool := false) (fromDamage : Bool := false) (combat : Bool := false)
    (cause : Option EventCause := none) : GameEvent :=
  let ev :=
    if gained then LifeEvent.gained player amount
    else .lost player amount fromDamage combat
  rulesOrUnclassified turn (.life ev) cause

/-- Damage was dealt to an object (CR 120.3 / 120.4b). -/
def damaged (turn : Nat) (source : EventObject) (object : EventObject)
    (amount : Nat) (combat : Bool := false)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.damage (.dealt #[{
    source := source
    recipient := .permanent object
    amount := amount
    combat := combat }])) cause

/-- Damage was dealt to a player (CR 120.3a / 120.4b). -/
def damagedPlayer (turn : Nat) (source : EventObject) (player : PlayerId)
    (amount : Nat) (combat : Bool := false)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.damage (.dealt #[{
    source := source
    recipient := .player player
    amount := amount
    combat := combat }])) cause

/-- Result of damage to a creature (CR 120.3e): marks `amount` damage on `object`. -/
def damageMarked (turn : Nat) (object : ObjectId) (amount : Nat)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.damage (.marked object amount)) cause

/-- Result of cleanup (CR 514.2) or regeneration (CR 701.19a): clears marked damage. -/
def damageMarkedCleared (turn : Nat) (objects : Array ObjectId)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.damage (.markedCleared objects)) cause

/-- Damage that was prevented (CR 615.1 / 615.6). -/
def damagePrevented (turn : Nat) (source : EventObject)
    (recipient : DamageRecipient) (amount : Nat)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.damage (.prevented source recipient amount)) cause

/-- `player` cast `spell`. -/
def cast (turn : Nat) (player : PlayerId) (spell : EventObject) (fromZone : Zone)
    (manaValue : Nat := 0) (manaSpent : Nat := 0)
    (fromGraveyard : Bool := false) (teamwork : Bool := false) (gift : Bool := false) : GameEvent :=
  unclassified turn (.rules (.cast player spell fromZone manaValue manaSpent fromGraveyard teamwork gift))

/-- `player` attacked `whom` with `attacker`. -/
def attacked (turn : Nat) (player : PlayerId) (attacker : EventObject) (whom : PlayerId)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.attacked player attacker whom) cause

/-- `object` became tapped or untapped by a tap action (CR 701.26a). `nowTapped` is the result. -/
def tapped (turn : Nat) (object : EventObject) (nowTapped : Bool := true)
    (duringControllersTurn : Bool := false)
    (cause : Option EventCause := none) : GameEvent :=
  if nowTapped then
    rulesOrUnclassified turn (.permanent (.tapped object duringControllersTurn)) cause
  else
    rulesOrUnclassified turn (.permanent (.untapped object)) cause

/-- Counters were put on or removed from `object` (CR 122.1). -/
def counters (turn : Nat) (player : Option PlayerId) (object : EventObject)
    (kind : CounterKind) (n : Nat) (removed : Bool := false)
    (cause : Option EventCause := none) : GameEvent :=
  let delta := if removed then CounterDelta.removed n else .put n
  rulesOrUnclassified turn (.permanent (.counters (.object object) kind delta player)) cause

/-- `player` scried or surveilled (CR 701.22 / 701.25 / 610.1). `n` cards were looked at. `asked` is the
printed number; it defaults to `n`. -/
def looked (turn : Nat) (player : PlayerId) (n : Nat) (surveil : Bool := false)
    (asked : Nat := n) (id : EffectId := ⟨0⟩) : GameEvent :=
  effectApplied turn id (.looked player n surveil asked)

/-- `player` sacrificed `object` (CR 701.21 / 610.1). -/
def sacrificed (turn : Nat) (player : PlayerId) (object : EventObject)
    (id : EffectId := ⟨0⟩) : GameEvent :=
  effectApplied turn id (.sacrificed player object)

/-- `player` created `object` (CR 111 / 701.7 / 610.1). -/
def created (turn : Nat) (player : PlayerId) (object : EventObject)
    (id : EffectId := ⟨0⟩) : GameEvent :=
  effectApplied turn id (.created player object)

/-- `object` changed controller from `fromPlayer` to `toPlayer` (CR 110.2 / 613.1b). -/
def control (turn : Nat) (object : ObjectId) (fromPlayer toPlayer : PlayerId)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.permanent (.controlChanged { id := object } fromPlayer toPlayer)) cause

/-- The step or phase changed. -/
def stepped (turn : Nat) (step : Step) (active : PlayerId) : GameEvent :=
  unclassified turn (.rules (.stepped step active))

/-- `player` activated an ability of `source`. `equip` is set when the
activation has been completed, so a proposal still being paid does not count. -/
def activated (turn : Nat) (player : PlayerId) (source : EventObject)
    (loyalty : Bool := false) (equip : Bool := false) : GameEvent :=
  unclassified turn (.rules (.activated player source loyalty equip))

/-- `player` played `land` (CR 116.2a / 305.1). -/
def playedLand (turn : Nat) (player : PlayerId) (land : EventObject) : GameEvent :=
  rules turn (.playedLand player land) (.specialAction .playLand player)

/-- The `nth` counted resolution for `player` this turn (CR 610.1). -/
def resolved (turn : Nat) (player : PlayerId) (nth : Nat)
    (id : EffectId := ⟨0⟩) : GameEvent :=
  effectApplied turn id (.resolved player nth)

/-- `object` became attached to `host` (CR 701.3a / 303.4 / 301.5). -/
def attached (turn : Nat) (object host : ObjectId)
    (previous : Option ObjectId := none)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.permanent (.attached { id := object } host previous)) cause

/-- `attachment` became unattached from `fromHost` (CR 701.3d / 704.5n / 704.5p). -/
def unattached (turn : Nat) (attachment : EventObject) (fromHost : ObjectId)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.permanent (.unattached attachment fromHost)) cause

/-- `player` beheld `quality` (CR 701.62 / 610.1). -/
def beheld (turn : Nat) (player : PlayerId) (quality : CardSubtype)
    (id : EffectId := ⟨0⟩) : GameEvent :=
  effectApplied turn id (.beheld player quality)

/-- `player` spent mana (CR 118.3). -/
def spentMana (turn : Nat) (player : PlayerId) (amount : Nat) : GameEvent :=
  rules turn (.spentMana player amount) (.costPayment .mana player)

/-- `player` got poison counters (CR 122.1c). -/
def poisoned (turn : Nat) (player : PlayerId) (n : Nat)
    (byPlayer : Option PlayerId := none)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.permanent (.counters (.player player) .poison (.put n) byPlayer)) cause

/-- `player` proliferated (CR 701.34 / 610.1). -/
def proliferated (turn : Nat) (player : PlayerId)
    (id : EffectId := ⟨0⟩) : GameEvent :=
  effectApplied turn id (.proliferated player)

/-- `player` chose to have The Sensational She-Hulk deal damage (CR 610.1). -/
def sheHulkDealtDamage (turn : Nat) (player : PlayerId)
    (id : EffectId := ⟨0⟩) : GameEvent :=
  effectApplied turn id (.sheHulkDealtDamage player)

/-- `object` untapped, or a stun counter replaced that untap (CR 701.26b / 122.1d). -/
def untapped (turn : Nat) (object : EventObject) (replacedByStun : Bool := false)
    (cause : Option EventCause := none) : GameEvent :=
  if replacedByStun then
    rulesOrUnclassified turn (.permanent (.counters (.object object) .stun (.removed 1) none)) cause
  else
    rulesOrUnclassified turn (.permanent (.untapped object)) cause

/-- A continuous effect begins (CR 611). -/
def effectCreated (turn : Nat) (id : EffectId) (effect : ContinuousEffect) : GameEvent :=
  unclassified turn (.rules (.effectCreated id effect))

/-- A continuous effect ends (CR 611). -/
def effectExpired (turn : Nat) (id : EffectId) (effect : ContinuousEffect) : GameEvent :=
  unclassified turn (.rules (.effectExpired id effect))

/-- Bookkeeping on an existing continuous effect `id` (CR 611). -/
def effectUpdated (turn : Nat) (id : EffectId) (effect : ContinuousEffect) : GameEvent :=
  unclassified turn (.rules (.effectUpdated id effect))

/-- Same event, sent to `toZone` instead. Used after a zone replacement. -/
def withDestination (e : GameEvent) (toZone : Zone) (discarded : Bool) : GameEvent :=
  match e.change with
  | .rules (.effectApplied id (.moved object fromZone _ sacrificed _)) =>
    { e with change := .rules (.effectApplied id (.moved object fromZone toZone sacrificed discarded)) }
  | _ => e

/-- A creature moved from the battlefield to a graveyard (CR 700.4). -/
def isCreatureToGraveyard (e : GameEvent) : Bool :=
  match e.change with
  | .rules (.effectApplied _ (.moved object .battlefield (.graveyard _) _ _)) => object.creature
  | _ => false

/-- A permanent moved from the battlefield to a graveyard. -/
def isPermanentToGraveyard (e : GameEvent) : Bool :=
  match e.change with
  | .rules (.effectApplied _ (.moved _ .battlefield (.graveyard _) _ _)) => true
  | _ => false

/-- An object left the stack for another zone. -/
def leavesStack (e : GameEvent) : Bool :=
  match e.change with
  | .rules (.effectApplied _ (.moved _ .stack toZone _ _)) => toZone != .stack
  | _ => false

/-- An instant or sorcery moved from the stack to its owner's graveyard. -/
def entersOwnGraveyardFromStack (e : GameEvent) : Bool :=
  match e.change with
  | .rules (.effectApplied _ (.moved object .stack (.graveyard owner) _ _)) =>
    object.instantOrSorcery && owner == object.owner
  | _ => false

/-- A permanent entered the battlefield. -/
def enteredBattlefield (e : GameEvent) : Bool :=
  match e.change with
  | .rules (.effectApplied _ (.moved _ _ .battlefield _ _)) => true
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
    | .rules (.effectApplied _ (.drew _ _ _ _)) => true
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
    | .rules (.effectApplied _ (.created _ _)) => true
    | _ => false
  | .wouldPutCounter =>
    match e.change with
    | .rules (.permanent (.counters _ _ (.put n) _)) => n > 0
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
  let this (o : EventObject) : Bool := o.id == sourceId
  let yours (o : EventObject) : Bool := o.controller == some listener
  let other (o : EventObject) : Bool := o.id != sourceId
  match e.change with
  | .engine _ => false
  | .rules r =>
    match r, te with
    | .effectApplied _ (.drew p _ _ _), .youDraw => you p
    | .effectApplied _ (.drew p _ nth _), .youDrawSecondCard => you p && nth == 2
    | .effectApplied _ (.drew _ _ nth _), .anyPlayerDrawsSecond => nth == 2
    | .effectApplied _ (.drew p _ _ first), .opponentDrawsExceptFirstDrawStep => !you p && !first
    | .effectApplied _ (.drew p _ nth _), .opponentDrawsSecondCard => !you p && nth == 2
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
    | .damage (.dealt pkts), .dealsCombatDamageToPlayerOrBattle =>
      pkts.any (fun pkt => pkt.combat && match pkt.recipient with | .player _ | .battle _ => true | _ => false)
    | .damage (.dealt pkts), .combatDamageToYou =>
      pkts.any (fun pkt => pkt.combat && match pkt.recipient with | .player p => you p | _ => false)
    | .damage (.dealt pkts), .heroesDealDamageToPlayer =>
      pkts.any (fun pkt =>
        match pkt.recipient with
        | .player _ => yours pkt.source && pkt.source.hero
        | _ => false)
    | .effectApplied _ (.moved object .battlefield (.graveyard _) _ _), .dying =>
      this object && object.creature
    | .effectApplied _ (.moved object .battlefield _ _ _), .leaving => this object
    | .effectApplied _ (.moved object _ .battlefield _ _), .entering => this object
    | .effectApplied _ (.moved object _ .battlefield _ _), .landYouControlEnters =>
      yours object && object.land
    | .effectApplied _ (.moved object _ .battlefield _ _), .forestYouControlEnters =>
      yours object && object.forest
    | .effectApplied _ (.moved object _ .battlefield _ _), .mountainYouControlEnters =>
      yours object && object.mountain
    | .effectApplied _ (.moved object _ .battlefield _ _), .artifactYouControlEnters =>
      yours object && object.artifact
    | .effectApplied _ (.moved object _ .battlefield _ _), .creatureYouControlEnters =>
      yours object && object.creature
    | .effectApplied _ (.moved object _ .battlefield _ _), .anotherCreatureYouControlEnters =>
      yours object && other object && object.creature
    | .effectApplied _ (.moved object _ .battlefield _ _), .anotherElfYouControlEnters =>
      yours object && other object && object.elf
    | .effectApplied _ (.moved object _ .battlefield _ _), .tokenYouControlEnters =>
      yours object && object.token
    | .effectApplied _ (.moved object _ .battlefield _ _), .equipmentYouControlEnters =>
      yours object && object.equipment
    | .effectApplied _ (.moved object _ .battlefield _ _), .anotherArtifactEnters =>
      yours object && other object && object.artifact
    | .effectApplied _ (.moved object _ .battlefield _ _), .anotherVillainEnters =>
      yours object && other object && object.villain
    | .effectApplied _ (.moved object _ .battlefield _ _), .anotherVillainOrArtifactEnters =>
      yours object && other object && (object.villain || object.artifact)
    | .effectApplied _ (.moved object _ .battlefield _ _), .anotherNontokenHeroEnters =>
      yours object && other object && !object.token && object.hero
    | .effectApplied _ (.moved object _ .battlefield _ _), .anotherNontokenArtifactEnters =>
      yours object && other object && !object.token && object.artifact
    | .effectApplied _ (.moved object .battlefield (.graveyard _) _ _), .creatureYouControlDies =>
      yours object && object.creature
    | .effectApplied _ (.moved object .battlefield (.graveyard _) _ _), .nontokenYouControlDies =>
      yours object && object.creature && !object.token
    | .effectApplied _ (.moved object .battlefield (.graveyard _) _ _), .anotherGoblinOrcArmyDies =>
      yours object && other object && object.creature && object.goblinOrcArmy
    | .effectApplied _ (.moved object .battlefield (.graveyard _) _ _), .villainYouControlDies =>
      yours object && other object && object.creature && object.villain
    | .effectApplied _ (.moved object .battlefield (.graveyard _) _ _), .attackingCreatureYouControlDies =>
      yours object && object.creature && object.attacking
    | .effectApplied _ (.moved object .battlefield (.graveyard _) _ _), .oneOrMoreOtherCreaturesDie =>
      other object && object.creature
    | .effectApplied _ (.moved object .battlefield (.hand _) _ _), .anotherNonlandReturned =>
      yours object && other object && !object.land
    | .effectApplied _ (.moved object (.graveyard owner) _ _ _), .creatureCardLeavesYourGy =>
      you owner && object.creature
    | .effectApplied _ (.moved object _ (.graveyard owner) _ _), .creatureCardsPutIntoYourGy =>
      you owner && object.creature && !object.token
    | .effectApplied _ (.moved _ (.hand p) (.graveyard q) _ true), .youDiscard =>
      you p && p == q
    | .effectApplied _ (.moved object (.hand p) (.graveyard q) _ true), .fra .youDiscardThis =>
      you p && p == q && this object
    | .effectApplied _ (.moved _ (.hand p) (.graveyard q) _ true), .fra .youDiscardOne =>
      you p && p == q
    | .effectApplied _ (.moved _ (.hand p) (.graveyard q) _ true), .fra .playerDiscards =>
      p == q
    | .effectApplied _ (.moved object .battlefield (.graveyard _) _ _), .fra .enchantedDies =>
      object.creature
    | .effectApplied _ (.moved object .battlefield (.graveyard _) _ _), .fra .nontokenCreatureYouControlDies =>
      yours object && object.creature && !object.token
    | .effectApplied _ (.moved object .battlefield (.graveyard _) _ _), .fra .anotherCreatureOrPlaneswalkerYouControlDies =>
      yours object && other object && (object.creature || object.planeswalker)
    | .effectApplied _ (.moved object .battlefield _ _ _), .fra .creatureYouControlLeaves =>
      yours object && other object && object.creature
    | .effectApplied _ (.moved object _ .battlefield _ _), .subtypeYouControlEnters sub =>
      yours object && object.hasSubtype sub
    | .cast p spell _ _ _ _ _ _, .youCastInstantOrSorcery =>
      you p && spell.instantOrSorcery
    | .cast p spell _ _ _ _ _ _, .youCastNoncreature =>
      you p && !spell.creature
    | .cast p spell _ _ _ _ _ _, .youCastCreature =>
      you p && spell.creature
    | .cast p _ _ _ _ _ _ _, .youCastSpell => you p
    | .cast p _ _ _ _ _ _ _, .youCastColor _ => you p
    | .cast p _ (.hand _) _ _ _ _ _, .youCastColorFromHand _ => you p
    | .cast p _ _ _ _ _ _ _, .youCastGreen => you p
    | .cast p spell _ _ _ _ _ _, .youCastVillain => you p && spell.villain
    | .cast p _ _ _ _ _ _ _, .opponentCastsSpell => !you p
    | .cast p spell _ _ _ _ _ _, .youCastFirstNoncreature => you p && !spell.creature
    | .cast p _ _ _ _ _ _ _, .youCastSecondSpell => you p
    | .cast _ _ _ _ _ _ _ _, .anyPlayerCastsSecondSpell => true
    | .cast p _ _ _ _ _ _ _, .opponentCastsFirstNoncreature => !you p
    | .cast p spell _ _ _ _ _ _, .fra .castThis => you p && this spell
    | .attacked p attacker _, .attacking => you p && this attacker
    | .attacked p _ _, .youAttack => you p
    | .attacked p attacker _, .youAttackWithElves => you p && attacker.elf
    | .attacked p _ _, .youAttackWithTwoOrMore => you p
    | .attacked p attacker _, .creatureYouControlAttacksAlone =>
      you p && attacker.creature
    | .attacked p _ _, .equippedAttacks => you p
    | .attacked p attacker _, .equippedCreatureYouControlAttacks =>
      you p && attacker.creature
    | .attacked p attacker _, .merfolkAttackPlayer => you p && attacker.merfolk
    | .attacked p attacker _, .fra .creatureYouControlAttacks =>
      you p && attacker.creature
    | .permanent (.tapped object _), .sourceBecomesTapped => this object
    | .permanent (.tapped object _), .creaturesYouControlBecomeTapped =>
      yours object && object.creature
    | .permanent (.tapped object _), .equippedBecomesTapped => object.creature
    | .permanent (.tapped object during), .creatureYouControlTapped =>
      yours object && object.creature && during
    | .effectApplied _ (.looked p _ false asked), .youScry => you p && asked > 0
    | .effectApplied _ (.looked p _ _ asked), .youScryOrSurveil => you p && asked > 0
    | .permanent (.counters (.object _) .plusOnePlusOne (.put n) (some p)), .youPutPlusOne =>
      you p && n > 0
    | .permanent (.counters (.object object) _ (.put n) (some p)), .youPutCountersOnGoblinOrcArmy =>
      you p && n > 0 && object.goblinOrcArmy
    | .permanent (.counters (.object object) .plan (.put n) _), .nthPlanCounter _ =>
      this object && n > 0
    | .permanent (.counters (.object object) .lore (.put n) _), .sagaChapter =>
      this object && n > 0
    | .stepped .upkeep active, .yourUpkeep => you active
    | .stepped .upkeep _, .eachUpkeep => true
    | .stepped .upkeep _, .fra .eachUpkeepFromGraveyard => true
    | .stepped .end active, .yourEndStep => you active
    | .stepped .end _, .eachEndStep => true
    | .stepped .beginningOfCombat active, .yourBeginCombat => you active
    | .stepped .beginningOfCombat active, .fra .yourBeginCombatFromGraveyard => you active
    | .stepped .beginningOfCombat _, .eachBeginCombat => true
    | .stepped .beginningOfCombat active, .fra .opponentBeginCombat => !you active
    | .stepped .precombatMain active, .yourFirstMain => you active
    | .stepped .draw active, .eachOpponentDrawStep => !you active
    | .stepped .upkeep _, .eaglesCreateBirds => true
    | .stepped .upkeep active, .enchantedControllerUpkeep => you active
    | .effectApplied _ (.sacrificed p object), .youSacrificeToken => you p && object.token
    | .activated p _ true _, .youActivateLoyaltyAbility => you p
    | .activated p source false _, .youActivateCreatureAbility =>
      you p && source.creature
    | .activated p _ true _, .fra .opponentActivatesLoyaltyAbility => !you p
    | .effectApplied _ (.created p object), .fra .youCreateCreatureTokens => you p && object.creature
    | _, _ => false

/-- Cards `p` drew on `turn` in `events`. -/
def draws (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.effectApplied _ (.drew q _ _ _)) => if q == p then n + 1 else n
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
      | .rules (.cast q _ _ _ _ _ _ _) => if q == p then n + 1 else n
      | _ => n) 0

/-- `p` scried at least one card on `turn`. -/
def scried (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .rules (.effectApplied _ (.looked q _ false asked)) => q == p && asked > 0
      | _ => false

/-- `p` surveilled on `turn`. Surveil 0 does not count. -/
def surveilled (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .rules (.effectApplied _ (.looked q _ true asked)) => q == p && asked > 0
      | _ => false

/-- An artifact entered under `p`'s control on `turn`. -/
def artifactEntered (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .rules (.effectApplied _ (.moved object _ .battlefield _ _)) =>
        object.controller == some p && object.artifact
      | .rules (.effectApplied _ (.created q object)) => q == p && object.artifact
      | _ => false

/-- `p` attacked with a permanent of `subtype` on `turn`. -/
def attackedWithSubtype (events : Array GameEvent) (turn : Nat) (p : PlayerId)
    (subtype : CardSubtype) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .rules (.attacked q attacker _) => q == p && attacker.hasSubtype subtype
      | _ => false

/-- A permanent of `subtype` entered under `p`'s control on `turn`. -/
def subtypeEntered (events : Array GameEvent) (turn : Nat) (p : PlayerId)
    (subtype : CardSubtype) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .rules (.effectApplied _ (.moved object _ .battlefield _ _)) =>
        object.controller == some p && object.hasSubtype subtype
      | .rules (.effectApplied _ (.created q object)) => q == p && object.hasSubtype subtype
      | _ => false

/-- `p` activated a loyalty ability on `turn`. -/
def activatedLoyalty (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .rules (.activated q _ true _) => q == p
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

/-- Mana recorded for `spell` when it was cast, if the log has that cast. -/
def manaSpentOn (events : Array GameEvent) (spell : ObjectId) : Nat :=
  events.foldl (fun n e =>
    match e.change with
    | .rules (.cast _ s _ _ spent _ _ _) => if s.id == spell then max n spent else n
    | _ => n) 0

/-- Same event, naming the object id it has after the zone change (CR 400.7). -/
def withObjectId (e : GameEvent) (id : ObjectId) : GameEvent :=
  match e.change with
  | .rules (.effectApplied eid (.moved object fromZone toZone sacrificed discarded)) =>
    { e with change := .rules (.effectApplied eid (.moved { object with id := id } fromZone toZone sacrificed discarded)) }
  | .rules (.effectApplied eid (.created player object)) =>
    { e with change := .rules (.effectApplied eid (.created player { object with id := id })) }
  | _ => e

/-- Creature spells `p` cast on `turn`. -/
def creatureSpells (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.cast q spell _ _ _ _ _ _) => if q == p && spell.creature then n + 1 else n
      | _ => n) 0

/-- Noncreature spells `p` cast on `turn`. -/
def noncreatureSpells (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.cast q spell _ _ _ _ _ _) => if q == p && !spell.creature then n + 1 else n
      | _ => n) 0

/-- Creatures `p` attacked with on `turn`. -/
def attacks (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.attacked q _ _) => if q == p then n + 1 else n
      | _ => n) 0

/-- Cards that moved from `p`'s library to `p`'s graveyard on `turn`. -/
def milled (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.effectApplied _ (.moved _ (.library owner) (.graveyard q) _ _)) =>
        if owner == p && q == p then n + 1 else n
      | _ => n) 0

/-- `p` has already drawn the first card of their draw step on `turn`. -/
def drewFirstOfDrawStep (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .rules (.effectApplied _ (.drew q _ _ true)) => q == p
      | _ => false

/-- Equip abilities `p` completed on `turn`. -/
def equipActivations (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.activated q _ _ true) => if q == p then n + 1 else n
      | _ => n) 0

/-- Mana values of spells `p` cast on `turn`, oldest first. Copies are absent. -/
def castManaValues (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Array Nat :=
  events.foldl (fun acc e =>
    if e.turn != turn then acc
    else
      match e.change with
      | .rules (.cast q _ _ mv _ _ _ _) => if q == p then acc.push mv else acc
      | _ => acc) #[]

/-- Cards `p` discarded on `turn`. A discard is a card moving from that
player's hand to their graveyard. -/
def discards (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.effectApplied _ (.moved _ (.hand q) (.graveyard r) _ true)) => if q == p && q == r then n + 1 else n
      | _ => n) 0

/-- Life `p` lost on `turn`, including life lost to damage. -/
def lifeLost (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.life (.lost q amount _ _)) => if q == p then n + amount else n
      | _ => n) 0

/-- Counted resolutions for `p` on `turn`. -/
def resolutions (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.effectApplied _ (.resolved q _)) => if q == p then n + 1 else n
      | _ => n) 0

/-- Lands `p` played on `turn`. -/
def landsPlayed (events : Array GameEvent) (turn : Nat) (p : PlayerId) : Nat :=
  events.foldl (fun n e =>
    if e.turn != turn then n
    else
      match e.change with
      | .rules (.playedLand q _) => if q == p then n + 1 else n
      | _ => n) 0

/-- Graveyard ids of creatures that moved from the battlefield to a graveyard
on `turn`. The id is the one the card has after it arrives (CR 400.7). -/
def creaturesToGraveyard (events : Array GameEvent) (turn : Nat) : Array ObjectId :=
  events.foldl (fun acc e =>
    if e.turn != turn then acc
    else
      match e.change with
      | .rules (.effectApplied _ (.moved object .battlefield (.graveyard _) _ _)) =>
        if object.creature then acc.push object.id else acc
      | _ => acc) #[]

/-- Graveyard id of the most recent attacking creature that died. -/
def lastDiedAttacker (events : Array GameEvent) : Option ObjectId :=
  events.foldl (fun acc e =>
    match e.change with
    | .rules (.effectApplied _ (.moved object .battlefield (.graveyard _) _ _)) =>
      if object.creature && object.attacking then some object.id else acc
    | _ => acc) none

/-- Id of the permanent that most recently became tapped. -/
def lastBecameTapped (events : Array GameEvent) : Option ObjectId :=
  events.foldl (fun acc e =>
    match e.change with
    | .rules (.permanent (.tapped object _)) => some object.id
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
      | .rules (.effectApplied _ (.sheHulkDealtDamage _)) => true
      | _ => false

/-- `id` entered the battlefield on `turn`. -/
def objectEntered (events : Array GameEvent) (turn : Nat) (id : ObjectId) : Bool :=
  events.any fun e =>
    e.turn == turn &&
      match e.change with
      | .rules (.effectApplied _ (.moved object _ .battlefield _ _)) => object.id == id
      | .rules (.effectApplied _ (.created _ object)) => object.id == id
      | _ => false

/-- The cast of `spell` was from a graveyard. -/
def castFromGraveyard (events : Array GameEvent) (spell : ObjectId) : Bool :=
  events.any fun e =>
    match e.change with
    | .rules (.cast _ s _ _ _ true _ _) => s.id == spell
    | _ => false

/-- A gift was promised as `spell` was cast. -/
def giftPromised (events : Array GameEvent) (spell : ObjectId) : Bool :=
  events.any fun e =>
    match e.change with
    | .rules (.cast _ s _ _ _ _ _ true) => s.id == spell
    | _ => false

/-- `spell` was cast using teamwork. -/
def teamwork (events : Array GameEvent) (spell : ObjectId) : Bool :=
  events.any fun e =>
    match e.change with
    | .rules (.cast _ s _ _ _ _ true _) => s.id == spell
    | _ => false

/-- `id` entered from a spell cast for its impending cost (CR 702.176,
ruling 970). -/
def castForImpending (events : Array GameEvent) (id : ObjectId) : Bool :=
  events.any fun e =>
    match e.change with
    | .rules (.effectCreated _ (.notACreature oid)) => oid == id
    | _ => false

/-- All one-shot effects applied in `events` with their `EffectId`s, in chronological order (CR 610). -/
def appliedEffectsWithId (events : Array GameEvent) : Array (EffectId × OneShotEffect) :=
  events.foldl (fun acc e =>
    match e.change with
    | .rules (.effectApplied id eff) => acc.push (id, eff)
    | _ => acc) #[]

/-- All one-shot effects applied in `events`, in chronological order (CR 610). -/
def appliedEffects (events : Array GameEvent) : Array OneShotEffect :=
  (appliedEffectsWithId events).map Prod.snd

/-- All continuous effects created in `events` with their `EffectId`s, in chronological order (CR 611). -/
def createdEffectsWithId (events : Array GameEvent) : Array (EffectId × ContinuousEffect) :=
  events.foldl (fun acc e =>
    match e.change with
    | .rules (.effectCreated id eff) => acc.push (id, eff)
    | _ => acc) #[]

/-- All continuous effects created in `events`, in chronological order (CR 611). -/
def createdEffects (events : Array GameEvent) : Array ContinuousEffect :=
  events.foldl (fun acc e =>
    match e.change with
    | .rules (.effectCreated _ eff) => acc.push eff
    | _ => acc) #[]

/-- All continuous effects that expired in `events` with their `EffectId`s, in chronological order (CR 611). -/
def expiredEffectsWithId (events : Array GameEvent) : Array (EffectId × ContinuousEffect) :=
  events.foldl (fun acc e =>
    match e.change with
    | .rules (.effectExpired id eff) => acc.push (id, eff)
    | _ => acc) #[]

/-- All continuous effects that expired in `events`, in chronological order (CR 611). -/
def expiredEffects (events : Array GameEvent) : Array ContinuousEffect :=
  events.foldl (fun acc e =>
    match e.change with
    | .rules (.effectExpired _ eff) => acc.push eff
    | _ => acc) #[]

end GameEvent

end Mtg.Engine
