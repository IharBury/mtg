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
(CR 113.7a). Subtypes include those granted at that moment.
Note: `colors`, `manaValue`, `types`, `subtypes`, `power`, `toughness`,
`keywords`, and `staticAbilities` are provisional until the Layer 1–7 pipeline
in Phase 8 (CR 613.1). -/
structure EventObject where
  id              : Option ObjectId      := none
  controller      : Option PlayerId      := none
  owner           : PlayerId             := ⟨0⟩
  -- characteristics (CR 109.3)
  name            : String               := ""
  /-- Provisional until Layer 5 in Phase 8 (CR 613.1e). -/
  colors          : ColorSet             := {}
  manaValue       : Nat                  := 0
  supertypes      : Array Supertype      := #[]
  /-- Provisional until Layer 4 in Phase 8 (CR 613.1d). -/
  types           : Array CardType       := #[]
  /-- Provisional until Layer 4 in Phase 8 (CR 613.1d). -/
  subtypes        : Array CardSubtype    := #[]
  /-- Provisional until Layer 7 in Phase 8 (CR 613.4). -/
  power           : Option Int           := none
  /-- Provisional until Layer 7 in Phase 8 (CR 613.4). -/
  toughness       : Option Int           := none
  loyalty         : Option Nat           := none
  /-- Provisional until Layer 6 in Phase 8 (CR 613.1f). -/
  keywords        : Keywords             := {}
  toxic           : Nat                  := 0
  /-- Provisional until Layer 6 in Phase 8 (CR 613.1f). -/
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
  -- Arrival status, printed card, and stack-copy metadata carried so
  -- `applyZoneEvent` reconstructs the `GameObject` without a follow-up `setObject`.
  summoningSick      : Bool                        := false
  attackingWhom      : Option PlayerId             := none
  returnedAsArtifact : Bool                        := false
  onlyFoodArtifact   : Bool                        := false
  wasCast            : Bool                        := false
  printed            : Option CardDef              := none
  chosenX            : Option Nat                  := none
  kicked             : Bool                        := false
  teamworkPaid       : Bool                        := false
  sneakPaid          : Bool                        := false
  sneakAttackWhom    : Option PlayerId             := none
  giftPromisedTo     : Option PlayerId             := none
  adventurerCard     : Option CardDef              := none
  abilityEffect      : Option Effect               := none
  triggeredAbility   : Option TriggeredAbility     := none
  sourceId           : Option ObjectId             := none
  lastKnownPower     : Option Int                  := none
  lastKnownToughness : Option Int                  := none
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

/-- This object as it is now, for a `GameEvent` (CR 113.7a).
Note: layer-dependent fields (`colors`, `types`, `subtypes`, `power`,
`toughness`, `keywords`, `staticAbilities`) are provisional until Phase 8 when
read without `Game`; prefer `Game.snapshot` when `Game` is in scope. -/
def GameObject.asEvent (o : GameObject) : EventObject :=
  { id := some o.id
    controller := o.controller
    owner := o.owner
    name := o.printed.name
    colors := o.printed.colors
    manaValue := o.printed.manaValue + o.chosenX.getD 0
    supertypes := o.supertypes
    types := o.types
    subtypes := o.subtypes
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
    attackingWhom := o.status.attackingWhom
    returnedAsArtifact := o.status.returnedAsArtifact
    onlyFoodArtifact := o.status.onlyFoodArtifact
    wasCast := o.wasCast
    printed := some o.printed
    chosenX := o.chosenX
    kicked := o.kicked
    teamworkPaid := o.teamworkPaid
    sneakPaid := o.sneakPaid
    sneakAttackWhom := o.sneakAttackWhom
    giftPromisedTo := o.giftPromisedTo
    adventurerCard := o.adventurerCard
    abilityEffect := o.abilityEffect
    triggeredAbility := o.triggeredAbility
    sourceId := o.sourceId
    lastKnownPower := o.lastKnownPower
    lastKnownToughness := o.lastKnownToughness }

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
  | removedFromCombat (object : EventObject)                                 -- 506.4 / 511.3 / 702.26b
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
  /-- Combat damage assigned by attacking (`forAttackers`) or blocking creatures
  (CR 510.1 / 510.4 / 703.4k). -/
  | combatAssigned (forAttackers : Bool) (assignments : Array CreatureCombatAssignment)
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

/-- Player-level actions that don't mutate a single object's zone, status, life,
or damage (CR 701.22, 701.25, 701.34, 701.62). -/
inductive PlayerEvent where
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
  /-- `player` beheld `quality` (CR 701.62). Later zone changes do not undo it. -/
  | beheld (player : PlayerId) (quality : CardSubtype)
  /-- `player` proliferated (CR 701.34). Each counter added also emits its own
  `PermanentEvent.counters` event. -/
  | proliferated (player : PlayerId) (permanents : Array ObjectId := #[])
      (players : Array PlayerId := #[])
  /-- `player` chose to have The Sensational She-Hulk deal damage. Once each turn. -/
  | sheHulkDealtDamage (player : PlayerId)
  /-- `player`'s mana pool emptied (CR 500.5 / 703.4q). `amount` is the mana
  that was in the pool; `keptColorless` is true when unspent mana became
  colorless instead of emptying. -/
  | manaEmptied (player : PlayerId) (amount : Nat := 0) (keptColorless : Bool := false)
  /-- `player` lost the game (CR 104.3 / 704.5a–c). -/
  | lost (player : PlayerId)
  /-- `player` left the game (CR 104.5 / 800.4a). -/
  | leftGame (player : PlayerId)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Stack-object events (CR 608). -/
inductive StackObjectEvent where
  /-- `obj` resolved (`nth` time this ability resolved for its controller this turn, CR 608). -/
  | resolved (obj : EventObject) (nth : Nat := 1)
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
  /-- Stack-object resolution events. -/
  | stackObject (e : StackObjectEvent)
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
  /-- A continuous effect begins (CR 611). -/
  | effectCreated (id : EffectId) (effect : ContinuousEffect)
  /-- A continuous effect ends (CR 611). -/
  | effectExpired (id : EffectId) (effect : ContinuousEffect)
  /-- Bookkeeping on an existing continuous effect `id` (a decremented turn
  counter, or last-known information after its source left), keeping the same
  `EffectId`. This neither creates nor ends an effect (CR 611). -/
  | effectUpdated (id : EffectId) (effect : ContinuousEffect)
deriving Repr, Inhabited, BEq

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
  | resolvingSpell (v : Option ObjectId)
  | resolvingAbility (v : Option ObjectId)
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
  | delayedEndStepReturns (v : Array (ObjectId × EventCause))
  | pushDelayedEndStepReturn (id : ObjectId) (cause : EventCause)
  | extraTurns (v : Array PlayerId)
  | extraTurnCauses (v : Array EventCause)
  | pushExtraTurn (p : PlayerId) (cause : Option EventCause := none)
  | powerUpsForbidden (v : Bool)
  | delayedEndStepExiles (v : Array (ObjectId × EventCause))
  | pushDelayedEndStepExile (id : ObjectId) (cause : EventCause)
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
  | delayedEndStepSacrifices (v : Array (ObjectId × EventCause))
  | pushDelayedEndStepSacrifice (id : ObjectId) (cause : EventCause)
  | delayedGraveReturns (v : Array (ObjectId × PlayerId × EventCause))
  | pushDelayedGraveReturn (id : ObjectId) (p : PlayerId) (cause : EventCause)
  | delayedSynthetic (v : Array (PlayerId × Nat × EventCause))
  | pushDelayedSynthetic (p : PlayerId) (n : Nat) (cause : EventCause)
  | eaglesBirdsCauses (v : Array (PlayerId × Nat × EventCause))
  | pushEaglesBirdsCause (p : PlayerId) (n : Nat) (cause : EventCause)
  | linkedExileCauses (v : Array (ObjectId × EventCause))
  | setLinkedExileCause (id : ObjectId) (cause : Option EventCause)
  | untapSearchedIfLands (v : Option Nat)
  | pendingCreatureTokenCreators (v : Array PlayerId)
  | pushPendingCreatureTokenCreator (p : PlayerId)
  | ancestryLandsTapped (v : Array ObjectId)
  | pushAncestryLandTapped (id : ObjectId)
  | removeAncestryLandTapped (id : ObjectId)
  | resolvingContext (v : Option (Option ObjectId × PlayerId))
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

/-- Route a `RulesEvent` with an optional `EventCause` through `rules`,
defaulting `none` to `.unclassified` (upgraded to `.oneShotEffect` by
`applyEvent` when a spell or ability is actively resolving). -/
def rulesOrUnclassified (turn : Nat) (e : RulesEvent)
    (cause : Option EventCause := none) (batch : BatchId := ⟨0⟩) : GameEvent :=
  rules turn e (cause.getD .unclassified) batch

/-- Construct an internal `EngineChange` event. -/
def engine (turn : Nat) (c : EngineChange) (batch : BatchId := ⟨0⟩) : GameEvent :=
  unclassified turn (.engine c) batch

/-- `object` moved from `fromZone` to `toZone` (CR 400.6 / 400.7). -/
def moved (turn : Nat) (before : EventObject) (fromZone toZone : Zone)
    (sacrificed : Bool := false) (discarded : Bool := false)
    (after : Option EventObject := none)
    (verb : Option ZoneVerb := none)
    (actor : Option PlayerId := none)
    (entersWith : CounterBag := #[])
    (libraryPosition : Option LibraryPosition := none)
    (cause : Option EventCause := none) : GameEvent :=
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
      if sacrificed then before.controller.orElse (fun _ => some before.owner)
      else if discarded then
        match fromZone with
        | .hand p => some p
        | _ => some before.owner
      else none
  rulesOrUnclassified turn
    (.zone (.moved beforeObj afterObj fromZone toZone v actor' entersWith libraryPosition))
    cause

/-- `player` drew `card` as the `nth` card this turn (CR 121.1 / 400.7). -/
def drew (turn : Nat) (player : PlayerId) (card : ObjectId) (nth : Nat)
    (firstOfOwnDrawStep : Bool := false)
    (before : Option EventObject := none)
    (after : Option EventObject := none)
    (cause : Option EventCause := none) : GameEvent :=
  let b := before.getD { id := some card, owner := player, zone := .library player }
  let a := after.getD { b with id := some card, owner := player, zone := .hand player }
  rulesOrUnclassified turn
    (.zone (.moved b a (.library player) (.hand player) (.draw nth firstOfOwnDrawStep) (some player)))
    cause

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

/-- Combat damage was assigned by attacking (`forAttackers`) or blocking
creatures (CR 510.1 / 510.4 / 703.4k). -/
def combatDamageAssigned (turn : Nat) (forAttackers : Bool)
    (assignments : Array CreatureCombatAssignment)
    (firstStrike : Bool := false)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.damage (.combatAssigned forAttackers assignments))
    (cause.getD (.turnBased (.assignCombatDamage firstStrike)))

/-- `player` cast `spell` (CR 601.2i). -/
def cast (turn : Nat) (player : PlayerId) (spell : EventObject) (fromZone : Zone)
    (manaValue : Nat := 0) (manaSpent : Nat := 0)
    (fromGraveyard : Bool := false) (teamwork : Bool := false) (gift : Bool := false)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.cast player spell fromZone manaValue manaSpent fromGraveyard teamwork gift)
    (cause.getD (.gameRule .spellCast))

/-- `player` attacked `whom` with `attacker` (CR 508.1). -/
def attacked (turn : Nat) (player : PlayerId) (attacker : EventObject) (whom : PlayerId)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.attacked player attacker whom)
    (cause.getD (.turnBased .declareAttackers))

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
    (asked : Nat := n) (id : Option EffectId := none)
    (top : Array ObjectId := #[]) (rest : Array ObjectId := #[])
    (cause : Option EventCause := none) : GameEvent :=
  let ev : PlayerEvent :=
    if surveil then .surveilled player top rest n asked
    else .scried player top rest n asked
  rules turn (.player ev) (cause.getD (.oneShotEffect id none (some player)))

/-- `player` sacrificed `object` (CR 701.21 / 400.7). -/
def sacrificed (turn : Nat) (player : PlayerId) (object : EventObject)
    (cause : Option EventCause := none) : GameEvent :=
  let before := { object with zone := .battlefield }
  let after := { object with zone := .graveyard object.owner, controller := none }
  rulesOrUnclassified turn
    (.zone (.moved before after .battlefield (.graveyard object.owner) .sacrifice (some player)))
    cause

/-- `player` created `object` (CR 111 / 701.7 / 707.10). -/
def created (turn : Nat) (player : PlayerId) (object : EventObject)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.zone (.created object player)) cause

/-- `object` ceased to exist (CR 704.5d / 704.5e / 111.8). -/
def ceasedToExist (turn : Nat) (object : EventObject)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.zone (.ceasedToExist object)) cause

/-- `object` changed controller from `fromPlayer` to `toPlayer` (CR 110.2 / 613.1b). -/
def control (turn : Nat) (object : ObjectId) (fromPlayer toPlayer : PlayerId)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.permanent (.controlChanged { id := some object } fromPlayer toPlayer)) cause

/-- The step or phase changed (CR 500.1). -/
def stepped (turn : Nat) (step : Step) (active : PlayerId)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.stepped step active) (cause.getD (.gameRule .stepAdvance))

/-- `player` activated an ability of `source` (CR 602.2). `equip` is set when the
activation has been completed, so a proposal still being paid does not count. -/
def activated (turn : Nat) (player : PlayerId) (source : EventObject)
    (loyalty : Bool := false) (equip : Bool := false)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.activated player source loyalty equip)
    (cause.getD (.gameRule .abilityActivated))

/-- `player` played `land` (CR 116.2a / 305.1). -/
def playedLand (turn : Nat) (player : PlayerId) (land : EventObject)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.playedLand player land) (cause.getD (.specialAction .playLand player))

/-- The `nth` counted resolution for `player` this turn (CR 608 / 610.1). -/
def resolved (turn : Nat) (player : PlayerId) (nth : Nat)
    (id : Option EffectId := none) (obj : Option EventObject := none)
    (cause : Option EventCause := none) : GameEvent :=
  let evObj := obj.getD { controller := some player, owner := player, zone := .stack }
  rules turn (.stackObject (.resolved evObj nth))
    (cause.getD (.oneShotEffect id evObj.id (some player)))

/-- `object` became attached to `host` (CR 701.3a / 303.4 / 301.5). -/
def attached (turn : Nat) (object host : ObjectId)
    (previous : Option ObjectId := none)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.permanent (.attached { id := some object } host previous)) cause

/-- `attachment` became unattached from `fromHost` (CR 701.3d / 704.5n / 704.5p). -/
def unattached (turn : Nat) (attachment : EventObject) (fromHost : ObjectId)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.permanent (.unattached attachment fromHost)) cause

/-- `object` gained or lost designation `d` (CR 110.6 / 701.15b / 701.54a / 903.3). -/
def designation (turn : Nat) (object : EventObject) (d : PermanentDesignation)
    (gained : Bool := true) (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.permanent (.designation object d gained)) cause

/-- `object` phased out (CR 702.26b / 702.26g). -/
def phasedOut (turn : Nat) (object : EventObject) (indirectly : Bool := false)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.permanent (.phasedOut object indirectly)) cause

/-- `object` phased in (CR 702.26c / 702.26g). -/
def phasedIn (turn : Nat) (object : EventObject) (indirectly : Bool := false)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.permanent (.phasedIn object indirectly)) cause

/-- `object` transformed (CR 701.27a / 712.18). -/
def transformed (turn : Nat) (object : EventObject) (nowBackFace : Bool)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.permanent (.transformed object nowBackFace)) cause

/-- `object` was turned face up (CR 701.40b / 708.8). -/
def turnedFaceUp (turn : Nat) (object : EventObject)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.permanent (.turnedFaceUp object)) cause

/-- `object` was turned face down (CR 701.40f / 708.2). -/
def turnedFaceDown (turn : Nat) (object : EventObject)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.permanent (.turnedFaceDown object)) cause

/-- `player` beheld `quality` (CR 701.62). -/
def beheld (turn : Nat) (player : PlayerId) (quality : CardSubtype)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.player (.beheld player quality)) cause

/-- `player` spent mana (CR 118.3). -/
def spentMana (turn : Nat) (player : PlayerId) (amount : Nat)
    (forObject : Option ObjectId := none)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.spentMana player amount)
    (cause.getD (.costPayment .mana player forObject))

/-- `player` got poison counters (CR 122.1c). -/
def poisoned (turn : Nat) (player : PlayerId) (n : Nat)
    (byPlayer : Option PlayerId := none)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.permanent (.counters (.player player) .poison (.put n) byPlayer)) cause

/-- `player` proliferated (CR 701.34 / 610.1). -/
def proliferated (turn : Nat) (player : PlayerId)
    (id : Option EffectId := none)
    (permanents : Array ObjectId := #[]) (players : Array PlayerId := #[])
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.proliferated player permanents players))
    (cause.getD (.oneShotEffect id none (some player)))

/-- `player` chose to have The Sensational She-Hulk deal damage (CR 610.1). -/
def sheHulkDealtDamage (turn : Nat) (player : PlayerId)
    (id : Option EffectId := none) (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.sheHulkDealtDamage player))
    (cause.getD (.oneShotEffect id none (some player)))

/-- `object` untapped, or a stun counter replaced that untap (CR 701.26b / 122.1d). -/
def untapped (turn : Nat) (object : EventObject) (replacedByStun : Bool := false)
    (cause : Option EventCause := none) : GameEvent :=
  if replacedByStun then
    rulesOrUnclassified turn (.permanent (.counters (.object object) .stun (.removed 1) none)) cause
  else
    rulesOrUnclassified turn (.permanent (.untapped object)) cause

/-- `object` was removed from combat (CR 506.4 / 511.3 / 702.26b). -/
def removedFromCombat (turn : Nat) (object : EventObject)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.permanent (.removedFromCombat object)) cause

/-- `player`'s mana pool emptied (CR 500.5 / 703.4q). -/
def manaEmptied (turn : Nat) (player : PlayerId)
    (amount : Nat := 0) (keptColorless : Bool := false)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.manaEmptied player amount keptColorless))
    (cause.getD (.turnBased .emptyManaPools))

/-- `player` lost the game (CR 104.3 / 704.5a–c). -/
def playerLost (turn : Nat) (player : PlayerId)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.player (.lost player)) cause

/-- `player` left the game (CR 104.5 / 800.4a). -/
def playerLeftGame (turn : Nat) (player : PlayerId)
    (cause : Option EventCause := none) : GameEvent :=
  rules turn (.player (.leftGame player))
    (cause.getD (.gameRule .playerLeftGame))

/-- A continuous effect begins (CR 611). -/
def effectCreated (turn : Nat) (id : EffectId) (effect : ContinuousEffect)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.effectCreated id effect) cause

/-- A continuous effect ends (CR 611). -/
def effectExpired (turn : Nat) (id : EffectId) (effect : ContinuousEffect)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.effectExpired id effect) cause

/-- Bookkeeping on an existing continuous effect `id` (CR 611). -/
def effectUpdated (turn : Nat) (id : EffectId) (effect : ContinuousEffect)
    (cause : Option EventCause := none) : GameEvent :=
  rulesOrUnclassified turn (.effectUpdated id effect) cause

/-- Same event, sent to `toZone` instead. Used after a zone replacement (CR 614.6). -/
def withDestination (e : GameEvent) (toZone : Zone) (discarded : Bool) : GameEvent :=
  match e.change with
  | .rules (.zone (.moved before after fromZone origTo verb actor entersWith libPos)) =>
    let verb' :=
      if toZone != origTo && toZone == .exile then .exile
      else if discarded then .discard
      else if verb == .discard && !discarded then .put
      else verb
    let after' := { after with
      zone := toZone
      controller := if toZone == .battlefield || toZone == .stack then after.controller else none
      tapped := if toZone == .battlefield then after.tapped else false
      counters := if toZone == .battlefield then after.counters else #[] }
    let entersWith' := if toZone == .battlefield then entersWith else #[]
    { e with change := .rules (.zone (.moved before after' fromZone toZone verb' actor entersWith' libPos)) }
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
    | .rules (.zone (.created object _)) => object.token
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
    | .damage (.dealt pkts), .dealsCombatDamageToPlayerOrBattle =>
      pkts.any (fun pkt => pkt.combat && match pkt.recipient with | .player _ | .battle _ => true | _ => false)
    | .damage (.dealt pkts), .combatDamageToYou =>
      pkts.any (fun pkt => pkt.combat && match pkt.recipient with | .player p => you p | _ => false)
    | .damage (.dealt pkts), .heroesDealDamageToPlayer =>
      pkts.any (fun pkt =>
        match pkt.recipient with
        | .player _ => yours pkt.source && pkt.source.hero
        | _ => false)
    | .zone (.moved before _ .battlefield (.graveyard _) _ _ _ _), .dying =>
      this before && before.creature
    | .zone (.moved before _ .battlefield _ _ _ _ _), .leaving => this before
    | .zone (.moved before after _ .battlefield _ _ _ _), .entering => this after || this before
    | .zone (.moved _ after _ .battlefield _ _ _ _), .landYouControlEnters =>
      yours after && after.land
    | .zone (.moved _ after _ .battlefield _ _ _ _), .forestYouControlEnters =>
      yours after && after.forest
    | .zone (.moved _ after _ .battlefield _ _ _ _), .mountainYouControlEnters =>
      yours after && after.mountain
    | .zone (.moved _ after _ .battlefield _ _ _ _), .artifactYouControlEnters =>
      yours after && after.artifact
    | .zone (.moved _ after _ .battlefield _ _ _ _), .creatureYouControlEnters =>
      yours after && after.creature
    | .zone (.moved _ after _ .battlefield _ _ _ _), .anotherCreatureYouControlEnters =>
      yours after && other after && after.creature
    | .zone (.moved _ after _ .battlefield _ _ _ _), .anotherElfYouControlEnters =>
      yours after && other after && after.elf
    | .zone (.moved _ after _ .battlefield _ _ _ _), .tokenYouControlEnters =>
      yours after && after.token
    | .zone (.moved _ after _ .battlefield _ _ _ _), .equipmentYouControlEnters =>
      yours after && after.equipment
    | .zone (.moved _ after _ .battlefield _ _ _ _), .anotherArtifactEnters =>
      yours after && other after && after.artifact
    | .zone (.moved _ after _ .battlefield _ _ _ _), .anotherVillainEnters =>
      yours after && other after && after.villain
    | .zone (.moved _ after _ .battlefield _ _ _ _), .anotherVillainOrArtifactEnters =>
      yours after && other after && (after.villain || after.artifact)
    | .zone (.moved _ after _ .battlefield _ _ _ _), .anotherNontokenHeroEnters =>
      yours after && other after && !after.token && after.hero
    | .zone (.moved _ after _ .battlefield _ _ _ _), .anotherNontokenArtifactEnters =>
      yours after && other after && !after.token && after.artifact
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
    | .zone (.moved _ _ (.hand p) (.graveyard q) .discard _ _ _), .youDiscard =>
      you p && p == q
    | .zone (.moved before after (.hand p) (.graveyard q) .discard _ _ _), .fra .youDiscardThis =>
      you p && p == q && (this before || this after)
    | .zone (.moved _ _ (.hand p) (.graveyard q) .discard _ _ _), .fra .youDiscardOne =>
      you p && p == q
    | .zone (.moved _ _ (.hand p) (.graveyard q) .discard _ _ _), .fra .playerDiscards =>
      p == q
    | .zone (.moved before _ .battlefield (.graveyard _) _ _ _ _), .fra .enchantedDies =>
      before.creature
    | .zone (.moved before _ .battlefield (.graveyard _) _ _ _ _), .fra .nontokenCreatureYouControlDies =>
      yours before && before.creature && !before.token
    | .zone (.moved before _ .battlefield (.graveyard _) _ _ _ _), .fra .anotherCreatureOrPlaneswalkerYouControlDies =>
      yours before && other before && (before.creature || before.planeswalker)
    | .zone (.moved before _ .battlefield _ _ _ _ _), .fra .creatureYouControlLeaves =>
      yours before && other before && before.creature
    | .zone (.moved _ after _ .battlefield _ _ _ _), .subtypeYouControlEnters sub =>
      yours after && after.hasSubtype sub
    | .zone (.moved before after _ .battlefield _ _ entersWith _), .sagaChapter =>
      (this after || this before) && entersWith.count .lore > 0
    | .zone (.moved before after _ .battlefield _ _ entersWith _), .nthPlanCounter _ =>
      (this after || this before) && entersWith.count .plan > 0
    | .zone (.moved _ after _ .battlefield _ actor entersWith _), .youPutPlusOne =>
      let p := actor.orElse (fun _ => after.controller)
      p.any you && entersWith.count .plusOnePlusOne > 0
    | .zone (.moved _ after _ .battlefield _ actor entersWith _), .youPutCountersOnGoblinOrcArmy =>
      let p := actor.orElse (fun _ => after.controller)
      p.any you && entersWith.any (fun (_, n) => n > 0) && after.goblinOrcArmy
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
    | .player (.scried p _ _ _ asked), .youScry => you p && asked > 0
    | .player (.scried p _ _ _ asked), .youScryOrSurveil => you p && asked > 0
    | .player (.surveilled p _ _ _ asked), .youScryOrSurveil => you p && asked > 0
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
    | .zone (.moved before _ .battlefield (.graveyard owner) .sacrifice actor _ _), .youSacrificeToken =>
      let p := actor.getD (before.controller.getD before.owner)
      you p && this before && before.token && owner == before.owner
    | .activated p _ true _, .youActivateLoyaltyAbility => you p
    | .activated p source false _, .youActivateCreatureAbility =>
      you p && source.creature
    | .activated p _ true _, .fra .opponentActivatesLoyaltyAbility => !you p
    | .zone (.created object p), .fra .youCreateCreatureTokens => you p && object.creature
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
      | .rules (.cast q _ _ _ _ _ _ _) => if q == p then n + 1 else n
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
      | .rules (.zone (.created object q)) => q == p && object.artifact
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
      | .rules (.zone (.moved _ after _ .battlefield _ _ _ _)) =>
        after.controller == some p && after.hasSubtype subtype
      | .rules (.zone (.created object q)) => q == p && object.hasSubtype subtype
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
    | .rules (.cast _ s _ _ spent _ _ _) => if s.id == some spell then max n spent else n
    | _ => n) 0

/-- Same event, naming the object id it has after the zone change (CR 400.7). -/
def withObjectId (e : GameEvent) (id : ObjectId) : GameEvent :=
  match e.change with
  | .rules (.zone (.moved before after fromZone toZone verb actor entersWith libPos)) =>
    { e with change := .rules (.zone (.moved before { after with id := some id } fromZone toZone verb actor entersWith libPos)) }
  | .rules (.zone (.created object controller)) =>
    { e with change := .rules (.zone (.created { object with id := some id } controller)) }
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
      | .rules (.zone (.moved _ _ (.hand q) (.graveyard r) .discard _ _ _)) =>
        if q == p && q == r then n + 1 else n
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
      | .rules (.stackObject (.resolved obj _)) =>
        if (obj.controller.getD obj.owner) == p then n + 1 else n
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
      | .rules (.zone (.created object _)) => object.id == some id
      | _ => false

/-- The cast of `spell` was from a graveyard. -/
def castFromGraveyard (events : Array GameEvent) (spell : ObjectId) : Bool :=
  events.any fun e =>
    match e.change with
    | .rules (.cast _ s _ _ _ true _ _) => s.id == some spell
    | _ => false

/-- A gift was promised as `spell` was cast. -/
def giftPromised (events : Array GameEvent) (spell : ObjectId) : Bool :=
  events.any fun e =>
    match e.change with
    | .rules (.cast _ s _ _ _ _ _ true) => s.id == some spell
    | _ => false

/-- `spell` was cast using teamwork. -/
def teamwork (events : Array GameEvent) (spell : ObjectId) : Bool :=
  events.any fun e =>
    match e.change with
    | .rules (.cast _ s _ _ _ _ true _) => s.id == some spell
    | _ => false

/-- `id` entered from a spell cast for its impending cost (CR 702.176,
ruling 970). -/
def castForImpending (events : Array GameEvent) (id : ObjectId) : Bool :=
  events.any fun e =>
    match e.change with
    | .rules (.effectCreated _ (.notACreature oid)) => oid == id
    | _ => false

/-- All rules events caused by a one-shot effect in `events`, paired with their
`EffectId`s, in chronological order (CR 610). -/
def oneShotEffectsWithId (events : Array GameEvent) : Array (EffectId × RulesEvent) :=
  events.foldl (fun acc e =>
    match e.cause.oneShotEffectId?, e.change with
    | some id, .rules r =>
      match r with
      | .effectCreated .. | .effectExpired .. | .effectUpdated .. => acc
      | _ => acc.push (id, r)
    | _, _ => acc) #[]

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
