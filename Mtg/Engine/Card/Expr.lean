import Mtg.Engine.Card.Primitives
import Mtg.Engine.Card.ManaTypes
import Mtg.Engine.Mana
import Mtg.Engine.Card.Text
import Mtg.Engine.Card.Counter

/-!
# Pure Expression Algebra (Layer 1 — CR 107, 109.3, 113, 400.7, 608.2c/h, 611.2)

Pure, side-effect-free expression ASTs evaluated over `(Game, EvalEnv)` (and
`GameSnapshot` / `EventObject` for CR 603.10 / 608.2h last-known information),
anchored to the 6 November 2026 Comprehensive Rules:

- `VarId`, `CmpOp`, `ArithOp`, `AggOp`, `LibraryPosSpec`
- `PlayerFilter` / `PlayerPred` / `PlayerExpr` (11 constructors)
- `ObjectPred` (37 constructors) / `ObjectFilter` / `ObjectExpr` (10 constructors)
- `ValueExpr` (13 constructors)
- `Condition` (14 constructors)
- `DurationExpr` (11 constructors, 1-to-1 with `EffectDuration`)
- `HasTextChange` functorial Layer 3 instances (CR 612.2 / 613.1c)
- `PrintCtx` and `ToOracle` canonical Oracle printers

Every `inductive` in this module stays at < 40 constructors (`< 17%` of the
Lean 4 C runtime `LeanMaxCtorTag = 243` ceiling).
-/

namespace Mtg.Engine

/-- Lexical binding slot for an earlier step's post-replacement outcome
(CR 608.2c / 614.6). -/
structure VarId where
  idx : Nat
deriving DecidableEq, Repr, Inhabited, BEq

/-- Comparison operator for numeric conditions and predicates (CR 107.1). -/
inductive CmpOp where
  | eq | ne | lt | le | gt | ge
deriving DecidableEq, Repr, Inhabited, BEq

namespace CmpOp

/-- Evaluate `op` on two integers. -/
def eval : CmpOp → Int → Int → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .lt, a, b => a < b
  | .le, a, b => a ≤ b
  | .gt, a, b => a > b
  | .ge, a, b => a ≥ b

end CmpOp

/-- Binary arithmetic operator for `ValueExpr.binary` (CR 107.1a). -/
inductive ArithOp where
  | add | sub | mul | divFloor | max | min
deriving DecidableEq, Repr, Inhabited, BEq

namespace ArithOp

/-- Evaluate `op` on two integers. Floor division by zero yields `0` (CR 107.1a). -/
def eval : ArithOp → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .divFloor, a, b => if b == 0 then 0 else Int.fdiv a b
  | .max, a, b => Max.max a b
  | .min, a, b => Min.min a b

end ArithOp

/-- Aggregation operator over an evaluated set of objects (`ValueExpr.aggregate`). -/
inductive AggOp where
  | count | sum | max | min | countDistinct
deriving DecidableEq, Repr, Inhabited, BEq

/-- Numeric object characteristic (CR 109.3 / 202.3 / 208 / 209 / 210). -/
inductive StatKind where
  | power
  | toughness
  | manaValue
  | loyalty
  | defense
deriving DecidableEq, Repr, Inhabited, BEq

namespace StatKind

def oracleWord : StatKind → String
  | .power => "power"
  | .toughness => "toughness"
  | .manaValue => "mana value"
  | .loyalty => "loyalty"
  | .defense => "defense"

def pluralOracleWord : StatKind → String
  | .power => "powers"
  | .toughness => "toughnesses"
  | .manaValue => "mana values"
  | .loyalty => "loyalties"
  | .defense => "defenses"

end StatKind

/-- Per-object numeric metric aggregated by `ValueExpr.aggregate`. -/
inductive ObjectMetric where
  | one
  | stat (kind : StatKind)
  | counterCount (kind? : Option CounterKind := none)
  | colorCount
deriving DecidableEq, Repr, Inhabited, BEq

/-- Subtype category counted by `ValueExpr.subtypeCount` (CR 205.3). -/
inductive SubtypeCategory where
  | any
  | artifact
  | enchantment
  | land
  | basicLand
  | planeswalker
  | spell
  | creature
  | planar
  | dungeon
  | battle
deriving DecidableEq, Repr, Inhabited, BEq

namespace SubtypeCategory

/-- Whether `sub` belongs to `cat` (CR 205.3 / 305.6). -/
def matchesSubtype (cat : SubtypeCategory) (sub : CardSubtype) : Bool :=
  match cat with
  | .any => true
  | .artifact => sub.kind == .artifact
  | .enchantment => sub.kind == .enchantment
  | .land => sub.kind == .land
  | .basicLand =>
    sub == .plains || sub == .island || sub == .swamp || sub == .mountain || sub == .forest
  | .planeswalker => sub.kind == .planeswalker
  | .spell => sub.kind == .spell
  | .creature => sub.kind == .creature
  | .planar => sub.kind == .planar
  | .dungeon => sub.kind == .dungeon
  | .battle => sub.kind == .battle

def oraclePhrase : SubtypeCategory → String
  | .any => "subtypes"
  | .artifact => "artifact types"
  | .enchantment => "enchantment types"
  | .land => "land types"
  | .basicLand => "basic land types"
  | .planeswalker => "planeswalker types"
  | .spell => "spell types"
  | .creature => "creature types"
  | .planar => "planar types"
  | .dungeon => "dungeon types"
  | .battle => "battle types"

end SubtypeCategory

/-- Numeric metric queried on a player (`ValueExpr.playerMetric` / `PlayerPred.metric`). -/
inductive PlayerMetric where
  | one
  | life
  | handSize
  | librarySize
  | graveyardSize
  | landsPlayedThisTurn
  | spellsCastThisTurn
  | cardsDrawnThisTurn
  | cardsDiscardedThisTurn
  | cardsMilledThisTurn
  | otherSpellsManaValueThisTurn
  | lifeGainedThisTurn
  | lifeLostThisTurn
  | unspentMana
  | poisonCounters
  | opponentsCount
deriving DecidableEq, Repr, Inhabited, BEq

/-- Post-replacement numeric outcome read from a bound step (`ValueExpr.stepMetric`, CR 614.6). -/
inductive StepMetric where
  | movedCount
  | createdCount
  | damageDealt
  | excessDamage
  | lifeChanged
  | countersChanged
  | sumPower
  | chosenNumber
deriving DecidableEq, Repr, Inhabited, BEq

/-- Named player role carried by a triggering event (`PlayerExpr.triggerPlayer`). -/
inductive TriggerPlayerRole where
  | actor
  | caster
  | damagedPlayer
  | attackedPlayer
  | targetPlayer
  | controllerOfSubject
  | ownerOfSubject
  | giftOpponent
deriving DecidableEq, Repr, Inhabited, BEq

/-- Relationship of a player to the evaluating controller (CR 102 / 810). -/
inductive PlayerRelation where
  | you
  | opponent
  | teammate
  | anyPlayer
deriving DecidableEq, Repr, Inhabited, BEq

/-- Count / arity range for selections and target slots (CR 115.1 / 601.2c). -/
inductive CountRange where
  | exact (n : Nat)
  | upTo (n : Nat)
  | between (lo hi : Nat)
  | anyNumber
deriving DecidableEq, Repr, Inhabited, BEq

/-- Subtype reference: printed literal, creature type chosen on the source (CR 614.12),
or creature type chosen by an earlier step (`VarId`). -/
inductive SubtypeRef where
  | literal (subtype : CardSubtype)
  | chosenOnSource
  | fromStep (v : VarId)
deriving DecidableEq, Repr, Inhabited, BEq

instance : HasTextChange SubtypeRef where
  applyTextChanges tcs r :=
    if tcs.isEmpty then r
    else
      match r with
      | .literal s => .literal (HasTextChange.applyTextChanges tcs s)
      | .chosenOnSource => .chosenOnSource
      | .fromStep v => .fromStep v

/-- Color reference: printed literal, color chosen on the source, or commander color identity
(CR 105 / 614.12 / 903.4). -/
inductive ColorRef where
  | literal (color : Color)
  | chosenOnSource
  | commanderIdentity
deriving DecidableEq, Repr, Inhabited, BEq

instance : HasTextChange ColorRef where
  applyTextChanges tcs r :=
    if tcs.isEmpty then r
    else
      match r with
      | .literal c => .literal (HasTextChange.applyTextChanges tcs c)
      | .chosenOnSource => .chosenOnSource
      | .commanderIdentity => .commanderIdentity

/-- Card name reference: printed literal or card name chosen on the source (CR 201.4 / 614.12). -/
inductive NameRef where
  | literal (name : String)
  | chosenOnSource
deriving DecidableEq, Repr, Inhabited, BEq

/-- Parity reference: literal odd/even, parity chosen on the source (CR 614.12),
or parity chosen by an earlier step (`VarId`). -/
inductive ParityRef where
  | odd
  | even
  | chosenOnSource
  | fromStep (v : VarId)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Parameterized CR 702 keyword tag matched by `KeywordTag.param`. -/
inductive ParamKeywordTag where
  | affinity
  | equip
  | cycling
  | kicker
  | gift
  | flashback
  | morph
  | impending
  | sneak
  | crew
  | teamwork
deriving DecidableEq, Repr, Inhabited, BEq

namespace ParamKeywordTag

def oracleName : ParamKeywordTag → String
  | .affinity => "affinity"
  | .equip => "equip"
  | .cycling => "cycling"
  | .kicker => "kicker"
  | .gift => "gift"
  | .flashback => "flashback"
  | .morph => "morph"
  | .impending => "impending"
  | .sneak => "sneak"
  | .crew => "crew"
  | .teamwork => "teamwork"

end ParamKeywordTag

/-- Keyword identity tested by `ObjectPred.hasKeyword` (CR 702; 35 constructors). -/
inductive KeywordTag where
  | flying
  | firstStrike
  | doubleStrike
  | deathtouch
  | decayed
  | defender
  | exalted
  | flash
  | haste
  | hexproof
  | indestructible
  | lifelink
  | menace
  | reach
  | shadow
  | trample
  | vigilance
  | changeling
  | splitSecond
  | convoke
  | improvise
  | ascend
  | storied
  | daybound
  | nightbound
  | prowess
  | cascade
  | myriad
  | undying
  | extort
  | ward
  | toxic
  | protection
  | landwalk (subtype? : Option CardSubtype := none)
  | param (kind : ParamKeywordTag)
deriving DecidableEq, Repr, Inhabited, BEq

namespace KeywordTag

def oracleName : KeywordTag → String
  | .flying => "flying"
  | .firstStrike => "first strike"
  | .doubleStrike => "double strike"
  | .deathtouch => "deathtouch"
  | .decayed => "decayed"
  | .defender => "defender"
  | .exalted => "exalted"
  | .flash => "flash"
  | .haste => "haste"
  | .hexproof => "hexproof"
  | .indestructible => "indestructible"
  | .lifelink => "lifelink"
  | .menace => "menace"
  | .reach => "reach"
  | .shadow => "shadow"
  | .trample => "trample"
  | .vigilance => "vigilance"
  | .changeling => "changeling"
  | .splitSecond => "split second"
  | .convoke => "convoke"
  | .improvise => "improvise"
  | .ascend => "ascend"
  | .storied => "storied"
  | .daybound => "daybound"
  | .nightbound => "nightbound"
  | .prowess => "prowess"
  | .cascade => "cascade"
  | .myriad => "myriad"
  | .undying => "undying"
  | .extort => "extort"
  | .ward => "ward"
  | .toxic => "toxic"
  | .protection => "protection"
  | .landwalk (some sub) => s!"{sub.englishName.map Char.toLower}walk"
  | .landwalk none => "landwalk"
  | .param k => k.oracleName

/-- Parse an Oracle keyword name into its `KeywordTag` (case-insensitive). -/
def ofOracle? (raw : String) : Option KeywordTag :=
  match raw.trimAscii.copy.map Char.toLower with
  | "flying" => some .flying
  | "first strike" => some .firstStrike
  | "double strike" => some .doubleStrike
  | "deathtouch" => some .deathtouch
  | "decayed" => some .decayed
  | "defender" => some .defender
  | "exalted" => some .exalted
  | "flash" => some .flash
  | "haste" => some .haste
  | "hexproof" => some .hexproof
  | "indestructible" => some .indestructible
  | "lifelink" => some .lifelink
  | "menace" => some .menace
  | "reach" => some .reach
  | "shadow" => some .shadow
  | "trample" => some .trample
  | "vigilance" => some .vigilance
  | "changeling" => some .changeling
  | "split second" => some .splitSecond
  | "convoke" => some .convoke
  | "improvise" => some .improvise
  | "ascend" => some .ascend
  | "storied" => some .storied
  | "daybound" => some .daybound
  | "nightbound" => some .nightbound
  | "prowess" => some .prowess
  | "cascade" => some .cascade
  | "myriad" => some .myriad
  | "undying" => some .undying
  | "extort" => some .extort
  | "ward" => some .ward
  | "toxic" => some .toxic
  | "protection" => some .protection
  | "landwalk" => some (.landwalk none)
  | "plainswalk" => some (.landwalk (some .plains))
  | "islandwalk" => some (.landwalk (some .island))
  | "swampwalk" => some (.landwalk (some .swamp))
  | "mountainwalk" => some (.landwalk (some .mountain))
  | "forestwalk" => some (.landwalk (some .forest))
  | "affinity" => some (.param .affinity)
  | "equip" => some (.param .equip)
  | "cycling" => some (.param .cycling)
  | "kicker" => some (.param .kicker)
  | "gift" => some (.param .gift)
  | "flashback" => some (.param .flashback)
  | "morph" => some (.param .morph)
  | "impending" => some (.param .impending)
  | "sneak" => some (.param .sneak)
  | "crew" => some (.param .crew)
  | "teamwork" => some (.param .teamwork)
  | _ => none

end KeywordTag

instance : HasTextChange KeywordTag where
  applyTextChanges tcs kw :=
    if tcs.isEmpty then kw
    else
      match kw with
      | .landwalk (some sub) => .landwalk (some (HasTextChange.applyTextChanges tcs sub))
      | other => other

/-- Bound single-object reference for `ObjectPred.sameAs` / `ObjectPred.otherThan`. -/
inductive ObjectRef where
  | this
  | target (slot : Nat := 0)
  | attachedHost
  | triggerSubject
  | stepVar (v : VarId)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Shared characteristic queried by `ObjectPred.shares` (CR 105.2c / 201.2a / 205). -/
inductive SharedCharacteristic where
  | color
  | cardType
  | creatureType
  | subtype
  | name
deriving DecidableEq, Repr, Inhabited, BEq

/-- Direction for `ObjectExpr.extremum`. -/
inductive ExtremumDir where
  | max
  | min
deriving DecidableEq, Repr, Inhabited, BEq

/-- Predicate over mana spent to cast a spell (`CastContextPred.manaSpentMatches`, CR 106.6 / 400.7d). -/
inductive ManaSpentPred where
  | fromTreasure
  | fromSource
  | ofColor (color : Color)
  | amount (op : CmpOp) (n : Nat)
  | colorCount (op : CmpOp) (n : Nat)
  | withRider (rider : SpellRiderSpec)
deriving DecidableEq, Repr, Inhabited, BEq

instance : HasTextChange ManaSpentPred where
  applyTextChanges tcs p :=
    if tcs.isEmpty then p
    else
      match p with
      | .ofColor c => .ofColor (HasTextChange.applyTextChanges tcs c)
      | other => other

/-- Predicate over a spell's CR 400.7d cast history (`Condition.castPred`). -/
inductive CastContextPred where
  | wasKicked (obj : ObjectRef := .this)
  | giftPromised (obj : ObjectRef := .this)
  | impendingPaid (obj : ObjectRef := .this)
  | teamworkPaid (obj : ObjectRef := .this)
  | sneakPaid (obj : ObjectRef := .this)
  | castFrom (zone : ZoneKind) (obj : ObjectRef := .this)
  | manaSpentMatches (pred : ManaSpentPred) (obj : ObjectRef := .this)
deriving DecidableEq, Repr, Inhabited, BEq

instance : HasTextChange CastContextPred where
  applyTextChanges tcs p :=
    if tcs.isEmpty then p
    else
      match p with
      | .manaSpentMatches mp obj => .manaSpentMatches (HasTextChange.applyTextChanges tcs mp) obj
      | other => other

/-- Object category tested by `ObjectPred.isKind` (CR 108.2 / 110.4a / 111.6 / 112.1). -/
inductive ObjectCategory where
  /-- Represented by a card (not a token, stack ability, emblem, or non-card copy; CR 108.2 / 111.6). -/
  | card
  /-- A card with at least one permanent card type (CR 110.4a / 111.6). -/
  | permanentCard
  /-- A spell on the stack (card or copy of a card on the stack, never an ability; CR 112.1). -/
  | spell
deriving DecidableEq, Repr, Inhabited, BEq

mutual

/-- Player relation paired with a player predicate (CR 102 / 810). -/
structure PlayerFilter where
  relation : PlayerRelation
  pred : PlayerPred

/-- Predicate over a player (`PlayerFilter`, `PlayerExpr.matching`, `Condition.playerPred`). -/
inductive PlayerPred where
  | any
  | all (preds : Array PlayerPred)
  | anyOf (preds : Array PlayerPred)
  | not (pred : PlayerPred)
  | hasDesignation (d : PlayerDesignation)
  | isMonarch
  | isActivePlayer
  | isDefendingPlayer
  | metric (m : PlayerMetric) (op : CmpOp) (rhs : ValueExpr)
  | controls (filter : ObjectFilter) (minCount : ValueExpr)
  | isSeat (idx : Nat)
  | thatPlayer
  | matchesExpr (who : PlayerExpr)

/-- Pure expression evaluating to zero, one, or more players (11 constructors). -/
inductive PlayerExpr where
  | you
  | activePlayer
  | defendingPlayer
  | monarch
  | target (slot : Nat := 0)
  | controllerOf (obj : ObjectExpr)
  | ownerOf (obj : ObjectExpr)
  | triggerPlayer (role : TriggerPlayerRole)
  | stepPlayers (v : VarId)
  | matching (rel : PlayerRelation) (pred : PlayerPred)
  | chosenBy (chooser : PlayerExpr) (count : CountRange) (filter : PlayerFilter)

/-- Combat role predicate for `ObjectPred.combatRole` (CR 508 / 509; 7 constructors). -/
inductive CombatRolePred where
  | attacking
  | attackingPlayer (who : PlayerExpr)
  | attackingAlone
  | blocking
  | blockingObject (attacker : ObjectExpr)
  | blocked
  | unblocked

/-- Target reference for `ObjectPred.targets` (CR 115). -/
inductive ObjectOrPlayerExpr where
  | object (obj : ObjectExpr)
  | player (who : PlayerExpr)
  | either (obj : ObjectExpr) (who : PlayerExpr)

/-- Damage recipient filter for `ObjectPred.dealtDamageThisTurn` and damage replacement
effects (CR 120). -/
inductive RecipientFilter where
  | player (filter : PlayerFilter)
  | object (filter : ObjectFilter)
  | playerOrObject (player : PlayerFilter) (object : ObjectFilter)
  | any

/-- Owner filter for owned zones (`library`, `hand`, `graveyard`, `outside`; CR 400.1). -/
inductive ZoneOwnerSpec where
  | any
  | matching (filter : PlayerFilter)
  | ofPlayer (who : PlayerExpr)

/-- Set of zones to query (CR 400.1). -/
structure ZoneSetSpec where
  zones : Array ZoneKind
  owner : ZoneOwnerSpec

/-- Pure predicate over an object's Layer 1–7d characteristics, status, relations,
and turn/cast history (37 constructors, < 40 tag budget). -/
inductive ObjectPred where
  -- Boolean combinators (3)
  | all (preds : Array ObjectPred)
  | any (preds : Array ObjectPred)
  | not (pred : ObjectPred)
  -- Layer 1–7d characteristics (CR 109.3 / 613) (9)
  | hasType (cardType : CardType)
  | hasSupertype (supertype : Supertype)
  | hasSubtype (subtype : SubtypeRef)
  | hasColor (color : ColorRef)
  | colorCount (op : CmpOp) (n : Nat)
  | named (name : NameRef)
  | hasKeyword (kw : KeywordTag)
  | stat (kind : StatKind) (op : CmpOp) (rhs : ValueExpr)
  | statParity (kind : StatKind) (parity : ParityRef)
  -- Status & identity (CR 110.5 / 111 / 708) (10)
  | isToken (v : Bool := true)
  | isFaceDown (v : Bool := true)
  | isCopy (v : Bool := true)
  | isCommander
  | isKind (kind : ObjectCategory)
  | tapped (v : Bool := true)
  | phasedOut (v : Bool := true)
  | combatRole (role : CombatRolePred)
  | hasDesignation (tag : PermanentDesignationTag)
  | counterCount (kind? : Option CounterKind) (op : CmpOp) (rhs : ValueExpr)
  -- Relations (8)
  | sameAs (ref : ObjectRef)
  | otherThan (ref : ObjectRef)
  | controlledBy (filter : PlayerFilter)
  | ownedBy (filter : PlayerFilter)
  | attachedTo (host : ObjectExpr)
  | hasAttachment (filter : ObjectFilter)
  | targets (target : ObjectOrPlayerExpr)
  | shares (char : SharedCharacteristic) (withObj : ObjectExpr)
  -- Event & cast history (CR 400.7d) (7)
  | wasCast
  | castFrom (zone : ZoneKind)
  | enteredThisTurn
  | attackedThisTurn
  | dealtDamageThisTurn (combatOnly : Bool := false) (recipient? : Option RecipientFilter)
      (thisTurnOnly : Bool := true)
  | wasDealtDamageThisTurn
  | receivedCounterThisTurn (kind? : Option CounterKind) (byPlayer? : Option PlayerFilter)
  | putIntoGraveyardFromBattlefieldThisTurn
  | chosenAnchorIs (anchor : String)

/-- Zone-scoped object predicate (used by continuous effects, filters, and noun phrases). -/
structure ObjectFilter where
  zones : ZoneSetSpec
  pred : ObjectPred

/-- Pure expression evaluating to a sequence of objects (live or LKI, 15 constructors). -/
inductive ObjectExpr where
  | this
  | target (slot : Nat := 0)
  | allTargets
  | attachedHost
  | triggerSubject
  | targetsOf (stackObj : ObjectExpr)
  | stepObjects (v : VarId)
  | linkedExile (source : ObjectExpr)
  | costPaidObjects
  | inZones (zones : ZoneSetSpec) (pred : ObjectPred)
  | topOfLibrary (owner : PlayerExpr) (count : ValueExpr)
  | extremum (dir : ExtremumDir) (metric : StatKind) (among : ObjectExpr)
  | filter (objs : ObjectExpr) (pred : ObjectPred)
  | union (exprs : Array ObjectExpr)
  | diff (lhs rhs : ObjectExpr)

/-- Pure integer-valued expression (CR 107 / 608.2h; 16 constructors). -/
inductive ValueExpr where
  | const (n : Int)
  | chosenX
  | eventAmount
  | objectStat (kind : StatKind) (obj : ObjectExpr)
  | counterCount (kind? : Option CounterKind) (obj : ObjectExpr)
  | aggregate (op : AggOp) (metric : ObjectMetric) (objs : ObjectExpr)
  | basicLandTypeCount (objs : ObjectExpr)
  | cardTypeCount (objs : ObjectExpr)
  | subtypeCount (category : SubtypeCategory) (objs : ObjectExpr)
  | colorCountAmong (objs : ObjectExpr)
  | playerMetric (metric : PlayerMetric) (who : PlayerExpr)
  | maxControlled (who : PlayerFilter) (pred : ObjectPred)
  | manaSymbols (color? : Option Color) (objs : ObjectExpr)
  | manaSpent (obj : ObjectExpr)
  | stepMetric (metric : StepMetric) (v : VarId)
  | binary (op : ArithOp) (lhs rhs : ValueExpr)

end

-- Single `Inhabited` instances for the mutual block.
instance : Inhabited PlayerPred := ⟨.any⟩
instance : Inhabited PlayerFilter := ⟨{ relation := .anyPlayer, pred := .any }⟩
instance : Inhabited PlayerExpr := ⟨.you⟩
instance : Inhabited CombatRolePred := ⟨.attacking⟩
instance : Inhabited ObjectOrPlayerExpr := ⟨.object .this⟩
instance : Inhabited RecipientFilter := ⟨.any⟩
instance : Inhabited ZoneOwnerSpec := ⟨.any⟩
instance : Inhabited ZoneSetSpec := ⟨{ zones := #[.battlefield], owner := .any }⟩
instance : Inhabited ObjectPred := ⟨.all #[]⟩
instance : Inhabited ObjectFilter :=
  ⟨{ zones := { zones := #[.battlefield], owner := .any }, pred := .all #[] }⟩
instance : Inhabited ObjectExpr := ⟨.this⟩
instance : Inhabited ValueExpr := ⟨.const 0⟩

-- Derive the 12-way mutual `BEq` and `Repr` tuples ONCE and project per-type instances.
deriving instance BEq, Repr for PlayerFilter

instance : BEq PlayerPred := ⟨instBEqPlayerFilter.beq_2⟩
instance : BEq PlayerExpr := ⟨instBEqPlayerFilter.beq_3⟩
instance : BEq CombatRolePred := ⟨instBEqPlayerFilter.beq_4⟩
instance : BEq ObjectOrPlayerExpr := ⟨instBEqPlayerFilter.beq_5⟩
instance : BEq RecipientFilter := ⟨instBEqPlayerFilter.beq_6⟩
instance : BEq ZoneOwnerSpec := ⟨instBEqPlayerFilter.beq_7⟩
instance : BEq ZoneSetSpec := ⟨instBEqPlayerFilter.beq_8⟩
instance : BEq ObjectPred := ⟨instBEqPlayerFilter.beq_9⟩
instance : BEq ObjectFilter := ⟨instBEqPlayerFilter.beq_10⟩
instance : BEq ObjectExpr := ⟨instBEqPlayerFilter.beq_11⟩
instance : BEq ValueExpr := ⟨instBEqPlayerFilter.beq_12⟩

instance : Repr PlayerPred := ⟨instReprPlayerFilter.repr_2⟩
instance : Repr PlayerExpr := ⟨instReprPlayerFilter.repr_3⟩
instance : Repr CombatRolePred := ⟨instReprPlayerFilter.repr_4⟩
instance : Repr ObjectOrPlayerExpr := ⟨instReprPlayerFilter.repr_5⟩
instance : Repr RecipientFilter := ⟨instReprPlayerFilter.repr_6⟩
instance : Repr ZoneOwnerSpec := ⟨instReprPlayerFilter.repr_7⟩
instance : Repr ZoneSetSpec := ⟨instReprPlayerFilter.repr_8⟩
instance : Repr ObjectPred := ⟨instReprPlayerFilter.repr_9⟩
instance : Repr ObjectFilter := ⟨instReprPlayerFilter.repr_10⟩
instance : Repr ObjectExpr := ⟨instReprPlayerFilter.repr_11⟩
instance : Repr ValueExpr := ⟨instReprPlayerFilter.repr_12⟩

/-- Symbolic library placement position (CR 401; symbolic counterpart of Layer-0
`LibraryPosition` where `.fromTop` takes a `ValueExpr`). -/
inductive LibraryPosSpec where
  | top
  | bottom
  | bottomRandom
  | fromTop (offset : ValueExpr)
  | shuffledIn
deriving Repr, Inhabited, BEq

/-- Turn-history event pattern matched by `EventHistoryPred` against `Game.events`
(14 constructors). -/
inductive EventPattern where
  | permanentEntered (pred : ObjectPred)
  | permanentDied (pred : ObjectPred) (minCount : Nat := 1)
  | permanentLeftBattlefield (pred : ObjectPred)
  | attackedWith (pred : ObjectPred) (minCount : Nat := 1)
  | castSpell (pred : ObjectPred)
  | drewCard (minCount : Nat := 1)
  | discardedCard (pred : ObjectPred := .all #[])
  | milledCard (minCount : Nat := 1)
  | gainedLife (minAmount : Nat := 1)
  | lostLife (minAmount : Nat := 1)
  | dealtDamage (combatOnly : Bool := false) (noncombatOnly : Bool := false)
  | activatedLoyalty
  | beheld (subtype : CardSubtype)
  | proliferated
deriving Repr, Inhabited, BEq

/-- Turn-history predicate evaluated over `Game.events` (`Condition.turnHistory`). -/
inductive EventHistoryPred where
  | scriedThisTurn (who : PlayerFilter := { relation := .you, pred := .any })
  | surveilledThisTurn (who : PlayerFilter := { relation := .you, pred := .any })
  | eventOccurredThisTurn (who : PlayerFilter) (pattern : EventPattern)
  | eventOccurredLastTurn (who : PlayerFilter) (pattern : EventPattern)
  | firstResolutionThisTurn
  | nthResolutionThisTurn (n : Nat)
  | optionalOnceUnusedThisTurn
deriving Repr, Inhabited, BEq

/-- Pure boolean condition (CR 603.4 / 608.2 / 611; 14 constructors). -/
inductive Condition where
  | cmp (op : CmpOp) (lhs rhs : ValueExpr)
  | exists (objs : ObjectExpr)
  | forAll (objs : ObjectExpr) (pred : ObjectPred)
  | playerPred (who : PlayerExpr) (pred : PlayerPred)
  | castPred (pred : CastContextPred)
  | turnHistory (pred : EventHistoryPred)
  | stepSucceeded (v : VarId)
  | duringStep (step : Step)
  | duringPhase (phase : Phase)
  | isYourTurn
  | isNight
  | all (conds : Array Condition)
  | any (conds : Array Condition)
  | not (cond : Condition)
deriving Repr, Inhabited, BEq

/-- Symbolic continuous-effect duration (1-to-1 with `EffectDuration`, CR 611.2a–b;
11 constructors). -/
inductive DurationExpr where
  | untilEndOfTurn
  | untilEndOfCombat
  | untilEndOfStepOrPhase (s : StepOrPhase)
  | untilStepOrPhase (s : StepOrPhase)
  | untilNextTurnOf (who : PlayerExpr)
  | untilEndOfNextTurnOf (who : PlayerExpr)
  | whileOnBattlefield (obj : ObjectExpr)
  | untilLeavesBattlefield (obj : ObjectExpr)
  | whileHasCounter (obj : ObjectExpr) (kind : CounterKind)
  | whileInZone (obj : ObjectExpr) (zone : ZoneKind)
  | indefinite
deriving Repr, Inhabited, BEq

/-! ### Smart Constructors and Helpers -/

namespace PlayerFilter

def you : PlayerFilter := { relation := .you, pred := .any }
def opponent : PlayerFilter := { relation := .opponent, pred := .any }
def teammate : PlayerFilter := { relation := .teammate, pred := .any }
def any : PlayerFilter := { relation := .anyPlayer, pred := .any }
def defendingPlayer : PlayerFilter := { relation := .anyPlayer, pred := .isDefendingPlayer }
def seat (idx : Nat) : PlayerFilter := { relation := .anyPlayer, pred := .isSeat idx }
def thatPlayer : PlayerFilter := { relation := .anyPlayer, pred := .thatPlayer }
def ofExpr (who : PlayerExpr) : PlayerFilter := { relation := .anyPlayer, pred := .matchesExpr who }

end PlayerFilter

namespace ZoneSetSpec

def battlefield : ZoneSetSpec := { zones := #[.battlefield], owner := .any }
def stack : ZoneSetSpec := { zones := #[.stack], owner := .any }
def exile : ZoneSetSpec := { zones := #[.exile], owner := .any }
def command : ZoneSetSpec := { zones := #[.command], owner := .any }
def yourGraveyard : ZoneSetSpec := { zones := #[.graveyard], owner := .matching .you }
def opponentGraveyard : ZoneSetSpec := { zones := #[.graveyard], owner := .matching .opponent }
def anyGraveyard : ZoneSetSpec := { zones := #[.graveyard], owner := .any }
def yourHand : ZoneSetSpec := { zones := #[.hand], owner := .matching .you }
def yourLibrary : ZoneSetSpec := { zones := #[.library], owner := .matching .you }
def ofPlayer (z : ZoneKind) (who : PlayerExpr) : ZoneSetSpec :=
  { zones := #[z], owner := .ofPlayer who }
def handOf (who : PlayerExpr) : ZoneSetSpec := ofPlayer .hand who
def graveyardOf (who : PlayerExpr) : ZoneSetSpec := ofPlayer .graveyard who
def libraryOf (who : PlayerExpr) : ZoneSetSpec := ofPlayer .library who

end ZoneSetSpec

namespace PlayerExpr

def opponents : PlayerExpr := .matching .opponent .any
def eachPlayer : PlayerExpr := .matching .anyPlayer .any

end PlayerExpr

namespace ObjectPred

/-- Tautology predicate matching any object. -/
def anyObject : ObjectPred := .all #[]

/-- Represented by a card (not a token, stack ability, emblem, or non-card copy; CR 108.2 / 111.6). -/
def isCard : ObjectPred := .isKind .card

/-- A card with at least one permanent card type (CR 110.4a / 111.6). -/
def isPermanentCard : ObjectPred := .isKind .permanentCard

/-- A spell on the stack (never an ability; CR 112.1). -/
def isSpell : ObjectPred := .isKind .spell

/-- Historic: artifact, legendary, or Saga (CR 700.6). -/
def historic : ObjectPred :=
  .any #[.hasType .artifact, .hasSupertype .legendary, .hasSubtype (.literal .saga)]

/-- Storied permanent filter (HOB): artifact, legendary, or Saga. -/
def storied : ObjectPred := historic

/-- Worthy creature (MSH Equip worthy, CR 702.6c): legendary non-Villain red or white creature. -/
def worthy : ObjectPred :=
  .all #[
    .hasSupertype .legendary,
    .not (.hasSubtype (.literal .villain)),
    .any #[.hasColor (.literal .red), .hasColor (.literal .white)],
    .hasType .creature
  ]

/-- Flatten nested `.all` conjunctions into a single canonical `ObjectPred`. -/
def andAll (ps : Array ObjectPred) : ObjectPred :=
  let flat := ps.foldl (fun acc p =>
    match p with
    | .all inner => acc ++ inner
    | other => acc.push other) #[]
  match flat.toList with
  | [p] => p
  | _ => .all flat

/-- Canonical disjunction of predicates. -/
def orAny (ps : Array ObjectPred) : ObjectPred :=
  match ps.toList with
  | [p] => p
  | _ => .any ps

end ObjectPred

namespace ObjectFilter

def onBattlefield (pred : ObjectPred := .anyObject) : ObjectFilter :=
  { zones := .battlefield, pred }

def creaturesYouControl : ObjectFilter :=
  onBattlefield (.all #[.hasType .creature, .controlledBy .you])

def landsYouControl : ObjectFilter :=
  onBattlefield (.all #[.hasType .land, .controlledBy .you])

def landsOpponentsControl : ObjectFilter :=
  onBattlefield (.all #[.hasType .land, .controlledBy .opponent])

def legendaryCreaturesAndPlaneswalkersYouControl : ObjectFilter :=
  onBattlefield (.all #[
    .hasSupertype .legendary,
    .any #[.hasType .creature, .hasType .planeswalker],
    .controlledBy .you
  ])

def toExpr (f : ObjectFilter) : ObjectExpr :=
  .inZones f.zones f.pred

end ObjectFilter

namespace ObjectExpr

/-- Creatures you control on the battlefield. -/
def creaturesYouControl : ObjectExpr := ObjectFilter.creaturesYouControl.toExpr

/-- Lands you control on the battlefield. -/
def landsYouControl : ObjectExpr := ObjectFilter.landsYouControl.toExpr

/-- Lands opponents control on the battlefield. -/
def landsOpponentsControl : ObjectExpr := ObjectFilter.landsOpponentsControl.toExpr

/-- Other lands you control on the battlefield (e.g. Reflecting Pool). -/
def otherLandsYouControl : ObjectExpr :=
  .inZones .battlefield (.all #[.otherThan .this, .hasType .land, .controlledBy .you])

/-- Legendary creatures and planeswalkers you control (e.g. Mox Amber). -/
def legendaryCreaturesAndPlaneswalkersYouControl : ObjectExpr :=
  ObjectFilter.legendaryCreaturesAndPlaneswalkersYouControl.toExpr

/-- Permanents of `subtype` you control on the battlefield. -/
def controlledOfSubtype (subtype : CardSubtype) : ObjectExpr :=
  .inZones .battlefield (.all #[.hasSubtype (.literal subtype), .controlledBy .you])

end ObjectExpr

namespace ValueExpr

/-- Count of objects matching `objs`. -/
def count (objs : ObjectExpr) : ValueExpr :=
  .aggregate .count .one objs

/-- Pure evaluation for context-independent `ValueExpr`s (`.const`, `.chosenX`,
and `.binary` over them). Returns `none` when game state is required. -/
def evalConst? (x : Nat := 0) : ValueExpr → Option Int
  | .const n => some n
  | .chosenX => some (Int.ofNat x)
  | .binary op a b =>
    match evalConst? x a, evalConst? x b with
    | some va, some vb => some (op.eval va vb)
    | _, _ => none
  | _ => none

end ValueExpr

namespace Condition

/-- Combine an array of conditions into a canonical `Option Condition`, flattening
nested `.all` conjunctions. -/
def andAll (cs : Array Condition) : Option Condition :=
  let flat := cs.foldl (fun acc c =>
    match c with
    | .all inner => acc ++ inner
    | other => acc.push other) #[]
  match flat.toList with
  | [] => none
  | [c] => some c
  | _ => some (.all flat)

/-- Conjoin two optional conditions. -/
def andOpt (a b : Option Condition) : Option Condition :=
  match a, b with
  | none, x | x, none => x
  | some c1, some c2 => andAll #[c1, c2]

/-- True iff the source object (`ObjectExpr.this`) exists and satisfies `pred`. -/
def thisMatches (pred : ObjectPred) : Condition :=
  .all #[.exists .this, .forAll .this pred]

/-- True iff the triggering subject (`ObjectExpr.triggerSubject`) exists and satisfies `pred`. -/
def triggerSubjectMatches (pred : ObjectPred) : Condition :=
  .all #[.exists .triggerSubject, .forAll .triggerSubject pred]

end Condition

mutual

private partial def playerFilterMentionsTarget (pf : PlayerFilter) : Bool :=
  playerPredMentionsTarget pf.pred

private partial def playerPredMentionsTarget : PlayerPred → Bool
  | .all ps | .anyOf ps => ps.any playerPredMentionsTarget
  | .not p => playerPredMentionsTarget p
  | .metric _ _ rhs => valueExprMentionsTarget rhs
  | .controls f minC => objectFilterMentionsTarget f || valueExprMentionsTarget minC
  | .matchesExpr who => playerExprMentionsTarget who
  | _ => false

private partial def playerExprMentionsTarget : PlayerExpr → Bool
  | .target _ => true
  | .controllerOf o | .ownerOf o => objectExprMentionsTarget o
  | .matching _ p => playerPredMentionsTarget p
  | .chosenBy ch _ f => playerExprMentionsTarget ch || playerFilterMentionsTarget f
  | _ => false

private partial def objectPredMentionsTarget : ObjectPred → Bool
  | .all ps | .any ps => ps.any objectPredMentionsTarget
  | .not p => objectPredMentionsTarget p
  | .stat _ _ rhs | .counterCount _ _ rhs => valueExprMentionsTarget rhs
  | .combatRole (.attackingPlayer w) => playerExprMentionsTarget w
  | .combatRole (.blockingObject o) => objectExprMentionsTarget o
  | .sameAs (.target _) | .otherThan (.target _) => true
  | .controlledBy pf | .ownedBy pf => playerFilterMentionsTarget pf
  | .attachedTo o | .shares _ o => objectExprMentionsTarget o
  | .hasAttachment f => objectFilterMentionsTarget f
  | .targets (.object o) => objectExprMentionsTarget o
  | .targets (.player p) => playerExprMentionsTarget p
  | .targets (.either o p) => objectExprMentionsTarget o || playerExprMentionsTarget p
  | .dealtDamageThisTurn _ (some (.player pf)) _ => playerFilterMentionsTarget pf
  | .dealtDamageThisTurn _ (some (.object f)) _ => objectFilterMentionsTarget f
  | .dealtDamageThisTurn _ (some (.playerOrObject pf f)) _ =>
    playerFilterMentionsTarget pf || objectFilterMentionsTarget f
  | .receivedCounterThisTurn _ (some pf) => playerFilterMentionsTarget pf
  | _ => false

private partial def objectFilterMentionsTarget (f : ObjectFilter) : Bool :=
  (match f.zones.owner with
   | .matching pf => playerFilterMentionsTarget pf
   | .ofPlayer p => playerExprMentionsTarget p
   | .any => false) || objectPredMentionsTarget f.pred

private partial def objectExprMentionsTarget : ObjectExpr → Bool
  | .target _ | .allTargets => true
  | .targetsOf stackObj => objectExprMentionsTarget stackObj
  | .linkedExile src => objectExprMentionsTarget src
  | .inZones zs pred =>
    (match zs.owner with
     | .matching pf => playerFilterMentionsTarget pf
     | .ofPlayer p => playerExprMentionsTarget p
     | .any => false) || objectPredMentionsTarget pred
  | .topOfLibrary owner cnt => playerExprMentionsTarget owner || valueExprMentionsTarget cnt
  | .extremum _ _ among => objectExprMentionsTarget among
  | .filter objs pred => objectExprMentionsTarget objs || objectPredMentionsTarget pred
  | .union es => es.any objectExprMentionsTarget
  | .diff a b => objectExprMentionsTarget a || objectExprMentionsTarget b
  | _ => false

private partial def valueExprMentionsTarget : ValueExpr → Bool
  | .objectStat _ o | .counterCount _ o | .aggregate _ _ o | .basicLandTypeCount o
  | .cardTypeCount o | .subtypeCount _ o | .colorCountAmong o | .manaSymbols _ o
  | .manaSpent o =>
    objectExprMentionsTarget o
  | .playerMetric _ w => playerExprMentionsTarget w
  | .maxControlled pf pred => playerFilterMentionsTarget pf || objectPredMentionsTarget pred
  | .binary _ a b => valueExprMentionsTarget a || valueExprMentionsTarget b
  | _ => false

end

/-- Whether `v` references a chosen target (`ObjectExpr.target` / `PlayerExpr.target`),
so cost computation must evaluate it after CR 601.2c target selection. -/
def ValueExpr.mentionsTarget (v : ValueExpr) : Bool :=
  valueExprMentionsTarget v

/-- Whether `c` references a chosen target (`ObjectExpr.target` / `PlayerExpr.target`),
so cost computation must evaluate it after CR 601.2c target selection. -/
def Condition.mentionsTarget : Condition → Bool
  | .cmp _ a b => valueExprMentionsTarget a || valueExprMentionsTarget b
  | .exists o => objectExprMentionsTarget o
  | .forAll o p => objectExprMentionsTarget o || objectPredMentionsTarget p
  | .playerPred w p => playerExprMentionsTarget w || playerPredMentionsTarget p
  | .castPred cp =>
    match cp with
    | .wasKicked (.target _) | .giftPromised (.target _) | .impendingPaid (.target _)
    | .teamworkPaid (.target _) | .sneakPaid (.target _) | .castFrom _ (.target _)
    | .manaSpentMatches _ (.target _) => true
    | _ => false
  | .all cs | .any cs => cs.attach.any fun ⟨c, _⟩ => Condition.mentionsTarget c
  | .not c => Condition.mentionsTarget c
  | _ => false

/-! ### Functorial Layer 3 `HasTextChange` Instances (CR 612.2 / 613.1c) -/

mutual

private partial def applyTcPlayerFilter (tcs : Array TextChange) (pf : PlayerFilter) : PlayerFilter :=
  { pf with pred := applyTcPlayerPred tcs pf.pred }

private partial def applyTcPlayerPred (tcs : Array TextChange) : PlayerPred → PlayerPred
  | .any => .any
  | .all ps => .all (ps.map (applyTcPlayerPred tcs))
  | .anyOf ps => .anyOf (ps.map (applyTcPlayerPred tcs))
  | .not p => .not (applyTcPlayerPred tcs p)
  | .hasDesignation d => .hasDesignation d
  | .isMonarch => .isMonarch
  | .isActivePlayer => .isActivePlayer
  | .isDefendingPlayer => .isDefendingPlayer
  | .metric m op rhs => .metric m op (applyTcValueExpr tcs rhs)
  | .controls f minC => .controls (applyTcObjectFilter tcs f) (applyTcValueExpr tcs minC)
  | .isSeat idx => .isSeat idx
  | .thatPlayer => .thatPlayer
  | .matchesExpr who => .matchesExpr (applyTcPlayerExpr tcs who)

private partial def applyTcPlayerExpr (tcs : Array TextChange) : PlayerExpr → PlayerExpr
  | .you => .you
  | .activePlayer => .activePlayer
  | .defendingPlayer => .defendingPlayer
  | .monarch => .monarch
  | .target slot => .target slot
  | .controllerOf obj => .controllerOf (applyTcObjectExpr tcs obj)
  | .ownerOf obj => .ownerOf (applyTcObjectExpr tcs obj)
  | .triggerPlayer role => .triggerPlayer role
  | .stepPlayers v => .stepPlayers v
  | .matching rel pred => .matching rel (applyTcPlayerPred tcs pred)
  | .chosenBy ch cnt f =>
    .chosenBy (applyTcPlayerExpr tcs ch) cnt (applyTcPlayerFilter tcs f)

private partial def applyTcCombatRolePred (tcs : Array TextChange) : CombatRolePred → CombatRolePred
  | .attacking => .attacking
  | .attackingPlayer who => .attackingPlayer (applyTcPlayerExpr tcs who)
  | .attackingAlone => .attackingAlone
  | .blocking => .blocking
  | .blockingObject atk => .blockingObject (applyTcObjectExpr tcs atk)
  | .blocked => .blocked
  | .unblocked => .unblocked

private partial def applyTcObjectOrPlayerExpr (tcs : Array TextChange) : ObjectOrPlayerExpr → ObjectOrPlayerExpr
  | .object o => .object (applyTcObjectExpr tcs o)
  | .player p => .player (applyTcPlayerExpr tcs p)
  | .either o p => .either (applyTcObjectExpr tcs o) (applyTcPlayerExpr tcs p)

private partial def applyTcRecipientFilter (tcs : Array TextChange) : RecipientFilter → RecipientFilter
  | .player pf => .player (applyTcPlayerFilter tcs pf)
  | .object of => .object (applyTcObjectFilter tcs of)
  | .playerOrObject pf of => .playerOrObject (applyTcPlayerFilter tcs pf) (applyTcObjectFilter tcs of)
  | .any => .any

private partial def applyTcZoneOwnerSpec (tcs : Array TextChange) : ZoneOwnerSpec → ZoneOwnerSpec
  | .any => .any
  | .matching pf => .matching (applyTcPlayerFilter tcs pf)
  | .ofPlayer pe => .ofPlayer (applyTcPlayerExpr tcs pe)

private partial def applyTcZoneSetSpec (tcs : Array TextChange) (zs : ZoneSetSpec) : ZoneSetSpec :=
  { zs with owner := applyTcZoneOwnerSpec tcs zs.owner }

private partial def applyTcObjectPred (tcs : Array TextChange) : ObjectPred → ObjectPred
  | .all ps => .all (ps.map (applyTcObjectPred tcs))
  | .any ps => .any (ps.map (applyTcObjectPred tcs))
  | .not p => .not (applyTcObjectPred tcs p)
  | .hasType t => .hasType t
  | .hasSupertype s => .hasSupertype s
  | .hasSubtype sr => .hasSubtype (HasTextChange.applyTextChanges tcs sr)
  | .hasColor cr => .hasColor (HasTextChange.applyTextChanges tcs cr)
  | .colorCount op n => .colorCount op n
  | .named nr => .named nr
  | .hasKeyword kw => .hasKeyword (HasTextChange.applyTextChanges tcs kw)
  | .stat k op rhs => .stat k op (applyTcValueExpr tcs rhs)
  | .statParity k pr => .statParity k pr
  | .isToken v => .isToken v
  | .isFaceDown v => .isFaceDown v
  | .isCopy v => .isCopy v
  | .isCommander => .isCommander
  | .isKind k => .isKind k
  | .tapped v => .tapped v
  | .phasedOut v => .phasedOut v
  | .combatRole r => .combatRole (applyTcCombatRolePred tcs r)
  | .hasDesignation tag => .hasDesignation tag
  | .counterCount k? op rhs => .counterCount k? op (applyTcValueExpr tcs rhs)
  | .sameAs r => .sameAs r
  | .otherThan r => .otherThan r
  | .controlledBy pf => .controlledBy (applyTcPlayerFilter tcs pf)
  | .ownedBy pf => .ownedBy (applyTcPlayerFilter tcs pf)
  | .attachedTo host => .attachedTo (applyTcObjectExpr tcs host)
  | .hasAttachment f => .hasAttachment (applyTcObjectFilter tcs f)
  | .targets tgt => .targets (applyTcObjectOrPlayerExpr tcs tgt)
  | .shares ch o => .shares ch (applyTcObjectExpr tcs o)
  | .wasCast => .wasCast
  | .castFrom z => .castFrom z
  | .enteredThisTurn => .enteredThisTurn
  | .attackedThisTurn => .attackedThisTurn
  | .dealtDamageThisTurn combatOnly rec? thisTurnOnly =>
    .dealtDamageThisTurn combatOnly (rec?.map (applyTcRecipientFilter tcs)) thisTurnOnly
  | .wasDealtDamageThisTurn => .wasDealtDamageThisTurn
  | .receivedCounterThisTurn kind? byPlayer? =>
    .receivedCounterThisTurn kind? (byPlayer?.map (applyTcPlayerFilter tcs))
  | .putIntoGraveyardFromBattlefieldThisTurn => .putIntoGraveyardFromBattlefieldThisTurn
  | .chosenAnchorIs anchor => .chosenAnchorIs anchor

private partial def applyTcObjectFilter (tcs : Array TextChange) (f : ObjectFilter) : ObjectFilter :=
  { zones := applyTcZoneSetSpec tcs f.zones, pred := applyTcObjectPred tcs f.pred }

private partial def applyTcObjectExpr (tcs : Array TextChange) : ObjectExpr → ObjectExpr
  | .this => .this
  | .target slot => .target slot
  | .allTargets => .allTargets
  | .attachedHost => .attachedHost
  | .triggerSubject => .triggerSubject
  | .targetsOf stackObj => .targetsOf (applyTcObjectExpr tcs stackObj)
  | .stepObjects v => .stepObjects v
  | .linkedExile src => .linkedExile (applyTcObjectExpr tcs src)
  | .costPaidObjects => .costPaidObjects
  | .inZones zs pred => .inZones (applyTcZoneSetSpec tcs zs) (applyTcObjectPred tcs pred)
  | .topOfLibrary owner cnt =>
    .topOfLibrary (applyTcPlayerExpr tcs owner) (applyTcValueExpr tcs cnt)
  | .extremum dir m among => .extremum dir m (applyTcObjectExpr tcs among)
  | .filter objs pred => .filter (applyTcObjectExpr tcs objs) (applyTcObjectPred tcs pred)
  | .union es => .union (es.map (applyTcObjectExpr tcs))
  | .diff a b => .diff (applyTcObjectExpr tcs a) (applyTcObjectExpr tcs b)

private partial def applyTcValueExpr (tcs : Array TextChange) : ValueExpr → ValueExpr
  | .const n => .const n
  | .chosenX => .chosenX
  | .eventAmount => .eventAmount
  | .objectStat k obj => .objectStat k (applyTcObjectExpr tcs obj)
  | .counterCount k? obj => .counterCount k? (applyTcObjectExpr tcs obj)
  | .aggregate op m objs => .aggregate op m (applyTcObjectExpr tcs objs)
  | .basicLandTypeCount objs => .basicLandTypeCount (applyTcObjectExpr tcs objs)
  | .cardTypeCount objs => .cardTypeCount (applyTcObjectExpr tcs objs)
  | .subtypeCount cat objs => .subtypeCount cat (applyTcObjectExpr tcs objs)
  | .colorCountAmong objs => .colorCountAmong (applyTcObjectExpr tcs objs)
  | .playerMetric m who => .playerMetric m (applyTcPlayerExpr tcs who)
  | .maxControlled pf pred => .maxControlled (applyTcPlayerFilter tcs pf) (applyTcObjectPred tcs pred)
  | .manaSymbols col? objs =>
    .manaSymbols (HasTextChange.applyTextChanges tcs col?) (applyTcObjectExpr tcs objs)
  | .manaSpent obj => .manaSpent (applyTcObjectExpr tcs obj)
  | .stepMetric m v => .stepMetric m v
  | .binary op a b => .binary op (applyTcValueExpr tcs a) (applyTcValueExpr tcs b)

end

instance : HasTextChange PlayerFilter where
  applyTextChanges tcs x := if tcs.isEmpty then x else applyTcPlayerFilter tcs x

instance : HasTextChange PlayerPred where
  applyTextChanges tcs x := if tcs.isEmpty then x else applyTcPlayerPred tcs x

instance : HasTextChange PlayerExpr where
  applyTextChanges tcs x := if tcs.isEmpty then x else applyTcPlayerExpr tcs x

instance : HasTextChange CombatRolePred where
  applyTextChanges tcs x := if tcs.isEmpty then x else applyTcCombatRolePred tcs x

instance : HasTextChange ObjectOrPlayerExpr where
  applyTextChanges tcs x := if tcs.isEmpty then x else applyTcObjectOrPlayerExpr tcs x

instance : HasTextChange RecipientFilter where
  applyTextChanges tcs x := if tcs.isEmpty then x else applyTcRecipientFilter tcs x

instance : HasTextChange ZoneOwnerSpec where
  applyTextChanges tcs x := if tcs.isEmpty then x else applyTcZoneOwnerSpec tcs x

instance : HasTextChange ZoneSetSpec where
  applyTextChanges tcs x := if tcs.isEmpty then x else applyTcZoneSetSpec tcs x

instance : HasTextChange ObjectPred where
  applyTextChanges tcs x := if tcs.isEmpty then x else applyTcObjectPred tcs x

instance : HasTextChange ObjectFilter where
  applyTextChanges tcs x := if tcs.isEmpty then x else applyTcObjectFilter tcs x

instance : HasTextChange ObjectExpr where
  applyTextChanges tcs x := if tcs.isEmpty then x else applyTcObjectExpr tcs x

instance : HasTextChange ValueExpr where
  applyTextChanges tcs x := if tcs.isEmpty then x else applyTcValueExpr tcs x

instance : HasTextChange LibraryPosSpec where
  applyTextChanges tcs
    | .fromTop v => .fromTop (HasTextChange.applyTextChanges tcs v)
    | other => other

instance : HasTextChange EventPattern where
  applyTextChanges tcs p :=
    if tcs.isEmpty then p
    else
      match p with
      | .permanentEntered op => .permanentEntered (HasTextChange.applyTextChanges tcs op)
      | .permanentDied op n => .permanentDied (HasTextChange.applyTextChanges tcs op) n
      | .permanentLeftBattlefield op =>
        .permanentLeftBattlefield (HasTextChange.applyTextChanges tcs op)
      | .attackedWith op n => .attackedWith (HasTextChange.applyTextChanges tcs op) n
      | .castSpell op => .castSpell (HasTextChange.applyTextChanges tcs op)
      | .discardedCard op => .discardedCard (HasTextChange.applyTextChanges tcs op)
      | .beheld sub => .beheld (HasTextChange.applyTextChanges tcs sub)
      | other => other

instance : HasTextChange EventHistoryPred where
  applyTextChanges tcs p :=
    if tcs.isEmpty then p
    else
      match p with
      | .scriedThisTurn who => .scriedThisTurn (HasTextChange.applyTextChanges tcs who)
      | .surveilledThisTurn who => .surveilledThisTurn (HasTextChange.applyTextChanges tcs who)
      | .eventOccurredThisTurn who pat =>
        .eventOccurredThisTurn (HasTextChange.applyTextChanges tcs who)
          (HasTextChange.applyTextChanges tcs pat)
      | .eventOccurredLastTurn who pat =>
        .eventOccurredLastTurn (HasTextChange.applyTextChanges tcs who)
          (HasTextChange.applyTextChanges tcs pat)
      | .firstResolutionThisTurn => .firstResolutionThisTurn
      | .nthResolutionThisTurn n => .nthResolutionThisTurn n
      | .optionalOnceUnusedThisTurn => .optionalOnceUnusedThisTurn

private def applyTcCondition (tcs : Array TextChange) : Condition → Condition
  | .cmp op a b => .cmp op (HasTextChange.applyTextChanges tcs a) (HasTextChange.applyTextChanges tcs b)
  | .exists o => .exists (HasTextChange.applyTextChanges tcs o)
  | .forAll o p =>
    .forAll (HasTextChange.applyTextChanges tcs o) (HasTextChange.applyTextChanges tcs p)
  | .playerPred w p =>
    .playerPred (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs p)
  | .castPred cp => .castPred (HasTextChange.applyTextChanges tcs cp)
  | .turnHistory hp => .turnHistory (HasTextChange.applyTextChanges tcs hp)
  | .stepSucceeded v => .stepSucceeded v
  | .duringStep s => .duringStep s
  | .duringPhase p => .duringPhase p
  | .isYourTurn => .isYourTurn
  | .isNight => .isNight
  | .all cs => .all (cs.attach.map fun ⟨c, _⟩ => applyTcCondition tcs c)
  | .any cs => .any (cs.attach.map fun ⟨c, _⟩ => applyTcCondition tcs c)
  | .not c => .not (applyTcCondition tcs c)

instance : HasTextChange Condition where
  applyTextChanges tcs c := if tcs.isEmpty then c else applyTcCondition tcs c

instance : HasTextChange DurationExpr where
  applyTextChanges tcs d :=
    if tcs.isEmpty then d
    else
      match d with
      | .untilNextTurnOf w => .untilNextTurnOf (HasTextChange.applyTextChanges tcs w)
      | .untilEndOfNextTurnOf w => .untilEndOfNextTurnOf (HasTextChange.applyTextChanges tcs w)
      | .whileOnBattlefield o => .whileOnBattlefield (HasTextChange.applyTextChanges tcs o)
      | .untilLeavesBattlefield o => .untilLeavesBattlefield (HasTextChange.applyTextChanges tcs o)
      | .whileHasCounter o k => .whileHasCounter (HasTextChange.applyTextChanges tcs o) k
      | .whileInZone o z => .whileInZone (HasTextChange.applyTextChanges tcs o) z
      | other => other

/-! ### Canonical `ToOracle` Printers -/

/-- Rendering context for `ToOracle` (CR 207). -/
structure PrintCtx where
  /-- Self-reference text (`"this creature"`, `"this permanent"`, card name, or `"~"`). -/
  selfRef : String := "this permanent"
  /-- Render noun phrases in plural form when applicable. -/
  plural : Bool := false
  /-- Capitalize the leading character (sentence start). -/
  capitalize : Bool := false
deriving DecidableEq, Repr, Inhabited, BEq

/-- Canonical Oracle-text printer for card expression and ability AST nodes. -/
class ToOracle (α : Type) where
  toOracle : PrintCtx → α → String

/-- Render `x` to canonical Oracle text under `ctx`. -/
def toOracleStr {α : Type} [ToOracle α] (x : α) (ctx : PrintCtx := {}) : String :=
  let s := ToOracle.toOracle ctx x
  if ctx.capitalize then capitalizeAscii s else s

private def applyCap (ctx : PrintCtx) (s : String) : String :=
  if ctx.capitalize then capitalizeAscii s else s

private def renderCmpBound (op : CmpOp) (rhs : String) : String :=
  match op with
  | .eq => rhs
  | .ne => s!"not equal to {rhs}"
  | .lt => s!"less than {rhs}"
  | .le => s!"{rhs} or less"
  | .gt => s!"greater than {rhs}"
  | .ge => s!"{rhs} or greater"

private def renderZonePhrase (z : ZoneKind) : String :=
  match z with
  | .battlefield => "the battlefield"
  | .stack => "the stack"
  | .exile => "exile"
  | .command => "the command zone"
  | .ante => "the ante zone"
  | .outside => "outside the game"
  | .graveyard => "a graveyard"
  | .hand => "a hand"
  | .library => "a library"

private def renderPlayerRel (rel : PlayerRelation) (plural : Bool := false) : String :=
  match rel, plural with
  | .you, _ => "you"
  | .opponent, false => "an opponent"
  | .opponent, true => "opponents"
  | .teammate, false => "a teammate"
  | .teammate, true => "teammates"
  | .anyPlayer, false => "a player"
  | .anyPlayer, true => "players"

private def renderCountRange (cr : CountRange) : String :=
  match cr with
  | .exact 1 => "one"
  | .exact n => englishNumber n
  | .upTo n => s!"up to {englishNumber n}"
  | .between lo hi => s!"{englishNumber lo} to {englishNumber hi}"
  | .anyNumber => "any number of"

mutual

private partial def printPlayerFilter (ctx : PrintCtx) (pf : PlayerFilter) : String :=
  let base := renderPlayerRel pf.relation ctx.plural
  match pf.relation, pf.pred with
  | _, .any => base
  | .anyPlayer, .isDefendingPlayer => "defending player"
  | .anyPlayer, .isSeat _ | .anyPlayer, .thatPlayer => "that player"
  | .anyPlayer, .matchesExpr who => printPlayerExpr { ctx with capitalize := false } who
  | _, p => s!"{base} who {printPlayerPred { ctx with capitalize := false } p}"

private partial def printPlayerPred (ctx : PrintCtx) : PlayerPred → String
  | .any => "is a player"
  | .all ps => String.intercalate " and " (ps.toList.map (printPlayerPred { ctx with capitalize := false }))
  | .anyOf ps => String.intercalate " or " (ps.toList.map (printPlayerPred { ctx with capitalize := false }))
  | .not p => s!"does not ({printPlayerPred { ctx with capitalize := false } p})"
  | .hasDesignation .citysBlessing => "has the city's blessing"
  | .hasDesignation .enduringStory => "has an enduring story"
  | .isMonarch => "is the monarch"
  | .isActivePlayer => "is the active player"
  | .isDefendingPlayer => "is the defending player"
  | .metric m op rhs =>
    let rhsS := printValueExpr { ctx with capitalize := false } rhs
    let mS :=
      match m with
      | .one => "count"
      | .life => "life total"
      | .handSize => "number of cards in hand"
      | .librarySize => "number of cards in library"
      | .graveyardSize => "number of cards in graveyard"
      | .landsPlayedThisTurn => "number of lands played this turn"
      | .spellsCastThisTurn => "number of spells cast this turn"
      | .cardsDrawnThisTurn => "number of cards drawn this turn"
      | .cardsDiscardedThisTurn => "number of cards discarded this turn"
      | .cardsMilledThisTurn => "number of cards milled this turn"
      | .otherSpellsManaValueThisTurn => "total mana value of other spells cast this turn"
      | .lifeGainedThisTurn => "life gained this turn"
      | .lifeLostThisTurn => "life lost this turn"
      | .unspentMana => "unspent mana"
      | .poisonCounters => "poison counters"
      | .opponentsCount => "number of opponents"
    s!"has {mS} {renderCmpBound op rhsS}"
  | .controls f minC =>
    match minC with
    | .const 1 =>
      let noun := printObjectFilter { ctx with plural := false, capitalize := false } f
      s!"controls {indefinite noun} {noun}"
    | _ =>
      let noun := printObjectFilter { ctx with plural := true, capitalize := false } f
      s!"controls {printValueExpr { ctx with capitalize := false } minC} or more {noun}"
  | .isSeat _ | .thatPlayer => "is that player"
  | .matchesExpr who => s!"is {printPlayerExpr { ctx with capitalize := false } who}"

private partial def printPlayerExpr (ctx : PrintCtx) : PlayerExpr → String
  | .you => "you"
  | .activePlayer => "the active player"
  | .defendingPlayer => "the defending player"
  | .monarch => "the monarch"
  | .target _ => "target player"
  | .controllerOf obj => s!"{printObjectExpr { ctx with capitalize := false } obj}'s controller"
  | .ownerOf obj => s!"{printObjectExpr { ctx with capitalize := false } obj}'s owner"
  | .triggerPlayer .actor => "that player"
  | .triggerPlayer .caster => "that spell's controller"
  | .triggerPlayer .damagedPlayer => "that player"
  | .triggerPlayer .attackedPlayer => "the defending player"
  | .triggerPlayer .targetPlayer => "that player"
  | .triggerPlayer .controllerOfSubject => "its controller"
  | .triggerPlayer .ownerOfSubject => "its owner"
  | .triggerPlayer .giftOpponent => "the chosen opponent"
  | .stepPlayers _ => "that player"
  | .matching rel .any =>
    match rel with
    | .you => "you"
    | .opponent => "each opponent"
    | .teammate => "each teammate"
    | .anyPlayer => "each player"
  | .matching rel pred =>
    let relS :=
      match rel with
      | .you => "you"
      | .opponent => "each opponent"
      | .teammate => "each teammate"
      | .anyPlayer => "each player"
    s!"{relS} who {printPlayerPred { ctx with capitalize := false } pred}"
  | .chosenBy _ cnt filter =>
    s!"{renderCountRange cnt} chosen {printPlayerFilter { ctx with plural := true, capitalize := false } filter}"

private partial def printZoneSetSuffix (ctx : PrintCtx) (zs : ZoneSetSpec) : Option String :=
  if zs.zones == #[.battlefield] then none
  else if zs.zones == #[.stack] then some "on the stack"
  else if zs.zones == #[.exile] then some "in exile"
  else if zs.zones == #[.command] then some "in the command zone"
  else
    let ownerPrefix : String :=
      match zs.owner with
      | .any => "a "
      | .matching { relation := .you, pred := .any } => "your "
      | .matching { relation := .opponent, pred := .any } => "an opponent's "
      | .matching pf => s!"{printPlayerFilter { ctx with capitalize := false } pf}'s "
      | .ofPlayer .you => "your "
      | .ofPlayer pe => s!"{printPlayerExpr { ctx with capitalize := false } pe}'s "
    let zoneWords := zs.zones.toList.map ZoneKind.englishName
    some s!"in {ownerPrefix}{orJoin zoneWords}"

private partial def printObjectPredParts (ctx : PrintCtx) (pred : ObjectPred)
    (zones : ZoneSetSpec) : String := Id.run do
  let rawAtoms : List ObjectPred :=
    match pred with
    | .all ps => ps.toList
    | single => [single]
  let worthyAtoms : List ObjectPred :=
    [.hasSupertype .legendary,
     .not (.hasSubtype (.literal .villain)),
     .any #[.hasColor (.literal .red), .hasColor (.literal .white)],
     .hasType .creature]
  let isWorthy := worthyAtoms.all (fun w => rawAtoms.contains w)
  let atoms : List ObjectPred :=
    if isWorthy then rawAtoms.filter (fun a => !worthyAtoms.contains a)
    else rawAtoms
  let isBf := zones.zones == #[.battlefield]
  let isStack := zones.zones == #[.stack]
  let hasCard := atoms.any (· == .isKind .card)
  let hasPermCard := atoms.any (· == .isKind .permanentCard)
  let hasSpell := atoms.any (· == .isKind .spell)
  let hasToken := atoms.any (· == .isToken true)
  let typeIsHead := !hasCard && !hasPermCard && !hasSpell && !hasToken && isBf
  let mut preMods : List String := []
  let mut colorMods : List String := []
  let mut nonTypeMods : List String := []
  let mut superMods : List String := []
  let mut subtypeMods : List String := []
  let mut typeWords : List String := []
  let mut ctrlSuffix : List String := []
  let mut withClauses : List String := []
  let mut withoutClauses : List String := []
  let mut thatClauses : List String := []
  if isWorthy then
    preMods := preMods ++ ["worthy"]
    typeWords := typeWords ++ [if ctx.plural && typeIsHead then "creatures" else "creature"]
  for a in atoms do
    match a with
    | .otherThan .this =>
      preMods := preMods ++ [if ctx.plural then "other" else "another"]
    | .otherThan .attachedHost =>
      thatClauses := thatClauses ++ ["other than enchanted creature"]
    | .otherThan _ =>
      preMods := preMods ++ [if ctx.plural then "other" else "another"]
    | .tapped true => preMods := preMods ++ ["tapped"]
    | .tapped false => preMods := preMods ++ ["untapped"]
    | .combatRole .attacking => preMods := preMods ++ ["attacking"]
    | .combatRole .blocking => preMods := preMods ++ ["blocking"]
    | .combatRole .blocked => preMods := preMods ++ ["blocked"]
    | .combatRole .unblocked => preMods := preMods ++ ["unblocked"]
    | .combatRole .attackingAlone => thatClauses := thatClauses ++ ["that's attacking alone"]
    | .combatRole (.attackingPlayer who) =>
      thatClauses := thatClauses ++ [s!"attacking {printPlayerExpr { ctx with capitalize := false } who}"]
    | .combatRole (.blockingObject o) =>
      thatClauses := thatClauses ++ [s!"blocking {printObjectExpr { ctx with capitalize := false } o}"]
    | .isFaceDown true => preMods := preMods ++ ["face-down"]
    | .isFaceDown false => preMods := preMods ++ ["face-up"]
    | .isToken true => pure ()
    | .isToken false => preMods := preMods ++ ["nontoken"]
    | .isCommander => preMods := preMods ++ ["commander"]
    | .isCopy true => thatClauses := thatClauses ++ ["that's a copy"]
    | .isCopy false => thatClauses := thatClauses ++ ["that isn't a copy"]
    | .phasedOut true => thatClauses := thatClauses ++ ["that's phased out"]
    | .phasedOut false => pure ()
    | .hasColor (.literal c) => colorMods := colorMods ++ [c.englishName]
    | .hasColor .chosenOnSource => thatClauses := thatClauses ++ ["of the chosen color"]
    | .hasColor .commanderIdentity => thatClauses := thatClauses ++ ["in your commander's color identity"]
    | .not (.hasColor (.literal c)) => colorMods := colorMods ++ [s!"non{c.englishName}"]
    | .colorCount .eq 0 => colorMods := colorMods ++ ["colorless"]
    | .colorCount .eq 1 => colorMods := colorMods ++ ["monocolored"]
    | .colorCount .ge 2 => colorMods := colorMods ++ ["multicolored"]
    | .colorCount op n =>
      thatClauses := thatClauses ++ [s!"with {renderCmpBound op (toString n)} colors"]
    | .hasSupertype s => superMods := superMods ++ [s.oracleWord]
    | .not (.hasSupertype s) => superMods := superMods ++ [s!"non{s.oracleWord}"]
    | .hasSubtype (.literal s) => subtypeMods := subtypeMods ++ [s.englishName]
    | .hasSubtype .chosenOnSource | .hasSubtype (.fromStep _) =>
      thatClauses := thatClauses ++ ["of the chosen type"]
    | .not (.hasSubtype (.literal s)) => subtypeMods := subtypeMods ++ [s!"non-{s.englishName}"]
    | .hasType t =>
      typeWords := typeWords ++ [if ctx.plural && typeIsHead then t.pluralName else t.oracleWord]
    | .not (.hasType t) => nonTypeMods := nonTypeMods ++ [s!"non{t.oracleWord}"]
    | .isKind _ => pure ()
    | .any ps =>
      if a == ObjectPred.historic then
        superMods := superMods ++ ["historic"]
      else if ps == #[.combatRole .attacking, .combatRole .blocking] then
        preMods := preMods ++ ["attacking or blocking"]
      else if ps.size == 2 &&
          (match ps[0]!, ps[1]! with
           | .stat .power op1 rhs1, .stat .toughness op2 rhs2 => op1 == op2 && rhs1 == rhs2
           | _, _ => false) then
        match ps[0]! with
        | .stat .power op rhs =>
          withClauses := withClauses ++
            [s!"power or toughness {renderCmpBound op (printValueExpr { ctx with capitalize := false } rhs)}"]
        | _ => pure ()
      else if ps.all (fun | .hasType _ => true | _ => false) then
        let ws := ps.toList.filterMap (fun
          | .hasType t => some (if ctx.plural && typeIsHead then t.pluralName else t.oracleWord)
          | _ => none)
        typeWords := typeWords ++ [orJoin ws]
      else if ps.all (fun | .hasColor (.literal _) => true | _ => false) then
        let cs := ps.toList.filterMap (fun
          | .hasColor (.literal c) => some c.englishName
          | _ => none)
        colorMods := colorMods ++ [orJoin cs]
      else if ps.all (fun | .hasSubtype (.literal _) => true | _ => false) then
        let ss := ps.toList.filterMap (fun
          | .hasSubtype (.literal s) => some s.englishName
          | _ => none)
        subtypeMods := subtypeMods ++ [orJoin ss]
      else
        let mixedWord? : ObjectPred → Option String
          | .hasType t => some (if ctx.plural && typeIsHead then t.pluralName else t.oracleWord)
          | .hasSubtype (.literal s) => some (if ctx.plural && typeIsHead then s.pluralName else s.englishName)
          | .hasSupertype s => some s.oracleWord
          | .all #[.not (.hasType neg), .hasType t]
          | .all #[.hasType t, .not (.hasType neg)] =>
            some s!"non{neg.oracleWord} {if ctx.plural && typeIsHead then t.pluralName else t.oracleWord}"
          | .all #[.not (.hasSubtype (.literal s)), .hasType t]
          | .all #[.hasType t, .not (.hasSubtype (.literal s))] =>
            some s!"non-{s.englishName} {if ctx.plural && typeIsHead then t.pluralName else t.oracleWord}"
          | _ => none
        let mixedWords := ps.toList.filterMap mixedWord?
        if mixedWords.length == ps.size && !mixedWords.isEmpty then
          typeWords := typeWords ++ [orJoin mixedWords]
        else
          thatClauses := thatClauses ++
            [String.intercalate " or " (ps.toList.map (printObjectPredParts ctx · zones))]
    | .controlledBy { relation := .you, pred := .any } =>
      ctrlSuffix := ctrlSuffix ++ ["you control"]
    | .controlledBy { relation := .opponent, pred := .any } =>
      ctrlSuffix := ctrlSuffix ++ ["an opponent controls"]
    | .controlledBy { relation := .teammate, pred := .any } =>
      ctrlSuffix := ctrlSuffix ++ ["a teammate controls"]
    | .controlledBy pf =>
      ctrlSuffix := ctrlSuffix ++ [s!"{printPlayerFilter { ctx with capitalize := false } pf} controls"]
    | .ownedBy { relation := .you, pred := .any } =>
      ctrlSuffix := ctrlSuffix ++ ["you own"]
    | .ownedBy { relation := .opponent, pred := .any } =>
      ctrlSuffix := ctrlSuffix ++ ["an opponent owns"]
    | .ownedBy pf =>
      ctrlSuffix := ctrlSuffix ++ [s!"{printPlayerFilter { ctx with capitalize := false } pf} owns"]
    | .hasKeyword kw => withClauses := withClauses ++ [kw.oracleName]
    | .not (.hasKeyword kw) => withoutClauses := withoutClauses ++ [kw.oracleName]
    | .stat k op rhs =>
      withClauses := withClauses ++
        [s!"{k.oracleWord} {renderCmpBound op (printValueExpr { ctx with capitalize := false } rhs)}"]
    | .statParity k .odd => withClauses := withClauses ++ [s!"odd {k.oracleWord}"]
    | .statParity k .even => withClauses := withClauses ++ [s!"even {k.oracleWord}"]
    | .statParity k .chosenOnSource | .statParity k (.fromStep _) =>
      withClauses := withClauses ++ [s!"{k.oracleWord} of the chosen quality"]
    | .counterCount (some k) .ge (.const 1) =>
      withClauses := withClauses ++ [s!"{k.countersPhrase 1} on it"]
    | .counterCount (some k) .eq (.const 0) =>
      withClauses := withClauses ++ [s!"no {k.oracleName} counters on it"]
    | .counterCount (some k) op rhs =>
      withClauses := withClauses ++
        [s!"{renderCmpBound op (printValueExpr { ctx with capitalize := false } rhs)} {k.oracleName} counters on it"]
    | .counterCount none .ge (.const 1) =>
      withClauses := withClauses ++ ["a counter on it"]
    | .counterCount none .eq (.const 0) =>
      withClauses := withClauses ++ ["no counters on it"]
    | .counterCount none op rhs =>
      withClauses := withClauses ++
        [s!"{renderCmpBound op (printValueExpr { ctx with capitalize := false } rhs)} counters on it"]
    | .named (.literal n) => thatClauses := thatClauses ++ [s!"named {n}"]
    | .named .chosenOnSource => thatClauses := thatClauses ++ ["with the chosen name"]
    | .hasDesignation .ringBearer => thatClauses := thatClauses ++ ["that's a Ring-bearer"]
    | .hasDesignation .goaded => preMods := preMods ++ ["goaded"]
    | .hasDesignation .prepared => preMods := preMods ++ ["prepared"]
    | .hasDesignation .harnessed => preMods := preMods ++ ["harnessed"]
    | .sameAs .this => thatClauses := thatClauses ++ [s!"that is {ctx.selfRef}"]
    | .sameAs _ => thatClauses := thatClauses ++ ["that is that object"]
    | .attachedTo host =>
      thatClauses := thatClauses ++ [s!"attached to {printObjectExpr { ctx with capitalize := false } host}"]
    | .hasAttachment f =>
      withClauses := withClauses ++ [s!"{printObjectFilter { ctx with capitalize := false } f} attached to it"]
    | .targets (.object o) =>
      thatClauses := thatClauses ++ [s!"that targets {printObjectExpr { ctx with capitalize := false } o}"]
    | .targets (.player p) =>
      thatClauses := thatClauses ++ [s!"that targets {printPlayerExpr { ctx with capitalize := false } p}"]
    | .targets (.either o p) =>
      thatClauses := thatClauses ++
        [s!"that targets {printObjectExpr { ctx with capitalize := false } o} or {printPlayerExpr { ctx with capitalize := false } p}"]
    | .shares ch o =>
      match ch with
      | .name =>
        thatClauses := thatClauses ++ [s!"with the same name as {printObjectExpr { ctx with capitalize := false } o}"]
      | _ =>
        let chS :=
          match ch with
          | .color => "a color"
          | .cardType => "a card type"
          | .creatureType => "a creature type"
          | .subtype => "a subtype"
          | .name => "a name"
        thatClauses := thatClauses ++ [s!"that shares {chS} with {printObjectExpr { ctx with capitalize := false } o}"]
    | .wasCast => thatClauses := thatClauses ++ ["that was cast"]
    | .castFrom z => thatClauses := thatClauses ++ [s!"that was cast from {renderZonePhrase z}"]
    | .enteredThisTurn => thatClauses := thatClauses ++ ["that entered this turn"]
    | .attackedThisTurn => thatClauses := thatClauses ++ ["that attacked this turn"]
    | .dealtDamageThisTurn combatOnly rec? thisTurnOnly =>
      let dmg := if combatOnly then "combat damage" else "damage"
      let recS :=
        match rec? with
        | none | some .any => ""
        | some (.player pf) => s!" to {printPlayerFilter { ctx with capitalize := false } pf}"
        | some (.object f) => s!" to {printObjectFilter { ctx with capitalize := false } f}"
        | some (.playerOrObject pf f) =>
          s!" to {printPlayerFilter { ctx with capitalize := false } pf} or {printObjectFilter { ctx with capitalize := false } f}"
      let whenS := if thisTurnOnly then " this turn" else ""
      thatClauses := thatClauses ++ [s!"that dealt {dmg}{recS}{whenS}"]
    | .wasDealtDamageThisTurn =>
      thatClauses := thatClauses ++ ["that was dealt damage this turn"]
    | .receivedCounterThisTurn kind? byPlayer? =>
      let kS := match kind? with
        | some k => s!"one or more {k.oracleName} counters"
        | none => "one or more counters"
      let whoS := match byPlayer? with
        | some { relation := .you, pred := .any } => "you've put"
        | some pf => s!"{printPlayerFilter { ctx with capitalize := false } pf} put"
        | none => "had"
      if byPlayer?.isSome then
        thatClauses := thatClauses ++ [s!"that {whoS} {kS} on this turn"]
      else
        thatClauses := thatClauses ++ [s!"that had {kS} put on it this turn"]
    | .putIntoGraveyardFromBattlefieldThisTurn =>
      thatClauses := thatClauses ++ ["that were put there from the battlefield this turn"]
    | .chosenAnchorIs anchor =>
      thatClauses := thatClauses ++ [s!"whose chosen option is {anchor}"]
    | .not inner =>
      thatClauses := thatClauses ++ [s!"that isn't {printObjectPredParts ctx inner zones}"]
    | .all _ => pure ()
  let headNoun : List String :=
    if hasSpell then
      typeWords ++ [if ctx.plural then "spells" else "spell"]
    else if hasPermCard then
      typeWords ++ [if ctx.plural then "permanent cards" else "permanent card"]
    else if hasCard then
      typeWords ++ [if ctx.plural then "cards" else "card"]
    else if hasToken then
      typeWords ++ [if ctx.plural then "tokens" else "token"]
    else if !typeWords.isEmpty then
      if isStack then typeWords ++ [if ctx.plural then "spells" else "spell"]
      else if !isBf then typeWords ++ [if ctx.plural then "cards" else "card"]
      else typeWords
    else if !subtypeMods.isEmpty then
      if isStack then [if ctx.plural then "spells" else "spell"]
      else if !isBf then [if ctx.plural then "cards" else "card"]
      else []
    else if isStack then
      [if ctx.plural then "spells" else "spell"]
    else if isBf then
      [if ctx.plural then "permanents" else "permanent"]
    else
      [if ctx.plural then "cards" else "card"]
  let zoneSuffix :=
    match printZoneSetSuffix ctx zones with
    | some z => [z]
    | none => []
  let withSuffix :=
    if withClauses.isEmpty then []
    else ["with " ++ String.intercalate " and " withClauses]
  let withoutSuffix :=
    if withoutClauses.isEmpty then []
    else ["without " ++ String.intercalate " and " withoutClauses]
  let parts :=
    preMods ++ colorMods ++ nonTypeMods ++ superMods ++ subtypeMods ++ headNoun ++
      ctrlSuffix ++ zoneSuffix ++ withSuffix ++ withoutSuffix ++ thatClauses
  return String.intercalate " " (parts.filter (!·.isEmpty))

private partial def printObjectFilter (ctx : PrintCtx) (f : ObjectFilter) : String :=
  printObjectPredParts ctx f.pred f.zones

private partial def printObjectExpr (ctx : PrintCtx) : ObjectExpr → String
  | .this => ctx.selfRef
  | .target _ => "target"
  | .allTargets => "each target"
  | .attachedHost => "enchanted or equipped permanent"
  | .triggerSubject => "that object"
  | .targetsOf stackObj => s!"objects targeted by {printObjectExpr { ctx with capitalize := false } stackObj}"
  | .stepObjects _ => "those objects"
  | .linkedExile src => s!"cards exiled with {printObjectExpr { ctx with capitalize := false } src}"
  | .costPaidObjects => "those exiled cards"
  | .inZones zs pred => printObjectPredParts ctx pred zs
  | .topOfLibrary owner cnt =>
    let whoS :=
      match owner with
      | .you => "your"
      | pe => s!"{printPlayerExpr { ctx with capitalize := false } pe}'s"
    match cnt with
    | .const 1 => s!"the top card of {whoS} library"
    | _ => s!"the top {printValueExpr { ctx with capitalize := false } cnt} cards of {whoS} library"
  | .extremum dir m among =>
    let adj := match dir with | .max => "greatest" | .min => "least"
    s!"{printObjectExpr { ctx with plural := false, capitalize := false } among} with the {adj} {m.oracleWord}"
  | .filter objs pred =>
    s!"{printObjectExpr { ctx with capitalize := false } objs} matching {printObjectPredParts { ctx with capitalize := false } pred .battlefield}"
  | .union es =>
    String.intercalate " and " (es.toList.map (printObjectExpr { ctx with capitalize := false }))
  | .diff a b =>
    s!"{printObjectExpr { ctx with capitalize := false } a} other than {printObjectExpr { ctx with capitalize := false } b}"

private partial def printValueExpr (ctx : PrintCtx) : ValueExpr → String
  | .const n => toString n
  | .chosenX => "X"
  | .eventAmount => "that amount"
  | .objectStat k obj =>
    s!"{printObjectExpr { ctx with plural := false, capitalize := false } obj}'s {k.oracleWord}"
  | .counterCount (some k) obj =>
    s!"the number of {k.oracleName} counters on {printObjectExpr { ctx with plural := false, capitalize := false } obj}"
  | .counterCount none obj =>
    s!"the number of counters on {printObjectExpr { ctx with plural := false, capitalize := false } obj}"
  | .aggregate .count _ objs =>
    s!"the number of {printObjectExpr { ctx with plural := true, capitalize := false } objs}"
  | .aggregate .sum (.stat k) objs =>
    s!"the total {k.oracleWord} of {printObjectExpr { ctx with plural := true, capitalize := false } objs}"
  | .aggregate .sum (.counterCount (some k)) objs =>
    s!"the total number of {k.oracleName} counters on {printObjectExpr { ctx with plural := true, capitalize := false } objs}"
  | .aggregate .sum _ objs =>
    s!"the total among {printObjectExpr { ctx with plural := true, capitalize := false } objs}"
  | .aggregate .max (.stat k) objs =>
    s!"the greatest {k.oracleWord} among {printObjectExpr { ctx with plural := true, capitalize := false } objs}"
  | .aggregate .min (.stat k) objs =>
    s!"the least {k.oracleWord} among {printObjectExpr { ctx with plural := true, capitalize := false } objs}"
  | .aggregate .countDistinct (.stat k) objs =>
    s!"the number of different {k.pluralOracleWord} among {printObjectExpr { ctx with plural := true, capitalize := false } objs}"
  | .aggregate .max _ objs =>
    s!"the greatest value among {printObjectExpr { ctx with plural := true, capitalize := false } objs}"
  | .aggregate .min _ objs =>
    s!"the least value among {printObjectExpr { ctx with plural := true, capitalize := false } objs}"
  | .aggregate .countDistinct _ objs =>
    s!"the number of different values among {printObjectExpr { ctx with plural := true, capitalize := false } objs}"
  | .basicLandTypeCount objs =>
    s!"the number of basic land types among {printObjectExpr { ctx with plural := true, capitalize := false } objs}"
  | .cardTypeCount objs =>
    s!"the number of card types among {printObjectExpr { ctx with plural := true, capitalize := false } objs}"
  | .subtypeCount cat objs =>
    s!"the number of {cat.oraclePhrase} among {printObjectExpr { ctx with plural := true, capitalize := false } objs}"
  | .colorCountAmong objs =>
    s!"the number of colors among {printObjectExpr { ctx with plural := true, capitalize := false } objs}"
  | .playerMetric m who =>
    let isYou := who == .you
    let poss := if isYou then "your" else s!"{printPlayerExpr { ctx with capitalize := false } who}'s"
    let subj := if isYou then "you" else printPlayerExpr { ctx with capitalize := false } who
    match m with
    | .one => s!"the number of players matching {subj}"
    | .life => s!"{poss} life total"
    | .handSize => s!"the number of cards in {poss} hand"
    | .librarySize => s!"the number of cards in {poss} library"
    | .graveyardSize => s!"the number of cards in {poss} graveyard"
    | .landsPlayedThisTurn =>
      if isYou then "the number of lands you've played this turn"
      else s!"the number of lands {subj} played this turn"
    | .spellsCastThisTurn =>
      if isYou then "the number of spells you've cast this turn"
      else s!"the number of spells {subj} cast this turn"
    | .cardsDrawnThisTurn =>
      if isYou then "the number of cards you've drawn this turn"
      else s!"the number of cards {subj} drew this turn"
    | .cardsDiscardedThisTurn =>
      if isYou then "the number of cards you've discarded this turn"
      else s!"the number of cards {subj} discarded this turn"
    | .cardsMilledThisTurn =>
      if isYou then "the number of cards put into your graveyard from your library this turn"
      else s!"the number of cards put into {poss} graveyard from {poss} library this turn"
    | .otherSpellsManaValueThisTurn =>
      if isYou then "the total mana value of other spells you've cast this turn"
      else s!"the total mana value of other spells {subj} cast this turn"
    | .lifeGainedThisTurn => s!"the amount of life {subj} gained this turn"
    | .lifeLostThisTurn => s!"the amount of life {subj} lost this turn"
    | .unspentMana =>
      if isYou then "the amount of unspent mana you have"
      else s!"the amount of unspent mana {subj} has"
    | .poisonCounters =>
      if isYou then "the number of poison counters you have"
      else s!"the number of poison counters {subj} has"
    | .opponentsCount =>
      if isYou then "the number of opponents you have"
      else s!"the number of opponents {subj} has"
  | .maxControlled who pred =>
    let whoS := printPlayerFilter { ctx with plural := false, capitalize := false } who
    let noun := printObjectPredParts { ctx with plural := true, capitalize := false } pred .battlefield
    s!"the greatest number of {noun} {whoS} controls"
  | .manaSymbols (some c) objs =>
    s!"the number of {c.englishName} mana symbols in the mana costs of {printObjectExpr { ctx with plural := true, capitalize := false } objs}"
  | .manaSymbols none objs =>
    s!"the number of mana symbols in the mana costs of {printObjectExpr { ctx with plural := true, capitalize := false } objs}"
  | .manaSpent obj =>
    s!"the amount of mana spent to cast {printObjectExpr { ctx with plural := false, capitalize := false } obj}"
  | .stepMetric .movedCount _ => "the number of cards moved this way"
  | .stepMetric .createdCount _ => "the number of tokens created this way"
  | .stepMetric .damageDealt _ => "the amount of damage dealt this way"
  | .stepMetric .excessDamage _ => "the excess damage dealt this way"
  | .stepMetric .lifeChanged _ => "that much life"
  | .stepMetric .countersChanged _ => "the number of counters modified this way"
  | .stepMetric .sumPower _ => "the total power of creatures affected this way"
  | .stepMetric .chosenNumber _ => "the chosen number"
  | .binary .mul (.const 2) x => s!"twice {printValueExpr { ctx with capitalize := false } x}"
  | .binary .divFloor x (.const 2) =>
    s!"half {printValueExpr { ctx with capitalize := false } x}, rounded down"
  | .binary .add a b =>
    s!"{printValueExpr { ctx with capitalize := false } a} plus {printValueExpr { ctx with capitalize := false } b}"
  | .binary .sub a b =>
    s!"{printValueExpr { ctx with capitalize := false } a} minus {printValueExpr { ctx with capitalize := false } b}"
  | .binary .mul a b =>
    s!"{printValueExpr { ctx with capitalize := false } a} times {printValueExpr { ctx with capitalize := false } b}"
  | .binary .divFloor a b =>
    s!"{printValueExpr { ctx with capitalize := false } a} divided by {printValueExpr { ctx with capitalize := false } b}, rounded down"
  | .binary .max a b =>
    s!"the greater of {printValueExpr { ctx with capitalize := false } a} and {printValueExpr { ctx with capitalize := false } b}"
  | .binary .min a b =>
    s!"the lesser of {printValueExpr { ctx with capitalize := false } a} and {printValueExpr { ctx with capitalize := false } b}"

end

instance : ToOracle PlayerFilter where toOracle ctx x := applyCap ctx (printPlayerFilter ctx x)
instance : ToOracle PlayerPred where toOracle ctx x := applyCap ctx (printPlayerPred ctx x)
instance : ToOracle PlayerExpr where toOracle ctx x := applyCap ctx (printPlayerExpr ctx x)
instance : ToOracle ObjectPred where
  toOracle ctx x := applyCap ctx (printObjectPredParts ctx x .battlefield)
instance : ToOracle ObjectFilter where toOracle ctx x := applyCap ctx (printObjectFilter ctx x)
instance : ToOracle ObjectExpr where toOracle ctx x := applyCap ctx (printObjectExpr ctx x)
instance : ToOracle ValueExpr where toOracle ctx x := applyCap ctx (printValueExpr ctx x)

instance : ToOracle LibraryPosSpec where
  toOracle ctx
    | .top => applyCap ctx "on top of its owner's library"
    | .bottom => applyCap ctx "on the bottom of its owner's library"
    | .bottomRandom => applyCap ctx "on the bottom of its owner's library in a random order"
    | .fromTop v =>
      applyCap ctx s!"{printValueExpr { ctx with capitalize := false } v} from the top of its owner's library"
    | .shuffledIn => applyCap ctx "shuffled into its owner's library"

private def printEventHistory (ctx : PrintCtx) : EventHistoryPred → String
  | .scriedThisTurn { relation := .you, pred := .any } => "you've scried this turn"
  | .scriedThisTurn pf => s!"{printPlayerFilter { ctx with capitalize := false } pf} scried this turn"
  | .surveilledThisTurn { relation := .you, pred := .any } => "you've surveilled this turn"
  | .surveilledThisTurn pf =>
    s!"{printPlayerFilter { ctx with capitalize := false } pf} surveilled this turn"
  | .eventOccurredThisTurn who pat => printEventAtTurn ctx who pat "this turn"
  | .eventOccurredLastTurn who pat => printEventAtTurn ctx who pat "last turn"
  | .firstResolutionThisTurn => "this is the first time this ability has resolved this turn"
  | .nthResolutionThisTurn 1 => "this is the first time this ability has resolved this turn"
  | .nthResolutionThisTurn 2 => "this is the second time this ability has resolved this turn"
  | .nthResolutionThisTurn 3 => "this is the third time this ability has resolved this turn"
  | .nthResolutionThisTurn n => s!"this is time {n} this ability has resolved this turn"
  | .optionalOnceUnusedThisTurn => "this optional effect hasn't been used this turn"
where
  printEventAtTurn (ctx : PrintCtx) (who : PlayerFilter) (pat : EventPattern) (whenS : String) : String :=
    let whoS :=
      match who with
      | { relation := .you, pred := .any } => "you"
      | pf => printPlayerFilter { ctx with capitalize := false } pf
    match pat with
    | .permanentEntered pred =>
      let noun := printObjectPredParts { ctx with plural := false, capitalize := false } pred .battlefield
      let under :=
        match who with
        | { relation := .anyPlayer, pred := .any } => ""
        | { relation := .you, pred := .any } => " under your control"
        | pf => s!" under {printPlayerFilter { ctx with capitalize := false } pf}'s control"
      s!"{indefinite noun} {noun} entered{under} {whenS}"
    | .permanentDied pred 1 =>
      let noun := printObjectPredParts { ctx with plural := false, capitalize := false } pred .battlefield
      s!"{indefinite noun} {noun} died {whenS}"
    | .permanentDied pred n =>
      let noun := printObjectPredParts { ctx with plural := true, capitalize := false } pred .battlefield
      s!"{englishNumber n} or more {noun} died {whenS}"
    | .permanentLeftBattlefield pred =>
      let noun := printObjectPredParts { ctx with plural := false, capitalize := false } pred .battlefield
      s!"{indefinite noun} {noun} left the battlefield {whenS}"
    | .attackedWith (.all #[]) 1 => s!"{whoS} attacked {whenS}"
    | .attackedWith pred 1 =>
      let noun := printObjectPredParts { ctx with plural := false, capitalize := false } pred .battlefield
      s!"{whoS} attacked with {indefinite noun} {noun} {whenS}"
    | .attackedWith pred n =>
      let noun := printObjectPredParts { ctx with plural := true, capitalize := false } pred .battlefield
      s!"{whoS} attacked with {englishNumber n} or more {noun} {whenS}"
    | .castSpell pred =>
      let noun := printObjectPredParts { ctx with plural := false, capitalize := false } pred .stack
      s!"{whoS} cast {indefinite noun} {noun} {whenS}"
    | .drewCard 1 => s!"{whoS} drew a card {whenS}"
    | .drewCard n => s!"{whoS} drew {englishNumber n} or more cards {whenS}"
    | .discardedCard (.all #[]) => s!"{whoS} discarded a card {whenS}"
    | .discardedCard pred =>
      let noun := printObjectPredParts { ctx with plural := false, capitalize := false } pred .yourHand
      s!"{whoS} discarded {indefinite noun} {noun} {whenS}"
    | .milledCard 1 => s!"{whoS} milled a card {whenS}"
    | .milledCard n => s!"{whoS} milled {englishNumber n} or more cards {whenS}"
    | .gainedLife 1 => s!"{whoS} gained life {whenS}"
    | .gainedLife n => s!"{whoS} gained {n} or more life {whenS}"
    | .lostLife 1 => s!"{whoS} lost life {whenS}"
    | .lostLife n => s!"{whoS} lost {n} or more life {whenS}"
    | .dealtDamage true false => s!"{whoS} were dealt combat damage {whenS}"
    | .dealtDamage false true => s!"{whoS} were dealt noncombat damage {whenS}"
    | .dealtDamage _ _ => s!"{whoS} were dealt damage {whenS}"
    | .activatedLoyalty => s!"{whoS} activated a loyalty ability {whenS}"
    | .beheld sub => s!"{whoS} beheld {indefinite sub.englishName} {sub.englishName} {whenS}"
    | .proliferated => s!"{whoS} proliferated {whenS}"

private def printCastPred : CastContextPred → String
  | .wasKicked _ => "this spell was kicked"
  | .giftPromised _ => "the gift was promised"
  | .impendingPaid _ => "its impending cost was paid"
  | .teamworkPaid _ => "its teamwork cost was paid"
  | .sneakPaid _ => "its sneak cost was paid"
  | .castFrom z _ => s!"this spell was cast from {renderZonePhrase z}"
  | .manaSpentMatches .fromTreasure _ => "mana from a Treasure was spent to cast this spell"
  | .manaSpentMatches .fromSource _ => "mana produced by this permanent was spent to cast this spell"
  | .manaSpentMatches (.ofColor c) _ =>
    s!"{c.englishName} mana was spent to cast this spell"
  | .manaSpentMatches (.amount op n) _ =>
    s!"{renderCmpBound op (toString n)} mana was spent to cast this spell"
  | .manaSpentMatches (.colorCount op n) _ =>
    s!"{renderCmpBound op (toString n)} colors of mana were spent to cast this spell"
  | .manaSpentMatches (.withRider .cantBeCountered) _ =>
    "uncounterable mana was spent to cast this spell"
  | .manaSpentMatches (.withRider .gainsHaste) _ =>
    "haste-granting mana was spent to cast this spell"
  | .manaSpentMatches (.withRider (.entersWithPlusOneCounters n)) _ =>
    s!"+{n}/+{n}-counter mana was spent to cast this spell"

private partial def printCondition (ctx : PrintCtx) : Condition → String
  | .cmp op a b =>
    s!"{printValueExpr { ctx with capitalize := false } a} is {renderCmpBound op (printValueExpr { ctx with capitalize := false } b)}"
  | .exists (.inZones zs pred) =>
    let noun := printObjectPredParts { ctx with plural := false, capitalize := false } pred zs
    s!"there is {indefinite noun} {noun}"
  | .exists objs =>
    s!"there is {printObjectExpr { ctx with plural := false, capitalize := false } objs}"
  | .forAll objs pred =>
    s!"every {printObjectExpr { ctx with plural := false, capitalize := false } objs} is {printObjectPredParts { ctx with plural := false, capitalize := false } pred .battlefield}"
  | .playerPred .you (.hasDesignation .citysBlessing) => "you have the city's blessing"
  | .playerPred .you (.hasDesignation .enduringStory) => "you have an enduring story"
  | .playerPred .you .isMonarch => "you're the monarch"
  | .playerPred who pred =>
    s!"{printPlayerExpr { ctx with capitalize := false } who} {printPlayerPred { ctx with capitalize := false } pred}"
  | .castPred cp => printCastPred cp
  | .turnHistory hp => printEventHistory ctx hp
  | .stepSucceeded _ => "you do"
  | .duringStep s => s!"it's the {s.englishName}"
  | .duringPhase p => s!"it's the {p.englishName}"
  | .isYourTurn => "it's your turn"
  | .isNight => "it's night"
  | .all cs =>
    String.intercalate " and " (cs.toList.map (printCondition { ctx with capitalize := false }))
  | .any cs =>
    String.intercalate " or " (cs.toList.map (printCondition { ctx with capitalize := false }))
  | .not .isYourTurn => "it's not your turn"
  | .not .isNight => "it's day"
  | .not c => s!"not ({printCondition { ctx with capitalize := false } c})"

instance : ToOracle Condition where
  toOracle ctx c := applyCap ctx (printCondition ctx c)

instance : ToOracle DurationExpr where
  toOracle ctx d :=
    let s :=
      match d with
      | .untilEndOfTurn => "until end of turn"
      | .untilEndOfCombat => "until end of combat"
      | .untilEndOfStepOrPhase sp => s!"until end of the {sp.englishName}"
      | .untilStepOrPhase sp => s!"until the {sp.englishName}"
      | .untilNextTurnOf .you => "until your next turn"
      | .untilNextTurnOf who =>
        s!"until {printPlayerExpr { ctx with capitalize := false } who}'s next turn"
      | .untilEndOfNextTurnOf .you => "until the end of your next turn"
      | .untilEndOfNextTurnOf who =>
        s!"until the end of {printPlayerExpr { ctx with capitalize := false } who}'s next turn"
      | .whileOnBattlefield obj =>
        s!"for as long as {printObjectExpr { ctx with capitalize := false } obj} remains on the battlefield"
      | .untilLeavesBattlefield obj =>
        s!"until {printObjectExpr { ctx with capitalize := false } obj} leaves the battlefield"
      | .whileHasCounter obj k =>
        s!"for as long as {printObjectExpr { ctx with capitalize := false } obj} has {k.countersPhrase 1} on it"
      | .whileInZone obj .exile =>
        s!"for as long as {printObjectExpr { ctx with capitalize := false } obj} remains exiled"
      | .whileInZone obj z =>
        s!"for as long as {printObjectExpr { ctx with capitalize := false } obj} remains in {renderZonePhrase z}"
      | .indefinite => "for the rest of the game"
    applyCap ctx s

end Mtg.Engine
