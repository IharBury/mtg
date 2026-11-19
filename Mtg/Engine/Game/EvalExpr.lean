import Mtg.Engine.Game.Designations
import Mtg.Engine.Card.ManaSpec

/-!
# Pure Expression Evaluator (Live + LKI — CR 109.3, 400.7, 603.10, 608.2h, 611.2)

Evaluates the Layer-1 pure expression algebra (`Mtg.Engine.Card.Expr`) and
symbolic `ManaSpec` / `ManaPoolPalette` (`Mtg.Engine.Card.ManaSpec`) over
`(Game, EvalEnv)` without mutating `Game`.

Supports both:
- **Live evaluation** through CR 613 Layers 1–7d on `GameObject`s, and
- **Last-known information (LKI) / look-back evaluation** through `EventObject`
  snapshots and optional `GameSnapshot` (`EvalEnv.lookBackState?`), honoring
  CR 113.7a, CR 400.7 / 400.7d, CR 603.10a–f, CR 608.2h, and CR 702.26b.
-/

namespace Mtg.Engine

/-- Post-replacement outcome summary of a single bound instruction step
(CR 608.2c / 614.6). Populated from `EventCause.oneShotEffectId?`-filtered
`RulesEvent` slices in Phases 8–9 and already queryable by `EvalExpr`. -/
structure StepOutcome where
  objects : Array ObjectId := #[]
  players : Array PlayerId := #[]
  movedCount : Nat := 0
  createdCount : Nat := 0
  damageDealt : Nat := 0
  excessDamage : Nat := 0
  lifeChanged : Int := 0
  countersChanged : Int := 0
  sumPower : Int := 0
  chosenNumber : Int := 0
  succeeded : Bool := false
deriving Repr, Inhabited, BEq

/-- Read-only evaluation environment for pure expression queries over
`(Game, EvalEnv)` (CR 109.3 / 109.5 / 400.7 / 603.10 / 608.2h). -/
structure EvalEnv where
  /-- Controller of the spell, ability, or static ability ("you", CR 109.5). -/
  controller : PlayerId := ⟨0⟩
  /-- Source object of the spell or ability ("this permanent" / "this spell"). -/
  sourceId : Option ObjectId := none
  /-- Frozen LKI snapshot of the source if it already left its zone (CR 113.7a / 608.2h). -/
  sourceSnapshot : Option EventObject := none
  /-- Announced targets per slot (CR 115.1 / 601.2c). -/
  targetSlots : Array (Array Target) := #[]
  /-- Object that caused a trigger ("that creature" / "it"). -/
  triggerSubjectId : Option ObjectId := none
  /-- Frozen LKI snapshot of the trigger subject when available (CR 603.10 / 608.2h). -/
  triggerSubjectSnapshot : Option EventObject := none
  /-- Named player roles carried by a triggering event. -/
  triggerPlayers : Array (TriggerPlayerRole × PlayerId) := #[]
  /-- Announced value of `{X}` (CR 107.3a). -/
  chosenX : Nat := 0
  /-- Lexical bindings from earlier bound steps (`Instruction.bind`, CR 608.2c / 614.6). -/
  stepEnv : Array (VarId × StepOutcome) := #[]
  /-- Optional pre-event `GameSnapshot` for CR 603.10 look-back evaluation.
  When present, board existence and live characteristics are queried against
  this snapshot while event-log history queries consult `g.events`. -/
  lookBackState? : Option GameSnapshot := none
  /-- Explicit LKI snapshots for objects referenced after leaving their zone (CR 608.2h). -/
  lkiObjects : Array (ObjectId × EventObject) := #[]
  /-- Pre-resolved player choices for `PlayerExpr.chosenBy` (pure query). -/
  chosenPlayers : Array PlayerId := #[]
deriving Inhabited

namespace EvalEnv

/-- Construct an `EvalEnv` from a Phase-1 `CopyTokenContext`, controller, and `{X}` value. -/
def ofCopyTokenContext (controller : PlayerId := ⟨0⟩) (chosenX : Nat := 0)
    (copyCtx : CopyTokenContext := {}) : EvalEnv :=
  { controller
    sourceId := copyCtx.sourceId
    targetSlots :=
      match copyCtx.targetId with
      | some tid => #[#[.permanent tid]]
      | none => #[]
    triggerSubjectId := copyCtx.triggerSubjectId
    chosenX }

/-- Look up a bound `StepOutcome` by `VarId`. -/
def stepOutcome? (env : EvalEnv) (v : VarId) : Option StepOutcome :=
  (env.stepEnv.find? (·.1 == v)).map Prod.snd

/-- Look up an explicit LKI snapshot by `ObjectId`. -/
def lkiOf? (env : EvalEnv) (oid : ObjectId) : Option EventObject :=
  if env.sourceId == some oid && env.sourceSnapshot.isSome then env.sourceSnapshot
  else if env.triggerSubjectId == some oid && env.triggerSubjectSnapshot.isSome then
    env.triggerSubjectSnapshot
  else (env.lkiObjects.find? (·.1 == oid)).map Prod.snd

end EvalEnv

/-- Unified read-only view of an object: either a live `GameObject` evaluated
through CR 613 Layers 1–7d or a frozen `EventObject` LKI snapshot (CR 113.7a /
608.2h). -/
inductive ObjectView where
  | live (obj : GameObject)
  | lki (snap : EventObject)
deriving Repr, Inhabited, BEq

namespace ObjectView

def id? : ObjectView → Option ObjectId
  | .live o => some o.id
  | .lki eo => eo.id

def owner : ObjectView → PlayerId
  | .live o => o.owner
  | .lki eo => eo.owner

def zone : ObjectView → Zone
  | .live o => o.zone
  | .lki eo => eo.zone

def isLive : ObjectView → Bool
  | .live _ => true
  | .lki _ => false

def live? : ObjectView → Option GameObject
  | .live o => some o
  | .lki _ => none

end ObjectView

namespace EvalExpr

private def pushUnique {α : Type} [BEq α] (acc : Array α) (x : α) : Array α :=
  if acc.contains x then acc else acc.push x

private def dedupViews (views : Array ObjectView) : Array ObjectView :=
  views.foldl (fun acc v =>
    match v.id? with
    | some oid => if acc.any (fun u => u.id? == some oid) then acc else acc.push v
    | none => acc.push v) #[]

/-- Active board state to read live object characteristics from (`lookBackState?` when set). -/
@[inline] def boardState (g : Game) (env : EvalEnv) : Game :=
  env.lookBackState?.getD g

/-- Resolve an `ObjectId` to a live `GameObject` in `boardState`, falling back
to explicit LKI snapshots in `env` (`sourceSnapshot`, `triggerSubjectSnapshot`,
`lkiObjects`) or `lastKnownBefore?` only when the object is no longer in
`boardState` (CR 113.7a / 400.7 / 608.2h). `lookBackState?` selects the
CR 603.10 pre-event board. -/
def resolveObjectView? (g : Game) (env : EvalEnv) (oid : ObjectId) : Option ObjectView :=
  let st := boardState g env
  match st.findObject? oid with
  | some o => some (.live o)
  | none =>
    match env.lkiOf? oid with
    | some eo => some (.lki eo)
    | none =>
      match g.lastKnownBefore? oid with
      | some eo => some (.lki eo)
      | none => (st.lastKnownBefore? oid).map ObjectView.lki

/-- Resolve an `ObjectRef` to its `ObjectId?` and/or `ObjectView?`. -/
def resolveRefViews (g : Game) (env : EvalEnv) (ref : ObjectRef) : Array ObjectView :=
  match ref with
  | .this =>
    match env.sourceId with
    | some sid =>
      match resolveObjectView? g env sid with
      | some v => #[v]
      | none => match env.sourceSnapshot with | some eo => #[.lki eo] | none => #[]
    | none => match env.sourceSnapshot with | some eo => #[.lki eo] | none => #[]
  | .target slot =>
    let ts := env.targetSlots[slot]?.getD #[]
    ts.filterMap fun
      | .permanent oid | .card oid => resolveObjectView? g env oid
      | .player _ => none
  | .attachedHost =>
    match env.sourceId.bind (resolveObjectView? g env) with
    | some (.live src) =>
      match src.attachedTo.bind (resolveObjectView? g env) with
      | some host => #[host]
      | none => #[]
    | some (.lki eo) =>
      match eo.attachedTo.bind (resolveObjectView? g env) with
      | some host => #[host]
      | none => #[]
    | none => #[]
  | .triggerSubject =>
    match env.triggerSubjectId with
    | some sid =>
      match resolveObjectView? g env sid with
      | some v => #[v]
      | none => match env.triggerSubjectSnapshot with | some eo => #[.lki eo] | none => #[]
    | none => match env.triggerSubjectSnapshot with | some eo => #[.lki eo] | none => #[]
  | .stepVar v =>
    match env.stepOutcome? v with
    | some out => out.objects.filterMap (resolveObjectView? g env)
    | none => #[]

/-- Resolve the `ObjectId`s associated with an `ObjectRef`. -/
def resolveRefIds (g : Game) (env : EvalEnv) (ref : ObjectRef) : Array ObjectId :=
  match ref with
  | .this =>
    match env.sourceId with
    | some id => #[id]
    | none => match env.sourceSnapshot.bind (·.id) with | some id => #[id] | none => #[]
  | .target slot =>
    (env.targetSlots[slot]?.getD #[]).filterMap fun
      | .permanent oid | .card oid => some oid
      | .player _ => none
  | .attachedHost =>
    (resolveRefViews g env .attachedHost).filterMap ObjectView.id?
  | .triggerSubject =>
    match env.triggerSubjectId with
    | some id => #[id]
    | none => match env.triggerSubjectSnapshot.bind (·.id) with | some id => #[id] | none => #[]
  | .stepVar v =>
    (env.stepOutcome? v).map (·.objects) |>.getD #[]

/-! ### `ObjectView` Characteristic Accessors (Live Layers 1–7d & LKI `EventObject`) -/

def viewController? (st : Game) : ObjectView → Option PlayerId
  | .live o => st.controllerOf o
  | .lki eo => eo.controller

def viewName (st : Game) : ObjectView → String
  | .live o => st.name o
  | .lki eo => eo.name

def viewTypes (st : Game) : ObjectView → Array CardType
  | .live o => st.types o
  | .lki eo => eo.types

def viewSupertypes (st : Game) : ObjectView → Array Supertype
  | .live o => st.supertypes o
  | .lki eo => eo.supertypes

def viewSubtypes (st : Game) : ObjectView → Array CardSubtype
  | .live o => st.subtypes o
  | .lki eo => eo.subtypes

def viewColors (st : Game) : ObjectView → ColorSet
  | .live o => st.colors o
  | .lki eo => eo.colors

def viewIsToken : ObjectView → Bool
  | .live o => o.printed.isToken
  | .lki eo => eo.token

def viewIsFaceDown : ObjectView → Bool
  | .live o => o.status.faceDown
  | .lki eo => eo.faceDown

def viewIsCopy (st : Game) : ObjectView → Bool
  | .live o => o.isCopy || st.hasActiveCopy o
  | .lki eo => eo.isCopy

def viewIsCommander : ObjectView → Bool
  | .live o => o.isCommander
  | .lki eo => eo.isCommander

/-- Whether `v` is an activated, triggered, or delayed-triggered ability on the stack
(not a spell or card; CR 112.1 / 113.1). -/
def viewIsStackAbility (st : Game) : ObjectView → Bool
  | .live o =>
    o.abilityEffect.isSome || o.triggeredAbility.isSome || o.reflexiveResolution.isSome ||
      (o.zone == .stack && st.stack.any (fun e => e.objectId == o.id && e.delayedTrigger.isSome))
  | .lki eo => eo.zone == .stack && eo.types.isEmpty

/-- Whether `v` is represented by a card (not a token, stack ability, emblem, or
non-card copy; CR 108.2 / 111.6 / 114.4 / 707.10 / 707.12). -/
def viewIsCard (st : Game) : ObjectView → Bool
  | .live o =>
    !o.printed.isToken && !o.isCopy && !viewIsStackAbility st (.live o) &&
      (o.zone != .command || !(st.types o).isEmpty) && !(st.types o).isEmpty
  | .lki eo =>
    !eo.token && !(eo.zone != .battlefield && eo.isCopy) && !eo.types.isEmpty

/-- Whether `v` is a permanent card (a card with at least one permanent card type;
CR 110.4a / 108.2 / 111.6). Tokens are never permanent cards. -/
def viewIsPermanentCard (st : Game) (v : ObjectView) : Bool :=
  viewIsCard st v && (viewTypes st v).any CardType.isPermanentType

/-- Whether `v` is a spell on the stack (a card or copy of a card on the stack,
never an ability; CR 112.1). -/
def viewIsSpell (st : Game) : ObjectView → Bool
  | .live o =>
    o.zone == .stack && !viewIsStackAbility st (.live o) && !(st.types o).isEmpty
  | .lki eo =>
    eo.zone == .stack && !eo.types.isEmpty

def viewTapped : ObjectView → Bool
  | .live o => o.status.tapped
  | .lki eo => eo.tapped

def viewPhasedOut : ObjectView → Bool
  | .live o => o.status.phasedOut
  | .lki eo => eo.phasedOut

def viewAttachedTo? : ObjectView → Option ObjectId
  | .live o => o.attachedTo
  | .lki eo => eo.attachedTo

def viewChosenSubtype? : ObjectView → Option CardSubtype
  | .live o => o.status.chosenCreatureType
  | .lki eo => eo.chosenCreatureType

def viewChosenColor? : ObjectView → Option Color
  | .live o => o.status.chosenColor
  | .lki eo => eo.chosenColor

def viewChosenName? : ObjectView → Option String
  | .live o => o.status.chosenName
  | .lki eo => eo.chosenName

def viewChosenOdd? : ObjectView → Option Bool
  | .live o => o.status.chosenOdd
  | .lki eo => eo.chosenOdd

def viewCounterCount (v : ObjectView) (kind? : Option CounterKind) : Nat :=
  let bag : CounterBag :=
    match v with
    | .live o => o.status.counters
    | .lki eo => eo.counters
  match kind? with
  | some k => bag.count k
  | none => bag.foldl (fun acc (_, n) => acc + n) 0

/-- Numeric stat of `v`, returning `none` when `v` does not have that
characteristic (CR 208.3 / 209.2 / 210.2). Only creatures have power and
toughness (CR 208.3), even when a noncreature has a printed P/T box (e.g. an
uncrewed Vehicle or a permanent that lost the creature type in Layer 4). -/
def viewStat? (st : Game) (v : ObjectView) (kind : StatKind) : Option Int :=
  match v, kind with
  | .live o, .power => if st.isCreature o then some (st.power o) else none
  | .lki eo, .power => if eo.hasType .creature then eo.power else none
  | .live o, .toughness => if st.isCreature o then some (st.toughness o) else none
  | .lki eo, .toughness => if eo.hasType .creature then eo.toughness else none
  | .live o, .manaValue => some (Int.ofNat (st.objectManaValue o))
  | .lki eo, .manaValue => some (Int.ofNat eo.manaValue)
  | .live o, .loyalty =>
    if o.zone == .battlefield && st.isPlaneswalker o then
      some (Int.ofNat o.status.loyaltyCounters)
    else (st.baseCard o).loyalty
  | .lki eo, .loyalty =>
    if eo.zone == .battlefield && eo.hasType .planeswalker then
      some (Int.ofNat (eo.counters.count .loyalty))
    else eo.loyalty.map Int.ofNat
  | .live o, .defense => ((st.baseCard o).defense).map Int.ofNat
  | .lki eo, .defense => (eo.printed.bind (·.defense)).map Int.ofNat

/-- Mana cost of `v` for devotion / mana-symbol counting (CR 202.1 / 700.5 / 708.2a). -/
def viewManaCost (st : Game) : ObjectView → ManaCost
  | .live o =>
    if o.isOnBattlefield && o.status.faceDown then ManaCost.empty
    else (st.copiableValues o).manaCost
  | .lki eo =>
    if eo.faceDown then ManaCost.empty
    else ((eo.copiable.orElse (fun _ => eo.printed)).map (·.manaCost)).getD ManaCost.empty

/-- Whether `v` currently has keyword `kw` (Layer 6 for live objects, snapshot for LKI;
CR 613.1f / 702). -/
def viewHasKeyword (st : Game) (v : ObjectView) (kw : KeywordTag) : Bool :=
  match v with
  | .live o =>
    let curKw := st.currentKeywords o
    let bc := st.baseCard o
    let retains := st.retainsPrintedAbilities o
    let sas := st.staticAbilities o
    match kw with
    | .flying => st.hasFlying o
    | .firstStrike => st.hasFirstStrike o
    | .doubleStrike => st.hasDoubleStrike o
    | .deathtouch => st.hasDeathtouch o
    | .decayed => false
    | .defender => curKw.defender
    | .exalted => false
    | .flash => curKw.flash
    | .haste => st.hasHaste o
    | .hexproof => st.hasHexproof o
    | .indestructible => st.hasIndestructible o
    | .lifelink => st.hasLifelink o
    | .menace => st.hasMenace o
    | .reach => curKw.reach
    | .shadow => st.hasShadow o
    | .trample => st.hasTrample o
    | .vigilance => st.hasVigilance o
    | .changeling => curKw.changeling
    | .splitSecond => sas.any (fun | .instantSorcerySplitSecond => true | _ => false)
    | .convoke => curKw.convoke
    | .improvise => sas.any (fun | .improvise => true | _ => false)
    | .ascend => curKw.ascend
    | .storied => curKw.storied
    | .daybound => retains && bc.daybound
    | .nightbound => false
    | .prowess => curKw.prowess || (retains && bc.prowessInstances > 0)
    | .cascade => retains && bc.cascade > 0
    | .myriad => false
    | .undying => false
    | .extort => sas.any (fun | .extort => true | _ => false)
    | .ward => !(st.wardCostsOn o).isEmpty
    | .toxic => retains && bc.toxic > 0
    | .protection =>
      (retains && (!bc.protectionFromColors.isEmpty || bc.protectionFromChosenCardType)) ||
        (st.controllerOf o).any fun p =>
          (st.permanentsOf p).any fun em =>
            (st.baseCard em).protectionFromChosenCardType &&
              st.retainsPrintedAbilities em && em.status.chosenCardType.isSome
    | .landwalk none => curKw.islandwalk
    | .landwalk (some .island) => curKw.islandwalk
    | .landwalk (some _) => false
    | .param .affinity => retains && bc.affinityForSubtype.isSome
    | .param .equip => retains && bc.activatedAbilities.any (·.isEquip)
    | .param .cycling => retains && bc.cycling.isSome
    | .param .kicker => retains && bc.kicker.isSome
    | .param .gift => retains && bc.giftTreasure
    | .param .flashback => retains && bc.flashback.isSome
    | .param .morph => retains && bc.morph.isSome
    | .param .impending => retains && bc.impending.isSome
    | .param .sneak => sas.any (fun | .sneak _ => true | _ => false)
    | .param .crew => retains && bc.crew.isSome
    | .param .teamwork => retains && bc.teamwork.isSome
  | .lki eo =>
    let k := eo.keywords
    let bc? := if eo.faceDown then none else eo.copiable.orElse (fun _ => eo.printed)
    let sas := eo.staticAbilities
    match kw with
    | .flying => k.flying
    | .firstStrike => k.firstStrike
    | .doubleStrike => k.doubleStrike
    | .deathtouch => k.deathtouch
    | .decayed => false
    | .defender => k.defender
    | .exalted => false
    | .flash => k.flash
    | .haste => k.haste
    | .hexproof => k.hexproof
    | .indestructible => k.indestructible
    | .lifelink => k.lifelink
    | .menace => k.menace
    | .reach => k.reach
    | .shadow => k.shadow
    | .trample => k.trample
    | .vigilance => k.vigilance
    | .changeling => k.changeling || eo.changeling
    | .splitSecond => sas.any (fun | .instantSorcerySplitSecond => true | _ => false)
    | .convoke => k.convoke
    | .improvise => sas.any (fun | .improvise => true | _ => false)
    | .ascend => k.ascend
    | .storied => k.storied
    | .daybound => bc?.any (·.daybound)
    | .nightbound => false
    | .prowess => k.prowess || bc?.any (·.prowessInstances > 0)
    | .cascade => bc?.any (·.cascade > 0)
    | .myriad => false
    | .undying => false
    | .extort => sas.any (fun | .extort => true | _ => false)
    | .ward =>
      bc?.any (·.ward.isSome) ||
        sas.any (fun
          | .wardDiscardEnchantmentInstantOrSorcery | .wardSacrificeLegendary
          | .wardDiscardOrPay _ | .wardPoisonCounters _
          | .fra .wardDiscardCard | .fra .wardSacrificeThreePermanents => true
          | _ => false)
    | .toxic => eo.toxic > 0
    | .protection =>
      bc?.any (fun c => !c.protectionFromColors.isEmpty || c.protectionFromChosenCardType)
    | .landwalk none => k.islandwalk
    | .landwalk (some .island) => k.islandwalk
    | .landwalk (some _) => false
    | .param .affinity => bc?.any (·.affinityForSubtype.isSome)
    | .param .equip => bc?.any (fun c => c.activatedAbilities.any (·.isEquip))
    | .param .cycling => bc?.any (·.cycling.isSome)
    | .param .kicker => bc?.any (·.kicker.isSome)
    | .param .gift => bc?.any (·.giftTreasure)
    | .param .flashback => bc?.any (·.flashback.isSome)
    | .param .morph => bc?.any (·.morph.isSome)
    | .param .impending => bc?.any (·.impending.isSome)
    | .param .sneak => sas.any (fun | .sneak _ => true | _ => false)
    | .param .crew => bc?.any (·.crew.isSome)
    | .param .teamwork => bc?.any (·.teamwork.isSome)

def viewHasDesignation (st : Game) (v : ObjectView) (tag : PermanentDesignationTag) : Bool :=
  match v, tag with
  | .live o, .ringBearer => st.isAnyRingBearer o
  | .lki eo, .ringBearer =>
    match eo.id with
    | some oid =>
      eo.zone == .battlefield && !eo.phasedOut &&
        st.players.any (fun pl => pl.ringBearerId == some oid && eo.controller == some pl.id)
    | none => false
  | .live o, .goaded => o.status.goaded || !o.status.goadedBy.isEmpty
  | .lki _, .goaded => false
  | .live o, .prepared => o.status.prepared
  | .lki _, .prepared => false
  | .live o, .harnessed => o.status.harnessed
  | .lki _, .harnessed => false

/-- Source permanent/object view for `.chosenOnSource` references (CR 614.12). -/
private def sourceView? (g : Game) (env : EvalEnv) : Option ObjectView :=
  match env.sourceId with
  | some sid => resolveObjectView? g env sid
  | none => env.sourceSnapshot.map ObjectView.lki

/-- Whether `pred` explicitly requests phased-out permanents (CR 702.26b). -/
private partial def predMentionsPhasedOut : ObjectPred → Bool
  | .phasedOut true => true
  | .all ps | .any ps => ps.any predMentionsPhasedOut
  | _ => false

/-- Whether `oid` (or the stack spell it resolved from, CR 400.7d) was cast from a zone
of kind `zk` (and is not an uncast stack copy, CR 707.10). -/
def objectCastFrom (events : Array GameEvent) (oid : ObjectId) (zk : ZoneKind)
    (isCopy : Bool := false) : Bool :=
  if isCopy || GameEvent.isUncastStackCopy events oid then false
  else
    let sid := GameEvent.stackSpellIdOf events oid
    events.any fun e =>
      match e.change with
      | .rules (.cast (.spellCast s _ fromZ)) =>
        (s.id == some sid || s.id == some oid) && fromZ.kind == zk
      | .rules (.cast (.proposed obj _ fromZ way)) =>
        (obj == sid || obj == oid) &&
          (fromZ.kind == zk || (zk == .graveyard && way == .alternative "flashback"))
      | .rules (.zone (.moved _ after fromZ .stack .cast ..)) =>
        (after.id == some sid || after.id == some oid) && fromZ.kind == zk
      | _ => false

/-- Mana units recorded as spent to cast `oid` (or the spell it resolved from, CR 400.7d). -/
def manaUnitsSpentOn (events : Array GameEvent) (oid : ObjectId) : Array ManaUnit :=
  let spellId := GameEvent.stackSpellIdOf events oid
  if GameEvent.isUncastStackCopy events spellId || GameEvent.isUncastStackCopy events oid then #[]
  else
    let bound := GameEvent.castEventBound events spellId
    (events.extract 0 bound).foldl (fun acc e =>
      match e.change, e.cause? with
      | .rules (.player (.manaSpent _ units forObj)), some (.costPayment .mana _ oid?) =>
        if forObj == some spellId || oid? == some spellId then acc ++ units else acc
      | .rules (.player (.manaSpent _ units forObj)), _ =>
        if forObj == some spellId then acc ++ units else acc
      | _, _ => acc) #[]

/-- Evaluate a `PlayerMetric` for a single player `p`. -/
def evalPlayerMetricSingle (g : Game) (env : EvalEnv) (m : PlayerMetric) (p : PlayerId) : Int :=
  let st := boardState g env
  let pl := st.player p
  match m with
  | .life => pl.life
  | .handSize => Int.ofNat pl.hand.size
  | .librarySize => Int.ofNat pl.library.size
  | .graveyardSize => Int.ofNat pl.graveyard.size
  | .landsPlayedThisTurn => Int.ofNat (GameEvent.landsPlayed g.events st.turnNumber p)
  | .spellsCastThisTurn => Int.ofNat (GameEvent.spellsCast g.events st.turnNumber p)
  | .cardsDrawnThisTurn => Int.ofNat (GameEvent.draws g.events st.turnNumber p)
  | .lifeGainedThisTurn => Int.ofNat (GameEvent.lifeGained g.events st.turnNumber p)
  | .lifeLostThisTurn => Int.ofNat (GameEvent.lifeLost g.events st.turnNumber p)
  | .unspentMana => Int.ofNat pl.manaPool.total
  | .poisonCounters => Int.ofNat pl.poison
  | .opponentsCount => Int.ofNat (st.livingOpponents p).size

/-- Index of the start of the most recent combat phase on `turn` in `events`
(or `0` when no explicit combat-phase transition was logged on `turn`). -/
private def combatPhaseStartIdx (events : Array GameEvent) (turn : Nat) : Nat := Id.run do
  let mut start := 0
  for i in [0:events.size] do
    let e := events[i]!
    if e.turn == turn then
      match e.change with
      | .rules (.turn (.phaseBegan .combat))
      | .rules (.turn (.stepBegan .beginningOfCombat _)) => start := i
      | _ => pure ()
  return start

/-- Departure boundary `(batchStartIdx, departEventIdx)` in `events` for when `oid`
last left the battlefield or was removed from combat during `[startIdx, events.size)`
on `turn`. Returns `(events.size, events.size)` when `oid` did not depart in that slice. -/
private def lkiCombatDepartBounds (events : Array GameEvent) (startIdx turn : Nat)
    (oid : ObjectId) : Nat × Nat := Id.run do
  let mut departIdx : Option Nat := none
  let mut departBatch : Option BatchId := none
  for i in [startIdx:events.size] do
    let e := events[i]!
    if e.turn == turn then
      let left : Bool :=
        match e.change with
        | .rules (.zone (.moved before _ .battlefield toZ _ _ _ _)) =>
          toZ != .battlefield && before.id == some oid
        | .rules (.combat (.removedFromCombat eo)) =>
          eo.id == some oid
        | _ => false
      if left then
        departIdx := some i
        departBatch := e.batch
  match departIdx with
  | none => return (events.size, events.size)
  | some idx =>
    match departBatch with
    | none => return (idx, idx)
    | some bid =>
      let mut bStart := idx
      while bStart > startIdx && events[bStart - 1]!.batch == some bid do
        bStart := bStart - 1
      return (bStart, idx)

/-- Whether an LKI attacking creature `eo` was attacking alone when it left combat
(CR 506.5 / 608.2h): reconstructs the set of attacking creatures controlled by
`eo.controller` in the current combat phase up to `eo`'s departure batch
(`attackersDeclared` / `becameAttacking` minus earlier departures/removals). -/
private def lkiAttackingAlone (st : Game) (events : Array GameEvent) (eo : EventObject) : Bool :=
  if !eo.attacking then false
  else
    let turn := st.turnNumber
    let startIdx := combatPhaseStartIdx events turn
    let endIdx :=
      match eo.id with
      | some oid => (lkiCombatDepartBounds events startIdx turn oid).1
      | none => events.size
    let (attackers, sawSelf) : Array ObjectId × Bool := Id.run do
      let mut active : Array ObjectId := #[]
      let mut foundSelf := false
      for i in [startIdx:endIdx] do
        let e := events[i]!
        if e.turn == turn then
          match e.change with
          | .rules (.combat (.attackersDeclared p decls)) =>
            if some p == eo.controller then
              for (atk, _) in decls do
                if let some aid := atk.id then
                  active := pushUnique active aid
                  if eo.id == some aid then foundSelf := true
          | .rules (.combat (.becameAttacking atk _)) =>
            if atk.controller == eo.controller then
              if let some aid := atk.id then
                active := pushUnique active aid
                if eo.id == some aid then foundSelf := true
          | .rules (.combat (.removedFromCombat obj)) =>
            if let some rid := obj.id then
              active := active.filter (· != rid)
          | .rules (.zone (.moved before _ .battlefield toZ _ _ _ _)) =>
            if toZ != .battlefield then
              if let some lid := before.id then
                active := active.filter (· != lid)
          | _ => pure ()
      return (active, foundSelf)
    if sawSelf then
      attackers.size == 1
    else
      -- Fallback when no `attackersDeclared`/`becameAttacking` event logged `eo.id`.
      let liveOthers := st.battlefield.filter fun x =>
        x.status.attacking && st.controllerOf x == eo.controller && some x.id != eo.id
      liveOthers.isEmpty && (attackers.filter fun id => some id != eo.id).isEmpty

/-- Whether an LKI attacking creature `eo` became blocked in the current combat
phase (CR 509.1h / 608.2h), reconstructed from `CombatEvent.becameBlocked`. -/
private def lkiWasBlocked (st : Game) (events : Array GameEvent) (eo : EventObject) : Bool :=
  if !eo.attacking then false
  else
    match eo.id with
    | none => false
    | some oid =>
      let turn := st.turnNumber
      let startIdx := combatPhaseStartIdx events turn
      let endIdx := (lkiCombatDepartBounds events startIdx turn oid).2
      Id.run do
        let mut blocked := false
        for i in [startIdx:endIdx] do
          let e := events[i]!
          if e.turn == turn then
            match e.change with
            | .rules (.combat (.becameBlocked atk _)) =>
              if atk.id == some oid then blocked := true
            | .rules (.combat (.removedFromCombat obj)) =>
              if obj.id == some oid then blocked := false
            | _ => pure ()
        return blocked

/-! ### Core Mutual Evaluators -/

mutual

/-- Check whether player `p` satisfies `PlayerRelation` relative to `env.controller` (CR 102 / 810). -/
private partial def matchesPlayerRelation (st : Game) (env : EvalEnv)
    (rel : PlayerRelation) (p : PlayerId) : Bool :=
  if !st.stillInGame p then false
  else
    match rel with
    | .you => p == env.controller
    | .opponent => st.isLivingOpponentOf env.controller p
    | .teammate => st.areTeammates env.controller p
    | .anyPlayer => true

/-- Evaluate `PlayerPred` on a specific player `p`. -/
partial def evalPlayerPred (g : Game) (env : EvalEnv) (p : PlayerId) (pred : PlayerPred) : Bool :=
  let st := boardState g env
  if !st.stillInGame p then false
  else
    let pl := st.player p
    match pred with
    | .any => true
    | .all ps => ps.all (evalPlayerPred g env p)
    | .anyOf ps => ps.any (evalPlayerPred g env p)
    | .not inner => !evalPlayerPred g env p inner
    | .hasDesignation .citysBlessing => pl.citysBlessing
    | .hasDesignation .enduringStory => pl.enduringStory
    | .isMonarch => pl.isMonarch
    | .isActivePlayer => st.activePlayer == p
    | .isDefendingPlayer =>
      let defs := st.defendingPlayers
      if defs.isEmpty then st.defendingPlayer == p else defs.contains p
    | .metric m op rhs =>
      op.eval (evalPlayerMetricSingle g env m p) (evalValue g env rhs)
    | .controls filter minCount =>
      let need := evalValue g env minCount
      let subEnv := { env with controller := p }
      let controlled := (evalObjects g subEnv filter.toExpr).filter fun v =>
        viewController? st v == some p
      Int.ofNat controlled.size ≥ need

/-- Evaluate a `PlayerFilter` to living players in APNAP turn order (CR 101.4 / 800.4). -/
partial def evalPlayerFilter (g : Game) (env : EvalEnv) (pf : PlayerFilter) : Array PlayerId :=
  let st := boardState g env
  let ordered := st.playersInOrderFrom st.activePlayer (fun pl => st.stillInGame pl.id)
  ordered.filter fun p =>
    matchesPlayerRelation st env pf.relation p && evalPlayerPred g env p pf.pred

/-- Evaluate a `PlayerExpr` to zero, one, or more `PlayerId`s. -/
partial def evalPlayer (g : Game) (env : EvalEnv) (expr : PlayerExpr) : Array PlayerId :=
  let st := boardState g env
  match expr with
  | .you => if st.stillInGame env.controller then #[env.controller] else #[]
  | .activePlayer => if st.stillInGame st.activePlayer then #[st.activePlayer] else #[]
  | .defendingPlayer =>
    let defs := st.defendingPlayers
    if !defs.isEmpty then defs
    else if st.stillInGame st.defendingPlayer then #[st.defendingPlayer] else #[]
  | .monarch =>
    let ordered := st.playersInOrderFrom st.activePlayer (fun pl => st.stillInGame pl.id)
    ordered.filter fun p => (st.player p).isMonarch
  | .target slot =>
    (env.targetSlots[slot]?.getD #[]).filterMap fun
      | .player p => if st.stillInGame p then some p else none
      | .permanent _ | .card _ => none
  | .controllerOf obj =>
    (evalObjects g env obj).foldl (fun acc v =>
      match viewController? st v with
      | some p => pushUnique acc p
      | none => acc) #[]
  | .ownerOf obj =>
    (evalObjects g env obj).foldl (fun acc v => pushUnique acc v.owner) #[]
  | .triggerPlayer role =>
    match env.triggerPlayers.find? (·.1 == role) with
    | some (_, p) => #[p]
    | none =>
      match role with
      | .controllerOfSubject =>
        (resolveRefViews g env .triggerSubject).foldl (fun acc v =>
          match viewController? st v with
          | some p => pushUnique acc p
          | none => acc) #[]
      | .ownerOfSubject =>
        (resolveRefViews g env .triggerSubject).foldl (fun acc v => pushUnique acc v.owner) #[]
      | _ => #[]
  | .stepPlayers v =>
    (env.stepOutcome? v).map (·.players) |>.getD #[]
  | .matching rel pred =>
    evalPlayerFilter g env { relation := rel, pred }
  | .chosenBy _ _ filter =>
    let legal := evalPlayerFilter g env filter
    env.chosenPlayers.filter legal.contains

/-- Evaluate a `CombatRolePred` against `v` (CR 506 / 508 / 509). -/
private partial def evalCombatRole (g : Game) (env : EvalEnv) (v : ObjectView)
    (role : CombatRolePred) : Bool :=
  let st := boardState g env
  match v with
  | .live o =>
    match role with
    | .attacking => o.status.attacking
    | .attackingPlayer who =>
      if !o.status.attacking then false
      else
        let ps := evalPlayer g env who
        match o.status.attackingTarget with
        | some (.player p) => ps.contains p
        | _ => false
    | .attackingAlone =>
      o.status.attacking &&
        (st.battlefield.filter (fun x =>
          x.status.attacking && st.controllerOf x == st.controllerOf o)).size == 1
    | .blocking => !o.status.blocking.isEmpty
    | .blockingObject atkExpr =>
      let atkIds := (evalObjects g env atkExpr).filterMap ObjectView.id?
      o.status.blocking.any atkIds.contains
    | .blocked => o.status.attacking && o.status.blocked
    | .unblocked => o.status.attacking && !o.status.blocked
  | .lki eo =>
    match role with
    | .attacking => eo.attacking
    | .attackingPlayer who =>
      if !eo.attacking then false
      else
        let ps := evalPlayer g env who
        match eo.attackingTarget with
        | some (.player p) => ps.contains p
        | _ => false
    | .attackingAlone => lkiAttackingAlone st g.events eo
    | .blocking => eo.blocking
    | .blockingObject atkExpr =>
      let atkIds := (evalObjects g env atkExpr).filterMap ObjectView.id?
      eo.blockingIds.any atkIds.contains
    | .blocked => eo.attacking && lkiWasBlocked st g.events eo
    | .unblocked => eo.attacking && !lkiWasBlocked st g.events eo

/-- Evaluate `ObjectPred` on an `ObjectView` (live or LKI). -/
partial def evalObjectPred (g : Game) (env : EvalEnv) (v : ObjectView) (pred : ObjectPred) : Bool :=
  let st := boardState g env
  match pred with
  | .all ps => ps.all (evalObjectPred g env v)
  | .any ps => ps.any (evalObjectPred g env v)
  | .not inner => !evalObjectPred g env v inner
  | .hasType t => (viewTypes st v).contains t
  | .hasSupertype s => (viewSupertypes st v).contains s
  | .hasSubtype (.literal sub) => (viewSubtypes st v).contains sub
  | .hasSubtype .chosenOnSource =>
    match (sourceView? g env).bind viewChosenSubtype? with
    | some sub => (viewSubtypes st v).contains sub
    | none => false
  | .hasColor (.literal c) => (viewColors st v).contains c
  | .hasColor .chosenOnSource =>
    match (sourceView? g env).bind viewChosenColor? with
    | some c => (viewColors st v).contains c
    | none => false
  | .hasColor .commanderIdentity =>
    let pl := st.player env.controller
    if !pl.hasCommander then false
    else
      let cols := viewColors st v
      Color.all.any fun c => pl.commanderColorIdentity.contains c && cols.contains c
  | .colorCount op n => op.eval (Int.ofNat (viewColors st v).count) (Int.ofNat n)
  | .named (.literal nm) => viewName st v == nm
  | .named .chosenOnSource =>
    match (sourceView? g env).bind viewChosenName? with
    | some nm => viewName st v == nm
    | none => false
  | .hasKeyword kw => viewHasKeyword st v kw
  | .stat kind op rhs =>
    match viewStat? st v kind with
    | some lhs => op.eval lhs (evalValue g env rhs)
    | none => false
  | .statParity kind parity =>
    match viewStat? st v kind with
    | none => false
    | some val =>
      let isOdd := val.natAbs % 2 == 1
      match parity with
      | .odd => isOdd
      | .even => !isOdd
      | .chosenOnSource =>
        match (sourceView? g env).bind viewChosenOdd? with
        | some wantOdd => isOdd == wantOdd
        | none => false
  | .isToken want => viewIsToken v == want
  | .isFaceDown want => viewIsFaceDown v == want
  | .isCopy want => viewIsCopy st v == want
  | .isCommander => viewIsCommander v
  | .isKind .card => viewIsCard st v
  | .isKind .permanentCard => viewIsPermanentCard st v
  | .isKind .spell => viewIsSpell st v
  | .tapped want => viewTapped v == want
  | .phasedOut want => viewPhasedOut v == want
  | .combatRole role => evalCombatRole g env v role
  | .hasDesignation tag => viewHasDesignation st v tag
  | .counterCount k? op rhs =>
    op.eval (Int.ofNat (viewCounterCount v k?)) (evalValue g env rhs)
  | .sameAs ref =>
    match v.id? with
    | some oid => (resolveRefIds g env ref).contains oid
    | none => false
  | .otherThan ref =>
    match v.id? with
    | some oid => !(resolveRefIds g env ref).contains oid
    | none => true
  | .controlledBy pf =>
    match viewController? st v with
    | some ctrl => (evalPlayerFilter g env pf).contains ctrl
    | none => false
  | .ownedBy pf => (evalPlayerFilter g env pf).contains v.owner
  | .attachedTo hostExpr =>
    match viewAttachedTo? v with
    | some hid => ((evalObjects g env hostExpr).filterMap ObjectView.id?).contains hid
    | none => false
  | .hasAttachment attFilter =>
    match v.id? with
    | none => false
    | some oid =>
      (evalObjects g env attFilter.toExpr).any (fun att => viewAttachedTo? att == some oid)
  | .targets tgtExpr =>
    match v.id? with
    | none => false
    | some oid =>
      match st.stack.find? (·.objectId == oid) with
      | none => false
      | some entry =>
        let matchObj (oe : ObjectExpr) : Bool :=
          let ids := (evalObjects g env oe).filterMap ObjectView.id?
          entry.targets.any fun
            | .permanent id | .card id => ids.contains id
            | .player _ => false
        let matchPl (pe : PlayerExpr) : Bool :=
          let pids := evalPlayer g env pe
          entry.targets.any fun
            | .player p => pids.contains p
            | .permanent _ | .card _ => false
        match tgtExpr with
        | .object oe => matchObj oe
        | .player pe => matchPl pe
        | .either oe pe => matchObj oe || matchPl pe
  | .shares ch withExpr =>
    let others := evalObjects g env withExpr
    let myCols := viewColors st v
    let myTypes := viewTypes st v
    let mySubs := viewSubtypes st v
    others.any fun other =>
      match ch with
      | .color =>
        let oCols := viewColors st other
        Color.all.any fun c => myCols.contains c && oCols.contains c
      | .cardType =>
        let oTypes := viewTypes st other
        myTypes.any oTypes.contains
      | .creatureType =>
        let oSubs := viewSubtypes st other
        mySubs.any fun s => s.isCreatureType && oSubs.contains s
      | .subtype =>
        let oSubs := viewSubtypes st other
        mySubs.any oSubs.contains
  | .wasCast =>
    match v.id? with
    | some oid => GameEvent.wasCast g.events oid (viewIsCopy st v)
    | none => false
  | .castFrom zk =>
    match v.id? with
    | some oid => objectCastFrom g.events oid zk (viewIsCopy st v)
    | none => false
  | .enteredThisTurn =>
    match v.id? with
    | some oid => GameEvent.objectEntered g.events st.turnNumber oid
    | none => false
  | .attackedThisTurn =>
    match v.id? with
    | some oid => st.declaredAsAttackerThisTurn oid
    | none => false
  | .dealtDamageThisTurn combatOnly rec? =>
    match v.id? with
    | none => false
    | some oid =>
      let recMatches (r : DamageRecipient) : Bool :=
        match rec? with
        | none | some .any => true
        | some (.player pf) =>
          match r with
          | .player p => (evalPlayerFilter g env pf).contains p
          | _ => false
        | some (.object f) =>
          match r with
          | .permanent eo | .battle eo => evalObjectPred g env (.lki eo) f.pred
          | .player _ => false
      g.events.any fun e =>
        e.turn == st.turnNumber &&
          match e.change with
          | .rules (.damage (.dealt pkts)) =>
            pkts.any fun pkt =>
              pkt.amount > 0 && pkt.source.id == some oid &&
                (!combatOnly || pkt.combat) && recMatches pkt.recipient
          | _ => false

/-- Evaluate an `ObjectExpr` to an ordered array of `ObjectView`s (live or LKI). -/
partial def evalObjects (g : Game) (env : EvalEnv) (expr : ObjectExpr) : Array ObjectView :=
  let st := boardState g env
  match expr with
  | .this => resolveRefViews g env .this
  | .target slot => resolveRefViews g env (.target slot)
  | .attachedHost => resolveRefViews g env .attachedHost
  | .triggerSubject => resolveRefViews g env .triggerSubject
  | .stepObjects v => resolveRefViews g env (.stepVar v)
  | .inZones zs pred =>
    let allowPhased := predMentionsPhasedOut pred
    let restrictOwner := zs.owner != .any
    let owners : Array PlayerId :=
      match zs.owner with
      | .any => st.players.map (·.id)
      | .matching pf => evalPlayerFilter g env pf
      | .ofPlayer pe => evalPlayer g env pe
    let ownerOk (o : GameObject) : Bool := !restrictOwner || owners.contains o.owner
    let candidates : Array ObjectView := Id.run do
      let mut acc : Array ObjectView := #[]
      for zk in zs.zones do
        match zk with
        | .battlefield =>
          for o in st.objects do
            if o.zone == .battlefield && ownerOk o && (allowPhased || !o.status.phasedOut) then
              acc := acc.push (.live o)
        | .stack =>
          for o in st.objects do
            if o.zone == .stack && ownerOk o then acc := acc.push (.live o)
        | .exile =>
          for o in st.objects do
            if o.zone == .exile && ownerOk o then acc := acc.push (.live o)
        | .command =>
          for o in st.objects do
            if o.zone == .command && ownerOk o then acc := acc.push (.live o)
        | .ante =>
          for o in st.objects do
            if o.zone == .ante && ownerOk o then acc := acc.push (.live o)
        | .library =>
          for p in owners do
            for oid in (st.player p).library do
              if let some o := st.findObject? oid then acc := acc.push (.live o)
        | .hand =>
          for p in owners do
            for oid in (st.player p).hand do
              if let some o := st.findObject? oid then acc := acc.push (.live o)
        | .graveyard =>
          for p in owners do
            for oid in (st.player p).graveyard do
              if let some o := st.findObject? oid then acc := acc.push (.live o)
        | .outside =>
          for p in owners do
            for o in st.objects do
              if o.zone == .outside p then acc := acc.push (.live o)
      return acc
    dedupViews (candidates.filter (fun v => evalObjectPred g env v pred))
  | .topOfLibrary ownerExpr countExpr =>
    let n := (evalValue g env countExpr).toNat
    if n == 0 then #[]
    else
      let owners := evalPlayer g env ownerExpr
      Id.run do
        let mut out : Array ObjectView := #[]
        for p in owners do
          let lib := (st.player p).library
          let takeN := min n lib.size
          for k in [0:takeN] do
            let idx := lib.size - 1 - k
            if let some o := st.findObject? lib[idx]! then
              out := out.push (.live o)
        return out
  | .extremum dir metric amongExpr =>
    let pairs := (evalObjects g env amongExpr).filterMap fun v =>
      (viewStat? st v metric).map (v, ·)
    match pairs[0]? with
    | none => #[]
    | some (_, firstVal) =>
      let best := pairs.foldl (fun acc (_, x) =>
        match dir with
        | .max => Max.max acc x
        | .min => Min.min acc x) firstVal
      (pairs.filter (·.2 == best)).map Prod.fst
  | .union es =>
    dedupViews (es.foldl (fun acc e => acc ++ evalObjects g env e) #[])
  | .diff lhs rhs =>
    let rIds := (evalObjects g env rhs).filterMap ObjectView.id?
    (evalObjects g env lhs).filter fun v =>
      match v.id? with
      | some oid => !rIds.contains oid
      | none => true

/-- Evaluate a `ValueExpr` to an `Int` (CR 107.1–2 / 608.2h). -/
partial def evalValue (g : Game) (env : EvalEnv) (expr : ValueExpr) : Int :=
  let st := boardState g env
  match expr with
  | .const n => n
  | .chosenX => Int.ofNat env.chosenX
  | .objectStat kind objExpr =>
    match (evalObjects g env objExpr)[0]? with
    | some v => (viewStat? st v kind).getD 0
    | none => 0
  | .counterCount kind? objExpr =>
    match (evalObjects g env objExpr)[0]? with
    | some v => Int.ofNat (viewCounterCount v kind?)
    | none => 0
  | .aggregate op metric objsExpr =>
    let views := evalObjects g env objsExpr
    match op with
    | .count => Int.ofNat views.size
    | .sum | .max | .min | .countDistinct =>
      let vals : Array Int := views.filterMap fun v =>
        match metric with
        | .one => some 1
        | .stat sk => viewStat? st v sk
        | .counterCount k? => some (Int.ofNat (viewCounterCount v k?))
        | .colorCount => some (Int.ofNat (viewColors st v).count)
      match op with
      | .sum => vals.foldl (· + ·) 0
      | .max =>
        match vals[0]? with
        | none => 0
        | some v0 => vals.foldl Max.max v0
      | .min =>
        match vals[0]? with
        | none => 0
        | some v0 => vals.foldl Min.min v0
      | .countDistinct =>
        let uniq := vals.foldl pushUnique #[]
        Int.ofNat uniq.size
      | .count => Int.ofNat views.size
  | .basicLandTypeCount objsExpr =>
    let views := evalObjects g env objsExpr
    let basics : Array CardSubtype := #[.plains, .island, .swamp, .mountain, .forest]
    Int.ofNat (basics.filter (fun b => views.any fun v => (viewSubtypes st v).contains b)).size
  | .cardTypeCount objsExpr =>
    let views := evalObjects g env objsExpr
    let seen := views.foldl (fun acc v =>
      (viewTypes st v).foldl pushUnique acc) #[]
    Int.ofNat seen.size
  | .subtypeCount cat objsExpr =>
    let views := evalObjects g env objsExpr
    let seen := views.foldl (fun acc v =>
      (viewSubtypes st v).foldl (fun a sub =>
        if cat.matchesSubtype sub then pushUnique a sub else a) acc) #[]
    Int.ofNat seen.size
  | .playerMetric m whoExpr =>
    (evalPlayer g env whoExpr).foldl (fun acc p => acc + evalPlayerMetricSingle g env m p) 0
  | .manaSymbols col? objsExpr =>
    let views := evalObjects g env objsExpr
    let total : Nat := views.foldl (fun acc v =>
      let mc := viewManaCost st v
      let contrib : Nat :=
        match col? with
        | some c => mc.symbolsIncludingColor c
        | none =>
          mc.symbols.foldl (fun n s =>
            match s with
            | .colored _ | .colorless | .hybrid _ _ | .twobrid _ => n + 1
            | .generic _ | .x => n) 0
      acc + contrib) 0
    Int.ofNat total
  | .stepMetric m v =>
    match env.stepOutcome? v with
    | none => 0
    | some out =>
      match m with
      | .movedCount => Int.ofNat out.movedCount
      | .createdCount => Int.ofNat out.createdCount
      | .damageDealt => Int.ofNat out.damageDealt
      | .excessDamage => Int.ofNat out.excessDamage
      | .lifeChanged => out.lifeChanged
      | .countersChanged => out.countersChanged
      | .sumPower => out.sumPower
      | .chosenNumber => out.chosenNumber
  | .binary op a b => op.eval (evalValue g env a) (evalValue g env b)

end

/-! ### Top-Level Convenience Helpers & Condition / Duration / ManaSpec Evaluators -/

/-- First `ObjectView` matching `expr`, if any. -/
def evalObjectView? (g : Game) (env : EvalEnv) (expr : ObjectExpr) : Option ObjectView :=
  (evalObjects g env expr)[0]?

/-- First `ObjectId` matching `expr`, if any. -/
def evalObjectId? (g : Game) (env : EvalEnv) (expr : ObjectExpr) : Option ObjectId :=
  (evalObjectView? g env expr).bind ObjectView.id?

/-- Evaluate a `CastContextPred` against `g.events` (CR 400.7d / 707.10). -/
def evalCastPred (g : Game) (env : EvalEnv) (pred : CastContextPred) : Bool :=
  let evalObj (ref : ObjectRef) (f : ObjectId → Bool) : Bool :=
    (resolveRefIds g env ref).any f
  match pred with
  | .wasKicked ref => evalObj ref (GameEvent.wasKicked g.events)
  | .giftPromised ref => evalObj ref (GameEvent.giftPromised g.events)
  | .impendingPaid ref => evalObj ref (GameEvent.castForImpending g.events)
  | .teamworkPaid ref => evalObj ref (GameEvent.teamwork g.events)
  | .sneakPaid ref => evalObj ref fun oid => (GameEvent.sneakAttackTarget? g.events oid).isSome
  | .castFrom zk ref =>
    (resolveRefViews g env ref).any fun v =>
      match v.id? with
      | some oid => objectCastFrom g.events oid zk (viewIsCopy (boardState g env) v)
      | none => false
  | .manaSpentMatches mp ref =>
    evalObj ref fun oid =>
      let units := manaUnitsSpentOn g.events oid
      match mp with
      | .fromTreasure => g.wasCast oid && GameEvent.treasureManaSpentOn g.events (GameEvent.stackSpellIdOf g.events oid)
      | .ofColor c => units.any (·.mana == .colored c)
      | .amount op n => op.eval (Int.ofNat units.size) (Int.ofNat n)
      | .colorCount op n =>
        let cols := units.foldl (fun acc u =>
          match u.mana with
          | .colored c => pushUnique acc c
          | .colorless => acc) #[]
        op.eval (Int.ofNat cols.size) (Int.ofNat n)
      | .withRider r => units.any (fun u => u.restriction.any (·.grantsRider r))

/-- Evaluate an `EventPattern` for players `who` on a specific `targetTurn`. -/
def evalEventPatternOnTurn (g : Game) (env : EvalEnv) (targetTurn : Nat)
    (who : PlayerFilter) (pat : EventPattern) : Bool :=
  let pids := evalPlayerFilter g env who
  if pids.isEmpty then false
  else
    let anyPlayer := who == .any
    let matchesOwnerOrCtrl (p? : Option PlayerId) : Bool :=
      match p? with
      | some p => pids.contains p
      | none => anyPlayer
    match pat with
    | .permanentEntered pred =>
      g.events.any fun e =>
        e.turn == targetTurn &&
          match e.change with
          | .rules (.zone (.moved _ after fromZ .battlefield _ _ _ _)) =>
            fromZ != .battlefield && !after.phasedOut &&
              matchesOwnerOrCtrl after.controller &&
              evalObjectPred g env (.lki after) pred
          | .rules (.zone (.created obj ctrl)) =>
            obj.zone == .battlefield && !obj.phasedOut &&
              pids.contains (obj.controller.getD ctrl) &&
              evalObjectPred g env (.lki obj) pred
          | _ => false
    | .permanentDied pred =>
      g.events.any fun e =>
        e.turn == targetTurn &&
          match e.change with
          | .rules (.zone (.moved before _ .battlefield (.graveyard _) _ _ _ _)) =>
            !before.phasedOut && matchesOwnerOrCtrl before.controller &&
              evalObjectPred g env (.lki before) pred
          | _ => false
    | .permanentLeftBattlefield pred =>
      g.events.any fun e =>
        e.turn == targetTurn &&
          match e.change with
          | .rules (.zone (.moved before _ .battlefield toZ _ _ _ _)) =>
            toZ != .battlefield && !before.phasedOut &&
              matchesOwnerOrCtrl before.controller &&
              evalObjectPred g env (.lki before) pred
          | _ => false
    | .attackedWith pred =>
      g.events.any fun e =>
        e.turn == targetTurn &&
          match e.change with
          | .rules (.combat (.attackersDeclared q decls)) =>
            pids.contains q && decls.any (fun (eo, _) => evalObjectPred g env (.lki eo) pred)
          | _ => false
    | .castSpell pred =>
      g.events.any fun e =>
        e.turn == targetTurn &&
          match e.change with
          | .rules (.cast (.spellCast eo q _)) =>
            pids.contains q && evalObjectPred g env (.lki eo) pred
          | _ => false
    | .drewCard minCount =>
      pids.any fun p => GameEvent.draws g.events targetTurn p ≥ minCount
    | .discardedCard pred =>
      g.events.any fun e =>
        e.turn == targetTurn &&
          match e.change with
          | .rules (.zone (.moved before _ (.hand q) toZ .discard _ _ _)) =>
            pids.contains q && toZ != .hand q && evalObjectPred g env (.lki before) pred
          | _ => false
    | .milledCard minCount =>
      pids.any fun p => GameEvent.milled g.events targetTurn p ≥ minCount
    | .gainedLife minAmount =>
      pids.any fun p => GameEvent.lifeGained g.events targetTurn p ≥ minAmount
    | .lostLife minAmount =>
      pids.any fun p => GameEvent.lifeLost g.events targetTurn p ≥ minAmount
    | .dealtDamage combatOnly noncombatOnly =>
      g.events.any fun e =>
        e.turn == targetTurn &&
          match e.change with
          | .rules (.damage (.dealt pkts)) =>
            pkts.any fun pkt =>
              pkt.amount > 0 &&
                (!combatOnly || pkt.combat) && (!noncombatOnly || !pkt.combat) &&
                match pkt.recipient with
                | .player p => pids.contains p
                | _ => false
          | .rules (.life (.lost q amt true isCombat)) =>
            amt > 0 && pids.contains q &&
              (!combatOnly || isCombat) && (!noncombatOnly || !isCombat)
          | _ => false
    | .activatedLoyalty =>
      pids.any fun p => GameEvent.activatedLoyalty g.events targetTurn p
    | .beheld sub =>
      g.events.any fun e =>
        e.turn == targetTurn &&
          match e.change with
          | .rules (.player (.beheld q s)) => pids.contains q && s == sub
          | _ => false
    | .proliferated =>
      g.events.any fun e =>
        e.turn == targetTurn &&
          match e.change with
          | .rules (.player (.proliferated q _ _)) => pids.contains q
          | _ => false

/-- Evaluate an `EventHistoryPred` against `g.events`. -/
def evalEventHistory (g : Game) (env : EvalEnv) (hp : EventHistoryPred) : Bool :=
  let turn := (boardState g env).turnNumber
  match hp with
  | .scriedThisTurn who =>
    (evalPlayerFilter g env who).any fun p => GameEvent.scried g.events turn p
  | .surveilledThisTurn who =>
    (evalPlayerFilter g env who).any fun p => GameEvent.surveilled g.events turn p
  | .eventOccurredThisTurn who pat =>
    evalEventPatternOnTurn g env turn who pat
  | .eventOccurredLastTurn who pat =>
    if turn > 1 then evalEventPatternOnTurn g env (turn - 1) who pat
    else false

/-- Evaluate a pure `Condition` over `(g, env)` (CR 603.4 / 608.2 / 611). -/
partial def evalCondition (g : Game) (env : EvalEnv) (cond : Condition) : Bool :=
  let st := boardState g env
  match cond with
  | .cmp op a b => op.eval (evalValue g env a) (evalValue g env b)
  | .exists objs => !(evalObjects g env objs).isEmpty
  | .forAll objs pred => (evalObjects g env objs).all (fun v => evalObjectPred g env v pred)
  | .playerPred who pred =>
    let ps := evalPlayer g env who
    !ps.isEmpty && ps.all (fun p => evalPlayerPred g env p pred)
  | .castPred cp => evalCastPred g env cp
  | .turnHistory hp => evalEventHistory g env hp
  | .stepSucceeded v => (env.stepOutcome? v).map (·.succeeded) |>.getD false
  | .duringStep s => st.step == s
  | .duringPhase ph => st.step.phase == ph
  | .isYourTurn => st.activePlayer == env.controller
  | .isNight => st.isNight
  | .all cs => cs.all (evalCondition g env)
  | .any cs => cs.any (evalCondition g env)
  | .not c => !evalCondition g env c

/-- Evaluate a symbolic `DurationExpr` into a concrete `EffectDuration` (CR 611.2a–b). -/
def evalDuration (g : Game) (env : EvalEnv) (dur : DurationExpr) : Option EffectDuration :=
  match dur with
  | .untilEndOfTurn => some .untilEndOfTurn
  | .untilEndOfCombat => some .untilEndOfCombat
  | .untilEndOfStepOrPhase sp => some (.untilEndOfStepOrPhase sp)
  | .untilStepOrPhase sp => some (.untilStepOrPhase sp)
  | .untilNextTurnOf who => ((evalPlayer g env who)[0]?).map EffectDuration.untilNextTurnOf
  | .untilEndOfNextTurnOf who =>
    ((evalPlayer g env who)[0]?).map EffectDuration.untilEndOfNextTurnOf
  | .whileOnBattlefield obj =>
    (evalObjectId? g env obj).map EffectDuration.whileSourceOnBattlefield
  | .untilLeavesBattlefield obj =>
    (evalObjectId? g env obj).map EffectDuration.untilSourceLeaves
  | .whileHasCounter obj k =>
    (evalObjectId? g env obj).map (fun oid => EffectDuration.whileSourceHasCounter oid k)
  | .whileInZone obj z =>
    match evalObjectView? g env obj with
    | some view =>
      match view.id? with
      | some oid => some (.whileInZone oid (z.toZone view.owner))
      | none => none
    | none => none
  | .indefinite => some .indefinite

/-- Evaluate a symbolic `LibraryPosSpec` into a concrete `LibraryPosition` (CR 401). -/
def evalLibraryPos (g : Game) (env : EvalEnv) (pos : LibraryPosSpec) : LibraryPosition :=
  match pos with
  | .top => .top
  | .bottom => .bottom
  | .fromTop v => .fromTop (evalValue g env v).toNat
  | .shuffledIn => .shuffledIn

/-- Evaluate a symbolic `ManaPoolPalette` to its concrete array of `ManaType`s
(CR 106.1 / 106.7 / 903.4). `landsCouldProduce` computes the mana types that
matching lands could produce (supplied by `Game.landsCouldProduce` in `ManaAbilities.lean`). -/
def evalManaPalette (g : Game) (env : EvalEnv)
    (landsCouldProduce : Game → Array GameObject → Array ManaType := fun _ _ => #[])
    (palette : ManaPoolPalette) : Array ManaType :=
  let st := boardState g env
  match palette with
  | .explicit ts => ts
  | .anyColor => anyColorMana
  | .chosenColorOnSource =>
    match (sourceView? g env).bind viewChosenColor? with
    | some c => #[.colored c]
    | none => #[]
  | .commanderColorIdentity who =>
    let combined := (evalPlayer g env who).foldl (fun acc p =>
      let pl := st.player p
      if pl.hasCommander then ColorSet.union acc pl.commanderColorIdentity else acc) ColorSet.empty
    (combined.toList.map ManaType.colored).toArray
  | .colorsAmong objs =>
    let combined := (evalObjects g env objs).foldl (fun acc v =>
      ColorSet.union acc (viewColors st v)) ColorSet.empty
    (combined.toList.map ManaType.colored).toArray
  | .typesLandsCouldProduce lands =>
    let liveLands := (evalObjects g env lands).filterMap ObjectView.live?
    landsCouldProduce st liveLands

/-- Evaluate a symbolic `ManaSpec` into a concrete `ManaOutput` (CR 106.1 / 605). -/
def evalManaSpec (g : Game) (env : EvalEnv)
    (landsCouldProduce : Game → Array GameObject → Array ManaType := fun _ _ => #[])
    (spec : ManaSpec) : ManaOutput :=
  match spec with
  | .sequence items =>
    let mana := items.foldl (fun acc (t, amtExpr) =>
      let n := (evalValue g env amtExpr).toNat
      acc ++ Array.replicate n t) #[]
    .fixed mana
  | .oneOf pal amtExpr =>
    .oneOf (evalManaPalette g env landsCouldProduce pal) (evalValue g env amtExpr).toNat
  | .combination pal amtExpr =>
    .combination (evalManaPalette g env landsCouldProduce pal) (evalValue g env amtExpr).toNat
  | .colorAmong pal =>
    .colorAmong (evalManaPalette g env landsCouldProduce pal)

end EvalExpr

end Mtg.Engine
