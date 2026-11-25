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

/-- Read-only evaluation environment for pure expression queries over
`(Game, EvalEnv)` (CR 109.3 / 109.5 / 400.7 / 603.10 / 608.2h).
Parameterized as `EvalEnvOf GameSnapshot` so serializable continuations store
`StoredEvalEnv := EvalEnvOf Unit` without duplicating the struct (CR 707.2). -/
abbrev EvalEnv := EvalEnvOf GameSnapshot

namespace EvalEnv

/-- Construct an `EvalEnv` from a live `Game` and unified interpreter context `InterpCtx`,
populating `stepEnv` from `g.currentStepEnv`. -/
def ofInterpCtx (g : Game) (ctx : InterpCtx) : EvalEnv :=
  let slots : Array (Array Target) :=
    if !ctx.targetSlots.isEmpty then ctx.targetSlots
    else ctx.targets.map fun t => #[t]
  { controller := ctx.controller
    sourceId := ctx.sourceId
    sourceSnapshot := ctx.sourceSnapshot
    targetSlots := slots
    triggerSubjectId := ctx.triggerSubjectId
    triggerSubjectIds := ctx.triggerSubjectIds
    triggerSubjectSnapshot := ctx.triggerSubjectSnapshot
    triggerPlayers := ctx.triggerPlayers
    chosenX := ctx.chosenX
    eventAmount := ctx.lastKnownPower.getD (Int.ofNat ctx.chosenX)
    stepEnv := g.currentStepEnv }

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
  match st.findLiveSourceObject? oid with
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
    if !env.triggerSubjectIds.isEmpty then
      env.triggerSubjectIds.filterMap (resolveObjectView? g env)
    else
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
    if !env.triggerSubjectIds.isEmpty then env.triggerSubjectIds
    else
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

def viewHasSubtype (st : Game) (v : ObjectView) (sub : CardSubtype) : Bool :=
  match v with
  | .live o => st.hasSubtype o sub
  | .lki eo => eo.subtypes.contains sub

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
    o.abilityEffect.isSome || o.triggeredAbility.isSome || o.isReflexive ||
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

def viewChosenAnchor? : ObjectView → Option String
  | .live o => o.status.chosenAnchor
  | .lki eo => eo.chosenAnchor

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
    if KeywordAbility.hasTag curKw kw then true
    else
      let bc := st.baseCard o
      let retains := st.retainsPrintedAbilities o
      match kw with
      | .ward => !(st.wardCostsOn o).isEmpty
      | .param .equip =>
        (retains && bc.allActivatedAbilities.any (·.isEquip)) ||
          (st.activatedAbilitiesOf o).any (·.isEquip)
      | _ => false
  | .lki eo =>
    if KeywordAbility.hasTag eo.keywords kw then true
    else
      let retains := eo.retainsPrintedAbilities.getD (!eo.faceDown)
      let bc? := if eo.faceDown then none else eo.copiable.orElse (fun _ => eo.printed)
      match kw with
      | .changeling => eo.changeling
      | .toxic => eo.toxic > 0
      | .ward => !eo.wardCosts.isEmpty
      | .param .equip =>
        (retains && bc?.any (fun c => c.allActivatedAbilities.any (·.isEquip))) ||
          (eo.activatedAbilities.getD #[]).any (·.isEquip)
      | _ => false

def viewHasDesignation (st : Game) (v : ObjectView) (tag : PermanentDesignationTag) : Bool :=
  match v, tag with
  | .live o, .ringBearer => st.isAnyRingBearer o
  | .lki eo, .ringBearer => eo.ringBearer
  | .live o, .goaded => o.status.goaded || !o.status.goadedBy.isEmpty
  | .lki eo, .goaded => eo.goaded
  | .live o, .prepared => o.status.prepared
  | .lki eo, .prepared => eo.prepared
  | .live o, .harnessed => o.status.harnessed
  | .lki eo, .harnessed => eo.harnessed

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
  | .landsPlayedThisTurn => Int.ofNat (GameEvent.landsPlayed st.events st.turnNumber p)
  | .spellsCastThisTurn => Int.ofNat (GameEvent.spellsCast st.events st.turnNumber p)
  | .cardsDrawnThisTurn => Int.ofNat (GameEvent.draws st.events st.turnNumber p)
  | .cardsDiscardedThisTurn =>
    Int.ofNat (st.events.foldl (fun n e =>
      if e.turn == st.turnNumber then
        match e.change with
        | .rules (.zone (.moved _ _ (.hand q) _ .discard _ _ _)) => if q == p then n + 1 else n
        | _ => n
      else n) 0)
  | .cardsMilledThisTurn =>
    Int.ofNat (st.events.foldl (fun n e =>
      if e.turn == st.turnNumber then
        match e.change with
        | .rules (.zone (.moved _ _ (.library q) _ .mill _ _ _)) => if q == p then n + 1 else n
        | _ => n
      else n) 0)
  | .otherSpellsManaValueThisTurn =>
    let selfSpellId? :=
      ((env.sourceId.orElse (fun _ => env.sourceSnapshot.bind (·.id))).map
        (GameEvent.stackSpellIdOf st.events)).orElse (fun _ => st.resolvingSpell)
    let (sumOther, matchedSelf, hasUnidentified) :=
      st.events.foldl (fun (acc, matched, unid) e =>
        if e.turn == st.turnNumber then
          match e.change with
          | .rules (.cast (.spellCast spellSnap q _)) =>
            if q == p then
              if selfSpellId?.isSome && spellSnap.id == selfSpellId? then
                (acc, true, unid)
              else
                (acc + spellSnap.manaValue, matched, unid || spellSnap.id.isNone)
            else (acc, matched, unid)
          | _ => (acc, matched, unid)
        else (acc, matched, unid)) (0, false, false)
    let ownFallback :=
      if !matchedSelf && hasUnidentified then
        match selfSpellId?.bind st.findObject? with
        | some spell =>
          if spell.zone == .stack && !spell.isCopy && st.controllerOf spell == some p &&
              !st.proposedSpell.any (·.spellId == spell.id) then
            st.objectManaValue spell
          else 0
        | none => 0
      else 0
    Int.ofNat (sumOther - ownFallback)
  | .lifeGainedThisTurn => Int.ofNat (GameEvent.lifeGained st.events st.turnNumber p)
  | .lifeLostThisTurn => Int.ofNat (GameEvent.lifeLost st.events st.turnNumber p)
  | .unspentMana => Int.ofNat pl.manaPool.total
  | .poisonCounters => Int.ofNat pl.poison
  | .opponentsCount => Int.ofNat (st.livingOpponents p).size
  | .one => 1

/-- Whether an LKI attacking creature `eo` was attacking alone when it left combat
(CR 506.5 / 608.2h). Delegates to `Core.lkiAttackingAlone`. -/
private def lkiAttackingAlone (st : Game) (env : EvalEnv) (events : Array GameEvent)
    (eo : EventObject) : Bool :=
  st.lkiAttackingAlone events eo.attacking eo.id eo.controller env.eventIdx?

/-- Whether an LKI attacking creature `eo` became blocked in the combat phase
containing its departure or phasing out (CR 509.1h / 608.2h / 702.26b).
Delegates to `Core.lkiWasBlocked`. -/
private def lkiWasBlocked (st : Game) (env : EvalEnv) (events : Array GameEvent)
    (eo : EventObject) : Bool :=
  st.lkiWasBlocked events eo.attacking eo.id env.eventIdx?

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
      let defOfView (v : ObjectView) : Option PlayerId :=
        match v with
        | .live o => if o.isOnBattlefield && o.status.attacking then some (st.defendingPlayerOf o) else none
        | .lki eo =>
          if !eo.attacking then none
          else
            match eo.attackingTarget with
            | some (.player dp) => some dp
            | some (.planeswalker pwId) | some (.battle pwId) =>
              ((st.findLiveSourceObject? pwId).bind st.controllerOf).orElse
                (fun _ => (st.lastKnownBefore? pwId).bind (·.controller))
            | none => some (st.defendingPlayerOf (Game.damageSourceObjectFromLki eo))
      let attackerDef? : Option PlayerId :=
        (env.sourceId.bind (resolveObjectView? g env)).bind fun srcView =>
          let fromHost :=
            (viewAttachedTo? srcView).bind (resolveObjectView? g env) |>.bind defOfView
          fromHost.orElse fun _ => defOfView srcView
      match attackerDef? with
      | some dp => dp == p
      | none =>
        let defs := st.defendingPlayers
        if defs.isEmpty then st.isLivingOpponentOf st.activePlayer st.defendingPlayer && st.defendingPlayer == p
        else defs.contains p
    | .metric m op rhs =>
      op.eval (evalPlayerMetricSingle g env m p) (evalValue g env rhs)
    | .controls filter minCount =>
      let need := evalValue g env minCount
      let subEnv := { env with controller := p }
      let controlled := (evalObjects g subEnv filter.toExpr).filter fun v =>
        viewController? st v == some p
      Int.ofNat controlled.size ≥ need
    | .isSeat idx => p.idx == idx
    | .thatPlayer =>
      match env.triggerPlayers.find? (·.1 == .actor) with
      | some (_, tp) => p == tp
      | none => true
    | .matchesExpr who => (evalPlayer g env who).contains p

/-- Whether living player `p` satisfies `pf` under `env`. -/
partial def matchesPlayerFilter (g : Game) (env : EvalEnv) (pf : PlayerFilter) (p : PlayerId) : Bool :=
  let st := boardState g env
  st.stillInGame p &&
    matchesPlayerRelation st env pf.relation p &&
    evalPlayerPred g env p pf.pred

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
    let defOfView (v : ObjectView) : Option PlayerId :=
      match v with
      | .live o => if o.isOnBattlefield && o.status.attacking then some (st.defendingPlayerOf o) else none
      | .lki eo =>
        if !eo.attacking then none
        else
          match eo.attackingTarget with
          | some (.player dp) => some dp
          | some (.planeswalker pwId) | some (.battle pwId) =>
            ((st.findLiveSourceObject? pwId).bind st.controllerOf).orElse
              (fun _ => (st.lastKnownBefore? pwId).bind (·.controller))
          | none => some (st.defendingPlayerOf (Game.damageSourceObjectFromLki eo))
    let attackerDef? : Option PlayerId :=
      (env.sourceId.bind (resolveObjectView? g env)).bind fun srcView =>
        let fromHost :=
          (viewAttachedTo? srcView).bind (resolveObjectView? g env) |>.bind defOfView
        fromHost.orElse fun _ => defOfView srcView
    match attackerDef? with
    | some dp => if st.stillInGame dp then #[dp] else #[]
    | none =>
      let defs := st.defendingPlayers
      if !defs.isEmpty then defs
      else if st.isLivingOpponentOf st.activePlayer st.defendingPlayer then #[st.defendingPlayer] else #[]
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
      | .giftOpponent =>
        match env.sourceId.bind (GameEvent.giftPromisedTo? g.events) with
        | some p => if st.stillInGame p then #[p] else #[]
        | none =>
          match st.proposedSpell.bind (·.giftTo) with
          | some p => if st.stillInGame p then #[p] else #[]
          | none => #[]
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
    | .attackingAlone => lkiAttackingAlone st env st.events eo
    | .blocking => eo.blocking
    | .blockingObject atkExpr =>
      let atkIds := (evalObjects g env atkExpr).filterMap ObjectView.id?
      eo.blockingIds.any atkIds.contains
    | .blocked => eo.attacking && lkiWasBlocked st env st.events eo
    | .unblocked => eo.attacking && !lkiWasBlocked st env st.events eo

/-- Evaluate `ObjectPred` on an `ObjectView` (live or LKI). -/
partial def evalObjectPred (g : Game) (env : EvalEnv) (v : ObjectView) (pred : ObjectPred) : Bool :=
  let st := boardState g env
  match pred with
  | .all ps => ps.all (evalObjectPred g env v)
  | .any ps => ps.any (evalObjectPred g env v)
  | .not inner => !evalObjectPred g env v inner
  | .hasType t => (viewTypes st v).contains t
  | .hasSupertype s => (viewSupertypes st v).contains s
  | .hasSubtype (.literal sub) => viewHasSubtype st v sub
  | .hasSubtype .chosenOnSource =>
    match (sourceView? g env).bind viewChosenSubtype? with
    | some sub => viewHasSubtype st v sub
    | none => false
  | .hasSubtype (.fromStep sv) =>
    match (env.stepOutcome? sv).bind (·.chosenSubtype?) with
    | some sub => viewHasSubtype st v sub
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
      | .fromStep sv =>
        match (env.stepOutcome? sv).bind (·.chosenParity?) with
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
    let hostIds := (evalObjects g env hostExpr).filterMap ObjectView.id?
    match viewAttachedTo? v with
    | some hid => hostIds.contains hid
    | none =>
      match v with
      | .live _ => false
      | .lki eo =>
        match eo.id with
        | none => false
        | some attId =>
          hostIds.any fun hid =>
            !(st.findObject? hid).any (·.isOnBattlefield) &&
              (st.departedOrPhasedOutAttachments? hid).any (fun atts =>
                atts.any (·.id == some attId))
  | .hasAttachment attFilter =>
    match v.id? with
    | none => false
    | some oid =>
      if (evalObjects g env attFilter.toExpr).any (fun att => viewAttachedTo? att == some oid) then
        true
      else if (st.findObject? oid).any (·.isOnBattlefield) then
        false
      else if !attFilter.zones.zones.contains .battlefield then
        false
      else
        match st.departedOrPhasedOutAttachments? oid with
        | none => false
        | some atts =>
          let restrictOwner := attFilter.zones.owner != .any
          let owners : Array PlayerId :=
            match attFilter.zones.owner with
            | .any => #[]
            | .matching pf => evalPlayerFilter g env pf
            | .ofPlayer pe => evalPlayer g env pe
          atts.any fun att =>
            (!restrictOwner || owners.contains att.owner) &&
              evalObjectPred g env (.lki att) attFilter.pred
  | .targets tgtExpr =>
    match v.id? with
    | none => false
    | some oid =>
      let tgts? : Option (Array Target) :=
        match st.stack.find? (·.objectId == oid) with
        | some entry => some entry.targets
        | none =>
          GameEvent.lastKnownTargetsOf? st.events oid
      match tgts? with
      | none => false
      | some tgts =>
        let matchObj (oe : ObjectExpr) : Bool :=
          let ids := (evalObjects g env oe).filterMap ObjectView.id?
          tgts.any fun
            | .permanent id | .card id => ids.contains id
            | .player _ => false
        let matchPl (pe : PlayerExpr) : Bool :=
          let pids := evalPlayer g env pe
          tgts.any fun
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
      | .name =>
        -- CR 201.2a: nameless face-down permanents have no name and never share a name.
        let myName := viewName st v
        let oName := viewName st other
        !myName.isEmpty && myName == oName
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
  | .dealtDamageThisTurn combatOnly rec? thisTurnOnly =>
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
        | some (.playerOrObject pf f) =>
          match r with
          | .player p => (evalPlayerFilter g env pf).contains p
          | .permanent eo | .battle eo => evalObjectPred g env (.lki eo) f.pred
      if thisTurnOnly then
        g.events.any fun e =>
          e.turn == st.turnNumber &&
            match e.change with
            | .rules (.damage (.dealt pkts)) =>
              pkts.any fun pkt =>
                pkt.amount > 0 && pkt.source.id == some oid &&
                  (!combatOnly || pkt.combat) && recMatches pkt.recipient
            | _ => false
      else
        g.events.foldl (fun dealt e =>
          match e.change with
          | .rules (.zone (.moved _ after _ .battlefield ..)) =>
            if after.id == some oid then false else dealt
          | .rules (.zone (.created obj _)) =>
            if obj.zone == .battlefield && obj.id == some oid then false else dealt
          | .rules (.damage (.dealt pkts)) =>
            dealt || pkts.any fun pkt =>
              pkt.amount > 0 && pkt.source.id == some oid &&
                (!combatOnly || pkt.combat) && recMatches pkt.recipient
          | _ => dealt) false
  | .wasDealtDamageThisTurn =>
    let liveDamaged :=
      match v with
      | .live o => o.status.damage > 0
      | .lki _ => false
    liveDamaged ||
      match v.id? with
      | none => false
      | some oid =>
        g.events.any fun e =>
          e.turn == st.turnNumber &&
            match e.change with
            | .rules (.damage (.dealt pkts)) =>
              pkts.any fun pkt =>
                pkt.amount > 0 &&
                  match pkt.recipient with
                  | .permanent eo | .battle eo => eo.id == some oid
                  | .player _ => false
            | _ => false
  | .receivedCounterThisTurn kind? byPlayer? =>
    match v.id? with
    | none => false
    | some oid =>
      let allowedPlayers? := byPlayer?.map (evalPlayerFilter g env)
      g.events.any fun e =>
        e.turn == st.turnNumber &&
          e.countersPutInEvent.any fun (eo, kind, n, actor?) =>
            eo.id == some oid && n > 0 &&
              (match kind? with | none => true | some k => kind == k) &&
              (match allowedPlayers? with
               | none => true
               | some ps =>
                 match actor? with
                 | some p => ps.contains p
                 | none =>
                   match eo.controller with
                   | some c => ps.contains c
                   | none => true)
  | .putIntoGraveyardFromBattlefieldThisTurn =>
    match v.id? with
    | none => false
    | some oid =>
      g.events.any fun e =>
        e.turn == st.turnNumber &&
          match e.change with
          | .rules (.zone (.moved _ after .battlefield (.graveyard _) _ _ _ _)) =>
            after.id == some oid
          | _ => false
  | .chosenAnchorIs anchor =>
    viewChosenAnchor? v == some anchor

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
    let rec attachedToHostExprs : ObjectPred → Array ObjectExpr
      | .attachedTo h => #[h]
      | .all ps => ps.foldl (fun a p => a ++ attachedToHostExprs p) #[]
      | _ => #[]
    let candidates : Array ObjectView := Id.run do
      let mut acc : Array ObjectView := #[]
      for zk in zs.zones do
        match zk with
        | .battlefield =>
          let (lkiAtts, lkiAttIds) : Array EventObject × Array ObjectId :=
            if allowPhased then (#[], #[])
            else Id.run do
              let mut attsOut : Array EventObject := #[]
              let mut idsOut : Array ObjectId := #[]
              for hostExpr in attachedToHostExprs pred do
                let hostIds := (evalObjects g env hostExpr).filterMap ObjectView.id?
                for hid in hostIds do
                  if !(st.findObject? hid).any (·.isOnBattlefield) then
                    if let some atts := st.departedOrPhasedOutAttachments? hid then
                      for att in atts do
                        if !restrictOwner || owners.contains att.owner then
                          if !attsOut.any (fun prev => prev.id == att.id && att.id.isSome) then
                            attsOut := attsOut.push att
                          if let some aid := att.id then
                            if !idsOut.contains aid then
                              idsOut := idsOut.push aid
              return (attsOut, idsOut)
          for o in st.objects do
            if o.zone == .battlefield && ownerOk o && (allowPhased || !o.status.phasedOut) &&
                !(o.attachedTo.isNone && lkiAttIds.contains o.id) then
              acc := acc.push (.live o)
          for att in lkiAtts do
            acc := acc.push (.lki att)
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
  | .allTargets =>
    dedupViews (env.targetSlots.foldl (fun acc slot =>
      slot.foldl (fun a t =>
        match t with
        | .permanent oid | .card oid =>
          match resolveObjectView? g env oid with
          | some v => a.push v
          | none => a
        | .player _ => a) acc) #[])
  | .linkedExile srcExpr =>
    let srcs := evalObjects g env srcExpr
    dedupViews (srcs.foldl (fun acc sv =>
      match sv.id? with
      | none => acc
      | some sid =>
        (st.allLinkedExilesOf sid).foldl (fun a eid =>
          match st.findObject? eid with
          | some eo => if eo.zone == .exile then a.push (.live eo) else a
          | none => a) acc) #[])
  | .costPaidObjects =>
    if !env.costPaidObjects.isEmpty then
      dedupViews (env.costPaidObjects.filterMap (resolveObjectView? g env))
    else
      match env.sourceId with
      | none => #[]
      | some sid =>
        let spellId := GameEvent.stackSpellIdOf g.events sid
        let ids : Array ObjectId := g.events.foldl (fun acc e =>
          match e.cause?, e.change with
          | some (.costPayment _ _ (some forObj)), .rules (.zone (.moved before after ..)) =>
            if forObj == sid || forObj == spellId then
              match after.id.orElse (fun _ => before.id) with
              | some oid => pushUnique acc oid
              | none => acc
            else acc
          | _, _ => acc) #[]
        dedupViews (ids.filterMap (resolveObjectView? g env))
  | .targetsOf stackObj =>
    let objs := evalObjects g env stackObj
    dedupViews (objs.foldl (fun acc sv =>
      match sv.id? with
      | none => acc
      | some oid =>
        let tgts : Array Target :=
          match st.stack.find? (·.objectId == oid) with
          | some entry => entry.targets
          | none =>
            (GameEvent.lastKnownTargetsOf? st.events oid).getD #[]
        tgts.foldl (fun a t =>
          match t with
          | .permanent tid | .card tid =>
            match resolveObjectView? g env tid with
            | some v => a.push v
            | none => a
          | .player _ => a) acc) #[])
  | .filter inner pred =>
    (evalObjects g env inner).filter (fun v => evalObjectPred g env v pred)

/-- Evaluate a `ValueExpr` to an `Int` (CR 107.1–2 / 608.2h). -/
partial def evalValue (g : Game) (env : EvalEnv) (expr : ValueExpr) : Int :=
  let st := boardState g env
  match expr with
  | .const n => n
  | .chosenX => Int.ofNat env.chosenX
  | .eventAmount => env.eventAmount
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
  | .colorCountAmong objsExpr =>
    let views := evalObjects g env objsExpr
    let mask := views.foldl (fun acc v => ColorSet.union acc (viewColors st v)) ColorSet.empty
    Int.ofNat mask.count
  | .playerMetric m whoExpr =>
    (evalPlayer g env whoExpr).foldl (fun acc p => acc + evalPlayerMetricSingle g env m p) 0
  | .maxControlled who pred =>
    let ps := evalPlayerFilter g env who
    let allowPhased := predMentionsPhasedOut pred
    ps.foldl (fun acc p =>
      let cnt := st.objects.foldl (fun n o =>
        if o.zone == .battlefield && (allowPhased || !o.status.phasedOut) &&
            st.controllerOf o == some p && evalObjectPred g env (.live o) pred then n + 1
        else n) 0
      Max.max acc (Int.ofNat cnt)) 0
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
  | .manaSpent objsExpr =>
    let oid? :=
      ((evalObjects g env objsExpr)[0]?.bind ObjectView.id?).orElse fun _ =>
        match objsExpr with
        | .triggerSubject => env.triggerSubjectId
        | .this => env.sourceId
        | _ => none
    match oid? with
    | some oid => Int.ofNat (manaUnitsSpentOn g.events oid).size
    | none => 0
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
  | .wasKicked ref =>
    evalObj ref fun oid =>
      GameEvent.wasKicked g.events oid ||
        (match g.proposedSpell with
         | some prop => prop.spellId == oid && prop.kicked
         | none => false)
  | .giftPromised ref =>
    evalObj ref fun oid =>
      GameEvent.giftPromised g.events oid ||
        (match g.proposedSpell with
         | some prop => prop.spellId == oid && prop.giftTo.isSome
         | none => false)
  | .impendingPaid ref => evalObj ref (GameEvent.castForImpending g.events)
  | .teamworkPaid ref =>
    evalObj ref fun oid =>
      GameEvent.teamwork g.events oid ||
        (match g.proposedSpell with
         | some prop => prop.spellId == oid && prop.teamworkPaid
         | none => false)
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
      | .fromSource =>
        match env.sourceId with
        | some sid => units.any (·.source == some sid)
        | none => false
      | .ofColor c => units.any (·.mana == .colored c)
      | .amount op n => op.eval (Int.ofNat units.size) (Int.ofNat n)
      | .colorCount op n =>
        let cols := units.foldl (fun acc u =>
          match u.mana with
          | .colored c => pushUnique acc c
          | .colorless => acc) #[]
        op.eval (Int.ofNat cols.size) (Int.ofNat n)
      | .withRider r => units.any (·.hasRider r)

/-- Evaluate an `EventPattern` for players `who` on a specific `targetTurn`. -/
def evalEventPatternOnTurn (g : Game) (env : EvalEnv) (targetTurn : Nat)
    (who : PlayerFilter) (pat : EventPattern) : Bool :=
  let st := boardState g env
  let pids : Array PlayerId :=
    if who.pred == .any then
      -- CR 800.4 / Ruling 226: historical turn events still recognize players who later left the game.
      st.players.filterMap fun pl =>
        let relOk :=
          match who.relation with
          | .you => pl.id == env.controller
          | .opponent => pl.id != env.controller && !st.areTeammates env.controller pl.id
          | .teammate => st.areTeammates env.controller pl.id
          | .anyPlayer => true
        if relOk then some pl.id else none
    else evalPlayerFilter g env who
  if pids.isEmpty then false
  else
    let anyPlayer := who == .any
    let matchesOwnerOrCtrl (p? : Option PlayerId) : Bool :=
      match p? with
      | some p => pids.contains p
      | none => anyPlayer
    let anyEventOnTurn (f : Nat → GameEvent → Bool) : Bool := Id.run do
      for i in [0:st.events.size] do
        let e := st.events[i]!
        if e.turn == targetTurn && f i e then
          return true
      return false
    match pat with
    | .permanentEntered pred =>
      anyEventOnTurn fun i e =>
        let eEnv : EvalEnv := { env with eventIdx? := some i }
        match e.change with
        | .rules (.zone (.moved _ after fromZ .battlefield _ _ _ _)) =>
          fromZ != .battlefield && !after.phasedOut &&
            matchesOwnerOrCtrl after.controller &&
            evalObjectPred g eEnv (.lki after) pred
        | .rules (.zone (.created obj ctrl)) =>
          obj.zone == .battlefield && !obj.phasedOut &&
            pids.contains (obj.controller.getD ctrl) &&
            evalObjectPred g eEnv (.lki obj) pred
        | _ => false
    | .permanentDied pred minCount =>
      let count : Nat := Id.run do
        let mut n := 0
        for i in [0:st.events.size] do
          let e := st.events[i]!
          if e.turn == targetTurn then
            match e.change with
            | .rules (.zone (.moved before _ .battlefield (.graveyard _) _ _ _ _)) =>
              if !before.phasedOut && matchesOwnerOrCtrl before.controller &&
                  evalObjectPred g { env with eventIdx? := some i } (.lki before) pred then
                n := n + 1
            | _ => pure ()
        return n
      count >= minCount
    | .permanentLeftBattlefield pred =>
      anyEventOnTurn fun i e =>
        match e.change with
        | .rules (.zone (.moved before _ .battlefield toZ _ _ _ _)) =>
          toZ != .battlefield && !before.phasedOut &&
            matchesOwnerOrCtrl before.controller &&
            evalObjectPred g { env with eventIdx? := some i } (.lki before) pred
        | .rules (.zone (.ceasedToExist before)) =>
          before.zone == .battlefield && !before.phasedOut &&
            matchesOwnerOrCtrl before.controller &&
            evalObjectPred g { env with eventIdx? := some i } (.lki before) pred
        | _ => false
    | .attackedWith pred minCount =>
      pids.any fun p => Id.run do
        let mut count : Nat := 0
        for i in [0:st.events.size] do
          let e := st.events[i]!
          if e.turn == targetTurn then
            match e.change with
            | .rules (.combat (.attackersDeclared q decls)) =>
              if q == p then
                for (eo, _) in decls do
                  if evalObjectPred g { env with eventIdx? := some i } (.lki eo) pred then
                    count := count + 1
            | _ => pure ()
        return count ≥ minCount
    | .castSpell pred =>
      anyEventOnTurn fun i e =>
        match e.change with
        | .rules (.cast (.spellCast eo q _)) =>
          pids.contains q && evalObjectPred g { env with eventIdx? := some i } (.lki eo) pred
        | _ => false
    | .drewCard minCount =>
      pids.any fun p => GameEvent.draws st.events targetTurn p ≥ minCount
    | .discardedCard pred =>
      anyEventOnTurn fun i e =>
        match e.change with
        | .rules (.zone (.moved before _ (.hand q) toZ .discard _ _ _)) =>
          pids.contains q && toZ != .hand q &&
            evalObjectPred g { env with eventIdx? := some i } (.lki before) pred
        | _ => false
    | .milledCard minCount =>
      pids.any fun p => GameEvent.milled st.events targetTurn p ≥ minCount
    | .gainedLife minAmount =>
      pids.any fun p => GameEvent.lifeGained st.events targetTurn p ≥ minAmount
    | .lostLife minAmount =>
      pids.any fun p => GameEvent.lifeLost st.events targetTurn p ≥ minAmount
    | .dealtDamage combatOnly noncombatOnly =>
      st.events.any fun e =>
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
      pids.any fun p => GameEvent.activatedLoyalty st.events targetTurn p
    | .beheld sub =>
      st.events.any fun e =>
        e.turn == targetTurn &&
          match e.change with
          | .rules (.player (.beheld q s)) => pids.contains q && s == sub
          | _ => false
    | .proliferated =>
      st.events.any fun e =>
        e.turn == targetTurn &&
          match e.change with
          | .rules (.player (.proliferated q _ _)) => pids.contains q
          | _ => false

/-- Evaluate an `EventHistoryPred` against `st.events` (`boardState g env`). -/
def evalEventHistory (g : Game) (env : EvalEnv) (hp : EventHistoryPred) : Bool :=
  let st := boardState g env
  let turn := st.turnNumber
  match hp with
  | .scriedThisTurn who =>
    (evalPlayerFilter g env who).any fun p => GameEvent.scried st.events turn p
  | .surveilledThisTurn who =>
    (evalPlayerFilter g env who).any fun p => GameEvent.surveilled st.events turn p
  | .eventOccurredThisTurn who pat =>
    evalEventPatternOnTurn g env turn who pat
  | .eventOccurredLastTurn who pat =>
    if turn > 1 then evalEventPatternOnTurn g env (turn - 1) who pat
    else false
  | .firstResolutionThisTurn =>
    match env.sourceId with
    | none => true
    | some sid =>
      !st.events.any fun e =>
        e.turn == turn &&
          match e.change with
          | .rules (.stackObject (.resolved _ nth srcId? _)) => nth > 0 && srcId? == some sid
          | .rules (.player (.optionalOnceActed _ s)) => s == sid
          | _ => false
  | .nthResolutionThisTurn n =>
    let ab? := st.resolvingAbility.bind fun id =>
      (st.findObject? id).bind (·.triggeredAbility)
    GameEvent.resolutions st.events turn env.controller env.sourceId ab? == n
  | .optionalOnceUnusedThisTurn =>
    match env.sourceId with
    | none => true
    | some sid => !st.optionalOnceUsedThisTurn sid

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
  | .isYourTurn => st.isOnActiveTeam env.controller
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
  | .bottom | .bottomRandom => .bottom
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
  | .colorAmong pal incC =>
    .colorAmong (evalManaPalette g env landsCouldProduce pal) incC

/-- Evaluate an `ActivatedAbility`'s optional `Condition` (CR 602.5b / 605.3b). -/
def evalActivationCondition (g : Game) (p : PlayerId) (sourceId : ObjectId)
    (cond? : Option Condition) : Bool :=
  match cond? with
  | none => true
  | some cond =>
    let env : EvalEnv := { controller := p, sourceId := some sourceId }
    evalCondition g env cond

/-- Total generic-mana cost reduction across an `ActivatedAbility`'s
`costReductions` (CR 602.2b / 601.2f). Target-dependent entries evaluate against
`targets` when non-empty and contribute 0 before targets are chosen. -/
def evalActivationCostReductions (g : Game) (p : PlayerId) (sourceId : Option ObjectId)
    (reductions : Array ActivationCostReduction) (targets : Array Target := #[]) : Nat :=
  let env : EvalEnv :=
    { controller := p
      sourceId := sourceId
      targetSlots := targets.map fun t => #[t] }
  reductions.foldl (fun acc red =>
    if targets.isEmpty && red.mentionsTarget then acc
    else
      let ok := match red.condition? with
        | none => true
        | some cond => evalCondition g env cond
      if ok then acc + (evalValue g env red.amount).toNat
      else acc) 0

/-- Synthesize an `ObjectView` for evaluating spell predicates against a card face
(`face`, which may be an Adventure, MDFC back face, or prepare face) with its
Layer-3 text changes, CR 604.3 / 613.3 CDAs (`.setTypes`, `.setColors`, `.setPT`,
`.allCreatureTypes`), and computed `manaValue` (CR 601.2f / 613.1c–e). -/
def spellFaceView (g : Game) (card : GameObject) (face : CardDef) (caster : PlayerId)
    (manaValue : Nat) : ObjectView :=
  let tcs := g.evalLayer3 card
  let rawSubs :=
    (CardSubtype.ofSubtypes face.subtypes).map fun s =>
      if tcs.isEmpty then s else HasTextChange.applyTextChanges tcs s
  let sas :=
    if tcs.isEmpty then face.staticAbilities
    else HasTextChange.applyTextChanges tcs face.staticAbilities
  let kws :=
    if tcs.isEmpty then face.keywords
    else HasTextChange.applyTextChanges tcs face.keywords
  let (cdaTypes, cdaSubs0, cdaSups) :=
    sas.foldl (fun (ts, subs, sups) ab =>
      match ab with
      | .characteristicDefining (.setTypes tm) => tm.apply ts subs sups
      | _ => (ts, subs, sups)) (face.types, rawSubs, face.supertypes)
  let isChangeling := face.hasSimpleKeyword .changeling ||
    sas.any fun | .characteristicDefining .allCreatureTypes => true | _ => false
  let subs0 :=
    if isChangeling && (cdaTypes.contains .creature || cdaTypes.contains .kindred) then
      CardSubtype.allCreatureSubtypes.foldl
        (fun acc s => if acc.contains s then acc else acc.push s) cdaSubs0
    else cdaSubs0
  let subs :=
    if cdaTypes.contains .creature || cdaTypes.contains .kindred then subs0
    else subs0.filter CardSubtype.isNoncreature
  let cdaColors :=
    sas.foldl (fun cols ab =>
      match ab with
      | .characteristicDefining (.setColors cs) => cs
      | _ => cols) face.colors
  let selfEnv : EvalEnv :=
    { controller := caster
      sourceId := if card.id == noSourceSentinelId then none else some card.id }
  let (cdaP, cdaT) :=
    sas.foldl (fun (pw, tg) ab =>
      match ab with
      | .characteristicDefining (.setPT p? t?) =>
        let pw' := match p? with | some v => some (evalValue g selfEnv v) | none => pw
        let tg' := match t? with | some v => some (evalValue g selfEnv v) | none => tg
        (pw', tg')
      | _ => (pw, tg)) (face.powerValue, face.toughnessValue)
  .lki {
    id := some card.id
    controller := some caster
    owner := card.owner
    name := face.name
    colors := cdaColors
    manaValue := manaValue
    supertypes := cdaSups
    types := cdaTypes
    subtypes := subs
    power := cdaP
    toughness := cdaT
    loyalty := face.loyalty.map Int.toNat
    keywords := kws
    toxic := KeywordAbility.toxicTotal kws
    staticAbilities := sas
    zone := card.zone
    token := face.isToken
    isCopy := card.isCopy
    isCommander := card.isCommander
    changeling := isChangeling
    printed := some face
    copiable := some face
    chosenX := card.chosenX
  }

end EvalExpr

end Mtg.Engine
