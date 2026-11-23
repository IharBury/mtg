import Mtg.Engine.Card.Expr

/-!
# Unified Targeting Specifications (CR 115.1 / 115.3–5 / 601.2c–d / 603.3d / 700.2)

Compositional `TargetSpec` / `TargetSlot` / `TargetDomain` AST backed directly
by Layer-1 `ObjectPred`, `PlayerFilter`, `ZoneSetSpec`, `CountRange`,
`ValueExpr`, and `Condition` (`Mtg.Engine.Card.Expr`).

Every `"target"` word in Oracle text corresponds to one `TargetSlot` (CR 115.1).
No raw `noun : String` is stored on any targeting type; Oracle wording is
rendered canonically via `ToOracle`, and Layer-3 text changes (CR 612.2 /
613.1c) transform every targeting node functorially via `HasTextChange`.

Every `inductive` in this module has ≤ 5 constructors.
-/

namespace Mtg.Engine

/-! ### `CountRange` Bounds Helpers (CR 115.1 / 601.2c) -/

namespace CountRange

/-- Minimum number of targets required for this `"target"` word (CR 601.2c). -/
def minCount : CountRange → Nat
  | .exact n => n
  | .upTo _ => 0
  | .between lo _ => lo
  | .anyNumber => 0

/-- Upper bound on targets for this `"target"` word (`none` for `"any number of"`). -/
def maxCount? : CountRange → Option Nat
  | .exact n => some n
  | .upTo n => some n
  | .between _ hi => some hi
  | .anyNumber => none

/-- Upper bound with `fallback` (default `100`) for `"any number of"`. -/
def maxCount (cr : CountRange) (fallback : Nat := 100) : Nat :=
  (cr.maxCount?).getD fallback

/-- True when choosing zero targets is legal for this slot (CR 115.1c). -/
def allowsZero (cr : CountRange) : Bool :=
  cr.minCount == 0

/-- Construct a `CountRange` from `(minCount, maxCount)` bounds. -/
def ofBounds (minN maxN : Nat) : CountRange :=
  let hi := max minN maxN
  if minN == 0 then .upTo hi
  else if minN == hi then .exact minN
  else .between minN hi

/-- Whether this count renders its noun phrase in plural form. -/
def isPlural : CountRange → Bool
  | .exact n => n != 1
  | .upTo n => n != 1
  | .between _ hi => hi != 1
  | .anyNumber => true

private def countWord (n : Nat) : String :=
  if n == 1 then "one" else englishNumber n

/-- Leading Oracle quantifier phrase before `"target"` / `"other target"`. Empty for `.exact 1`. -/
def quantifierPrefix : CountRange → String
  | .exact 1 => ""
  | .exact n => countWord n
  | .upTo n => s!"up to {countWord n}"
  | .between lo hi =>
    if hi == lo + 1 then s!"{countWord lo} or {countWord hi}"
    else s!"{countWord lo} to {countWord hi}"
  | .anyNumber => "any number of"

end CountRange

/-! ### Core Targeting AST Types -/

/-- What quantity is divided among a slot's targets at announcement (CR 601.2d). -/
inductive DivisionKind where
  | damage
  | counters (kind : CounterKind)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Multi-target relational constraint across targets chosen for a single
`TargetSlot` or cross-slot group (CR 115.3 / 601.2c / 608.2b). -/
inductive GroupTargetConstraint where
  | totalManaValueAtMost (cap : ValueExpr)
  | shareCharacteristic (char : SharedCharacteristic)
  | distinctControllers
  | distinctNames
  | distinctCardTypes
deriving Repr, Inhabited, BEq

instance : HasTextChange GroupTargetConstraint where
  applyTextChanges tcs gc :=
    if tcs.isEmpty then gc
    else
      match gc with
      | .totalManaValueAtMost cap =>
        .totalManaValueAtMost (HasTextChange.applyTextChanges tcs cap)
      | other => other

/-- Restriction on CR 115.4 `"any target"` (creature, planeswalker, battle, or player). -/
inductive RecipientPred where
  /-- Any creature, planeswalker, battle, or player (CR 115.4). -/
  | any
  /-- Any target other than `ref` (`"any other target"`, CR 115.4). -/
  | otherThan (ref : ObjectRef)
  /-- Filtered CR 115.4 recipient (creature/planeswalker/battle matching `objPred`
  or player matching `playerFilter`). -/
  | filtered (objPred : ObjectPred) (playerFilter : PlayerFilter)
deriving Repr, Inhabited, BEq

instance : HasTextChange RecipientPred where
  applyTextChanges tcs rp :=
    if tcs.isEmpty then rp
    else
      match rp with
      | .any => .any
      | .otherThan ref => .otherThan ref
      | .filtered op pf =>
        .filtered (HasTextChange.applyTextChanges tcs op)
          (HasTextChange.applyTextChanges tcs pf)

/-- Domain of legal objects, players, or stack abilities for one `TargetSlot`
(CR 115.1 / 115.4 / 115.5). -/
inductive TargetDomain where
  | object (zones : ZoneSetSpec) (pred : ObjectPred)
  | player (filter : PlayerFilter)
  | anyTarget (pred : RecipientPred := .any)
  | stackAbility (controller : PlayerFilter := .you) (sourcePred : ObjectPred := .anyObject)
  | anyOf (domains : Array TargetDomain)
deriving Repr, Inhabited, BEq

private def applyTcTargetDomain (tcs : Array TextChange) : TargetDomain → TargetDomain
  | .object zs pred =>
    .object (HasTextChange.applyTextChanges tcs zs) (HasTextChange.applyTextChanges tcs pred)
  | .player pf => .player (HasTextChange.applyTextChanges tcs pf)
  | .anyTarget rp => .anyTarget (HasTextChange.applyTextChanges tcs rp)
  | .stackAbility ctrl src =>
    .stackAbility (HasTextChange.applyTextChanges tcs ctrl) (HasTextChange.applyTextChanges tcs src)
  | .anyOf ds => .anyOf (ds.attach.map fun ⟨d, _⟩ => applyTcTargetDomain tcs d)

instance : HasTextChange TargetDomain where
  applyTextChanges tcs d := if tcs.isEmpty then d else applyTcTargetDomain tcs d

/-- One instance of the word `"target"` in Oracle text (CR 115.1 / 601.2c–d). -/
structure TargetSlot where
  domain : TargetDomain
  count : CountRange := .exact 1
  division? : Option (DivisionKind × ValueExpr) := none
  groupConstraint? : Option GroupTargetConstraint := none
  /-- When set, repeats this slot once per player matching the filter at
  announcement (`"for each opponent, ... that player controls"`, CR 601.2c).
  Expanded into concrete per-seat slots on the stack. -/
  forEach? : Option PlayerFilter := none
  /-- Optional conditional domain override (e.g. Teamwork target relaxation,
  CR 601.2b–c / 702.194). -/
  altDomainIf? : Option (Condition × TargetDomain) := none
deriving Repr, Inhabited, BEq

instance : HasTextChange TargetSlot where
  applyTextChanges tcs s :=
    if tcs.isEmpty then s
    else
      { domain := HasTextChange.applyTextChanges tcs s.domain
        count := s.count
        division? := s.division?.map fun (dk, v) => (dk, HasTextChange.applyTextChanges tcs v)
        groupConstraint? := s.groupConstraint?.map (HasTextChange.applyTextChanges tcs)
        forEach? := s.forEach?.map (HasTextChange.applyTextChanges tcs)
        altDomainIf? := s.altDomainIf?.map fun (c, d) =>
          (HasTextChange.applyTextChanges tcs c, HasTextChange.applyTextChanges tcs d) }

/-- Cross-slot relational requirement linking distinct `"target"` slots in one
`TargetSpec` (CR 115.3). -/
inductive CrossSlotRelation where
  /-- Targets across the listed slots must be pairwise distinct
  (e.g. `"target artifact you control and a second target artifact you control"`). -/
  | distinct
  /-- Targets across the listed slots must jointly satisfy `constraint`. -/
  | group (constraint : GroupTargetConstraint)
deriving Repr, Inhabited, BEq

instance : HasTextChange CrossSlotRelation where
  applyTextChanges tcs r :=
    if tcs.isEmpty then r
    else
      match r with
      | .distinct => .distinct
      | .group gc => .group (HasTextChange.applyTextChanges tcs gc)

/-- Cross-slot constraint applied across the 0-based `TargetSpec.slots` indices
listed in `slots`. -/
structure CrossSlotConstraint where
  slots : Array Nat
  relation : CrossSlotRelation
deriving Repr, Inhabited, BEq

instance : HasTextChange CrossSlotConstraint where
  applyTextChanges tcs c :=
    if tcs.isEmpty then c
    else { c with relation := HasTextChange.applyTextChanges tcs c.relation }

/-- Unified targeting specification for a spell, activated ability, or triggered
ability (CR 115.1 / 601.2c–d / 603.3d / 700.2). Each `TargetSlot` corresponds
to one instance of the word `"target"` in Oracle text; empty `slots` means no
targets. -/
structure TargetSpec where
  slots : Array TargetSlot := #[]
  crossSlotConstraints : Array CrossSlotConstraint := #[]
deriving Repr, Inhabited, BEq

instance : HasTextChange TargetSpec where
  applyTextChanges tcs ts :=
    if tcs.isEmpty then ts
    else
      { slots := HasTextChange.applyTextChanges tcs ts.slots
        crossSlotConstraints := HasTextChange.applyTextChanges tcs ts.crossSlotConstraints }

/-- Default demonstration-agent choice among legal targets (CR 601.2c). -/
inductive TargetPreference where
  /-- A permanent the caster controls. -/
  | own
  /-- A permanent an opponent controls. -/
  | opponent
  /-- The opposing player, else the first legal target. -/
  | opponentPlayer
  /-- The last legal target (e.g. a graveyard card). -/
  | last
  /-- Own permanent if any, otherwise an opponent's. -/
  | ownThenOpponent
  /-- This player (e.g. a “target player draws” you want to hit yourself with). -/
  | selfPlayer
deriving Repr, Inhabited, BEq, DecidableEq

/-! ### Structural Predicate Helpers -/

private def objPredAtoms : ObjectPred → List ObjectPred
  | .all ps => ps.toList
  | p => [p]

private def objPredHasAtom (pred : ObjectPred) (p : ObjectPred → Bool) : Bool :=
  (objPredAtoms pred).any p

private def splitOtherThan (pred : ObjectPred) : Bool × ObjectPred :=
  let atoms := objPredAtoms pred
  let hasOther := atoms.any (fun | .otherThan _ => true | _ => false)
  if !hasOther then (false, pred)
  else
    let rest := atoms.filter (fun | .otherThan _ => false | _ => true)
    (true, ObjectPred.andAll rest.toArray)

private def isControlledBy (pf : PlayerFilter) : ObjectPred → Bool
  | .controlledBy f => f == pf
  | _ => false

/-- Replace occurrences of `matchPf` in controller/owner predicates with `replacement`
(used when rewriting or expanding `"for each opponent/player, ... that player controls"`). -/
private partial def substPlayerFilterPred (matchPf replacement : PlayerFilter) :
    ObjectPred → ObjectPred
  | .all ps => .all (ps.map (substPlayerFilterPred matchPf replacement))
  | .any ps => .any (ps.map (substPlayerFilterPred matchPf replacement))
  | .not p => .not (substPlayerFilterPred matchPf replacement p)
  | .controlledBy pf =>
    if pf == matchPf then .controlledBy replacement else .controlledBy pf
  | .ownedBy pf =>
    if pf == matchPf then .ownedBy replacement else .ownedBy pf
  | other => other

/-- Replace occurrences of `matchPf` with `replacement` inside a `TargetDomain`. -/
def TargetDomain.substitutePlayerFilter (matchPf replacement : PlayerFilter) :
    TargetDomain → TargetDomain
  | .object zs pred =>
    let zs' :=
      match zs.owner with
      | .matching pf => if pf == matchPf then { zs with owner := .matching replacement } else zs
      | _ => zs
    .object zs' (substPlayerFilterPred matchPf replacement pred)
  | .player pf => if pf == matchPf then .player replacement else .player pf
  | .anyTarget (.filtered op pf) =>
    .anyTarget (.filtered (substPlayerFilterPred matchPf replacement op)
      (if pf == matchPf then replacement else pf))
  | .anyTarget rp => .anyTarget rp
  | .stackAbility ctrl src =>
    .stackAbility (if ctrl == matchPf then replacement else ctrl) src
  | .anyOf ds => .anyOf (ds.attach.map fun ⟨d, _⟩ => d.substitutePlayerFilter matchPf replacement)

/-- Replace opponent controller/player filter with `replacement` inside a `TargetDomain`. -/
def TargetDomain.substituteOpponent (replacement : PlayerFilter) (d : TargetDomain) : TargetDomain :=
  d.substitutePlayerFilter .opponent replacement

/-- Substitute the bound `"that player"` placeholder (and `.opponent` when
expanding a `forEach? := some .opponent` slot) with concrete `replacement`. -/
def TargetDomain.substituteForEach (forEachFilter replacement : PlayerFilter)
    (d : TargetDomain) : TargetDomain :=
  let d' := d.substitutePlayerFilter .thatPlayer replacement
  if forEachFilter == .opponent then d'.substitutePlayerFilter .opponent replacement
  else d'

/-- Whether `d` targets any stack object (spell or stack ability). -/
def TargetDomain.targetsStackSpell : TargetDomain → Bool
  | .object zs _ => zs.zones.contains .stack
  | .stackAbility .. => true
  | .anyOf ds => ds.attach.any fun ⟨d, _⟩ => d.targetsStackSpell
  | .player _ | .anyTarget _ => false

/-- Whether `d` targets any graveyard zone. -/
private def TargetDomain.targetsGraveyard : TargetDomain → Bool
  | .object zs _ => zs.zones.contains .graveyard
  | .anyOf ds => ds.attach.any fun ⟨d, _⟩ => d.targetsGraveyard
  | .player _ | .anyTarget _ | .stackAbility .. => false

/-- Structural default AI preference for a `TargetDomain` (CR 601.2c). -/
def TargetDomain.defaultPreference : TargetDomain → TargetPreference
  | .anyTarget _ => .opponentPlayer
  | .player { relation := .you, .. } => .selfPlayer
  | .player _ => .opponentPlayer
  | .stackAbility .. => .opponent
  | .anyOf ds =>
    if ds.attach.any fun ⟨d, _⟩ => d.targetsGraveyard then .last
    else if ds.any (fun | .player _ => true | _ => false) then .ownThenOpponent
    else match ds[0]? with
      | some d =>
        -- Avoid recursive call on non-structurally-smaller `ds[0]?` by matching directly.
        match d with
        | .anyTarget _ => .opponentPlayer
        | .player { relation := .you, .. } => .selfPlayer
        | .player _ => .opponentPlayer
        | .object zs _ => if zs.zones.contains .graveyard then .last else .opponent
        | _ => .opponent
      | none => .opponent
  | .object zs pred =>
    if zs.zones.contains .graveyard then .last
    else if objPredHasAtom pred (isControlledBy .you) then .own
    else if objPredHasAtom pred (isControlledBy .opponent) then .opponent
    else if pred == .anyObject ||
        pred == .not (.hasType .land) ||
        pred == .all #[.not (.hasType .land), .isToken false] then
      .ownThenOpponent
    else if objPredHasAtom pred (fun | .combatRole .attacking => true | _ => false) then
      .own
    else if objPredHasAtom pred (fun | .stat .power .le _ => true | _ => false) then
      .own
    else .opponent

/-! ### Canonical `ToOracle` Rendering (`TargetDomain`, `TargetSlot`, `TargetSpec`) -/

private def renderObjectFilterForTarget (ctx : PrintCtx) (zones : ZoneSetSpec) (pred : ObjectPred) : String :=
  -- Special concise Oracle phrasing for bare creature-subtype permanent targets:
  -- e.g. `"Elf you control"`, `"Goblin or Orc you control"`.
  let atoms := objPredAtoms pred
  let bareCreatureSubtype? : Option String :=
    if zones != .battlefield then none
    else
      match atoms with
      | [.hasSubtype (.literal s), .hasType .creature, .controlledBy { relation := .you, pred := .any }] =>
        if s.isCreatureType then
          some s!"{if ctx.plural then s.pluralName else s.englishName} you control"
        else none
      | [.any ss, .hasType .creature, .controlledBy { relation := .you, pred := .any }] =>
        let subs := ss.toList.filterMap fun
          | .hasSubtype (.literal s) => if s.isCreatureType then some s else none
          | _ => none
        if subs.length == ss.size && !subs.isEmpty then
          let names := subs.map fun s => if ctx.plural then s.pluralName else s.englishName
          some s!"{orJoin names} you control"
        else none
      | _ => none
  match bareCreatureSubtype? with
  | some s => s
  | none =>
    let raw :=
      if zones.zones == #[.graveyard] then
        -- Render graveyard targets using `"from ... graveyard"` after any `with` clauses
        -- (matching standard MTG Oracle wording: `"target creature card with mana value 3 or less from your graveyard"`).
        let base := toOracleStr (ObjectFilter.mk .battlefield pred) { ctx with capitalize := false }
        let base :=
          if !atoms.any (fun | .isKind .card | .isKind .permanentCard => true | _ => false) &&
             !base.endsWith " card" && !base.endsWith " cards" then
            -- Ensure `"card"` head appears when no explicit `.isKind` atom was supplied.
            toOracleStr (ObjectFilter.mk .battlefield (ObjectPred.andAll (atoms.toArray.push .isCard)))
              { ctx with capitalize := false }
          else base
        let gyLoc :=
          match zones.owner with
          | .any => "from a graveyard"
          | .matching { relation := .you, pred := .any } => "from your graveyard"
          | .matching { relation := .opponent, pred := .any } => "from an opponent's graveyard"
          | .matching pf => s!"from {toOracleStr pf { ctx with capitalize := false }}'s graveyard"
          | .ofPlayer .you => "from your graveyard"
          | .ofPlayer pe => s!"from {toOracleStr pe { ctx with capitalize := false }}'s graveyard"
        s!"{base} {gyLoc}"
      else
        let rendered := toOracleStr (ObjectFilter.mk zones pred) { ctx with capitalize := false }
        -- Omit redundant `" on the stack"` when `"spell"` / `"spells"` already implies the stack.
        if zones == .stack && atoms.any (· == .isKind .spell) then
          rendered.replace " on the stack" ""
        else rendered
    -- Idiomatic MTG comma between `"nonland"` and `"nontoken"`.
    (raw.replace "nontoken nonland" "nonland, nontoken").replace "nonland nontoken" "nonland, nontoken"

private def renderPlayerTargetBody (ctx : PrintCtx) (pf : PlayerFilter) : String :=
  match pf.relation, pf.pred with
  | .anyPlayer, .any => if ctx.plural then "players" else "player"
  | .opponent, .any => if ctx.plural then "opponents" else "opponent"
  | .teammate, .any => if ctx.plural then "teammates" else "teammate"
  | .you, .any => "you"
  | .anyPlayer, .isDefendingPlayer => "defending player"
  | .anyPlayer, .isSeat _ | .anyPlayer, .thatPlayer => "that player"
  | rel, p =>
    let head :=
      match rel with
      | .anyPlayer => if ctx.plural then "players" else "player"
      | .opponent => if ctx.plural then "opponents" else "opponent"
      | .teammate => if ctx.plural then "teammates" else "teammate"
      | .you => "you"
    s!"{head} who {toOracleStr p { ctx with capitalize := false }}"

private partial def renderDomainBody (ctx : PrintCtx) : TargetDomain → String
  | .object zones pred => renderObjectFilterForTarget ctx zones pred
  | .player pf => renderPlayerTargetBody ctx pf
  | .anyTarget .any => if ctx.plural then "targets" else "any target"
  | .anyTarget (.otherThan _) => if ctx.plural then "other targets" else "any other target"
  | .anyTarget (.filtered op pf) =>
    s!"{renderObjectFilterForTarget ctx .battlefield op} or {renderPlayerTargetBody ctx pf}"
  | .stackAbility ctrl src =>
    let ctrlS :=
      if ctrl == PlayerFilter.you then "you control"
      else if ctrl == PlayerFilter.opponent then "an opponent controls"
      else if ctrl == PlayerFilter.any then ""
      else s!"{toOracleStr ctrl { ctx with capitalize := false }} controls"
    let abWord := if ctx.plural then "activated or triggered abilities" else "activated or triggered ability"
    let srcPart :=
      match src with
      | .all #[] => ""
      | .hasType ty =>
        let w := ty.oracleWord
        s!" from {indefinite w} {w} source"
      | other =>
        let w := toOracleStr (ObjectFilter.mk .battlefield other) { ctx with plural := false, capitalize := false }
        s!" from {indefinite w} {w} source"
    let mid := if ctrlS.isEmpty then abWord else s!"{abWord} {ctrlS}"
    s!"{mid}{srcPart}"
  | .anyOf ds =>
    let parts := ds.map (renderDomainBody ctx)
    -- Special `"creature card in a graveyard"` phrasing for multi-zone union.
    let parts := parts.map fun p => p.replace " from a graveyard" " in a graveyard"
    orJoin parts.toList

private def renderGroupConstraintSuffix (ctx : PrintCtx) : GroupTargetConstraint → String
  | .totalManaValueAtMost cap =>
    s!" with total mana value {toOracleStr cap { ctx with capitalize := false }} or less"
  | .shareCharacteristic .color => " that share a color"
  | .shareCharacteristic .cardType => " that share a card type"
  | .shareCharacteristic .creatureType => " that share a creature type"
  | .shareCharacteristic .subtype => " that share a subtype"
  | .shareCharacteristic .name => " that share a name"
  | .distinctControllers => " with different controllers"
  | .distinctNames => " with different names"
  | .distinctCardTypes => " of each card type"

/-- Render one `TargetSlot` to canonical Oracle text (CR 115.1 / 207). -/
def TargetSlot.renderOracle (ctx : PrintCtx) (slot : TargetSlot) : String :=
  let plural := slot.count.isPlural
  let subCtx := { ctx with plural, capitalize := false }
  let domain :=
    match slot.forEach? with
    | some pf =>
      if pf == PlayerFilter.opponent then slot.domain.substituteOpponent .thatPlayer
      else slot.domain
    | none => slot.domain
  let qPfx := slot.count.quantifierPrefix
  let core : String :=
    match domain with
    | .anyTarget .any =>
      if slot.count == CountRange.exact 1 then "any target"
      else if qPfx.isEmpty then "any target"
      else s!"{qPfx} {if plural then "targets" else "target"}"
    | .anyTarget (.otherThan _) =>
      if slot.count == CountRange.exact 1 then "any other target"
      else if qPfx.isEmpty then "any other target"
      else s!"{qPfx} other {if plural then "targets" else "target"}"
    | .object zones pred =>
      let (hasOther, restPred) := splitOtherThan pred
      let body := renderObjectFilterForTarget subCtx zones restPred
      if hasOther then
        if slot.count == CountRange.exact 1 then s!"another target {body}"
        else s!"{qPfx} other target {body}"
      else
        if qPfx.isEmpty then s!"target {body}"
        else s!"{qPfx} target {body}"
    | other =>
      let body := renderDomainBody subCtx other
      if qPfx.isEmpty then s!"target {body}"
      else s!"{qPfx} target {body}"
  let gcSfx :=
    match slot.groupConstraint? with
    | some gc => renderGroupConstraintSuffix subCtx gc
    | none => ""
  let full :=
    match slot.forEach? with
    | some pf =>
      let who :=
        if pf == PlayerFilter.opponent then "each opponent"
        else if pf == PlayerFilter.any then "each player"
        else s!"each {toOracleStr pf { ctx with capitalize := false }}"
      s!"for {who}, {core}{gcSfx}"
    | none => s!"{core}{gcSfx}"
  if ctx.capitalize then capitalizeAscii full else full

instance : ToOracle TargetDomain where
  toOracle ctx d :=
    let s := renderDomainBody { ctx with capitalize := false } d
    if ctx.capitalize then capitalizeAscii s else s

instance : ToOracle TargetSlot where
  toOracle ctx slot := slot.renderOracle ctx

instance : ToOracle TargetSpec where
  toOracle ctx ts :=
    let raw :=
      match ts.slots.toList with
      | [] => ""
      | [s] => s.renderOracle { ctx with capitalize := false }
      | [s0, s1] =>
        let isSecondDistinct :=
          s0 == s1 &&
            ts.crossSlotConstraints.any fun c =>
              c.relation == .distinct && c.slots == #[0, 1]
        if isSecondDistinct then
          s!"{s0.renderOracle { ctx with capitalize := false }} and a second {s1.renderOracle { ctx with capitalize := false }}"
        else
          s!"{s0.renderOracle { ctx with capitalize := false }} and {s1.renderOracle { ctx with capitalize := false }}"
      | ss =>
        String.intercalate " and " (ss.map fun s => s.renderOracle { ctx with capitalize := false })
    if ctx.capitalize then capitalizeAscii raw else raw

/-! ### `TargetSlot` and `TargetSpec` Operations -/

namespace TargetSlot

/-- Construct a single-target slot for `domain`. -/
def of (domain : TargetDomain) (count : CountRange := .exact 1) : TargetSlot :=
  { domain, count }

/-- Canonical Oracle noun phrase for this slot. -/
def noun (s : TargetSlot) : String :=
  s.renderOracle {}

/-- Number of flat target positions occupied by this slot when announcing. -/
def width (s : TargetSlot) : Nat :=
  max 1 (s.count.maxCount 100)

/-- Minimum targets required for this slot. -/
def minCount (s : TargetSlot) : Nat :=
  s.count.minCount

/-- Maximum targets allowed for this slot. -/
def maxCount (s : TargetSlot) (fallback : Nat := 100) : Nat :=
  s.count.maxCount fallback

/-- True when zero targets may be chosen for this slot. -/
def allowsZero (s : TargetSlot) : Bool :=
  s.count.allowsZero

/-- True when this slot targets any stack spell or ability. -/
def targetsStackSpell (s : TargetSlot) : Bool :=
  s.domain.targetsStackSpell

/-- Structural default AI preference for this slot. -/
def defaultPreference (s : TargetSlot) : TargetPreference :=
  s.domain.defaultPreference

/-- Apply legacy `(allowsZero, maxTargets)` bounds when refining a single slot. -/
def withBounds (s : TargetSlot) (allowsZero : Bool) (maxTargets : Nat) : TargetSlot :=
  if s.count == .anyNumber then s
  else
    let curMax := s.count.maxCount
    let nextMax := if maxTargets == 0 then curMax else max maxTargets 1
    let curMin := s.count.minCount
    let nextMin := if allowsZero then 0 else min curMin nextMax
    { s with count := CountRange.ofBounds nextMin nextMax }

end TargetSlot

namespace TargetSpec

/-- No target (`slots := #[]`). -/
def none : TargetSpec := {}

/-- Single `"target"` word specification. -/
def single (slot : TargetSlot) : TargetSpec :=
  { slots := #[slot] }

/-- Single `"target"` word specification for `domain` with count `count`. -/
def ofDomain (domain : TargetDomain) (count : CountRange := .exact 1) : TargetSpec :=
  single { domain, count }

/-- Multi-slot targeting specification (one `TargetSlot` per `"target"` word). -/
def ofSlots (slots : Array TargetSlot) (cross : Array CrossSlotConstraint := #[]) : TargetSpec :=
  { slots, crossSlotConstraints := cross }

/-- Concatenate two targeting specifications in printed order (e.g. combining
chosen modes of a modal spell or ability, CR 700.2). -/
def append (a b : TargetSpec) : TargetSpec :=
  let off := a.slots.size
  { slots := a.slots ++ b.slots
    crossSlotConstraints :=
      a.crossSlotConstraints ++
        b.crossSlotConstraints.map fun c => { c with slots := c.slots.map (· + off) } }

/-- True when this specification has no `"target"` slots. -/
def isEmpty (ts : TargetSpec) : Bool :=
  ts.slots.isEmpty

/-- True when this specification has exactly one `"target"` word. -/
def isSingleSlot (ts : TargetSpec) : Bool :=
  ts.slots.size == 1

/-- True when this specification has multiple sequential `"target"` words. -/
def isMultiSlot (ts : TargetSpec) : Bool :=
  ts.slots.size > 1

/-- Total flat target positions across all slots. -/
def totalPositions (ts : TargetSpec) : Nat :=
  ts.slots.foldl (fun acc s => acc + s.width) 0

/-- Minimum total targets across all slots. -/
def minTargetCount (ts : TargetSpec) : Nat :=
  ts.slots.foldl (fun acc s => acc + s.minCount) 0

/-- Maximum total targets across all slots. -/
def maxTargetCount (ts : TargetSpec) (fallback : Nat := 100) : Nat :=
  ts.slots.foldl (fun acc s => acc + s.maxCount fallback) 0

/-- Canonical target count of this specification (0 when untargeted; for a
single `.between lo hi` slot returns `lo`; for `.exact n` / `.upTo n` returns
`n`; for multi-slot returns `totalPositions`). -/
def targetCount (ts : TargetSpec) : Nat :=
  match ts.slots.toList with
  | [] => 0
  | [s] =>
    match s.count with
    | .exact n => n
    | .upTo n => n
    | .between lo _ => lo
    | .anyNumber => 1
  | _ => ts.totalPositions

/-- True when every slot allows choosing zero targets (CR 115.1c). -/
def allowsZero (ts : TargetSpec) : Bool :=
  !ts.slots.isEmpty && ts.slots.all TargetSlot.allowsZero

/-- Canonical Oracle noun phrase for this targeting specification. -/
def noun (ts : TargetSpec) : String :=
  toOracleStr ts

/-- Map a flat target position `pos` to `(slotIdx, slot, offsetWithinSlot)`. -/
def slotAtPos? (ts : TargetSpec) (pos : Nat) : Option (Nat × TargetSlot × Nat) := Id.run do
  let mut cursor : Nat := 0
  for i in [0:ts.slots.size] do
    let s := ts.slots[i]!
    let w := s.width
    if pos < cursor + w then
      return some (i, s, pos - cursor)
    cursor := cursor + w
  return Option.none

/-- `TargetSlot` owning flat target position `pos` (defaults to slot 0). -/
def slotAtPos (ts : TargetSpec) (pos : Nat) : TargetSlot :=
  match ts.slotAtPos? pos with
  | some (_, s, _) => s
  | Option.none => ts.slots[0]?.getD default

/-- 0-based `TargetSlot` index owning flat target position `pos`. -/
def slotIndexOfPos (ts : TargetSpec) (pos : Nat) : Nat :=
  match ts.slotAtPos? pos with
  | some (i, _, _) => i
  | Option.none => 0

/-- Half-open flat position range `[start, stop)` occupied by `slotIdx`. -/
def posRangeOfSlot (ts : TargetSpec) (slotIdx : Nat) : Nat × Nat := Id.run do
  let mut cursor : Nat := 0
  for i in [0:ts.slots.size] do
    let w := ts.slots[i]!.width
    if i == slotIdx then
      return (cursor, cursor + w)
    cursor := cursor + w
  return (cursor, cursor)

/-- Half-open flat position range `[start, stop)` sharing one instance of the
word `"target"` containing flat position `pos` (CR 601.2c). -/
def instanceGroupBounds (ts : TargetSpec) (pos : Nat) : Nat × Nat :=
  match ts.slotAtPos? pos with
  | some (slotIdx, _, _) => ts.posRangeOfSlot slotIdx
  | Option.none => (pos, pos + 1)

/-- True when flat target position `pos` is optional (`offset >= slot.minCount`,
CR 115.1c / 601.2c). -/
def isOptionalPos (ts : TargetSpec) (pos : Nat) : Bool :=
  match ts.slotAtPos? pos with
  | some (_, s, off) => off >= s.minCount
  | Option.none => false

/-- True when slot `slotIdx` allows choosing zero targets (`minCount == 0`). -/
def isOptionalSlot (ts : TargetSpec) (slotIdx : Nat) : Bool :=
  (ts.slots[slotIdx]?.map TargetSlot.allowsZero).getD false

/-- 0-based flat-position groups whose chosen targets must be pairwise distinct
under CR 115.3 (every slot with width > 1 plus every cross-slot `.distinct`
constraint). -/
def distinctPosGroups (ts : TargetSpec) : Array (Array Nat) := Id.run do
  let mut groups : Array (Array Nat) := #[]
  let mut cursor : Nat := 0
  for i in [0:ts.slots.size] do
    let w := ts.slots[i]!.width
    if w > 1 then
      groups := groups.push ((List.range w).toArray.map (· + cursor))
    cursor := cursor + w
  for c in ts.crossSlotConstraints do
    if c.relation == .distinct then
      let mut grp : Array Nat := #[]
      for si in c.slots do
        let (lo, hi) := ts.posRangeOfSlot si
        for p in [lo:hi] do
          if !grp.contains p then grp := grp.push p
      if grp.size > 1 then
        groups := groups.push grp
  return groups

/-- `(constraint, flatPositions)` pairs for all intra-slot `groupConstraint?`s
and cross-slot `.group` constraints. -/
def constraintPosGroups (ts : TargetSpec) : Array (GroupTargetConstraint × Array Nat) := Id.run do
  let mut out : Array (GroupTargetConstraint × Array Nat) := #[]
  let mut cursor : Nat := 0
  for i in [0:ts.slots.size] do
    let s := ts.slots[i]!
    let w := s.width
    if let some gc := s.groupConstraint? then
      out := out.push (gc, (List.range w).toArray.map (· + cursor))
    cursor := cursor + w
  for c in ts.crossSlotConstraints do
    if let .group gc := c.relation then
      let mut grp : Array Nat := #[]
      for si in c.slots do
        let (lo, hi) := ts.posRangeOfSlot si
        for p in [lo:hi] do
          if !grp.contains p then grp := grp.push p
      if !grp.isEmpty then
        out := out.push (gc, grp)
  return out

/-- Constant total-mana-value cap if any slot constrains combined MV ≤ `n`. -/
def totalMvCap? (ts : TargetSpec) : Option Nat :=
  ts.slots.findSome? fun s =>
    match s.groupConstraint? with
    | some (.totalManaValueAtMost (.const n)) => if n >= 0 then some n.toNat else Option.none
    | _ => Option.none

/-- True when any slot targets a spell or ability on the stack. -/
def targetsStackSpell (ts : TargetSpec) : Bool :=
  ts.slots.any TargetSlot.targetsStackSpell

/-- Structural default AI preference for this targeting specification. -/
def defaultPreference (ts : TargetSpec) : TargetPreference :=
  match ts.slots.toList with
  | [] => .own
  | [s] =>
    if s.count == .exact 2 && s.domain == .player .any then .ownThenOpponent
    else s.defaultPreference
  | [s0, s1] =>
    if s0.allowsZero && s1.domain == .player .any then .own
    else
      match s0.defaultPreference, s1.defaultPreference with
      | .own, .opponent => .ownThenOpponent
      | p0, _ => p0
  | s0 :: _ => s0.defaultPreference

/-- Canonical Oracle noun for slot `slotIdx` (with its exact `CountRange`
quantifier, e.g. `"up to one target creature"`, `"target player"`). -/
def announcedSlotNoun (ts : TargetSpec) (slotIdx : Nat) : String :=
  match ts.slots[slotIdx]? with
  | some s => s.noun
  | Option.none => ""

/-- Canonical Oracle noun for the `"target"` word containing flat position `pos`. -/
def announcedPosNoun (ts : TargetSpec) (pos : Nat) : String :=
  ts.announcedSlotNoun (ts.slotIndexOfPos pos)

/-- Apply `(allowsZero, maxTargets)` bounds when `ts` is a single slot. -/
def withSlotBounds (ts : TargetSpec) (allowsZero : Bool) (maxTargets : Nat) : TargetSpec :=
  if ts.slots.size == 1 then
    { ts with slots := #[ts.slots[0]!.withBounds allowsZero maxTargets] }
  else ts

/-- Refine a single-slot `TargetSpec` to target up to `n` targets (CR 115.1c). -/
def asUpTo (ts : TargetSpec) (n : Nat := 1) : TargetSpec :=
  ts.withSlotBounds true n

/-- Refine a single-slot `TargetSpec` to target between `lo` and `hi` targets (CR 115.1c). -/
def asBetween (ts : TargetSpec) (lo hi : Nat) : TargetSpec :=
  if ts.slots.size == 1 then
    { ts with slots := #[{ ts.slots[0]! with count := CountRange.ofBounds lo hi }] }
  else ts

/-- Refine a single-slot `TargetSpec` to target any number of targets (CR 115.1c). -/
def asAnyNumber (ts : TargetSpec) : TargetSpec :=
  if ts.slots.size == 1 then
    { ts with slots := #[{ ts.slots[0]! with count := .anyNumber }] }
  else ts

/-- Single-slot divided-damage targeting specification (CR 601.2d):
`amount` damage divided among one to `maxTargets` targets matching `domain`. -/
def dividedDamage (domain : TargetDomain) (amount maxTargets : Nat) : TargetSpec :=
  single {
    domain
    count := if maxTargets <= 1 then .exact 1 else .between 1 maxTargets
    division? := some (.damage, .const (Int.ofNat amount))
  }

/-- Extract `(amount, maxTargets)` from a divided-damage `TargetSpec`, if any (CR 601.2d). -/
def dividedDamage? (ts : TargetSpec) : Option (Nat × Nat) :=
  match ts.slots[0]? with
  | some slot =>
    match slot.division? with
    | some (.damage, .const n) =>
      if n >= 0 then some (n.toNat, slot.maxCount) else Option.none
    | _ => Option.none
  | Option.none => Option.none

/-- If `ts` is a single slot targeting a creature you control with one literal
subtype (`Equip <Subtype>`, etc.), return that subtype. -/
def creatureYouControlSubtype? (ts : TargetSpec) : Option CardSubtype :=
  match ts.slots.toList with
  | [{ domain := .object zs pred, count := .exact 1, groupConstraint? := Option.none, .. }] =>
    if zs != .battlefield then Option.none
    else
      match objPredAtoms pred with
      | [.hasSubtype (.literal s), .hasType .creature, .controlledBy pf]
      | [.hasSubtype (.literal s), .controlledBy pf] =>
        if pf == .you then some s else Option.none
      | _ => Option.none
  | _ => Option.none

/-- If `ts` is a single slot targeting a creature you control with one or more
literal subtypes (`target Elf you control`, `target Goblin or Orc you control`),
return those subtypes. -/
def creatureYouControlAnySubtype? (ts : TargetSpec) : Option (Array CardSubtype) :=
  match ts.slots.toList with
  | [{ domain := .object zs pred, count := .exact 1, groupConstraint? := Option.none, .. }] =>
    if zs != .battlefield then Option.none
    else
      match objPredAtoms pred with
      | [.hasSubtype (.literal s), .hasType .creature, .controlledBy pf]
      | [.hasSubtype (.literal s), .controlledBy pf] =>
        if pf == .you then some #[s] else Option.none
      | [.any ss, .hasType .creature, .controlledBy pf]
      | [.any ss, .controlledBy pf] =>
        if pf == .you then
          let subs := ss.filterMap fun
            | .hasSubtype (.literal s) => some s
            | _ => Option.none
          if subs.size == ss.size && !subs.isEmpty then some subs else Option.none
        else Option.none
      | _ => Option.none
  | _ => Option.none

/-- True when `ts` is the MSH Equip worthy target (`worthyCreatureYouControl`). -/
def isWorthyCreatureYouControl (ts : TargetSpec) : Bool :=
  match ts.slots.toList with
  | [{ domain := .object zs pred, count := .exact 1, .. }] =>
    zs == .battlefield &&
      pred == ObjectPred.andAll #[ObjectPred.worthy, .controlledBy .you]
  | _ => false

end TargetSpec

/-! ### Compositional `TargetDomain` and `TargetSpec` Smart Constructors -/

namespace TargetDomain

def creature : TargetDomain :=
  .object .battlefield (.hasType .creature)

def creatureYouControl : TargetDomain :=
  .object .battlefield (.all #[.hasType .creature, .controlledBy .you])

def anotherCreatureYouControl : TargetDomain :=
  .object .battlefield (.all #[.otherThan .this, .hasType .creature, .controlledBy .you])

def anotherCreature : TargetDomain :=
  .object .battlefield (.all #[.otherThan .this, .hasType .creature])

def oppCreature : TargetDomain :=
  .object .battlefield (.all #[.hasType .creature, .controlledBy .opponent])

def oppTappedCreature : TargetDomain :=
  .object .battlefield (.all #[.tapped true, .hasType .creature, .controlledBy .opponent])

def creatureWithFlying : TargetDomain :=
  .object .battlefield (.all #[.hasType .creature, .hasKeyword .flying])

def artifactOrLand : TargetDomain :=
  .object .battlefield (.any #[.hasType .artifact, .hasType .land])

def colorlessNonland : TargetDomain :=
  .object .battlefield (.all #[.colorCount .eq 0, .not (.hasType .land)])

def artifactOrEnchantment : TargetDomain :=
  .object .battlefield (.any #[.hasType .artifact, .hasType .enchantment])

def artifactOrCreatureYouControl : TargetDomain :=
  .object .battlefield (.all #[.any #[.hasType .artifact, .hasType .creature], .controlledBy .you])

def nonland : TargetDomain :=
  .object .battlefield (.not (.hasType .land))

def oppNonland : TargetDomain :=
  .object .battlefield (.all #[.not (.hasType .land), .controlledBy .opponent])

def attackingCreatureWithoutFlying : TargetDomain :=
  .object .battlefield (.all #[.combatRole .attacking, .hasType .creature, .not (.hasKeyword .flying)])

def creatureYouControlSubtype (s : CardSubtype) : TargetDomain :=
  if s.isCreatureType then
    .object .battlefield (.all #[.hasSubtype (.literal s), .hasType .creature, .controlledBy .you])
  else
    .object .battlefield (.all #[.hasSubtype (.literal s), .controlledBy .you])

def creatureYouControlAnySubtype (ss : Array CardSubtype) : TargetDomain :=
  if ss.isEmpty then creatureYouControl
  else
    let subPred := ObjectPred.orAny (ss.map fun s => .hasSubtype (.literal s))
    if ss.all CardSubtype.isCreatureType then
      .object .battlefield (.all #[subPred, .hasType .creature, .controlledBy .you])
    else
      .object .battlefield (.all #[subPred, .controlledBy .you])

def spell : TargetDomain :=
  .object .stack .isSpell

def creatureSpell : TargetDomain :=
  .object .stack (.all #[.hasType .creature, .isKind .spell])

def creatureSpellPTAtMost (n : Nat) : TargetDomain :=
  .object .stack (.all #[
    .hasType .creature,
    .isKind .spell,
    .any #[.stat .power .le (.const n), .stat .toughness .le (.const n)]
  ])

def defendingPlayerCreature : TargetDomain :=
  .object .battlefield (.all #[.hasType .creature, .controlledBy .defendingPlayer])

def creaturePowerAtLeast (n : Int) : TargetDomain :=
  .object .battlefield (.all #[.hasType .creature, .stat .power .ge (.const n)])

def creaturePowerAtMost (n : Int) : TargetDomain :=
  .object .battlefield (.all #[.hasType .creature, .stat .power .le (.const n)])

def creatureYouControlPowerAtMost (n : Int) : TargetDomain :=
  .object .battlefield (.all #[.hasType .creature, .controlledBy .you, .stat .power .le (.const n)])

def anotherCreatureYouControlPowerAtMost (n : Int) : TargetDomain :=
  .object .battlefield (.all #[.otherThan .this, .hasType .creature, .controlledBy .you, .stat .power .le (.const n)])

def oppCreaturePowerAtMost (n : Int) : TargetDomain :=
  .object .battlefield (.all #[.hasType .creature, .controlledBy .opponent, .stat .power .le (.const n)])

def permanent : TargetDomain :=
  .object .battlefield .anyObject

def permanentYouControl : TargetDomain :=
  .object .battlefield (.controlledBy .you)

def oppPermanent : TargetDomain :=
  .object .battlefield (.controlledBy .opponent)

def legendaryCreatureYouControl : TargetDomain :=
  .object .battlefield (.all #[.hasSupertype .legendary, .hasType .creature, .controlledBy .you])

def artifact : TargetDomain :=
  .object .battlefield (.hasType .artifact)

def oppArtifact : TargetDomain :=
  .object .battlefield (.all #[.hasType .artifact, .controlledBy .opponent])

def artifactYouControl : TargetDomain :=
  .object .battlefield (.all #[.hasType .artifact, .controlledBy .you])

def artifactToken : TargetDomain :=
  .object .battlefield (.all #[.hasType .artifact, .isToken true])

def land : TargetDomain :=
  .object .battlefield (.hasType .land)

def attackingCreature : TargetDomain :=
  .object .battlefield (.all #[.combatRole .attacking, .hasType .creature])

def attackingOrBlockingCreature : TargetDomain :=
  .object .battlefield (.all #[.any #[.combatRole .attacking, .combatRole .blocking], .hasType .creature])

def attackingAloneCreatureYouControl : TargetDomain :=
  .object .battlefield (.all #[.hasType .creature, .controlledBy .you, .combatRole .attackingAlone])

def equipmentYouControl : TargetDomain :=
  .object .battlefield (.all #[.hasSubtype (.literal .equipment), .controlledBy .you])

def creatureOrLandYouControl : TargetDomain :=
  .object .battlefield (.all #[.any #[.hasType .creature, .hasType .land], .controlledBy .you])

def creatureMvAtMost (n : Nat) : TargetDomain :=
  .object .battlefield (.all #[.hasType .creature, .stat .manaValue .le (.const n)])

def creatureToughnessAtLeast (n : Int) : TargetDomain :=
  .object .battlefield (.all #[.hasType .creature, .stat .toughness .ge (.const n)])

def enchantmentMvAtLeast (n : Nat) : TargetDomain :=
  .object .battlefield (.all #[.hasType .enchantment, .stat .manaValue .ge (.const n)])

def noncreatureArtifact : TargetDomain :=
  .object .battlefield (.all #[.not (.hasType .creature), .hasType .artifact])

def noncreatureArtifactOrEnchantment : TargetDomain :=
  .object .battlefield (.any #[
    .all #[.not (.hasType .creature), .hasType .artifact],
    .all #[.not (.hasType .creature), .hasType .enchantment]
  ])

def oppCreatureDealtDamageThisTurn : TargetDomain :=
  .object .battlefield (.all #[.hasType .creature, .controlledBy .opponent, .dealtDamageThisTurn false Option.none])

def nonlandNontoken : TargetDomain :=
  .object .battlefield (.all #[.not (.hasType .land), .isToken false])

def creatureOrPlaneswalker : TargetDomain :=
  .object .battlefield (.any #[.hasType .creature, .hasType .planeswalker])

def planeswalkerYouControl : TargetDomain :=
  .object .battlefield (.all #[.hasType .planeswalker, .controlledBy .you])

def oppCreatureOrPlaneswalker : TargetDomain :=
  .object .battlefield (.all #[.any #[.hasType .creature, .hasType .planeswalker], .controlledBy .opponent])

def worthyCreatureYouControl : TargetDomain :=
  .object .battlefield (ObjectPred.andAll #[ObjectPred.worthy, .controlledBy .you])

def elfInYourGraveyard : TargetDomain :=
  .object .yourGraveyard (.all #[.hasSubtype (.literal .elf), .isKind .card])

def oppGraveyardCard : TargetDomain :=
  .object .opponentGraveyard .isCard

def creatureCardInYourGraveyard : TargetDomain :=
  .object .yourGraveyard (.all #[.hasType .creature, .isKind .card])

def creatureCardInYourGraveyardMvAtMost (n : Nat) : TargetDomain :=
  .object .yourGraveyard (.all #[.hasType .creature, .isKind .card, .stat .manaValue .le (.const n)])

def permanentCardInYourGraveyard : TargetDomain :=
  .object .yourGraveyard .isPermanentCard

def equipmentInstantOrSorceryInYourGraveyard : TargetDomain :=
  .object .yourGraveyard (.all #[
    .any #[.hasSubtype (.literal .equipment), .hasType .instant, .hasType .sorcery],
    .isKind .card
  ])

def artEnchCardInYourGraveyard : TargetDomain :=
  .object .yourGraveyard (.all #[.any #[.hasType .artifact, .hasType .enchantment], .isKind .card])

def creatureOrGyCreatureCard : TargetDomain :=
  .anyOf #[
    .object .battlefield (.hasType .creature),
    .object .anyGraveyard (.all #[.hasType .creature, .isKind .card])
  ]

def spellOrCreature : TargetDomain :=
  .anyOf #[.object .stack .isSpell, .object .battlefield (.hasType .creature)]

def permanentOrPlayer : TargetDomain :=
  .anyOf #[.object .battlefield .anyObject, .player .any]

def anyPlayer : TargetDomain :=
  .player .any

def opponent : TargetDomain :=
  .player .opponent

end TargetDomain

namespace TargetSpec

def creature : TargetSpec := ofDomain .creature
def creatureYouControl : TargetSpec := ofDomain .creatureYouControl
def anotherCreatureYouControl : TargetSpec := ofDomain .anotherCreatureYouControl
def anotherCreature : TargetSpec := ofDomain .anotherCreature
def anyTarget : TargetSpec := ofDomain (.anyTarget .any)
def anyOtherTarget : TargetSpec := ofDomain (.anyTarget (.otherThan .this))
def player : TargetSpec := ofDomain .anyPlayer
def opponent : TargetSpec := ofDomain .opponent
def oppCreature : TargetSpec := ofDomain .oppCreature
def oppTappedCreature : TargetSpec := ofDomain .oppTappedCreature
def creatureWithFlying : TargetSpec := ofDomain .creatureWithFlying
def artifactOrLand : TargetSpec := ofDomain .artifactOrLand
def colorlessNonland : TargetSpec := ofDomain .colorlessNonland
def artifactOrEnchantment : TargetSpec := ofDomain .artifactOrEnchantment
def artifactOrCreatureYouControl : TargetSpec := ofDomain .artifactOrCreatureYouControl
def nonland : TargetSpec := ofDomain .nonland
def oppNonland : TargetSpec := ofDomain .oppNonland
def attackingCreatureWithoutFlying : TargetSpec := ofDomain .attackingCreatureWithoutFlying
def creatureYouControlSubtype (s : CardSubtype) : TargetSpec := ofDomain (.creatureYouControlSubtype s)
def creatureYouControlAnySubtype (ss : Array CardSubtype) : TargetSpec := ofDomain (.creatureYouControlAnySubtype ss)
def spell : TargetSpec := ofDomain .spell
def creatureSpell : TargetSpec := ofDomain .creatureSpell
def creatureSpellPTAtMost (n : Nat) : TargetSpec := ofDomain (.creatureSpellPTAtMost n)
def defendingPlayerCreature : TargetSpec := ofDomain .defendingPlayerCreature
def creaturePowerAtLeast (n : Int) : TargetSpec := ofDomain (.creaturePowerAtLeast n)
def creaturePowerAtMost (n : Int) : TargetSpec := ofDomain (.creaturePowerAtMost n)
def creatureYouControlPowerAtMost (n : Int) : TargetSpec := ofDomain (.creatureYouControlPowerAtMost n)
def anotherCreatureYouControlPowerAtMost (n : Int) : TargetSpec := ofDomain (.anotherCreatureYouControlPowerAtMost n)
def oppCreaturePowerAtMost (n : Int) : TargetSpec := ofDomain (.oppCreaturePowerAtMost n)
def permanent : TargetSpec := ofDomain .permanent
def permanentYouControl : TargetSpec := ofDomain .permanentYouControl
def oppPermanent : TargetSpec := ofDomain .oppPermanent
def legendaryCreatureYouControl : TargetSpec := ofDomain .legendaryCreatureYouControl
def artifact : TargetSpec := ofDomain .artifact
def oppArtifact : TargetSpec := ofDomain .oppArtifact
def artifactYouControl : TargetSpec := ofDomain .artifactYouControl
def artifactToken : TargetSpec := ofDomain .artifactToken
def land : TargetSpec := ofDomain .land
def attackingCreature : TargetSpec := ofDomain .attackingCreature
def attackingOrBlockingCreature : TargetSpec := ofDomain .attackingOrBlockingCreature
def attackingAloneCreatureYouControl : TargetSpec := ofDomain .attackingAloneCreatureYouControl
def equipmentYouControl : TargetSpec := ofDomain .equipmentYouControl
def creatureOrLandYouControl : TargetSpec := ofDomain .creatureOrLandYouControl
def creatureMvAtMost (n : Nat) : TargetSpec := ofDomain (.creatureMvAtMost n)
def creatureMvAtMostOrAnyIfTeamwork (n : Nat) : TargetSpec :=
  single {
    domain := .creatureMvAtMost n
    altDomainIf? := some (.castPred (.teamworkPaid .this), .creature)
  }
def creatureToughnessAtLeast (n : Int) : TargetSpec := ofDomain (.creatureToughnessAtLeast n)
def enchantmentMvAtLeast (n : Nat) : TargetSpec := ofDomain (.enchantmentMvAtLeast n)
def noncreatureArtifact : TargetSpec := ofDomain .noncreatureArtifact
def noncreatureArtifactOrEnchantment : TargetSpec := ofDomain .noncreatureArtifactOrEnchantment
def oppCreatureDealtDamageThisTurn : TargetSpec := ofDomain .oppCreatureDealtDamageThisTurn
def nonlandNontoken : TargetSpec := ofDomain .nonlandNontoken
def creatureOrPlaneswalker : TargetSpec := ofDomain .creatureOrPlaneswalker
def planeswalkerYouControl : TargetSpec := ofDomain .planeswalkerYouControl
def oppCreatureOrPlaneswalker : TargetSpec := ofDomain .oppCreatureOrPlaneswalker
def worthyCreatureYouControl : TargetSpec := ofDomain .worthyCreatureYouControl
def elfInYourGraveyard : TargetSpec := ofDomain .elfInYourGraveyard
def oppGraveyardCard : TargetSpec := ofDomain .oppGraveyardCard
def creatureCardInYourGraveyard : TargetSpec := ofDomain .creatureCardInYourGraveyard
def creatureCardInYourGraveyardMvAtMost (n : Nat) : TargetSpec := ofDomain (.creatureCardInYourGraveyardMvAtMost n)
def creatureCardInYourGraveyardMvAtMostOrAnyIfTeamwork (n : Nat) : TargetSpec :=
  single {
    domain := .creatureCardInYourGraveyardMvAtMost n
    altDomainIf? := some (.castPred (.teamworkPaid .this), .creatureCardInYourGraveyard)
  }
def permanentCardInYourGraveyard : TargetSpec := ofDomain .permanentCardInYourGraveyard
def equipmentInstantOrSorceryInYourGraveyard : TargetSpec := ofDomain .equipmentInstantOrSorceryInYourGraveyard
def artEnchCardInYourGraveyard : TargetSpec := ofDomain .artEnchCardInYourGraveyard
def creatureOrGyCreatureCard : TargetSpec := single { domain := .creatureOrGyCreatureCard, count := .upTo 1 }
def spellOrCreature : TargetSpec := ofDomain .spellOrCreature
def permanentOrPlayer : TargetSpec := ofDomain .permanentOrPlayer
def stackAbilityFromSource (ty : CardType) : TargetSpec := ofDomain (.stackAbility .you (.hasType ty))

def twoNonlandsSharingType : TargetSpec :=
  single {
    domain := .nonland
    count := .exact 2
    groupConstraint? := some (.shareCharacteristic .cardType)
  }

def twoCreaturesOrLandsYouControl : TargetSpec :=
  single { domain := .creatureOrLandYouControl, count := .exact 2 }

def twoPlayers : TargetSpec :=
  single { domain := .anyPlayer, count := .exact 2 }

def twoArtifactsYouControl : TargetSpec :=
  ofSlots #[.of .artifactYouControl, .of .artifactYouControl]
    #[{ slots := #[0, 1], relation := .distinct }]

def upToTwoCreaturesTotalMvAtMost (n : Nat) : TargetSpec :=
  single {
    domain := .creature
    count := .upTo 2
    groupConstraint? := some (.totalManaValueAtMost (.const n))
  }

def playerThenCreature : TargetSpec :=
  ofSlots #[.of .anyPlayer, .of .creature]

def creatureYouControlThenOppCreature : TargetSpec :=
  ofSlots #[.of .creatureYouControl, .of .oppCreature]

def oppCreatureThenUpToOneCreatureYouControl : TargetSpec :=
  ofSlots #[.of .oppCreature, { domain := .creatureYouControl, count := .upTo 1 }]

def equipmentYouControlThenCreatureYouControl : TargetSpec :=
  ofSlots #[.of .equipmentYouControl, { domain := .creatureYouControl, count := .upTo 1 }]

def upToOneEquipmentThenCreatureYouControl : TargetSpec :=
  ofSlots #[{ domain := .equipmentYouControl, count := .upTo 1 }, .of .creatureYouControl]

def upToOneCreatureThenPlayer : TargetSpec :=
  ofSlots #[{ domain := .creature, count := .upTo 1 }, .of .anyPlayer]

def creatureYouControlThenOppCreatureOrPlaneswalker : TargetSpec :=
  ofSlots #[.of .creatureYouControl, .of .oppCreatureOrPlaneswalker]

def planeswalkerYouControlThenOppCreatureOrPlaneswalker : TargetSpec :=
  ofSlots #[.of .planeswalkerYouControl, .of .oppCreatureOrPlaneswalker]

/-- `"for each opponent, up to one target <pred> that player controls"` (CR 601.2c). -/
def forEachOpponentControlled (pred : ObjectPred) (count : CountRange := .upTo 1) : TargetSpec :=
  single {
    domain := .object .battlefield (ObjectPred.andAll #[pred, .controlledBy .opponent])
    count
    forEach? := some .opponent
  }

/-- `"for each player, up to one target <pred> that player controls"` (CR 601.2c). -/
def forEachPlayerControlled (pred : ObjectPred) (count : CountRange := .upTo 1) : TargetSpec :=
  single {
    domain := .object .battlefield (ObjectPred.andAll #[pred, .controlledBy .thatPlayer])
    count
    forEach? := some .any
  }

end TargetSpec

/-! ### `HasTargeting` -/

/-- Types that carry a `TargetSpec`. `targetCount`, `maxTargetCount`,
`allowsZeroTargets`, and `requiresTarget` derive here directly so spell,
ability, and trigger wrappers do not restate them. -/
class HasTargeting (α : Type) where
  targetSpec : α → TargetSpec

namespace HasTargeting
variable {α : Type} [HasTargeting α]

def targetCount (e : α) : Nat := targetSpec e |>.targetCount
def maxTargetCount (e : α) : Nat := targetSpec e |>.maxTargetCount
def allowsZeroTargets (e : α) : Bool := targetSpec e |>.allowsZero
def requiresTarget (e : α) : Bool := !(targetSpec e).isEmpty

end HasTargeting

end Mtg.Engine
