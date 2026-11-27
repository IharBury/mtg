import Mtg.Engine.Card.Expr

/-!
# Compositional Cost Specifications (Layer 2 — CR 118, 601.2b/f/h, 602.2b, 606.2–6)

Unified, compositional `CostSpec` / `CostItem` AST for activation, additional,
alternative, trigger-payment, and ward costs, anchored to the 6 November 2026
Comprehensive Rules:

- `LoyaltySymbol` (CR 107.7 / 606.2 / 606.4–6)
- `CostCountSpec`, `SelfOrFilter`, `DiscardCostTarget`, `CounterCostTarget`
- `CostItem` (15 constructors, lowering to `EventCause.costPayment` + `CostKind`)
- `CostSpec` (items + optional `bindVar? : Option VarId` for step outcomes)
- `AdditionalCostSpec` and `AlternativeCostSpec` (CR 118.8 / 118.9)
- Functorial Layer 3 `HasTextChange` and canonical `ToOracle` / `ToString`

Every `inductive` in this module stays at ≤ 15 constructors (`< 7%` of the
Lean 4 C runtime `LeanMaxCtorTag = 243` ceiling).
-/

namespace Mtg.Engine

/-- A loyalty symbol in an activation cost (CR 107.7 / 606.2 / 606.4–6).

`[+N]` puts N loyalty counters on the source, `[-N]` removes N, and `[0]`
puts zero. `[+X]` and `[-X]` use X in place of a fixed number (CR 107.3a). -/
inductive LoyaltySymbol where
  | plus (n : Nat)
  | minus (n : Nat)
  | zero
  | plusX
  | minusX
deriving DecidableEq, Repr, Inhabited, BEq

namespace LoyaltySymbol

/-- Rules notation: `[+N]`, `[-N]`, `[0]`, `[+X]`, or `[-X]`. -/
def toNotation : LoyaltySymbol → String
  | .plus n => s!"[+{n}]"
  | .minus n => s!"[-{n}]"
  | .zero => "[0]"
  | .plusX => "[+X]"
  | .minusX => "[-X]"

/-- Counters this symbol adds, or removes when negative.
`[+X]` and `[-X]` are not a fixed number. -/
def counters : LoyaltySymbol → Option Int
  | .plus n => some (Int.ofNat n)
  | .minus n => some (-Int.ofNat n)
  | .zero => some 0
  | .plusX | .minusX => none

/-- Net loyalty counter delta for `chosenX` (CR 606.4–5). -/
def netDelta (sym : LoyaltySymbol) (chosenX : Nat) : Int :=
  match sym with
  | .plus n => Int.ofNat n
  | .minus n => -Int.ofNat n
  | .zero => 0
  | .plusX => Int.ofNat chosenX
  | .minusX => -Int.ofNat chosenX

/-- True when this symbol involves `X` (CR 107.3a). -/
def hasX : LoyaltySymbol → Bool
  | .plusX | .minusX => true
  | _ => false

instance : ToString LoyaltySymbol := ⟨toNotation⟩
instance : ToOracle LoyaltySymbol := ⟨fun _ => toNotation⟩

end LoyaltySymbol

/-- Quantity or aggregate threshold required by an object-based cost item
(CR 118.3 / 701.59 / 702.122 / 702.194). -/
inductive CostCountSpec where
  /-- Exactly `n` objects (evaluated via `ValueExpr`). -/
  | count (n : ValueExpr)
  /-- Any number (`0` or more; `X` when bound) of matching objects. -/
  | anyNumber
  /-- Any number of matching objects with total power at least `n`
  (Crew CR 702.122a / Teamwork CR 702.194a). -/
  | totalPowerAtLeast (n : ValueExpr)
  /-- Any number of matching objects with total mana value at least `n`
  (Collect Evidence CR 701.59). -/
  | totalManaValueAtLeast (n : ValueExpr)
  /-- Any number of matching objects with at least `n` mana symbols of `color?`
  among their mana costs. -/
  | totalManaSymbolsAtLeast (color? : Option Color) (n : ValueExpr)
deriving Repr, Inhabited, BEq

namespace CostCountSpec

/-- Fixed natural count `n`. -/
def exact (n : Nat) : CostCountSpec := .count (.const n)

/-- Extract a constant natural count when `self` is `.count (.const k)` with `k ≥ 0`. -/
def fixedNat? : CostCountSpec → Option Nat
  | .count (.const k) => if k ≥ 0 then some k.toNat else none
  | _ => none

end CostCountSpec

instance : HasTextChange CostCountSpec where
  applyTextChanges tcs c :=
    if tcs.isEmpty then c
    else
      match c with
      | .count n => .count (HasTextChange.applyTextChanges tcs n)
      | .anyNumber => .anyNumber
      | .totalPowerAtLeast n => .totalPowerAtLeast (HasTextChange.applyTextChanges tcs n)
      | .totalManaValueAtLeast n => .totalManaValueAtLeast (HasTextChange.applyTextChanges tcs n)
      | .totalManaSymbolsAtLeast col? n =>
        .totalManaSymbolsAtLeast (HasTextChange.applyTextChanges tcs col?)
          (HasTextChange.applyTextChanges tcs n)

/-- Whether a cost acts on the source object itself or on chosen object(s)
matching an `ObjectPred` (CR 118.3). -/
inductive SelfOrFilter where
  | self
  | filter (pred : ObjectPred)
deriving Repr, Inhabited, BEq

instance : HasTextChange SelfOrFilter where
  applyTextChanges tcs
    | .self => .self
    | .filter pred => .filter (HasTextChange.applyTextChanges tcs pred)

/-- Which card(s) a discard cost discards (CR 701.9 / 702.29). -/
inductive DiscardCostTarget where
  | self
  | hand
  | random
  | matching (pred : ObjectPred)
deriving Repr, Inhabited, BEq

instance : HasTextChange DiscardCostTarget where
  applyTextChanges tcs
    | .self => .self
    | .hand => .hand
    | .random => .random
    | .matching pred => .matching (HasTextChange.applyTextChanges tcs pred)

/-- Recipient of counters placed as a cost (CR 118.3 / 122.1 / 702.21). -/
inductive CounterCostTarget where
  | self
  | filter (pred : ObjectPred)
  | payer
deriving Repr, Inhabited, BEq

instance : HasTextChange CounterCostTarget where
  applyTextChanges tcs
    | .self => .self
    | .filter pred => .filter (HasTextChange.applyTextChanges tcs pred)
    | .payer => .payer

mutual

/-- One atomic or choice-combinator item inside a `CostSpec` (CR 118, 15 constructors).
Lowers during payment to `EventCause.costPayment` + `RulesEvent`. -/
inductive CostItem where
  /-- Mana cost (CR 118.3 / 202.1). -/
  | mana (cost : ManaCost)
  /-- Loyalty symbol `[+N]`, `[-N]`, `[0]`, `[+X]`, `[-X]` (CR 606.2 / 606.4–6). -/
  | loyalty (sym : LoyaltySymbol)
  /-- `{T}` tap this permanent (CR 118.3 / 701.26). -/
  | tapSelf
  /-- `{Q}` untap this permanent (CR 118.3 / 701.26). -/
  | untapSelf
  /-- Tap chosen untapped permanent(s) matching `filter` (incl. Crew CR 702.122 / Teamwork CR 702.194). -/
  | tapObjects (count : CostCountSpec) (filter : ObjectPred)
  /-- Pay `amount` life (CR 118.3b / 119.4). -/
  | payLife (amount : ValueExpr)
  /-- Sacrifice this permanent or matching permanent(s) (CR 701.21). -/
  | sacrifice (count : CostCountSpec) (what : SelfOrFilter)
  /-- Discard this card or card(s) from hand (CR 701.9 / 702.29). -/
  | discard (count : CostCountSpec) (what : DiscardCostTarget)
  /-- Exile this object or card(s)/permanent(s) from `zones` (incl. Collect Evidence CR 701.59). -/
  | exile (count : CostCountSpec) (zones : ZoneSetSpec) (what : SelfOrFilter)
      (isCollectEvidence : Bool := false)
  /-- Remove counters from this permanent or matching permanent(s) (CR 122.1). -/
  | removeCounters (count : CostCountSpec) (kind? : Option CounterKind) (fromObj : SelfOrFilter)
  /-- Put counters on this permanent, matching permanent(s), or the paying player (e.g. stun / poison; CR 122.1). -/
  | putCounters (count : ValueExpr) (kind : CounterKind) (target : CounterCostTarget := .self)
  /-- Return permanent(s) to their owners' hands (e.g. Sneak CR 702.190a). -/
  | returnToHand (count : CostCountSpec) (what : SelfOrFilter)
  /-- Behold a permanent/card of `subtype` (CR 701.4). -/
  | behold (subtype : CardSubtype)
  /-- Waterbend `{amount}` (CR 701.67). -/
  | waterbend (amount : ValueExpr)
  /-- Choice combinator: pay any one of `choices` (CR 118.8 / 601.2b). -/
  | or (choices : Array CostSpec)

/-- Compositional cost specification (CR 118 / 601.2b,f,h / 602.2b).
Optionally binds paid objects/amounts to `bindVar?` so resolving effects can
query them via `ValueExpr.stepMetric` / `ObjectExpr.stepObjects`. -/
structure CostSpec where
  items : Array CostItem := #[]
  bindVar? : Option VarId := none

end

instance : Inhabited CostItem := ⟨.tapSelf⟩
instance : Inhabited CostSpec := ⟨{}⟩

-- Derive the 2-way mutual `BEq` and `Repr` tuple once and project per-type instances.
deriving instance BEq, Repr for CostItem

instance : BEq CostSpec := ⟨instBEqCostItem.beq_2⟩
instance : Repr CostSpec := ⟨instReprCostItem.repr_2⟩

mutual

private partial def applyTcCostItem (tcs : Array TextChange) : CostItem → CostItem
  | .mana c => .mana c
  | .loyalty s => .loyalty s
  | .tapSelf => .tapSelf
  | .untapSelf => .untapSelf
  | .tapObjects cnt f =>
    .tapObjects (HasTextChange.applyTextChanges tcs cnt) (HasTextChange.applyTextChanges tcs f)
  | .payLife amt => .payLife (HasTextChange.applyTextChanges tcs amt)
  | .sacrifice cnt w =>
    .sacrifice (HasTextChange.applyTextChanges tcs cnt) (HasTextChange.applyTextChanges tcs w)
  | .discard cnt w =>
    .discard (HasTextChange.applyTextChanges tcs cnt) (HasTextChange.applyTextChanges tcs w)
  | .exile cnt z w ce =>
    .exile (HasTextChange.applyTextChanges tcs cnt) (HasTextChange.applyTextChanges tcs z)
      (HasTextChange.applyTextChanges tcs w) ce
  | .removeCounters cnt k f =>
    .removeCounters (HasTextChange.applyTextChanges tcs cnt) k (HasTextChange.applyTextChanges tcs f)
  | .putCounters cnt k t =>
    .putCounters (HasTextChange.applyTextChanges tcs cnt) k (HasTextChange.applyTextChanges tcs t)
  | .returnToHand cnt w =>
    .returnToHand (HasTextChange.applyTextChanges tcs cnt) (HasTextChange.applyTextChanges tcs w)
  | .behold s => .behold (HasTextChange.applyTextChanges tcs s)
  | .waterbend amt => .waterbend (HasTextChange.applyTextChanges tcs amt)
  | .or cs => .or (cs.map (applyTcCostSpec tcs))

private partial def applyTcCostSpec (tcs : Array TextChange) (spec : CostSpec) : CostSpec :=
  if tcs.isEmpty then spec
  else { spec with items := spec.items.map (applyTcCostItem tcs) }

end

instance : HasTextChange CostItem where
  applyTextChanges tcs item := if tcs.isEmpty then item else applyTcCostItem tcs item

instance : HasTextChange CostSpec := ⟨applyTcCostSpec⟩

namespace CostItem

/-- Primary `CostKind` lowered into `EventCause.costPayment` for this item
(CR 118.3 / 601.2h / 602.2b / 606.4). `.or` has no `CostKind` of its own:
the chosen branch emits its items' `CostKind`s. -/
def costKind? : CostItem → Option CostKind
  | .mana _ => some .mana
  | .loyalty _ => some .loyalty
  | .tapSelf => some .tap
  | .untapSelf => some .untap
  | .tapObjects _ _ => some .tap
  | .payLife _ => some .life
  | .sacrifice _ _ => some .sacrifice
  | .discard _ _ => some .discard
  | .exile _ _ _ isCollectEvidence =>
    some (if isCollectEvidence then .collectEvidence else .exile)
  | .removeCounters _ _ _ => some .removeCounters
  | .putCounters _ _ _ => some .putCounters
  | .returnToHand _ _ => some .returnToHand
  | .behold _ => some .behold
  | .waterbend _ => some .waterbend
  | .or _ => none

/-- True when paying this item moves an object to or from a library (CR 605.1a). -/
partial def movesToOrFromLibrary : CostItem → Bool
  | .exile _ zones _ _ => zones.zones.contains .library
  | .or cs => cs.any (fun c => c.items.any movesToOrFromLibrary)
  | _ => false

end CostItem

-- Canonical Oracle printing for `CostItem` / `CostSpec`.

private def renderCostPredNoun (pred : ObjectPred) (plural : Bool) (isCard : Bool)
    (ctx : PrintCtx := {}) : String :=
  -- Recognize standard compact predicates first for crisp Oracle phrasing.
  let has (p : ObjectPred) : Bool :=
    match pred with
    | .all ps => ps.contains p
    | other => other == p
  let flatPreds : Array ObjectPred :=
    match pred with
    | .all ps => ps
    | other => #[other]
  let isOther := flatPreds.contains (.otherThan .this)
  let withoutOther := flatPreds.filter (· != .otherThan .this)
  let stripped : ObjectPred :=
    match withoutOther.toList with
    | [] => .anyObject
    | [p] => p
    | ps => .all ps.toArray
  let baseNoun : String :=
    if stripped == .anyObject then
      if isCard then (if plural then "cards" else "card")
      else (if plural then "permanents" else "permanent")
    else
      match stripped with
      | .hasType t =>
        let w := t.englishName.toLower
        if isCard then (if plural then s!"{w} cards" else s!"{w} card")
        else (if plural then s!"{w}s" else w)
      | .hasSupertype s =>
        let w := s.englishName.toLower
        if isCard then (if plural then s!"{w} cards" else s!"{w} card")
        else (if plural then s!"{w} permanents" else s!"{w} permanent")
      | .hasSubtype (.literal sub) =>
        if plural then pluralizeName sub.englishName else sub.englishName
      | .not (.hasType .land) =>
        if isCard then (if plural then "nonland cards" else "nonland card")
        else (if plural then "nonland permanents" else "nonland permanent")
      | .any #[.hasType .creature, .hasType .artifact] =>
        if plural then "creatures or artifacts" else "creature or artifact"
      | .any #[.hasType .artifact, .hasType .creature] =>
        if plural then "artifacts or creatures" else "artifact or creature"
      | .any #[.hasType .creature, .hasType .planeswalker] =>
        if plural then "creatures or planeswalkers" else "creature or planeswalker"
      | .any #[.hasType .artifact, .hasType .land] =>
        if plural then "artifacts or lands" else "artifact or land"
      | .any #[.hasType .enchantment, .hasType .instant, .hasType .sorcery] =>
        if isCard then "enchantment, instant, or sorcery card"
        else "enchantment, instant, or sorcery"
      | .all #[.hasSupertype .legendary, .hasType .artifact] =>
        if plural then "legendary artifacts" else "legendary artifact"
      | .all #[.hasSupertype .legendary, .any #[.hasType .artifact, .hasType .creature]] =>
        "legendary artifact or legendary creature"
      | .all #[.hasSubtype (.literal .equipment), .attachedTo .this] =>
        "Equipment attached to this"
      | .all #[.hasType .creature, .tapped false, .controlledBy .you] =>
        if plural then "untapped creatures you control" else "untapped creature you control"
      | .all #[.hasType .artifact, .tapped false, .controlledBy .you] =>
        if plural then "untapped artifacts you control" else "untapped artifact you control"
      | .all #[.hasType .creature, .isKind .card] =>
        if plural then "creature cards" else "creature card"
      | .all #[.hasSupertype .legendary, .shares .name (.inZones .battlefield (.all #[.hasSupertype .legendary, .controlledBy .you]))] =>
        "legendary card with the same name as a legendary permanent you control"
      | _ =>
        let rendered := ToOracle.toOracle { ctx with capitalize := false } stripped
        if plural then rendered else rendered
  if isOther then
    if plural then s!"other {baseNoun}" else s!"another {baseNoun}"
  else
    let _ := has
    baseNoun

private def renderCountedNoun (cnt : CostCountSpec) (pred : ObjectPred) (isCard : Bool)
    (ctx : PrintCtx := {}) : String :=
  match cnt with
  | .count (.const 1) =>
    let noun := renderCostPredNoun pred false isCard ctx
    if noun.startsWith "another " then noun
    else s!"{indefinite noun} {noun}"
  | .count (.const n) =>
    let k := n.toNat
    let noun := renderCostPredNoun pred (k != 1) isCard ctx
    if k == 1 then
      if noun.startsWith "another " then noun else s!"{indefinite noun} {noun}"
    else
      s!"{englishNumber k} {noun}"
  | .count e =>
    let noun := renderCostPredNoun pred true isCard ctx
    s!"{ToOracle.toOracle { ctx with capitalize := false } e} {noun}"
  | .anyNumber =>
    let noun := renderCostPredNoun pred true isCard ctx
    s!"any number of {noun}"
  | .totalPowerAtLeast n =>
    let noun := renderCostPredNoun pred true isCard ctx
    s!"any number of {noun} with total power {ToOracle.toOracle { ctx with capitalize := false } n} or more"
  | .totalManaValueAtLeast n =>
    let noun := renderCostPredNoun pred true isCard ctx
    s!"any number of {noun} with total mana value {ToOracle.toOracle { ctx with capitalize := false } n} or more"
  | .totalManaSymbolsAtLeast col? n =>
    let noun := renderCostPredNoun pred true isCard ctx
    let colStr := match col? with | some c => s!"{c.englishName} " | none => ""
    s!"any number of {noun} with {ToOracle.toOracle { ctx with capitalize := false } n} or more {colStr}mana symbols among their mana costs"

private def renderCounterCount (cnt : CostCountSpec) (kind? : Option CounterKind) : String :=
  match cnt, kind? with
  | .count (.const 1), some k => k.countersPhrase 1
  | .count (.const n), some k => k.countersPhrase n.toNat
  | .anyNumber, some k => s!"any number of {k.oracleName} counters"
  | .anyNumber, none => "any number of counters"
  | .count (.const 1), none => "a counter"
  | .count (.const n), none => s!"{englishNumber n.toNat} counters"
  | .count e, some k => s!"{ToOracle.toOracle {} e} {k.oracleName} counters"
  | .count e, none => s!"{ToOracle.toOracle {} e} counters"
  | _, some k => s!"{k.oracleName} counters"
  | _, none => "counters"

mutual

/-- Render one `CostItem` in canonical Oracle wording. -/
partial def renderCostItem (ctx : PrintCtx) (item : CostItem) : String :=
  let raw :=
    match item with
    | .mana m => toString m
    | .loyalty sym => sym.toNotation
    | .tapSelf => "{T}"
    | .untapSelf => "{Q}"
    | .tapObjects cnt pred => s!"tap {renderCountedNoun cnt pred false ctx}"
    | .payLife (.const n) => s!"pay {n} life"
    | .payLife e => s!"pay {ToOracle.toOracle { ctx with capitalize := false } e} life"
    | .sacrifice _ .self => "sacrifice this"
    | .sacrifice cnt (.filter pred) => s!"sacrifice {renderCountedNoun cnt pred false ctx}"
    | .discard _ .self => "discard this card"
    | .discard (.count (.const 1)) .hand => "discard a card"
    | .discard (.count (.const n)) .hand => s!"discard {englishNumber n.toNat} cards"
    | .discard cnt .hand => s!"discard {renderCountedNoun cnt .anyObject true ctx}"
    | .discard (.count (.const 1)) .random => "discard a card at random"
    | .discard cnt .random => s!"discard {renderCountedNoun cnt .anyObject true ctx} at random"
    | .discard cnt (.matching pred) => s!"discard {renderCountedNoun cnt pred true ctx}"
    | .exile _ zones .self _ =>
      if zones.zones == #[.graveyard] then "exile this card from your graveyard"
      else if zones.zones == #[.hand] then "exile this card from your hand"
      else if zones.zones == #[.stack] then "exile this spell"
      else "exile this permanent"
    | .exile cnt zones (.filter pred) isCollectEvidence =>
      if isCollectEvidence then
        match cnt with
        | .totalManaValueAtLeast n => s!"collect evidence {ToOracle.toOracle { ctx with capitalize := false } n}"
        | _ => s!"exile {renderCountedNoun cnt pred true ctx} from your graveyard"
      else
        let fromClause :=
          if zones.zones == #[.graveyard] then " from your graveyard"
          else if zones.zones == #[.hand] then " from your hand"
          else ""
        s!"exile {renderCountedNoun cnt pred (zones.zones != #[.battlefield]) ctx}{fromClause}"
    | .removeCounters cnt kind? .self =>
      s!"remove {renderCounterCount cnt kind?} from this"
    | .removeCounters cnt kind? (.filter pred) =>
      s!"remove {renderCounterCount cnt kind?} from {renderCountedNoun (.exact 1) pred false ctx}"
    | .putCounters (.const n) kind .payer =>
      let phrase :=
        if n == 1 then s!"{indefinite kind.oracleName} {kind.oracleName} counter"
        else s!"{englishNumber n.toNat} {kind.oracleName} counters"
      s!"get {phrase}"
    | .putCounters e kind .payer =>
      s!"get {ToOracle.toOracle { ctx with capitalize := false } e} {kind.oracleName} counters"
    | .putCounters (.const n) kind .self =>
      s!"put {kind.countersPhrase n.toNat} on this"
    | .putCounters e kind .self =>
      s!"put {ToOracle.toOracle { ctx with capitalize := false } e} {kind.oracleName} counters on this"
    | .putCounters (.const n) kind (.filter pred) =>
      s!"put {kind.countersPhrase n.toNat} on {renderCountedNoun (.exact 1) pred false ctx}"
    | .putCounters e kind (.filter pred) =>
      s!"put {ToOracle.toOracle { ctx with capitalize := false } e} {kind.oracleName} counters on {renderCountedNoun (.exact 1) pred false ctx}"
    | .returnToHand _ .self => "return this permanent to its owner's hand"
    | .returnToHand cnt (.filter pred) =>
      s!"return {renderCountedNoun cnt pred false ctx} to its owner's hand"
    | .behold sub => s!"behold {indefinite sub.englishName} {sub.englishName}"
    | .waterbend (.const n) => s!"waterbend \{{n}}"
    | .waterbend e => s!"waterbend {ToOracle.toOracle { ctx with capitalize := false } e}"
    | .or choices =>
      let parts := choices.toList.map fun c =>
        match c.items.toList with
        | [.mana m] => s!"pay {m}"
        | _ => renderCostSpec { ctx with capitalize := false } c
      orJoin parts
  if ctx.capitalize && !raw.startsWith "{" && !raw.startsWith "[" then
    capitalizeAscii raw
  else raw

/-- Render a `CostSpec` in canonical Oracle wording (`{1}, {T}, Pay 2 life`). -/
partial def renderCostSpec (ctx : PrintCtx) (spec : CostSpec) : String :=
  -- Keep `"Sacrifice this and a legendary artifact"` merged when both appear.
  let hasSelfSac := spec.items.any fun
    | .sacrifice _ .self => true
    | _ => false
  let hasLegArtSac := spec.items.any fun
    | .sacrifice (.count (.const 1)) (.filter (.all #[.hasSupertype .legendary, .hasType .artifact])) => true
    | _ => false
  let parts : List String :=
    if hasSelfSac && hasLegArtSac then
      let merged := if ctx.capitalize then "Sacrifice this and a legendary artifact"
                    else "sacrifice this and a legendary artifact"
      let rest := spec.items.toList.filter fun
        | .sacrifice _ .self => false
        | .sacrifice (.count (.const 1)) (.filter (.all #[.hasSupertype .legendary, .hasType .artifact])) => false
        | _ => true
      rest.map (renderCostItem ctx) ++ [merged]
    else
      spec.items.toList.map (renderCostItem ctx)
  String.intercalate ", " parts

end

instance : ToOracle CostItem := ⟨renderCostItem⟩
instance : ToOracle CostSpec := ⟨renderCostSpec⟩

namespace CostSpec

def empty : CostSpec := {}

def isEmpty (c : CostSpec) : Bool := c.items.isEmpty

def ofItem (item : CostItem) : CostSpec := { items := #[item] }

def ofItems (items : Array CostItem) : CostSpec := { items := items }

def ofMana (m : ManaCost) : CostSpec :=
  if m.symbols.isEmpty then {} else { items := #[.mana m] }

def ofGeneric (n : Nat) : CostSpec :=
  ofMana (ManaCost.ofGeneric n)

def ofLoyalty (sym : LoyaltySymbol) : CostSpec :=
  { items := #[.loyalty sym] }

def append (a b : CostSpec) : CostSpec :=
  { items := a.items ++ b.items, bindVar? := a.bindVar?.orElse fun _ => b.bindVar? }

/-- Canonical Oracle notation (capitalized items joined by `", "`, e.g. `"{1}, {T}"`). -/
def toNotation (c : CostSpec) : String :=
  renderCostSpec { capitalize := true } c

/-- Lowercase inline Oracle phrase (e.g. `"discard a card or pay {2}"`). -/
def toInlinePhrase (c : CostSpec) : String :=
  renderCostSpec { capitalize := false } c

instance : ToString CostSpec := ⟨toNotation⟩

/-- Combined `ManaCost` across all `.mana` items in `c`. -/
def manaCost (c : CostSpec) : ManaCost :=
  let syms := c.items.foldl (fun acc item =>
    match item with
    | .mana m => acc ++ m.symbols
    | _ => acc) #[]
  { symbols := syms }

/-- Mana portion of this cost specification. -/
@[inline] def mana (c : CostSpec) : ManaCost := c.manaCost

/-- Replace all `.mana` items in `c` with `m` (omitting if `m` is empty). -/
def withMana (c : CostSpec) (m : ManaCost) : CostSpec :=
  let nonMana := c.items.filter fun | .mana _ => false | _ => true
  let items := if m.symbols.isEmpty then nonMana else #[CostItem.mana m] ++ nonMana
  { c with items }

/-- All loyalty symbols in `c` (CR 606.2 / 606.5). -/
def loyaltySymbols (c : CostSpec) : Array LoyaltySymbol :=
  c.items.filterMap fun
    | .loyalty sym => some sym
    | _ => none

/-- First loyalty symbol in `c`, if any (CR 606.2). -/
def loyalty (c : CostSpec) : Option LoyaltySymbol :=
  c.items.findSome? fun
    | .loyalty sym => some sym
    | _ => none

/-- True when `c` contains a loyalty symbol (CR 606.2). -/
def isLoyalty (c : CostSpec) : Bool :=
  c.items.any fun | .loyalty _ => true | _ => false

/-- CR 606.5: combine every add/remove loyalty cost in `c` into one net delta
(`none` when `c` contains no loyalty symbols). -/
def netLoyaltyDelta (c : CostSpec) (chosenX : Nat := 0) : Option Int :=
  let syms := c.loyaltySymbols
  if syms.isEmpty then none
  else some (syms.foldl (fun acc sym => acc + sym.netDelta chosenX) 0)

/-- True when `c` includes `{T}`. -/
def tap (c : CostSpec) : Bool :=
  c.items.any fun | .tapSelf => true | _ => false

/-- True when `c` includes `{Q}`. -/
def untap (c : CostSpec) : Bool :=
  c.items.any fun | .untapSelf => true | _ => false

/-- Fixed life payment in `c`, summed across constant `.payLife` items (CR 119.4). -/
def payLife (c : CostSpec) : Nat :=
  c.items.foldl (fun acc item =>
    match item with
    | .payLife (.const n) => if n > 0 then acc + n.toNat else acc
    | _ => acc) 0

/-- True when `c` sacrifices the source itself. -/
def sacrificeSource (c : CostSpec) : Bool :=
  c.items.any fun | .sacrifice _ .self => true | _ => false

/-- True when `c` discards the source card itself (CR 702.29). -/
def discardSource (c : CostSpec) : Bool :=
  c.items.any fun | .discard _ .self => true | _ => false

/-- Zone from which `c` exiles the source itself, if any. -/
def exileSourceFrom? (c : CostSpec) : Option ZoneKind :=
  c.items.findSome? fun
    | .exile _ zones .self _ => zones.zones[0]?
    | _ => none

def exileSourceFromGraveyard (c : CostSpec) : Bool :=
  c.items.any fun | .exile _ zones .self _ => zones.zones.contains .graveyard | _ => false

def exileSourceFromHand (c : CostSpec) : Bool :=
  c.items.any fun | .exile _ zones .self _ => zones.zones.contains .hand | _ => false

def exileSourceFromBattlefield (c : CostSpec) : Bool :=
  c.items.any fun | .exile _ zones .self _ => zones.zones.contains .battlefield | _ => false

/-- True when `c` removes a counter of `kind` from the source itself (fixed count 1). -/
def removesCounterFromSelf (c : CostSpec) (kind : CounterKind) : Bool :=
  c.items.any fun
    | .removeCounters (.count (.const 1)) (some k) .self => k == kind
    | _ => false

/-- True when `c` removes any number of `+1/+1` counters from the source itself. -/
def removeAnyNumberPlusOne (c : CostSpec) : Bool :=
  c.items.any fun
    | .removeCounters .anyNumber (some .plusOnePlusOne) .self => true
    | _ => false

def removeIndestructibleCounter (c : CostSpec) : Bool :=
  c.removesCounterFromSelf .indestructible

def removeStoryCounter (c : CostSpec) : Bool :=
  c.removesCounterFromSelf .story

/-- True when `c` puts a stun counter on the source itself. -/
def putStunCounterOnSource (c : CostSpec) : Bool :=
  c.items.any fun
    | .putCounters (.const 1) .stun .self => true
    | _ => false

/-- Crew power requirement if `c` has a Crew tap-total-power item (CR 702.122a). -/
def crewPower? (c : CostSpec) : Option Nat :=
  c.items.findSome? fun
    | .tapObjects (.totalPowerAtLeast (.const n)) _ => if n ≥ 0 then some n.toNat else none
    | _ => none

/-- True when `c` has an exile-mana-symbols cost item (e.g. fifteen black mana symbols). -/
def exileManaSymbols? (c : CostSpec) : Option (Option Color × Nat × ObjectPred) :=
  c.items.findSome? fun
    | .exile (.totalManaSymbolsAtLeast col? (.const n)) _ (.filter pred) _ =>
      if n ≥ 0 then some (col?, n.toNat, pred) else none
    | _ => none

/-- True when `c` contains a `sacrifice` of a legendary artifact. -/
def sacrificeLegendaryArtifact (c : CostSpec) : Bool :=
  c.items.any fun
    | .sacrifice (.count (.const 1)) (.filter (.all #[.hasSupertype .legendary, .hasType .artifact])) => true
    | _ => false

/-- True when `c` contains a `sacrifice` of an Equipment attached to this permanent. -/
def sacrificeEquipmentAttachedToSource (c : CostSpec) : Bool :=
  c.items.any fun
    | .sacrifice (.count (.const 1)) (.filter (.all #[.hasSubtype (.literal .equipment), .attachedTo .this])) => true
    | _ => false

/-- True when `c` contains a `sacrifice` of another creature or artifact. -/
def sacrificeAnotherCreatureOrArtifact (c : CostSpec) : Bool :=
  c.items.any fun
    | .sacrifice (.count (.const 1)) (.filter (.all #[.otherThan .this, .any #[.hasType .creature, .hasType .artifact]])) => true
    | .sacrifice (.count (.const 1)) (.filter (.all #[.otherThan .this, .any #[.hasType .artifact, .hasType .creature]])) => true
    | _ => false

/-- True when paying `c` moves any object to or from a library (CR 605.1a). -/
def movesToOrFromLibrary (c : CostSpec) : Bool :=
  c.items.any CostItem.movesToOrFromLibrary

/-- True when `c` requires paying only mana (single `.mana` item, or empty). -/
def isManaOnly (c : CostSpec) : Bool :=
  c.items.all fun | .mana _ => true | _ => false

/-- If `c` is solely a generic mana cost `{n}`, return `some n`. -/
def soleGenericMana? (c : CostSpec) : Option Nat :=
  match c.items.toList with
  | [.mana { symbols := #[.generic n] }] => some n
  | _ => none

/-- If `c` is a single-item poison-counter payment (`Get N poison counters`), return `some n`. -/
def solePoisonCounters? (c : CostSpec) : Option Nat :=
  match c.items.toList with
  | [.putCounters (.const n) .poison .payer] => if n ≥ 0 then some n.toNat else none
  | _ => none

-- Reusable canonical cost builders (zero card-specific constructors).

def tapOnly : CostSpec := ofItem .tapSelf
def sacSelf : CostSpec := ofItem (.sacrifice (.exact 1) .self)
def discardCard : CostSpec := ofItem (.discard (.exact 1) .hand)
def discardNonland : CostSpec := ofItem (.discard (.exact 1) (.matching (.not (.hasType .land))))
def discardLegendaryCard : CostSpec := ofItem (.discard (.exact 1) (.matching (.hasSupertype .legendary)))
def discardEnchantmentInstantOrSorcery : CostSpec :=
  ofItem (.discard (.exact 1) (.matching (.any #[.hasType .enchantment, .hasType .instant, .hasType .sorcery])))
def discardLegendarySameName : CostSpec :=
  ofItem (.discard (.exact 1) (.matching (.all #[
    .hasSupertype .legendary,
    .shares .name (.inZones .battlefield (.all #[.hasSupertype .legendary, .controlledBy .you]))
  ])))

def sacrificeCreature : CostSpec :=
  ofItem (.sacrifice (.exact 1) (.filter (.hasType .creature)))
def sacrificeAnotherCreature : CostSpec :=
  ofItem (.sacrifice (.exact 1) (.filter (.all #[.otherThan .this, .hasType .creature])))
def sacrificeAnotherSubtype (sub : CardSubtype) : CostSpec :=
  ofItem (.sacrifice (.exact 1) (.filter (.all #[.otherThan .this, .hasSubtype (.literal sub)])))
def sacrificeArtifact : CostSpec :=
  ofItem (.sacrifice (.exact 1) (.filter (.hasType .artifact)))
def sacrificeAnotherArtifact : CostSpec :=
  ofItem (.sacrifice (.exact 1) (.filter (.all #[.otherThan .this, .hasType .artifact])))
def sacrificeLegendaryArtifactSpec : CostSpec :=
  ofItem (.sacrifice (.exact 1) (.filter (.all #[.hasSupertype .legendary, .hasType .artifact])))
def sacrificeLegendaryArtifactOrCreature : CostSpec :=
  ofItem (.sacrifice (.exact 1) (.filter (.all #[.hasSupertype .legendary, .any #[.hasType .artifact, .hasType .creature]])))
def sacrificeArtifactOrCreature : CostSpec :=
  ofItem (.sacrifice (.exact 1) (.filter (.any #[.hasType .artifact, .hasType .creature])))
def sacrificeAnotherCreatureOrArtifactSpec : CostSpec :=
  ofItem (.sacrifice (.exact 1) (.filter (.all #[.otherThan .this, .any #[.hasType .creature, .hasType .artifact]])))
def sacrificeCreatureOrPlaneswalker : CostSpec :=
  ofItem (.sacrifice (.exact 1) (.filter (.any #[.hasType .creature, .hasType .planeswalker])))
def sacrificeAnotherCreatureOrPlaneswalker : CostSpec :=
  ofItem (.sacrifice (.exact 1) (.filter (.all #[.otherThan .this, .any #[.hasType .creature, .hasType .planeswalker]])))
def sacrificeArtifactOrLand : CostSpec :=
  ofItem (.sacrifice (.exact 1) (.filter (.any #[.hasType .artifact, .hasType .land])))
def sacrificeEquipmentAttached : CostSpec :=
  ofItem (.sacrifice (.exact 1) (.filter (.all #[.hasSubtype (.literal .equipment), .attachedTo .this])))
def sacrificePermanents (n : Nat) : CostSpec :=
  ofItem (.sacrifice (.exact n) (.filter .anyObject))

def sacrificeArtifactOrDiscardNonland : CostSpec :=
  ofItem (.or #[sacrificeArtifact, discardNonland])
def sacrificeArtifactOrDiscardCard : CostSpec :=
  ofItem (.or #[sacrificeArtifact, discardCard])
def discardCardOrPayGeneric (n : Nat) : CostSpec :=
  ofItem (.or #[discardCard, ofGeneric n])
def sacrificeArtifactOrCreatureOrPayGeneric (n : Nat) : CostSpec :=
  ofItem (.or #[sacrificeArtifactOrCreature, ofGeneric n])
def sacrificeCreatureOrPlaneswalkerOrPayGeneric (n : Nat) : CostSpec :=
  ofItem (.or #[sacrificeCreatureOrPlaneswalker, ofGeneric n])
def beholdOrPayGeneric (sub : CardSubtype) (n : Nat) : CostSpec :=
  ofItem (.or #[ofItem (.behold sub), ofGeneric n])

def getPoisonCounters (n : Nat) : CostSpec :=
  ofItem (.putCounters (.const n) .poison .payer)

def tapUntappedCreature : CostSpec :=
  ofItem (.tapObjects (.exact 1) (.all #[.hasType .creature, .tapped false, .controlledBy .you]))
def tapTwoUntappedArtifacts : CostSpec :=
  ofItem (.tapObjects (.exact 2) (.all #[.hasType .artifact, .tapped false, .controlledBy .you]))
def exileAnotherCreatureCardFromGraveyard : CostSpec :=
  ofItem (.exile (.exact 1) .yourGraveyard (.filter (.all #[.otherThan .this, .hasType .creature, .isKind .card])))

/-- Crew `n` cost: tap any number of other untapped creatures you control with
total power `n` or more (CR 702.122a). -/
def crewCost (power : Nat) : CostSpec :=
  ofItem (.tapObjects (.totalPowerAtLeast (.const power))
    (.all #[.otherThan .this, .hasType .creature, .tapped false, .controlledBy .you]))

/-- Teamwork `n` optional additional cost: tap any number of untapped creatures
you control with total power `n` or more (CR 702.194a). -/
def teamworkCost (power : Nat) : CostSpec :=
  ofItem (.tapObjects (.totalPowerAtLeast (.const power))
    (.all #[.hasType .creature, .tapped false, .controlledBy .you]))

/-- Exile any number of black cards from your graveyard with `n` or more black
mana symbols among their mana costs. -/
def exileBlackManaSymbols (n : Nat := 15) : CostSpec :=
  ofItem (.exile (.totalManaSymbolsAtLeast (some .black) (.const n)) .yourGraveyard
    (.filter (.all #[.hasColor (.literal .black), .isKind .card])))

/-- Sneak alternative cost: pay `cost` and return an unblocked attacking
creature you control to its owner's hand (CR 702.190a). -/
def sneakFullCost (base : CostSpec) : CostSpec :=
  base.append (ofItem (.returnToHand (.exact 1) (.filter (.all #[
    .hasType .creature, .combatRole .unblocked, .controlledBy .you
  ]))))

end CostSpec

/-- A spell's additional cost specification (CR 118.8 / 601.2b,f,h). -/
structure AdditionalCostSpec where
  cost : CostSpec
  optional : Bool := false
  /-- Optional keyword tag when generated by a keyword (e.g. `.kicker`, `.teamwork`, `.gift`). -/
  keywordTag? : Option ParamKeywordTag := none
deriving Repr, Inhabited, BEq

instance : HasTextChange AdditionalCostSpec where
  applyTextChanges tcs s :=
    if tcs.isEmpty then s else { s with cost := HasTextChange.applyTextChanges tcs s.cost }

namespace AdditionalCostSpec

/-- Mandatory additional cost (printed `"As an additional cost to cast this spell, ..."`). -/
def mandatory (cost : CostSpec) : AdditionalCostSpec :=
  { cost, optional := false }

/-- Optional additional cost (e.g. Kicker CR 702.33a, Teamwork CR 702.194a, Gift CR 702.174a). -/
def opt (cost : CostSpec) (tag? : Option ParamKeywordTag := none) : AdditionalCostSpec :=
  { cost, optional := true, keywordTag? := tag? }

/-- Render `"As an additional cost to cast this spell, ..."` in Oracle wording. -/
def toOracleLine (s : AdditionalCostSpec) : String :=
  if s.optional then
    s!"As an additional cost to cast this spell, you may {s.cost.toInlinePhrase}."
  else
    s!"As an additional cost to cast this spell, {s.cost.toInlinePhrase}."

instance : ToOracle AdditionalCostSpec := ⟨fun _ s => s.toOracleLine⟩
instance : ToString AdditionalCostSpec := ⟨toOracleLine⟩

end AdditionalCostSpec

/-- A spell's alternative cost specification (CR 118.9 / 601.2b,f). -/
structure AlternativeCostSpec where
  cost : CostSpec
  fromZones : Array ZoneKind := #[.hand]
  condition? : Option Condition := none
  /-- Optional keyword tag when generated by a keyword (e.g. `.morph`, `.flashback`, `.impending`, `.sneak`). -/
  keywordTag? : Option ParamKeywordTag := none
  /-- True when casting via this alternative cost casts the card face down as a
  2/2 creature with no text, name, subtypes, or mana cost (Morph CR 702.37a/c). -/
  faceDown : Bool := false
deriving Repr, Inhabited, BEq

instance : HasTextChange AlternativeCostSpec where
  applyTextChanges tcs s :=
    if tcs.isEmpty then s
    else
      { s with
        cost := HasTextChange.applyTextChanges tcs s.cost
        condition? := HasTextChange.applyTextChanges tcs s.condition? }

-- Compile-time guards for `CostSpec` / `CostItem` / `LoyaltySymbol`.
#guard (CostSpec.ofItems #[.loyalty (.plus 1), .loyalty (.minus 4)]).netLoyaltyDelta 0 == some (-3)
#guard (CostSpec.ofItems #[.loyalty .minusX]).netLoyaltyDelta 5 == some (-5)
#guard (CostSpec.ofGeneric 2).soleGenericMana? == some 2
#guard (CostSpec.getPoisonCounters 5).solePoisonCounters? == some 5
#guard CostItem.tapSelf.costKind? == some .tap
#guard (CostItem.exile (.totalManaValueAtLeast (.const 4)) .yourGraveyard (.filter (.isKind .card)) true).costKind? == some .collectEvidence
#guard (CostItem.or #[]).costKind? == none
#guard (HasTextChange.applyTextChanges #[TextChange.replaceCreatureType .goblin .elf]
    (CostSpec.beholdOrPayGeneric .goblin 2)) == CostSpec.beholdOrPayGeneric .elf 2

end Mtg.Engine
