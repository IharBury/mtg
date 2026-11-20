import Mtg.Engine.Card.Cost

/-!
# Parameterized Keyword Abilities (Layer 2 — CR 702, CR 122.1b)

Layer-2 parameterized keyword abilities and keyword counters:

- `SimpleKeyword` (29 unit constructors, CR 702)
- `GiftKind` (CR 702.174d–i), `QualityFilter` (CR 702.11d),
  `ProtectionQuality` (CR 702.16)
- `KeywordAbility` (17 constructors: `.simple` + 16 parameterized keywords)
- `CounterKind.grantedKeyword?` covering all 15 CR 122.1b keyword counters
- Functorial Layer 3 `HasTextChange`, canonical `ToOracle`, and multiplicity-
  preserving array helpers for cumulative keywords (CR 702.21b / 702.83b /
  702.85 / 702.101b / 702.108b / 702.116b / 702.164b).

Non-keyword `"can't be blocked"` (CR 509.1b) is not a CR 702 keyword and lives
on `StaticAbility.cantBeBlocked` / Layer 6 continuous effects.
-/

namespace Mtg.Engine

/-- Parameter-free CR 702 keyword abilities (29 unit constructors). -/
inductive SimpleKeyword where
  /-- CR 702.9 -/
  | flying
  /-- CR 702.7 -/
  | firstStrike
  /-- CR 702.4 -/
  | doubleStrike
  /-- CR 702.2 -/
  | deathtouch
  /-- CR 702.147: can't block; when it attacks, sacrifice it at end of combat. -/
  | decayed
  /-- CR 702.3 -/
  | defender
  /-- CR 702.83: whenever a creature you control attacks alone, it gets +1/+1 until EOT. -/
  | exalted
  /-- CR 702.8 -/
  | flash
  /-- CR 702.10 -/
  | haste
  /-- CR 702.12 -/
  | indestructible
  /-- CR 702.15 -/
  | lifelink
  /-- CR 702.111 -/
  | menace
  /-- CR 702.17 -/
  | reach
  /-- CR 702.19 -/
  | trample
  /-- CR 702.20 -/
  | vigilance
  /-- CR 702.28 -/
  | shadow
  /-- CR 702.73 -/
  | changeling
  /-- CR 702.61 -/
  | splitSecond
  /-- CR 702.51 -/
  | convoke
  /-- CR 702.126 -/
  | improvise
  /-- CR 702.131 -/
  | ascend
  /-- HOB keyword ability granting `PlayerDesignation.enduringStory`. -/
  | storied
  /-- CR 702.145 -/
  | daybound
  /-- CR 702.145 -/
  | nightbound
  /-- CR 702.108 -/
  | prowess
  /-- CR 702.85 -/
  | cascade
  /-- CR 702.116 -/
  | myriad
  /-- CR 702.93 -/
  | undying
  /-- CR 702.101 -/
  | extort
deriving DecidableEq, Repr, Inhabited, BEq

namespace SimpleKeyword

/-- Lowercase Oracle name of `kw`. -/
def oracleName : SimpleKeyword → String
  | .flying => "flying"
  | .firstStrike => "first strike"
  | .doubleStrike => "double strike"
  | .deathtouch => "deathtouch"
  | .decayed => "decayed"
  | .defender => "defender"
  | .exalted => "exalted"
  | .flash => "flash"
  | .haste => "haste"
  | .indestructible => "indestructible"
  | .lifelink => "lifelink"
  | .menace => "menace"
  | .reach => "reach"
  | .trample => "trample"
  | .vigilance => "vigilance"
  | .shadow => "shadow"
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

/-- Every `SimpleKeyword` in canonical display order. -/
def all : List SimpleKeyword := [
  .flash, .haste, .vigilance, .flying, .menace, .indestructible, .reach,
  .trample, .deathtouch, .decayed, .defender, .exalted, .lifelink,
  .firstStrike, .doubleStrike, .storied, .prowess, .ascend, .shadow,
  .changeling, .splitSecond, .convoke, .improvise, .daybound, .nightbound,
  .cascade, .myriad, .undying, .extort
]

/-- Parse a case-insensitive Oracle name into a `SimpleKeyword`. -/
def ofName? (s : String) : Option SimpleKeyword :=
  match s.trimAscii.copy.map Char.toLower with
  | "flying" => some .flying
  | "first strike" => some .firstStrike
  | "double strike" => some .doubleStrike
  | "deathtouch" => some .deathtouch
  | "decayed" => some .decayed
  | "defender" => some .defender
  | "exalted" => some .exalted
  | "flash" => some .flash
  | "haste" => some .haste
  | "indestructible" => some .indestructible
  | "lifelink" => some .lifelink
  | "menace" => some .menace
  | "reach" => some .reach
  | "trample" => some .trample
  | "vigilance" => some .vigilance
  | "shadow" => some .shadow
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
  | _ => none

/-- True when multiple instances of `kw` trigger or apply separately
(CR 702.83b / 702.85 / 702.101b / 702.108b / 702.116b). -/
def isCumulative : SimpleKeyword → Bool
  | .prowess | .cascade | .exalted | .myriad | .extort => true
  | _ => false

/-- Matching Layer-1 `KeywordTag` for `ObjectPred.hasKeyword`. -/
def toTag : SimpleKeyword → KeywordTag
  | .flying => .flying
  | .firstStrike => .firstStrike
  | .doubleStrike => .doubleStrike
  | .deathtouch => .deathtouch
  | .decayed => .decayed
  | .defender => .defender
  | .exalted => .exalted
  | .flash => .flash
  | .haste => .haste
  | .indestructible => .indestructible
  | .lifelink => .lifelink
  | .menace => .menace
  | .reach => .reach
  | .trample => .trample
  | .vigilance => .vigilance
  | .shadow => .shadow
  | .changeling => .changeling
  | .splitSecond => .splitSecond
  | .convoke => .convoke
  | .improvise => .improvise
  | .ascend => .ascend
  | .storied => .storied
  | .daybound => .daybound
  | .nightbound => .nightbound
  | .prowess => .prowess
  | .cascade => .cascade
  | .myriad => .myriad
  | .undying => .undying
  | .extort => .extort

instance : ToString SimpleKeyword := ⟨oracleName⟩
instance : ToOracle SimpleKeyword := ⟨fun ctx kw =>
  if ctx.capitalize then capitalizeAscii kw.oracleName else kw.oracleName⟩

end SimpleKeyword

/-- Gift variants defined by CR 702.174d–i. -/
inductive GiftKind where
  /-- CR 702.174d: Gift a Food. -/
  | food
  /-- CR 702.174e: Gift a card. -/
  | card
  /-- CR 702.174f: Gift a tapped Fish. -/
  | tappedFish
  /-- CR 702.174g: Gift an extra turn. -/
  | extraTurn
  /-- CR 702.174h: Gift a Treasure. -/
  | treasure
  /-- CR 702.174i: Gift an Octopus. -/
  | octopus
deriving DecidableEq, Repr, Inhabited, BEq

namespace GiftKind

def oraclePhrase : GiftKind → String
  | .food => "a Food"
  | .card => "a card"
  | .tappedFish => "a tapped Fish"
  | .extraTurn => "an extra turn"
  | .treasure => "a Treasure"
  | .octopus => "an Octopus"

def ofOracle? (s : String) : Option GiftKind :=
  match s.trimAscii.copy.map Char.toLower with
  | "a food" | "food" => some .food
  | "a card" | "card" => some .card
  | "a tapped fish" | "tapped fish" => some .tappedFish
  | "an extra turn" | "extra turn" => some .extraTurn
  | "a treasure" | "treasure" => some .treasure
  | "an octopus" | "octopus" => some .octopus
  | _ => none

end GiftKind

/-- Quality filter for `"hexproof from [quality]"` (CR 702.11d). -/
inductive QualityFilter where
  | color (c : ColorRef)
  | cardType (t : CardType)
  | subtype (s : SubtypeRef)
  | objectPred (pred : ObjectPred)
  | multicolored
deriving Repr, Inhabited, BEq

instance : HasTextChange QualityFilter where
  applyTextChanges tcs q :=
    if tcs.isEmpty then q
    else
      match q with
      | .color c => .color (HasTextChange.applyTextChanges tcs c)
      | .cardType t => .cardType t
      | .subtype s => .subtype (HasTextChange.applyTextChanges tcs s)
      | .objectPred p => .objectPred (HasTextChange.applyTextChanges tcs p)
      | .multicolored => .multicolored

namespace QualityFilter

def toOraclePhrase (ctx : PrintCtx) : QualityFilter → String
  | .color (.literal c) => c.englishName
  | .color .chosenOnSource => "the chosen color"
  | .color .commanderIdentity => "a color in your commander's color identity"
  | .cardType t => pluralizeName t.englishName.toLower
  | .subtype (.literal s) => pluralizeName s.englishName
  | .subtype .chosenOnSource => "the chosen type"
  | .objectPred p => ToOracle.toOracle { ctx with capitalize := false } p
  | .multicolored => "multicolored"

instance : ToOracle QualityFilter := ⟨toOraclePhrase⟩

end QualityFilter

/-- Quality protected against by `"protection from [quality]"` (CR 702.16). -/
inductive ProtectionQuality where
  | color (c : ColorRef)
  | cardType (t : CardType)
  | chosenCardType
  | subtype (s : SubtypeRef)
  | quality (pred : ObjectPred)
  | everything
  | allColors
  | colorless
deriving Repr, Inhabited, BEq

instance : HasTextChange ProtectionQuality where
  applyTextChanges tcs q :=
    if tcs.isEmpty then q
    else
      match q with
      | .color c => .color (HasTextChange.applyTextChanges tcs c)
      | .cardType t => .cardType t
      | .chosenCardType => .chosenCardType
      | .subtype s => .subtype (HasTextChange.applyTextChanges tcs s)
      | .quality p => .quality (HasTextChange.applyTextChanges tcs p)
      | .everything => .everything
      | .allColors => .allColors
      | .colorless => .colorless

namespace ProtectionQuality

def toOraclePhrase (ctx : PrintCtx) : ProtectionQuality → String
  | .color (.literal c) => c.englishName
  | .color .chosenOnSource => "the chosen color"
  | .color .commanderIdentity => "a color in your commander's color identity"
  | .cardType t => pluralizeName t.englishName.toLower
  | .chosenCardType => "the chosen card type"
  | .subtype (.literal s) => pluralizeName s.englishName
  | .subtype .chosenOnSource => "the chosen type"
  | .quality p => ToOracle.toOracle { ctx with capitalize := false } p
  | .everything => "everything"
  | .allColors => "all colors"
  | .colorless => "colorless"

instance : ToOracle ProtectionQuality := ⟨toOraclePhrase⟩

end ProtectionQuality

/-- Unified, parameterized CR 702 keyword ability (17 constructors: `.simple` +
16 parameterized keywords). Stored as `Array KeywordAbility` on `CardDef`,
`CustomTokenSpec`, `CopyModification`, and Layer 6 `AbilitySet`. -/
inductive KeywordAbility where
  /-- One of the 29 parameter-free CR 702 keywords. -/
  | simple (kw : SimpleKeyword)
  /-- Hexproof or hexproof from `[quality]` (CR 702.11 / 702.11d). -/
  | hexproof (from? : Option QualityFilter := none)
  /-- Ward `[cost]` (CR 702.21). -/
  | ward (cost : CostSpec)
  /-- Protection from `[quality]` (CR 702.16). -/
  | protection (fromQuality : ProtectionQuality)
  /-- `[Land-predicate]walk` (CR 702.14; e.g. Islandwalk = `.hasSubtype (.literal .island)`). -/
  | landwalk (pred : ObjectPred)
  /-- Toxic `n` (CR 702.164). -/
  | toxic (n : Nat)
  /-- Affinity for `[filter]` (CR 702.41). -/
  | affinity (forWhat : ObjectFilter)
  /-- Equip `[filter]` `[cost]` (CR 702.6). -/
  | equip (filter : ObjectPred) (cost : CostSpec)
  /-- Cycling / `[Type]cycling` `[cost]` (CR 702.29). -/
  | cycling (typeFilter? : Option ObjectPred) (cost : CostSpec)
  /-- Kicker `[cost]` (CR 702.33). -/
  | kicker (cost : CostSpec)
  /-- Gift `[kind]` (CR 702.174). -/
  | gift (kind : GiftKind)
  /-- Flashback `[cost]` (CR 702.34). -/
  | flashback (cost : CostSpec)
  /-- Morph `[cost]` (CR 702.37; face-down cast is `{3}`, turn-face-up special action is `cost`). -/
  | morph (cost : CostSpec)
  /-- Impending `counters`—`[cost]` (CR 702.176). -/
  | impending (counters : Nat) (cost : CostSpec)
  /-- Sneak `[cost]` (CR 702.190). -/
  | sneak (cost : CostSpec)
  /-- Crew `power` (CR 702.122). -/
  | crew (power : Nat)
  /-- Teamwork `count` (CR 702.194). -/
  | teamwork (count : Nat)
deriving Repr, Inhabited, BEq

instance : HasTextChange KeywordAbility where
  applyTextChanges tcs kw :=
    if tcs.isEmpty then kw
    else
      match kw with
      | .simple s => .simple s
      | .hexproof f? => .hexproof (f?.map (HasTextChange.applyTextChanges tcs))
      | .ward cost => .ward (HasTextChange.applyTextChanges tcs cost)
      | .protection q => .protection (HasTextChange.applyTextChanges tcs q)
      | .landwalk pred => .landwalk (HasTextChange.applyTextChanges tcs pred)
      | .toxic n => .toxic n
      | .affinity f => .affinity (HasTextChange.applyTextChanges tcs f)
      | .equip f cost =>
        .equip (HasTextChange.applyTextChanges tcs f) (HasTextChange.applyTextChanges tcs cost)
      | .cycling f? cost =>
        .cycling (f?.map (HasTextChange.applyTextChanges tcs))
          (HasTextChange.applyTextChanges tcs cost)
      | .kicker cost => .kicker (HasTextChange.applyTextChanges tcs cost)
      | .gift kind => .gift kind
      | .flashback cost => .flashback (HasTextChange.applyTextChanges tcs cost)
      | .morph cost => .morph (HasTextChange.applyTextChanges tcs cost)
      | .impending n cost => .impending n (HasTextChange.applyTextChanges tcs cost)
      | .sneak cost => .sneak (HasTextChange.applyTextChanges tcs cost)
      | .crew n => .crew n
      | .teamwork n => .teamwork n

/-- All 15 CR 122.1b keyword counters mapped to the `KeywordAbility` they grant
in Layer 6 (CR 613.1f / 613.7c). -/
def CounterKind.grantedKeyword? : CounterKind → Option KeywordAbility
  | .flying => some (.simple .flying)
  | .firstStrike => some (.simple .firstStrike)
  | .doubleStrike => some (.simple .doubleStrike)
  | .deathtouch => some (.simple .deathtouch)
  | .decayed => some (.simple .decayed)
  | .exalted => some (.simple .exalted)
  | .haste => some (.simple .haste)
  | .hexproof => some (.hexproof none)
  | .indestructible => some (.simple .indestructible)
  | .lifelink => some (.simple .lifelink)
  | .menace => some (.simple .menace)
  | .reach => some (.simple .reach)
  | .shadow => some (.simple .shadow)
  | .trample => some (.simple .trample)
  | .vigilance => some (.simple .vigilance)
  | _ => none

/-- Precomputed table of all 15 CR 122.1b `(CounterKind, KeywordAbility)` pairs. -/
def CounterKind.keywordCounters : Array (CounterKind × KeywordAbility) :=
  (CounterKind.all.filterMap fun k => k.grantedKeyword?.map (k, ·)).toArray

#guard CounterKind.keywordCounters.size == 15

namespace KeywordAbility

/-- Canonical `islandwalk` keyword ability (CR 702.14). -/
def islandwalk : KeywordAbility :=
  .landwalk (.hasSubtype (.literal .island))

/-- Landwalk for any land subtype (e.g. `.swamp` → swampwalk, CR 702.14). -/
def subtypeLandwalk (sub : CardSubtype) : KeywordAbility :=
  .landwalk (.hasSubtype (.literal sub))

/-- True when multiple instances of `kw` are cumulative and must retain
multiplicity (CR 702.21b / 702.41b / 702.83b / 702.85 / 702.101b / 702.108b /
702.116b / 702.164b). -/
def isCumulative : KeywordAbility → Bool
  | .simple s => s.isCumulative
  | .ward _ | .toxic _ | .affinity _ => true
  | _ => false

/-- True when `kw` prints inline on a comma-separated keyword line
(e.g. `"Flying, vigilance, hexproof, islandwalk"`). -/
def isInlineKeyword : KeywordAbility → Bool
  | .simple _ => true
  | .hexproof none => true
  | .landwalk (.hasSubtype (.literal _)) => true
  | _ => false

/-- Render `kw` in canonical Oracle wording. -/
def toOracleStr (ctx : PrintCtx) (kw : KeywordAbility) : String :=
  let raw :=
    match kw with
    | .simple s => s.oracleName
    | .hexproof none => "hexproof"
    | .hexproof (some q) => s!"hexproof from {QualityFilter.toOraclePhrase ctx q}"
    | .ward cost =>
      if cost.isManaOnly && !cost.isEmpty then s!"ward {cost.manaCost}"
      else s!"ward—{cost.toNotation}."
    | .protection q => s!"protection from {ProtectionQuality.toOraclePhrase ctx q}"
    | .landwalk (.hasSubtype (.literal sub)) => s!"{sub.englishName.toLower}walk"
    | .landwalk (.all #[.hasType .land, .not (.hasSupertype .basic)]) => "nonbasic landwalk"
    | .landwalk pred => s!"{ToOracle.toOracle { ctx with capitalize := false } pred}walk"
    | .toxic n => s!"toxic {n}"
    | .affinity f =>
      let what :=
        match f.pred with
        | .all #[.hasSubtype (.literal sub), .controlledBy .you]
        | .hasSubtype (.literal sub) => pluralizeName sub.englishName
        | .all #[.hasType t, .controlledBy .you]
        | .hasType t => pluralizeName t.englishName.toLower
        | other => ToOracle.toOracle { ctx with capitalize := false } other
      s!"affinity for {what}"
    | .equip pred cost =>
      let qual :=
        if pred == ObjectPred.all #[.hasType .creature, .controlledBy .you] || pred == .hasType .creature then ""
        else
          match pred with
          | .all #[.hasType .creature, .hasSubtype (.literal sub), .controlledBy .you]
          | .hasSubtype (.literal sub) => s!" {sub.englishName}"
          | _ => s!" {ToOracle.toOracle { ctx with capitalize := false } pred}"
      if cost.isManaOnly && !cost.isEmpty then s!"equip{qual} {cost.manaCost}"
      else s!"equip{qual}—{cost.toNotation}."
    | .cycling none cost =>
      if cost.isManaOnly && !cost.isEmpty then s!"cycling {cost.manaCost}"
      else s!"cycling—{cost.toNotation}."
    | .cycling (some pred) cost =>
      let prefix_ :=
        match pred with
        | .hasSubtype (.literal sub) => sub.englishName.toLower
        | .all #[.hasSupertype .basic, .hasType .land] => "basic land"
        | .hasSupertype s => s.englishName.toLower
        | other => ToOracle.toOracle { ctx with capitalize := false } other
      if cost.isManaOnly && !cost.isEmpty then s!"{prefix_}cycling {cost.manaCost}"
      else s!"{prefix_}cycling—{cost.toNotation}."
    | .kicker cost =>
      if cost.isManaOnly && !cost.isEmpty then s!"kicker {cost.manaCost}"
      else s!"kicker—{cost.toNotation}."
    | .gift kind => s!"gift {kind.oraclePhrase}"
    | .flashback cost =>
      if cost.isManaOnly && !cost.isEmpty then s!"flashback {cost.manaCost}"
      else s!"flashback—{cost.toNotation}."
    | .morph cost =>
      if cost.isManaOnly && !cost.isEmpty then s!"morph {cost.manaCost}"
      else s!"morph—{cost.toNotation}."
    | .impending n cost => s!"impending {n}—{cost.toNotation}"
    | .sneak cost => s!"sneak {cost.toNotation}"
    | .crew n => s!"crew {n}"
    | .teamwork n => s!"teamwork {n}"
  if ctx.capitalize then capitalizeAscii raw else raw

instance : ToOracle KeywordAbility := ⟨toOracleStr⟩
instance : ToString KeywordAbility := ⟨toOracleStr { capitalize := false }⟩

/-- Parse a single lowercase/mixed-case inline keyword name (all 29 `SimpleKeyword`s,
bare `hexproof`, or `<land-subtype>walk` / `nonbasic landwalk`). -/
def ofSimpleName? (s : String) : Option KeywordAbility :=
  let low := s.trimAscii.copy.map Char.toLower
  match SimpleKeyword.ofName? low with
  | some sk => some (.simple sk)
  | none =>
    if low == "hexproof" then some (.hexproof none)
    else if low == "nonbasic landwalk" then
      some (.landwalk (.all #[.hasType .land, .not (.hasSupertype .basic)]))
    else if low.endsWith "walk" && low.length > 4 then
      let stem := (low.dropEnd 4).copy
      match CardSubtype.ofOracle? stem with
      | some sub =>
        if sub.kind == .land then some (.landwalk (.hasSubtype (.literal sub))) else none
      | none => none
    else none

/-- Whether `kw` satisfies a Layer-1 `KeywordTag` test (`ObjectPred.hasKeyword`). -/
def matchesTag (kw : KeywordAbility) (tag : KeywordTag) : Bool :=
  match kw, tag with
  | .simple s, t => s.toTag == t
  | .hexproof _, .hexproof => true
  | .ward _, .ward => true
  | .protection _, .protection => true
  | .landwalk _, .landwalk none => true
  | .landwalk pred, .landwalk (some sub) =>
    match pred with
    | .hasSubtype (.literal s) => s == sub
    | .all ps => ps.contains (.hasSubtype (.literal sub))
    | _ => false
  | .toxic n, .toxic => n > 0
  | .affinity _, .param .affinity => true
  | .equip _ _, .param .equip => true
  | .cycling _ _, .param .cycling => true
  | .kicker _, .param .kicker => true
  | .gift _, .param .gift => true
  | .flashback _, .param .flashback => true
  | .morph _, .param .morph => true
  | .impending _ _, .param .impending => true
  | .sneak _, .param .sneak => true
  | .crew _, .param .crew => true
  | .teamwork _, .param .teamwork => true
  | _, _ => false

/-- Extract the ward `CostSpec`, if `kw` is `.ward`. -/
def wardCost? : KeywordAbility → Option CostSpec
  | .ward c => some c
  | _ => none

/-- Canonical display-sort rank matching traditional Oracle keyword ordering. -/
def displayOrder : KeywordAbility → Nat
  | .simple .flash => 0
  | .simple .haste => 1
  | .simple .vigilance => 2
  | .simple .flying => 3
  | .simple .menace => 4
  | .hexproof _ => 5
  | .simple .indestructible => 6
  | .simple .reach => 7
  | .simple .trample => 8
  | .simple .deathtouch => 9
  | .simple .defender => 10
  | .simple .lifelink => 11
  | .simple .firstStrike => 12
  | .landwalk _ => 13
  | .simple .storied => 14
  | .simple .doubleStrike => 15
  | .simple .prowess => 16
  | .simple .ascend => 17
  | .simple .shadow => 18
  | .simple .changeling => 19
  | .simple .convoke => 20
  | .simple .decayed => 21
  | .simple .exalted => 22
  | .simple .splitSecond => 23
  | .simple .improvise => 24
  | .simple .daybound => 25
  | .simple .nightbound => 26
  | .simple .cascade => 27
  | .simple .myriad => 28
  | .simple .undying => 29
  | .simple .extort => 30
  | .ward _ => 31
  | .protection _ => 32
  | .toxic _ => 33
  | .affinity _ => 34
  | .equip _ _ => 35
  | .cycling _ _ => 36
  | .kicker _ => 37
  | .gift _ => 38
  | .flashback _ => 39
  | .morph _ => 40
  | .impending _ _ => 41
  | .sneak _ => 42
  | .crew _ => 43
  | .teamwork _ => 44

/-- Append `k` to `ks`, retaining multiplicity when `k.isCumulative` and
deduplicating otherwise. -/
def add (ks : Array KeywordAbility) (k : KeywordAbility) : Array KeywordAbility :=
  if k.isCumulative || !ks.contains k then ks.push k else ks

/-- Merge two `Array KeywordAbility` lists, retaining multiplicity for cumulative
keywords and deduplicating non-cumulative keywords. -/
def merge (a b : Array KeywordAbility) : Array KeywordAbility :=
  b.foldl add a

/-- Merge every keyword array in `kss`. -/
def mergeAll (kss : Array (Array KeywordAbility)) : Array KeywordAbility :=
  kss.foldl merge #[]

/-- True when every keyword in `sub` is already present in `sup`. -/
def containsAll (sup sub : Array KeywordAbility) : Bool :=
  sub.all sup.contains

/-- Remove all occurrences of simple keyword `s` from `ks`. -/
def removeSimple (ks : Array KeywordAbility) (s : SimpleKeyword) : Array KeywordAbility :=
  ks.filter (· != .simple s)

/-- True when `ks` contains `.simple s`. -/
@[inline] def hasSimple (ks : Array KeywordAbility) (s : SimpleKeyword) : Bool :=
  ks.contains (.simple s)

/-- Count occurrences of `.simple s` in `ks`. -/
def countSimple (ks : Array KeywordAbility) (s : SimpleKeyword) : Nat :=
  ks.foldl (fun n k => if k == .simple s then n + 1 else n) 0

@[inline] def hasFlying (ks : Array KeywordAbility) : Bool := hasSimple ks .flying
@[inline] def hasFirstStrike (ks : Array KeywordAbility) : Bool := hasSimple ks .firstStrike
@[inline] def hasDoubleStrike (ks : Array KeywordAbility) : Bool := hasSimple ks .doubleStrike
@[inline] def hasDeathtouch (ks : Array KeywordAbility) : Bool := hasSimple ks .deathtouch
@[inline] def hasDecayed (ks : Array KeywordAbility) : Bool := hasSimple ks .decayed
@[inline] def hasDefender (ks : Array KeywordAbility) : Bool := hasSimple ks .defender
@[inline] def hasExalted (ks : Array KeywordAbility) : Bool := hasSimple ks .exalted
@[inline] def hasFlash (ks : Array KeywordAbility) : Bool := hasSimple ks .flash
@[inline] def hasHaste (ks : Array KeywordAbility) : Bool := hasSimple ks .haste
@[inline] def hasIndestructible (ks : Array KeywordAbility) : Bool := hasSimple ks .indestructible
@[inline] def hasLifelink (ks : Array KeywordAbility) : Bool := hasSimple ks .lifelink
@[inline] def hasMenace (ks : Array KeywordAbility) : Bool := hasSimple ks .menace
@[inline] def hasReach (ks : Array KeywordAbility) : Bool := hasSimple ks .reach
@[inline] def hasTrample (ks : Array KeywordAbility) : Bool := hasSimple ks .trample
@[inline] def hasVigilance (ks : Array KeywordAbility) : Bool := hasSimple ks .vigilance
@[inline] def hasShadow (ks : Array KeywordAbility) : Bool := hasSimple ks .shadow
@[inline] def hasChangeling (ks : Array KeywordAbility) : Bool := hasSimple ks .changeling
@[inline] def hasSplitSecond (ks : Array KeywordAbility) : Bool := hasSimple ks .splitSecond
@[inline] def hasConvoke (ks : Array KeywordAbility) : Bool := hasSimple ks .convoke
@[inline] def hasImprovise (ks : Array KeywordAbility) : Bool := hasSimple ks .improvise
@[inline] def hasAscend (ks : Array KeywordAbility) : Bool := hasSimple ks .ascend
@[inline] def hasStoried (ks : Array KeywordAbility) : Bool := hasSimple ks .storied
@[inline] def hasDaybound (ks : Array KeywordAbility) : Bool := hasSimple ks .daybound
@[inline] def hasNightbound (ks : Array KeywordAbility) : Bool := hasSimple ks .nightbound
@[inline] def hasProwess (ks : Array KeywordAbility) : Bool := hasSimple ks .prowess
@[inline] def hasCascade (ks : Array KeywordAbility) : Bool := hasSimple ks .cascade
@[inline] def hasExtort (ks : Array KeywordAbility) : Bool := hasSimple ks .extort

/-- True when `ks` grants unconditional hexproof (CR 702.11). -/
def hasHexproof (ks : Array KeywordAbility) : Bool :=
  ks.any fun | .hexproof none => true | _ => false

/-- True when `ks` grants any hexproof (unconditional or from a quality). -/
def hasAnyHexproof (ks : Array KeywordAbility) : Bool :=
  ks.any fun | .hexproof _ => true | _ => false

/-- True when `ks` contains Islandwalk (`.landwalk (.hasSubtype (.literal .island))`). -/
def hasIslandwalk (ks : Array KeywordAbility) : Bool :=
  ks.any fun | .landwalk (.hasSubtype (.literal .island)) => true | _ => false

/-- All landwalk predicates in `ks` (CR 702.14). -/
def landwalkPreds (ks : Array KeywordAbility) : Array ObjectPred :=
  ks.filterMap fun | .landwalk pred => some pred | _ => none

/-- All ward `CostSpec`s in `ks`, preserving multiplicity (CR 702.21b). -/
def wardCosts (ks : Array KeywordAbility) : Array CostSpec :=
  ks.filterMap wardCost?

/-- Total printed/granted prowess instances in `ks` (CR 702.108b). -/
def prowessCount (ks : Array KeywordAbility) : Nat :=
  countSimple ks .prowess

/-- Total cascade instances in `ks` (CR 702.85). -/
def cascadeCount (ks : Array KeywordAbility) : Nat :=
  countSimple ks .cascade

/-- Total toxic value across all `.toxic n` instances in `ks` (CR 702.164b). -/
def toxicTotal (ks : Array KeywordAbility) : Nat :=
  ks.foldl (fun acc k => match k with | .toxic n => acc + n | _ => acc) 0

/-- True when any keyword in `ks` matches `tag`. -/
def hasTag (ks : Array KeywordAbility) (tag : KeywordTag) : Bool :=
  ks.any (·.matchesTag tag)

/-- Canonical ordered lowercase Oracle names of keywords in `ks`, deduplicating
identical non-cumulative entries while keeping cumulative multiplicity. -/
def toOracleList (ks : Array KeywordAbility) : List String :=
  let sorted := ks.qsort (fun a b => a.displayOrder < b.displayOrder)
  sorted.toList.map (toOracleStr { capitalize := false })

/-- Oracle-style keyword list for ability sentences: one keyword prints as
itself, two join with `and`, more join with commas. -/
def joinedAnd (ks : Array KeywordAbility) : String :=
  match toOracleList ks with
  | [a, b] => s!"{a} and {b}"
  | xs => String.intercalate ", " xs

/-- Comma-separated lowercase summary of `ks` (for `CardDef.summary` / demo rendering). -/
def renderSummary (ks : Array KeywordAbility) : String :=
  let xs := toOracleList ks
  if xs.isEmpty then "" else String.intercalate ", " xs

/-- Full Oracle lines for `renderFullOracle`: inline evergreen keywords share
one comma-separated capitalized line; parameterized keywords print on their own
capitalized lines. -/
def renderOracleLines (ks : Array KeywordAbility) : List String :=
  let (inlineKws, paramKws) := ks.partition isInlineKeyword
  let inlineLine : List String :=
    if inlineKws.isEmpty then []
    else
      let names := (toOracleList inlineKws).map capitalizeAscii
      [String.intercalate ", " names]
  let paramLines : List String :=
    paramKws.toList.map (toOracleStr { capitalize := true })
  inlineLine ++ paramLines

end KeywordAbility

/-!
Singleton `KeywordAbility` constants in `namespace Keyword` so card definitions
and tests stay concise (`#[Keyword.flying, Keyword.haste]`).
-/
namespace Keyword
def flying : KeywordAbility := .simple .flying
def firstStrike : KeywordAbility := .simple .firstStrike
def doubleStrike : KeywordAbility := .simple .doubleStrike
def deathtouch : KeywordAbility := .simple .deathtouch
def decayed : KeywordAbility := .simple .decayed
def defender : KeywordAbility := .simple .defender
def exalted : KeywordAbility := .simple .exalted
def flash : KeywordAbility := .simple .flash
def haste : KeywordAbility := .simple .haste
def hexproof : KeywordAbility := .hexproof none
def indestructible : KeywordAbility := .simple .indestructible
def lifelink : KeywordAbility := .simple .lifelink
def menace : KeywordAbility := .simple .menace
def reach : KeywordAbility := .simple .reach
def trample : KeywordAbility := .simple .trample
def vigilance : KeywordAbility := .simple .vigilance
def shadow : KeywordAbility := .simple .shadow
def changeling : KeywordAbility := .simple .changeling
def splitSecond : KeywordAbility := .simple .splitSecond
def convoke : KeywordAbility := .simple .convoke
def improvise : KeywordAbility := .simple .improvise
def ascend : KeywordAbility := .simple .ascend
def storied : KeywordAbility := .simple .storied
def daybound : KeywordAbility := .simple .daybound
def nightbound : KeywordAbility := .simple .nightbound
def prowess : KeywordAbility := .simple .prowess
def cascade : KeywordAbility := .simple .cascade
def myriad : KeywordAbility := .simple .myriad
def undying : KeywordAbility := .simple .undying
def extort : KeywordAbility := .simple .extort
def islandwalk : KeywordAbility := KeywordAbility.islandwalk
end Keyword

-- Compile-time guards for `KeywordAbility` and `CounterKind.grantedKeyword?`.
#guard KeywordAbility.ofSimpleName? "trample" == some Keyword.trample
#guard KeywordAbility.ofSimpleName? "Flying" == some Keyword.flying
#guard KeywordAbility.ofSimpleName? "islandwalk" == some Keyword.islandwalk
#guard KeywordAbility.ofSimpleName? "swampwalk" == some (KeywordAbility.subtypeLandwalk .swamp)
#guard KeywordAbility.ofSimpleName? "decayed" == some Keyword.decayed
#guard KeywordAbility.ofSimpleName? "exalted" == some Keyword.exalted
#guard (KeywordAbility.ofSimpleName? "can't be blocked").isNone
#guard (KeywordAbility.ofSimpleName? "not a keyword").isNone
#guard KeywordAbility.joinedAnd #[Keyword.trample] == "trample"
#guard KeywordAbility.joinedAnd #[Keyword.trample, Keyword.haste] == "haste and trample"
#guard KeywordAbility.joinedAnd #[Keyword.haste, Keyword.trample, Keyword.flying] ==
  "haste, flying, trample"
#guard (KeywordAbility.merge #[Keyword.prowess] #[Keyword.prowess]).size == 2
#guard (KeywordAbility.merge #[Keyword.flying] #[Keyword.flying]).size == 1
#guard (HasTextChange.applyTextChanges #[TextChange.replaceCreatureType .island .swamp] Keyword.islandwalk) ==
  KeywordAbility.subtypeLandwalk .swamp
#guard CounterKind.grantedKeyword? .decayed == some Keyword.decayed
#guard CounterKind.grantedKeyword? .exalted == some Keyword.exalted
#guard CounterKind.grantedKeyword? .hexproof == some Keyword.hexproof

end Mtg.Engine
