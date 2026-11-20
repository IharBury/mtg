import Mtg.Engine.Card.Cost
import Mtg.Engine.Card.Expr
import Mtg.Engine.Card.Keywords
import Mtg.Engine.Card.ManaSpec
import Mtg.Engine.Card.OracleNorm
import Mtg.Engine.Card.Targeting

/-!
# Stage-4 Compositional Expression, Targeting, Cost & Keyword Sub-Grammars
(CR 107, 109.3, 113, 115, 118, 601.2b/f/h, 602.2b, 603.4, 606.2–6, 611.2, 702)

Compositional Oracle parsers for the Layer-1 expression algebra (`Mtg.Engine.Card.Expr`)
and Layer-2 unified targeting, cost, and keyword specifications (`Mtg.Engine.Card.Targeting`,
`Mtg.Engine.Card.Cost`, `Mtg.Engine.Card.Keywords`):

- `parseNounPhrase` — quantifiers, `target`, status/color/supertype/subtype/type
  modifiers, controller/zone suffixes, `with`/`without` clauses, and `that`
  history/relation clauses into `(NounQuantifier, isTarget, ObjectFilter)`.
- `parseTargetSlot` / `parseTargetSpec` / `parseTargetSpecPrefix` — compositional
  lowering of object, player, CR 115.4 `"any target"`, stack-ability, multi-domain,
  and multi-slot target phrases into `TargetSlot` / `TargetSpec`.
- `parseValueExpr` — constants, `X`, arithmetic combinators, object stats,
  counters, aggregates, Domain/Delirium/subtype counts, devotion/mana symbols,
  and player metrics into `ValueExpr`.
- `parseCondition` — `if`/`as long as`/`unless` conditions, boolean combinators,
  control/existence/comparison checks, designations, cast context, turn history,
  and step/phase/turn/night checks into `Condition`.
- `parseDuration` — timed, turn-anchored, battlefield-anchored, counter-anchored,
  zone-anchored, and indefinite durations into `DurationExpr`.
- `parseCostItem` / `parseCostSpec` / `parseAdditionalCostSpec` — compositional
  lowering of mana, tap/untap, loyalty, life, sacrifice, discard, exile,
  counter, return, tap-objects, behold, waterbend, and `or` choice costs into
  `CostItem` / `CostSpec` / `AdditionalCostSpec`.
- `parseKeywordAbility` / `parseKeywordLine` — compositional lowering of all 29
  `SimpleKeyword`s and 16 parameterized `KeywordAbility` forms (preserving
  multiplicity for cumulative keywords and keeping `"can't be blocked"` out of
  `KeywordAbility`).

These sub-grammars operate on normalized token slices (`Array String`) with
convenient `String` entry points, and round-trip cleanly against `ToOracle`.
-/

namespace Mtg.Engine.Parser

open Mtg.Engine

/-- Quantifier leading an Oracle noun phrase (`parseNounPhrase`). -/
inductive NounQuantifier where
  | singular
  | plural
  | each
  | exact (n : Nat)
  | upTo (n : Nat)
  | between (lo hi : Nat)
  | anyNumber
deriving DecidableEq, Repr, Inhabited, BEq

/-- Result of parsing an Oracle noun phrase into its quantifier, optional
`"target"` marker, and compositional `ObjectFilter`. -/
structure ParsedNounPhrase where
  quantifier : NounQuantifier := .singular
  isTarget : Bool := false
  filter : ObjectFilter
deriving Repr, Inhabited, BEq

/-! ### Tokenization & Basic Helpers -/

private def normalizeQuotes (s : String) : String :=
  s.map fun c =>
    if c == '\u2019' || c == '\u2018' then '\''
    else if c == '\u201C' || c == '\u201D' then '"'
    else c

/-- Clean leading/trailing whitespace and terminal sentence punctuation. -/
private def cleanClause (s : String) : String :=
  let s := (OracleNorm.collapseWs (normalizeQuotes s)).trimAscii.copy
  let rec stripEnd (cs : List Char) : List Char :=
    match cs with
    | '.' :: rest | ',' :: rest | ';' :: rest => stripEnd rest
    | other => other
  (String.ofList (stripEnd s.toList.reverse).reverse).trimAscii.copy

/-- Split a cleaned clause into lowercase-preserving whitespace tokens,
keeping commas as separate tokens only when needed. -/
private def splitWords (s : String) : Array String :=
  let s := cleanClause s
  if s.isEmpty then #[]
  else
    let parts := s.splitOn " " |>.filter (!·.isEmpty)
    parts.toArray

private def lower (s : String) : String :=
  s.map Char.toLower

private def stripTrailingComma (s : String) : String :=
  if s.endsWith "," then (s.take (s.length - 1)).copy else s

/-- Parse an English cardinal number word or ASCII decimal numeral (CR 107.1). -/
def parseNatWord? (raw : String) : Option Nat :=
  match lower (stripTrailingComma raw) with
  | "zero" | "no" => some 0
  | "a" | "an" | "one" => some 1
  | "two" => some 2
  | "three" => some 3
  | "four" => some 4
  | "five" => some 5
  | "six" => some 6
  | "seven" => some 7
  | "eight" => some 8
  | "nine" => some 9
  | "ten" => some 10
  | "eleven" => some 11
  | "twelve" => some 12
  | "thirteen" => some 13
  | "fourteen" => some 14
  | "fifteen" => some 15
  | "sixteen" => some 16
  | "seventeen" => some 17
  | "eighteen" => some 18
  | "nineteen" => some 19
  | "twenty" => some 20
  | s =>
    if !s.isEmpty && s.all Char.isDigit then s.toNat? else none

/-- Parse a signed integer word or ASCII numeral. -/
def parseIntWord? (raw : String) : Option Int :=
  let s := lower (stripTrailingComma raw)
  if s.startsWith "-" then
    let rest := (s.drop 1).copy
    if !rest.isEmpty && rest.all Char.isDigit then
      rest.toNat?.map fun n => -(Int.ofNat n)
    else none
  else
    (parseNatWord? s).map Int.ofNat

/-- Parse an Oracle color word (case-insensitive). -/
def parseColorWord? (raw : String) : Option Color :=
  match lower (stripTrailingComma raw) with
  | "white" => some .white
  | "blue" => some .blue
  | "black" => some .black
  | "red" => some .red
  | "green" => some .green
  | _ => none

/-- Parse a negated Oracle color word (`nonwhite`, `nonblack`, `non-red`, etc.). -/
def parseNonColorWord? (raw : String) : Option Color :=
  let s := lower (stripTrailingComma raw)
  if s.startsWith "non-" then parseColorWord? (s.drop 4).copy
  else if s.startsWith "non" then parseColorWord? (s.drop 3).copy
  else none

/-- Parse a negated card type (`nonland`, `noncreature`, `nonartifact`, etc.). -/
def parseNonCardType? (raw : String) : Option CardType :=
  let s := lower (stripTrailingComma raw)
  if s.startsWith "non-" then CardType.ofOracle? (s.drop 4).copy
  else if s.startsWith "non" then CardType.ofOracle? (s.drop 3).copy
  else none

/-- Parse a negated supertype (`nonbasic`, `nonlegendary`, etc.). -/
def parseNonSupertype? (raw : String) : Option Supertype :=
  let s := lower (stripTrailingComma raw)
  if s.startsWith "non-" then Supertype.ofOracle? (s.drop 4).copy
  else if s.startsWith "non" then Supertype.ofOracle? (s.drop 3).copy
  else none

/-- Parse a negated subtype (`non-Human`, `non-Aura`, `non-Elf`, etc.). -/
def parseNonSubtype? (raw : String) : Option CardSubtype :=
  let s := stripTrailingComma raw
  let low := lower s
  if low.startsWith "non-" then CardSubtype.ofOracle? (s.drop 4).copy
  else none

/-- Parse a `ZoneKind` name from an Oracle zone phrase. -/
def parseZoneKind? (raw : String) : Option ZoneKind :=
  match lower (cleanClause raw) with
  | "battlefield" | "the battlefield" => some .battlefield
  | "graveyard" | "a graveyard" | "graveyards" | "any graveyard" | "your graveyard" => some .graveyard
  | "hand" | "a hand" | "hands" | "your hand" => some .hand
  | "library" | "a library" | "libraries" | "your library" => some .library
  | "stack" | "the stack" => some .stack
  | "exile" | "exiled" => some .exile
  | "command" | "command zone" | "the command zone" => some .command
  | "ante" | "the ante zone" => some .ante
  | "outside the game" => some .outside
  | _ => none

/-- Parse a `StatKind` phrase (singular or plural). -/
def parseStatKind? (raw : String) : Option StatKind :=
  match lower (cleanClause raw) with
  | "power" | "powers" => some .power
  | "toughness" | "toughnesses" => some .toughness
  | "mana value" | "mana values" => some .manaValue
  | "loyalty" | "loyalties" => some .loyalty
  | "defense" | "defenses" => some .defense
  | _ => none

/-- Parse a `Step` from an Oracle step/main-phase name. -/
def parseStep? (raw : String) : Option Step :=
  match lower (cleanClause raw) with
  | "untap" | "untap step" => some .untap
  | "upkeep" | "upkeep step" => some .upkeep
  | "draw" | "draw step" => some .draw
  | "precombat main" | "precombat main phase" | "first main phase" => some .precombatMain
  | "beginning of combat" | "beginning of combat step" => some .beginningOfCombat
  | "declare attackers" | "declare attackers step" => some .declareAttackers
  | "declare blockers" | "declare blockers step" => some .declareBlockers
  | "combat damage" | "combat damage step" => some .combatDamage
  | "end of combat" | "end of combat step" => some .endOfCombat
  | "postcombat main" | "postcombat main phase" | "second main phase" => some .postcombatMain
  | "end" | "end step" => some .end
  | "cleanup" | "cleanup step" => some .cleanup
  | _ => none

/-- Parse a `Phase` from an Oracle phase name. -/
def parsePhase? (raw : String) : Option Phase :=
  match lower (cleanClause raw) with
  | "beginning" | "beginning phase" => some .beginning
  | "precombat main" | "precombat main phase" => some .precombatMain
  | "combat" | "combat phase" => some .combat
  | "postcombat main" | "postcombat main phase" => some .postcombatMain
  | "ending" | "ending phase" => some .ending
  | _ => none

/-- Parse a `StepOrPhase` anchor from an Oracle step or phase name. -/
def parseStepOrPhase? (raw : String) : Option StepOrPhase :=
  let s := lower (cleanClause raw)
  let s := if s.startsWith "the " then (s.drop 4).copy else s
  -- Prefer `.phase` when `"phase"` is explicitly named (except main phases which are both;
  -- check step-only names first, then explicit phase names).
  match s with
  | "beginning phase" => some (.phase .beginning)
  | "combat phase" => some (.phase .combat)
  | "ending phase" => some (.phase .ending)
  | _ =>
    match parseStep? s with
    | some st => some (.step st)
    | none => (parsePhase? s).map StepOrPhase.phase

/-- Strip a case-insensitive prefix `pfx` from `s`, returning the trimmed remainder. -/
private def dropPrefixCI? (s pfx : String) : Option String :=
  if (lower s).startsWith (lower pfx) then
    some ((s.drop pfx.length).trimAscii.copy)
  else none

/-- Strip a case-insensitive suffix `sfx` from `s`, returning the trimmed prefix. -/
private def dropSuffixCI? (s sfx : String) : Option String :=
  if (lower s).endsWith (lower sfx) then
    some ((s.take (s.length - sfx.length)).trimAscii.copy)
  else none

/-- Find the first occurrence of case-insensitive substring `needle` in `haystack`,
splitting `(before, after)` with both trimmed. -/
private def splitFirstCI? (haystack needle : String) : Option (String × String) :=
  let hLow := lower haystack
  let nLow := lower needle
  if nLow.isEmpty || nLow.length > hLow.length then none
  else
    let hArr := hLow.toList.toArray
    let nArr := nLow.toList.toArray
    let origArr := haystack.toList.toArray
    let limit := hArr.size - nArr.size + 1
    Id.run do
      for i in [0:limit] do
        let mut ok := true
        for j in [0:nArr.size] do
          if hArr[i + j]! != nArr[j]! then
            ok := false
            break
        if ok then
          let pre := String.ofList (origArr.extract 0 i).toList |>.trimAscii.copy
          let post := String.ofList (origArr.extract (i + nArr.size) origArr.size).toList |>.trimAscii.copy
          return some (pre, post)
      return none

/-- Find the LAST occurrence of case-insensitive substring `needle` in `haystack`. -/
private def splitLastCI? (haystack needle : String) : Option (String × String) :=
  let hLow := lower haystack
  let nLow := lower needle
  if nLow.isEmpty || nLow.length > hLow.length then none
  else
    let hArr := hLow.toList.toArray
    let nArr := nLow.toList.toArray
    let origArr := haystack.toList.toArray
    let limit := hArr.size - nArr.size + 1
    Id.run do
      let mut found : Option Nat := none
      for i in [0:limit] do
        let mut ok := true
        for j in [0:nArr.size] do
          if hArr[i + j]! != nArr[j]! then
            ok := false
            break
        if ok then found := some i
      match found with
      | none => return none
      | some i =>
        let pre := String.ofList (origArr.extract 0 i).toList |>.trimAscii.copy
        let post := String.ofList (origArr.extract (i + nArr.size) origArr.size).toList |>.trimAscii.copy
        return some (pre, post)

/-- Split `s` on `needle` (case-insensitive) ONLY at parenthesis depth 0. -/
private def splitTopLevelCI? (haystack needle : String) : Option (String × String) :=
  let hLow := lower haystack
  let nLow := lower needle
  if nLow.isEmpty || nLow.length > hLow.length then none
  else
    let hArr := hLow.toList.toArray
    let nArr := nLow.toList.toArray
    let origArr := haystack.toList.toArray
    let limit := hArr.size - nArr.size + 1
    Id.run do
      let mut depth : Nat := 0
      for i in [0:limit] do
        let ch := origArr[i]!
        if ch == '(' then depth := depth + 1
        else if ch == ')' then depth := if depth == 0 then 0 else depth - 1
        if depth == 0 then
          let mut ok := true
          for j in [0:nArr.size] do
            if hArr[i + j]! != nArr[j]! then
              ok := false
              break
          if ok then
            let pre := String.ofList (origArr.extract 0 i).toList |>.trimAscii.copy
            let post := String.ofList (origArr.extract (i + nArr.size) origArr.size).toList |>.trimAscii.copy
            return some (pre, post)
      return none

/-- Parse a `PlayerRelation` / simple `PlayerExpr` from a short Oracle phrase. -/
def parsePlayerExpr? (raw : String) : Option PlayerExpr :=
  let s := lower (cleanClause raw)
  match s with
  | "you" | "your" => some .you
  | "the active player" | "active player" => some .activePlayer
  | "the defending player" | "defending player" => some .defendingPlayer
  | "the monarch" | "monarch" => some .monarch
  | "target player" => some (.target 0)
  | "target opponent" => some (.target 0)
  | "that player" | "they" | "their" => some (.triggerPlayer .actor)
  | "its controller" => some (.triggerPlayer .controllerOfSubject)
  | "its owner" => some (.triggerPlayer .ownerOfSubject)
  | "each opponent" | "opponents" => some (.matching .opponent .any)
  | "each player" | "players" => some (.matching .anyPlayer .any)
  | "each teammate" | "teammates" => some (.matching .teammate .any)
  | _ =>
    if let some pre := dropSuffixCI? s "'s controller" then
      if pre == "target" || pre == "target creature" || pre == "target permanent" then
        some (.controllerOf (.target 0))
      else if pre == "this permanent" || pre == "this creature" || pre == "it" then
        some (.controllerOf .this)
      else if pre == "that object" || pre == "that creature" || pre == "that permanent" then
        some (.controllerOf .triggerSubject)
      else none
    else if let some pre := dropSuffixCI? s "'s owner" then
      if pre == "target" || pre == "target creature" || pre == "target permanent" then
        some (.ownerOf (.target 0))
      else if pre == "this permanent" || pre == "this creature" || pre == "it" then
        some (.ownerOf .this)
      else if pre == "that object" || pre == "that creature" || pre == "that permanent" then
        some (.ownerOf .triggerSubject)
      else none
    else none

/-- Parse a `PlayerFilter` from a short Oracle phrase. -/
def parsePlayerFilter? (raw : String) : Option PlayerFilter :=
  match lower (cleanClause raw) with
  | "you" | "your" => some .you
  | "an opponent" | "opponent" | "opponents" | "each opponent" | "any opponent" => some .opponent
  | "a teammate" | "teammate" | "teammates" | "each teammate" => some .teammate
  | "a player" | "player" | "players" | "each player" | "any player" => some .any
  | _ => none

/-- Parse a simple object reference phrase into an `ObjectExpr`. -/
def parseSimpleObjectExpr? (raw : String) : Option ObjectExpr :=
  let s := lower (cleanClause raw)
  match s with
  | "this" | "this permanent" | "this creature" | "this artifact" | "this enchantment"
  | "this land" | "this planeswalker" | "this spell" | "this card" | "this token"
  | "it" | "~" => some .this
  | "target" | "target permanent" | "target creature" | "target spell" | "target card" =>
    some (.target 0)
  | "enchanted creature" | "equipped creature" | "enchanted permanent"
  | "enchanted or equipped permanent" | "fortified land" => some .attachedHost
  | "that object" | "that creature" | "that permanent" | "that spell" | "that card" =>
    some .triggerSubject
  | "those objects" | "those creatures" | "those cards" | "those permanents" =>
    some (.stepObjects ⟨0⟩)
  | _ => none

/-- Parse a `SubtypeCategory` from phrases like `"planeswalker types"`, `"creature types"`, etc. -/
def parseSubtypeCategory? (raw : String) : Option SubtypeCategory :=
  match lower (cleanClause raw) with
  | "subtypes" => some .any
  | "artifact types" | "artifact subtypes" => some .artifact
  | "enchantment types" | "enchantment subtypes" => some .enchantment
  | "land types" | "land subtypes" => some .land
  | "basic land types" => some .basicLand
  | "planeswalker types" | "planeswalker subtypes" => some .planeswalker
  | "spell types" | "spell subtypes" => some .spell
  | "creature types" | "creature subtypes" => some .creature
  | "planar types" => some .planar
  | "dungeon types" => some .dungeon
  | "battle types" => some .battle
  | _ => none

/-! ### Mutual Stage-4 Sub-Grammars (`parseNounPhrase`, `parseValueExpr`, `parseCondition`, `parseDuration`) -/

mutual

/-- Parse a comparison bound right-hand side (`"4 or greater"`, `"3 or less"`,
`"less than 3"`, `"greater than X"`, `"not equal to 0"`, `"2"`). -/
private partial def parseCmpBound? (raw : String) : Option (CmpOp × ValueExpr) :=
  let s := cleanClause raw
  if let some pre := dropSuffixCI? s " or greater" then
    (parseValueExpr pre).map (.ge, ·)
  else if let some pre := dropSuffixCI? s " or more" then
    (parseValueExpr pre).map (.ge, ·)
  else if let some pre := dropSuffixCI? s " or less" then
    (parseValueExpr pre).map (.le, ·)
  else if let some pre := dropSuffixCI? s " or fewer" then
    (parseValueExpr pre).map (.le, ·)
  else if let some rest := dropPrefixCI? s "greater than " then
    (parseValueExpr rest).map (.gt, ·)
  else if let some rest := dropPrefixCI? s "more than " then
    (parseValueExpr rest).map (.gt, ·)
  else if let some rest := dropPrefixCI? s "less than " then
    (parseValueExpr rest).map (.lt, ·)
  else if let some rest := dropPrefixCI? s "fewer than " then
    (parseValueExpr rest).map (.lt, ·)
  else if let some rest := dropPrefixCI? s "not equal to " then
    (parseValueExpr rest).map (.ne, ·)
  else if let some rest := dropPrefixCI? s "at least " then
    (parseValueExpr rest).map (.ge, ·)
  else if let some rest := dropPrefixCI? s "at most " then
    (parseValueExpr rest).map (.le, ·)
  else if let some rest := dropPrefixCI? s "equal to " then
    (parseValueExpr rest).map (.eq, ·)
  else
    (parseValueExpr s).map (.eq, ·)

/-- Parse a single `"with ..."` predicate atom inside a noun phrase. -/
private partial def parseWithClauseAtom? (raw : String) : Option ObjectPred :=
  let s := cleanClause raw
  let low := lower s
  -- Keyword ("with flying", "with first strike", ...)
  if let some kw := KeywordTag.ofOracle? s then
    some (.hasKeyword kw)
  -- Stat parity ("with odd mana value", "with even power", "with mana value of the chosen quality")
  else if let some rest := dropPrefixCI? s "odd " then
    (parseStatKind? rest).map (.statParity · .odd)
  else if let some rest := dropPrefixCI? s "even " then
    (parseStatKind? rest).map (.statParity · .even)
  else if let some pre := dropSuffixCI? s " of the chosen quality" then
    (parseStatKind? pre).map (.statParity · .chosenOnSource)
  -- Chosen name ("with the chosen name")
  else if low == "the chosen name" then
    some (.named .chosenOnSource)
  -- Stat bounds ("power or toughness 2 or less", "power 4 or greater", "mana value 3 or less", ...)
  else if let some rest := dropPrefixCI? s "power or toughness " then
    (parseCmpBound? rest).map fun (op, v) =>
      .any #[.stat .power op v, .stat .toughness op v]
  else if let some rest := dropPrefixCI? s "mana value " then
    (parseCmpBound? rest).map fun (op, v) => .stat .manaValue op v
  else if let some rest := dropPrefixCI? s "power " then
    (parseCmpBound? rest).map fun (op, v) => .stat .power op v
  else if let some rest := dropPrefixCI? s "toughness " then
    (parseCmpBound? rest).map fun (op, v) => .stat .toughness op v
  else if let some rest := dropPrefixCI? s "loyalty " then
    (parseCmpBound? rest).map fun (op, v) => .stat .loyalty op v
  else if let some rest := dropPrefixCI? s "defense " then
    (parseCmpBound? rest).map fun (op, v) => .stat .defense op v
  -- Counters ("a +1/+1 counter on it", "no counters on it", "a counter on it",
  -- "3 or more lore counters on it", "+1/+1 counter")
  else
    let core := (dropSuffixCI? s " on it").getD ((dropSuffixCI? s " on them").getD s)
    let coreLow := lower core
    if coreLow == "a counter" || coreLow == "one or more counters" then
      some (.counterCount none .ge (.const 1))
    else if coreLow == "no counters" then
      some (.counterCount none .eq (.const 0))
    else if let some pre := dropSuffixCI? core " counters" then
      if let some rest := dropPrefixCI? pre "no " then
        match CounterKind.ofPrefix (splitWords rest).toList with
        | some (k, n) =>
          if n == (splitWords rest).size then some (.counterCount (some k) .eq (.const 0))
          else none
        | none => none
      else
        -- Try splitting `<cmpBound> <counterKind>` or `<cmpBound>` (generic counters)
        let ws := splitWords pre
        let matchedKind? : Option (CounterKind × Nat) :=
          if ws.size ≥ 2 then
            match CounterKind.ofPrefix [lower ws[ws.size - 2]!, lower ws[ws.size - 1]!] with
            | some (k, 2) => some (k, 2)
            | _ =>
              match CounterKind.ofPrefix [lower ws[ws.size - 1]!] with
              | some (k, 1) => some (k, 1)
              | _ => none
          else if ws.size == 1 then
            match CounterKind.ofPrefix [lower ws[0]!] with
            | some (k, 1) => some (k, 1)
            | _ => none
          else none
        match matchedKind? with
        | some (k, kLen) =>
          let boundStr := String.intercalate " " (ws.extract 0 (ws.size - kLen)).toList
          if boundStr.isEmpty then some (.counterCount (some k) .ge (.const 1))
          else (parseCmpBound? boundStr).map fun (op, v) => .counterCount (some k) op v
        | none =>
          (parseCmpBound? pre).map fun (op, v) => .counterCount none op v
    else
      match CounterKind.matchPhrase ((splitWords core).toList.map lower) with
      | some (n, k, consumed) =>
        if consumed == (splitWords core).size then
          some (.counterCount (some k) .ge (.const (Int.ofNat n)))
        else none
      | none =>
        -- Attachment ("<filter> attached to it")
        if let some attStr := dropSuffixCI? s " attached to it" then
          (parseNounPhrase attStr).map fun np => .hasAttachment np.filter
        else none

/-- Parse a `"that ..."` or trailing participial clause on a noun phrase. -/
private partial def parseThatClause? (raw : String) : Option ObjectPred :=
  let s := cleanClause raw
  let low := lower s
  if low == "was cast" || low == "were cast" then some .wasCast
  else if let some zStr := (dropPrefixCI? s "was cast from ").orElse (fun _ => dropPrefixCI? s "were cast from ") then
    (parseZoneKind? zStr).map ObjectPred.castFrom
  else if low == "entered this turn" || low == "entered the battlefield this turn" then
    some .enteredThisTurn
  else if low == "attacked this turn" then
    some .attackedThisTurn
  else if low == "'s attacking alone" || low == "is attacking alone" then
    some (.combatRole .attackingAlone)
  else if low == "dealt damage this turn" then
    some (.dealtDamageThisTurn false none)
  else if low == "dealt combat damage this turn" then
    some (.dealtDamageThisTurn true none)
  else if let some recStr := dropPrefixCI? s "dealt combat damage to " then
    if let some recCore := dropSuffixCI? recStr " this turn" then
      match parsePlayerFilter? recCore with
      | some pf => some (.dealtDamageThisTurn true (some (.player pf)))
      | none =>
        (parseNounPhrase recCore).map fun np => .dealtDamageThisTurn true (some (.object np.filter))
    else none
  else if let some recStr := dropPrefixCI? s "dealt damage to " then
    if let some recCore := dropSuffixCI? recStr " this turn" then
      match parsePlayerFilter? recCore with
      | some pf => some (.dealtDamageThisTurn false (some (.player pf)))
      | none =>
        (parseNounPhrase recCore).map fun np => .dealtDamageThisTurn false (some (.object np.filter))
    else none
  else if low == "'s a copy" || low == "is a copy" || low == "are copies" then some (.isCopy true)
  else if low == "isn't a copy" || low == "is not a copy" || low == "aren't copies" || low == "isnt a copy" then some (.isCopy false)
  else if low == "'s a ring-bearer" || low == "is a ring-bearer" then
    some (.hasDesignation .ringBearer)
  else if low == "'s phased out" || low == "is phased out" || low == "are phased out" then
    some (.phasedOut true)
  else if let some colStr := (dropPrefixCI? s "'s ").orElse (fun _ => dropPrefixCI? s "is ") then
    -- e.g. `"that's green or blue"` / `"that's red or white"`
    let parts := colStr.splitOn " or " |>.map cleanClause |>.filter (!·.isEmpty)
    let cols := parts.filterMap parseColorWord?
    if !cols.isEmpty && cols.length == parts.length then
      some (ObjectPred.orAny (cols.toArray.map fun c => .hasColor (.literal c)))
    else none
  else if let some objStr := (dropPrefixCI? s "shares a color with ").orElse (fun _ => dropPrefixCI? s "share a color with ") then
    (parseObjectExpr? objStr).map (.shares .color)
  else if let some objStr := (dropPrefixCI? s "shares a card type with ").orElse (fun _ => dropPrefixCI? s "share a card type with ") then
    (parseObjectExpr? objStr).map (.shares .cardType)
  else if let some objStr := (dropPrefixCI? s "shares a creature type with ").orElse (fun _ => dropPrefixCI? s "share a creature type with ") then
    (parseObjectExpr? objStr).map (.shares .creatureType)
  else if let some objStr := (dropPrefixCI? s "shares a subtype with ").orElse (fun _ => dropPrefixCI? s "share a subtype with ") then
    (parseObjectExpr? objStr).map (.shares .subtype)
  else if let some tgtStr := (dropPrefixCI? s "targets ").orElse (fun _ => dropPrefixCI? s "target ") then
    match parsePlayerExpr? tgtStr with
    | some p => some (.targets (.player p))
    | none => (parseObjectExpr? tgtStr).map fun o => .targets (.object o)
  else if let some hostStr := (dropPrefixCI? s "is attached to ").orElse (fun _ => dropPrefixCI? s "are attached to ") then
    (parseObjectExpr? hostStr).map ObjectPred.attachedTo
  else if let some innerStr := (dropPrefixCI? s "isn't ").orElse (fun _ => (dropPrefixCI? s "is not ").orElse (fun _ => dropPrefixCI? s "isnt ")) then
    (parseNounPhrase innerStr).map fun np => .not np.filter.pred
  else none

/-- Parse a general `ObjectExpr` (either a simple object reference or a noun phrase). -/
private partial def parseObjectExpr? (raw : String) : Option ObjectExpr :=
  let s := cleanClause raw
  if let some obj := parseSimpleObjectExpr? s then
    some obj
  else if let some rest := dropPrefixCI? s "the top card of " then
    if let some whoStr := dropSuffixCI? rest " library" then
      let whoStr := (dropSuffixCI? whoStr "'s").getD whoStr
      (parsePlayerExpr? whoStr).map fun p => .topOfLibrary p (.const 1)
    else none
  else if let some rest := dropPrefixCI? s "the top " then
    if let some (cntStr, tail) := splitFirstCI? rest " cards of " then
      if let some whoStr := dropSuffixCI? tail " library" then
        let whoStr := (dropSuffixCI? whoStr "'s").getD whoStr
        match parseValueExpr cntStr, parsePlayerExpr? whoStr with
        | some v, some p => some (.topOfLibrary p v)
        | _, _ => none
      else none
    else none
  else if let some (lhs, rhs) := splitFirstCI? s " other than " then
    match parseObjectExpr? lhs, parseObjectExpr? rhs with
    | some a, some b => some (.diff a b)
    | _, _ => none
  else
    (parseNounPhrase s).map fun np => np.filter.toExpr

/-- Stage-4 compositional Oracle noun-phrase parser:
`[quantifier] [another/other] [target] [modifiers] <type/subtype/noun> [controller] [zone] [with/without ...] [that ...]`. -/
partial def parseNounPhrase (raw : String) : Option ParsedNounPhrase := Id.run do
  let mut s := cleanClause raw
  if s.isEmpty then return none

  -- 1. Extract trailing clauses from right to left in any valid MTG Oracle order
  --    (`that ...`, `without ...`, `with ...`, zone suffixes `in/from ...`,
  --    and controller/owner suffixes `you control`, `an opponent controls`, etc.).
  let mut extraPreds : Array ObjectPred := #[]
  let mut ctrlPreds : Array ObjectPred := #[]
  let mut zones : ZoneSetSpec := .battlefield
  let mut explicitZone := false
  let mut progress := true
  while progress do
    progress := false
    -- `that's` / `thats` / `that` clauses
    if let some (lhs, rhs) := splitLastCI? s " that's " then
      if let some p := parseThatClause? s!"'s {rhs}" then
        extraPreds := #[p] ++ extraPreds; s := lhs; progress := true
    if !progress then
      if let some (lhs, rhs) := splitLastCI? s " thats " then
        if let some p := parseThatClause? s!"'s {rhs}" then
          extraPreds := #[p] ++ extraPreds; s := lhs; progress := true
    if !progress then
      if let some (lhs, rhs) := splitLastCI? s " that " then
        if let some p := parseThatClause? rhs then
          extraPreds := #[p] ++ extraPreds; s := lhs; progress := true
    if !progress then
      if let some (lhs, rhs) := splitLastCI? s " attached to " then
        if let some host := parseObjectExpr? rhs then
          extraPreds := #[.attachedTo host] ++ extraPreds; s := lhs; progress := true
    if !progress then
      if let some (lhs, rhs) := splitLastCI? s " named " then
        if !rhs.isEmpty then
          extraPreds := #[.named (.literal rhs)] ++ extraPreds; s := lhs; progress := true
    if !progress then
      if let some pre := dropSuffixCI? s " of the chosen type" then
        extraPreds := #[.hasSubtype .chosenOnSource] ++ extraPreds; s := pre; progress := true
    if !progress then
      if let some pre := dropSuffixCI? s " of the chosen color" then
        extraPreds := #[.hasColor .chosenOnSource] ++ extraPreds; s := pre; progress := true
    if !progress then
      if let some pre := (dropSuffixCI? s " in your commander's color identity").orElse
          (fun _ => dropSuffixCI? s " in your commanders color identity") then
        extraPreds := #[.hasColor .commanderIdentity] ++ extraPreds; s := pre; progress := true
    if !progress then
      if let some pre := dropSuffixCI? s " attacking alone" then
        extraPreds := #[.combatRole .attackingAlone] ++ extraPreds; s := pre; progress := true
    if !progress then
      if let some (lhs, rhs) := splitLastCI? s " attacking " then
        let ll := lower lhs
        if !ll.endsWith " or" && !ll.endsWith "target" && ll != "a" && ll != "an" && ll != "each" then
          if let some who := parsePlayerExpr? rhs then
            extraPreds := #[.combatRole (.attackingPlayer who)] ++ extraPreds; s := lhs; progress := true
    if !progress then
      if let some (lhs, rhs) := splitLastCI? s " blocking " then
        let ll := lower lhs
        if !ll.endsWith " or" && !ll.endsWith "target" && ll != "a" && ll != "an" && ll != "each" then
          if let some atk := parseObjectExpr? rhs then
            extraPreds := #[.combatRole (.blockingObject atk)] ++ extraPreds; s := lhs; progress := true
    -- `without ...` and `with ...` clauses
    if !progress then
      if let some (lhs, rhs) := splitLastCI? s " without " then
        let items := rhs.splitOn " and " |>.map cleanClause |>.filter (!·.isEmpty)
        let mut parsed : Array ObjectPred := #[]
        let mut ok := !items.isEmpty
        for item in items do
          match parseWithClauseAtom? item with
          | some p => parsed := parsed.push (.not p)
          | none => ok := false
        if ok then
          extraPreds := parsed ++ extraPreds; s := lhs; progress := true
    if !progress then
      if let some (lhs, rhs) := splitLastCI? s " with " then
        match parseWithClauseAtom? rhs with
        | some p =>
          extraPreds := #[p] ++ extraPreds; s := lhs; progress := true
        | none =>
          let items := rhs.splitOn " and " |>.map cleanClause |>.filter (!·.isEmpty)
          let mut parsed : Array ObjectPred := #[]
          let mut ok := !items.isEmpty
          for item in items do
            match parseWithClauseAtom? item with
            | some p => parsed := parsed.push p
            | none => ok := false
          if ok then
            extraPreds := parsed ++ extraPreds; s := lhs; progress := true
    -- Zone suffixes (`on the battlefield`, `in/from ... graveyard`, `on the stack`, etc.)
    if !progress && !explicitZone then
      if let some pre := dropSuffixCI? s " on the battlefield" then
        zones := .battlefield; explicitZone := true; s := pre; progress := true
      else if let some pre := dropSuffixCI? s " on the stack" then
        zones := .stack; explicitZone := true; s := pre; progress := true
      else if let some pre := dropSuffixCI? s " in exile" then
        zones := .exile; explicitZone := true; s := pre; progress := true
      else if let some pre := dropSuffixCI? s " in the command zone" then
        zones := .command; explicitZone := true; s := pre; progress := true
      else if let some pre := (dropSuffixCI? s " in your hand or graveyard").orElse
          (fun _ => dropSuffixCI? s " from your hand or graveyard") then
        zones := { zones := #[.hand, .graveyard], owner := .matching .you }
        explicitZone := true; s := pre; progress := true
      else if let some pre := (dropSuffixCI? s " in your graveyard").orElse
          (fun _ => dropSuffixCI? s " from your graveyard") then
        zones := .yourGraveyard; explicitZone := true; s := pre; progress := true
      else if let some pre := (dropSuffixCI? s " in an opponent's graveyard").orElse
          (fun _ => (dropSuffixCI? s " from an opponent's graveyard").orElse
            (fun _ => (dropSuffixCI? s " in an opponents graveyard").orElse
              (fun _ => dropSuffixCI? s " from an opponents graveyard"))) then
        zones := .opponentGraveyard; explicitZone := true; s := pre; progress := true
      else if let some pre := (dropSuffixCI? s " in opponents' graveyards").orElse
          (fun _ => (dropSuffixCI? s " from opponents' graveyards").orElse
            (fun _ => (dropSuffixCI? s " in opponents graveyards").orElse
              (fun _ => dropSuffixCI? s " from opponents graveyards"))) then
        zones := .opponentGraveyard; explicitZone := true; s := pre; progress := true
      else if let some pre := (dropSuffixCI? s " in that player's graveyard").orElse
          (fun _ => dropSuffixCI? s " from that player's graveyard") then
        zones := { zones := #[.graveyard], owner := .matching .thatPlayer }
        explicitZone := true; s := pre; progress := true
      else if let some pre := (dropSuffixCI? s " in a graveyard").orElse
          (fun _ => (dropSuffixCI? s " from a graveyard").orElse
            (fun _ => (dropSuffixCI? s " in any graveyard").orElse
              (fun _ => (dropSuffixCI? s " from any graveyard").orElse
                (fun _ => (dropSuffixCI? s " in graveyards").orElse
                  (fun _ => dropSuffixCI? s " from graveyards"))))) then
        zones := .anyGraveyard; explicitZone := true; s := pre; progress := true
      else if let some pre := (dropSuffixCI? s " in your hand").orElse
          (fun _ => dropSuffixCI? s " from your hand") then
        zones := .yourHand; explicitZone := true; s := pre; progress := true
      else if let some pre := (dropSuffixCI? s " in an opponent's hand").orElse
          (fun _ => dropSuffixCI? s " from an opponent's hand") then
        zones := { zones := #[.hand], owner := .matching .opponent }
        explicitZone := true; s := pre; progress := true
      else if let some pre := (dropSuffixCI? s " in your library").orElse
          (fun _ => dropSuffixCI? s " from your library") then
        zones := .yourLibrary; explicitZone := true; s := pre; progress := true
      else if let some (lhs, rhs) := (splitLastCI? s " in ").orElse (fun _ => splitLastCI? s " from ") then
        if let some (ownerStr, zoneStr) := splitFirstCI? rhs "'s " then
          if let some zk := parseZoneKind? zoneStr then
            if let some pf := parsePlayerFilter? ownerStr then
              zones := { zones := #[zk], owner := .matching pf }
              explicitZone := true; s := lhs; progress := true
            else if let some pe := parsePlayerExpr? ownerStr then
              zones := { zones := #[zk], owner := .ofPlayer pe }
              explicitZone := true; s := lhs; progress := true
    -- Controller / owner suffixes (`you control`, `an opponent controls`, `defending player controls`, ...)
    if !progress && ctrlPreds.isEmpty then
      if let some pre := dropSuffixCI? s " you own and control" then
        ctrlPreds := ctrlPreds.push (.ownedBy .you) |>.push (.controlledBy .you); s := pre; progress := true
      else if let some pre := dropSuffixCI? s " you control" then
        ctrlPreds := ctrlPreds.push (.controlledBy .you); s := pre; progress := true
      else if let some pre := dropSuffixCI? s " an opponent controls" then
        ctrlPreds := ctrlPreds.push (.controlledBy .opponent); s := pre; progress := true
      else if let some pre := dropSuffixCI? s " opponents control" then
        ctrlPreds := ctrlPreds.push (.controlledBy .opponent); s := pre; progress := true
      else if let some pre := dropSuffixCI? s " your opponents control" then
        ctrlPreds := ctrlPreds.push (.controlledBy .opponent); s := pre; progress := true
      else if let some pre := (dropSuffixCI? s " defending player controls").orElse
          (fun _ => dropSuffixCI? s " the defending player controls") then
        ctrlPreds := ctrlPreds.push (.controlledBy .defendingPlayer); s := pre; progress := true
      else if let some pre := dropSuffixCI? s " that player controls" then
        ctrlPreds := ctrlPreds.push (.controlledBy .thatPlayer); s := pre; progress := true
      else if let some pre := dropSuffixCI? s " a teammate controls" then
        ctrlPreds := ctrlPreds.push (.controlledBy .teammate); s := pre; progress := true
      else if let some pre := dropSuffixCI? s " a player controls" then
        ctrlPreds := ctrlPreds.push (.controlledBy .any); s := pre; progress := true
      else if let some pre := dropSuffixCI? s " you own" then
        ctrlPreds := ctrlPreds.push (.ownedBy .you); s := pre; progress := true
      else if let some pre := dropSuffixCI? s " an opponent owns" then
        ctrlPreds := ctrlPreds.push (.ownedBy .opponent); s := pre; progress := true
      else if let some pre := dropSuffixCI? s " opponents own" then
        ctrlPreds := ctrlPreds.push (.ownedBy .opponent); s := pre; progress := true
      else if let some pre := dropSuffixCI? s " that player owns" then
        ctrlPreds := ctrlPreds.push (.ownedBy .thatPlayer); s := pre; progress := true

  -- 2. Parse leading quantifier, optional `another`/`other`, and optional `target`.
  let mut toks := splitWords s
  if toks.isEmpty then return none
  let mut idx : Nat := 0
  let mut quant : NounQuantifier := .singular
  let mut hasExplicitQuant := false
  let w0 := lower toks[0]!
  if w0 == "any" && toks.size ≥ 3 && lower toks[1]! == "number" && lower toks[2]! == "of" then
    quant := .anyNumber; hasExplicitQuant := true; idx := 3
  else if w0 == "up" && toks.size ≥ 3 && lower toks[1]! == "to" then
    match parseNatWord? toks[2]! with
    | some n => quant := .upTo n; hasExplicitQuant := true; idx := 3
    | none => pure ()
  else if (w0 == "one" || w0 == "1") && toks.size ≥ 3 && lower toks[1]! == "or" && lower toks[2]! == "more" then
    quant := .plural; hasExplicitQuant := true; idx := 3
  else if toks.size ≥ 3 && (lower toks[1]! == "or" || lower toks[1]! == "to") &&
      (parseNatWord? toks[0]!).isSome && (parseNatWord? toks[2]!).isSome then
    let lo := (parseNatWord? toks[0]!).get!
    let hi := (parseNatWord? toks[2]!).get!
    if lo ≥ 1 && hi > lo then
      quant := .between lo hi; hasExplicitQuant := true; idx := 3
  else if w0 == "each" then
    quant := .each; hasExplicitQuant := true; idx := 1
  else if w0 == "all" then
    quant := .plural; hasExplicitQuant := true; idx := 1
  else if w0 == "a" || w0 == "an" || w0 == "the" then
    quant := .singular; hasExplicitQuant := true; idx := 1
  else if let some n := parseNatWord? toks[0]! then
    if n ≥ 1 then
      quant := .exact n; hasExplicitQuant := true; idx := 1

  let mut otherBeforeTarget := false
  let mut sawPluralHead := false
  if idx < toks.size && (lower toks[idx]! == "another" || lower toks[idx]! == "other") then
    if idx + 1 < toks.size && lower toks[idx + 1]! == "target" then
      otherBeforeTarget := true
      if lower toks[idx]! == "other" && !hasExplicitQuant then sawPluralHead := true
      idx := idx + 1

  let mut isTarget := false
  if idx < toks.size && lower toks[idx]! == "target" then
    isTarget := true
    idx := idx + 1

  -- 3. Parse modifiers and head noun(s) over `toks[idx..]`.
  let mut preds : Array ObjectPred := #[]
  if otherBeforeTarget then
    preds := preds.push (.otherThan .this)
  let mut colorChoices : Array Color := #[]
  let mut headChoices : Array ObjectPred := #[]
  let mut inOrChain := false
  let mut sawAnyNounOrMod := otherBeforeTarget
  let mut sawSpellHead := false
  let mut sawCardHead := false

  let flushColors (preds : Array ObjectPred) (cs : Array Color) : Array ObjectPred × Array Color :=
    if cs.isEmpty then (preds, cs)
    else (preds.push (ObjectPred.orAny (cs.map fun c => .hasColor (.literal c))), #[])
  let flushHeads (preds : Array ObjectPred) (hs : Array ObjectPred) : Array ObjectPred × Array ObjectPred :=
    if hs.isEmpty then (preds, hs)
    else (preds.push (ObjectPred.orAny hs), #[])

  let nextIsOr (toks : Array String) (i : Nat) : Bool :=
    i < toks.size &&
      (toks[i]!.endsWith "," ||
        (i + 1 < toks.size && (lower toks[i + 1]! == "or" || lower toks[i + 1]! == "and/or")))

  -- Look ahead across comma-stripped Oxford `or`-lists (e.g. normalized `"bear spider or wolf"`,
  -- `"equipment instant or sorcery"`, `"white blue or black"`).
  let colorContinuesOr (toks : Array String) (i : Nat) : Bool := Id.run do
    if nextIsOr toks i then return true
    let mut k := i + 1
    while k < toks.size do
      let w := stripTrailingComma toks[k]!
      let wl := lower w
      if wl == "or" || wl == "and/or" then
        return k + 1 < toks.size && (parseColorWord? (stripTrailingComma toks[k + 1]!)).isSome
      else if (parseColorWord? w).isSome then
        k := k + 1
      else
        return false
    return false

  let isHeadListWord (toks : Array String) (k : Nat) : Nat :=
    if k >= toks.size then 0
    else
      let w := stripTrailingComma toks[k]!
      if (CardType.ofOracle? w).isSome then 1
      else if k + 1 < toks.size &&
          (CardSubtype.ofOracle? s!"{w} {stripTrailingComma toks[k + 1]!}").isSome then 2
      else if (CardSubtype.ofOracle? w).isSome then 1
      else if (Supertype.ofOracle? w).isSome then 1
      else 0

  let headContinuesOr (toks : Array String) (i : Nat) : Bool := Id.run do
    if nextIsOr toks i then return true
    let mut k := i + 1
    while k < toks.size do
      let w := stripTrailingComma toks[k]!
      let wl := lower w
      if wl == "or" || wl == "and/or" then
        if k + 1 >= toks.size then return false
        let nxt := stripTrailingComma toks[k + 1]!
        return isHeadListWord toks (k + 1) > 0 ||
          ((parseNonSubtype? nxt).isSome && k + 2 < toks.size &&
            (CardType.ofOracle? (stripTrailingComma toks[k + 2]!)).isSome) ||
          ((parseNonCardType? nxt).isSome && k + 2 < toks.size &&
            (CardType.ofOracle? (stripTrailingComma toks[k + 2]!)).isSome)
      else
        let step := isHeadListWord toks k
        if step > 0 then k := k + step
        else return false
    return false

  while idx < toks.size do
    let rawTok := stripTrailingComma toks[idx]!
    let tok := lower rawTok
    if tok == "or" || tok == "and/or" then
      inOrChain := true
      idx := idx + 1
    else if let some c := parseColorWord? rawTok then
      (preds, headChoices) := flushHeads preds headChoices
      let continues := inOrChain || !colorChoices.isEmpty || colorContinuesOr toks idx
      if continues then
        colorChoices := colorChoices.push c
        if !colorContinuesOr toks idx then
          (preds, colorChoices) := flushColors preds colorChoices
      else
        preds := preds.push (.hasColor (.literal c))
      inOrChain := false
      sawAnyNounOrMod := true
      idx := idx + 1
    -- `"attacking or blocking"` combat role disjunction
    else if tok == "attacking" && idx + 2 < toks.size &&
        lower toks[idx + 1]! == "or" && lower (stripTrailingComma toks[idx + 2]!) == "blocking" then
      (preds, colorChoices) := flushColors preds colorChoices
      (preds, headChoices) := flushHeads preds headChoices
      preds := preds.push (.any #[.combatRole .attacking, .combatRole .blocking])
      inOrChain := false; sawAnyNounOrMod := true; idx := idx + 3
    -- `"non-Aura enchantment"` inside an `or` chain (`artifact or non-Aura enchantment`)
    else if (inOrChain || !headChoices.isEmpty) && (parseNonSubtype? rawTok).isSome &&
        idx + 1 < toks.size && (CardType.ofOracle? (stripTrailingComma toks[idx + 1]!)).isSome then
      (preds, colorChoices) := flushColors preds colorChoices
      let sub := (parseNonSubtype? rawTok).get!
      let ty := (CardType.ofOracle? (stripTrailingComma toks[idx + 1]!)).get!
      if lower (stripTrailingComma toks[idx + 1]!) == lower ty.pluralName then sawPluralHead := true
      headChoices := headChoices.push (.all #[.not (.hasSubtype (.literal sub)), .hasType ty])
      if !headContinuesOr toks (idx + 1) then
        (preds, headChoices) := flushHeads preds headChoices
      inOrChain := false; sawAnyNounOrMod := true; idx := idx + 2
    -- `"non<type> <type>"` inside an `or` chain (`noncreature artifact or noncreature enchantment`)
    else if (parseNonCardType? rawTok).isSome &&
        idx + 1 < toks.size && (CardType.ofOracle? (stripTrailingComma toks[idx + 1]!)).isSome &&
        (inOrChain || !headChoices.isEmpty ||
          (idx + 3 < toks.size &&
            (lower toks[idx + 2]! == "or" || lower toks[idx + 2]! == "and/or") &&
            (parseNonCardType? (stripTrailingComma toks[idx + 3]!)).isSome)) then
      (preds, colorChoices) := flushColors preds colorChoices
      let neg := (parseNonCardType? rawTok).get!
      let ty := (CardType.ofOracle? (stripTrailingComma toks[idx + 1]!)).get!
      if lower (stripTrailingComma toks[idx + 1]!) == lower ty.pluralName then sawPluralHead := true
      headChoices := headChoices.push (.all #[.not (.hasType neg), .hasType ty])
      if !headContinuesOr toks (idx + 1) then
        (preds, headChoices) := flushHeads preds headChoices
      inOrChain := false; sawAnyNounOrMod := true; idx := idx + 2
    else if let some ty := CardType.ofOracle? rawTok then
      (preds, colorChoices) := flushColors preds colorChoices
      if tok == lower ty.pluralName then sawPluralHead := true
      let continues := inOrChain || !headChoices.isEmpty || headContinuesOr toks idx
      if continues then
        headChoices := headChoices.push (.hasType ty)
        if !headContinuesOr toks idx then
          (preds, headChoices) := flushHeads preds headChoices
      else
        preds := preds.push (.hasType ty)
      inOrChain := false
      sawAnyNounOrMod := true
      idx := idx + 1
    -- Supertype inside an `or` chain (`creature or legendary spell`)
    else if (inOrChain || !headChoices.isEmpty) && (Supertype.ofOracle? rawTok).isSome then
      (preds, colorChoices) := flushColors preds colorChoices
      let sup := (Supertype.ofOracle? rawTok).get!
      headChoices := headChoices.push (.hasSupertype sup)
      if !headContinuesOr toks idx then
        (preds, headChoices) := flushHeads preds headChoices
      inOrChain := false; sawAnyNounOrMod := true; idx := idx + 1
    else
      (preds, colorChoices) := flushColors preds colorChoices
      let isSubtypeHere : Bool :=
        (CardSubtype.ofOracle? rawTok).isSome ||
        (idx + 1 < toks.size &&
          (CardSubtype.ofOracle? s!"{rawTok} {stripTrailingComma toks[idx + 1]!}").isSome)
      if !isSubtypeHere then
        (preds, headChoices) := flushHeads preds headChoices
      if tok == "another" then
        preds := preds.push (.otherThan .this); sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "other" then
        preds := preds.push (.otherThan .this); sawPluralHead := true; sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "tapped" then
        preds := preds.push (.tapped true); sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "untapped" then
        preds := preds.push (.tapped false); sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "attacking" then
        preds := preds.push (.combatRole .attacking); sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "blocking" then
        preds := preds.push (.combatRole .blocking); sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "blocked" then
        preds := preds.push (.combatRole .blocked); sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "unblocked" then
        preds := preds.push (.combatRole .unblocked); sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "face-down" then
        preds := preds.push (.isFaceDown true); sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "face-up" then
        preds := preds.push (.isFaceDown false); sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "token" || tok == "tokens" then
        if tok == "tokens" then sawPluralHead := true
        preds := preds.push (.isToken true); sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "nontoken" then
        preds := preds.push (.isToken false); sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "commander" then
        preds := preds.push .isCommander; sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "goaded" then
        preds := preds.push (.hasDesignation .goaded); sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "prepared" then
        preds := preds.push (.hasDesignation .prepared); sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "harnessed" then
        preds := preds.push (.hasDesignation .harnessed); sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "colorless" then
        preds := preds.push (.colorCount .eq 0); sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "monocolored" then
        preds := preds.push (.colorCount .eq 1); sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "multicolored" then
        preds := preds.push (.colorCount .ge 2); sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "historic" then
        preds := preds.push ObjectPred.historic; sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "storied" then
        preds := preds.push ObjectPred.storied; sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "worthy" then
        preds := preds.push ObjectPred.worthy; sawAnyNounOrMod := true
        if idx + 1 < toks.size &&
            (lower (stripTrailingComma toks[idx + 1]!) == "creature" ||
             lower (stripTrailingComma toks[idx + 1]!) == "creatures") then
          if lower (stripTrailingComma toks[idx + 1]!) == "creatures" then sawPluralHead := true
          idx := idx + 2
        else
          idx := idx + 1
      else if tok == "permanent" && idx + 1 < toks.size &&
          (lower (stripTrailingComma toks[idx + 1]!) == "card" ||
           lower (stripTrailingComma toks[idx + 1]!) == "cards") then
        let nextW := lower (stripTrailingComma toks[idx + 1]!)
        if nextW == "cards" then sawPluralHead := true
        preds := preds.push (.isKind .permanentCard)
        sawCardHead := true; sawAnyNounOrMod := true; idx := idx + 2
      else if tok == "permanent" || tok == "permanents" then
        if tok == "permanents" then sawPluralHead := true
        sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "spell" || tok == "spells" then
        if tok == "spells" then sawPluralHead := true
        preds := preds.push (.isKind .spell)
        sawSpellHead := true; sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "card" || tok == "cards" then
        if tok == "cards" then sawPluralHead := true
        preds := preds.push (.isKind .card)
        sawCardHead := true; sawAnyNounOrMod := true; idx := idx + 1
      else if let some c := parseNonColorWord? rawTok then
        preds := preds.push (.not (.hasColor (.literal c))); sawAnyNounOrMod := true; idx := idx + 1
      else if let some sup := Supertype.ofOracle? rawTok then
        preds := preds.push (.hasSupertype sup); sawAnyNounOrMod := true; idx := idx + 1
      else if let some sup := parseNonSupertype? rawTok then
        preds := preds.push (.not (.hasSupertype sup)); sawAnyNounOrMod := true; idx := idx + 1
      else if let some ty := parseNonCardType? rawTok then
        preds := preds.push (.not (.hasType ty)); sawAnyNounOrMod := true; idx := idx + 1
      else if tok.startsWith "non-" && idx + 1 < toks.size &&
          (CardSubtype.ofOracle? s!"{(rawTok.drop 4).copy} {stripTrailingComma toks[idx + 1]!}").isSome then
        let sub := (CardSubtype.ofOracle? s!"{(rawTok.drop 4).copy} {stripTrailingComma toks[idx + 1]!}").get!
        preds := preds.push (.not (.hasSubtype (.literal sub))); sawAnyNounOrMod := true; idx := idx + 2
      else if let some sub := parseNonSubtype? rawTok then
        preds := preds.push (.not (.hasSubtype (.literal sub))); sawAnyNounOrMod := true; idx := idx + 1
      else
        let twoWord? : Option CardSubtype :=
          if idx + 1 < toks.size then
            CardSubtype.ofOracle? s!"{rawTok} {stripTrailingComma toks[idx + 1]!}"
          else none
        match twoWord? with
        | some sub =>
          let twoRaw := lower s!"{rawTok} {stripTrailingComma toks[idx + 1]!}"
          if twoRaw == lower sub.pluralName && twoRaw != lower sub.englishName then
            sawPluralHead := true
          let hasMore := headContinuesOr toks (idx + 1)
          if inOrChain || hasMore || !headChoices.isEmpty then
            headChoices := headChoices.push (.hasSubtype (.literal sub))
            if !hasMore then
              (preds, headChoices) := flushHeads preds headChoices
          else
            preds := preds.push (.hasSubtype (.literal sub))
          inOrChain := false; sawAnyNounOrMod := true; idx := idx + 2
        | none =>
          match CardSubtype.ofOracle? rawTok with
          | some sub =>
            if tok == lower sub.pluralName && tok != lower sub.englishName then
              sawPluralHead := true
            let hasMore := headContinuesOr toks idx
            if inOrChain || hasMore || !headChoices.isEmpty then
              headChoices := headChoices.push (.hasSubtype (.literal sub))
              if !hasMore then
                (preds, headChoices) := flushHeads preds headChoices
            else
              preds := preds.push (.hasSubtype (.literal sub))
            inOrChain := false; sawAnyNounOrMod := true; idx := idx + 1
          | none =>
            return none

  if !sawAnyNounOrMod then return none

  (preds, colorChoices) := flushColors preds colorChoices
  (preds, headChoices) := flushHeads preds headChoices

  if !explicitZone && sawSpellHead then
    zones := .stack
  else if !explicitZone && sawCardHead && ctrlPreds.isEmpty then
    zones := .battlefield

  let allPreds := preds ++ ctrlPreds ++ extraPreds
  let finalQuant :=
    if !hasExplicitQuant && sawPluralHead then .plural else quant
  return some {
    quantifier := finalQuant
    isTarget
    filter := { zones, pred := ObjectPred.andAll allPreds }
  }

/-- Stage-4 compositional Oracle value-expression parser (`ValueExpr`). -/
partial def parseValueExpr (raw : String) : Option ValueExpr := Id.run do
  let mut s := cleanClause raw
  if s.isEmpty then return none

  -- Optional leading connectors ("where X is ...", "equal to ...").
  if let some rest := dropPrefixCI? s "where x is " then s := rest
  else if let some rest := dropPrefixCI? s "equal to " then s := rest

  let low := lower s
  -- Variable X and literal integers.
  if low == "x" then return some .chosenX
  if let some n := parseIntWord? s then return some (.const n)

  -- Prefix unary / binary combinators.
  if let some rest := dropPrefixCI? s "twice " then
    return (parseValueExpr rest).map fun v => .binary .mul (.const 2) v
  if let some rest := dropPrefixCI? s "half " then
    if let some inner := (dropSuffixCI? rest ", rounded up").orElse (fun _ => dropSuffixCI? rest " rounded up") then
      return (parseValueExpr inner).map fun v => .binary .divFloor (.binary .add v (.const 1)) (.const 2)
    let inner := (dropSuffixCI? rest ", rounded down").getD
      ((dropSuffixCI? rest " rounded down").getD rest)
    return (parseValueExpr inner).map fun v => .binary .divFloor v (.const 2)
  if let some rest := dropPrefixCI? s "the greater of " then
    if let some (a, b) := splitFirstCI? rest " and " then
      match parseValueExpr a, parseValueExpr b with
      | some va, some vb => return some (.binary .max va vb)
      | _, _ => pure ()
  if let some rest := dropPrefixCI? s "the lesser of " then
    if let some (a, b) := splitFirstCI? rest " and " then
      match parseValueExpr a, parseValueExpr b with
      | some va, some vb => return some (.binary .min va vb)
      | _, _ => pure ()

  -- Infix arithmetic (`plus`, `minus`, `times`, `divided by`).
  if let some (a, b) := splitLastCI? s " plus " then
    match parseValueExpr a, parseValueExpr b with
    | some va, some vb => return some (.binary .add va vb)
    | _, _ => pure ()
  if let some (a, b) := splitLastCI? s " minus " then
    match parseValueExpr a, parseValueExpr b with
    | some va, some vb => return some (.binary .sub va vb)
    | _, _ => pure ()
  if let some (a, b) := splitLastCI? s " times " then
    match parseValueExpr a, parseValueExpr b with
    | some va, some vb => return some (.binary .mul va vb)
    | _, _ => pure ()
  if let some (a, b) := splitLastCI? s " divided by " then
    let b' := (dropSuffixCI? b ", rounded down").getD
      ((dropSuffixCI? b " rounded down").getD b)
    match parseValueExpr a, parseValueExpr b' with
    | some va, some vb => return some (.binary .divFloor va vb)
    | _, _ => pure ()

  -- Step-outcome phrases (`the number of cards moved this way`, etc.).
  if low == "the number of cards moved this way" then
    return some (.stepMetric .movedCount ⟨0⟩)
  if low == "the number of tokens created this way" then
    return some (.stepMetric .createdCount ⟨0⟩)
  if low == "the amount of damage dealt this way" then
    return some (.stepMetric .damageDealt ⟨0⟩)
  if low == "the excess damage dealt this way" then
    return some (.stepMetric .excessDamage ⟨0⟩)
  if low == "that much life" then
    return some (.stepMetric .lifeChanged ⟨0⟩)
  if low == "the number of counters modified this way" then
    return some (.stepMetric .countersChanged ⟨0⟩)
  if low == "the total power of creatures affected this way" then
    return some (.stepMetric .sumPower ⟨0⟩)
  if low == "the chosen number" then
    return some (.stepMetric .chosenNumber ⟨0⟩)

  -- Devotion shorthand (`your devotion to <color>`).
  if let some colStr := dropPrefixCI? s "your devotion to " then
    if let some c := parseColorWord? colStr then
      return some (.manaSymbols (some c) (.inZones .battlefield (.controlledBy .you)))

  -- Player metrics (`your life total`, `the number of cards in your hand`, etc.).
  if let some pre := dropSuffixCI? s " life total" then
    let whoStr := (dropSuffixCI? pre "'s").getD pre
    if let some who := parsePlayerExpr? whoStr then
      return some (.playerMetric .life who)
  if let some rest := dropPrefixCI? s "the number of cards in " then
    if let some whoPre := dropSuffixCI? rest " hand" then
      let whoStr := (dropSuffixCI? whoPre "'s").getD whoPre
      if let some who := parsePlayerExpr? whoStr then
        return some (.playerMetric .handSize who)
    if let some whoPre := dropSuffixCI? rest " library" then
      let whoStr := (dropSuffixCI? whoPre "'s").getD whoPre
      if let some who := parsePlayerExpr? whoStr then
        return some (.playerMetric .librarySize who)
    if let some whoPre := dropSuffixCI? rest " graveyard" then
      let whoStr := (dropSuffixCI? whoPre "'s").getD whoPre
      if let some who := parsePlayerExpr? whoStr then
        return some (.playerMetric .graveyardSize who)
  if low == "the number of lands you've played this turn" then
    return some (.playerMetric .landsPlayedThisTurn .you)
  if low == "the number of spells you've cast this turn" then
    return some (.playerMetric .spellsCastThisTurn .you)
  if low == "the number of cards you've drawn this turn" then
    return some (.playerMetric .cardsDrawnThisTurn .you)
  if low == "the amount of life you gained this turn" then
    return some (.playerMetric .lifeGainedThisTurn .you)
  if low == "the amount of life you lost this turn" then
    return some (.playerMetric .lifeLostThisTurn .you)
  if low == "the amount of unspent mana you have" then
    return some (.playerMetric .unspentMana .you)
  if low == "the number of poison counters you have" then
    return some (.playerMetric .poisonCounters .you)
  if low == "the number of opponents you have" then
    return some (.playerMetric .opponentsCount .you)
  if let some rest := dropPrefixCI? s "the amount of life " then
    if let some whoStr := dropSuffixCI? rest " gained this turn" then
      if let some who := parsePlayerExpr? whoStr then
        return some (.playerMetric .lifeGainedThisTurn who)
    if let some whoStr := dropSuffixCI? rest " lost this turn" then
      if let some who := parsePlayerExpr? whoStr then
        return some (.playerMetric .lifeLostThisTurn who)

  -- Mana symbols (`the number of [<color>] mana symbols in the mana costs of <objs>`).
  if let some rest := dropPrefixCI? s "the number of " then
    if let some (pre, objStr) := splitFirstCI? rest "mana symbols in the mana costs of " then
      if let some objs := parseObjectExpr? objStr then
        if pre.isEmpty then return some (.manaSymbols none objs)
        else if let some c := parseColorWord? pre then return some (.manaSymbols (some c) objs)

  -- Domain / Delirium / subtype counts (`the number of basic land types among <objs>`, etc.).
  if let some rest := dropPrefixCI? s "the number of basic land types among " then
    return (parseObjectExpr? rest).map ValueExpr.basicLandTypeCount
  if let some rest := dropPrefixCI? s "the number of card types among " then
    return (parseObjectExpr? rest).map ValueExpr.cardTypeCount
  if let some rest := dropPrefixCI? s "the number of different " then
    if let some (statStr, objStr) := splitFirstCI? rest " among " then
      match parseStatKind? statStr, parseObjectExpr? objStr with
      | some sk, some objs => return some (.aggregate .countDistinct (.stat sk) objs)
      | _, _ => pure ()
  if let some rest := dropPrefixCI? s "the number of " then
    if let some (catStr, objStr) := splitFirstCI? rest " among " then
      if let some cat := parseSubtypeCategory? catStr then
        if let some objs := parseObjectExpr? objStr then
          return some (.subtypeCount cat objs)

  -- Counters (`the number of [<kind>] counters on <obj>`).
  if let some rest := dropPrefixCI? s "the number of counters on " then
    return (parseObjectExpr? rest).map (.counterCount none)
  if let some rest := dropPrefixCI? s "the number of " then
    if let some (kindStr, objStr) := splitFirstCI? rest " counters on " then
      let ws := (splitWords kindStr).toList.map lower
      match CounterKind.ofPrefix ws, parseObjectExpr? objStr with
      | some (k, n), some obj =>
        if n == ws.length then return some (.counterCount (some k) obj)
      | _, _ => pure ()

  -- Aggregates (`the total <stat> of`, `the greatest/least <stat> among`, `the number of`, `for each`).
  if let some rest := dropPrefixCI? s "the total " then
    if let some (statStr, objStr) := splitFirstCI? rest " of " then
      match parseStatKind? statStr, parseObjectExpr? objStr with
      | some sk, some objs => return some (.aggregate .sum (.stat sk) objs)
      | _, _ => pure ()
  if let some rest := dropPrefixCI? s "the greatest " then
    if let some (statStr, objStr) := splitFirstCI? rest " among " then
      match parseStatKind? statStr, parseObjectExpr? objStr with
      | some sk, some objs => return some (.aggregate .max (.stat sk) objs)
      | _, _ => pure ()
  if let some rest := dropPrefixCI? s "the least " then
    if let some (statStr, objStr) := splitFirstCI? rest " among " then
      match parseStatKind? statStr, parseObjectExpr? objStr with
      | some sk, some objs => return some (.aggregate .min (.stat sk) objs)
      | _, _ => pure ()
  if let some rest := dropPrefixCI? s "the number of " then
    return (parseObjectExpr? rest).map fun objs => .aggregate .count .one objs
  if let some rest := dropPrefixCI? s "for each " then
    return (parseObjectExpr? rest).map fun objs => .aggregate .count .one objs

  -- Object stats (`<obj>'s <stat>` or `its <stat>`).
  if let some rest := dropPrefixCI? s "its " then
    if let some sk := parseStatKind? rest then
      return some (.objectStat sk .this)
  if let some (objStr, statStr) := splitLastCI? s "'s " then
    match parseObjectExpr? objStr, parseStatKind? statStr with
    | some obj, some sk => return some (.objectStat sk obj)
    | _, _ => pure ()

  return none

/-- Parse a turn-history condition clause ending in `"this turn"` or `"last turn"`. -/
private partial def parseTurnHistory? (raw : String) : Option EventHistoryPred := Id.run do
  let s := cleanClause raw
  let low := lower s
  if low == "you've scried this turn" || low == "you scried this turn" then
    return some (.scriedThisTurn .you)
  if low == "you've surveilled this turn" || low == "you surveilled this turn" then
    return some (.surveilledThisTurn .you)
  if let some pre := dropSuffixCI? s " scried this turn" then
    if let some pf := parsePlayerFilter? pre then return some (.scriedThisTurn pf)
  if let some pre := dropSuffixCI? s " surveilled this turn" then
    if let some pf := parsePlayerFilter? pre then return some (.surveilledThisTurn pf)

  let (body, isLastTurn) ←
    match dropSuffixCI? s " last turn" with
    | some b => (b, true)
    | none =>
      match dropSuffixCI? s " this turn" with
      | some b => (b, false)
      | none => return none
  let wrap (who : PlayerFilter) (pat : EventPattern) : EventHistoryPred :=
    if isLastTurn then .eventOccurredLastTurn who pat else .eventOccurredThisTurn who pat

  if let some npStr := dropSuffixCI? body " died" then
    return (parseNounPhrase npStr).map fun np => wrap .any (.permanentDied np.filter.pred)
  if let some npStr := dropSuffixCI? body " left the battlefield" then
    return (parseNounPhrase npStr).map fun np => wrap .any (.permanentLeftBattlefield np.filter.pred)
  if let some (npStr, underStr) := splitFirstCI? body " entered under " then
    let whoStr := (dropSuffixCI? underStr "'s control").getD
      ((dropSuffixCI? underStr " control").getD underStr)
    match parseNounPhrase npStr, parsePlayerFilter? whoStr with
    | some np, some pf => return some (wrap pf (.permanentEntered np.filter.pred))
    | _, _ => pure ()
  if let some (npStr, underStr) := splitFirstCI? body " entered the battlefield under " then
    let whoStr := (dropSuffixCI? underStr "'s control").getD
      ((dropSuffixCI? underStr " control").getD underStr)
    match parseNounPhrase npStr, parsePlayerFilter? whoStr with
    | some np, some pf => return some (wrap pf (.permanentEntered np.filter.pred))
    | _, _ => pure ()
  if let some npStr := dropSuffixCI? body " entered the battlefield" then
    return (parseNounPhrase npStr).map fun np => wrap .any (.permanentEntered np.filter.pred)
  if let some npStr := dropSuffixCI? body " entered" then
    return (parseNounPhrase npStr).map fun np => wrap .any (.permanentEntered np.filter.pred)

  if let some (whoStr, npStr) := splitFirstCI? body " attacked with " then
    match parsePlayerFilter? whoStr, parseNounPhrase npStr with
    | some pf, some np => return some (wrap pf (.attackedWith np.filter.pred))
    | _, _ => pure ()
  if let some whoStr := dropSuffixCI? body " attacked" then
    if let some pf := parsePlayerFilter? whoStr then
      return some (wrap pf (.attackedWith .anyObject))

  if let some (whoStr, npStr) := splitFirstCI? body " cast " then
    match parsePlayerFilter? whoStr, parseNounPhrase npStr with
    | some pf, some np => return some (wrap pf (.castSpell np.filter.pred))
    | _, _ => pure ()

  if let some (whoStr, rest) := splitFirstCI? body " drew " then
    if let some pf := parsePlayerFilter? whoStr then
      let rl := lower rest
      if rl == "a card" then return some (wrap pf (.drewCard 1))
      if let some cntStr := dropSuffixCI? rest " or more cards" then
        if let some n := parseNatWord? cntStr then return some (wrap pf (.drewCard n))

  if let some (whoStr, npStr) := splitFirstCI? body " discarded " then
    if let some pf := parsePlayerFilter? whoStr then
      if lower npStr == "a card" then return some (wrap pf (.discardedCard .anyObject))
      if let some np := parseNounPhrase npStr then
        return some (wrap pf (.discardedCard np.filter.pred))

  if let some (whoStr, rest) := splitFirstCI? body " milled " then
    if let some pf := parsePlayerFilter? whoStr then
      let rl := lower rest
      if rl == "a card" then return some (wrap pf (.milledCard 1))
      if let some cntStr := dropSuffixCI? rest " or more cards" then
        if let some n := parseNatWord? cntStr then return some (wrap pf (.milledCard n))

  if let some (whoStr, rest) := splitFirstCI? body " gained " then
    if let some pf := parsePlayerFilter? whoStr then
      if lower rest == "life" then return some (wrap pf (.gainedLife 1))
      if let some cntStr := dropSuffixCI? rest " or more life" then
        if let some n := parseNatWord? cntStr then return some (wrap pf (.gainedLife n))

  if let some (whoStr, rest) := splitFirstCI? body " lost " then
    if let some pf := parsePlayerFilter? whoStr then
      if lower rest == "life" then return some (wrap pf (.lostLife 1))
      if let some cntStr := dropSuffixCI? rest " or more life" then
        if let some n := parseNatWord? cntStr then return some (wrap pf (.lostLife n))

  if let some whoStr := dropSuffixCI? body " were dealt combat damage" then
    if let some pf := parsePlayerFilter? whoStr then
      return some (wrap pf (.dealtDamage true false))
  if let some whoStr := dropSuffixCI? body " was dealt combat damage" then
    if let some pf := parsePlayerFilter? whoStr then
      return some (wrap pf (.dealtDamage true false))
  if let some whoStr := dropSuffixCI? body " were dealt noncombat damage" then
    if let some pf := parsePlayerFilter? whoStr then
      return some (wrap pf (.dealtDamage false true))
  if let some whoStr := dropSuffixCI? body " was dealt noncombat damage" then
    if let some pf := parsePlayerFilter? whoStr then
      return some (wrap pf (.dealtDamage false true))
  if let some whoStr := dropSuffixCI? body " were dealt damage" then
    if let some pf := parsePlayerFilter? whoStr then
      return some (wrap pf (.dealtDamage false false))
  if let some whoStr := dropSuffixCI? body " was dealt damage" then
    if let some pf := parsePlayerFilter? whoStr then
      return some (wrap pf (.dealtDamage false false))

  if let some whoStr := dropSuffixCI? body " activated a loyalty ability" then
    if let some pf := parsePlayerFilter? whoStr then
      return some (wrap pf .activatedLoyalty)
  if let some whoStr := dropSuffixCI? body " proliferated" then
    if let some pf := parsePlayerFilter? whoStr then
      return some (wrap pf .proliferated)
  if let some (whoStr, subStr) := splitFirstCI? body " beheld " then
    if let some pf := parsePlayerFilter? whoStr then
      let subStr := (dropPrefixCI? subStr "an ").getD ((dropPrefixCI? subStr "a ").getD subStr)
      if let some sub := CardSubtype.ofOracle? subStr then
        return some (wrap pf (.beheld sub))

  return none

/-- Stage-4 compositional Oracle condition parser (`Condition`). -/
partial def parseCondition (raw : String) : Option Condition := Id.run do
  let mut s := cleanClause raw
  if s.isEmpty then return none

  -- Optional leading `"if "` / `"as long as "` / `"unless "`.
  if let some rest := dropPrefixCI? s "unless " then
    return (parseCondition rest).map Condition.not
  if let some rest := dropPrefixCI? s "if " then s := rest
  else if let some rest := dropPrefixCI? s "as long as " then s := rest

  -- Explicit `not (...)` wrapper.
  if let some rest := dropPrefixCI? s "not (" then
    if rest.endsWith ")" then
      let inner := (rest.take (rest.length - 1)).trimAscii.copy
      return (parseCondition inner).map Condition.not

  -- Try top-level `" and "` / `" or "` splitting only when both sides parse cleanly as conditions.
  if let some (lhs, rhs) := splitTopLevelCI? s " and " then
    match parseCondition lhs, parseCondition rhs with
    | some c1, some c2 =>
      let flat :=
        match c1, c2 with
        | .all a, .all b => a ++ b
        | .all a, b => a.push b
        | a, .all b => #[a] ++ b
        | a, b => #[a, b]
      return some (.all flat)
    | _, _ => pure ()
  if let some (lhs, rhs) := splitTopLevelCI? s " or " then
    match parseCondition lhs, parseCondition rhs with
    | some c1, some c2 =>
      let flat :=
        match c1, c2 with
        | .any a, .any b => a ++ b
        | .any a, b => a.push b
        | a, .any b => #[a] ++ b
        | a, b => #[a, b]
      return some (.any flat)
    | _, _ => pure ()

  let low := lower s

  -- Turn / step / phase / day-night.
  if low == "it's your turn" || low == "it is your turn" then return some .isYourTurn
  if low == "it's not your turn" || low == "it is not your turn" then
    return some (.not .isYourTurn)
  if low == "it's night" || low == "it is night" then return some .isNight
  if low == "it's day" || low == "it is day" then return some (.not .isNight)
  if low == "you do" then return some (.stepSucceeded ⟨0⟩)
  if let some rest := dropPrefixCI? s "it's the " then
    match parseStepOrPhase? rest with
    | some (.step st) => return some (.duringStep st)
    | some (.phase ph) => return some (.duringPhase ph)
    | none => pure ()
  if let some rest := dropPrefixCI? s "during the " then
    match parseStepOrPhase? rest with
    | some (.step st) => return some (.duringStep st)
    | some (.phase ph) => return some (.duringPhase ph)
    | none => pure ()
  if let some rest := dropPrefixCI? s "during " then
    match parseStepOrPhase? rest with
    | some (.step st) => return some (.duringStep st)
    | some (.phase ph) => return some (.duringPhase ph)
    | none => pure ()

  -- Designations & monarch.
  if low == "you have the city's blessing" then
    return some (.playerPred .you (.hasDesignation .citysBlessing))
  if low == "you have an enduring story" then
    return some (.playerPred .you (.hasDesignation .enduringStory))
  if low == "you're the monarch" || low == "you are the monarch" then
    return some (.playerPred .you .isMonarch)

  -- Cast context (CR 400.7d).
  if low == "this spell was kicked" || low == "it was kicked" then
    return some (.castPred (.wasKicked .this))
  if low == "the gift was promised" || low == "its gift was promised" then
    return some (.castPred (.giftPromised .this))
  if low == "its impending cost was paid" || low == "this permanent's impending cost was paid" then
    return some (.castPred (.impendingPaid .this))
  if low == "its teamwork cost was paid" || low == "teamwork was paid" then
    return some (.castPred (.teamworkPaid .this))
  if low == "its sneak cost was paid" || low == "sneak was paid" then
    return some (.castPred (.sneakPaid .this))
  if low == "mana from a treasure was spent to cast this spell" ||
      low == "mana from a treasure was spent to cast it" then
    return some (.castPred (.manaSpentMatches .fromTreasure .this))
  if low == "uncounterable mana was spent to cast this spell" then
    return some (.castPred (.manaSpentMatches (.withRider .cantBeCountered) .this))
  if let some pre := dropSuffixCI? s " mana was spent to cast this spell" then
    if let some c := parseColorWord? pre then
      return some (.castPred (.manaSpentMatches (.ofColor c) .this))
  if let some zStr := dropPrefixCI? s "this spell was cast from " then
    if let some z := parseZoneKind? zStr then
      return some (.castPred (.castFrom z .this))
  if let some zStr := dropPrefixCI? s "it was cast from " then
    if let some z := parseZoneKind? zStr then
      return some (.castPred (.castFrom z .this))

  -- Turn history (`... this turn` / `... last turn`).
  if let some hp := parseTurnHistory? s then
    return some (.turnHistory hp)

  -- Player control / existence checks (`you control ...`, `there is ...`, `every ... is ...`).
  if let some rest := dropPrefixCI? s "you don't control " then
    if let some np := parseNounPhrase s!"{rest} you control" then
      return some (.not (.exists np.filter.toExpr))
  if let some rest := dropPrefixCI? s "you control no " then
    if let some np := parseNounPhrase s!"{rest} you control" then
      return some (.not (.exists np.filter.toExpr))
  if let some rest := dropPrefixCI? s "you control " then
    if let some (cntStr, npStr) := splitFirstCI? rest " or more " then
      match parseValueExpr cntStr, parseNounPhrase s!"{npStr} you control" with
      | some v, some np => return some (.cmp .ge (.aggregate .count .one np.filter.toExpr) v)
      | _, _ => pure ()
    if let some np := parseNounPhrase s!"{rest} you control" then
      return some (.exists np.filter.toExpr)
  if let some rest := dropPrefixCI? s "there are no " then
    if let some np := parseNounPhrase rest then
      return some (.not (.exists np.filter.toExpr))
  if let some rest := dropPrefixCI? s "there are " then
    if let some (cntStr, npStr) := splitFirstCI? rest " or more " then
      match parseValueExpr cntStr, parseNounPhrase npStr with
      | some v, some np => return some (.cmp .ge (.aggregate .count .one np.filter.toExpr) v)
      | _, _ => pure ()
    if let some np := parseNounPhrase rest then
      return some (.exists np.filter.toExpr)
  if let some rest := dropPrefixCI? s "there is " then
    if let some np := parseNounPhrase rest then
      return some (.exists np.filter.toExpr)
  if let some rest := dropPrefixCI? s "every " then
    if let some (objStr, predStr) := splitFirstCI? rest " is " then
      match parseObjectExpr? objStr, parseNounPhrase predStr with
      | some objs, some np => return some (.forAll objs np.filter.pred)
      | _, _ => pure ()

  -- Player shortcuts (`you have N or less life`, `you have N or more cards in your graveyard/hand`).
  if let some rest := dropPrefixCI? s "you have " then
    if lower rest == "no cards in hand" || lower rest == "no cards in your hand" then
      return some (.cmp .eq (.playerMetric .handSize .you) (.const 0))
    if let some boundStr := dropSuffixCI? rest " life" then
      if let some (op, v) := parseCmpBound? boundStr then
        return some (.cmp op (.playerMetric .life .you) v)
    if let some boundStr := dropSuffixCI? rest " cards in your graveyard" then
      if let some (op, v) := parseCmpBound? boundStr then
        return some (.cmp op (.playerMetric .graveyardSize .you) v)
    if let some boundStr := dropSuffixCI? rest " cards in your hand" then
      if let some (op, v) := parseCmpBound? boundStr then
        return some (.cmp op (.playerMetric .handSize .you) v)
    if let some boundStr := dropSuffixCI? rest " cards in hand" then
      if let some (op, v) := parseCmpBound? boundStr then
        return some (.cmp op (.playerMetric .handSize .you) v)

  -- General numeric comparison (`<lhs> is <cmpBound>`).
  if let some (lhs, rhs) := splitFirstCI? s " is " then
    match parseValueExpr lhs, parseCmpBound? rhs with
    | some vl, some (op, vr) => return some (.cmp op vl vr)
    | _, _ => pure ()

  return none

/-- Stage-4 compositional Oracle duration parser (`DurationExpr`, CR 611.2a–b). -/
partial def parseDuration (raw : String) : Option DurationExpr := Id.run do
  let s := cleanClause raw
  let low := lower s
  if low == "until end of turn" then return some .untilEndOfTurn
  if low == "until end of combat" then return some .untilEndOfCombat
  if low == "for the rest of the game" then return some .indefinite
  if low == "until your next turn" then return some (.untilNextTurnOf .you)
  if low == "until the end of your next turn" || low == "until end of your next turn" then
    return some (.untilEndOfNextTurnOf .you)

  if let some rest := dropPrefixCI? s "until the end of " then
    if let some whoStr := dropSuffixCI? rest "'s next turn" then
      return (parsePlayerExpr? whoStr).map DurationExpr.untilEndOfNextTurnOf
    if let some sp := parseStepOrPhase? rest then
      return some (.untilEndOfStepOrPhase sp)
  if let some rest := dropPrefixCI? s "until end of " then
    if let some whoStr := dropSuffixCI? rest "'s next turn" then
      return (parsePlayerExpr? whoStr).map DurationExpr.untilEndOfNextTurnOf
    if let some sp := parseStepOrPhase? rest then
      return some (.untilEndOfStepOrPhase sp)

  if let some rest := dropPrefixCI? s "until " then
    if let some whoStr := dropSuffixCI? rest "'s next turn" then
      return (parsePlayerExpr? whoStr).map DurationExpr.untilNextTurnOf
    if let some objStr := dropSuffixCI? rest " leaves the battlefield" then
      return (parseObjectExpr? objStr).map DurationExpr.untilLeavesBattlefield
    if let some sp := parseStepOrPhase? rest then
      return some (.untilStepOrPhase sp)

  let asLong? := (dropPrefixCI? s "for as long as ").orElse fun _ =>
    (dropPrefixCI? s "as long as ").orElse fun _ => dropPrefixCI? s "while "
  if let some rest := asLong? then
    if let some objStr := dropSuffixCI? rest " remains on the battlefield" then
      return (parseObjectExpr? objStr).map DurationExpr.whileOnBattlefield
    if let some objStr := dropSuffixCI? rest " remains exiled" then
      return (parseObjectExpr? objStr).map (DurationExpr.whileInZone · .exile)
    if let some (objStr, zStr) := splitLastCI? rest " remains in " then
      match parseObjectExpr? objStr, parseZoneKind? zStr with
      | some obj, some z => return some (.whileInZone obj z)
      | _, _ => pure ()
    if let some (objStr, cntStr) := splitFirstCI? rest " has " then
      let cntCore := (dropSuffixCI? cntStr " on it").getD cntStr
      match parseObjectExpr? objStr, CounterKind.matchPhrase ((splitWords cntCore).toList.map lower) with
      | some obj, some (_, k, _) => return some (.whileHasCounter obj k)
      | _, _ => pure ()

  return none

end

/-! ### Phase-3 Compositional Target Parsers (`TargetSlot`, `TargetSpec`) -/

/-- Add `.hasType .creature` after bare battlefield creature-subtype predicates
(e.g. `"target Elf you control"`, `"target Goblin or Orc you control"`), while
leaving non-creature subtypes (`Equipment`, `Aura`, `Forest`, ...) and non-battlefield
cards untouched. -/
private def normalizeTargetObjectPred (zones : ZoneSetSpec) (pred : ObjectPred) : ObjectPred :=
  if zones != .battlefield then pred
  else
    let atoms := match pred with | .all ps => ps | p => #[p]
    let hasExplicitTypeOrKind := atoms.any fun
      | .hasType _ | .not (.hasType _) | .isKind _ => true
      | .any ps =>
        ps.any (fun
          | .hasType _ | .hasSupertype _ => true
          | .all inner => inner.any (fun | .hasType _ => true | _ => false)
          | _ => false)
      | _ => false
    if hasExplicitTypeOrKind || pred == ObjectPred.worthy then pred
    else
      let isCreatureSubAtom : ObjectPred → Bool
        | .hasSubtype (.literal s) => s.isCreatureType
        | .any ps =>
          !ps.isEmpty && ps.all (fun
            | .hasSubtype (.literal s) => s.isCreatureType
            | _ => false)
        | _ => false
      let rec insertAfterSub : List ObjectPred → Bool → List ObjectPred
        | [], _ => []
        | a :: rest, false =>
          if isCreatureSubAtom a then a :: .hasType .creature :: rest
          else a :: insertAfterSub rest false
        | xs, true => xs
      let updated := insertAfterSub atoms.toList false
      if updated.length == atoms.size then pred
      else ObjectPred.andAll updated.toArray

/-- Strip a leading target quantifier (`"up to N "`, `"any number of "`, `"lo or hi "`, `"N "`).
Returns `(count, rest, hasExplicitQuant)`. -/
private def stripTargetQuantPrefix (s : String) : CountRange × String × Bool := Id.run do
  let toks := splitWords s
  if toks.isEmpty then return (.exact 1, s, false)
  let w0 := lower toks[0]!
  if w0 == "any" && toks.size >= 3 && lower toks[1]! == "number" && lower toks[2]! == "of" then
    let rest := String.intercalate " " (toks.toList.drop 3)
    return (.anyNumber, rest, true)
  if w0 == "up" && toks.size >= 3 && lower toks[1]! == "to" then
    if let some n := parseNatWord? toks[2]! then
      let rest := String.intercalate " " (toks.toList.drop 3)
      return (.upTo n, rest, true)
  if toks.size >= 3 && (lower toks[1]! == "or" || lower toks[1]! == "to") then
    match parseNatWord? toks[0]!, parseNatWord? toks[2]! with
    | some lo, some hi =>
      if lo >= 1 && hi > lo then
        let rest := String.intercalate " " (toks.toList.drop 3)
        return (.between lo hi, rest, true)
    | _, _ => pure ()
  if let some n := parseNatWord? toks[0]! then
    if n >= 1 then
      let rest := String.intercalate " " (toks.toList.drop 1)
      return (.exact n, rest, true)
  return (.exact 1, s, false)

/-- Parse a `PlayerPred` after `"player who "` / `"opponent who "` (matching `printPlayerPred`). -/
private def parsePlayerPredClause? (raw : String) : Option PlayerPred := Id.run do
  let s := cleanClause raw
  let low := lower s
  if low == "is the monarch" then return some .isMonarch
  if low == "is the active player" then return some .isActivePlayer
  if low == "is the defending player" then return some .isDefendingPlayer
  if low == "has the city's blessing" || low == "has the citys blessing" then
    return some (.hasDesignation .citysBlessing)
  if low == "has an enduring story" then
    return some (.hasDesignation .enduringStory)
  if let some rest := (dropPrefixCI? s "controls ").orElse (fun _ => dropPrefixCI? s "control ") then
    if let some (cntStr, npStr) := splitFirstCI? rest " or more " then
      match parseValueExpr cntStr, parseNounPhrase npStr with
      | some v, some np => return some (.controls np.filter v)
      | _, _ => pure ()
    if let some np := parseNounPhrase rest then
      return some (.controls np.filter (.const 1))
  if let some rest := (dropPrefixCI? s "has ").orElse (fun _ => dropPrefixCI? s "have ") then
    if let some b := dropSuffixCI? rest " life" then
      if let some (op, v) := parseCmpBound? b then return some (.metric .life op v)
    if let some b := (dropSuffixCI? rest " cards in hand").orElse (fun _ => dropSuffixCI? rest " cards in their hand") then
      if let some (op, v) := parseCmpBound? b then return some (.metric .handSize op v)
    if let some b := (dropSuffixCI? rest " cards in their graveyard").orElse (fun _ => dropSuffixCI? rest " cards in graveyard") then
      if let some (op, v) := parseCmpBound? b then return some (.metric .graveyardSize op v)
    if let some b := dropSuffixCI? rest " poison counters" then
      if let some (op, v) := parseCmpBound? b then return some (.metric .poisonCounters op v)
  return none

/-- Parse a player-target phrase after stripping `"target "` (e.g. `"player"`,
`"opponent"`, `"players"`, `"player who controls an artifact"`). -/
private def parseTargetPlayerDomain? (raw : String) : Option TargetDomain := Id.run do
  let s := cleanClause raw
  let low := lower s
  if low == "player" || low == "players" then return some (.player .any)
  if low == "opponent" || low == "opponents" then return some (.player .opponent)
  if low == "teammate" || low == "teammates" then return some (.player .teammate)
  if low == "defending player" then return some (.player .defendingPlayer)
  if let some (head, predStr) := splitFirstCI? s " who " then
    let rel? : Option PlayerRelation :=
      match lower head with
      | "player" | "players" => some .anyPlayer
      | "opponent" | "opponents" => some .opponent
      | "teammate" | "teammates" => some .teammate
      | _ => none
    match rel? with
    | some rel =>
      if let some p := parsePlayerPredClause? predStr then
        return some (.player { relation := rel, pred := p })
    | none => pure ()
  return none

/-- Parse a stack-ability target domain after stripping `"target "` (e.g.
`"activated or triggered ability you control from an artifact source"`). -/
private def parseStackAbilityDomain? (raw : String) : Option TargetDomain := Id.run do
  let s := cleanClause raw
  let rest? :=
    (dropPrefixCI? s "activated or triggered abilities").orElse fun _ =>
      dropPrefixCI? s "activated or triggered ability"
  let some rest := rest? | return none
  let mut r := rest.trimAscii.copy
  let mut srcPred : ObjectPred := .anyObject
  if let some (beforeFrom, fromStr) := splitFirstCI? r " from " then
    let inner := (dropSuffixCI? fromStr " source").getD fromStr
    let inner := (dropPrefixCI? inner "an ").getD ((dropPrefixCI? inner "a ").getD inner)
    if let some ty := CardType.ofOracle? inner then
      srcPred := .hasType ty
      r := beforeFrom.trimAscii.copy
    else if let some np := parseNounPhrase inner then
      srcPred := np.filter.pred
      r := beforeFrom.trimAscii.copy
    else
      return none
  let rl := lower r
  let ctrl : PlayerFilter ←
    if rl.isEmpty then .any
    else if rl == "you control" then .you
    else if rl == "an opponent controls" || rl == "opponents control" then .opponent
    else if rl == "that player controls" then .thatPlayer
    else return none
  return some (.stackAbility ctrl srcPred)

/-- Parse one Oracle target phrase corresponding to a single `"target"` word
(CR 115.1 / 115.4 / 601.2c). -/
partial def parseTargetSlot (raw : String) : Option TargetSlot := Id.run do
  let mut s := cleanClause raw
  if s.isEmpty then return none

  -- 1. Optional `"for each opponent, ..."` / `"for each player, ..."` prefix.
  let mut forEach? : Option PlayerFilter := none
  if let some rest := (dropPrefixCI? s "for each opponent, ").orElse
      (fun _ => dropPrefixCI? s "for each opponent ") then
    forEach? := some .opponent; s := rest
  else if let some rest := (dropPrefixCI? s "for each player, ").orElse
      (fun _ => dropPrefixCI? s "for each player ") then
    forEach? := some .any; s := rest

  -- 2. Optional trailing `GroupTargetConstraint` suffix.
  let mut gc? : Option GroupTargetConstraint := none
  if let some (lhs, rhs) := splitLastCI? s " with total mana value " then
    if let some vStr := dropSuffixCI? rhs " or less" then
      if let some v := parseValueExpr vStr then
        gc? := some (.totalManaValueAtMost v); s := lhs
  else if let some pre := dropSuffixCI? s " that share a color" then
    gc? := some (.shareCharacteristic .color); s := pre
  else if let some pre := dropSuffixCI? s " that share a card type" then
    gc? := some (.shareCharacteristic .cardType); s := pre
  else if let some pre := dropSuffixCI? s " that share a creature type" then
    gc? := some (.shareCharacteristic .creatureType); s := pre
  else if let some pre := dropSuffixCI? s " that share a subtype" then
    gc? := some (.shareCharacteristic .subtype); s := pre
  else if let some pre := dropSuffixCI? s " with different controllers" then
    gc? := some .distinctControllers; s := pre
  else if let some pre := dropSuffixCI? s " with different names" then
    gc? := some .distinctNames; s := pre
  else if let some pre := dropSuffixCI? s " of each card type" then
    gc? := some .distinctCardTypes; s := pre

  let mkSlot (domain : TargetDomain) (count : CountRange) : TargetSlot :=
    let domain :=
      match forEach? with
      | some pf =>
        if pf == .opponent then domain.substitutePlayerFilter .thatPlayer .opponent
        else domain
      | none => domain
    { domain, count, groupConstraint? := gc?, forEach? }

  let low := lower s
  -- 3. CR 115.4 `"any target"` / `"any other target"` and bare quantified targets.
  if low == "any target" then
    return some (mkSlot (.anyTarget .any) (.exact 1))
  if low == "any other target" then
    return some (mkSlot (.anyTarget (.otherThan .this)) (.exact 1))

  let (qCount, afterQuant, hasExplicitQuant) := stripTargetQuantPrefix s
  let aqLow := lower afterQuant
  if hasExplicitQuant then
    if aqLow == "target" || aqLow == "targets" then
      return some (mkSlot (.anyTarget .any) qCount)
    if aqLow == "other target" || aqLow == "other targets" then
      return some (mkSlot (.anyTarget (.otherThan .this)) qCount)

  -- 4. Special non-single-object domains after `"target "`.
  if let some afterTarget := dropPrefixCI? afterQuant "target " then
    let atLow := lower afterTarget
    -- 4a. Player targets (`target player`, `two target players`, `target opponent`, ...).
    if let some pd := parseTargetPlayerDomain? afterTarget then
      return some (mkSlot pd qCount)
    -- 4b. Stack abilities (`target activated or triggered ability you control from an artifact source`).
    if let some sd := parseStackAbilityDomain? afterTarget then
      return some (mkSlot sd qCount)
    -- 4c. Multi-domain unions (`spell or creature`, `permanent or player`,
    --     `creature or creature card in a graveyard`, `<obj> or player/opponent`).
    if atLow == "spell or creature" || atLow == "spells or creatures" then
      return some (mkSlot TargetDomain.spellOrCreature qCount)
    if atLow == "permanent or player" || atLow == "permanents or players" then
      return some (mkSlot TargetDomain.permanentOrPlayer qCount)
    if atLow == "creature or creature card in a graveyard" ||
        atLow == "creature or creature card from a graveyard" then
      return some (mkSlot TargetDomain.creatureOrGyCreatureCard qCount)
    if let some (lhs, rhs) := splitLastCI? afterTarget " or " then
      if let some pd := parseTargetPlayerDomain? rhs then
        if let some np := parseNounPhrase lhs then
          let pred := normalizeTargetObjectPred np.filter.zones np.filter.pred
          return some (mkSlot (.anyOf #[.object np.filter.zones pred, pd]) qCount)

  -- 5. General object target via `parseNounPhrase`.
  let some np := parseNounPhrase s | return none
  if !np.isTarget then return none
  let count : CountRange ←
    match np.quantifier with
    | .singular => .exact 1
    | .exact n => .exact n
    | .upTo n => .upTo n
    | .between lo hi => .between lo hi
    | .anyNumber => .anyNumber
    | .each | .plural => return none
  let pred := normalizeTargetObjectPred np.filter.zones np.filter.pred
  return some (mkSlot (.object np.filter.zones pred) count)

/-- Parse a single-slot or multi-slot Oracle target specification (CR 115.1 / 115.3). -/
partial def parseTargetSpec (raw : String) : Option TargetSpec := Id.run do
  let s := cleanClause raw
  if s.isEmpty then return none

  -- 1. Distinct repeated slot: `"<slot0> and a second <slot1>"`.
  if let some (lhs, rhs) := splitFirstCI? s " and a second " then
    match parseTargetSlot lhs, parseTargetSlot rhs with
    | some s0, some s1 =>
      return some (TargetSpec.ofSlots #[s0, s1] #[{ slots := #[0, 1], relation := .distinct }])
    | _, _ => pure ()

  -- 2. Explicit multi-slot `"<slot0> and <rest>"` where `<rest>` contains `"target"`.
  if let some (lhs, rhs) := splitFirstCI? s " and " then
    if (lower rhs).contains "target" then
      match parseTargetSlot lhs, parseTargetSpec rhs with
      | some s0, some tsRest =>
        return some (TargetSpec.append (TargetSpec.single s0) tsRest)
      | _, _ => pure ()

  -- 3. Single-slot target specification.
  if let some slot := parseTargetSlot s then
    return some (TargetSpec.single slot)

  -- 4. Shorthand second slot omitting `"target"` (`"target creature you control and a creature an opponent controls"`).
  if let some (lhs, rhs) := splitFirstCI? s " and " then
    let rhsBody? := (dropPrefixCI? rhs "an ").orElse (fun _ => dropPrefixCI? rhs "a ")
    if let some rhsBody := rhsBody? then
      match parseTargetSlot lhs, parseTargetSlot s!"target {rhsBody}" with
      | some s0, some s1 => return some (TargetSpec.ofSlots #[s0, s1])
      | _, _ => pure ()

  return none

/-- Longest prefix of normalized Oracle tokens that parses as a `TargetSpec`.
Replaces `OracleArgs.fromNounPrefix`'s hardcoded tables with the compositional
Stage-4 target grammar. -/
def parseTargetSpecPrefix (toks : List String) : Option (TargetSpec × Nat) := Id.run do
  let t0 :: _ := toks | return none
  let w0 := lower t0
  let plausibleStart :=
    w0 == "target" || w0 == "another" || w0 == "other" ||
    w0 == "any" || w0 == "up" || w0 == "for" ||
    (parseNatWord? t0).isSome
  if !plausibleStart then return none
  let arr := toks.toArray
  let maxLen := min arr.size 24
  let mut len := maxLen
  while len > 0 do
    let phrase := String.intercalate " " (arr.extract 0 len).toList
    if let some ts := parseTargetSpec phrase then
      return some (ts, len)
    len := len - 1
  return none

/-! ### Stage-4 Compositional Cost & Keyword Sub-Grammars (CR 118, 606.2–6, 702) -/

/-- Strip balanced parenthetical reminder text `(...)` from an Oracle string. -/
def stripReminderText (s : String) : String := Id.run do
  let mut out : List Char := []
  let mut depth : Nat := 0
  for c in s.toList do
    if c == '(' then
      depth := depth + 1
    else if c == ')' then
      if depth > 0 then depth := depth - 1
    else if depth == 0 then
      out := c :: out
  -- Collapse redundant spaces introduced around stripped parentheses.
  let raw := (String.ofList out.reverse).trimAscii.copy
  let mut prevSpace := false
  let mut collapsed : List Char := []
  for c in raw.toList do
    if c == ' ' then
      if !prevSpace then
        collapsed := c :: collapsed
        prevSpace := true
    else
      collapsed := c :: collapsed
      prevSpace := false
  (String.ofList collapsed.reverse).trimAscii.copy

/-- Parse one mana symbol `{W}`, `{2}`, `{G/U}`, `{2/W}`, `{X}`, `{C}` from the
front of `s`, returning the symbol and remaining trimmed text. -/
def parseManaSymbol? (s : String) : Option (ManaSymbol × String) :=
  let s := s.trimAscii.copy
  if !s.startsWith "{" then none
  else
    match (s.drop 1).copy.splitOn "}" with
    | [] => none
    | head :: rest =>
      let sym := head.trimAscii.copy.map Char.toUpper
      let after := (String.intercalate "}" rest).trimAscii.copy
      let color? : String → Option Color
        | "W" => some .white
        | "U" => some .blue
        | "B" => some .black
        | "R" => some .red
        | "G" => some .green
        | _ => none
      if sym == "X" then some (.x, after)
      else if sym == "C" then some (.colorless, after)
      else
        match sym.splitOn "/" with
        | [a, b] =>
          match color? a, color? b with
          | some ca, some cb => some (.hybrid ca cb, after)
          | none, some cb =>
            if a.all Char.isDigit && !a.isEmpty then some (.twobrid cb, after)
            else none
          | _, _ => none
        | _ =>
          match color? sym with
          | some c => some (.colored c, after)
          | none =>
            if sym.all Char.isDigit && !sym.isEmpty then
              some (.generic sym.toNat!, after)
            else none

/-- Parse a string consisting solely of mana symbols (`{1}{G}`, `{0}`, `{X}{R}`). -/
def parseManaCost? (s : String) : Option ManaCost :=
  let s := s.trimAscii.copy
  if s.isEmpty || !s.startsWith "{" then none
  else
    let rec go (left : String) (acc : Array ManaSymbol) : Option ManaCost :=
      if left.isEmpty then some { symbols := acc }
      else
        match parseManaSymbol? left with
        | none => none
        | some (sym, rest) =>
          if rest.length < left.length then go rest (acc.push sym) else none
    termination_by left.length
    go s #[]

/-- Parse a planeswalker loyalty symbol (`[+1]`, `[-2]`, `[−2]`, `[0]`, `[+X]`, `[-X]`). -/
def parseLoyaltySymbol? (raw : String) : Option LoyaltySymbol :=
  let s := raw.trimAscii.copy.replace "\u2212" "-"
  let inner? :=
    if s.startsWith "[" && s.endsWith "]" && s.length ≥ 3 then
      some (((s.drop 1).copy.dropEnd 1).copy.trimAscii.copy)
    else none
  match inner? with
  | none => none
  | some core =>
    let up := core.map Char.toUpper
    if up == "0" then some .zero
    else if up == "+X" then some .plusX
    else if up == "-X" then some .minusX
    else if up.startsWith "+" then
      let digits := (up.drop 1).copy
      if !digits.isEmpty && digits.all Char.isDigit then some (.plus digits.toNat!) else none
    else if up.startsWith "-" then
      let digits := (up.drop 1).copy
      if !digits.isEmpty && digits.all Char.isDigit then some (.minus digits.toNat!) else none
    else none

private def isSelfObjectPhrase (raw : String) : Bool :=
  match lower (cleanClause raw) with
  | "~" | "this" | "it" | "this permanent" | "this creature" | "this artifact"
  | "this enchantment" | "this land" | "this planeswalker" | "this equipment"
  | "this vehicle" | "this aura" | "this card" | "this spell" | "this saga" => true
  | _ => false

private def stripTrailingPeriod (s : String) : String :=
  let t := s.trimAscii.copy
  if t.endsWith "." then (t.dropEnd 1).copy.trimAscii.copy else t

private def splitAllCI (haystack needle : String) : Array (String × String) := Id.run do
  let hLow := lower haystack
  let nLow := lower needle
  if nLow.isEmpty || hLow.length < nLow.length then return #[]
  let hChars := haystack.toList.toArray
  let hLowChars := hLow.toList.toArray
  let nChars := nLow.toList.toArray
  let mut out : Array (String × String) := #[]
  for i in [0 : hChars.size - nChars.size + 1] do
    let mut ok := true
    for j in [0 : nChars.size] do
      if hLowChars[i + j]! != nChars[j]! then
        ok := false
        break
    if ok then
      let lhs := (String.ofList (hChars.extract 0 i).toList).trimAscii.copy
      let rhs := (String.ofList (hChars.extract (i + nChars.size) hChars.size).toList).trimAscii.copy
      out := out.push (lhs, rhs)
  return out

private def parseCounterPhrase? (raw : String) : Option (CostCountSpec × Option CounterKind) := Id.run do
  let s := lower (cleanClause raw)
  if let some rest := dropPrefixCI? s "any number of " then
    let ws := (splitWords rest).toList
    if let some (k, consumed) := CounterKind.ofPrefix ws then
      let tail := ws.drop consumed
      if tail == ["counter"] || tail == ["counters"] || tail.isEmpty then
        return some (.anyNumber, some k)
    if rest == "counters" || rest == "counter" then
      return some (.anyNumber, none)
  let ws := (splitWords s).toList
  if let some (n, k, consumed) := CounterKind.matchPhrase ws then
    if consumed == ws.length then
      return some (.exact n, some k)
  -- `"X <kind> counters"` / `"a/N counter(s)"`
  match ws with
  | ["a", "counter"] | ["one", "counter"] | ["1", "counter"] =>
    return some (.exact 1, none)
  | [nWord, "counters"] =>
    if nWord == "x" then return some (.count .chosenX, none)
    if let some n := parseNatWord? nWord then return some (.exact n, none)
  | nWord :: rest =>
    if nWord == "x" then
      if let some (k, consumed) := CounterKind.ofPrefix rest then
        let tail := rest.drop consumed
        if tail == ["counter"] || tail == ["counters"] then
          return some (.count .chosenX, some k)
  | _ => pure ()
  return none

private def nounQuantToCostCount : NounQuantifier → Option CostCountSpec
  | .singular => some (.exact 1)
  | .exact n => some (.exact n)
  | .anyNumber => some .anyNumber
  | _ => none

private def parseSacrificePhrase? (raw : String) : Option (CostCountSpec × SelfOrFilter) := Id.run do
  let s := stripTrailingPeriod (cleanClause raw)
  if isSelfObjectPhrase s then
    return some (.exact 1, .self)
  let lowS := lower s
  -- Canonical multi-type / special sacrifice patterns first so AST matches `CostSpec` builders.
  if lowS == "a creature" then
    return some (.exact 1, .filter (.hasType .creature))
  if lowS == "another creature" then
    return some (.exact 1, .filter (.all #[.otherThan .this, .hasType .creature]))
  if lowS == "an artifact" then
    return some (.exact 1, .filter (.hasType .artifact))
  if lowS == "another artifact" then
    return some (.exact 1, .filter (.all #[.otherThan .this, .hasType .artifact]))
  if lowS == "a legendary artifact" then
    return some (.exact 1, .filter (.all #[.hasSupertype .legendary, .hasType .artifact]))
  if lowS == "a legendary artifact or legendary creature" || lowS == "a legendary creature or legendary artifact" then
    return some (.exact 1, .filter (.all #[.hasSupertype .legendary, .any #[.hasType .artifact, .hasType .creature]]))
  if lowS == "an artifact or creature" || lowS == "an artifact or a creature" then
    return some (.exact 1, .filter (.any #[.hasType .artifact, .hasType .creature]))
  if lowS == "a creature or artifact" || lowS == "a creature or an artifact" then
    return some (.exact 1, .filter (.any #[.hasType .creature, .hasType .artifact]))
  if lowS == "another creature or artifact" || lowS == "another artifact or creature" then
    return some (.exact 1, .filter (.all #[.otherThan .this, .any #[.hasType .creature, .hasType .artifact]]))
  if lowS == "a creature or planeswalker" || lowS == "a creature or a planeswalker" then
    return some (.exact 1, .filter (.any #[.hasType .creature, .hasType .planeswalker]))
  if lowS == "another creature or planeswalker" then
    return some (.exact 1, .filter (.all #[.otherThan .this, .any #[.hasType .creature, .hasType .planeswalker]]))
  if lowS == "an artifact or land" || lowS == "an artifact or a land" then
    return some (.exact 1, .filter (.any #[.hasType .artifact, .hasType .land]))
  if lowS == "an equipment attached to this creature" || lowS == "an equipment attached to ~" then
    return some (.exact 1, .filter (.all #[.hasSubtype (.literal .equipment), .attachedTo .this]))
  -- `"another <Subtype>"`
  if let some rest := dropPrefixCI? s "another " then
    if let some sub := CardSubtype.ofOracle? rest then
      return some (.exact 1, .filter (.all #[.otherThan .this, .hasSubtype (.literal sub)]))
  -- `"N permanents"` / `"a permanent"`
  if lowS == "a permanent" then
    return some (.exact 1, .filter .anyObject)
  if let some nWord := dropSuffixCI? lowS " permanents" then
    if let some n := parseNatWord? nWord then
      return some (.exact n, .filter .anyObject)
  -- General compositional fallback via `parseNounPhrase`.
  if let some np := parseNounPhrase s then
    if !np.isTarget then
      if let some cnt := nounQuantToCostCount np.quantifier then
        return some (cnt, .filter np.filter.pred)
  return none

private def parseDiscardPhrase? (raw : String) : Option (CostCountSpec × DiscardCostTarget) := Id.run do
  let s := stripTrailingPeriod (cleanClause raw)
  let lowS := lower s
  if isSelfObjectPhrase s then
    return some (.exact 1, .self)
  if let some core := dropSuffixCI? lowS " at random" then
    if core == "a card" || core == "one card" || core == "1 card" then
      return some (.exact 1, .random)
    if let some nWord := dropSuffixCI? core " cards" then
      if let some n := parseNatWord? nWord then
        return some (.exact n, .random)
  if lowS == "a card" || lowS == "one card" || lowS == "1 card" then
    return some (.exact 1, .hand)
  if let some nWord := dropSuffixCI? lowS " cards" then
    if let some n := parseNatWord? nWord then
      return some (.exact n, .hand)
  if lowS == "a nonland card" then
    return some (.exact 1, .matching (.not (.hasType .land)))
  if lowS == "a legendary card" then
    return some (.exact 1, .matching (.hasSupertype .legendary))
  if lowS == "an enchantment, instant, or sorcery card" then
    return some (.exact 1, .matching (.any #[.hasType .enchantment, .hasType .instant, .hasType .sorcery]))
  if lowS == "a legendary card that has the same name as a legendary permanent you control" ||
     lowS == "a legendary card with the same name as a legendary permanent you control" then
    return some (.exact 1, .matching (.all #[
      .hasSupertype .legendary,
      .shares .name (.inZones .battlefield (.all #[.hasSupertype .legendary, .controlledBy .you]))
    ]))
  -- General compositional fallback via `parseNounPhrase`.
  if let some np := parseNounPhrase s then
    if !np.isTarget then
      if let some cnt := nounQuantToCostCount np.quantifier then
        return some (cnt, .matching np.filter.pred)
  return none

mutual

/-- Parse one atomic or choice-combinator `CostItem` from normalized Oracle text
(CR 118, 606.2–6, 701.4, 701.9, 701.21, 701.26, 701.59, 701.67, 702.122, 702.190, 702.194). -/
partial def parseCostItem (raw : String) : Option CostItem := Id.run do
  let s := stripTrailingPeriod (stripReminderText raw)
  if s.isEmpty then return none
  let lowS := lower s

  -- 1. `{T}` / `{Q}` / loyalty symbol / pure mana cost / `"pay {mana}"`
  if lowS == "{t}" then return some .tapSelf
  if lowS == "{q}" then return some .untapSelf
  if let some sym := parseLoyaltySymbol? s then return some (.loyalty sym)
  if let some mc := parseManaCost? s then return some (.mana mc)
  if let some rest := dropPrefixCI? s "pay " then
    if let some mc := parseManaCost? rest then
      return some (.mana mc)
    if let some amtStr := dropSuffixCI? rest " life" then
      if let some v := parseValueExpr amtStr then
        return some (.payLife v)

  -- 2. Waterbend (CR 701.67)
  if let some rest := dropPrefixCI? s "waterbend " then
    let cleanRest := rest.trimAscii.copy
    if cleanRest.startsWith "{" && cleanRest.endsWith "}" then
      let inner := ((cleanRest.drop 1).copy.dropEnd 1).copy
      if let some v := parseValueExpr inner then
        return some (.waterbend v)
    if let some v := parseValueExpr cleanRest then
      return some (.waterbend v)

  -- 3. Behold a/an <Subtype> (CR 701.4)
  if let some rest := dropPrefixCI? s "behold " then
    let subStr :=
      if let some r := dropPrefixCI? rest "an " then r
      else if let some r := dropPrefixCI? rest "a " then r
      else rest
    if let some sub := CardSubtype.ofOracle? subStr then
      return some (.behold sub)

  -- 4. Poison counters paid by the payer (`"Get N poison counters"`)
  if let some rest := dropPrefixCI? lowS "get " then
    if rest == "a poison counter" || rest == "one poison counter" || rest == "1 poison counter" then
      return some (.putCounters (.const 1) .poison .payer)
    if let some nWord := dropSuffixCI? rest " poison counters" then
      if let some n := parseNatWord? nWord then
        return some (.putCounters (.const n) .poison .payer)

  -- 5. Put counters on self / permanent / payer
  if let some rest := dropPrefixCI? s "put " then
    if let some (cntStr, tgtStr) := splitLastCI? rest " on " then
      if let some (cntSpec, some kind) := parseCounterPhrase? cntStr then
        let amt? : Option ValueExpr :=
          match cntSpec with
          | .count v => some v
          | _ => none
        if let some amt := amt? then
          if isSelfObjectPhrase tgtStr then
            return some (.putCounters amt kind .self)
          else if let some np := parseNounPhrase tgtStr then
            return some (.putCounters amt kind (.filter np.filter.pred))

  -- 6. Remove counters from self / permanent
  if let some rest := dropPrefixCI? s "remove " then
    if let some (cntStr, fromStr) := splitLastCI? rest " from " then
      if let some (cntSpec, kind?) := parseCounterPhrase? cntStr then
        if isSelfObjectPhrase fromStr then
          return some (.removeCounters cntSpec kind? .self)
        else if let some np := parseNounPhrase fromStr then
          return some (.removeCounters cntSpec kind? (.filter np.filter.pred))

  -- 7. Collect evidence N (CR 701.59)
  if let some rest := dropPrefixCI? lowS "collect evidence " then
    if let some n := parseNatWord? rest then
      return some (.exile (.totalManaValueAtLeast (.const n)) .yourGraveyard (.filter (.isKind .card)) true)

  -- 8. Sacrifice
  if let some rest := dropPrefixCI? s "sacrifice " then
    if let some (cnt, what) := parseSacrificePhrase? rest then
      return some (.sacrifice cnt what)

  -- 9. Discard
  if let some rest := dropPrefixCI? s "discard " then
    if let some (cnt, what) := parseDiscardPhrase? rest then
      return some (.discard cnt what)

  -- 10. Exile
  if let some rest := dropPrefixCI? s "exile " then
    let lowRest := lower rest
    -- `"exile this card from your graveyard"` / `"exile ~ from your graveyard"`
    if let some obj := dropSuffixCI? lowRest " from your graveyard" then
      if isSelfObjectPhrase obj then
        return some (.exile (.exact 1) .yourGraveyard .self false)
      if obj == "another creature card" then
        return some (.exile (.exact 1) .yourGraveyard
          (.filter (.all #[.otherThan .this, .hasType .creature, .isKind .card])) false)
    -- `"exile this card from your hand"` / `"exile ~ from your hand"`
    if let some obj := dropSuffixCI? lowRest " from your hand" then
      if isSelfObjectPhrase obj then
        return some (.exile (.exact 1) .yourHand .self false)
    -- `"exile any number of <color> cards from your graveyard with N or more <color> mana symbols among their mana costs"`
    if let some (lhs, rhs) := splitFirstCI? rest " with " then
      if let some symPart := dropSuffixCI? rhs " mana symbols among their mana costs" then
        if let some (nStr, colStr) := splitFirstCI? symPart " or more " then
          if let some n := parseNatWord? nStr then
            let col? := parseColorWord? colStr
            let pred :=
              match col? with
              | some col => ObjectPred.all #[.hasColor (.literal col), .isKind .card]
              | none => .isKind .card
            let zones : ZoneSetSpec :=
              if (lower lhs).contains "graveyard" then .yourGraveyard
              else if (lower lhs).contains "hand" then .yourHand
              else .battlefield
            return some (.exile (.totalManaSymbolsAtLeast col? (.const n)) zones (.filter pred) false)
    if isSelfObjectPhrase rest then
      return some (.exile (.exact 1) .battlefield .self false)
    if let some np := parseNounPhrase rest then
      if !np.isTarget then
        if let some cnt := nounQuantToCostCount np.quantifier then
          return some (.exile cnt np.filter.zones (.filter np.filter.pred) false)

  -- 11. Tap objects (including Crew / Teamwork total power)
  if let some rest := dropPrefixCI? s "tap " then
    let lowRest := lower rest
    if let some (objStr, powStr) := splitFirstCI? lowRest " with total power " then
      if let some nStr := dropSuffixCI? powStr " or more" then
        if let some n := parseNatWord? nStr then
          let isOther := objStr.contains "other "
          let basePred : ObjectPred :=
            if isOther then
              .all #[.otherThan .this, .hasType .creature, .tapped false, .controlledBy .you]
            else
              .all #[.hasType .creature, .tapped false, .controlledBy .you]
          return some (.tapObjects (.totalPowerAtLeast (.const n)) basePred)
    if lowRest == "an untapped creature you control" then
      return some (.tapObjects (.exact 1) (.all #[.hasType .creature, .tapped false, .controlledBy .you]))
    if lowRest == "two untapped artifacts you control" then
      return some (.tapObjects (.exact 2) (.all #[.hasType .artifact, .tapped false, .controlledBy .you]))
    if let some np := parseNounPhrase rest then
      if !np.isTarget then
        if let some cnt := nounQuantToCostCount np.quantifier then
          return some (.tapObjects cnt np.filter.pred)

  -- 12. Return to hand (e.g., Sneak CR 702.190a)
  if let some rest := dropPrefixCI? s "return " then
    let objStr? :=
      (dropSuffixCI? rest " to its owner's hand").orElse fun _ =>
      (dropSuffixCI? rest " to their owners' hands").orElse fun _ =>
      (dropSuffixCI? rest " to your hand")
    if let some objStr := objStr? then
      if isSelfObjectPhrase objStr then
        return some (.returnToHand (.exact 1) .self)
      if lower objStr == "an unblocked attacking creature you control" then
        return some (.returnToHand (.exact 1) (.filter (.all #[
          .hasType .creature, .combatRole .unblocked, .controlledBy .you
        ])))
      if let some np := parseNounPhrase objStr then
        if !np.isTarget then
          if let some cnt := nounQuantToCostCount np.quantifier then
            return some (.returnToHand cnt (.filter np.filter.pred))

  return none

/-- Parse a compositional `CostSpec` (comma-separated items, `"sacrifice this and ..."`,
and top-level `"<costA> or <costB>"` choice combinators; CR 118). -/
partial def parseCostSpec (raw : String) : Option CostSpec := Id.run do
  let s := stripTrailingPeriod (stripReminderText raw)
  if s.isEmpty then return none

  -- 1. Single atomic item first (keeps `"discard an enchantment, instant, or sorcery card"`
  --    and `"sacrifice an artifact or creature"` intact before splitting on `, ` / ` or `).
  if let some item := parseCostItem s then
    return some (CostSpec.ofItem item)

  -- 2. Top-level `" or "` combinator, trying split points right-to-left so
  --    `"sacrifice an artifact or creature or pay {4}"` splits as
  --    `("sacrifice an artifact or creature", "pay {4}")`.
  let orSplits := splitAllCI s " or "
  for idx in [0 : orSplits.size] do
    let (lhs, rhs) := orSplits[orSplits.size - 1 - idx]!
    if let some c1 := parseCostSpec lhs then
      if let some c2 := parseCostSpec rhs then
        let choices :=
          match c1.items.toList with
          | [.or xs] => xs.push c2
          | _ => #[c1, c2]
        return some (CostSpec.ofItem (.or choices))

  -- 3. Merged `"sacrifice <self> and <other>"` (e.g. `"sacrifice ~ and a legendary artifact"`).
  if let some rest := dropPrefixCI? s "sacrifice " then
    if let some (lhs, rhs) := splitFirstCI? rest " and " then
      if let some (cnt1, w1) := parseSacrificePhrase? lhs then
        if let some (cnt2, w2) := parseSacrificePhrase? rhs then
          return some (CostSpec.ofItems #[.sacrifice cnt1 w1, .sacrifice cnt2 w2])

  -- 4. Comma-separated cost items (`"{1}{B}, {T}, Sacrifice a creature"`).
  let parts := (s.splitOn ",").map (fun p => p.trimAscii.copy) |>.filter (!·.isEmpty)
  if parts.length ≥ 2 then
    let mut items : Array CostItem := #[]
    let mut ok := true
    for part in parts do
      match parseCostSpec part with
      | some sub => items := items ++ sub.items
      | none =>
        ok := false
        break
    if ok && !items.isEmpty then
      return some { items }

  return none

end

/-- Parse an Oracle `"As an additional cost to cast this spell, [you may] <cost>."`
line into an `AdditionalCostSpec` (CR 118.8 / 601.2b,f,h). -/
def parseAdditionalCostSpec (raw : String) : Option AdditionalCostSpec := Id.run do
  let s := stripTrailingPeriod (stripReminderText raw)
  let some body := dropPrefixCI? s "as an additional cost to cast this spell, " | return none
  if let some optBody := dropPrefixCI? body "you may " then
    if let some cost := parseCostSpec optBody then
      return some (AdditionalCostSpec.opt cost)
  if let some cost := parseCostSpec body then
    return some (AdditionalCostSpec.mandatory cost)
  return none

/-- Parse `"hexproof from <quality>"` quality filter (CR 702.11d). -/
def parseQualityFilter? (raw : String) : Option QualityFilter := Id.run do
  let s := stripTrailingPeriod (cleanClause raw)
  let lowS := lower s
  if lowS == "multicolored" then return some .multicolored
  if lowS == "the chosen color" then return some (.color .chosenOnSource)
  if let some col := parseColorWord? lowS then return some (.color (.literal col))
  if let some ct := CardType.ofOracle? lowS then return some (.cardType ct)
  if let some sub := CardSubtype.ofOracle? s then return some (.subtype (.literal sub))
  if let some np := parseNounPhrase s then
    return some (.objectPred np.filter.pred)
  return none

/-- Parse one `"protection from <quality>"` quality (CR 702.16). -/
def parseProtectionQuality? (raw : String) : Option ProtectionQuality := Id.run do
  let s := stripTrailingPeriod (cleanClause raw)
  let lowS := lower s
  if lowS == "everything" then return some .everything
  if lowS == "all colors" then return some .allColors
  if lowS == "colorless" then return some .colorless
  if lowS == "the chosen card type" then return some .chosenCardType
  if lowS == "the chosen color" then return some (.color .chosenOnSource)
  if lowS == "the chosen type" then return some (.subtype .chosenOnSource)
  if let some col := parseColorWord? lowS then return some (.color (.literal col))
  if let some ct := CardType.ofOracle? lowS then return some (.cardType ct)
  if let some sub := CardSubtype.ofOracle? s then return some (.subtype (.literal sub))
  if let some np := parseNounPhrase s then
    return some (.quality np.filter.pred)
  return none

/-- Parse a single keyword ability phrase into `KeywordAbility` (CR 702).
Never accepts `"can't be blocked"` (CR 509.1b — a static ability, not a keyword). -/
def parseKeywordAbility (raw : String) : Option KeywordAbility := Id.run do
  let s := stripTrailingPeriod (stripReminderText raw)
  if s.isEmpty then return none
  let lowS := lower s

  -- 1. All 29 parameter-free `SimpleKeyword`s.
  if let some sk := SimpleKeyword.ofName? lowS then
    return some (.simple sk)

  -- 2. Hexproof / Hexproof from [quality] (CR 702.11 / 702.11d).
  if lowS == "hexproof" then
    return some (.hexproof none)
  if let some qStr := dropPrefixCI? s "hexproof from " then
    if let some q := parseQualityFilter? qStr then
      return some (.hexproof (some q))

  -- 3. Ward [cost] / Ward—[cost] (CR 702.21).
  if let some rest := (dropPrefixCI? s "ward—").orElse (fun _ =>
      (dropPrefixCI? s "ward - ").orElse (fun _ => dropPrefixCI? s "ward ")) then
    if let some cost := parseCostSpec rest then
      return some (.ward cost)

  -- 4. Protection from [quality] (CR 702.16).
  if let some qStr := dropPrefixCI? s "protection from " then
    if !((lower qStr).contains " and ") then
      if let some q := parseProtectionQuality? qStr then
        return some (.protection q)

  -- 5. Landwalk variants (CR 702.14).
  if lowS == "nonbasic landwalk" then
    return some (.landwalk (.all #[.not (.hasSupertype .basic), .hasType .land]))
  if lowS == "legendary landwalk" then
    return some (.landwalk (.all #[.hasSupertype .legendary, .hasType .land]))
  if lowS == "snow landwalk" then
    return some (.landwalk (.all #[.hasSupertype .snow, .hasType .land]))
  if lowS.endsWith "walk" && lowS.length > 4 then
    let stem := (s.dropEnd 4).copy.trimAscii.copy
    if let some sub := CardSubtype.ofOracle? stem then
      return some (.landwalk (.hasSubtype (.literal sub)))

  -- 6. Toxic N (CR 702.164).
  if let some nStr := dropPrefixCI? lowS "toxic " then
    if let some n := parseNatWord? nStr then
      return some (.toxic n)

  -- 7. Crew N (CR 702.122).
  if let some nStr := dropPrefixCI? lowS "crew " then
    if let some n := parseNatWord? nStr then
      return some (.crew n)

  -- 8. Teamwork N (CR 702.194).
  if let some nStr := dropPrefixCI? lowS "teamwork " then
    if let some n := parseNatWord? nStr then
      return some (.teamwork n)

  -- 9. Affinity for [filter] (CR 702.41).
  if let some forStr := dropPrefixCI? s "affinity for " then
    let cleanFor := stripTrailingPeriod forStr
    let lowFor := lower cleanFor
    if let some ct := CardType.ofOracle? lowFor then
      return some (.affinity {
        zones := .battlefield
        pred := .all #[.hasType ct, .controlledBy .you]
      })
    if let some sub := CardSubtype.ofOracle? cleanFor then
      return some (.affinity {
        zones := .battlefield
        pred := .all #[.hasSubtype (.literal sub), .controlledBy .you]
      })
    if let some np := parseNounPhrase cleanFor then
      let pred :=
        match np.filter.pred with
        | .all ps =>
          if ps.any (fun | .controlledBy _ => true | _ => false) then np.filter.pred
          else .all (ps.push (.controlledBy .you))
        | other => .all #[other, .controlledBy .you]
      return some (.affinity { zones := .battlefield, pred })

  -- 10. Gift [kind] (CR 702.174).
  if let some giftStr := dropPrefixCI? s "gift " then
    if let some kind := GiftKind.ofOracle? giftStr then
      return some (.gift kind)

  -- 11. Kicker [cost] / Kicker—[cost] (CR 702.33).
  if let some rest := (dropPrefixCI? s "kicker—").orElse (fun _ =>
      (dropPrefixCI? s "kicker - ").orElse (fun _ => dropPrefixCI? s "kicker ")) then
    if let some cost := parseCostSpec rest then
      return some (.kicker cost)

  -- 12. Flashback [cost] / Flashback—[cost] (CR 702.34).
  if let some rest := (dropPrefixCI? s "flashback—").orElse (fun _ =>
      (dropPrefixCI? s "flashback - ").orElse (fun _ => dropPrefixCI? s "flashback ")) then
    if let some cost := parseCostSpec rest then
      return some (.flashback cost)

  -- 13. Morph [cost] / Morph—[cost] (CR 702.37).
  if let some rest := (dropPrefixCI? s "morph—").orElse (fun _ =>
      (dropPrefixCI? s "morph - ").orElse (fun _ => dropPrefixCI? s "morph ")) then
    if let some cost := parseCostSpec rest then
      return some (.morph cost)

  -- 14. Impending N—[cost] (CR 702.176).
  if let some rest := dropPrefixCI? s "impending " then
    let split? := (splitFirstCI? rest "—").orElse fun _ => splitFirstCI? rest " - "
    if let some (nStr, costStr) := split? then
      if let some n := parseNatWord? nStr then
        if let some cost := parseCostSpec costStr then
          return some (.impending n cost)

  -- 15. Sneak [cost] / Sneak—[cost] (CR 702.190).
  if let some rest := (dropPrefixCI? s "sneak—").orElse (fun _ =>
      (dropPrefixCI? s "sneak - ").orElse (fun _ => dropPrefixCI? s "sneak ")) then
    if let some cost := parseCostSpec rest then
      return some (.sneak cost)

  -- 16. Cycling / [Type]cycling [cost] (CR 702.29).
  if let some rest := (dropPrefixCI? s "cycling—").orElse (fun _ =>
      (dropPrefixCI? s "cycling - ").orElse (fun _ => dropPrefixCI? s "cycling ")) then
    if let some cost := parseCostSpec rest then
      return some (.cycling none cost)
  if let some (lhs, rhs) := splitFirstCI? s "cycling " then
    let qual := lhs.trimAscii.copy
    if !qual.isEmpty then
      if let some cost := parseCostSpec rhs then
        let filter? : Option ObjectPred :=
          if lower qual == "basic land" then
            some (.all #[.hasSupertype .basic, .hasType .land])
          else if let some sub := CardSubtype.ofOracle? qual then
            some (.hasSubtype (.literal sub))
          else if let some ct := CardType.ofOracle? (lower qual) then
            some (.hasType ct)
          else none
        if let some f := filter? then
          return some (.cycling (some f) cost)

  -- 17. Equip [quality] [cost] (CR 702.6).
  if let some rest := (dropPrefixCI? s "equip—").orElse (fun _ => dropPrefixCI? s "equip - ") then
    if let some cost := parseCostSpec rest then
      return some (.equip (.all #[.hasType .creature, .controlledBy .you]) cost)
  if let some rest := dropPrefixCI? s "equip " then
    if let some cost := parseCostSpec rest then
      return some (.equip (.all #[.hasType .creature, .controlledBy .you]) cost)
    -- `"equip <subtype/quality> <cost>"` (e.g. `"Equip Soldier {1}"`, `"Equip legendary creature {2}"`)
    let ws := splitWords rest
    if ws.size ≥ 2 then
      -- Find rightmost suffix starting with `{` or em-dash.
      let mut splitAt? : Option Nat := none
      for i in [1 : ws.size] do
        if ws[i]!.startsWith "{" then
          splitAt? := some i
          break
      if let some idx := splitAt? then
        let qualStr := String.intercalate " " (ws.extract 0 idx).toList
        let costStr := String.intercalate " " (ws.extract idx ws.size).toList
        if let some cost := parseCostSpec costStr then
          if let some sub := CardSubtype.ofOracle? qualStr then
            return some (.equip (.all #[.hasSubtype (.literal sub), .hasType .creature, .controlledBy .you]) cost)
          if let some np := parseNounPhrase qualStr then
            return some (.equip (.all #[np.filter.pred, .controlledBy .you]) cost)

  return none

/-- Parse a single keyword line (e.g., `"Flying, vigilance"`, `"Prowess, prowess"`,
`"Flying, protection from white and from black"`, `"Ward—Discard a card or pay {2}."`)
into an array of `KeywordAbility`s, retaining multiplicity for cumulative keywords.
Returns `none` if any clause on the line is not a keyword ability. -/
def parseKeywordLine (raw : String) : Option (Array KeywordAbility) := Id.run do
  let s := stripTrailingPeriod (stripReminderText raw)
  if s.isEmpty then return none

  -- Single keyword first (handles commas inside `"Ward—Discard an enchantment, instant, or sorcery card."`
  -- or `"Flashback—{1}{B}, Discard a card."`).
  if let some kw := parseKeywordAbility s then
    return some #[kw]

  -- Split top-level on `";"` then `","`, supporting `"protection from X and from Y"` per segment.
  let semiParts := (s.splitOn ";").map (fun p => p.trimAscii.copy) |>.filter (!·.isEmpty)
  let mut out : Array KeywordAbility := #[]
  for semi in semiParts do
    if let some kw := parseKeywordAbility semi then
      out := out.push kw
    else
      let commaParts := (semi.splitOn ",").map (fun p => p.trimAscii.copy) |>.filter (!·.isEmpty)
      for part in commaParts do
        if let some kw := parseKeywordAbility part then
          out := out.push kw
        else if let some qRest := dropPrefixCI? part "protection from " then
          let pieces := (qRest.replace " and from " " and ").splitOn " and "
          let mut parsedAny := false
          for piece in pieces do
            match parseProtectionQuality? piece with
            | some q =>
              out := out.push (.protection q)
              parsedAny := true
            | none => return none
          if !parsedAny then return none
        else
          return none
  if out.isEmpty then return none else return some out

end Mtg.Engine.Parser
