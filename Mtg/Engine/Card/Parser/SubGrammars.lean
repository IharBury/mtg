import Mtg.Engine.Card.ActivatedAbility
import Mtg.Engine.Card.Cost
import Mtg.Engine.Card.Expr
import Mtg.Engine.Card.Keywords
import Mtg.Engine.Card.ManaSpec
import Mtg.Engine.Card.OracleNorm
import Mtg.Engine.Card.Parser.Lexer
import Mtg.Engine.Card.StaticAbility
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
  | "thirty" => some 30
  | "forty" => some 40
  | "fifty" => some 50
  | "sixty" => some 60
  | "seventy" => some 70
  | "eighty" => some 80
  | "ninety" => some 90
  | s =>
    if !s.isEmpty && s.all Char.isDigit then s.toNat?
    else
      match s.splitOn "-" with
      | [tensStr, onesStr] =>
        let tens? : Option Nat :=
          match tensStr with
          | "twenty" => some 20 | "thirty" => some 30 | "forty" => some 40
          | "fifty" => some 50 | "sixty" => some 60 | "seventy" => some 70
          | "eighty" => some 80 | "ninety" => some 90 | _ => none
        let ones? : Option Nat :=
          match onesStr with
          | "one" => some 1 | "two" => some 2 | "three" => some 3
          | "four" => some 4 | "five" => some 5 | "six" => some 6
          | "seven" => some 7 | "eight" => some 8 | "nine" => some 9 | _ => none
        match tens?, ones? with
        | some t, some o => some (t + o)
        | _, _ => none
      | _ => none

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
  else if let some rest := dropPrefixCI? s "greater than or equal to " then
    (parseValueExpr rest).map (.ge, ·)
  else if let some rest := dropPrefixCI? s "less than or equal to " then
    (parseValueExpr rest).map (.le, ·)
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
  else if low == "equal or lesser mana value than that spell" || low == "mana value less than or equal to that spell's mana value" then
    some (.stat .manaValue .le (.objectStat .manaValue .triggerSubject))
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
  else if low == "is this permanent" || low == "is this creature" || low == "is this" then
    some (.sameAs .this)
  else if low == "is that object" || low == "is that creature" || low == "is that permanent" then
    some (.sameAs .triggerSubject)
  else if low == "was put there from the battlefield this turn" ||
      low == "were put there from the battlefield this turn" then
    some .putIntoGraveyardFromBattlefieldThisTurn
  else if low == "was put there from anywhere this turn" ||
      low == "were put there from anywhere this turn" then
    some .anyObject
  else if let some zStr := (dropPrefixCI? s "was cast from ").orElse (fun _ => dropPrefixCI? s "were cast from ") then
    (parseZoneKind? zStr).map ObjectPred.castFrom
  else if low == "entered this turn" || low == "entered the battlefield this turn" then
    some .enteredThisTurn
  else if low == "attacked this turn" then
    some .attackedThisTurn
  else if low == "'s attacking alone" || low == "is attacking alone" then
    some (.combatRole .attackingAlone)
  else if low == "dealt damage this turn" then
    some (.dealtDamageThisTurn false none true)
  else if low == "dealt damage" then
    some (.dealtDamageThisTurn false none false)
  else if low == "dealt combat damage this turn" then
    some (.dealtDamageThisTurn true none true)
  else if low == "dealt combat damage" then
    some (.dealtDamageThisTurn true none false)
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
  else if let some (baseStr, predStr) := splitFirstCI? s " matching " then
    match parseObjectExpr? baseStr, parseNounPhrase predStr with
    | some b, some np => some (.filter b np.filter.pred)
    | _, _ => none
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
        if !(lower rhs == "it" && (lower lhs).contains " with ") then
          if let some host := parseObjectExpr? rhs then
            extraPreds := #[.attachedTo host] ++ extraPreds; s := lhs; progress := true
    if !progress then
      if let some (lhs, rhs) := splitLastCI? s " named " then
        if !rhs.isEmpty then
          extraPreds := #[.named (.literal rhs)] ++ extraPreds; s := lhs; progress := true
    if !progress then
      if let some pre := dropSuffixCI? s " other than enchanted creature" then
        extraPreds := #[.otherThan .attachedHost] ++ extraPreds; s := pre; progress := true
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
      else if let some pre := (dropSuffixCI? s " in your opponents' graveyards").orElse
          (fun _ => (dropSuffixCI? s " from your opponents' graveyards").orElse
            (fun _ => (dropSuffixCI? s " in opponents' graveyards").orElse
              (fun _ => (dropSuffixCI? s " from opponents' graveyards").orElse
                (fun _ => (dropSuffixCI? s " in opponents graveyards").orElse
                  (fun _ => dropSuffixCI? s " from opponents graveyards"))))) then
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
      else if let some pre := (dropSuffixCI? s " in their hand").orElse
          (fun _ => dropSuffixCI? s " from their hand") then
        zones := { zones := #[.hand], owner := .matching .thatPlayer }
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
    -- Suffixes: `"whose chosen option is <X>"`, `"of their choice"`
    if !progress then
      if let some (lhs, anchor) := splitLastCI? s " whose chosen option is " then
        extraPreds := extraPreds.push (.chosenAnchorIs (cleanClause anchor)); s := lhs; progress := true
      else if let some pre := dropSuffixCI? s " of their choice" then
        s := pre; progress := true
    -- Controller / owner suffixes (`you control`, `an opponent controls`, `defending player controls`, ...)
    if !progress && ctrlPreds.isEmpty then
      if let some pre := dropSuffixCI? s " you own and control" then
        ctrlPreds := ctrlPreds.push (.ownedBy .you) |>.push (.controlledBy .you); s := pre; progress := true
      else if let some pre := dropSuffixCI? s " you control" then
        ctrlPreds := ctrlPreds.push (.controlledBy .you); s := pre; progress := true
      else if let some pre := dropSuffixCI? s " an opponent controls" then
        ctrlPreds := ctrlPreds.push (.controlledBy .opponent); s := pre; progress := true
      else if let some pre := dropSuffixCI? s " your opponents control" then
        ctrlPreds := ctrlPreds.push (.controlledBy .opponent); s := pre; progress := true
      else if let some pre := dropSuffixCI? s " opponents control" then
        ctrlPreds := ctrlPreds.push (.controlledBy .opponent); s := pre; progress := true
      else if let some pre := (dropSuffixCI? s " the defending player controls").orElse
          (fun _ => dropSuffixCI? s " defending player controls") then
        ctrlPreds := ctrlPreds.push (.controlledBy .defendingPlayer); s := pre; progress := true
      else if let some pre := (dropSuffixCI? s " the active player controls").orElse
          (fun _ => dropSuffixCI? s " active player controls") then
        ctrlPreds := ctrlPreds.push (.controlledBy { relation := .anyPlayer, pred := .matchesExpr .activePlayer }); s := pre; progress := true
      else if let some pre := dropSuffixCI? s " target player controls" then
        ctrlPreds := ctrlPreds.push (.controlledBy { relation := .anyPlayer, pred := .matchesExpr (.target 0) }); s := pre; progress := true
      else if let some pre := dropSuffixCI? s " target opponent controls" then
        ctrlPreds := ctrlPreds.push (.controlledBy { relation := .anyPlayer, pred := .matchesExpr (.target 0) }); s := pre; progress := true
      else if let some pre := dropSuffixCI? s " that player controls" then
        ctrlPreds := ctrlPreds.push (.controlledBy .thatPlayer); s := pre; progress := true
      else if let some pre := dropSuffixCI? s " they control" then
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
  s := (dropPrefixCI? s "each of ").getD s
  let mut toks := (splitWords s).map fun w => if w.endsWith "," then (w.dropEnd 1).copy else w
  if toks.isEmpty then return none
  let mut idx : Nat := 0
  let mut quant : NounQuantifier := .singular
  let mut hasExplicitQuant := false
  let w0 := lower toks[0]!
  if w0 == "any" && toks.size ≥ 3 && lower toks[1]! == "number" && lower toks[2]! == "of" then
    quant := .anyNumber; hasExplicitQuant := true; idx := 3
  else if w0 == "up" && toks.size ≥ 4 && lower toks[1]! == "to" && lower toks[2]! == "that" && lower toks[3]! == "many" then
    quant := .anyNumber; hasExplicitQuant := true; idx := 4
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
        (i + 1 < toks.size && (lower toks[i + 1]! == "or" || lower toks[i + 1]! == "and/or" ||
          (lower toks[i + 1]! == "and" && i + 2 < toks.size &&
            ((CardType.ofOracle? (stripTrailingComma toks[i + 2]!)).isSome ||
             (CardSubtype.ofOracle? (stripTrailingComma toks[i + 2]!)).isSome)))))

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
      if wl == "or" || wl == "and/or" || wl == "and" then
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
        else if ((parseNonSubtype? w).isSome || (parseNonCardType? w).isSome) &&
            k + 1 < toks.size && (CardType.ofOracle? (stripTrailingComma toks[k + 1]!)).isSome then
          k := k + 2
        else return false
    return false

  while idx < toks.size do
    let rawTok := stripTrailingComma toks[idx]!
    let tok := lower rawTok
    if tok == "or" || tok == "and/or" ||
        (tok == "and" && !headChoices.isEmpty && isHeadListWord toks (idx + 1) > 0) then
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
      let isOrChainMod :=
        (inOrChain || headContinuesOr toks idx) &&
          ((parseNonSubtype? rawTok).isSome || (parseNonCardType? rawTok).isSome)
      if !isSubtypeHere && !isOrChainMod then
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
      else if tok == "nonattacking" then
        preds := preds.push (.not (.combatRole .attacking)); sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "equipped" then
        preds := preds.push (.hasAttachment { zones := .battlefield, pred := .hasSubtype (.literal .equipment) }); sawAnyNounOrMod := true; idx := idx + 1
      else if tok == "enchanted" then
        preds := preds.push (.hasAttachment { zones := .battlefield, pred := .hasSubtype (.literal .aura) }); sawAnyNounOrMod := true; idx := idx + 1
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
        let threeWord? : Option CardSubtype :=
          if idx + 2 < toks.size then
            CardSubtype.ofOracle? s!"{rawTok} {toks[idx + 1]!} {stripTrailingComma toks[idx + 2]!}"
          else none
        match threeWord? with
        | some sub =>
          let threeRaw := lower s!"{rawTok} {toks[idx + 1]!} {stripTrailingComma toks[idx + 2]!}"
          if threeRaw == lower sub.pluralName && threeRaw != lower sub.englishName then
            sawPluralHead := true
          let hasMore := headContinuesOr toks (idx + 2)
          if inOrChain || hasMore || !headChoices.isEmpty then
            headChoices := headChoices.push (.hasSubtype (.literal sub))
            if !hasMore then
              (preds, headChoices) := flushHeads preds headChoices
          else
            preds := preds.push (.hasSubtype (.literal sub))
          inOrChain := false; sawAnyNounOrMod := true; idx := idx + 3
        | none =>
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

  let predRank (p : ObjectPred) : Nat :=
    if p == ObjectPred.worthy then 8
    else if p == ObjectPred.historic then 7
    else
      match p with
      | .otherThan .this => 1
      | .tapped _ | .combatRole .attacking | .combatRole .blocking
      | .combatRole .blocked | .combatRole .unblocked
      | .isFaceDown _ | .isCommander
      | .hasDesignation .goaded | .hasDesignation .prepared | .hasDesignation .harnessed => 2
      | .any #[.combatRole .attacking, .combatRole .blocking] => 2
      | .colorCount .eq 0 | .colorCount .eq 1 | .colorCount .ge 2 => 3
      | .not (.hasType _) => 4
      | .isToken false => 5
      | .hasColor (.literal _) | .not (.hasColor (.literal _)) => 6
      | .any xs =>
        if !xs.isEmpty && xs.all (fun | .hasColor (.literal _) => true | _ => false) then 6
        else if !xs.isEmpty && xs.all (fun | .hasSubtype (.literal _) => true | _ => false) then 8
        else if xs.size == 2 &&
            (match xs[0]!, xs[1]! with
             | .stat .power _ _, .stat .toughness _ _ => true
             | _, _ => false) then 12
        else 9
      | .hasSupertype _ | .not (.hasSupertype _) => 7
      | .hasSubtype (.literal _) | .not (.hasSubtype (.literal _)) => 8
      | .hasType _ => 9
      | .isKind _ | .isToken true => 10
      | .controlledBy _ | .ownedBy _ => 11
      | .hasKeyword _ | .stat _ _ _ | .statParity _ _
      | .counterCount _ _ _ | .hasAttachment _ => 12
      | .not (.hasKeyword _) => 13
      | _ => 14
  let rawAllPreds := preds ++ ctrlPreds ++ extraPreds
  let allPreds : Array ObjectPred := Id.run do
    let mut out : Array ObjectPred := #[]
    for item in rawAllPreds do
      let r := predRank item
      let mut pos := out.size
      while pos > 0 && predRank out[pos - 1]! > r do
        pos := pos - 1
      out := out.insertIdx! pos item
    return out
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
  if low == "the number of cards moved this way" || low == "the number of cards drawn this way" ||
      low == "the number of creatures returned to your hand this way" ||
      low == "the number of cards exiled this way" then
    return some (.stepMetric .movedCount ⟨0⟩)
  if low == "the number of tokens created this way" then
    return some (.stepMetric .createdCount ⟨0⟩)
  if low == "the amount of damage dealt this way" then
    return some (.stepMetric .damageDealt ⟨0⟩)
  if low == "the excess damage dealt this way" || low == "that excess damage" then
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
  if let some rest := (dropPrefixCI? s "the number of cards that were put into ").orElse
      (fun _ => dropPrefixCI? s "the number of cards put into ") then
    if let some (whoPre, _) := splitFirstCI? rest "'s graveyard from " then
      if let some who := parsePlayerExpr? whoPre then
        return some (.playerMetric .cardsMilledThisTurn who)
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
  if let some rest := (dropPrefixCI? s "the amount of life ").orElse
      (fun _ => dropPrefixCI? s "the life ") then
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

  let (body0, isLastTurn) ←
    match dropSuffixCI? s " last turn" with
    | some b => (b, true)
    | none =>
      match dropSuffixCI? s " this turn" with
      | some b => (b, false)
      | none => return none
  let body :=
    let b1 :=
      match dropPrefixCI? body0 "you've " with
      | some r => "you " ++ r
      | none =>
        match dropPrefixCI? body0 "you have " with
        | some r => "you " ++ r
        | none => body0
    b1.replace " drawn " " drew "
  let wrap (who : PlayerFilter) (pat : EventPattern) : EventHistoryPred :=
    if isLastTurn then .eventOccurredLastTurn who pat else .eventOccurredThisTurn who pat

  if let some npStr := dropSuffixCI? body " died" then
    if let some (cntStr, restNp) := splitFirstCI? npStr " or more " then
      match parseNatWord? cntStr, parseNounPhrase restNp with
      | some n, some np => return some (wrap .any (.permanentDied np.filter.pred n))
      | _, _ => pure ()
    return (parseNounPhrase npStr).map fun np => wrap .any (.permanentDied np.filter.pred 1)
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
    if let some pf := parsePlayerFilter? whoStr then
      if let some (cntStr, restNp) := splitFirstCI? npStr " or more " then
        match parseNatWord? cntStr, parseNounPhrase restNp with
        | some n, some np => return some (wrap pf (.attackedWith np.filter.pred n))
        | _, _ => pure ()
      if let some np := parseNounPhrase npStr then
        return some (wrap pf (.attackedWith np.filter.pred 1))
  if let some whoStr := dropSuffixCI? body " attacked" then
    if let some pf := parsePlayerFilter? whoStr then
      return some (wrap pf (.attackedWith .anyObject 1))

  if let some (whoStr, npStr) := splitFirstCI? body " cast " then
    match parsePlayerFilter? whoStr, parseNounPhrase npStr with
    | some pf, some np =>
      let sp := match np.filter.pred with
        | .isKind .spell => .anyObject
        | .all ps => ObjectPred.andAll (ps.filter (· != .isKind .spell))
        | other => other
      return some (wrap pf (.castSpell sp))
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

  for (sfx, combatOnly, noncombatOnly) in
      [(" were dealt combat damage", true, false),
       (" was dealt combat damage", true, false),
       (" has been dealt combat damage", true, false),
       (" have been dealt combat damage", true, false),
       (" were dealt noncombat damage", false, true),
       (" was dealt noncombat damage", false, true),
       (" has been dealt noncombat damage", false, true),
       (" have been dealt noncombat damage", false, true),
       (" were dealt damage", false, false),
       (" was dealt damage", false, false),
       (" has been dealt damage", false, false),
       (" have been dealt damage", false, false)] do
    if let some whoStr := dropSuffixCI? body sfx then
      if let some pf := parsePlayerFilter? whoStr then
        return some (wrap pf (.dealtDamage combatOnly noncombatOnly))

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

  let low0 := lower s
  -- Combined scry/surveil idiom before generic `" or "` splitting.
  if low0 == "you've scried or surveilled this turn" ||
      low0 == "you have scried or surveilled this turn" then
    return some ActivatedAbility.condScriedOrSurveilledThisTurn

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

  -- Self entered this turn / attacked this turn / prepared / token / equipped / attacking.
  if low == "this land entered this turn" || low == "this permanent entered this turn" ||
      low == "this creature entered this turn" || low == "this entered this turn" ||
      low == "~ entered this turn" then
    return some (.all #[.exists .this, .forAll .this .enteredThisTurn])
  if low == "this creature attacked this turn" || low == "it attacked this turn" ||
      low == "~ attacked this turn" then
    return some ActivatedAbility.condSourceAttackedThisTurn
  if low == "this creature isn't prepared" || low == "this permanent isn't prepared" ||
      low == "it isn't prepared" then
    return some (.not (.exists (.filter .this (.hasDesignation .prepared))))
  if low == "it isn't a token" || low == "they're not a token" ||
      low == "this creature isn't a token" || low == "this permanent isn't a token" then
    return some (.not (.exists (.filter .this .isToken)))
  if low == "it's equipped" || low == "this creature is equipped" || low == "this permanent is equipped" then
    return some (.exists (.filter .this (.hasAttachment { zones := .battlefield, pred := .hasSubtype (.literal .equipment) })))
  if low == "it's attacking" || low == "this creature is attacking" || low == "this permanent is attacking" then
    return some (.exists (.filter .this (.combatRole .attacking)))
  if low == "it had counters on it" then
    return some (Condition.triggerSubjectMatches (.counterCount none .ge (.const 1)))
  if low == "this permanent has counters on it" || low == "this artifact has counters on it" ||
      low == "this creature has counters on it" then
    return some (Condition.thisMatches (.counterCount none .ge (.const 1)))
  if low == "your library has no cards in it" then
    return some (.cmp .eq (.playerMetric .librarySize .you) (.const 0))
  if low == "you didn't cast a spell this turn" then
    return some (.not (.turnHistory (.eventOccurredThisTurn .you (.castSpell .anyObject))))
  if low == "it has greater power or toughness than this permanent" ||
      low == "it has greater power or toughness than this creature" then
    return some (.all #[.exists .triggerSubject, .any #[
      .cmp .gt (.objectStat .power .triggerSubject) (.objectStat .power .this),
      .cmp .gt (.objectStat .toughness .triggerSubject) (.objectStat .toughness .this)
    ]])
  if let some rest := dropPrefixCI? s "you have fewer than " then
    if let some nStr := (dropSuffixCI? rest " cards in hand").orElse (fun _ => dropSuffixCI? rest " cards in your hand") then
      if let some n := parseNatWord? nStr then
        return some (.cmp .lt (.playerMetric .handSize .you) (.const (Int.ofNat n)))

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
  if low == "you cast it" || low == "you cast this spell" || low == "you cast this permanent" ||
      low == "you cast this creature" then
    return some (.all #[.exists .this, .forAll .this .wasCast])
  if low == "they were a creature" || low == "it was a creature" ||
      low == "this permanent was a creature" || low == "this creature was a creature" then
    return some (.exists (.filter .this (.hasType .creature)))
  if low == "this spell was kicked" || low == "it was kicked" then
    return some (.castPred (.wasKicked .this))
  if low == "the gift was promised" || low == "its gift was promised" then
    return some (.castPred (.giftPromised .this))
  if low == "its impending cost was paid" || low == "this permanent's impending cost was paid" then
    return some (.castPred (.impendingPaid .this))
  if low == "its teamwork cost was paid" || low == "teamwork was paid" ||
      low == "this spell was cast using teamwork" || low == "it was cast using teamwork" then
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
  if let some zStr0 := (dropPrefixCI? s "this spell was cast from ").orElse
      (fun _ => dropPrefixCI? s "it was cast from ") then
    let zStr :=
      (dropPrefixCI? zStr0 "a ").orElse (fun _ =>
      (dropPrefixCI? zStr0 "an ").orElse (fun _ =>
      (dropPrefixCI? zStr0 "your ").orElse (fun _ =>
      dropPrefixCI? zStr0 "the "))) |>.getD zStr0
    if let some z := parseZoneKind? zStr then
      return some (.castPred (.castFrom z .this))
  if low == "this spell wasn't cast from your hand" || low == "it wasn't cast from your hand" then
    return some (.not (.castPred (.castFrom .hand .this)))

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
    if let some atLeastRest := dropPrefixCI? rest "at least " then
      let aws := splitWords atLeastRest
      if aws.size >= 2 then
        if let some v := parseValueExpr aws[0]! then
          let npStr := String.intercalate " " (aws.extract 1 aws.size).toList
          if let some np := parseNounPhrase s!"{npStr} you control" then
            return some (.cmp .ge (.aggregate .count .one np.filter.toExpr) v)
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
    if let some (cntStr, tail) := splitFirstCI? rest " or more " then
      -- `"there are N or more <counter> counters among <objs>"`
      if let some (ctrStr, objsStr) := splitFirstCI? tail " counters among " then
        let ctrWords := (splitWords ctrStr).toList.map lower
        match parseValueExpr cntStr, CounterKind.ofPrefix ctrWords, parseObjectExpr? objsStr with
        | some v, some (k, consumed), some objs =>
          if consumed == ctrWords.length then
            return some (.cmp .ge (.aggregate .sum (.counterCount (some k)) objs) v)
        | _, _, _ => pure ()
      match parseValueExpr cntStr, parseNounPhrase tail with
      | some v, some np =>
        if np.filter.zones == .yourGraveyard &&
            (np.filter.pred == .isKind .card || np.filter.pred == .anyObject) then
          return some (.cmp .ge (.playerMetric .graveyardSize .you) v)
        return some (.cmp .ge (.aggregate .count .one np.filter.toExpr) v)
      | _, _ => pure ()
    if let some np := parseNounPhrase rest then
      return some (.exists np.filter.toExpr)
  if let some rest := dropPrefixCI? s "there is " then
    let restNorm := (dropPrefixCI? rest "an another ").map ("another " ++ ·) |>.getD rest
    if let some oe := parseObjectExpr? restNorm then
      return some (.exists oe)
    if let some np := parseNounPhrase restNorm then
      return some (.exists np.filter.toExpr)
  if let some rest := dropPrefixCI? s "every " then
    if let some (objStr, predStr) := splitFirstCI? rest " is " then
      match parseObjectExpr? objStr, parseNounPhrase predStr with
      | some objs, some np => return some (.forAll objs np.filter.pred)
      | _, _ => pure ()
  -- `"not (<cond>)"` from canonical `Expr.toOracle`
  if let some inner := dropPrefixCI? s "not (" then
    if let some core := dropSuffixCI? inner ")" then
      if let some c := parseCondition core then
        return some (.not c)
  -- `"<obj> has no <k> counters on it"` / `"<obj> has N or more <k> counters on it"`
  if let some (objStr, ctrRest) := splitFirstCI? s " has " then
    if let some core := (dropSuffixCI? ctrRest " on it").orElse (fun _ => some ctrRest) then
      let ol := lower objStr
      let isSelfOrIt := ol == "this" || ol == "it" || ol.startsWith "this "
      if let some noRest := dropPrefixCI? core "no " then
        let cWords := (splitWords ((dropSuffixCI? noRest " counters").orElse (fun _ => dropSuffixCI? noRest " counter") |>.getD noRest)).toList.map lower
        let kind? := (CounterKind.ofPrefix cWords).map Prod.fst
        let obj? := if isSelfOrIt then some ObjectExpr.this else parseObjectExpr? objStr
        if let some obj := obj? then
          if obj == .this && kind?.isSome then
            return some (.all #[.exists .this, .cmp .eq (.counterCount kind? .this) (.const 0)])
          return some (.cmp .eq (.counterCount kind? obj) (.const 0))
      if let some (nStr, kRest) := splitFirstCI? core " or more " then
        if let some n := parseNatWord? nStr then
          let cWords := (splitWords ((dropSuffixCI? kRest " counters").orElse (fun _ => dropSuffixCI? kRest " counter") |>.getD kRest)).toList.map lower
          let kind? := (CounterKind.ofPrefix cWords).map Prod.fst
          let obj? := if isSelfOrIt then some ObjectExpr.this else parseObjectExpr? objStr
          if let some obj := obj? then
            return some (.cmp .ge (.counterCount kind? obj) (.const (Int.ofNat n)))

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
  if w0 == "up" && toks.size >= 4 && lower toks[1]! == "to" && lower toks[2]! == "that" && lower toks[3]! == "many" then
    let rest := String.intercalate " " (toks.toList.drop 4)
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
  else if let some (a, b) := splitFirstCI? s " of each card type " then
    gc? := some .distinctCardTypes; s := a ++ " " ++ b

  let mkSlot (domain : TargetDomain) (count : CountRange) : TargetSlot :=
    let count :=
      if gc? == some .distinctCardTypes && count == .upTo 1 then .upTo 8
      else count
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
        atLow == "creature or creature card from a graveyard" ||
        atLow == "creature on the battlefield or creature card in a graveyard" then
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

/-- Longest prefix of normalized Oracle tokens that parses as a `TargetSpec`
via the compositional Stage-4 target grammar. -/
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

/-- Strip balanced parenthetical CR 207.2a reminder text `(...)` (whose first non-space
char is uppercase, `{`, or empty) while preserving lowercase semantic annotations emitted
by `ToOracle` (`not (you do)`, `(chosen)`, `(move the rest)`, `(reveal first)`, `(s)`). -/
def stripReminderText (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out : Array Char := #[]
  let mut i : Nat := 0
  while i < cs.size do
    if cs[i]! == '(' then
      let mut j := i + 1
      let mut depth : Nat := 1
      let mut firstNonSpace? : Option Char := none
      while j < cs.size && depth > 0 do
        let ch := cs[j]!
        if firstNonSpace?.isNone && ch != ' ' then
          firstNonSpace? := some ch
        if ch == '(' then depth := depth + 1
        else if ch == ')' then depth := depth - 1
        j := j + 1
      let isSemanticLower :=
        match firstNonSpace? with
        | some ch => ch.isLower
        | none => false
      if isSemanticLower then
        for k in [i : j] do
          out := out.push cs[k]!
      i := j
    else
      out := out.push cs[i]!
      i := i + 1
  -- Collapse redundant spaces introduced around stripped parentheses.
  let raw := (String.ofList out.toList).trimAscii.copy
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
  | "this vehicle" | "this aura" | "this card" | "this spell" | "this saga"
  | "this token" => true
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
      if lower amtStr == "that amount" || lower amtStr == "that much" then
        return some (.payLife .eventAmount)
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
    if lowRest == "this spell" then
      return some (.exile (.exact 1) .stack .self false)
    -- `"exile <N> card(s)/permanent(s) named <Name> from your graveyard"` (e.g. *Sphinx's Approach*)
    if let some preGy := dropSuffixCI? rest " from your graveyard" then
      if let some (headStr, nameStr) := splitFirstCI? preGy " named " then
        let hws := (headStr.splitOn " ").filter (!·.isEmpty)
        if hws.length == 2 then
          let nounLow := lower hws[1]!
          if nounLow == "card" || nounLow == "cards" || nounLow == "permanent" || nounLow == "permanents" then
            if let some n := parseNatWord? hws[0]! then
              return some (.exile (.count (.const n)) .yourGraveyard (.filter (.named (.literal nameStr.trimAscii.copy))) false)
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
    -- `"exile any number of <color> card(s) [from your graveyard] with N or more <color> mana symbols among their mana costs [from your graveyard]"`
    if let some (_, rhs0) := splitFirstCI? rest " with " then
      let rhs :=
        ((dropSuffixCI? rhs0 " from your graveyard").orElse fun _ =>
          (dropSuffixCI? rhs0 " from your hand").orElse fun _ => some rhs0) |>.getD rhs0
      if let some symPart := dropSuffixCI? rhs " mana symbols among their mana costs" then
        if let some (nStr, colStr) := splitFirstCI? symPart " or more " then
          if let some n := parseNatWord? nStr then
            let col? := parseColorWord? colStr
            let pred :=
              match col? with
              | some col => ObjectPred.all #[.hasColor (.literal col), .isKind .card]
              | none => .isKind .card
            let fullLow := lower rest
            let zones : ZoneSetSpec :=
              if fullLow.contains "graveyard" then .yourGraveyard
              else if fullLow.contains "hand" then .yourHand
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

  -- 3b. Merged `"exile <a> and <b>"` (e.g. `"exile this spell and four cards named Sphinx's Approach from your graveyard"`).
  if let some rest := dropPrefixCI? s "exile " then
    if let some (lhs, rhs) := splitFirstCI? rest " and " then
      if let some c1 := parseCostItem ("exile " ++ lhs) then
        if let some c2 := parseCostItem ("exile " ++ rhs) then
          return some (CostSpec.ofItems #[c1, c2])

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

  -- 1. All 29 parameter-free `SimpleKeyword`s, bare `hexproof`, and all inline
  -- landwalk variants (`<land-subtype>walk`, `nonbasic/legendary/snow landwalk`,
  -- CR 702.11 / 702.14). Delegating directly to `KeywordAbility.ofSimpleName?`
  -- keeps both entry points identical (canonical predicate order and `sub.kind == .land`).
  if let some kw := KeywordAbility.ofSimpleName? s then
    return some kw

  -- 2. Hexproof from [quality] (CR 702.11d).
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

  -- 5. Toxic N (CR 702.164).
  if let some nStr := dropPrefixCI? lowS "toxic " then
    if let some n := parseNatWord? nStr then
      return some (.toxic n)

  -- 6. Crew N (CR 702.122).
  if let some nStr := dropPrefixCI? lowS "crew " then
    if let some n := parseNatWord? nStr then
      return some (.crew n)

  -- 7. Teamwork N (CR 702.194).
  if let some nStr := dropPrefixCI? lowS "teamwork " then
    if let some n := parseNatWord? nStr then
      return some (.teamwork n)

  -- 8. Affinity for [filter] (CR 702.41).
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

  -- 9. Gift [kind] (CR 702.174).
  if let some giftStr := dropPrefixCI? s "gift " then
    if let some kind := GiftKind.ofOracle? giftStr then
      return some (.gift kind)

  -- 10. Kicker [cost] / Kicker—[cost] (CR 702.33).
  if let some rest := (dropPrefixCI? s "kicker—").orElse (fun _ =>
      (dropPrefixCI? s "kicker - ").orElse (fun _ => dropPrefixCI? s "kicker ")) then
    if let some cost := parseCostSpec rest then
      return some (.kicker cost)

  -- 11. Flashback [cost] / Flashback—[cost] (CR 702.34).
  if let some rest := (dropPrefixCI? s "flashback—").orElse (fun _ =>
      (dropPrefixCI? s "flashback - ").orElse (fun _ => dropPrefixCI? s "flashback ")) then
    if let some cost := parseCostSpec rest then
      return some (.flashback cost)

  -- 12. Morph [cost] / Morph—[cost] (CR 702.37).
  if let some rest := (dropPrefixCI? s "morph—").orElse (fun _ =>
      (dropPrefixCI? s "morph - ").orElse (fun _ => dropPrefixCI? s "morph ")) then
    if let some cost := parseCostSpec rest then
      return some (.morph cost)

  -- 13. Impending N—[cost] (CR 702.176).
  if let some rest := dropPrefixCI? s "impending " then
    let split? := (splitFirstCI? rest "—").orElse fun _ => splitFirstCI? rest " - "
    if let some (nStr, costStr) := split? then
      if let some n := parseNatWord? nStr then
        if let some cost := parseCostSpec costStr then
          return some (.impending n cost)

  -- 14. Sneak [cost] / Sneak—[cost] (CR 702.190).
  if let some rest := (dropPrefixCI? s "sneak—").orElse (fun _ =>
      (dropPrefixCI? s "sneak - ").orElse (fun _ => dropPrefixCI? s "sneak ")) then
    if let some cost := parseCostSpec rest then
      return some (.sneak cost)

  -- 15. Cycling / [Type]cycling [cost] (CR 702.29).
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
          else if let some sup := Supertype.ofOracle? (lower qual) then
            some (.hasSupertype sup)
          else if let some ct := CardType.ofOracle? (lower qual) then
            some (.hasType ct)
          else none
        if let some f := filter? then
          return some (.cycling (some f) cost)

  -- 16. Equip [quality] [cost] (CR 702.6).
  if let some rest := (dropPrefixCI? s "equip—").orElse (fun _ => dropPrefixCI? s "equip - ") then
    if let some cost := parseCostSpec rest then
      return some (.equip (.all #[.hasType .creature, .controlledBy .you]) cost)
  if let some rest := dropPrefixCI? s "equip " then
    if let some cost := parseCostSpec rest then
      return some (.equip (.all #[.hasType .creature, .controlledBy .you]) cost)
    -- `"equip <subtype/quality> <cost>"` or `"equip <subtype/quality>—<cost>"`
    -- (e.g. `"Equip Soldier {1}"`, `"Equip worthy {1}"`, `"Equip legendary creature {2}"`, `"Equip Soldier—Pay 2 life."`)
    let qualAndCost? : Option (String × String) :=
      match (splitFirstCI? rest "—").orElse (fun _ => splitFirstCI? rest " - ") with
      | some (q, c) => some (q, c)
      | none =>
        let ws := splitWords rest
        if ws.size ≥ 2 then Id.run do
          let mut splitAt? : Option Nat := none
          for i in [1 : ws.size] do
            if ws[i]!.startsWith "{" then
              splitAt? := some i
              break
          match splitAt? with
          | some idx =>
            let q := String.intercalate " " (ws.extract 0 idx).toList
            let c := String.intercalate " " (ws.extract idx ws.size).toList
            return some (q, c)
          | none => return none
        else none
    if let some (qualStr, costStr) := qualAndCost? then
      if let some cost := parseCostSpec costStr then
        if lower qualStr == "worthy" then
          return some (.equip ObjectPred.worthy cost)
        if let some sub := CardSubtype.ofOracle? qualStr then
          return some (.equip (.all #[.hasType .creature, .hasSubtype (.literal sub), .controlledBy .you]) cost)
        if let some np := parseNounPhrase qualStr then
          let pred :=
            match np.filter.pred with
            | .all ps =>
              if ps.any (fun | .controlledBy _ => true | _ => false) then np.filter.pred
              else .all (ps.push (.controlledBy .you))
            | other => .all #[other, .controlledBy .you]
          return some (.equip pred cost)

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

/-! ### Phase-5 Compositional Mana-Production & Mana-Ability Sub-Grammar (CR 106, 605) -/

/-- Parse a single mana-type symbol `{W}`, `{U}`, `{B}`, `{R}`, `{G}`, `{C}` from
the front of `s`. Rejects generic, hybrid, or `{X}` symbols. -/
def parseManaTypeSymbol? (s : String) : Option (ManaType × String) :=
  match parseManaSymbol? s with
  | some (.colored c, rest) => some (.colored c, rest)
  | some (.colorless, rest) => some (.colorless, rest)
  | _ => none

/-- Parse a contiguous sequence of one or more concrete mana symbols (`{G}`,
`{C}{C}`, `{W}{U}`, `{C}{C}{C}`). -/
def parseManaTypeSeq? (raw : String) : Option (Array ManaType) :=
  let s := raw.trimAscii.copy
  if s.isEmpty || !s.startsWith "{" then none
  else
    let rec go (left : String) (acc : Array ManaType) : Option (Array ManaType) :=
      if left.isEmpty then if acc.isEmpty then none else some acc
      else
        match parseManaTypeSymbol? left with
        | none => none
        | some (t, rest) =>
          if rest.length < left.length then go rest (acc.push t) else none
    termination_by left.length
    go s #[]

/-- Parse a list of single mana symbols joined by `" or "`, `", or "`, `","`,
or `" and/or "` (e.g. `"{U} or {B}"`, `"{U}, {B}, and/or {R}"`). -/
private def parseManaTypeList? (raw : String) : Option (Array ManaType) := Id.run do
  let norm := (((cleanClause raw).replace ", and/or " "|").replace " and/or " "|")
    |>.replace ", or " "|" |>.replace " or " "|" |>.replace "," "|"
  let parts := norm.splitOn "|" |>.map (fun p => p.trimAscii.copy) |>.filter (!·.isEmpty)
  if parts.isEmpty then return none
  let mut out : Array ManaType := #[]
  for p in parts do
    match parseManaTypeSeq? p with
    | some ts =>
      if ts.size == 1 then out := out.push ts[0]!
      else return none
    | none => return none
  return some out

/-- Detect filter-land pair alternatives like `"{W}{W}, {W}{B}, or {B}{B}"` and
return the pair `#[a, b]`. -/
private def parseFilterPairList? (raw : String) : Option (Array ManaType) := Id.run do
  let norm := ((cleanClause raw).replace ", or " "|").replace " or " "|" |>.replace "," "|"
  let parts := norm.splitOn "|" |>.map (fun p => p.trimAscii.copy) |>.filter (!·.isEmpty)
  if parts.length != 3 then return none
  let mut uniq : Array ManaType := #[]
  for p in parts do
    match parseManaTypeSeq? p with
    | some ts =>
      if ts.size != 2 then return none
      for t in ts do
        if !uniq.contains t then uniq := uniq.push t
    | none => return none
  if uniq.size == 2 then return some uniq else return none

/-- Normalize full and legendary-shortened self-references (`"Doc Samson, Super Psychiatrist"`
or `"Doc Samson"`) to `replacement` (CR 201.5c). -/
private def replaceSelfName (raw cardName replacement : String) : String :=
  replaceCardNameOutsideQuotes raw cardName replacement

/-- Parse the object phrase following `"Add "` into a declarative `ManaSpec`
(CR 106.1 / 106.7 / 605). Returns `(spec, filterPairFormat)`. -/
def parseManaSpecWithFormat (raw : String) (cardName : String := "") : Option (ManaSpec × Bool) := Id.run do
  let raw := replaceSelfName raw cardName "this creature"
  let s := stripTrailingPeriod (cleanClause raw)
  if s.isEmpty then return none
  let lowS := lower s

  -- 1. Filter-land pair format: `"{W}{W}, {W}{B}, or {B}{B}"`.
  if let some pair := parseFilterPairList? s then
    return some (.combination (.explicit pair) (.const 2), true)

  -- 2. Scaled fixed mana: `"{G} for each Elf you control"`, `"{G} for each charge counter on this enchantment"`, etc.
  if let some (symStr, objsStr) := splitFirstCI? s " for each " then
    if let some ts := parseManaTypeSeq? symStr then
      if let some (ctrStr, hostStr) := (splitFirstCI? objsStr " counter on ").orElse
          (fun _ => splitFirstCI? objsStr " counters on ") then
        let ws := (splitWords ctrStr).toList.map lower
        match CounterKind.ofPrefix ws, parseObjectExpr? hostStr with
        | some (k, n), some host =>
          if n == ws.length then
            return some (.sequence (ts.map fun t => (t, .counterCount (some k) host)), false)
        | _, _ => pure ()
      let objs? : Option ObjectExpr :=
        if let some subStr := dropSuffixCI? objsStr " you control" then
          match CardSubtype.ofOracle? subStr with
          | some sub => some (.controlledOfSubtype sub)
          | none => parseObjectExpr? objsStr
        else parseObjectExpr? objsStr
      if let some objs := objs? then
        return some (.sequence (ts.map fun t => (t, ValueExpr.count objs)), false)

  -- 2b. Dynamic count prefix format from `ManaSpec.toOracle`: `"the number of charge counters on this permanent {G}"`
  if s.endsWith "}" then
    if let some (valStr, symTail) := splitLastCI? s " {" then
      let symStr := "{" ++ symTail
      if let some ts := parseManaTypeSeq? symStr then
        if let some v := parseValueExpr valStr then
          return some (.sequence (ts.map fun t => (t, v)), false)

  -- 3. CR 106.7 `"could produce"` palettes (Exotic Orchard / Reflecting Pool / general).
  if let some tail := dropPrefixCI? s "one mana of any color that " then
    if let some landsStr := dropSuffixCI? tail " could produce" then
      let landsLow := lower landsStr
      if landsLow == "a land an opponent controls" || landsLow == "lands an opponent controls" ||
          landsLow == "lands opponents control" then
        return some (.colorAmong (.typesLandsCouldProduce .landsOpponentsControl) false, false)
      if landsLow == "a land you control" || landsLow == "other lands you control" ||
          landsLow == "lands you control" then
        return some (.colorAmong (.typesLandsCouldProduce .otherLandsYouControl) false, false)
      if let some objs := parseObjectExpr? landsStr then
        return some (.colorAmong (.typesLandsCouldProduce objs) false, false)
  if let some tail := dropPrefixCI? s "one mana of any type that " then
    if let some landsStr := dropSuffixCI? tail " could produce" then
      let landsLow := lower landsStr
      if landsLow == "a land you control" || landsLow == "other lands you control" ||
          landsLow == "lands you control" then
        return some (.colorAmong (.typesLandsCouldProduce .otherLandsYouControl) true, false)
      if landsLow == "a land an opponent controls" || landsLow == "lands an opponent controls" ||
          landsLow == "lands opponents control" then
        return some (.colorAmong (.typesLandsCouldProduce .landsOpponentsControl) true, false)
      if let some objs := parseObjectExpr? landsStr then
        return some (.colorAmong (.typesLandsCouldProduce objs) true, false)

  -- 4. Commander color identity (Command Tower / Arcane Signet / Path of Ancestry).
  if lowS == "one mana of any color in your commander's color identity" ||
      lowS == "one mana of any one color in your commander's color identity" then
    return some (.colorAmong (.commanderColorIdentity .you) false, false)
  if let some tail := (dropPrefixCI? s "one mana of any color in ").orElse
      (fun _ => dropPrefixCI? s "one mana of any one color in ") then
    if let some whoStr := dropSuffixCI? tail "'s commander's color identity" then
      if let some who := parsePlayerExpr? whoStr then
        return some (.colorAmong (.commanderColorIdentity who) false, false)

  -- 5. Colors among permanents (Mox Amber / general).
  if let some objsStr := dropPrefixCI? s "one mana of any color among " then
    let ol := lower objsStr
    if ol == "legendary creatures and planeswalkers you control" then
      return some (.colorAmong (.colorsAmong .legendaryCreaturesAndPlaneswalkersYouControl) false, false)
    if let some objs := parseObjectExpr? objsStr then
      return some (.colorAmong (.colorsAmong objs) false, false)

  -- 6. Chosen color on source (`"one mana of the chosen color"`, `"N mana of the chosen color"`).
  if lowS == "one mana of the chosen color" then
    return some (.oneOf .chosenColorOnSource (.const 1), false)
  if let some cntStr := dropSuffixCI? s " mana of the chosen color" then
    if let some n := parseNatWord? cntStr then
      return some (.oneOf .chosenColorOnSource (.const (Int.ofNat n)), false)

  -- 7. Combination of mana (`"four mana in any combination of colors"`,
  --    `"two mana in any combination of {U}, {B}, and/or {R}"`, `"X mana in any combination of colors, where X is ..."`).
  if let some (cntStr, palStr) := splitFirstCI? s " mana in any combination of " then
    let (palPart, whereVal?) : String × Option ValueExpr :=
      match splitFirstCI? palStr ", where x is " with
      | some (p, vStr) => (p, parseValueExpr vStr)
      | none => (palStr, none)
    let amt? : Option ValueExpr :=
      if lower cntStr == "x" then whereVal?
      else (parseNatWord? cntStr).map fun n => .const (Int.ofNat n)
    if let some amt := amt? then
      let palLow := lower (cleanClause palPart)
      if palLow == "colors" || palLow == "any color" then
        return some (.combination .anyColor amt, false)
      if let some ts := parseManaTypeList? palPart then
        if ts.size ≥ 2 then
          return some (.combination (.explicit ts) amt, false)

  -- 8. Any color / any one color (constant or X-scaled).
  if lowS == "one mana of any color" || lowS == "one mana of any one color" then
    return some (.oneOf .anyColor (.const 1), false)
  if let some (head, valStr) := splitFirstCI? s ", where x is " then
    let hl := lower head
    if hl == "x mana of any one color" || hl == "x mana of any color" then
      if let some v := parseValueExpr valStr then
        return some (.oneOf .anyColor v, false)
  if let some cntStr := (dropSuffixCI? s " mana of any one color").orElse
      (fun _ => dropSuffixCI? s " mana of any color") then
    if let some n := parseNatWord? cntStr then
      return some (.oneOf .anyColor (.const (Int.ofNat n)), false)

  -- 9. Choice of explicit mana symbols (`"{U} or {B}"`, `"{W}, {U}, or {B}"`).
  if lowS.contains " or " then
    if let some ts := parseManaTypeList? s then
      if ts.size ≥ 2 then
        return some (.oneOf (.explicit ts) (.const 1), false)

  -- 10. Fixed sequence of concrete mana symbols (`"{G}"`, `"{C}{C}"`, `"{W}{U}"`, `"{C}{C}{C}"`).
  if let some ts := parseManaTypeSeq? s then
    return some (.fixed ts, false)

  return none

/-- Parse the object phrase following `"Add "` into a declarative `ManaSpec` (CR 106.1 / 605). -/
def parseManaSpec (raw : String) (cardName : String := "") : Option ManaSpec :=
  (parseManaSpecWithFormat raw cardName).map Prod.fst

/-- Split an Oracle effect body into non-empty trimmed sentences on `"."`. -/
private def splitSentences (raw : String) : Array String :=
  ((stripReminderText raw).splitOn ".").map (fun p => p.trimAscii.copy)
    |>.filter (!·.isEmpty) |>.toArray

/-- Parse a self-damage sentence (`"This land deals 1 damage to you"`,
`"This artifact deals 1 damage to you"`, `"~ deals 2 damage to you"`). -/
private def parseSelfDamageSentence? (raw : String) (cardName : String := "") : Option Nat := Id.run do
  let raw := replaceSelfName raw cardName "this permanent"
  let s := cleanClause raw
  let some (subj, rest) := splitFirstCI? s " deals " | return none
  if !isSelfObjectPhrase subj then return none
  let some amtStr := dropSuffixCI? rest " damage to you" | return none
  parseNatWord? amtStr

/-- Parse a standalone spell-rider sentence attached to a mana ability (CR 106.6). -/
private def parseStandaloneRiderSentence? (raw : String) : Option SpellRiderSpec := Id.run do
  let low := lower (cleanClause raw)
  if low == "that spell can't be countered" ||
      low == "if that mana is spent on a spell, that spell can't be countered" ||
      low == "if that mana is spent on a creature spell, it can't be countered" ||
      low == "if that mana is spent to cast a creature spell, that spell can't be countered" then
    return some .cantBeCountered
  if low == "that creature gains haste" ||
      low == "that creature gains haste until end of turn" ||
      low == "if that mana is spent on a creature spell, it gains haste" ||
      low == "if that mana is spent on a creature spell, it gains haste until end of turn" ||
      low == "if that mana is spent to cast a creature spell, that creature gains haste" ||
      low == "if that mana is spent to cast a creature spell, that creature gains haste until end of turn" then
    return some .gainsHaste
  if low == "that creature enters with an additional +1/+1 counter on it" ||
      low == "that creature enters with a +1/+1 counter on it" ||
      low == "if that mana is spent on a creature spell, that creature enters with a +1/+1 counter on it" ||
      low == "if that mana is spent on a creature spell, that creature enters with an additional +1/+1 counter on it" ||
      low == "if that mana is spent to cast a creature spell, that creature enters with a +1/+1 counter on it" ||
      low == "if that mana is spent to cast a creature spell, that creature enters with an additional +1/+1 counter on it" then
    return some (.entersWithPlusOneCounters 1)
  if let some rest := (dropPrefixCI? low "that creature enters with ").orElse
      (fun _ => (dropPrefixCI? low "if that mana is spent on a creature spell, that creature enters with ").orElse
        (fun _ => dropPrefixCI? low "if that mana is spent to cast a creature spell, that creature enters with ")) then
    let rest := (dropPrefixCI? rest "an additional ").getD rest
    let rest := (dropSuffixCI? rest " on it").getD rest
    if let some nStr0 := (dropSuffixCI? rest " +1/+1 counters").orElse
        (fun _ => dropSuffixCI? rest " +1/+1 counter") then
      let nStr := (dropSuffixCI? nStr0 " additional").getD nStr0
      if let some n := parseNatWord? nStr then
        return some (.entersWithPlusOneCounters n)
  return none

/-- Parse the effect sentences of a mana ability (everything after `":"` with any
`"Activate ..."` restriction sentences already stripped) into a `ManaProductionSpec`.
Returns `none` if any sentence is unrecognized (preventing non-mana multi-step
abilities from being misclassified). -/
def parseManaProductionSpec (sentences : Array String) (cardName : String := "") :
    Option ManaProductionSpec := Id.run do
  if sentences.isEmpty then return none
  let mut idx : Nat := 0
  let mut spec? : Option ManaSpec := none
  let mut chooseColorPrefix : Bool := false
  let mut filterPairFormat : Bool := false

  -- Case A: `"Choose a color."` followed by `"Add one mana of that color for each ..."`
  if lower sentences[0]! == "choose a color" && sentences.size ≥ 2 then
    let s1 := sentences[1]!
    if let some rest := dropPrefixCI? s1 "add one mana of that color for each " then
      let rLow := lower rest
      if rLow == "different power among creatures you control" then
        spec? := some (.oneOf .anyColor (.aggregate .countDistinct (.stat .power) .creaturesYouControl))
        chooseColorPrefix := true
        idx := 2
      else if let some subStr := dropSuffixCI? rest " you control" then
        match CardSubtype.ofOracle? subStr with
        | some sub =>
          spec? := some (.oneOf .anyColor (ValueExpr.count (.controlledOfSubtype sub)))
          chooseColorPrefix := true
          idx := 2
        | none =>
          match parseValueExpr s!"the number of {rest}" with
          | some v =>
            spec? := some (.oneOf .anyColor v)
            chooseColorPrefix := true
            idx := 2
          | none => return none
      else if let some v := parseValueExpr s!"the number of {rest}" then
        spec? := some (.oneOf .anyColor v)
        chooseColorPrefix := true
        idx := 2
      else return none
    else return none
  else
    -- Case B: `"Add <manaSpec>"`
    let some rest := dropPrefixCI? sentences[0]! "add " | return none
    let some (sp, isFilterPair) := parseManaSpecWithFormat rest cardName | return none
    spec? := some sp
    filterPairFormat := isFilterPair
    idx := 1

  let some spec := spec? | return none
  let mut restriction : Option ManaSpendRestriction := none
  let mut riders : Array SpellRiderSpec := #[]
  let mut damageYou : Nat := 0

  while idx < sentences.size do
    let sent := sentences[idx]!
    let sLow := lower sent
    if let some dmg := parseSelfDamageSentence? sent cardName then
      damageYou := damageYou + dmg
    else if sLow.startsWith "spend this mana " || sLow.startsWith "this mana can't be spent " ||
        sLow.startsWith "this mana cannot be spent " then
      match ManaSpendRestriction.parseOracle? sent with
      | some r =>
        restriction := some r
        for rd in r.riders do
          if !riders.contains rd then riders := riders.push rd
      | none => return none
    else if let some rd := parseStandaloneRiderSentence? sent then
      if !riders.contains rd then riders := riders.push rd
    else if sLow.startsWith "when that mana is spent to cast a creature spell that shares a creature type with your commander, scry " then
      -- Path of Ancestry delayed scry trigger (attached as a `TriggeredAbility` by `ParseOracle`).
      pure ()
    else
      return none
    idx := idx + 1

  return some { spec, restriction, riders, damageYou, chooseColorPrefix, filterPairFormat }

/-- Parse a complete Oracle mana-producing activated ability line
(`"<cost>: Add ... [self-damage.] [Spend this mana ...] [Activate only ...]"`)
into a unified `ActivatedAbility` with `PlayerOp.addMana` in `effect.body` (CR 605.1a).
Rejects triggered abilities and loyalty abilities (`[+1]: ...`), and returns
`none` if the effect contains non-mana instructions. -/
def parseManaAbilityLine (raw : String) (cardName : String := "") : Option ActivatedAbility := Id.run do
  let cleaned := stripReminderText raw
  let lowClean := lower cleaned
  if lowClean.startsWith "whenever " || lowClean.startsWith "when " ||
      lowClean.startsWith "at the beginning" then
    return none
  let some (costRaw, bodyRaw) := splitFirstCI? cleaned ":" | return none
  if !(lower bodyRaw).contains "add " then return none

  let mut costStr := costRaw.trimAscii.copy
  let mut tag? : Option ActivationMechanicTag := none
  let mut lifetimeLimit? : Option Nat := none
  let mut turnLimit? : Option Nat := none
  let mut condition? : Option Condition := none

  if let some rest := (dropPrefixCI? costStr "exhaust — ").orElse
      (fun _ => dropPrefixCI? costStr "exhaust—") then
    costStr := rest
    tag? := some .exhaust
    lifetimeLimit? := some 1
  else if let some rest := (dropPrefixCI? costStr "boast — ").orElse
      (fun _ => dropPrefixCI? costStr "boast—") then
    costStr := rest
    tag? := some .boast
    turnLimit? := some 1
    condition? := some ActivatedAbility.condSourceAttackedThisTurn

  let costStrNorm := replaceSelfName costStr cardName "this permanent"
  let some cost := parseCostSpec costStrNorm | return none
  if cost.isLoyalty then return none

  let allSents := splitSentences bodyRaw
  if allSents.isEmpty then return none

  let mut manaSents : Array String := #[]
  let mut timing : ActivationTiming := .instant
  let mut activeZones : Array ZoneKind := #[.battlefield]

  for sent in allSents do
    let sLow := lower sent
    if sLow == "activate only as a sorcery" then
      timing := .sorcery
    else if sLow == "activate only during your turn" then
      condition? := Condition.andOpt condition? (some .isYourTurn)
    else if sLow == "activate only once each turn" then
      turnLimit? := some 1
    else if sLow == "activate only once" then
      lifetimeLimit? := some 1
    else if sLow == "activate only from your graveyard" then
      activeZones := #[.graveyard]
    else if sLow == "activate only from your hand" then
      activeZones := #[.hand]
    else if let some rest := dropPrefixCI? sent "activate no more than " then
      if let some nStr := dropSuffixCI? rest " times each turn" then
        if let some n := parseNatWord? nStr then turnLimit? := some n
        else return none
      else if let some nStr := dropSuffixCI? rest " times" then
        if let some n := parseNatWord? nStr then lifetimeLimit? := some n
        else return none
      else return none
    else if let some condStr := dropPrefixCI? sent "activate only if " then
      let condStrNorm := replaceSelfName condStr cardName "this permanent"
      match parseCondition condStrNorm with
      | some c => condition? := Condition.andOpt condition? (some c)
      | none => return none
    else
      manaSents := manaSents.push sent

  let some mp := parseManaProductionSpec manaSents cardName | return none
  return some {
    cost
    effect := { body := .player (.addMana .you mp) }
    timing
    activeZones
    turnLimit?
    lifetimeLimit?
    condition?
    tag?
  }

/-! ### Stage-4 Compositional Static-Ability Sub-Grammar (CR 303.4a / 601.2f / 604 / 613 / 614–616) -/

/-- Extract the first `{N}` generic mana amount in `s`, if any. -/
private def firstGenericBraceNat? (s : String) : Option Nat :=
  let rec go : List Char → Option Nat
    | [] => none
    | '{' :: rest =>
      let digits := rest.takeWhile Char.isDigit
      match rest.dropWhile Char.isDigit with
      | '}' :: _ =>
        if digits.isEmpty then go rest else some (String.ofList digits).toNat!
      | _ => go rest
    | _ :: rest => go rest
  go s.toList

/-- Parse a signed integer token like `+2`, `-1`, `+0`, `−3`. -/
private def parseSignedStatToken? (raw : String) : Option Int :=
  let s := raw.trimAscii.copy
  if s.isEmpty then none
  else
    let c0 := s.front
    let isNeg := c0 == '-' || c0 == '−' || c0 == '–'
    let isPos := c0 == '+'
    if !isPos && !isNeg then none
    else
      let rest := (s.drop 1).copy
      if !rest.isEmpty && rest.all Char.isDigit then
        let n : Int := Int.ofNat rest.toNat!
        some (if isNeg then -n else n)
      else none

/-- Parse a signed P/T modifier (e.g. `+2/+2` or `-1` / `-1`) into `(P, T)`. -/
private def parsePTBonus? (raw : String) : Option (Int × Int) :=
  let s := raw.trimAscii.copy
  match s.splitOn "/" with
  | [p, t] =>
    match parseSignedStatToken? p, parseSignedStatToken? t with
    | some pv, some tv => some (pv, tv)
    | _, _ => none
  | _ => none

/-- Parse a comma/`and`-separated list of inline keywords (plus optional `ward {N}`). -/
private def parseGrantedKeywordsList? (raw : String) : Option (Array KeywordAbility) := Id.run do
  let s := cleanClause raw
  if s.isEmpty then return none
  let normalized := s.replace ", and " ", " |>.replace " and " ", "
  let parts := normalized.splitOn "," |>.map (·.trimAscii.copy) |>.filter (!·.isEmpty)
  if parts.isEmpty then return none
  let mut out : Array KeywordAbility := #[]
  for part in parts do
    match parseKeywordAbility part with
    | some k => out := out.push k
    | none => return none
  return some (out.qsort (fun a b => a.displayOrder < b.displayOrder))

/-- Parse `"a <sub1> or a <sub2>..."` subtype list (for check-lands / unless-control clauses). -/
private def parseOrSubtypes? (raw : String) : Option (Array CardSubtype) := Id.run do
  let s := cleanClause raw
  let pieces := ((s.replace ", or " " or ").splitOn " or ").map (·.trimAscii.copy) |>.filter (!·.isEmpty)
  if pieces.isEmpty then return none
  let mut out : Array CardSubtype := #[]
  for p in pieces do
    let w := (dropPrefixCI? p "an ").orElse (fun _ => dropPrefixCI? p "a ") |>.getD p
    match CardSubtype.ofOracle? w with
    | some sub => out := out.push sub
    | none => return none
  return some out

/-- Parse a Stage-4 static ability condition phrase (after `"if "` / `"unless "` / `"as long as "`),
producing canonical `StaticAbility.cond*` shapes so round-trip matches `ToOracle` identically. -/
private def parseStaticCondition? (raw : String) (cardName : String := "") : Option Condition := Id.run do
  let s0 := cleanClause (replaceSelfName raw cardName "this permanent")
  let low := lower s0
  if low == "you control a legendary creature" || low == "you control a legendary" then
    return some StaticAbility.condControlLegendaryCreature
  if low == "you control an equipment" then
    return some (StaticAbility.condControlSubtype .equipment)
  if low == "you control a planeswalker" then
    return some StaticAbility.condControlPlaneswalker
  if low == "you control a commander" then
    return some StaticAbility.condControlCommander
  if low == "you control two or more other lands" then
    return some (StaticAbility.condControlNOtherLands 2)
  if low == "a creature died this turn" then
    return some StaticAbility.condCreatureDiedThisTurn
  if low == "you've cast a noncreature spell this turn" then
    return some StaticAbility.condCastNoncreatureThisTurn
  if low == "an opponent has cast a spell this turn" then
    return some StaticAbility.condOpponentCastSpellThisTurn
  if low == "an opponent was dealt noncombat damage this turn" then
    return some StaticAbility.condOpponentDealtNoncombatDamageThisTurn
  if low == "you have an enduring story" then
    return some StaticAbility.condEnduringStory
  if low == "it targets a creature that was dealt damage this turn" then
    return some (StaticAbility.condTargetsCreature .wasDealtDamageThisTurn)
  if low == "it targets a tapped creature" then
    return some (StaticAbility.condTargetsCreature (.tapped true))
  if low == "it targets an attacking nontoken creature" then
    return some (StaticAbility.condTargetsCreature (.all #[.combatRole .attacking, .isToken false]))
  if low == "it targets an attacking creature" then
    return some (StaticAbility.condTargetsCreature (.combatRole .attacking))
  -- `"you control N or more basic lands"`
  if let some rest := dropPrefixCI? low "you control " then
    if let some nStr := dropSuffixCI? rest " or more basic lands" then
      if let some n := parseNatWord? nStr then
        return some (StaticAbility.condControlNBasicLands n)
    if let some nStr := dropSuffixCI? rest " or more other lands" then
      if let some n := parseNatWord? nStr then
        return some (StaticAbility.condControlNOtherLands n)
    if let some subStr := dropPrefixCI? rest "another " then
      if let some sub := CardSubtype.ofOracle? subStr then
        return some (StaticAbility.condControlOtherSubtype sub)
    -- `"you control a/an <sub1> or a/an <sub2>"` (land subtypes for check-lands)
    if rest.contains " or " then
      if let some subs := parseOrSubtypes? rest then
        if subs.size ≥ 2 && subs.all (·.kind == .land) then
          return some (StaticAbility.condControlLandAnySubtype subs)
    let afterArt := (dropPrefixCI? rest "an ").orElse (fun _ => dropPrefixCI? rest "a ") |>.getD rest
    if let some sub := CardSubtype.ofOracle? afterArt then
      return some (StaticAbility.condControlSubtype sub)
  -- `"your opponents control N or more lands"`
  if let some rest := dropPrefixCI? low "your opponents control " then
    if let some nStr := dropSuffixCI? rest " or more lands" then
      if let some n := parseNatWord? nStr then
        return some (StaticAbility.condOpponentsControlNLands n)
  -- `"there are N or more cards / other cards / creature cards in your graveyard"`
  if low == "there is a creature card in your graveyard" then
    return some (StaticAbility.condGyCreatureCardsAtLeast 1)
  if let some rest := dropPrefixCI? low "there are " then
    if let some nStr := dropSuffixCI? rest " or more creature cards in your graveyard" then
      if let some n := parseNatWord? nStr then
        return some (StaticAbility.condGyCreatureCardsAtLeast n)
    if let some nStr := dropSuffixCI? rest " or more other cards in your graveyard" then
      if let some n := parseNatWord? nStr then
        return some (StaticAbility.condOtherCardsInGraveyardAtLeast n)
    if let some nStr := dropSuffixCI? rest " or more cards in your graveyard" then
      if let some n := parseNatWord? nStr then
        return some (StaticAbility.condGraveyardAtLeast n)
    if let some nStr := dropSuffixCI? rest " or more lore counters among sagas you control" then
      if let some n := parseNatWord? nStr then
        return some (StaticAbility.condSagaLoreCountersAtLeast n)
  -- `"an opponent has N or more poison counters"`
  if let some rest := dropPrefixCI? low "an opponent has " then
    if let some nStr := dropSuffixCI? rest " or more poison counters" then
      if let some n := parseNatWord? nStr then
        return some (StaticAbility.condOpponentPoisonAtLeast n)
  parseCondition s0

/-- Parse a Stage-4 high-precision static ability line (CR 303.4a / 601.2f / 604 / 613 / 614–616),
returning one or more stratified `StaticAbility` values. Covers all migrated structural
static, cost-modifier, ETB, as-enters, rule-modifying, and Aura enchant-restriction lines
and round-trips canonically against `StaticAbility.toOracle`. -/
def parseStaticAbilityLine (raw : String) (cardName : String := "") : Option (Array StaticAbility) := Id.run do
  let cleaned := cleanClause (stripReminderText raw)
  if cleaned.isEmpty then return none
  let low := lower cleaned
  let selfNorm := cleanClause (replaceSelfName cleaned cardName "this permanent")
  let selfLow := lower selfNorm

  -- Do not intercept triggered abilities (`When`/`Whenever`/`At the beginning`) or activated abilities (`:`)
  -- unless the colon is inside quotes (`Creatures you control have "{T}: Add ..."`).
  if low.startsWith "when " || low.startsWith "whenever " || low.startsWith "at the beginning" then
    return none
  let beforeQuote := (cleaned.splitOn "\"").headD cleaned
  if beforeQuote.contains ':' then
    return none

  -- 1. Aura Enchant restrictions (CR 303.4a) — skip plain `"Enchant creature"` (default Aura target)
  if let some rest := dropPrefixCI? cleaned "enchant " then
    let rLow := lower rest
    if rLow == "creature" then return none
    if rLow == "artifact or non-aura enchantment" then
      return some #[StaticAbility.enchantArtifactOrNonAuraEnchantment]
    if rLow == "creature you control" then
      return some #[StaticAbility.enchantCreatureYouControl]
    if let some slot := parseTargetSlot ("target " ++ rest) then
      return some #[.enchantRestriction { slot with count := .exact 1 }]
    return none

  -- 2. Self spell cost reductions / free casts (CR 601.2f)
  if let some rest := dropPrefixCI? selfLow "this spell costs {x} less to cast, where x is " then
    if rest == "the total power of creatures you control with flying" then
      return some #[StaticAbility.costReductionEqualFlyingPower]
    if rest == "the greatest number of artifacts an opponent controls" then
      return some #[StaticAbility.costReductionEqualOppArtifacts]
    if rest == "the greatest power among creatures you control" then
      return some #[StaticAbility.costReductionGreatestPower]
    if rest == "the greatest toughness among creatures you control" then
      return some #[StaticAbility.costReductionGreatestToughness]
    if let some v := parseValueExpr rest then
      return some #[.costModifier none .thisSpell (.reduceGeneric v)]
    return none

  if selfLow.startsWith "this spell costs " && selfLow.contains " less to cast" then
    let some k := firstGenericBraceNat? cleaned | return none
    if selfLow.contains "dealt damage this turn" then
      return some #[StaticAbility.costReductionIfTargetDamaged k]
    if selfLow.contains "tapped creature" then
      return some #[StaticAbility.costReductionIfTargetTapped k]
    if selfLow.contains "attacking nontoken" then
      return some #[StaticAbility.costReductionIfTargetAttackingNontoken k]
    if selfLow.contains "attacking creature" then
      return some #[StaticAbility.costReductionIfTargetAttacking k]
    if selfLow.contains "if a creature died this turn" then
      return some #[StaticAbility.costReductionIfCreatureDied k]
    if selfLow.contains "if you've cast a noncreature spell this turn" then
      return some #[StaticAbility.costsLessIfCastNoncreature k]
    if let some (_, condStr) := splitFirstCI? cleaned " less to cast if " then
      if let some cond := parseStaticCondition? condStr cardName then
        return some #[.costModifier (some cond) .thisSpell (.reduceGeneric (.const k))]
      return none
    if selfLow.endsWith " less to cast" then
      return some #[.costModifier none .thisSpell (.reduceGeneric (.const k))]
    return none

  if selfLow.contains "without paying its mana cost" && selfLow.contains "commander" then
    return some #[StaticAbility.freeCastIfControlCommander]

  -- 3. Multi-spell / Eminence / first-creature / not-from-hand cost modifiers & flash
  if selfLow.startsWith "the first creature spell you cast each turn costs " then
    let some k := firstGenericBraceNat? cleaned | return none
    if selfLow.contains "as though it had flash" then
      return some #[StaticAbility.firstCreatureCostsLess k, StaticAbility.firstCreatureHasFlash]
    else
      return some #[StaticAbility.firstCreatureCostsLess k]
  if selfLow == "the first creature spell you cast each turn can be cast as though it had flash" then
    return some #[StaticAbility.firstCreatureHasFlash]
  if selfLow.contains "from anywhere other than your hand cost" then
    let some k := firstGenericBraceNat? cleaned | return none
    return some #[StaticAbility.costReductionNotFromHand k]
  if selfLow.contains " spells you cast cost " &&
      (selfLow.contains "command zone" || selfLow.startsWith "eminence") then
    let some k := firstGenericBraceNat? cleaned | return none
    let afterSubAnchor? :=
      (splitFirstCI? cleaned "other ").map Prod.snd
      |>.orElse fun _ => (splitFirstCI? cleaned "on the battlefield, ").map Prod.snd
    if let some afterAnchor := afterSubAnchor? then
      if let some (subStr, _) := splitFirstCI? afterAnchor " spells you cast" then
        if let some sub := CardSubtype.ofOracle? subStr then
          return some #[StaticAbility.eminenceSubtypeSpellsCostLess sub k]

  -- 4. Play rules (cantBeCountered, flashIf, graveyard restriction, castExiled, look/cast/play top, commander)
  if selfLow == "this spell can't be countered" then
    return some #[StaticAbility.spellCantBeCountered]
  if let some (_, condStr) := splitFirstCI? cleaned "you may cast this spell as though it had flash if " then
    if let some cond := parseStaticCondition? condStr cardName then
      return some #[.ruleModifying (some cond) (.play (.castAsThoughFlash .you .anyObject true none))]
  if let some rest := dropPrefixCI? selfLow "as long as there are " then
    if let some (numStr, tail) :=
        splitFirstCI? rest " or more cards in your graveyard, you may cast the exiled card" then
      if let some n := parseNatWord? numStr then
        if n == 7 then
          return some #[StaticAbility.castExiledWithSevenInGraveyard]
        else
          return some #[.ruleModifying (some (StaticAbility.condGraveyardAtLeast n))
            (.play (.mayPlayFrom .you .exile .anyObject (linkedExile := true)
              (castAnyColorMana := tail.contains "mana of any type")))]
  if let some condStr := dropPrefixCI? selfLow "you can't cast this spell unless " then
    if let some cond := parseStaticCondition? condStr cardName then
      -- Normalize `there are N or more cards in your graveyard` to `other cards` for cast restriction
      let cond :=
        match cond with
        | .cmp .ge (.playerMetric .graveyardSize .you) (.const n) =>
          StaticAbility.condOtherCardsInGraveyardAtLeast n.toNat
        | other => other
      return some #[.ruleModifying none (.play (.castRestriction cond))]
  if selfLow == "you may look at the top card of your library any time" then
    return some #[StaticAbility.mayLookAtTopAnytime]
  if selfLow == "you may cast creature spells from the top of your library" then
    return some #[StaticAbility.mayCastCreaturesFromTop]
  if selfLow == "you may play lands from the top of your library" then
    return some #[StaticAbility.mayPlayLandsFromTop]
  if selfLow == "you may play lands from your graveyard" then
    return some #[StaticAbility.mayPlayLandsFromGraveyard]
  if selfLow.endsWith " can be your commander" then
    return some #[StaticAbility.canBeCommander]

  -- 5. Player / Game rules (Platinum Angel, opponents can't gain life, -1/-1 lock, additional land)
  if selfLow == "your opponents can't gain life" then
    return some #[StaticAbility.opponentsCantGainLife]
  if selfLow.contains "you can't lose the game" && selfLow.contains "your opponents can't win the game" then
    return some #[StaticAbility.cantLoseAndOpponentsCantWin]
  if selfLow == "you can't lose the game" then
    return some #[.ruleModifying none (.player (.cantLoseGame .you))]
  if selfLow == "your opponents can't win the game" then
    return some #[.ruleModifying none (.player (.cantWinGame .opponent))]
  if selfLow.contains "creatures you control can't have -1/-1 counters put on them" then
    return some #[StaticAbility.creaturesCantGetMinusCounters]
  if selfLow.contains "you may play an additional land" && selfLow.contains "as long as you control another " then
    if let some (_, afterAnother) := splitFirstCI? cleaned "another " then
      let subWord := ((afterAnother.splitOn ",").headD afterAnother).splitOn "." |>.headD "" |>.trimAscii.copy
      if let some sub := CardSubtype.ofOracle? subWord then
        return some #[StaticAbility.extraLandIfOtherSubtype sub]
  if selfLow.startsWith "if this " && selfLow.contains "power is negative," &&
      selfLow.contains "assigns combat damage as though" && selfLow.endsWith "power were positive" then
    return some #[StaticAbility.negativePowerAssignsAsPositive]
  if selfLow == "during combat, players can't cast spells or activate abilities that aren't mana abilities" then
    return some #[StaticAbility.noSpellsOrAbilitiesDuringCombat]
  if selfLow == "spells with the chosen name can't be cast" then
    return some #[StaticAbility.chosenNameSpellsCantBeCast]
  if selfLow.contains "power is equal to the number of card types among cards in all graveyards" &&
      selfLow.contains "toughness is equal to that number plus 1" then
    return some #[StaticAbility.ptEqualGraveyardCardTypes]
  if selfLow.contains "you've put one or more +1/+1 counters on" &&
      selfLow.contains "this turn," && selfLow.endsWith "has flying" then
    return some #[StaticAbility.flyingIfPlusOneThisTurn]

  -- 6. ETB / As-enters / Replacement effects (CR 614 / 615)
  if selfLow.contains "enters tapped" && selfLow.contains " life" &&
      (selfLow.contains "you may pay " || selfLow.contains "unless you pay ") then
    let afterPay? :=
      (splitFirstCI? selfLow "you may pay ").map Prod.snd
      |>.orElse fun _ => (splitFirstCI? selfLow "unless you pay ").map Prod.snd
    if let some afterPay := afterPay? then
      let digits := (afterPay.takeWhile Char.isDigit).copy
      if !digits.isEmpty then
        return some #[StaticAbility.entersTappedUnlessPayLife digits.toNat!]
  if selfLow.contains "you may behold " && selfLow.contains "if you don't" && selfLow.contains "enters tapped" then
    if let some (_, afterBehold) := splitFirstCI? cleaned "you may behold " then
      let head := (afterBehold.splitOn ".").headD afterBehold |>.trimAscii.copy
      let word := (dropPrefixCI? head "an ").orElse (fun _ => dropPrefixCI? head "a ") |>.getD head
      if let some sub := CardSubtype.ofOracle? word then
        return some #[StaticAbility.entersTappedUnlessBehold sub]
  if selfLow == "this land enters tapped. as it enters, choose a color" then
    return some #[StaticAbility.entersTappedChooseColor]
  if let some (head, unlessStr) := splitFirstCI? selfNorm " enters tapped unless " then
    if isSelfObjectPhrase head then
      if let some cond := parseStaticCondition? unlessStr cardName then
        return some #[StaticAbility.entersTappedUnless cond]
  if let some head := dropSuffixCI? selfNorm " enters tapped" then
    if isSelfObjectPhrase head then
      return some #[StaticAbility.entersTapped]
  if let some head := dropSuffixCI? selfNorm " enters prepared" then
    if isSelfObjectPhrase head then
      return some #[StaticAbility.entersPrepared]
  if selfLow.contains "enters with a hope counter" && selfLow.contains "for each creature you control" then
    return some #[StaticAbility.entersWithHopePerCreature]
  if selfLow.contains "additional +1/+1 counters" && selfLow.contains "toughness" then
    return some #[StaticAbility.othersEnterWithPlusOneEqualToughness]
  if let some (head, afterWith) := splitFirstCI? selfNorm " enters with " then
    if isSelfObjectPhrase head then
      let trimmed := (dropSuffixCI? afterWith " on it").orElse
        (fun _ => (dropSuffixCI? afterWith " on him").orElse
          (fun _ => dropSuffixCI? afterWith " on her")) |>.getD afterWith
      if let some (cntSpec, some kind) := parseCounterPhrase? trimmed then
        match cntSpec with
        | .exact n => return some #[StaticAbility.entersWithCounters kind (.const n)]
        | .count v => return some #[StaticAbility.entersWithCounters kind v]
        | _ => pure ()
  if selfLow.startsWith "as " && selfLow.contains " enters, choose " then
    if selfLow.endsWith "choose a creature type" then
      return some #[StaticAbility.asEntersChooseCreatureType]
    if selfLow.endsWith "choose odd or even" then
      return some #[StaticAbility.asEntersChooseOddEven]
    if selfLow.endsWith "choose a card type" then
      return some #[StaticAbility.asEntersChooseCardType]
    if selfLow.endsWith "choose a nonland card name" then
      return some #[StaticAbility.asEntersChooseNonlandCardName]
    if selfLow.endsWith "choose a color" then
      return some #[.replacement none (.asEntersChoose .color)]
  if selfLow.startsWith "as " && selfLow.contains " enters, you may have it become a copy of any creature on the battlefield until end of turn, except it has haste" then
    return some #[StaticAbility.asEntersMayCopyCreatureHasteUntilEot]
  if selfLow.contains "if you would create a food token" && selfLow.contains "treasure" then
    return some #[StaticAbility.foodAlsoCreatesTreasure]
  if selfLow.contains "twice that many of those tokens are created instead" then
    return some #[StaticAbility.tokenDoubling]
  if let some (beforeTimes, _) := splitFirstCI? selfLow " times that many of those tokens are created instead" then
    let factorWord := (beforeTimes.splitOn ",").getLastD beforeTimes |>.trimAscii.copy
    if let some factor := parseNatWord? factorWord then
      if factor > 1 then
        return some #[.replacement none (.multiplyTokens .you factor)]
  if selfLow.contains "except the first one you draw in each of your draw steps" then
    return some #[StaticAbility.drawTwoExceptFirstDrawStep]
  if selfLow == "if you would lose unspent mana, that mana becomes colorless instead" then
    return some #[StaticAbility.unspentManaBecomesColorless]

  -- 7. Continuous abilities previously stored as CardDef fields
  if selfLow.contains "creatures you control have" && selfLow.contains "add one mana of any color" then
    return some #[StaticAbility.grantCreaturesTapAddAnyColor]
  if selfLow.contains "lands you control have" && selfLow.contains "add one mana of any color" then
    return some #[StaticAbility.grantLandsTapAnyColor]
  if selfLow.contains "lore counters among sagas you control" && selfLow.contains "hexproof and indestructible" then
    if let some (_, afterAre) := splitFirstCI? selfLow "there are " then
      let numWord := (afterAre.splitOn " ").headD ""
      if let some n := parseNatWord? numWord then
        return some #[StaticAbility.hexproofIndestructibleIfLore n]
  if selfLow.contains "for each mountain you control" && selfLow.contains "gets +" then
    if let some (_, afterPlus) := splitFirstCI? selfLow "gets +" then
      let digits := (afterPlus.takeWhile Char.isDigit).copy
      if !digits.isEmpty then
        return some #[StaticAbility.powerPerMountain digits.toNat!]
  if selfLow.contains "gets +1/+1 for each unspent mana you have" then
    return some #[StaticAbility.powerPerUnspentMana]
  if selfLow == "you and creatures you control have protection from the chosen card type" then
    return some #[StaticAbility.protectionFromChosenCardType]
  if selfLow.contains "creatures you control with toxic have lifelink" then
    return some #[StaticAbility.corruptedToxicLifelink]
  if selfLow == "if a creature an opponent controls would die, exile it instead" then
    return some #[StaticAbility.exileOpponentsDyingCreatures]

  return none

/-- Compositional fallback parser for novel static abilities not already present in the
catalog prototype index (e.g. novel conditional lord buffs, novel spell cost modifiers,
novel combat/player rules, novel CDAs). Invoked only after exact structural & prototype
matching fails so existing catalog ASTs remain canonical. -/
def parseNovelStaticAbilityLine (raw : String) (cardName : String := "") :
    Option (Array StaticAbility) := Id.run do
  let cleaned := cleanClause (stripReminderText raw)
  if cleaned.isEmpty then return none
  let low := lower cleaned
  if low.startsWith "when " || low.startsWith "whenever " || low.startsWith "at the beginning" then
    return none
  let beforeQuote := (cleaned.splitOn "\"").headD cleaned
  if beforeQuote.contains ':' then
    return none

  let selfNorm := cleanClause (replaceSelfName cleaned cardName "this permanent")

  -- Peel optional leading condition (`"As long as <cond>, <body>"` / `"During your turn, <body>"`)
  let (cond?, body) : Option Condition × String :=
    if let some rest := dropPrefixCI? selfNorm "during your turn, " then
      (some .isYourTurn, rest)
    else if let some rest := dropPrefixCI? selfNorm "as long as " then
      match splitFirstCI? rest ", " with
      | some (condStr, restBody) =>
        match parseStaticCondition? condStr cardName with
        | some c => (some c, restBody)
        | none => (none, selfNorm)
      | none => (none, selfNorm)
    else (none, selfNorm)

  let bLow := lower body

  -- Novel additional lands: `"you may play N additional land(s) on each of your turns"`
  if let some rest := dropPrefixCI? bLow "you may play " then
    if let some beforeAdd := (dropSuffixCI? rest " on each of your turns").orElse
        (fun _ => some rest) then
      if beforeAdd == "an additional land" then
        return some #[.ruleModifying cond? (.player (.additionalLands .you 1))]
      if let some nStr := dropSuffixCI? beforeAdd " additional lands" then
        if let some n := parseNatWord? nStr then
          return some #[.ruleModifying cond? (.player (.additionalLands .you n))]

  -- Novel player hexproof / protection
  if bLow == "you have hexproof" then
    return some #[.ruleModifying cond? (.player (.hexproof .you none))]
  if let some qStr := dropPrefixCI? bLow "you have protection from " then
    if let some (.protection q) := parseKeywordAbility s!"protection from {qStr}" then
      return some #[.ruleModifying cond? (.player (.protectionFrom .you q))]

  -- Novel spell cost modifiers: `"<type/subtype/supertype> spells you cast / your opponents cast cost {N} less/more to cast"`
  if let some (subjPart, costPart) := (splitFirstCI? body " cost ").orElse
      (fun _ => splitFirstCI? body " costs ") then
    let cLow := lower costPart
    let isLess := cLow.contains " less to cast"
    let isMore := cLow.contains " more to cast"
    if isLess || isMore then
      if let some n := firstGenericBraceNat? costPart then
        let (caster?, predStr?) : Option PlayerFilter × Option String :=
          match dropSuffixCI? subjPart " spells you cast" with
          | some p => (some .you, some p)
          | none =>
            match dropSuffixCI? subjPart " spells your opponents cast" with
            | some p => (some .opponent, some p)
            | none => (none, none)
        if let (some caster, some predStr) := (caster?, predStr?) then
          let pLow := lower predStr
          let spellPred? : Option ObjectPred :=
            if pLow == "noncreature" then some (.not (.hasType .creature))
            else if let some ty := CardType.ofOracle? pLow then some (.hasType ty)
            else if let some sup := Supertype.ofOracle? pLow then some (.hasSupertype sup)
            else if let some sub := CardSubtype.ofOracle? predStr then some (.hasSubtype (.literal sub))
            else none
          if let some sp := spellPred? then
            let cm : CostModification :=
              if isLess then .reduceGeneric (.const n) else .increaseGeneric (.const n)
            return some #[.costModifier cond? (.spells caster sp) cm]

  -- Novel CDA: `"this creature's power and toughness are each equal to <valueExpr>"` / `"this creature's power is equal to <valueExpr>"`
  if let some vStr := dropPrefixCI? bLow "this permanent's power and toughness are each equal to " then
    if let some v := parseValueExpr vStr then
      return some #[.characteristicDefining (.setPT (some v) (some v))]
  if let some vStr := dropPrefixCI? bLow "this creature's power and toughness are each equal to " then
    if let some v := parseValueExpr vStr then
      return some #[.characteristicDefining (.setPT (some v) (some v))]
  if let some vStr := (dropPrefixCI? bLow "this permanent's power is equal to ").orElse
      (fun _ => dropPrefixCI? bLow "this creature's power is equal to ") then
    if let some v := parseValueExpr vStr then
      return some #[.characteristicDefining (.setPT (some v) none)]

  -- Novel continuous scope + gets +P/+T and/or has/have <keywords>
  let parseScope? (subjRaw : String) : Option ObjectFilter :=
    let sLow := lower (cleanClause subjRaw)
    if isSelfObjectPhrase sLow then some StaticAbility.scopeSelf
    else if sLow == "equipped creature" then some StaticAbility.scopeEquippedCreature
    else if sLow == "enchanted creature" then some StaticAbility.scopeEnchantedCreature
    else if sLow == "enchanted permanent" then some StaticAbility.scopeEnchantedPermanent
    else if sLow == "creatures you control" then some StaticAbility.scopeCreaturesYouControl
    else if sLow == "other creatures you control" then some StaticAbility.scopeOtherCreaturesYouControl
    else if sLow == "creatures your opponents control" then some StaticAbility.scopeOpponentsCreatures
    else if sLow == "lands you control" then some StaticAbility.scopeLandsYouControl
    else if sLow == "planeswalkers you control" then some StaticAbility.scopePlaneswalkersYouControl
    else
      (parseNounPhrase subjRaw).map (·.filter)

  -- Case 1: `"<scope> get(s) +P/+T and have/has <keywords>"`
  let splitGets? := (splitFirstCI? body " get ").orElse (fun _ => splitFirstCI? body " gets ")
  if let some (subjStr, afterGets) := splitGets? then
    if let some sc := parseScope? subjStr then
      let splitAndHas? := (splitFirstCI? afterGets " and have ").orElse
        (fun _ => splitFirstCI? afterGets " and has ")
      match splitAndHas? with
      | some (ptStr, kwStr) =>
        if let (some (p, t), some kws) := (parsePTBonus? ptStr, parseGrantedKeywordsList? kwStr) then
          return some #[.continuous cond? sc (.all #[.modifyPT (.const p) (.const t), .grantKeywords kws])]
      | none =>
        if let some (p, t) := parsePTBonus? afterGets then
          return some #[.continuous cond? sc (.modifyPT (.const p) (.const t))]

  -- Case 2: `"<scope> have/has <keywords>"`
  let splitHas? := (splitFirstCI? body " have ").orElse (fun _ => splitFirstCI? body " has ")
  if let some (subjStr, kwStr) := splitHas? then
    if !kwStr.contains '"' then
      if let (some sc, some kws) := (parseScope? subjStr, parseGrantedKeywordsList? kwStr) then
        return some #[.continuous cond? sc (.grantKeywords kws)]

  return none

/-! ## Stage-4 Compositional Trigger Clause Parser (`parseTriggerClause`) -/

/-- Structured header of a triggered ability parsed by `parseTriggerClause` (CR 603.1 / 603.4). -/
structure ParsedTriggerHeader where
  word : TriggerWord
  pattern : TriggerPattern
  grouping : BatchGrouping := .perOccurrence
  interveningIf? : Option Condition := none
  activeZones : Array ZoneKind := #[.battlefield]
  limit : TriggerLimit := .unlimited
  effectText : String
deriving Repr, Inhabited, BEq

private def parseTriggerSubjectPred? (raw : String) (cardName : String) :
    Option (ObjectPred × Bool) := Id.run do
  let s0 := cleanClause (replaceSelfName raw cardName "this permanent")
  -- Normalize canonical `Expr.toOracle` `"a permanent permanent that is this permanent or <rest>"`
  let s :=
    if let some r := dropPrefixCI? s0 "a permanent permanent that is this permanent or " then
      "this or " ++ r
    else if let some r := dropPrefixCI? s0 "a permanent that is this permanent or " then
      "this or " ++ r
    else s0
  let (rest, isBatch) : String × Bool :=
    match dropPrefixCI? s "one or more " with
    | some r => (r, true)
    | none => (s, false)
  let rLow := lower rest
  if isSelfObjectPhrase rLow then
    return some (.sameAs .this, isBatch)
  if rLow == "enchanted creature" || rLow == "enchanted permanent" || rLow == "equipped creature" then
    return some (.sameAs .attachedHost, isBatch)
  -- `"this or another <rest>"` / `"this or <rest>"` (`Fíli`, `Balin`, `Thorin`, `Mabel`, `Proctor`)
  if let some rhs := (dropPrefixCI? rest "this or another ").orElse
      (fun _ => (dropPrefixCI? rest "this permanent or another ").orElse
        (fun _ => (dropPrefixCI? rest "this creature or another ").orElse
          (fun _ => dropPrefixCI? rest "this or "))) then
    if let some np := parseNounPhrase rhs then
      return some (.any #[.sameAs .this, np.filter.pred], isBatch)
  -- Strip leading `"a "` / `"an "` / `"another "` cleanly via `parseNounPhrase`.
  if let some np := parseNounPhrase rest then
    return some (np.filter.pred, isBatch)
  return none

private def parseStepClause? (clause : String) : Option TriggerPattern := Id.run do
  let l := lower (cleanClause clause)
  let some rest := dropPrefixCI? l "the beginning of " | return none
  if rest == "your upkeep" then return some .stepYourUpkeep
  if rest == "each upkeep" || rest == "each player's upkeep" then return some .stepEachUpkeep
  if rest == "each opponent's upkeep" || rest == "an opponent's upkeep" then
    return some (.stepBegins .upkeep (.player .opponent))
  if rest == "the next upkeep" || rest == "each upkeep" || rest == "each player's upkeep" then
    return some .stepEachUpkeep
  if rest == "the upkeep of enchanted creature's controller" then
    return some .stepEnchantedControllerUpkeep
  if rest == "your draw step" then return some (.stepBegins .draw (.player .you))
  if rest == "each opponent's draw step" then return some .stepEachOpponentDrawStep
  if rest == "each player's draw step" || rest == "each draw step" then
    return some (.stepBegins .draw (.player .any))
  if rest == "your first main phase" || rest == "your precombat main phase" then
    return some .stepYourFirstMain
  if rest == "combat on your turn" || rest == "your combat phase" then
    return some .stepYourBeginCombat
  if rest == "combat on each opponent's turn" then return some .stepOpponentBeginCombat
  if rest == "each combat" then return some .stepEachBeginCombat
  if rest == "your end step" then return some .stepYourEndStep
  if rest == "each end step" || rest == "the end step" || rest == "the next end step" then
    return some .stepEachEndStep
  if rest == "each opponent's end step" then
    return some (.stepBegins .end (.player .opponent))
  return none

private def parseOrdinalWord? (w : String) : Option Nat :=
  match lower w with
  | "first" | "1st" => some 1
  | "second" | "2nd" => some 2
  | "third" | "3rd" => some 3
  | "fourth" | "4th" => some 4
  | "fifth" | "5th" => some 5
  | "sixth" | "6th" => some 6
  | "seventh" | "7th" => some 7
  | "eighth" | "8th" => some 8
  | "ninth" | "9th" => some 9
  | "tenth" | "10th" => some 10
  | _ => none

private partial def parseAtomicTriggerEvent? (clause : String) (cardName : String) :
    Option (TriggerPattern × BatchGrouping × TriggerLimit × Array ZoneKind) := Id.run do
  let s := cleanClause (replaceSelfName clause cardName "this permanent")
  let l := lower s

  -- Step triggers (`"At the beginning of ..."`)
  if let some sp := parseStepClause? s then
    return some (sp, .perOccurrence, .unlimited, #[.battlefield])

  -- `"the Ring tempts you"` / `"you choose a creature as your Ring-bearer"` (CR 701.54)
  if l == "the ring tempts you" then
    return some (.playerAction .you .ringTempts, .perOccurrence, .unlimited, #[.battlefield])
  if l == "you choose a creature as your ring-bearer" then
    return some (.playerAction .you .chooseRingBearer, .perOccurrence, .unlimited, #[.battlefield])

  -- `"the final chapter ability of a Saga you control resolves"` (`Tom Bombadil`)
  if l == "the final chapter ability of a saga you control resolves" then
    return some (.stackObjectResolves (.all #[.hasSubtype (.literal .saga), .controlledBy .you]) true,
      .perOccurrence, .unlimited, #[.battlefield])

  -- `"that mana is spent to cast a creature spell that shares a creature type with your commander"` (`Path of Ancestry`)
  if l.startsWith "that mana is spent to cast " then
    let castRest := (dropPrefixCI? s "that mana is spent to cast ").getD ""
    if (lower castRest).contains "shares a creature type with your commander" then
      let allZones : ZoneSetSpec :=
        { zones := #[.library, .hand, .battlefield, .graveyard, .stack, .exile, .command], owner := .any }
      let pred : ObjectPred := .all #[.hasType .creature, .shares .creatureType (.inZones allZones (.all #[.isCommander, .ownedBy .you]))]
      return some (.castSpell .you pred (manaSpent? := some .fromSource), .perOccurrence, .unlimited, #[.battlefield])

  -- `"the <ordinal> <counter> counter is put on <subj>"` (Plan / counter-threshold triggers, CR 715.2b)
  if let some restThe := dropPrefixCI? s "the " then
    if let some (ordCtr, onSubj) := splitFirstCI? restThe " counter is put on " then
      let ws := splitWords ordCtr
      if ws.size >= 2 then
        if let some ord := parseOrdinalWord? ws[0]! then
          let kWords := (ws.extract 1 ws.size).toList.map lower
          if let some (k, _) := CounterKind.ofPrefix kWords then
            if let some (pred, _) := parseTriggerSubjectPred? onSubj cardName then
              return some (.putCounters none (some k) pred, .counterThreshold k #[ord], .unlimited, #[.battlefield])

  -- `"<A> and whenever <B>"` / `"<A> and when <B>"` / `"<A> or <B>"` disjunctions:
  if let some (lhs, rhs) := (splitFirstCI? s " and whenever ").orElse
      (fun _ => splitFirstCI? s " and when ") then
    if let (some (p1, g1, l1, z1), some (p2, g2, l2, z2)) :=
        (parseAtomicTriggerEvent? lhs cardName, parseAtomicTriggerEvent? rhs cardName) then
      if g1 == g2 && l1 == l2 && z1 == z2 then
        return some (.or p1 p2, g1, l1, z1)

  -- Homogeneous `"<ev1> or <ev2>"` (`Orcish Bowmasters`: `"this permanent enters or an opponent draws ..."`, `Danitha`: `"you cast an Equipment spell or you cast a spell that targets ..."`)
  for sep in #[" or an opponent ", " or you ", " or a player "] do
    if let some (lhs, rhsTail) := splitFirstCI? s sep then
      let rhs := ((dropPrefixCI? sep " or ").getD "") ++ " " ++ rhsTail
      if let (some (p1, g1, l1, z1), some (p2, g2, l2, z2)) :=
          (parseAtomicTriggerEvent? lhs cardName, parseAtomicTriggerEvent? rhs cardName) then
        if g1 == g2 && l1 == l2 && z1 == z2 then
          return some (.or p1 p2, g1, l1, z1)

  -- Self/subject compound verbs: `"<subj> enters or attacks"` / `"enters or dies"` / `"attacks or blocks"`
  for (sfx, mkPat) in [
      (" enters or attacks", fun p => TriggerPattern.or (.permanentEnters p) (.attacks p)),
      (" enter or attack", fun p => TriggerPattern.or (.permanentEnters p) (.attacks p)),
      (" enters or dies", fun p => TriggerPattern.or (.permanentEnters p) (.permanentDies p)),
      (" enter or die", fun p => TriggerPattern.or (.permanentEnters p) (.permanentDies p)),
      (" attacks or blocks", fun p => TriggerPattern.or (.attacks p) (.blocks p)),
      (" attack or block", fun p => TriggerPattern.or (.attacks p) (.blocks p))
    ] do
    if let some subjStr := dropSuffixCI? s sfx then
      if let some (pred, isBatch) := parseTriggerSubjectPred? subjStr cardName then
        let grp := if isBatch then BatchGrouping.oncePerBatch else .perOccurrence
        return some (mkPat pred, grp, .unlimited, #[.battlefield])

  -- Player-led events (`"you ..."`, `"an opponent ..."`, `"a player ..."`)
  let playerPrefixes : List (String × PlayerFilter) := [
    ("you ", .you),
    ("an opponent ", .opponent),
    ("any opponent ", .opponent),
    ("a player ", .any),
    ("any player ", .any)
  ]
  for (pfx, who) in playerPrefixes do
    if let some rest := dropPrefixCI? s pfx then
      let rLow := lower rest
      -- Cast spell
      if let some castBody0 := (dropPrefixCI? rest "cast ").orElse (fun _ => dropPrefixCI? rest "casts ") then
        -- Disjunctive cast trigger (`"an Equipment spell or a spell that targets <recip>"`, `Danitha`)
        if let some (cLhs, cRhs) := splitFirstCI? castBody0 " or a spell that targets " then
          let pfxVerb := pfx ++ "cast "
          match parseAtomicTriggerEvent? (pfxVerb ++ cLhs) cardName,
                parseAtomicTriggerEvent? (pfxVerb ++ "a spell that targets " ++ cRhs) cardName with
          | some (p1, g1, l1, z1), some (p2, _, _, _) =>
            return some (.or p1 p2, g1, l1, z1)
          | _, _ => pure ()
        -- Strip optional `"with one or more <color> mana symbols in its mana cost"` (`Namor`)
        let castBody :=
          match splitFirstCI? castBody0 " with one or more " with
          | some (preSym, symTail) =>
            if (lower symTail).contains "mana symbol" then preSym else castBody0
          | none => castBody0
        let cLow := lower castBody
        if cLow == "this spell" || cLow == "this card" || cLow == "this permanent" then
          return some (.castSpell who (.sameAs .this), .perOccurrence, .unlimited, #[.stack])
        -- `"a spell that targets <recip>"` (`Danitha`, `Iron Fist`, `Ms. Marvel`)
        if let some tgtPart := dropPrefixCI? castBody "a spell that targets " then
          let tLow := lower tgtPart
          let recip? : Option RecipientFilter :=
            if tLow == "an opponent or a creature an opponent controls" then
              some (.playerOrObject .opponent { zones := .battlefield, pred := .all #[.hasType .creature, .controlledBy .opponent] })
            else if let some pf := parsePlayerFilter? tgtPart then
              some (.player pf)
            else if let some np := parseNounPhrase tgtPart then
              some (.object np.filter)
            else none
          if let some recip := recip? then
            return some (.castSpell who .anyObject (targets? := some recip), .perOccurrence, .unlimited, #[.battlefield])
        -- `"your/their <ordinal> [<filter>] spell each turn"` (`The Queen of Dale`, `Saruman`)
        if let some coreTurn := dropSuffixCI? castBody " each turn" then
          let afterPoss? := (dropPrefixCI? coreTurn "your ").orElse (fun _ => dropPrefixCI? coreTurn "their ")
          if let some afterPoss := afterPoss? then
            let cws := splitWords afterPoss
            if cws.size >= 2 then
              if let some ord := parseOrdinalWord? cws[0]! then
                let tailW := String.intercalate " " (cws.extract 1 cws.size).toList
                let tailCore := (dropSuffixCI? tailW " spell").getD tailW
                let pred : ObjectPred :=
                  if lower tailCore == "spell" || tailCore.isEmpty then .anyObject
                  else if lower tailCore == "noncreature" then .not (.hasType .creature)
                  else (parseNounPhrase ("a " ++ tailCore)).map (·.filter.pred) |>.getD .anyObject
                return some (.castSpell who pred (nthOfFilter? := some ord), .perOccurrence, .unlimited, #[.battlefield])
        if cLow == "a spell" then
          return some (.castSpell who .anyObject, .perOccurrence, .unlimited, #[.battlefield])
        if cLow == "a prepared spell" then
          return some (.castSpell who .anyObject (mustBePrepared := true), .perOccurrence, .unlimited, #[.battlefield])
        let (spellCore, fromZ?) : String × Option ZoneKind :=
          match dropSuffixCI? castBody " from your hand" with
          | some pre => (pre, some .hand)
          | none =>
            match dropSuffixCI? castBody " from a graveyard" with
            | some pre => (pre, some .graveyard)
            | none => (castBody, none)
        let spellCore := (dropSuffixCI? spellCore " spell").getD spellCore
        if lower spellCore == "a noncreature" then
          return some (.castSpell who (.not (.hasType .creature)) (fromZone? := fromZ?),
            .perOccurrence, .unlimited, #[.battlefield])
        if let some np := parseNounPhrase spellCore then
          let sp := match np.filter.pred with
            | .isKind .spell => .anyObject
            | .all ps => ObjectPred.andAll (ps.filter (· != .isKind .spell))
            | other => other
          return some (.castSpell who sp (fromZone? := fromZ?),
            .perOccurrence, .unlimited, #[.battlefield])
      -- Draw card
      if rLow == "draw a card" || rLow == "draws a card" then
        return some (.drawCard who, .perOccurrence, .unlimited, #[.battlefield])
      if rLow == "draw a card except the first one they draw in each of their draw steps" ||
          rLow == "draws a card except the first one they draw in each of their draw steps" then
        return some (.drawCard who (exceptFirstDrawStep := true), .perOccurrence, .unlimited, #[.battlefield])
      if rLow == "draw your second card each turn" || rLow == "draws their second card each turn" then
        return some (.drawCard who, .perOccurrence, .nthEachTurn 2, #[.battlefield])
      -- Gain / lose life
      if rLow == "gain life" || rLow == "gains life" then
        return some (.gainLife who, .perOccurrence, .unlimited, #[.battlefield])
      if rLow == "lose life" || rLow == "loses life" then
        return some (.loseLife who, .perOccurrence, .unlimited, #[.battlefield])
      -- Discard / cycle
      if rLow == "discard this card" || rLow == "discard this permanent" then
        return some (.discard who (.sameAs .this), .perOccurrence, .unlimited, #[.hand])
      if rLow == "cycle this card" || rLow == "cycle this permanent" then
        return some (.discard who (.sameAs .this) (mustBeCycle := true), .perOccurrence, .unlimited, #[.hand])
      if rLow == "discard a card" || rLow == "discards a card" then
        return some (.discard who .anyObject, .perOccurrence, .unlimited, #[.battlefield])
      if rLow == "discard one or more cards" || rLow == "discards one or more cards" then
        return some (.discard who .anyObject, .oncePerBatch, .unlimited, #[.battlefield])
      -- Player actions
      if rLow == "scry" || rLow == "scries" then
        return some (.playerAction who .scry, .perOccurrence, .unlimited, #[.battlefield])
      if rLow == "surveil" || rLow == "surveils" then
        return some (.playerAction who .surveil, .perOccurrence, .unlimited, #[.battlefield])
      if rLow == "scry or surveil" || rLow == "scries or surveils" then
        return some (.or (.playerAction who .scry) (.playerAction who .surveil),
          .perOccurrence, .unlimited, #[.battlefield])
      if rLow == "proliferate" || rLow == "proliferates" then
        return some (.playerAction who .proliferate, .perOccurrence, .unlimited, #[.battlefield])
      if rLow == "lose the game" || rLow == "loses the game" then
        return some (.playerAction who .losesGame, .perOccurrence, .unlimited, #[.battlefield])
      -- Sacrifice
      if let some sacStr := (dropPrefixCI? rest "sacrifice ").orElse (fun _ => dropPrefixCI? rest "sacrifices ") then
        if let some (pred, isBatch) := parseTriggerSubjectPred? sacStr cardName then
          let grp := if isBatch then BatchGrouping.oncePerBatch else .perOccurrence
          return some (.sacrifice who pred, grp, .unlimited, #[.battlefield])
      -- Create tokens
      if let some tokStr := (dropPrefixCI? rest "create ").orElse (fun _ => dropPrefixCI? rest "creates ") then
        let tokCore := ((dropSuffixCI? tokStr " tokens").orElse fun _ => dropSuffixCI? tokStr " token") |>.getD tokStr
        if let some (pred, isBatch) := parseTriggerSubjectPred? tokCore cardName then
          let grp := if isBatch then BatchGrouping.oncePerBatch else .perOccurrence
          return some (.createTokens who pred, grp, .unlimited, #[.battlefield])
      -- Activate loyalty / mana / general ability
      if rLow == "activate a loyalty ability" || rLow == "activates a loyalty ability" then
        return some (.activateAbility who .anyObject (.loyalty 0), .perOccurrence, .unlimited, #[.battlefield])
      if rLow == "tap a permanent for mana" || rLow == "taps a permanent for mana" then
        return some (.activateAbility who .anyObject .manaAbility, .perOccurrence, .unlimited, #[.battlefield])
      if let some tapBody := (dropPrefixCI? rest "tap ").orElse (fun _ => dropPrefixCI? rest "taps ") then
        if let some permStr := dropSuffixCI? tapBody " for mana" then
          if let some (pred, _) := parseTriggerSubjectPred? permStr cardName then
            let fullPred :=
              if (lower permStr).contains "control" then pred
              else ObjectPred.andAll #[pred, .controlledBy who]
            return some (.activateAbility who fullPred .manaAbility, .perOccurrence, .unlimited, #[.battlefield])
      if let some srcStr := (dropPrefixCI? rest "activate a mana ability of ").orElse
          (fun _ => dropPrefixCI? rest "activates a mana ability of ") then
        if let some (pred, _) := parseTriggerSubjectPred? srcStr cardName then
          return some (.activateAbility who pred .manaAbility, .perOccurrence, .unlimited, #[.battlefield])
      if let some srcStr := (dropPrefixCI? rest "activate an ability of ").orElse
          (fun _ => dropPrefixCI? rest "activates an ability of ") then
        if let some (pred, _) := parseTriggerSubjectPred? srcStr cardName then
          return some (.activateAbility who pred .any, .perOccurrence, .unlimited, #[.battlefield])
      -- Attack (`"Whenever you attack"`, `"Whenever you attack with one or more <Sub>"`, `"Whenever you attack with creatures with total power N or greater [for the first time each turn]"`)
      if rLow == "attack" || rLow == "attacks" then
        return some (.attacks (.all #[.hasType .creature, .controlledBy who]),
          .oncePerBatch, .unlimited, #[.battlefield])
      if let some atkRest0 := (dropPrefixCI? rest "attack with ").orElse (fun _ => dropPrefixCI? rest "attacks with ") then
        let (atkRest, firstTimeLimit) : String × TriggerLimit :=
          match dropSuffixCI? atkRest0 " for the first time each turn" with
          | some pre => (pre, .onceEachTurn)
          | none => (atkRest0, .unlimited)
        if let some (_, powPart) := splitFirstCI? atkRest " with total power " then
          if let some nStr := dropSuffixCI? powPart " or greater" then
            if let some n := parseNatWord? nStr then
              return some (.attacks (.all #[.hasType .creature, .controlledBy who]) .any false 1 (some (Int.ofNat n)),
                .oncePerBatch, firstTimeLimit, #[.battlefield])
        if let some (pred, _) := parseTriggerSubjectPred? atkRest cardName then
          let fullPred :=
            match pred with
            | .all ps => .all (ps.push (.controlledBy who))
            | p => .all #[p, .controlledBy who]
          return some (.attacks fullPred, .oncePerBatch, firstTimeLimit, #[.battlefield])
      -- Put counters (`"you put one or more [+1/+1] counters on <subj>"`)
      if let some putRest := (dropPrefixCI? rest "put ").orElse (fun _ => dropPrefixCI? rest "puts ") then
        if let some (ctrPart, subjPart) := splitFirstCI? putRest " on " then
          let ctrLow := lower ctrPart
          let isBatch := ctrLow.startsWith "one or more "
          let ctrWords := (splitWords ctrLow).toList
          let strippedWords :=
            match ctrWords with
            | "one" :: "or" :: "more" :: ws => ws
            | "a" :: ws | "an" :: ws => ws
            | ws => ws
          let kind? : Option CounterKind := (CounterKind.ofPrefix strippedWords).map (·.1)
          if let some (pred, subjBatch) := parseTriggerSubjectPred? subjPart cardName then
            let grp := if isBatch || subjBatch then BatchGrouping.oncePerBatch else .perOccurrence
            return some (.putCounters (some who) kind? pred, grp, .unlimited, #[.battlefield])

  -- Counter threshold trigger (`"the fifth plan counter is put on this enchantment"`, `"the Nth <kind> counter is put on <subj>"`)
  if let some rest := dropPrefixCI? s "the " then
    if let some (ctrSpec, subjStr) := splitFirstCI? rest " counter is put on " then
      let ws := splitWords ctrSpec
      if ws.size >= 2 then
        let ord? : Option Nat :=
          match lower ws[0]! with
          | "first" | "1st" => some 1
          | "second" | "2nd" => some 2
          | "third" | "3rd" => some 3
          | "fourth" | "4th" => some 4
          | "fifth" | "5th" => some 5
          | "sixth" | "6th" => some 6
          | "seventh" | "7th" => some 7
          | "eighth" | "8th" => some 8
          | "ninth" | "9th" => some 9
          | "tenth" | "10th" => some 10
          | _ => none
        let kindWords := (ws.extract 1 ws.size).toList.map lower
        match ord?, CounterKind.ofPrefix kindWords, parseTriggerSubjectPred? subjStr cardName with
        | some n, some (k, consumed), some (pred, _) =>
          if consumed == kindWords.length then
            return some (.putCounters none (some k) pred, .counterThreshold k #[n], .unlimited, #[.battlefield])
        | _, _, _ => pure ()

  -- Player dealt damage (`"you are dealt ..."`, `"an opponent is dealt ..."`, `"one or more [of your] opponents are dealt ... [during your turn]"`)
  let (sNoTurn, duringYourTurn) : String × Bool :=
    match dropSuffixCI? s " during your turn" with
    | some pre => (pre, true)
    | none => (s, false)
  for (dmgSfx, combatOnly, noncombatOnly) in [
      (" is dealt combat damage", true, false),
      (" are dealt combat damage", true, false),
      (" is dealt noncombat damage", false, true),
      (" are dealt noncombat damage", false, true),
      (" is dealt damage", false, false),
      (" are dealt damage", false, false)
    ] do
    if let some whoStr := dropSuffixCI? sNoTurn dmgSfx then
      let wLow := lower whoStr
      if wLow == "one or more opponents" || wLow == "one or more of your opponents" then
        return some (.damageDealt .anyObject (.player .opponent) combatOnly noncombatOnly duringYourTurn,
          .oncePerBatch, .unlimited, #[.battlefield])
      if let some pf := parsePlayerFilter? whoStr then
        return some (.damageDealt .anyObject (.player pf) combatOnly noncombatOnly duringYourTurn,
          .perOccurrence, .unlimited, #[.battlefield])
      if let some (pred, isBatch) := parseTriggerSubjectPred? whoStr cardName then
        let grp :=
          if isBatch || pred == .sameAs .this then BatchGrouping.oncePerBatch
          else if !combatOnly && !noncombatOnly then .perSourceInBatch
          else .perOccurrence
        return some (.damageDealt .anyObject (.object { zones := .battlefield, pred }) combatOnly noncombatOnly duringYourTurn,
          grp, .unlimited, #[.battlefield])

  -- Subject deals damage (`"<subj> deals combat damage to a player [or planeswalker/battle] / to you"`)
  for (sfx, recip, combatOnly) in [
      (" deals combat damage to a player or planeswalker",
        RecipientFilter.playerOrObject .any { zones := .battlefield, pred := .hasType .planeswalker }, true),
      (" deal combat damage to a player or planeswalker",
        RecipientFilter.playerOrObject .any { zones := .battlefield, pred := .hasType .planeswalker }, true),
      (" deals combat damage to a player or battle",
        RecipientFilter.playerOrObject .any { zones := .battlefield, pred := .hasType .battle }, true),
      (" deal combat damage to a player or battle",
        RecipientFilter.playerOrObject .any { zones := .battlefield, pred := .hasType .battle }, true),
      (" deals combat damage to you", RecipientFilter.player .you, true),
      (" deal combat damage to you", RecipientFilter.player .you, true),
      (" deals combat damage to a player", RecipientFilter.player .any, true),
      (" deal combat damage to a player", RecipientFilter.player .any, true),
      (" deals damage to you", RecipientFilter.player .you, false),
      (" deal damage to you", RecipientFilter.player .you, false),
      (" deals damage to a player", RecipientFilter.player .any, false),
      (" deal damage to a player", RecipientFilter.player .any, false)
    ] do
    if let some subjStr := dropSuffixCI? s sfx then
      if let some (pred, isBatch) := parseTriggerSubjectPred? subjStr cardName then
        let grp := if isBatch then (if recip == .player .you then BatchGrouping.oncePerBatch else .perPlayerInBatch) else .perOccurrence
        return some (.damageDealt pred recip combatOnly, grp, .unlimited, #[.battlefield])

  -- Combat declarations (`attacks alone`, `attacks a player`, `attacks an opponent`, `attacks you or a planeswalker you control`, `N or more ... attack ...`, `attacks`, `blocks`, `becomes blocked`)
  for (sfx, mkPat) in [
      (" attacks a player alone", fun p n => TriggerPattern.attacks p (.player .any) (alone := true) (minAttackers := n)),
      (" attacks alone", fun p n => TriggerPattern.attacks p .any (alone := true) (minAttackers := n)),
      (" attacks you or a planeswalker you control", fun p n => TriggerPattern.attacks p (.playerOrPlaneswalker .you) (minAttackers := n)),
      (" attack you or a planeswalker you control", fun p n => TriggerPattern.attacks p (.playerOrPlaneswalker .you) (minAttackers := n)),
      (" attacks one of your opponents", fun p n => TriggerPattern.attacks p (.player .opponent) (minAttackers := n)),
      (" attack one of your opponents", fun p n => TriggerPattern.attacks p (.player .opponent) (minAttackers := n)),
      (" attacks an opponent", fun p n => TriggerPattern.attacks p (.player .opponent) (minAttackers := n)),
      (" attack an opponent", fun p n => TriggerPattern.attacks p (.player .opponent) (minAttackers := n)),
      (" attacks a player", fun p n => TriggerPattern.attacks p (.player .any) (minAttackers := n)),
      (" attack a player", fun p n => TriggerPattern.attacks p (.player .any) (minAttackers := n)),
      (" attacks", fun p n => TriggerPattern.attacks p (minAttackers := n)),
      (" attack", fun p n => TriggerPattern.attacks p (minAttackers := n)),
      (" blocks", fun p _ => TriggerPattern.blocks p),
      (" block", fun p _ => TriggerPattern.blocks p),
      (" becomes blocked", fun p _ => TriggerPattern.becomesBlocked p)
    ] do
    if let some subjStr0 := dropSuffixCI? s sfx then
      let (subjStr, minN, forceBatch) : String × Nat × Bool :=
        match splitFirstCI? subjStr0 " or more " with
        | some (nStr, restS) =>
          match parseNatWord? nStr with
          | some n => (restS, n, true)
          | none => (subjStr0, 1, false)
        | none => (subjStr0, 1, false)
      if let some (pred, isBatch) := parseTriggerSubjectPred? subjStr cardName then
        let pat := mkPat pred minN
        let grp :=
          if isBatch || forceBatch then
            match pat with
            | .attacks _ (.player _) _ _ _ _ => BatchGrouping.perPlayerInBatch
            | _ => .oncePerBatch
          else .perOccurrence
        return some (pat, grp, .unlimited, #[.battlefield])

  -- Targeting (`"<subj> becomes the target of ..."`)
  for (sfx, byCtrl, srcKind) in [
      (" becomes the target of a spell or ability an opponent controls", PlayerFilter.opponent, TargetingSourceKind.spellOrAbility),
      (" becomes the target of an ability you control", PlayerFilter.you, TargetingSourceKind.ability),
      (" becomes the target of a spell you control", PlayerFilter.you, TargetingSourceKind.spell),
      (" becomes the target of a spell or ability", PlayerFilter.any, TargetingSourceKind.spellOrAbility),
      (" becomes the target of a spell", PlayerFilter.any, TargetingSourceKind.spell)
    ] do
    if let some subjStr := dropSuffixCI? s sfx then
      if lower subjStr == "a player or permanent" then
        return some (.becomesTarget .playerOrPermanent byCtrl srcKind, .perOccurrence, .unlimited, #[.battlefield])
      if let some (pred, _) := parseTriggerSubjectPred? subjStr cardName then
        return some (.becomesTarget (.object pred) byCtrl srcKind, .perOccurrence, .unlimited, #[.battlefield])

  -- Tap / untap / phase out / unattach (CR 603.2e / 603.10b–c)
  if let some subjStr := dropSuffixCI? s " becomes tapped to pay a teamwork cost" then
    if let some (pred, isBatch) := parseTriggerSubjectPred? subjStr cardName then
      let grp := if isBatch then BatchGrouping.oncePerBatch else .perOccurrence
      return some (.becomesTapped pred false false (some .teamwork), grp, .unlimited, #[.battlefield])
  for (sfx, mkPat) in [
      (" becomes tapped during your turn", fun p => TriggerPattern.becomesTapped p true),
      (" become tapped during your turn", fun p => TriggerPattern.becomesTapped p true),
      (" becomes tapped", fun p => TriggerPattern.becomesTapped p),
      (" become tapped", fun p => TriggerPattern.becomesTapped p),
      (" becomes untapped", fun p => TriggerPattern.becomesUntapped p),
      (" become untapped", fun p => TriggerPattern.becomesUntapped p),
      (" phases out", fun p => TriggerPattern.phasesOut p),
      (" phase out", fun p => TriggerPattern.phasesOut p),
      (" becomes unattached", fun p => TriggerPattern.becomesUnattached p)
    ] do
    if let some subjStr := dropSuffixCI? s sfx then
      if let some (pred, isBatch) := parseTriggerSubjectPred? subjStr cardName then
        let grp := if isBatch then BatchGrouping.oncePerBatch else .perOccurrence
        return some (mkPat pred, grp, .unlimited, #[.battlefield])

  -- Zone changes (CR 603.6a, 603.6c, 603.10a, 700.4)
  for (sfx, mkPat) in [
      (" enters the battlefield", fun p => TriggerPattern.permanentEnters p),
      (" enter the battlefield", fun p => TriggerPattern.permanentEnters p),
      (" enters", fun p => TriggerPattern.permanentEnters p),
      (" enter", fun p => TriggerPattern.permanentEnters p),
      (" dies", fun p => TriggerPattern.permanentDies p),
      (" die", fun p => TriggerPattern.permanentDies p),
      (" leaves the battlefield", fun p => TriggerPattern.permanentLeaves p),
      (" leave the battlefield", fun p => TriggerPattern.permanentLeaves p),
      (" leaves your graveyard", fun p => TriggerPattern.zoneChange p (.inZones .yourGraveyard) (.notIn .graveyard)),
      (" leave your graveyard", fun p => TriggerPattern.zoneChange p (.inZones .yourGraveyard) (.notIn .graveyard)),
      (" leaves a graveyard", fun p => TriggerPattern.zoneChange p (.inZones .anyGraveyard) (.notIn .graveyard)),
      (" leave a graveyard", fun p => TriggerPattern.zoneChange p (.inZones .anyGraveyard) (.notIn .graveyard)),
      (" is put into a graveyard from the battlefield", fun p => TriggerPattern.permanentDies p),
      (" are put into a graveyard from the battlefield", fun p => TriggerPattern.permanentDies p),
      (" is put into your graveyard from anywhere",
        fun p => TriggerPattern.zoneChange p .any (.inZones .yourGraveyard)),
      (" are put into your graveyard from anywhere",
        fun p => TriggerPattern.zoneChange p .any (.inZones .yourGraveyard)),
      (" is put into a graveyard from anywhere",
        fun p => TriggerPattern.zoneChange p .any (.inZones .anyGraveyard)),
      (" are put into a graveyard from anywhere",
        fun p => TriggerPattern.zoneChange p .any (.inZones .anyGraveyard)),
      (" is returned to its owner's hand",
        fun p => TriggerPattern.zoneChange p (.inZones .battlefield)
          (.inZones { zones := #[.hand], owner := .any }))
    ] do
    if let some subjStr := dropSuffixCI? s sfx then
      if let some (pred, isBatch) := parseTriggerSubjectPred? subjStr cardName then
        let grp := if isBatch then BatchGrouping.oncePerBatch else .perOccurrence
        return some (mkPat pred, grp, .unlimited, #[.battlefield])

  -- Countered spell (CR 603.10e / 113.6)
  if let some spellStr := dropSuffixCI? s " is countered" then
    if let some (pred, _) := parseTriggerSubjectPred? spellStr cardName then
      let isSelf : Bool :=
        pred == .sameAs .this ||
          match pred with
          | .all ps => ps.contains (.sameAs .this)
          | _ => false
      let zones : Array ZoneKind := if isSelf then #[.stack] else #[.battlefield]
      return some (.spellCountered pred, .perOccurrence, .unlimited, zones)

  let _ := l
  return none

private partial def splitTriggerDisjunctClauses (word : TriggerWord) (s : String) :
    Array (TriggerWord × String) :=
  match splitFirstCI? s " and whenever " with
  | some (lhs, rhs) =>
    #[(word, lhs)] ++ splitTriggerDisjunctClauses .whenever rhs
  | none =>
    match splitFirstCI? s " and when " with
    | some (lhs, rhs) =>
      #[(word, lhs)] ++ splitTriggerDisjunctClauses .when rhs
    | none => #[(word, s)]

/-- Stage-4 compositional trigger-clause parser (CR 603.1 / 603.2 / 603.4).
Splits `"When/Whenever/At <event> [while <cond>], [if <intervening-if>,] <effect> [limit]"`
into one or more `ParsedTriggerHeader`s. Homogeneous `"<A> and when/whenever <B>"`
clauses (matching `grouping`, `limit`, and `activeZones`) merge into a single `.or`
header; heterogeneous clauses split into separate headers when `trailingLimit` is
`.unlimited` so each clause preserves its own `BatchGrouping`, `TriggerLimit`,
and `activeZones`. -/
def parseTriggerClauses (raw : String) (cardName : String := "") : Array ParsedTriggerHeader := Id.run do
  let cleaned0 := cleanClause (stripReminderText raw)
  if cleaned0.isEmpty then return #[]
  let cleaned := if cardName.contains ',' then replaceSelfName cleaned0 cardName "this permanent" else cleaned0

  -- Peel trailing turn-limit sentences
  let (withoutLimit, trailingLimit) : String × TriggerLimit :=
    if let some pre := dropSuffixCI? cleaned " This ability triggers only once each turn." then
      (cleanClause pre, .onceEachTurn)
    else if let some pre := dropSuffixCI? cleaned " This ability triggers only once each turn" then
      (cleanClause pre, .onceEachTurn)
    else if let some pre := dropSuffixCI? cleaned " Do this only once each turn." then
      (cleanClause pre, .optionalOnceEachTurn)
    else if let some pre := dropSuffixCI? cleaned " Do this only once each turn" then
      (cleanClause pre, .optionalOnceEachTurn)
    else
      (cleaned, .unlimited)

  -- Detect leading CR 603.1 trigger word
  let (word, afterWord) : TriggerWord × String ←
    if let some r := dropPrefixCI? withoutLimit "when " then
      (.when, r)
    else if let some r := dropPrefixCI? withoutLimit "whenever " then
      (.whenever, r)
    else if let some r := dropPrefixCI? withoutLimit "at " then
      (.at, r)
    else
      return #[]

  -- Try each comma split point in `afterWord` so Oxford commas inside the trigger event
  -- (e.g. `"a Goblin, Orc, or Army you control, this creature deals 2 damage..."`) don't split prematurely.
  let commaSplits := splitAllCI afterWord ", "
  if commaSplits.isEmpty then return #[]

  for (eventRaw, afterComma) in commaSplits.reverse do
    -- Peel special trigger-pattern refinements disguised as intervening-if:
    -- `"if it's the first time that creature has become tapped this turn, "` -> `firstTimeThisTurn := true`
    -- `"if that amount is N or greater, "` -> `ActivatedTriggerKind.loyalty N`
    let mut firstTimeTap := false
    let mut loyaltyMin? : Option Nat := none
    let mut afterComma1 := afterComma
    if let some rest1 := dropPrefixCI? afterComma1 "if it's the first time that creature has become tapped this turn, " then
      firstTimeTap := true
      afterComma1 := rest1
    else if let some rest1 := dropPrefixCI? afterComma1 "if that amount is " then
      if let some (nStr, rest2) := splitFirstCI? rest1 " or greater, " then
        if let some n := parseNatWord? nStr then
          loyaltyMin? := some n
          afterComma1 := rest2
    else if let some rest1 := dropPrefixCI? afterComma1 "if you removed " then
      if let some (nStr, rest2) := splitFirstCI? rest1 " or more loyalty counters to activate it, " then
        if let some n := parseNatWord? nStr then
          loyaltyMin? := some n
          afterComma1 := rest2

    -- Peel CR 603.4 intervening `"if <cond>, <effect>"` at the start of `afterComma1`
    let (interveningIf?, effectText) : Option Condition × String :=
      if let some ifRest := dropPrefixCI? afterComma1 "if " then
        -- Don't steal `"if <cond>, <then>. Otherwise, <else>"` which is an effect-level `Instruction.ifCond`!
        if (lower ifRest).contains ". otherwise," then
          (none, afterComma1.trimAscii.copy)
        else
          match splitFirstCI? ifRest ", " with
          | some (condStr, restEff) =>
            let cond? := (parseStaticCondition? condStr cardName).orElse (fun _ => parseCondition condStr)
            match cond? with
            | some c => (some c, restEff.trimAscii.copy)
            | none => (none, afterComma1.trimAscii.copy)
          | none => (none, afterComma1.trimAscii.copy)
      else (none, afterComma1.trimAscii.copy)

    if effectText.isEmpty then continue

    let effLow := lower effectText
    let refinePat (p : TriggerPattern) : TriggerPattern :=
      let p1 :=
        if firstTimeTap then
          match p with
          | .becomesTapped subj d _ ck => .becomesTapped subj d true ck
          | other => other
        else p
      let p2 :=
        match loyaltyMin? with
        | some n =>
          match p1 with
          | .activateAbility act src (.loyalty _) => .activateAbility act src (.loyalty n)
          | other => other
        | none => p1
      if effLow.contains "that many" || effLow.contains "that amount" || effLow.contains "that much" then
        match p2 with
        | .attacks subj tgt alone minAtk minPow _ => .attacks subj tgt alone minAtk minPow true
        | other => other
      else p2
    let inferZones (baseZones : Array ZoneKind) : Array ZoneKind :=
      if baseZones == #[.battlefield] && effLow.contains "from your graveyard" &&
          (effLow.contains "return this card" || effLow.contains s!"return {lower cardName}") then
        #[.graveyard]
      else baseZones

    let peelWhile (ev : String) : String × Option Condition :=
      match splitFirstCI? ev " while " with
      | some (evPart, condStr) =>
        let cond? := (parseStaticCondition? condStr cardName).orElse (fun _ => parseCondition condStr)
        match cond? with
        | some c => (evPart, some c)
        | none => (ev, none)
      | none => (ev, none)

    -- In `"Whenever a Forest you control enters, if you control at least five other Forests, ..."`,
    -- `"other"` in the intervening `"if"` refers to the entering object (`.triggerSubject`),
    -- not `this` permanent (CR 603.4, e.g. *Roiling Canopy*).
    let predHasThis (p : ObjectPred) : Bool :=
      let rec go : ObjectPred → Bool
        | .sameAs .this => true
        | .all xs | .any xs => xs.attach.any fun ⟨x, _⟩ => go x
        | _ => false
      go p
    let rec replaceOtherThisPred : ObjectPred → ObjectPred
      | .otherThan .this => .otherThan .triggerSubject
      | .all xs => .all (xs.attach.map fun ⟨x, _⟩ => replaceOtherThisPred x)
      | .any xs => .any (xs.attach.map fun ⟨x, _⟩ => replaceOtherThisPred x)
      | .not p => .not (replaceOtherThisPred p)
      | other => other
    let refineInterv (pat : TriggerPattern) (cond? : Option Condition) : Option Condition :=
      match pat, cond? with
      | .zoneChange subjPred _ _ _ _, some (.cmp op (.aggregate agg m (.inZones zs pred)) rhs) =>
        if !predHasThis subjPred then
          some (.cmp op (.aggregate agg m (.inZones zs (replaceOtherThisPred pred))) rhs)
        else cond?
      | _, _ => cond?

    let canPrintManaSpent : ManaSpentPred → Bool
      | .fromTreasure | .fromSource | .ofColor _ => true
      | _ => false
    let foldManaSpent (pat : TriggerPattern) (cond? : Option Condition) : TriggerPattern × Option Condition :=
      match pat, cond? with
      | .castSpell caster sp fromZ? none prep nth? tgt?, some (.castPred (.manaSpentMatches ms .this)) =>
        if canPrintManaSpent ms then
          (.castSpell caster sp fromZ? (some ms) prep nth? tgt?, none)
        else (pat, cond?)
      | _, _ => (pat, cond?)

    -- Fast path: single atomic event or homogeneous `"and when/whenever"` `.or`
    let (eventCore, whileCond?) := peelWhile eventRaw
    if let some (basePat0, grouping, patLimit, baseZones) := parseAtomicTriggerEvent? eventCore cardName then
      let (basePat, interv?) := foldManaSpent (refinePat basePat0) (refineInterv basePat0 interveningIf?)
      let pattern := match whileCond? with | some c => .whenCond basePat c | none => basePat
      let limit := if trailingLimit != .unlimited then trailingLimit else patLimit
      return #[{ word, pattern, grouping, interveningIf? := interv?, activeZones := inferZones baseZones, limit, effectText }]

    -- Heterogeneous `"<A> and when/whenever <B>"`: split into independent headers
    -- when no shared trailing once-per-turn cap couples them.
    if trailingLimit == .unlimited then
      let parts := splitTriggerDisjunctClauses word eventCore
      if parts.size >= 2 then
        let mut out : Array ParsedTriggerHeader := #[]
        let mut allOk := true
        for (wPart, rawPart) in parts do
          let (corePart, partWhile?) := peelWhile rawPart
          match parseAtomicTriggerEvent? corePart cardName with
          | none => allOk := false; break
          | some (basePat0, grouping, patLimit, baseZones) =>
            let (basePat, interv?) := foldManaSpent (refinePat basePat0) (refineInterv basePat0 interveningIf?)
            let pat1 := match partWhile? with | some c => .whenCond basePat c | none => basePat
            let pattern := match whileCond? with | some c => .whenCond pat1 c | none => pat1
            out := out.push {
              word := wPart
              pattern
              grouping
              interveningIf? := interv?
              activeZones := inferZones baseZones
              limit := patLimit
              effectText
            }
        if allOk && !out.isEmpty then
          return out
  return #[]

/-- Single-header convenience wrapper around `parseTriggerClauses`. Returns `none`
when the line splits into multiple heterogeneous triggers. -/
def parseTriggerClause (raw : String) (cardName : String := "") : Option ParsedTriggerHeader :=
  match parseTriggerClauses raw cardName with
  | #[hdr] => some hdr
  | _ => none

/-- Compositional fallback parser for novel triggered abilities not present in the
catalog prototype table. Composes `parseTriggerClauses` with an effect parser
`parseEffect` and rejects any effect whose body/resolution does nothing as a trigger. -/
def parseNovelTriggeredAbilityLines (raw : String) (cardName : String := "")
    (parseEffect : String → Option Effect) : Option (Array TriggeredAbility) := do
  let hdrs := parseTriggerClauses raw cardName
  if hdrs.isEmpty then none
  else
    let eff ← parseEffect hdrs[0]!.effectText
    if eff.doesNothingAsTrigger then none
    else
      some (hdrs.map fun hdr => {
        word := hdr.word
        pattern := hdr.pattern
        grouping := hdr.grouping
        interveningIf? := hdr.interveningIf?
        activeZones := hdr.activeZones
        limit := hdr.limit
        effect := eff
      })

/-- Single-ability convenience wrapper around `parseNovelTriggeredAbilityLines`. -/
def parseNovelTriggeredAbilityLine (raw : String) (cardName : String := "")
    (parseEffect : String → Option Effect) : Option TriggeredAbility :=
  match parseNovelTriggeredAbilityLines raw cardName parseEffect with
  | some #[ab] => some ab
  | _ => none

/-! ### Stage-4 Compositional One-Shot `Instruction` Sub-Grammar (CR 608 / Phase 8) -/

/-- Parse a target-or-object subject phrase, appending any new `TargetSlot` onto `slots`. -/
private def parseInstrObj (raw : String) (slots : Array TargetSlot) :
    Option (ObjectExpr × Array TargetSlot) :=
  let s := cleanClause raw
  let sLow := lower s
  if sLow == "it" || sLow == "them" || sLow == "that creature" || sLow == "that permanent" ||
      sLow == "that card" then
    if slots.isEmpty then some (.triggerSubject, slots)
    else some (.target (slots.size - 1), slots)
  else if sLow == "this creature" || sLow == "this permanent" || sLow == "this artifact" ||
      sLow == "this enchantment" || sLow == "this land" || sLow == "this planeswalker" ||
      sLow == "this card" then
    some (.this, slots)
  else if sLow.contains "target " then
    match parseTargetSlot s with
    | some slot =>
      let idx := slots.size
      some (.target idx, slots.push slot)
    | none => none
  else
    match parseObjectExpr? s with
    | some oe => some (oe, slots)
    | none => none

/-- Parse a target-or-player subject phrase, appending any new `TargetSlot` onto `slots`. -/
private def parseInstrPlayer (raw : String) (slots : Array TargetSlot) :
    Option (PlayerExpr × Array TargetSlot) :=
  let s := cleanClause raw
  let sLow := lower s
  if sLow == "you" then some (.you, slots)
  else if sLow == "each opponent" then some (.opponents, slots)
  else if sLow == "each player" then some (.eachPlayer, slots)
  else if sLow.contains "target " then
    match parseTargetSlot s with
    | some slot =>
      let idx := slots.size
      some (.target idx, slots.push slot)
    | none => none
  else
    match parsePlayerExpr? s with
    | some pe => some (pe, slots)
    | none => none

/-- Parse a damage recipient phrase (`"any target"`, `"target ..."`, `"each opponent"`,
`"each creature"`, etc.), appending any new `TargetSlot` onto `slots`. -/
private def parseInstrRecipient (raw : String) (slots : Array TargetSlot) :
    Option (RecipientExpr × Array TargetSlot) :=
  let s := cleanClause raw
  let sLow := lower s
  if sLow == "any target" then
    let idx := slots.size
    some (.targetSlot idx, slots.push { domain := .anyTarget })
  else if sLow == "each opponent" then
    some (.players .opponents, slots)
  else if sLow == "each player" then
    some (.players .eachPlayer, slots)
  else if sLow == "you" then
    some (.players .you, slots)
  else if sLow == "each creature" then
    some (.objects (.inZones .battlefield (.hasType .creature)), slots)
  else if sLow == "each creature and each planeswalker" then
    some (.objects (.inZones .battlefield (.any #[.hasType .creature, .hasType .planeswalker])), slots)
  else if sLow == "each creature and each player" then
    some (.both (.inZones .battlefield (.hasType .creature)) .eachPlayer, slots)
  else if sLow.contains "target " then
    match parseTargetSlot s with
    | some slot =>
      let idx := slots.size
      some (.targetSlot idx, slots.push slot)
    | none => none
  else
    match parsePlayerExpr? s with
    | some pe => some (.players pe, slots)
    | none =>
      match parseObjectExpr? s with
      | some oe => some (.objects oe, slots)
      | none => none

/-- Parse a count phrase (`"a"` / `"an"` / `"two"` / `"3"` / `"X"` / general `ValueExpr`). -/
private def parseInstrCount (raw : String) : Option ValueExpr :=
  let s := cleanClause raw
  let sLow := lower s
  if sLow == "a" || sLow == "an" then some (.const 1)
  else if sLow == "x" then some .chosenX
  else
    match parseNatWord? s with
    | some n => some (.const n)
    | none => parseValueExpr s

/-- Parse a predefined token name (`Food`, `Treasure`, `Clue`, `Map`, `Junk`, `Lander`,
`Mutagen`, `Vibranium`, `Heartwood`). -/
private def parsePredefinedTokenWord? (raw : String) : Option PredefinedToken :=
  match lower (cleanClause raw) with
  | "treasure" => some .treasure
  | "food" => some .food
  | "clue" => some .clue
  | "map" => some .map
  | "junk" => some .junk
  | "lander" => some .lander
  | "mutagen" => some .mutagen
  | "vibranium" => some .vibranium
  | "heartwood" => some .heartwood
  | _ => none

/-- Parse a `"Create <count> [tapped] <spec> token(s)"` body into `CreateOp.tokens`. -/
private def parseCreateTokensClause? (rest : String) : Option Instruction := Id.run do
  let s := cleanClause rest
  let words := splitWords s
  if words.size < 2 then return none
  let some cnt := parseInstrCount words[0]! | return none
  let mut idx : Nat := 1
  let mut tapped := false
  if idx < words.size && lower words[idx]! == "tapped" then
    tapped := true
    idx := idx + 1
  let tail := String.intercalate " " (words.extract idx words.size).toList
  let core? :=
    (dropSuffixCI? tail " tokens").orElse (fun _ => dropSuffixCI? tail " token")
  let some core := core? | return none
  -- Predefined tokens: `"Treasure"`, `"Food"`, `"Clue"`, etc.
  if let some pre := parsePredefinedTokenWord? core then
    return some (.create (.tokens .you cnt (.predefined pre) { tapped }))
  -- Custom creature token: `"P/T <colors...> <subtypes...> creature [with <keywords>]"`
  let (descPart, kwsPart?) :=
    match splitFirstCI? core " with " with
    | some (a, b) => (cleanClause a, some (cleanClause b))
    | none => (cleanClause core, none)
  let descCore? := dropSuffixCI? descPart " creature"
  let some descCore := descCore? | return none
  let dWords := splitWords descCore
  if dWords.size < 2 then return none
  let ptParts := dWords[0]!.splitOn "/"
  if ptParts.length != 2 then return none
  let some pVal := parseInstrCount ptParts[0]! | return none
  let some tVal := parseInstrCount ptParts[1]! | return none
  let mut colors := ColorSet.empty
  let mut subtypes : Array CardSubtype := #[]
  for w in dWords.extract 1 dWords.size do
    let wl := lower w
    if wl == "and" || wl == "colorless" then
      pure ()
    else if let some col := parseColorWord? w then
      colors := colors.insert col
    else if let some sub := CardSubtype.ofOracle? w then
      subtypes := subtypes.push sub
    else
      return none
  let kwsOpt : Option (Array KeywordAbility) :=
    match kwsPart? with
    | none => some #[]
    | some kwStr => parseGrantedKeywordsList? kwStr
  let some kws := kwsOpt | return none
  return some (.create (.tokens .you cnt (.custom {
    types := #[.creature]
    subtypes
    colors
    power? := some pVal
    toughness? := some tVal
    keywords := kws }) { tapped }))

/-- Parse one atomic one-shot instruction clause (no combinators), updating `slots`. -/
private def parseAtomicInstruction (raw : String) (cardName : String)
    (slots : Array TargetSlot) : Option (Instruction × Array TargetSlot) := Id.run do
  let norm := cleanClause (replaceSelfName raw cardName "this permanent")
  if norm.isEmpty then return none
  let lowNorm := lower norm

  -- Simple standalone keyword actions
  if lowNorm == "proliferate" then
    return some (.player (.proliferate .you), slots)
  if lowNorm == "the ring tempts you" then
    return some (.player (.temptWithRing .you), slots)
  if lowNorm == "you become the monarch" then
    return some (.player (.becomeMonarch .you), slots)
  if lowNorm == "draw a card" then
    return some (Instruction.drawFixed 1, slots)
  if lowNorm == "discard a card" then
    return some (Instruction.discardFixed 1, slots)

  -- `"Scry N"` / `"Surveil N"`
  if let some nStr := dropPrefixCI? norm "scry " then
    if let some v := parseInstrCount nStr then
      return some (.player (.scry .you v), slots)
  if let some nStr := dropPrefixCI? norm "surveil " then
    if let some v := parseInstrCount nStr then
      return some (.player (.surveil .you v), slots)

  -- `"Empower <subtype> N"`
  if let some rest := dropPrefixCI? norm "empower " then
    let ws := splitWords rest
    if ws.size == 2 then
      match CardSubtype.ofOracle? ws[0]!, parseInstrCount ws[1]! with
      | some sub, some amt => return some (.player (.empowerPlaneswalker sub amt), slots)
      | _, _ => pure ()

  -- `"Amass <subtype> N"`
  if let some rest := dropPrefixCI? norm "amass " then
    let ws := splitWords rest
    if ws.size == 2 then
      let subWord := (dropSuffixCI? ws[0]! "s").getD ws[0]!
      match CardSubtype.ofOracle? subWord, parseInstrCount ws[1]! with
      | some sub, some amt => return some (.player (.amass .you sub amt), slots)
      | _, _ => pure ()

  -- `"Add <mana>"`
  if lowNorm.startsWith "add " then
    if let some mp := parseManaProductionSpec #[norm] cardName then
      return some (.player (.addMana .you mp), slots)

  -- `"Destroy ..."` / `"Exile ..."` / `"Counter ..."` / `"Tap ..."` / `"Untap ..."`
  if let some rest := dropPrefixCI? norm "destroy " then
    if let some (obj, slots') := parseInstrObj rest slots then
      return some (Instruction.destroy obj, slots')
  if let some rest := dropPrefixCI? norm "exile " then
    if let some (obj, slots') := parseInstrObj rest slots then
      return some (Instruction.exile obj, slots')
  if let some rest := dropPrefixCI? norm "return " then
    if let some objStr := (dropSuffixCI? rest " to its owner's hand").orElse
        (fun _ => (dropSuffixCI? rest " to their owners' hands").orElse
          (fun _ => dropSuffixCI? rest " to your hand")) then
      if let some (obj, slots') := parseInstrObj objStr slots then
        return some (Instruction.bounce obj, slots')
  if let some rest := dropPrefixCI? norm "counter " then
    if let some (obj, slots') := parseInstrObj rest slots then
      return some (Instruction.counter obj, slots')
  if let some rest := dropPrefixCI? norm "tap " then
    if let some (obj, slots') := parseInstrObj rest slots then
      return some (Instruction.tap obj, slots')
  if let some rest := dropPrefixCI? norm "untap " then
    if let some (obj, slots') := parseInstrObj rest slots then
      return some (Instruction.untap obj, slots')

  -- `"Create ..."`
  if let some rest := dropPrefixCI? norm "create " then
    if let some instr := parseCreateTokensClause? rest then
      return some (instr, slots)

  -- `"Draw N cards"` / `"<player> draws N cards"`
  if let some rest := dropPrefixCI? norm "draw " then
    if let some nStr := (dropSuffixCI? rest " cards").orElse (fun _ => dropSuffixCI? rest " card") then
      if let some v := parseInstrCount nStr then
        return some (.player (.drawCards .you v), slots)
  if let some (whoStr, tail) := (splitFirstCI? norm " draws ").orElse (fun _ => splitFirstCI? norm " draw ") then
    if let some nStr := (dropSuffixCI? tail " cards").orElse (fun _ => dropSuffixCI? tail " card") then
      match parseInstrPlayer whoStr slots, parseInstrCount nStr with
      | some (who, slots'), some v => return some (.player (.drawCards who v), slots')
      | _, _ => pure ()

  -- `"Discard N cards"` / `"<player> discards N cards"`
  if let some rest := dropPrefixCI? norm "discard " then
    if let some nStr := (dropSuffixCI? rest " cards").orElse (fun _ => dropSuffixCI? rest " card") then
      if let some v := parseInstrCount nStr then
        return some (Instruction.discard v .you, slots)
  if let some (whoStr, tail) := (splitFirstCI? norm " discards ").orElse (fun _ => splitFirstCI? norm " discard ") then
    if let some nStr := (dropSuffixCI? tail " cards").orElse (fun _ => dropSuffixCI? tail " card") then
      match parseInstrPlayer whoStr slots, parseInstrCount nStr with
      | some (who, slots'), some v => return some (Instruction.discard v who, slots')
      | _, _ => pure ()

  -- `"Mill N cards"` / `"<player> mills N cards"`
  if let some rest := dropPrefixCI? norm "mill " then
    if let some nStr := (dropSuffixCI? rest " cards").orElse (fun _ => dropSuffixCI? rest " card") then
      if let some v := parseInstrCount nStr then
        return some (Instruction.mill v .you, slots)
  if let some (whoStr, tail) := (splitFirstCI? norm " mills ").orElse (fun _ => splitFirstCI? norm " mill ") then
    if let some nStr := (dropSuffixCI? tail " cards").orElse (fun _ => dropSuffixCI? tail " card") then
      match parseInstrPlayer whoStr slots, parseInstrCount nStr with
      | some (who, slots'), some v => return some (Instruction.mill v who, slots')
      | _, _ => pure ()

  -- `"You gain N life"` / `"Gain N life"` / `"<player> gains N life"` / `"loses N life"`
  if let some rest := (dropPrefixCI? norm "you gain ").orElse (fun _ => dropPrefixCI? norm "gain ") then
    if let some nStr := dropSuffixCI? rest " life" then
      if let some v := parseInstrCount nStr then
        return some (.life (.gain .you v), slots)
  if let some (whoStr, tail) := splitFirstCI? norm " gains " then
    if let some nStr := dropSuffixCI? tail " life" then
      match parseInstrPlayer whoStr slots, parseInstrCount nStr with
      | some (who, slots'), some v => return some (.life (.gain who v), slots')
      | _, _ => pure ()
  if let some rest := (dropPrefixCI? norm "you lose ").orElse (fun _ => dropPrefixCI? norm "lose ") then
    if let some nStr := dropSuffixCI? rest " life" then
      if let some v := parseInstrCount nStr then
        return some (.life (.lose .you v), slots)
  if let some (whoStr, tail) := splitFirstCI? norm " loses " then
    if let some nStr := dropSuffixCI? tail " life" then
      match parseInstrPlayer whoStr slots, parseInstrCount nStr with
      | some (who, slots'), some v => return some (.life (.lose who v), slots')
      | _, _ => pure ()

  -- `"<source> deals N damage to <recipient>"`
  if let some (srcStr, tail) := splitFirstCI? norm " deals " then
    if let some (amtStr, recStr) := splitFirstCI? tail " damage to " then
      match parseInstrObj srcStr slots, parseInstrCount amtStr with
      | some (src, slots1), some amt =>
        if let some (rec, slots2) := parseInstrRecipient recStr slots1 then
          return some (.damage (.deal src rec amt), slots2)
      | _, _ => pure ()

  -- `"Put <count> <counter> counter(s) on <obj>"`
  if let some rest := dropPrefixCI? norm "put " then
    if let some (ctrPart, objPart) := splitFirstCI? rest " on " then
      let ws := (splitWords ctrPart).toList.map lower
      if let some (n, kind, _) := CounterKind.matchPhrase ws then
        if let some (obj, slots') := parseInstrObj objPart slots then
          return some (.permanent (.modifyCounters (.put kind (.const n)) obj), slots')

  -- `"<obj> explores"` / `"<obj> connives"`
  if let some objStr := (dropSuffixCI? norm " explores").orElse (fun _ => dropSuffixCI? norm " explore") then
    if let some (obj, slots') := parseInstrObj objStr slots then
      return some (.player (.explore obj), slots')
  if let some objStr := (dropSuffixCI? norm " connives").orElse (fun _ => dropSuffixCI? norm " connive") then
    if let some (obj, slots') := parseInstrObj objStr slots then
      return some (.player (.connive obj), slots')

  -- `"<obj> gets +P/+T [and gains <kws>] until end of turn"` / `"<obj> gains <kws> until end of turn"`
  if let some core := dropSuffixCI? norm " until end of turn" then
    if let some (objStr, modStr) := (splitFirstCI? core " gets ").orElse (fun _ => splitFirstCI? core " get ") then
      if let some (obj, slots') := parseInstrObj objStr slots then
        match splitFirstCI? modStr " and gains " with
        | some (ptStr, kwStr) =>
          match parsePTBonus? ptStr, parseGrantedKeywordsList? kwStr with
          | some (p, t), some kws =>
            return some (.installEffect (.applyContinuous .untilEndOfTurn obj
              (.all #[.modifyPT (.const p) (.const t), .grantKeywords kws])), slots')
          | _, _ => pure ()
        | none =>
          if let some (p, t) := parsePTBonus? modStr then
            return some (Instruction.pumpFixed obj p t, slots')
    else if let some (objStr, kwStr) := (splitFirstCI? core " gains ").orElse (fun _ => splitFirstCI? core " gain ") then
      if let some (obj, slots') := parseInstrObj objStr slots then
        if let some kws := parseGrantedKeywordsList? kwStr then
          return some (Instruction.grantKeywords obj kws, slots')

  return none

/-- Parse one combinator-wrapped or sequential clause (`You may ...`, `If ..., ...`,
`... unless <player> pays <cost>`, `..., then ...`), updating `slots`. -/
private partial def parseClause (raw : String) (cardName : String)
    (slots : Array TargetSlot) : Option (Instruction × Array TargetSlot) :=
  let s := cleanClause raw
  if s.isEmpty then none
  else if let some (lhs, rhs) := splitFirstCI? s ", then " then
    do
      let (i1, slots1) ← parseClause lhs cardName slots
      let (i2, slots2) ← parseClause rhs cardName slots1
      some (.seq #[i1, i2], slots2)
  else if let some (actionStr, unlessTail) := splitFirstCI? s " unless " then
    match splitFirstCI? unlessTail " pays " with
    | some (payerStr, costStr) =>
      do
        let (act, slots1) ← parseClause actionStr cardName slots
        let (payer, slots2) ← parseInstrPlayer payerStr slots1
        let cost ← parseCostSpec (replaceSelfName costStr cardName "this permanent")
        some (.unlessPays payer cost act, slots2)
    | none => parseAtomicInstruction s cardName slots
  else if let some rest := dropPrefixCI? s "you may " then
    do
      let (inner, slots1) ← parseClause rest cardName slots
      some (.optional .you none inner .noop, slots1)
  else if let some ifRest := dropPrefixCI? s "if " then
    match splitFirstCI? ifRest ", " with
    | some (condStr, thenStr) =>
      let condNorm := replaceSelfName condStr cardName "this permanent"
      match (parseStaticCondition? condNorm cardName).orElse (fun _ => parseCondition condNorm) with
      | some c =>
        do
          let (inner, slots1) ← parseClause thenStr cardName slots
          some (.ifCond c inner .noop, slots1)
      | none => parseAtomicInstruction s cardName slots
    | none => parseAtomicInstruction s cardName slots
  else
    parseAtomicInstruction s cardName slots

/-- Stage-4 compositional Oracle parser for one-shot `Instruction` sequences
(CR 608 / Phase 8): handles modal `•` bullets, sentence sequences, `"You may pay
<cost>. If you do, ..."`, `", then "`, `"You may ..."`, `"If <cond>, ..."`,
`"... unless <player> pays <cost>"`, and verb-dispatched atomic MTG actions,
collecting inferred `TargetSlot`s in printed order. -/
partial def parseInstructionSeq (raw : String) (cardName : String := "") :
    Option (Instruction × Array TargetSlot) := Id.run do
  let cleaned := (stripReminderText raw).trimAscii.copy
  if cleaned.isEmpty then return none

  -- Modal bullets (`"Choose one — • ... • ..."`, `"Choose one or both — ..."`, `"Choose two — ..."`)
  if cleaned.contains "•" then
    let parts := cleaned.splitOn "•" |>.map (·.trimAscii.copy) |>.filter (!·.isEmpty)
    match parts with
    | header :: modeTexts =>
      if modeTexts.isEmpty then return none
      let hLow := lower header
      let (minM, maxM) : Nat × Nat :=
        if hLow.contains "choose one or both" then (1, 2)
        else if hLow.contains "choose two" then (2, 2)
        else if hLow.contains "choose one" then (1, 1)
        else (0, 0)
      if minM == 0 then return none
      let mut modes : Array Effect := #[]
      for mText in modeTexts do
        match parseInstructionSeq mText cardName with
        | some (mBody, mSlots) =>
          modes := modes.push {
            targets := { slots := mSlots }
            body := mBody
          }
        | none => return none
      return some (.chooseModes {
        minModes := .const minM
        maxModes := .const maxM
        modes }, #[])
    | _ => return none

  let sents := splitSentences cleaned
  if sents.isEmpty then return none

  let mut steps : Array Instruction := #[]
  let mut slots : Array TargetSlot := #[]
  let mut idx : Nat := 0
  while idx < sents.size do
    let sent := sents[idx]!
    -- Combine `"You may pay <cost>. If you do, <effect>"` across two sentences.
    let mut handledPair := false
    if let some costStr := dropPrefixCI? sent "you may pay " then
      if idx + 1 < sents.size then
        if let some followStr := dropPrefixCI? sents[idx + 1]! "if you do, " then
          let costNorm := replaceSelfName costStr cardName "this permanent"
          if let some cost := parseCostSpec costNorm then
            if let some (followInstr, slots') := parseClause followStr cardName slots then
              steps := steps.push (.optional .you (some cost) followInstr .noop)
              slots := slots'
              idx := idx + 2
              handledPair := true
    if !handledPair then
      match parseClause sent cardName slots with
      | some (instr, slots') =>
        steps := steps.push instr
        slots := slots'
        idx := idx + 1
      | none => return none

  if steps.isEmpty then return none
  else if steps.size == 1 then return some (steps[0]!, slots)
  else return some (.seq steps, slots)

/-- Parse a complete Oracle effect text directly into a unified Phase-8 `Effect`
via `parseInstructionSeq`. -/
def parseInstructionEffect (raw : String) (cardName : String := "") : Option Effect :=
  match parseInstructionSeq raw cardName with
  | some (body, slots) =>
    let eff : Effect := {
      targets := { slots }
      body
    }
    if eff.doesNothingAsSpell then none else some eff
  | none => none

end Mtg.Engine.Parser
