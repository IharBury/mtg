import Mtg.Engine.Card.Ability
import Mtg.Engine.Card.Token
import Mtg.Engine.Card.Parser.Lexer
import Mtg.Engine.Card.Parser.SubGrammars
import Mtg.Engine.Card.Parser.DiscourseBind

/-!
# Stage-4b-i Compositional Token, Copy-Modification & Emblem Grammar (CR 111, 114, 707.9)

Compositional parsers for:
- `QuotedAbilityParsers` recursive callback record tying `"..."` quoted abilities
  across `Instruction`, `TokenSpec`, `EmblemSpec`, `CopyModification`, and `StaticAbility`.
- `GrantedAbility` (`keyword`, `activated`, `triggered`, `static`).
- `CopyModification` (`"except ..."` clauses on copy tokens & copy effects).
- `TokenSpec` + `EnterMods` (`predefined`, card-name-shorthand, `copyOf`, and
  arbitrary `custom` creature/artifact/planeswalker/enchantment tokens).
- `EmblemSpec` (`"an emblem with \"...\""`).
-/

namespace Mtg.Engine.Parser

open Mtg.Engine
open Mtg.Engine.OracleNorm

/-- Recursive parsers for `"..."` quoted sub-abilities passed into Stage-4b
token/emblem/instruction grammars and tied by `AbilityGrammar`. -/
structure QuotedAbilityParsers where
  parseStatic : String → String → Option StaticAbility
  parseTriggered : String → String → Option TriggeredAbility
  parseActivated : String → String → Option ActivatedAbility
  parseEffect : String → String → Option Effect

/-- Empty default callbacks (used in standalone unit checks before tying the knot). -/
def QuotedAbilityParsers.empty : QuotedAbilityParsers := {
  parseStatic := fun _ _ => none
  parseTriggered := fun _ _ => none
  parseActivated := fun _ _ => none
  parseEffect := fun _ _ => none
}

instance : Inhabited QuotedAbilityParsers := ⟨QuotedAbilityParsers.empty⟩

/-! ### Shared Quote-Aware Clause & String Utilities -/

def pLower (s : String) : String := lowerAscii s

def pClean (s : String) : String := Id.run do
  let mut r := (collapseWs (normalizeTypography s)).trimAscii.copy
  while r.endsWith "." || r.endsWith "," || r.endsWith ";" do
    r := (r.dropEnd 1).trimAscii.copy
  return r

def pWords (s : String) : Array String :=
  ((collapseWs s).trimAscii.copy.splitOn " ").filter (!·.isEmpty) |>.toArray

def pDropPrefixCI? (s pfx : String) : Option String :=
  if (pLower s).startsWith (pLower pfx) then
    some ((s.drop pfx.length).trimAscii.copy)
  else none

def pDropSuffixCI? (s sfx : String) : Option String :=
  if (pLower s).endsWith (pLower sfx) then
    some ((s.dropEnd sfx.length).trimAscii.copy)
  else none

/-- Split `s` on the first occurrence of `sep` (case-insensitive) outside `"..."` quotes. -/
def pSplitFirstCI? (s sep : String) : Option (String × String) := Id.run do
  if sep.isEmpty then return none
  let cs := s.toList.toArray
  let lowCs := (pLower s).toList.toArray
  let sepCs := (pLower sep).toList.toArray
  if sepCs.size > lowCs.size then return none
  let mut inQuote := false
  for i in [0 : lowCs.size - sepCs.size + 1] do
    if cs[i]! == '"' then
      inQuote := !inQuote
    else if !inQuote then
      let mut ok := true
      for j in [0 : sepCs.size] do
        if lowCs[i + j]! != sepCs[j]! then
          ok := false
          break
      if ok then
        let lhs := (String.ofList (cs.extract 0 i).toList).trimAscii.copy
        let rhs := (String.ofList (cs.extract (i + sepCs.size) cs.size).toList).trimAscii.copy
        return some (lhs, rhs)
  return none

/-- Split `s` on the last occurrence of `sep` (case-insensitive) outside `"..."` quotes. -/
def pSplitLastCI? (s sep : String) : Option (String × String) := Id.run do
  if sep.isEmpty then return none
  let cs := s.toList.toArray
  let lowCs := (pLower s).toList.toArray
  let sepCs := (pLower sep).toList.toArray
  if sepCs.size > lowCs.size then return none
  let mut inQuote := false
  let mut found? : Option Nat := none
  for i in [0 : lowCs.size - sepCs.size + 1] do
    if cs[i]! == '"' then
      inQuote := !inQuote
    else if !inQuote then
      let mut ok := true
      for j in [0 : sepCs.size] do
        if lowCs[i + j]! != sepCs[j]! then
          ok := false
          break
      if ok then found? := some i
  match found? with
  | none => return none
  | some idx =>
    let lhs := (String.ofList (cs.extract 0 idx).toList).trimAscii.copy
    let rhs := (String.ofList (cs.extract (idx + sepCs.size) cs.size).toList).trimAscii.copy
    return some (lhs, rhs)

/-- Split a clause on top-level `, ` and ` and ` outside `"..."` quotes. -/
def splitTopLevelList (s : String) : Array String := Id.run do
  let cs := s.toList.toArray
  let lowCs := (pLower s).toList.toArray
  let mut parts : Array String := #[]
  let mut cur : Array Char := #[]
  let mut inQuote := false
  let mut i : Nat := 0
  let matchesAt (idx : Nat) (pat : String) : Bool := Id.run do
    let p := pat.toList.toArray
    if idx + p.size > lowCs.size then return false
    for j in [0 : p.size] do
      if lowCs[idx + j]! != p[j]! then return false
    return true
  while i < cs.size do
    let c := cs[i]!
    if c == '"' then
      inQuote := !inQuote
      cur := cur.push c
      i := i + 1
    else if !inQuote && matchesAt i ", and " then
      let piece := (String.ofList cur.toList).trimAscii.copy
      if !piece.isEmpty then parts := parts.push piece
      cur := #[]
      i := i + 6
    else if !inQuote && matchesAt i ", " then
      let piece := (String.ofList cur.toList).trimAscii.copy
      if !piece.isEmpty then parts := parts.push piece
      cur := #[]
      i := i + 2
    else if !inQuote && matchesAt i " and " then
      let piece := (String.ofList cur.toList).trimAscii.copy
      if !piece.isEmpty then parts := parts.push piece
      cur := #[]
      i := i + 5
    else
      cur := cur.push c
      i := i + 1
  let tail := (String.ofList cur.toList).trimAscii.copy
  if !tail.isEmpty then parts := parts.push tail
  return parts

/-- Parse a count phrase (`"a"`/`"an"`/`"one"`/`"two"`/`"3"`/`"X"`/`ValueExpr`). -/
def parseCountVal? (raw : String) : Option ValueExpr :=
  let s := pClean raw
  let l := pLower s
  if l == "a" || l == "an" then some (.const 1)
  else if l == "x" then some .chosenX
  else if l == "that many" || l == "that much" then some .eventAmount
  else
    match parseNatWord? s with
    | some n => some (.const (Int.ofNat n))
    | none => parseValueExpr s

/-- Parse a signed stat delta (`+P`, `−P`, `+X`, `−X`) into `ValueExpr`. -/
def parseSignedVal? (raw : String) : Option ValueExpr :=
  let s := raw.trimAscii.copy
  if s.isEmpty then none
  else if s == "+X" || s == "+x" || s == "X" || s == "x" then some .chosenX
  else if s == "-X" || s == "-x" || s == "−X" || s == "−x" then
    some (.binary .sub (.const 0) .chosenX)
  else if s.startsWith "+" then
    let rest := (s.drop 1).trimAscii.copy
    match parseNatWord? rest with
    | some n => some (.const (Int.ofNat n))
    | none => parseValueExpr rest
  else if s.startsWith "-" || s.startsWith "−" then
    let rest := (if s.startsWith "-" then s.drop 1 else s.drop 1).trimAscii.copy
    match parseNatWord? rest with
    | some n => some (.const (-(Int.ofNat n)))
    | none => (parseValueExpr rest).map fun v => .binary .sub (.const 0) v
  else
    match parseNatWord? s with
    | some n => some (.const (Int.ofNat n))
    | none => parseValueExpr s

/-- Parse `"+2/+1"`, `"−1/−1"`, `"+X/+0"`, `"+0/+8"` into `(powerVal, toughnessVal)`. -/
def parsePTDeltaExpr? (raw : String) : Option (ValueExpr × ValueExpr) :=
  let s := (pClean raw).replace "−" "-"
  match s.splitOn "/" with
  | [p, t] =>
    if (p.startsWith "+" || p.startsWith "-") && (t.startsWith "+" || t.startsWith "-") then
      match parseSignedVal? p, parseSignedVal? t with
      | some pv, some tv => some (pv, tv)
      | _, _ => none
    else none
  | _ => none

/-- Parse fixed `"+2/+1"` or `"−1/−1"` into `Int × Int`. -/
def parsePTDeltaInt? (raw : String) : Option (Int × Int) :=
  match parsePTDeltaExpr? raw with
  | some (.const p, .const t) => some (p, t)
  | _ => none

/-- Parse a comma/`and`-separated list of keywords (`"flying, trample, and haste"`). -/
def parseKeywordList? (raw : String) : Option (Array KeywordAbility) := Id.run do
  let parts := splitTopLevelList (pClean raw)
  if parts.isEmpty then return none
  let mut out : Array KeywordAbility := #[]
  for p in parts do
    match parseKeywordAbility p with
    | some k => out := out.push k
    | none => return none
  return some (out.qsort (fun a b => a.displayOrder < b.displayOrder))

/-- Parse a dynamic `ExprCountRange` (`"any number of"`, `"up to N"`, `"a/an"`, `"N"`, `"X"`). -/
def parseExprCountRange? (raw : String) : Option (ExprCountRange × String) :=
  let s := pClean raw
  if let some rest := pDropPrefixCI? s "any number of " then
    some (.anyNumber, rest)
  else if let some rest := pDropPrefixCI? s "up to " then
    let ws := pWords rest
    if ws.size >= 2 then
      match parseCountVal? ws[0]! with
      | some v =>
        some (.upTo v, String.intercalate " " (ws.extract 1 ws.size).toList)
      | none =>
        -- Check multi-word value like `"the number of ..."` or `"that many"`
        if let some rest2 := pDropPrefixCI? rest "that many " then
          some (.upTo .eventAmount, rest2)
        else if let some rest2 := pDropPrefixCI? rest "that much " then
          some (.upTo .eventAmount, rest2)
        else none
    else none
  else
    let ws := pWords s
    if ws.size >= 2 then
      match parseCountVal? ws[0]! with
      | some v =>
        some (.exact v, String.intercalate " " (ws.extract 1 ws.size).toList)
      | none => none
    else none

/-- Parse a counter phrase (`"a +1/+1 counter"`, `"two shield counters"`, `"X loyalty counters"`,
`"a number of +1/+1 counters equal to ..."`). -/
def parseCounterSpec? (raw : String) : Option (CounterKind × ValueExpr) := Id.run do
  let s := pClean raw
  -- `"<N> <kind> counter(s)"`
  let ws := (pWords s).toList.map pLower
  if let some (n, kind, consumed) := CounterKind.matchPhrase ws then
    if consumed == ws.length then
      return some (kind, .const (Int.ofNat n))
  -- `"X <kind> counter(s)"` or `"<ValueExpr> <kind> counter(s)"`
  let core? :=
    (pDropSuffixCI? s " counters").orElse (fun _ => pDropSuffixCI? s " counter")
  let some core := core? | return none
  -- Match trailing counter kind (1 or 2 words, e.g. `+1/+1`, `first strike`, `shield`)
  let cws := pWords core
  if cws.size < 2 then return none
  -- Try 2-word counter kind first (e.g. `first strike`, `double strike`)
  if cws.size >= 3 then
    if let some (kind, kLen) := CounterKind.ofPrefix [pLower cws[cws.size - 2]!, pLower cws[cws.size - 1]!] then
      if kLen == 2 then
        let cntStr := String.intercalate " " (cws.extract 0 (cws.size - 2)).toList
        if let some v := parseCountVal? cntStr then
          return some (kind, v)
  if let some (kind, kLen) := CounterKind.ofPrefix [pLower cws[cws.size - 1]!] then
    if kLen == 1 then
      let cntStr := String.intercalate " " (cws.extract 0 (cws.size - 1)).toList
      if let some v := parseCountVal? cntStr then
        return some (kind, v)
  return none

/-! ### `GrantedAbility` Parser -/

/-- Parse a single quoted or unquoted ability granted to a token or copy exception
into `GrantedAbility` using `qp`. -/
def parseGrantedAbility? (qp : QuotedAbilityParsers) (raw : String)
    (tokenName : String := "") : Option GrantedAbility := Id.run do
  let s := (pClean (raw.replace "\"" "")).trimAscii.copy
  if s.isEmpty then return none
  let low := pLower s
  -- Equip shortcut on tokens (`"equip {2}"` -> `GrantedAbility.equipGeneric 2` / activated)
  if let some eqRest := pDropPrefixCI? s "equip " then
    if let some mc := parseManaCost? eqRest then
      return some (.activated {
        cost := CostSpec.ofMana mc
        effect := { targets := .creatureYouControl, body := .permanent (.attach .this (.target 0)) }
        timing := .sorcery
        tag? := some (.equip none)
      })
  -- Common token static shortcuts (`Equipped creature gets +P/+T`, `can't block`, `attacks each combat`)
  if let some ptRest := pDropPrefixCI? s "equipped creature gets " then
    if let some (p, t) := parsePTDeltaInt? ptRest then
      return some (GrantedAbility.equippedCreatureGets p t)
  if low == "this token can't block" || low == "this tokens can't block" ||
      low == "this creature can't block" || low == "this permanent can't block" then
    return some GrantedAbility.cantBlock
  if low.endsWith " attacks each combat if able" then
    return some GrantedAbility.attacksEachCombatIfAble
  if let some maxRest := pDropPrefixCI? low "this token can't be blocked by more than " then
    let w := (pWords maxRest).getD 0 ""
    if let some n := parseNatWord? w then
      return some (GrantedAbility.cantBeBlockedByMoreThan n)
  if let some (_, maxRest) := pSplitFirstCI? low " can't be blocked by more than " then
    let w := (pWords maxRest).getD 0 ""
    if let some n := parseNatWord? w then
      return some (GrantedAbility.cantBeBlockedByMoreThan n)
  -- Check keyword (`toxic 1`, `flying`, etc.)
  if let some kw := parseKeywordAbility s then
    return some (.keyword kw)
  -- Strip optional ability word before classifying triggered/activated/static
  let (_, body) := extractLeadingLabel s
  let selfAlias := if tokenName.isEmpty then "this token" else tokenName
  let normBody :=
    let b1 :=
      if tokenName.isEmpty then body
      else replaceCardNameOutsideQuotes body tokenName "this permanent"
    b1.replace "this token" "this permanent" |>.replace "This token" "This permanent"
  -- Top-level `:` -> activated ability
  if hasTopLevelColon normBody then
    if let some ab := qp.parseActivated normBody selfAlias then
      return some (.activated ab)
  -- Starts with When / Whenever / At -> triggered ability
  let bLow := pLower normBody
  if bLow.startsWith "when " || bLow.startsWith "whenever " || bLow.startsWith "at " then
    if let some ab := qp.parseTriggered normBody selfAlias then
      return some (.triggered ab)
  -- Static ability fallback
  if let some sa := qp.parseStatic normBody selfAlias then
    return some (.static sa)
  return none

/-! ### `CopyModification` Parser (CR 707.9) -/

private def parseCardTypeWord? (w : String) : Option CardType :=
  match pLower w with
  | "artifact" | "artifacts" => some .artifact
  | "battle" | "battles" => some .battle
  | "creature" | "creatures" => some .creature
  | "enchantment" | "enchantments" => some .enchantment
  | "instant" | "instants" => some .instant
  | "kindred" => some .kindred
  | "land" | "lands" => some .land
  | "planeswalker" | "planeswalkers" => some .planeswalker
  | "sorcery" | "sorceries" => some .sorcery
  | _ => none

private def parseSupertypeWord? (w : String) : Option Supertype :=
  match pLower w with
  | "basic" => some .basic
  | "legendary" => some .legendary
  | "ongoing" => some .ongoing
  | "snow" => some .snow
  | "world" => some .world
  | _ => none

private def parsePTFixedSlash? (w : String) : Option (Int × Int) :=
  match w.splitOn "/" with
  | [p, t] =>
    match p.toInt?, t.toInt? with
    | some pv, some tv => some (pv, tv)
    | _, _ => none
  | _ => none

/-- Parse `"except <clause1>, <clause2>, and <clause3>"` into `Array CopyModification`. -/
def parseCopyModifications? (qp : QuotedAbilityParsers) (raw : String)
    (cardName : String := "") : Option (Array CopyModification) := Id.run do
  let cleaned := (pClean raw).trimAscii.copy
  let body := (pDropPrefixCI? cleaned "except ").getD cleaned
  if body.isEmpty then return some #[]
  -- Split carefully on top-level clause boundaries (`", and "`, `", "`, `" and it "`, `" and he's "`, `" and she's "`, `" and its "`, `" and his "`, `" and her "`)
  -- First preserve commas inside names like `"Taskmaster, Mercenary Mimic"` by splitting before pronoun-led clauses when possible.
  let rawClauses : Array String := Id.run do
    let cs := body.toList.toArray
    let lowCs := (pLower body).toList.toArray
    let seps := #[
      ", and it ", ", and it's ", ", and its ", ", and he ", ", and he's ", ", and his ",
      ", and she ", ", and she's ", ", and her ", ", and they ", ", and they're ",
      ", it ", ", it's ", ", its ", ", he ", ", he's ", ", his ", ", she ", ", she's ", ", her ",
      " and it ", " and it's ", " and its ", " and he ", " and he's ", " and his ",
      " and she ", " and she's ", " and her ", " and they ", " and they're "
    ]
    let matchesAt (idx : Nat) (pat : String) : Bool := Id.run do
      let p := pat.toList.toArray
      if idx + p.size > lowCs.size then return false
      for j in [0 : p.size] do
        if lowCs[idx + j]! != p[j]! then return false
      return true
    let mut out : Array String := #[]
    let mut cur : Array Char := #[]
    let mut inQuote := false
    let mut i : Nat := 0
    while i < cs.size do
      let c := cs[i]!
      if c == '"' then
        inQuote := !inQuote
        cur := cur.push c
        i := i + 1
      else if !inQuote then
        let mut matchedSep? : Option (Nat × Nat) := none
        for sep in seps do
          if matchesAt i sep then
            -- Advance past `", and "` (6) / `", "` (2) / `" and "` (5), keeping the pronoun
            let adv :=
              if sep.startsWith ", and " then 6
              else if sep.startsWith ", " then 2
              else 5
            matchedSep? := some (adv, sep.length)
            break
        match matchedSep? with
        | some (adv, _) =>
          let piece := (String.ofList cur.toList).trimAscii.copy
          if !piece.isEmpty then out := out.push piece
          cur := #[]
          i := i + adv
        | none =>
          cur := cur.push c
          i := i + 1
      else
        cur := cur.push c
        i := i + 1
    let tail := (String.ofList cur.toList).trimAscii.copy
    if !tail.isEmpty then out := out.push tail
    return out
  let mut mods : Array CopyModification := #[]
  for clause0 in rawClauses do
    let clause := pClean clause0
    let low := pLower clause
    -- `"it isn't legendary"` / `"it's not legendary"` / `"the tokens aren't legendary"` / `"they aren't legendary"`
    if let some supStr := (pDropPrefixCI? clause "it isn't ").orElse
        (fun _ => (pDropPrefixCI? clause "it is not ").orElse
          (fun _ => (pDropPrefixCI? clause "it's not ").orElse
            (fun _ => (pDropPrefixCI? clause "the tokens aren't ").orElse
              (fun _ => (pDropPrefixCI? clause "the token isn't ").orElse
                (fun _ => (pDropPrefixCI? clause "they aren't ").orElse
                  (fun _ => pDropPrefixCI? clause "they're not ")))))) then
      if let some sup := parseSupertypeWord? supStr then
        mods := mods.push (.removeSupertype sup)
        continue
      return none
    -- `"its/his/her name is <Name>"`
    if let some nameStr := (pDropPrefixCI? clause "its name is ").orElse
        (fun _ => (pDropPrefixCI? clause "his name is ").orElse
          (fun _ => (pDropPrefixCI? clause "her name is ").orElse
            (fun _ => pDropPrefixCI? clause "it's named "))) then
      let rawN := nameStr.trimAscii.copy
      let fixedName :=
        if !cardName.isEmpty && (pLower rawN).startsWith "this permanent" then cardName
        else rawN
      mods := mods.push (.setName fixedName)
      continue
    -- `"its creature types are <Subtypes>"`
    if let some subStr := pDropPrefixCI? clause "its creature types are " then
      let mut subs : Array CardSubtype := #[]
      for w in pWords subStr do
        let some sub := CardSubtype.ofOracle? w | return none
        subs := subs.push sub
      if subs.isEmpty then return none
      mods := mods.push (.replaceCreatureSubtypes subs)
      continue
    -- `"it has <keywords and/or quoted abilities>"` / `"he has ..."` / `"she has ..."`
    if let some hasStr := (pDropPrefixCI? clause "it has ").orElse
        (fun _ => (pDropPrefixCI? clause "he has ").orElse
          (fun _ => (pDropPrefixCI? clause "she has ").orElse
            (fun _ => pDropPrefixCI? clause "they have "))) then
      let items := splitTopLevelList hasStr
      if items.isEmpty then return none
      let mut kws : Array KeywordAbility := #[]
      let mut abs : Array GrantedAbility := #[]
      for it in items do
        let itClean := it.trimAscii.copy
        if itClean.startsWith "\"" then
          let some ga := parseGrantedAbility? qp itClean cardName | return none
          abs := abs.push ga
        else if let some kw := parseKeywordAbility itClean then
          kws := kws.push kw
        else
          let some ga := parseGrantedAbility? qp itClean cardName | return none
          abs := abs.push ga
      if !kws.isEmpty then mods := mods.push (.addKeywords kws)
      if !abs.isEmpty then mods := mods.push (.addAbilities abs)
      continue
    -- `"it's / he's / she's ... [in addition to its/his/her other types/colors]"`
    if let some isRest := (pDropPrefixCI? clause "it's ").orElse
        (fun _ => (pDropPrefixCI? clause "he's ").orElse
          (fun _ => (pDropPrefixCI? clause "she's ").orElse
            (fun _ => pDropPrefixCI? clause "it is "))) then
      let (inAddTypes, core1) :=
        match (pDropSuffixCI? isRest " in addition to its other types").orElse
            (fun _ => (pDropSuffixCI? isRest " in addition to his other types").orElse
              (fun _ => pDropSuffixCI? isRest " in addition to her other types")) with
        | some c => (true, c)
        | none => (false, isRest)
      let (inAddColors, core2) :=
        match (pDropSuffixCI? core1 " in addition to its other colors").orElse
            (fun _ => pDropSuffixCI? core1 " in addition to his other colors") with
        | some c => (true, c)
        | none => (false, core1)
      let core3 :=
        (pDropPrefixCI? core2 "an ").orElse (fun _ => pDropPrefixCI? core2 "a ")
          |>.getD core2
      let ws := pWords core3
      if ws.isEmpty then return none
      let mut sups : Array Supertype := #[]
      let mut tys : Array CardType := #[]
      let mut subs : Array CardSubtype := #[]
      let mut cols := ColorSet.empty
      let mut pt? : Option (Int × Int) := none
      for w in ws do
        let wl := pLower w
        if wl == "and" then
          pure ()
        else if let some pt := parsePTFixedSlash? w then
          pt? := some pt
        else if let some sup := parseSupertypeWord? w then
          sups := sups.push sup
        else if let some ty := parseCardTypeWord? w then
          tys := tys.push ty
        else if let some col := parseColorWord? w then
          cols := cols.insert col
        else if let some sub := CardSubtype.ofOracle? w then
          subs := subs.push sub
        else
          return none
      if !sups.isEmpty then mods := mods.push (.addSupertypes sups)
      if let some (p, t) := pt? then mods := mods.push (.setBasePT p t)
      if !cols.isColorless then mods := mods.push (.addColors cols)
      if !tys.isEmpty then mods := mods.push (.addTypes tys)
      if !subs.isEmpty then
        if inAddTypes then mods := mods.push (.addSubtypes subs)
        else mods := mods.push (.replaceCreatureSubtypes subs)
      if inAddColors && cols.isColorless then return none
      continue
    if low.isEmpty then continue
    return none
  return some mods

/-! ### `TokenSpec` + `EnterMods` Parser (CR 111 / 707.9) -/

/-- Parse a predefined token word (`Treasure`, `Food`, `Clue`, `Incubator`, `Map`,
`Junk`, `Lander`, `Mutagen`, `Vibranium`, `Heartwood`). -/
def parsePredefinedTokenWord? (raw : String) : Option PredefinedToken :=
  match pLower (pClean raw) with
  | "treasure" => some .treasure
  | "food" => some .food
  | "clue" => some .clue
  | "incubator" => some .incubator
  | "map" => some .map
  | "junk" => some .junk
  | "lander" => some .lander
  | "mutagen" => some .mutagen
  | "vibranium" => some .vibranium
  | "heartwood" => some .heartwood
  | _ => none

/-- Parse card-name-shorthand tokens (`Lotus`, `Gingerbrute`) whose full rules live in
`TokenSpec` definitions (CR 111.11 / card-named predefined tokens). -/
private def parseCardShorthandToken? (raw : String) : Option TokenSpec :=
  match pLower (pClean raw) with
  | "lotus" => some .lotus
  | "gingerbrute" => some .gingerbrute
  | _ => none

/-- Split a custom token tail `"with <kws/abilities> [named <Name>] [with <abilities>]"`
into `(keywords, abilities, name?)`. -/
private def parseTokenTailWithNamed (qp : QuotedAbilityParsers) (tail : String)
    (existingName? : Option String) : Option (Array KeywordAbility × Array GrantedAbility × Option String) := Id.run do
  let mut kws : Array KeywordAbility := #[]
  let mut abs : Array GrantedAbility := #[]
  let mut name? : Option String := existingName?
  let mut cur := tail.trimAscii.copy
  -- Extract `"named <Name>"` if present outside quotes (before or after `"with "`)
  if let some (beforeN, afterN) := pSplitFirstCI? cur "named " then
    -- Check if `" with "` follows the name
    let (nm, afterWith) :=
      match pSplitFirstCI? afterN " with " with
      | some (n, w) => (n.trimAscii.copy, "with " ++ w.trimAscii.copy)
      | none => (afterN.trimAscii.copy, "")
    if !nm.isEmpty then name? := some (pClean nm)
    cur := (beforeN.trimAscii.copy ++ " " ++ afterWith).trimAscii.copy
  -- Peel one or more `"with ..."` segments
  while !cur.isEmpty do
    let some rest := pDropPrefixCI? cur "with " | return none
    let (seg, nextCur) :=
      match pSplitFirstCI? rest " with " with
      | some (a, b) => (a.trimAscii.copy, "with " ++ b.trimAscii.copy)
      | none => (rest.trimAscii.copy, "")
    let items := splitTopLevelList seg
    if items.isEmpty then return none
    let tokNm := name?.getD ""
    for it in items do
      let itTrim := it.trimAscii.copy
      if itTrim.startsWith "\"" then
        let some ga := parseGrantedAbility? qp itTrim tokNm | return none
        abs := abs.push ga
      else if (pLower itTrim).startsWith "equip " then
        let some ga := parseGrantedAbility? qp itTrim tokNm | return none
        abs := abs.push ga
      else if (pLower itTrim).startsWith "toxic " then
        -- `TokenSpec.mite` stores `toxic` as `GrantedAbility.keyword (.toxic n)`
        let some kw := parseKeywordAbility itTrim | return none
        abs := abs.push (.keyword kw)
      else if let some kw := parseKeywordAbility itTrim then
        kws := kws.push kw
      else
        let some ga := parseGrantedAbility? qp itTrim tokNm | return none
        abs := abs.push ga
    cur := nextCur
  return some (kws, abs, name?)

/-- Parse a complete token description phrase (after the leading count word, or
starting with a legendary token name like `"Redwing, a legendary ..."`), returning
`(TokenSpec × EnterMods)`.
Handles:
- Predefined tokens (`"Treasure token"`, `"tapped Food tokens"`, `"Clue token"`)
- Card-name-shorthand tokens (`"Lotus token"`, `"Gingerbrute token"`)
- Copy tokens (`"token that's a copy of <ref>[, except ...]"`)
- Named-first custom tokens (`"<Name>, a [legendary] P/T ... token [with ...]"`)
- Standard custom tokens (`"[tapped] [and attacking] [legendary] [P/T] [<colors>] [<subtypes>] [<types>] token(s) [named ...] [with ...]"`)
- Inline `EnterMods` (`tapped`, `attacking`, `goaded`, `with a <counter> counter on it`). -/
def parseTokenDesc? (qp : QuotedAbilityParsers) (ctx : DiscourseCtx)
    (raw : String) (parseRefObj : DiscourseCtx → String → Option (ObjectExpr × DiscourseCtx)) :
    Option (TokenSpec × EnterMods × DiscourseCtx) := Id.run do
  let s := pClean raw
  if s.isEmpty then return none
  let mut mods : EnterMods := {}
  let mut body := s

  -- Peel trailing `"with <kws> until end of turn"` (e.g. `with haste until end of turn`, `with haste and lifelink until end of turn`)
  if let some beforeEot := pDropSuffixCI? body " until end of turn" then
    if let some (headB, kwPart) := pSplitLastCI? beforeEot " with " then
      if let some kws := parseKeywordList? kwPart then
        mods := { mods with grantKeywordsUntilEot := mods.grantKeywordsUntilEot ++ kws }
        body := headB

  -- Peel trailing `"with <count> <counter> counter(s) on it/them"` (e.g. Incubator tokens)
  if let some (beforeW, afterW) := pSplitLastCI? body " with " then
    let ctrClean? :=
      (pDropSuffixCI? afterW " on it").orElse fun _ => pDropSuffixCI? afterW " on them"
    if let some ctrClean := ctrClean? then
      let ctrParsed? : Option (CounterKind × ValueExpr) :=
        (parseCounterSpec? ctrClean).orElse fun _ => Id.run do
          let cNoWord := ((pDropSuffixCI? ctrClean " counters").orElse fun _ => pDropSuffixCI? ctrClean " counter") |>.getD ""
          if cNoWord.isEmpty then return none
          let cws := pWords cNoWord
          if cws.size < 2 then return none
          let kWord := cws[cws.size - 1]!
          let cntPart := String.intercalate " " (cws.extract 0 (cws.size - 1)).toList
          let k? := (CounterKind.ofPrefix [pLower kWord]).map Prod.fst
          let v? := (ctx.resolveStepMetric? cntPart).orElse fun _ =>
            (parseCountVal? cntPart).orElse fun _ => parseValueExpr cntPart
          match k?, v? with
          | some k, some v => return some (k, v)
          | _, _ => return none
      if let some (k, v) := ctrParsed? then
        mods := { mods with counters := mods.counters.push (k, v) }
        body := beforeW

  -- Peel trailing `"that's tapped and attacking"` / `"tapped and attacking"` / `"goaded"` / `"attacking"`
  if let some b := (pDropSuffixCI? body " that's tapped and attacking").orElse
      (fun _ => (pDropSuffixCI? body " tapped and attacking").orElse
        (fun _ => pDropSuffixCI? body " that are tapped and attacking")) then
    mods := { mods with tapped := true, attacking := true }
    body := b
  else if let some b := (pDropSuffixCI? body " tapped").orElse
      (fun _ => pDropSuffixCI? body " that's tapped") then
    mods := { mods with tapped := true }
    body := b
  else if let some b := (pDropSuffixCI? body " attacking").orElse
      (fun _ => pDropSuffixCI? body " that's attacking") then
    mods := { mods with attacking := true }
    body := b

  -- Peel leading `"tapped and attacking "` / `"tapped "`
  if let some b := pDropPrefixCI? body "tapped and attacking " then
    mods := { mods with tapped := true, attacking := true }
    body := b
  else if let some b := pDropPrefixCI? body "tapped " then
    mods := { mods with tapped := true }
    body := b

  -- Check copy token: `"token(s) that's/that are a copy/copies of <ref>[, except ...]"`
  let copyRest? :=
    (pDropPrefixCI? body "token that's a copy of ").orElse fun _ =>
    (pDropPrefixCI? body "tokens that's a copy of ").orElse fun _ =>
    (pDropPrefixCI? body "tokens that are copies of ").orElse fun _ =>
    (pDropPrefixCI? body "token that is a copy of ")
  if let some rest := copyRest? then
    let (refStr, excStr?) :=
      match pSplitFirstCI? rest ", except " with
      | some (a, b) => (a, some b)
      | none => (rest, none)
    let some (refObj, ctx') := parseRefObj ctx refStr | return none
    let some copyMods :=
      (match excStr? with
      | none => some #[]
      | some ex => parseCopyModifications? qp ex ctx.cardName)
      | return none
    return some (.copyOf refObj copyMods, mods, ctx')
  -- Bare `"token that's a copy"` (when target/loop referent is already in `ctx`)
  if pLower body == "token that's a copy" || pLower body == "tokens that are copies" then
    let refObj := ctx.lastSubject?.getD (if ctx.isTrigger then .triggerSubject else .this)
    return some (.copyOf refObj #[], mods, ctx)

  -- Check named-first format: `"<Name>, a(n) [legendary] ... token [with ...]"`
  let mut leadingName? : Option String := none
  if let some (nm, rest) := pSplitFirstCI? body ", a " then
    if !nm.contains '"' && (pLower rest).contains " token" then
      leadingName? := some nm.trimAscii.copy
      body := rest
  else if let some (nm, rest) := pSplitFirstCI? body ", an " then
    if !nm.contains '"' && (pLower rest).contains " token" then
      leadingName? := some nm.trimAscii.copy
      body := rest

  -- Split around `" token"` / `" tokens"` outside quotes
  let some (headPart0, tailPart) :=
    (match pSplitFirstCI? body " tokens" with
    | some (h, t) => some (h.trimAscii.copy, t.trimAscii.copy)
    | none =>
      match pSplitFirstCI? body " token" with
      | some (h, t) => some (h.trimAscii.copy, t.trimAscii.copy)
      | none => none)
    | return none

  -- Predefined token (`Treasure`, `Food`, `Clue`, `Incubator`, etc.) when no trailing `"with"` / `"named"`
  if leadingName?.isNone && tailPart.isEmpty then
    if let some pre := parsePredefinedTokenWord? headPart0 then
      return some (.predefined pre, mods, ctx)
    if let some sh := parseCardShorthandToken? headPart0 then
      return some (sh, mods, ctx)
    if pLower headPart0 == "blue jace planeswalker" then
      return some (.jace, mods, ctx)

  -- Parse custom token head: `[supertypes] [P/T or <ValueExpr>/<ValueExpr>] [colors / colorless] [subtypes] [types]`
  let mut power? : Option ValueExpr := none
  let mut toughness? : Option ValueExpr := none
  let mut headPart := headPart0
  let mut sups : Array Supertype := #[]
  if let some restLeg := pDropPrefixCI? headPart "legendary " then
    sups := sups.push .legendary
    headPart := restLeg
  -- Handle multi-word dynamic P/T like `"that object's mana value/that object's mana value blue Shark creature"`
  if headPart.contains '/' then
    match headPart.splitOn "/" with
    | [lhsPT, rhsAll] =>
      let lhsWords := pWords lhsPT
      if lhsWords.size > 1 then
        let lhsVal? : Option ValueExpr :=
          if pLower lhsPT == "that object's mana value" || pLower lhsPT == "that spell's mana value" then
            some (.objectStat .manaValue .triggerSubject)
          else if pLower lhsPT == "that amount" then
            some .eventAmount
          else parseValueExpr lhsPT
        if let some pv := lhsVal? then
          -- Match same expression prefix on RHS (or parse leading value expr words)
          if let some restAfterT := pDropPrefixCI? rhsAll (lhsPT ++ " ") then
            power? := some pv
            toughness? := some pv
            headPart := restAfterT
    | _ => pure ()

  let ws := pWords headPart
  if ws.isEmpty then return none
  let mut colors := ColorSet.empty
  let mut subtypes : Array CardSubtype := #[]
  let mut types : Array CardType := #[]
  for w in ws do
    let wl := pLower w
    if wl == "and" || wl == "colorless" then
      pure ()
    else if w.contains '/' then
      let parts := w.splitOn "/"
      if parts.length != 2 then return none
      let some pv := parseCountVal? parts[0]! | return none
      let some tv := parseCountVal? parts[1]! | return none
      power? := some pv
      toughness? := some tv
    else if let some sup := parseSupertypeWord? w then
      sups := sups.push sup
    else if let some col := parseColorWord? w then
      colors := colors.insert col
    else if let some ty := parseCardTypeWord? w then
      types := types.push ty
    else if let some sub := CardSubtype.ofOracle? w then
      subtypes := subtypes.push sub
    else
      return none
  if types.isEmpty then return none

  -- Parse trailing `"named ..."` / `"with ..."`
  let some (kws, abs, finalName?) := parseTokenTailWithNamed qp tailPart leadingName?
    | return none
  return some (.custom {
    name? := finalName?
    supertypes := sups
    types
    subtypes
    colors
    power?
    toughness?
    keywords := kws
    abilities := abs
  }, mods, ctx)

/-! ### `EmblemSpec` Parser (CR 114) -/

/-- Parse `"an emblem with \"<ab1>\" [and \"<ab2>\"]"` into `EmblemSpec`, recursively
parsing each quoted ability via `qp`. -/
def parseEmblemSpec? (qp : QuotedAbilityParsers) (raw : String) : Option EmblemSpec := Id.run do
  let s := pClean raw
  let body :=
    (pDropPrefixCI? s "an emblem with ").orElse (fun _ => pDropPrefixCI? s "emblem with ")
  let some rest := body | return none
  let spans := extractQuotedSpans rest
  if spans.isEmpty then return none
  let mut statics : Array StaticAbility := #[]
  let mut triggers : Array TriggeredAbility := #[]
  let mut activated : Array ActivatedAbility := #[]
  for sp in spans do
    let spNorm := sp.replace "this emblem" "this permanent" |>.replace "This emblem" "This permanent"
    if hasTopLevelColon spNorm then
      let some ab := qp.parseActivated spNorm "this emblem" | return none
      activated := activated.push ab
    else
      let low := pLower spNorm
      if low.startsWith "when " || low.startsWith "whenever " || low.startsWith "at " then
        let some ab := qp.parseTriggered spNorm "this emblem" | return none
        triggers := triggers.push ab
      else
        let some sa := qp.parseStatic spNorm "this emblem" | return none
        statics := statics.push sa
  return some {
    staticAbilities := statics
    triggeredAbilities := triggers
    activatedAbilities := activated
  }

end Mtg.Engine.Parser
