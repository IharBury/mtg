import Mtg.Engine.Card.OracleNorm

/-!
# Stage-2 Compositional Oracle Lexer & Quote-Aware Normalizer (CR 207.2a, 207.2c, 207.4)

Linear `Array Char` lexer for printed Oracle paragraphs:
- Strips balanced reminder text `(...)` (CR 207.2a) and leading `{CHAOS}` headers
  (CR 207.4) while preserving in-text `{CHAOS}` symbols.
- Recognizes mechanic-carrying em-dash labels (`Power-up —`, `Exhaust —`,
  `Boast —`, `Eminence —`, `Corrupted —`, `Threshold —`, `Teamwork —`,
  `Jeskai —`, `Mardu —`) as `MechanicLabel` / `OrbTok.label` tokens before
  discarding pure CR 207.2c ability words and CR 207.2d flavor words.
- Lexes `"..."` substrings into `OrbTok.quoted (Array OrbTok) String` *before*
  splitting on `:` or `.`, so granted abilities (`have "{T}: Add ..."`,
  `Planeswalkers you control have "[-2]: ..."`, token abilities, and emblems)
  are recursively parsed by Stages 3–5.
- Aliases card self-references (`<FullCardName>`, `<LegendShortName>`,
  `"this <type>"`) to `OrbTok.selfRef` outside quoted sub-abilities.
-/

namespace Mtg.Engine.Parser

open Mtg.Engine.OracleNorm

/-- Mechanic-carrying em-dash prefix recognized by Stage 2 (distinct from
purely flavor CR 207.2c ability words). -/
inductive MechanicLabel where
  | powerUp
  | exhaust
  | boast
  | eminence
  | corrupted
  | threshold
  | teamwork
  | infinity
  | anchor (name : String)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Stage-2 lexical token for an Oracle rules paragraph. -/
inductive OrbTok where
  | word (raw : String)
  | symbol (sym : String)
  | label (name : String)
  | quoted (inner : Array OrbTok) (raw : String)
  | selfRef (possessive : Bool)
  | colon
  | comma
  | period
  | semicolon
  | emDash
  | bullet
deriving Repr, Inhabited, BEq

/-- Normalize curly quotes, typographic apostrophes, and Unicode minus signs in a single linear pass. -/
def normalizeTypography (s : String) : String :=
  s.map fun c =>
    if c == '\u2019' || c == '\u2018' then '\''
    else if c == '\u201C' || c == '\u201D' then '"'
    else if c == '\u2212' then '-'
    else c

/-- Normalize gendered self-pronouns on named legendary creatures/planeswalkers
(`he`/`she`/`him` → `it`, `he's`/`she's` → `it's`, `his` → `its`, `her` → `its`
before possessed nouns or `it` otherwise) while preserving player phrases
(`"he or she"`, `"him or her"`, `"his or her"`). -/
def normalizeGenderedSelfPronouns (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let isW (c : Char) : Bool := c.isAlphanum || c == '\'' || c == '-'
  let nextWordAt (pos : Nat) : String := Id.run do
    let mut j := pos
    while j < cs.size && cs[j]! == ' ' do j := j + 1
    let st := j
    while j < cs.size && isW cs[j]! do j := j + 1
    return lowerAscii (String.ofList (cs.extract st j).toList)
  let possessiveAfterHer : Array String := #[
    "power", "toughness", "mana", "owner", "owner's", "controller", "controller's",
    "other", "name", "base", "color", "colors", "type", "types", "subtype", "subtypes",
    "abilities", "ability", "loyalty", "life", "hand", "library", "graveyard"
  ]
  let mut out : String := ""
  let mut i : Nat := 0
  while i < cs.size do
    if isW cs[i]! && (i == 0 || !isW cs[i - 1]!) then
      let start := i
      while i < cs.size && isW cs[i]! do i := i + 1
      let w := String.ofList (cs.extract start i).toList
      let lw := lowerAscii w
      let cap := w.front?.map Char.isUpper |>.getD false
      let preserveOrPhrase :=
        (lw == "he" || lw == "him" || lw == "his") &&
          nextWordAt i == "or"
      let rep? : Option String :=
        if preserveOrPhrase then none
        else if lw == "he's" || lw == "she's" then
          some (if cap then "It's" else "it's")
        else if lw == "his" then
          some (if cap then "Its" else "its")
        else if lw == "he" || lw == "she" || lw == "him" then
          some (if cap then "It" else "it")
        else if lw == "her" then
          let nw := nextWordAt i
          if possessiveAfterHer.contains nw then
            some (if cap then "Its" else "its")
          else
            some (if cap then "It" else "it")
        else none
      out := out ++ rep?.getD w
    else
      out := out.push cs[i]!
      i := i + 1
  return out

/-- Drop CR 207.2a parenthetical reminder text `(...)` (whose first non-space char is
uppercase, `{`, or empty) while preserving lowercase semantic annotations emitted by
`ToOracle` (e.g. `not (you do)`, `(chosen)`, `(move the rest)`, `(reveal first)`, `(s)`). -/
def dropReminderTextKeepSemantic (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out : Array Char := #[]
  let mut i : Nat := 0
  while i < cs.size do
    if cs[i]! == '(' then
      -- Find matching ')' and inspect first non-space char inside
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
  (collapseWs (String.ofList out.toList)).trimAscii.copy

/-- Preprocess a raw Oracle line: normalize quotes and minus signs, drop CR 207.2a
reminder text `(...)`, strip CR 207.4 leading `{CHAOS}` symbols, and normalize
gendered self-pronouns. -/
def preprocessOracleLine (line : String) : String :=
  let s := normalizeTypography line
  let s := dropReminderTextKeepSemantic s
  let s := stripChaosSymbol s
  normalizeGenderedSelfPronouns s

/-- Classify a leading em-dash label into a mechanic-carrying `MechanicLabel`
when it carries rules meaning; returns `none` for purely flavor CR 207.2c/d
words (`Landfall`, `Alliance`, `Ferocious`, `Street Justice`, etc.). -/
def classifyMechanicLabel? (raw : String) : Option MechanicLabel :=
  match lowerAscii raw.trimAscii.copy with
  | "power-up" => some .powerUp
  | "exhaust" => some .exhaust
  | "boast" => some .boast
  | "eminence" => some .eminence
  | "corrupted" => some .corrupted
  | "threshold" => some .threshold
  | "teamwork" => some .teamwork
  | "∞" => some .infinity
  | "jeskai" => some (.anchor "Jeskai")
  | "mardu" => some (.anchor "Mardu")
  | _ => none

/-- True when `head` before `—` is a keyword em-dash introduction rather than an
ability/flavor word (`Ward—`, `Flashback—`, `Equip—`, `Cycling—`, `Kicker—`,
`Morph—`, `Sneak—`, `Impending N—`), or a Saga Roman chapter (`I, II —`). -/
private def isRulesEmDashPrefix (head : String) : Bool :=
  let h := head.trimAscii.copy
  let low := lowerAscii h
  let isRoman :=
    let bits := h.splitOn "," |>.map (·.trimAscii.copy) |>.filter (· != "")
    !bits.isEmpty && bits.all (fun b => b.all (fun c => c == 'I' || c == 'V' || c == 'X'))
  let isModalHeader :=
    low.startsWith "choose " || low.contains "choose one" || low.contains "choose two" ||
    low.contains "choose up to" || low.contains "choose both"
  let isKeywordDash :=
    low == "ward" || low == "flashback" || low == "equip" || low == "cycling" ||
    low == "kicker" || low == "morph" || low == "sneak" ||
    low.startsWith "equip " || low.endsWith "cycling" || low.startsWith "impending "
  isRoman || isModalHeader || isKeywordDash

/-- Extract an optional leading `MechanicLabel` and strip any leading CR 207.2c
ability word or CR 207.2d flavor word (preserving keyword/modal/chapter em-dashes).
Strips inner CR 207.2c ability words inside quoted abilities as well. -/
def extractLeadingLabel (s : String) : Option MechanicLabel × String := Id.run do
  let s := (stripChaosSymbol (normalizeTypography s)).trimAscii.copy
  -- Check top-level leading `label — rest` before any quote or colon
  let cs := s.toList.toArray
  let mut dashIdx? : Option Nat := none
  let mut inQuote := false
  for i in [0 : cs.size] do
    let c := cs[i]!
    if c == '"' then
      inQuote := !inQuote
    else if !inQuote then
      if c == ':' || c == '.' || c == '•' then
        break
      if c == '—' then
        dashIdx? := some i
        break
  match dashIdx? with
  | none => return (none, stripAbilityWords s)
  | some idx =>
    let head := (String.ofList (cs.extract 0 idx).toList).trimAscii.copy
    let rest := (String.ofList (cs.extract (idx + 1) cs.size).toList).trimAscii.copy
    if head.isEmpty || rest.isEmpty || isRulesEmDashPrefix head then
      return (none, stripAbilityWords s)
    if let some lbl := classifyMechanicLabel? head then
      return (some lbl, stripAbilityWords rest)
    -- Pure CR 207.2c ability word or CR 207.2d flavor word (single-word or multi-word before em-dash)
    let stripped := stripAbilityWord s
    if stripped != s then
      return (none, stripAbilityWords stripped)
    let headWords := head.splitOn " " |>.filter (!·.isEmpty)
    if headWords.length <= 5 && !head.contains ',' && !head.contains '{' &&
        (head.front?.map Char.isUpper |>.getD false) then
      return (none, stripAbilityWords rest)
    return (none, stripAbilityWords s)

/-- Split `s` on the first top-level `:` that sits outside `"..."` quotes.
Returns `none` when no unquoted colon exists (for example, static abilities
granting `"{T}: Add one mana of any color."`). -/
def splitTopLevelColon (s : String) : Option (String × String) := Id.run do
  let cs := s.toList.toArray
  let mut inQuote := false
  for i in [0 : cs.size] do
    let c := cs[i]!
    if c == '"' then
      inQuote := !inQuote
    else if c == ':' && !inQuote then
      let lhs := (String.ofList (cs.extract 0 i).toList).trimAscii.copy
      let rhs := (String.ofList (cs.extract (i + 1) cs.size).toList).trimAscii.copy
      return some (lhs, rhs)
  return none

/-- True when `s` contains an unquoted `:` at top level. -/
def hasTopLevelColon (s : String) : Bool :=
  (splitTopLevelColon s).isSome

/-- Split `s` into top-level sentences on `.` boundaries that sit outside `"..."`
quotes, keeping quoted multi-sentence abilities intact inside their enclosing
sentence. Handles both `"Foo. Bar."` and `"Gains \"A. B.\" Bar."`. -/
def splitTopLevelSentences (s : String) : Array String := Id.run do
  let cs := s.toList.toArray
  let mut out : Array String := #[]
  let mut cur : Array Char := #[]
  let mut inQuote := false
  let mut i : Nat := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '"' then
      -- Check if closing a quote that ended with `.` followed by whitespace + uppercase/end
      if inQuote then
        inQuote := false
        cur := cur.push c
        let prevDot := cur.size >= 2 && cur[cur.size - 2]! == '.'
        let nextSpace := i + 1 < cs.size && (cs[i + 1]! == ' ' || cs[i + 1]! == '\n')
        if prevDot && nextSpace then
          -- Peek past spaces: if next char starts a new sentence (not lowercase continuation like `"until end of turn"` or `"and"`)
          let mut j := i + 1
          while j < cs.size && (cs[j]! == ' ' || cs[j]! == '\n') do
            j := j + 1
          if j < cs.size && cs[j]!.isUpper then
            let piece := (String.ofList cur.toList).trimAscii.copy
            if !piece.isEmpty then out := out.push piece
            cur := #[]
            i := j
            continue
        i := i + 1
      else
        inQuote := true
        cur := cur.push c
        i := i + 1
    else if !inQuote && c == '.' then
      let nextIsSpaceOrEnd :=
        i + 1 >= cs.size || cs[i + 1]! == ' ' || cs[i + 1]! == '\n'
      -- Keep honorifics (`Ms.`, `Mr.`, `Dr.`) and acronyms followed by lowercase continuations (`M.O.D.O.K. connives`) intact.
      let curStr := String.ofList cur.toList
      let isHonorific :=
        curStr == "Ms" || curStr == "Mr" || curStr == "Dr" ||
        curStr.endsWith " Ms" || curStr.endsWith " Mr" || curStr.endsWith " Dr"
      let isAcronymMidSentence :=
        if cur.size >= 2 && cur[cur.size - 1]!.isUpper && cur[cur.size - 2]! == '.' then
          let j := Id.run do
            let mut k := i + 1
            while k < cs.size && (cs[k]! == ' ' || cs[k]! == '\n') do k := k + 1
            return k
          j < cs.size && cs[j]!.isLower
        else false
      if nextIsSpaceOrEnd && !isHonorific && !isAcronymMidSentence then
        let piece := curStr.trimAscii.copy
        if !piece.isEmpty then out := out.push piece
        cur := #[]
        i := i + 1
        while i < cs.size && (cs[i]! == ' ' || cs[i]! == '\n') do
          i := i + 1
      else
        cur := cur.push c
        i := i + 1
    else
      cur := cur.push c
      i := i + 1
  let tail := (String.ofList cur.toList).trimAscii.copy
  if !tail.isEmpty then out := out.push tail
  return out

/-- Extract every top-level `"..."` span from `s` in left-to-right order. -/
def extractQuotedSpans (s : String) : Array String := Id.run do
  let cs := s.toList.toArray
  let mut out : Array String := #[]
  let mut inQuote := false
  let mut cur : Array Char := #[]
  for i in [0 : cs.size] do
    let c := cs[i]!
    if c == '"' then
      if inQuote then
        out := out.push (String.ofList cur.toList).trimAscii.copy
        cur := #[]
        inQuote := false
      else
        inQuote := true
    else if inQuote then
      cur := cur.push c
  return out

/-- Split `s` at the first top-level `"..."` span into `(beforeQuote, quotedInner, afterQuote)`. -/
def splitFirstQuoted (s : String) : Option (String × String × String) := Id.run do
  let cs := s.toList.toArray
  let mut startIdx? : Option Nat := none
  for i in [0 : cs.size] do
    if cs[i]! == '"' then
      match startIdx? with
      | none => startIdx? := some i
      | some st =>
        let before := (String.ofList (cs.extract 0 st).toList).trimAscii.copy
        let inner := (String.ofList (cs.extract (st + 1) i).toList).trimAscii.copy
        let after := (String.ofList (cs.extract (i + 1) cs.size).toList).trimAscii.copy
        return some (before, inner, after)
  return none

/-- CR 201.5c shortened card-name aliases: always includes full `cardName`, and
only includes a shortened prefix before `", "` (e.g. `"Gandalf, Friend of the Shire"`
→ `"Gandalf"`), `" of "` (e.g. `"Bolg of the North"` → `"Bolg"`), or `" the "`
(e.g. `"Smaug the Magnificent"` → `"Smaug"`). Never splits plain multi-word titles
like `"Treasure Vault"`, `"Shark Typhoon"`, `"Hero in Training"`, or `"Robot Domination"`. -/
private def safeShortAlias? (cardName : String) : Option String :=
  let cn := cardName.trimAscii.copy
  if cn.isEmpty then none
  else
    let short? :=
      match cn.splitOn ", " with
      | a :: _ :: _ => some a.trimAscii.copy
      | _ =>
        match cn.splitOn " of " with
        | a :: _ :: _ => some a.trimAscii.copy
        | _ =>
          match cn.splitOn " the " with
          | a :: _ :: _ => some a.trimAscii.copy
          | _ =>
            match cn.splitOn " " with
            | [a, _] =>
              let al := lowerAscii a
              if a.length >= 3 && (a.front?.map Char.isUpper |>.getD false) &&
                  al != "enchanted" && al != "equipped" && al != "the" && al != "a" && al != "an" then
                some a.trimAscii.copy
              else none
            | _ => none
    match short? with
    | none => none
    | some s =>
      let sl := lowerAscii s
      if s.isEmpty || s == cn || sl == "the" || sl == "a" || sl == "an" || sl == "this" ||
          sl == "way" || sl == "eye" || sl == "call" || sl == "dawn" || sl == "path" ||
          sl == "staff" || sl == "part" || sl == "last" || sl == "mount" || sl == "clash" ||
          sl == "enchanted" || sl == "equipped" then
        none
      else some s

/-- Replace `alias` as a whole word in `seg` with `replacement`, skipping occurrences
that sit in a non-self-reference syntactic context (preceded by `named`, `empower`,
`a`, `an`, `another`, `other`, `each`, or a color word; or followed by `token(s)`,
`planeswalker(s)`, `creature`, `artifact`, `enchantment`). -/
private def replaceSafeShortAlias (seg alias replacement : String) : String := Id.run do
  let cs := seg.toList.toArray
  let al := alias.toList.toArray
  if al.isEmpty || cs.size < al.size then return seg
  let isWordChar (c : Char) : Bool := c.isAlphanum || c == '\'' || c == '-'
  let prevWord (startIdx : Nat) : String := Id.run do
    if startIdx == 0 then return ""
    let mut j := startIdx
    while j > 0 && cs[j - 1]! == ' ' do j := j - 1
    let endW := j
    while j > 0 && isWordChar cs[j - 1]! do j := j - 1
    return lowerAscii (String.ofList (cs.extract j endW).toList)
  let nextWord (afterIdx : Nat) : String := Id.run do
    let mut j := afterIdx
    while j < cs.size && cs[j]! == ' ' do j := j + 1
    let st := j
    while j < cs.size && isWordChar cs[j]! do j := j + 1
    return lowerAscii (String.ofList (cs.extract st j).toList)
  let badPrev : Array String := #[
    "named", "empower", "the", "a", "an", "another", "other", "each", "your",
    "white", "blue", "black", "red", "green", "colorless", "legendary"
  ]
  let badNext : Array String := #[
    "token", "tokens", "planeswalker", "planeswalkers", "creature", "creatures",
    "artifact", "artifacts", "enchantment", "enchantments", "card", "cards", "spell", "spells"
  ]
  let mut out : String := ""
  let mut i : Nat := 0
  while i < cs.size do
    let mut matched := false
    if i + al.size <= cs.size then
      let leftOk := i == 0 || !isWordChar cs[i - 1]!
      let mut eq := leftOk
      if eq then
        for k in [0 : al.size] do
          if cs[i + k]! != al[k]! then
            eq := false
            break
      if eq then
        -- Check `'s` possessive or whole-word end
        let afterA := i + al.size
        let isPoss := afterA + 1 < cs.size && cs[afterA]! == '\'' && cs[afterA + 1]! == 's' &&
          (afterA + 2 >= cs.size || !isWordChar cs[afterA + 2]!)
        let rightOk := isPoss || afterA >= cs.size || !isWordChar cs[afterA]!
        if rightOk then
          let pw := prevWord i
          let nw := nextWord (if isPoss then afterA + 2 else afterA)
          if !badPrev.contains pw && !badNext.contains nw then
            if isPoss then
              out := out ++ replacement ++ "'s"
              i := afterA + 2
            else
              out := out ++ replacement
              i := afterA
            matched := true
    if !matched then
      out := out.push cs[i]!
      i := i + 1
  return out

/-- Replace exact `cn` (and `cn's`) outside `"named <cn>"` / `"name is <cn>"` contexts. -/
private def replaceFullCardName (seg cn replacement : String) : String := Id.run do
  let cs := seg.toList.toArray
  let al := cn.toList.toArray
  if al.isEmpty || cs.size < al.size then return seg
  let isWordChar (c : Char) : Bool := c.isAlphanum || c == '\'' || c == '-'
  let mut out : String := ""
  let mut i : Nat := 0
  while i < cs.size do
    let mut matched := false
    if i + al.size <= cs.size then
      let leftOk := i == 0 || !isWordChar cs[i - 1]!
      let mut eq := leftOk
      if eq then
        for k in [0 : al.size] do
          if cs[i + k]! != al[k]! then
            eq := false
            break
      if eq then
        let afterA := i + al.size
        let isPoss := afterA + 1 < cs.size && cs[afterA]! == '\'' && cs[afterA + 1]! == 's' &&
          (afterA + 2 >= cs.size || !isWordChar cs[afterA + 2]!)
        let rightOk := isPoss || afterA >= cs.size || !isWordChar cs[afterA]!
        if rightOk then
          let preLow := lowerAscii (String.ofList (cs.extract (if i >= 12 then i - 12 else 0) i).toList)
          let isLiteralName :=
            preLow.endsWith "named " || preLow.endsWith "name is " ||
            preLow.endsWith "this " || preLow.endsWith "a " || preLow.endsWith "an " ||
            preLow.endsWith "another " || preLow.endsWith "target " || preLow.endsWith "each "
          if !isLiteralName then
            if isPoss then
              out := out ++ replacement ++ "'s"
              i := afterA + 2
            else
              out := out ++ replacement
              i := afterA
            matched := true
    if !matched then
      out := out.push cs[i]!
      i := i + 1
  return out

/-- Replace card-name aliases with `replacement` strictly outside `"..."` quoted spans
(so quoted token/emblem abilities preserve their own names such as `Galactus` or `The Void`). -/
def replaceCardNameOutsideQuotes (s cardName : String) (replacement : String := "this permanent") : String := Id.run do
  let cn := cardName.trimAscii.copy
  if cn.isEmpty then return s
  let short? := safeShortAlias? cn
  let replaceSegment (seg : String) : String :=
    let s1 := replaceFullCardName seg cn replacement
    match short? with
    | some sh => replaceSafeShortAlias s1 sh replacement
    | none => s1
  if !s.contains '"' then
    return replaceSegment s
  let cs := s.toList.toArray
  let mut out := ""
  let mut cur : Array Char := #[]
  let mut inQuote := false
  for i in [0 : cs.size] do
    let c := cs[i]!
    if c == '"' then
      if inQuote then
        out := out ++ "\"" ++ String.ofList cur.toList ++ "\""
        cur := #[]
        inQuote := false
      else
        out := out ++ replaceSegment (String.ofList cur.toList)
        cur := #[]
        inQuote := true
    else
      cur := cur.push c
  if !cur.isEmpty then
    if inQuote then
      out := out ++ "\"" ++ String.ofList cur.toList
    else
      out := out ++ replaceSegment (String.ofList cur.toList)
  return out

/-- Linear Stage-2 tokenizer scanning `s` into `Array OrbTok`, recursively lexing
`"..."` quoted abilities into `OrbTok.quoted` and recognizing `{...}` symbols,
punctuation, and leading em-dash labels. -/
partial def lexRaw (s : String) : Array OrbTok := Id.run do
  let cs := s.toList.toArray
  let mut out : Array OrbTok := #[]
  let mut i : Nat := 0
  while i < cs.size do
    let c := cs[i]!
    if c == ' ' || c == '\t' || c == '\n' then
      i := i + 1
    else if c == ':' then
      out := out.push .colon; i := i + 1
    else if c == ',' then
      out := out.push .comma; i := i + 1
    else if c == '.' then
      out := out.push .period; i := i + 1
    else if c == ';' then
      out := out.push .semicolon; i := i + 1
    else if c == '—' then
      out := out.push .emDash; i := i + 1
    else if c == '•' then
      out := out.push .bullet; i := i + 1
    else if c == '{' then
      let start := i
      i := i + 1
      while i < cs.size && cs[i]! != '}' do
        i := i + 1
      if i < cs.size then i := i + 1
      out := out.push (.symbol (String.ofList (cs.extract start i).toList))
    else if c == '"' then
      let start := i + 1
      i := i + 1
      while i < cs.size && cs[i]! != '"' do
        i := i + 1
      let rawInner := (String.ofList (cs.extract start i).toList).trimAscii.copy
      if i < cs.size then i := i + 1
      out := out.push (.quoted (lexRaw rawInner) rawInner)
    else
      let start := i
      while i < cs.size do
        let ch := cs[i]!
        if ch == ' ' || ch == '\t' || ch == '\n' || ch == ':' || ch == ',' ||
            ch == ';' || ch == '—' || ch == '•' || ch == '{' || ch == '"' then
          break
        if ch == '.' && (i + 1 >= cs.size || cs[i + 1]! == ' ' || cs[i + 1]! == '"' || cs[i + 1]! == '\n') then
          break
        i := i + 1
      let w := String.ofList (cs.extract start i).toList
      if !w.isEmpty then out := out.push (.word w)
  return out

private def isSelfRefTypeWord (w : String) : Bool :=
  match lowerAscii w with
  | "creature" | "permanent" | "card" | "spell" | "artifact" | "enchantment"
  | "equipment" | "aura" | "land" | "planeswalker" | "vehicle" | "saga"
  | "token" | "emblem" => true
  | _ => false

/-- Lex an Oracle line for `cardName` into `Array OrbTok`: preprocesses reminder
text / `{CHAOS}`, folds a leading em-dash label into `OrbTok.label`, and folds
self-references (`<cardName>`, `"this <type>"`, `"this <type>'s"`) outside quotes
into `OrbTok.selfRef`. -/
def lexLine (cardName line : String) : Array OrbTok := Id.run do
  let pre := preprocessOracleLine line
  let (lbl?, body) :=
    match pre.splitOn "—" with
    | head :: rest =>
      if !rest.isEmpty && !head.contains '"' && !head.contains ':' && !isRulesEmDashPrefix head then
        let h := head.trimAscii.copy
        if (classifyMechanicLabel? h).isSome || stripAbilityWord pre != pre then
          (some h, (String.intercalate "—" rest).trimAscii.copy)
        else (none, pre)
      else (none, pre)
    | [] => (none, pre)
  let body := replaceCardNameOutsideQuotes body cardName "this permanent"
  let rawToks := lexRaw body
  let mut out : Array OrbTok := #[]
  if let some h := lbl? then
    out := out.push (.label h)
  let mut i : Nat := 0
  while i < rawToks.size do
    match rawToks[i]? with
    | some (.word w) =>
      if lowerAscii w == "this" then
        match rawToks[i + 1]? with
        | some (.word w2) =>
          let l2 := lowerAscii w2
          if l2.endsWith "'s" && isSelfRefTypeWord (l2.dropEnd 2).copy then
            out := out.push (.selfRef true)
            i := i + 2
          else if isSelfRefTypeWord l2 then
            out := out.push (.selfRef false)
            i := i + 2
          else
            out := out.push (.word w)
            i := i + 1
        | _ =>
          out := out.push (.word w)
          i := i + 1
      else
        out := out.push (.word w)
        i := i + 1
    | some tok =>
      out := out.push tok
      i := i + 1
    | none => break
  return out

end Mtg.Engine.Parser
