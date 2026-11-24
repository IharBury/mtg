import Mtg.Engine.Card.CardDef
import Mtg.Engine.Card.OracleNorm

/-!
# Stage-1 Oracle Card Frame Splitter (CR 201–212, 712, 714, 715)

Splits raw printed card text into structured `CardFrame` / `FaceFrame` /
`SubFaceFrame` headers and unparsed rules lines:
- `//` double-faced card back face (CR 712),
- `//ADV//` Adventure and `//PREP//` Prepare sub-faces (CR 715),
- Name & mana cost (`{W}`, `{2/W}`, `{W/U}`, `{X}`, `{C}`),
- Type line (CR 205),
- Printed power/toughness into `PrintedStat` (CR 208.1–2a),
- Color indicator (CR 204), `Token` marker (CR 111.1), `Daybound` marker,
- Planeswalker loyalty (CR 209.1), Battle defense (CR 210.1), and Vanguard
  hand/life modifiers (CR 211.1 / 212.1),
- Loyalty ability headers `[+N]:` / `−N:` / `[0]:` / `[-X]:` (CR 209.2 / 107.7)
  and Saga chapter headers `I, II — ...` (CR 714.2).
-/

namespace Mtg.Engine.Parser

open Mtg.Engine
open Mtg.Engine.OracleNorm

/-- Parse `{W}`, `{2}`, `{G/U}`, `{2/W}`, `{X}`, `{C}` from the front of `s`. -/
def parseManaSymbol (s : String) : Option (ManaSymbol × String) :=
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

/-- A string that is only mana symbols, such as `{1}{G}`. -/
def parseManaCost (s : String) : Option ManaCost :=
  let s := s.trimAscii.copy
  if s.isEmpty || !s.startsWith "{" then none
  else
    let rec go (left : String) (acc : Array ManaSymbol) : Option ManaCost :=
      if left.isEmpty then some { symbols := acc }
      else
        match parseManaSymbol left with
        | none => none
        | some (sym, rest) =>
          if rest.length < left.length then go rest (acc.push sym) else none
    termination_by left.length
    go s #[]

/-- Name, and a mana cost when the line ends with one (`Allure of Power {1}{B}`). -/
def splitNameCost (line : String) : String × Option ManaCost :=
  let line := line.trimAscii.copy
  let rec go (cs : List Char) (acc : List Char) : String × Option ManaCost :=
    match cs with
    | [] => (line, none)
    | '{' :: rest =>
      let suffix := String.ofList cs
      match parseManaCost suffix with
      | some cost =>
        let name := (String.ofList acc.reverse).trimAscii.copy
        if name.isEmpty then (line, none) else (name, some cost)
      | none => go rest ('{' :: acc)
    | c :: rest => go rest (c :: acc)
  go line.toList []

/-- Every supertype in CR 205.4a, in any case. -/
def parseSupertype (w : String) : Option Supertype :=
  Supertype.ofOracle? w

/-- Every card type in CR 205.2a, singular or plural, in any case. -/
def parseCardType (w : String) : Option CardType :=
  CardType.ofOracle? w

/-- `Legendary Creature — Human Wizard`, or `Instant`. -/
def parseTypeLine (line : String) : Except String (Array Supertype × Array CardType × Array Subtype) :=
  let line := line.trimAscii.copy
  let (head, sub) :=
    if (line.splitOn " — ").length > 1 then
      let parts := line.splitOn " — "
      (parts.headD "", String.intercalate " — " parts.tail)
    else if (line.splitOn " - ").length > 1 then
      let parts := line.splitOn " - "
      (parts.headD "", String.intercalate " - " parts.tail)
    else (line, "")
  let words := head.splitOn " " |>.filter (· != "")
  if words.isEmpty then .error s!"empty type line: {line}"
  else Id.run do
    let mut supers : Array Supertype := #[]
    let mut types : Array CardType := #[]
    for w in words do
      match parseSupertype w with
      | some s => supers := supers.push s
      | none =>
        match parseCardType w with
        | some t => types := types.push t
        | none => return .error s!"unknown type-line word '{w}' in: {line}"
    if types.isEmpty then return .error s!"type line has no card type: {line}"
    -- CR 205.3b: planes are one multi-word subtype; creatures and kindreds
    -- keep `Time Lord` together; every other subtype is a single word.
    return .ok (supers, types, splitPrintedSubtypes types sub)

def parseUnsignedNat (tok : String) : Option Nat :=
  let tok := tok.trimAscii.copy
  if !tok.isEmpty && tok.all Char.isDigit then some tok.toNat! else none

/-- A minus sign, including the Unicode minus and en dash used in Oracle text. -/
def isMinusSign (c : Char) : Bool :=
  c == '-' || c == '−' || c == '–'

/-- `+1`, `-2`, or `0`, as printed for a vanguard modifier (CR 211.1 / 212.1). -/
def parseModifier (tok : String) : Option Int :=
  let tok := tok.trimAscii.copy
  if tok == "0" then some 0
  else if !tok.isEmpty && (tok.startsWith "+" || isMinusSign tok.front) then
    let n := (tok.drop 1).trimAscii.copy
    if !n.isEmpty && n.all Char.isDigit then
      let k : Int := n.toNat!
      some (if tok.startsWith "+" then k else -k)
    else none
  else none

def renderModifier (n : Int) : String :=
  if n > 0 then s!"+{n}" else toString n

/-- Text after `label` when `line` starts with it, ignoring case. -/
def prefixRest (line label : String) : Option String :=
  let line := line.trimAscii.copy
  if (lowerAscii line).startsWith (lowerAscii label) then
    some ((line.drop label.length).trimAscii.copy)
  else none

/-- `Hand +1` or `Life modifier: -2`. -/
def parseKeyedModifier (part key : String) : Option Int :=
  match prefixRest part key with
  | none => none
  | some rest =>
    let rest :=
      if (lowerAscii rest).startsWith "modifier" then
        ((rest.drop "modifier".length).trimAscii.copy)
      else rest
    let rest :=
      if rest.startsWith ":" then (rest.drop 1).trimAscii.copy else rest
    parseModifier rest

/-- `Hand +1, Life +10`, or the same pair with Life first. -/
def parseHandLifeLine (line : String) : Option (Int × Int) :=
  let parts := line.splitOn "," |>.map (·.trimAscii.copy) |>.filter (· != "")
  match parts with
  | [a, b] =>
    match parseKeyedModifier a "hand", parseKeyedModifier b "life" with
    | some h, some l => some (h, l)
    | _, _ =>
      match parseKeyedModifier a "life", parseKeyedModifier b "hand" with
      | some l, some h => some (h, l)
      | _, _ => none
  | _ => none

/-- `+1 +10` or `+1, -2`: unlabeled hand then life (CR 211.1 / 212.1). -/
def parseBareModifierPair (line : String) : Option (Int × Int) :=
  let parts := (line.replace "," " ").splitOn " "
    |>.map (·.trimAscii.copy) |>.filter (· != "")
  match parts with
  | [a, b] =>
    match parseModifier a, parseModifier b with
    | some h, some l => some (h, l)
    | _, _ => none
  | _ => none

private def digitValue (c : Char) : Nat :=
  c.toNat - '0'.toNat

/-- Natural number at the front of `cs`. -/
def readNatPrefix (cs : List Char) : Option (Nat × List Char) :=
  let rec go : List Char → Nat → Bool → Option (Nat × List Char)
    | [], _, false => none
    | [], n, true => some (n, [])
    | c :: rest, n, any =>
      if c.isDigit then go rest (n * 10 + digitValue c) true
      else if any then some (n, c :: rest) else none
  go cs 0 false

/-- Constant added to the one star in `cs`.
`*`, `1+*`, `*+1`, `2+*`, `*-1`, and `-1+*` are accepted. -/
private def readStarConstant (cs : List Char) : Option Int :=
  let rec go (fuel : Nat) (cs : List Char) (acc : Int) (saw started : Bool) : Option Int :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match cs with
      | [] => if saw then some acc else none
      | '*' :: rest =>
        if saw || started then none else go fuel rest acc true true
      | '+' :: '*' :: rest =>
        if !started || saw then none else go fuel rest acc true true
      | '+' :: rest =>
        if !started then none
        else
          match readNatPrefix rest with
          | some (n, rest) => go fuel rest (acc + Int.ofNat n) saw true
          | none => none
      | '-' :: rest =>
        match readNatPrefix rest with
        | some (n, rest) => go fuel rest (acc - Int.ofNat n) saw true
        | none => none
      | _ =>
        if started then none
        else
          match readNatPrefix cs with
          | some (n, rest) => go fuel rest (acc + Int.ofNat n) saw true
          | none => none
  go (cs.length + 1) cs 0 false false

/-- `2`, `-1`, `*`, `1+*`, or `*+1`. -/
def parseStat (tok : String) : Option PrintedStat :=
  let cs := tok.toList
  if cs.contains '*' then
    (readStarConstant cs).map fun n => PrintedStat.star n
  else
    let (neg, digits) :=
      if cs.head? == some '-' then (true, cs.drop 1) else (false, cs)
    match readNatPrefix digits with
    | some (n, []) =>
      let k : Int := if neg then -Int.ofNat n else Int.ofNat n
      some (.fixed k)
    | _ => none

/-- `2/2`, `*/*`, `1/*`, or `1+*/1+*` (CR 208.1 / 208.2). -/
def parsePT (line : String) : Option (PrintedStat × PrintedStat) :=
  let line := line.trimAscii.copy.replace " " ""
  match line.splitOn "/" with
  | [a, b] =>
    match parseStat a, parseStat b with
    | some pa, some pb => some (pa, pb)
    | _, _ => none
  | _ => none

def parseColorName (w : String) : Option Color :=
  match lowerAscii w.trimAscii.copy with
  | "white" | "w" => some .white
  | "blue" | "u" => some .blue
  | "black" | "b" => some .black
  | "red" | "r" => some .red
  | "green" | "g" => some .green
  | _ => none

def parseColorIndicator (line : String) : Option ColorSet :=
  let line := line.trimAscii.copy
  let pref := "Color indicator:"
  if !(line.startsWith pref) then none
  else
    let rest := (line.drop pref.length).trimAscii.copy
    let words := rest.splitOn "," |>.map (·.trimAscii.copy) |>.filter (· != "")
    let colors := words.filterMap parseColorName
    if colors.isEmpty || colors.length != words.length then none
    else some (colors.foldl (fun acc c => acc.insert c) ColorSet.empty)

def nonEmptyLines (text : String) : List String :=
  text.splitOn "\n" |>.map (·.trimAscii.copy) |>.filter (· != "")

/-- Split a back face introduced by a line that is exactly `//` (CR 712). -/
def splitBackFace (lines : List String) : List String × Option (List String) :=
  match lines.idxOf? "//" with
  | none => (lines, none)
  | some i =>
    let front := lines.take i
    let back := lines.drop (i + 1)
    (front, some back)

/-- Pull a marked alternate-face block (`//ADV//` or `//PREP//`) out of the rules. -/
def splitMarked (mark : String) (lines : List String) : List String × Option (List String) :=
  let rec go (acc : List String) : List String → List String × Option (List String)
    | [] => (acc.reverse, none)
    | line :: rest =>
      if line == mark then (acc.reverse, some rest)
      else if line.startsWith mark then
        let extra := (line.drop mark.length).trimAscii.copy
        let face := if extra.isEmpty then rest else extra :: rest
        (acc.reverse, some face)
      else go (line :: acc) rest
  go [] lines

/-- Pull an Adventure block out of the rules lines (CR 715). -/
def splitAdventure (lines : List String) : List String × Option (List String) :=
  splitMarked "//ADV//" lines

/-- Pull a prepare-spell block out of the rules lines. -/
def splitPrepare (lines : List String) : List String × Option (List String) :=
  splitMarked "//PREP//" lines

def romanToken (s : String) : Bool :=
  s.all (fun c => c == 'I' || c == 'V' || c == 'X' || c == ',')

/-- `I — Scry 2.` or `II, III — …` (CR 714.2). -/
def parseChapterHeader (line : String) : Option (String × String) :=
  let line := line.trimAscii.copy
  let parts :=
    if (line.splitOn " — ").length > 1 then line.splitOn " — "
    else if line.contains '—' then line.splitOn "—"
    else []
  match parts with
  | roman :: rest =>
    let roman := roman.trimAscii.copy
    let text := (String.intercalate " — " rest).trimAscii.copy
    let bits := roman.splitOn "," |>.map (·.trimAscii.copy) |>.filter (· != "")
    if !bits.isEmpty && bits.all romanToken && !text.isEmpty then some (roman, text)
    else none
  | _ => none

/-- `Loyalty: N` (any case), the labeled form of the corner number (CR 209.1). -/
def parseLoyaltyLabel (line : String) : Option Nat :=
  prefixRest line "Loyalty:" |>.bind parseUnsignedNat

/-- Split labeled loyalty numbers from the other lines, keeping order. -/
def partitionLoyalty (lines : List String) : List Nat × List String :=
  let rec go : List String → List Nat → List String → List Nat × List String
    | [], labels, rules => (labels.reverse, rules.reverse)
    | line :: rest, labels, rules =>
      match parseLoyaltyLabel line with
      | some n => go rest (n :: labels) rules
      | none => go rest labels (line :: rules)
  go lines [] []

/-- A bare corner number at the start or end of `rules` (CR 209.1). -/
def takeCornerLoyalty (name : String) (rules : List String) :
    Except String (Option Nat × List String) :=
  match rules with
  | [] => .ok (none, [])
  | [only] =>
    match parseUnsignedNat only with
    | some n => .ok (some n, [])
    | none => .ok (none, rules)
  | first :: rest =>
    match rest.getLast? with
    | none => .ok (none, rules)
    | some last =>
      let middle := rest.dropLast
      match parseUnsignedNat first, parseUnsignedNat last with
      | some _, some _ => .error s!"{name} has more than one loyalty number"
      | some n, none => .ok (some n, rest)
      | none, some n => .ok (some n, first :: middle)
      | none, none => .ok (none, rules)

/-- Printed loyalty of a planeswalker, and the rules lines that remain (CR 209.1). -/
def detachLoyalty (name : String) (isPlaneswalker : Bool) (lines : List String) :
    Except String (Option Int × List String) :=
  if !isPlaneswalker then .ok (none, lines)
  else
    let (labels, rules) := partitionLoyalty lines
    if labels.length > 1 then .error s!"{name} has more than one loyalty number"
    else
      match takeCornerLoyalty name rules with
      | .error e => .error e
      | .ok (corner, rules) =>
        match labels, corner with
        | [n], none => .ok (some (n : Int), rules)
        | [], some n => .ok (some (n : Int), rules)
        | [], none => .ok (none, rules)
        | _, _ => .error s!"{name} has more than one loyalty number"

/-- `Defense: N` (any case), the labeled form of the corner number (CR 210.1). -/
def parseDefenseLabel (line : String) : Option Nat :=
  prefixRest line "Defense:" |>.bind parseUnsignedNat

/-- Split labeled defense numbers from the other lines, keeping order. -/
def partitionDefense (lines : List String) : List Nat × List String :=
  let rec go : List String → List Nat → List String → List Nat × List String
    | [], labels, rules => (labels.reverse, rules.reverse)
    | line :: rest, labels, rules =>
      match parseDefenseLabel line with
      | some n => go rest (n :: labels) rules
      | none => go rest labels (line :: rules)
  go lines [] []

/-- A bare corner number at the start or end of `rules` (CR 210.1). -/
def takeCornerDefense (name : String) (rules : List String) :
    Except String (Option Nat × List String) :=
  match rules with
  | [] => .ok (none, [])
  | [only] =>
    match parseUnsignedNat only with
    | some n => .ok (some n, [])
    | none => .ok (none, rules)
  | first :: rest =>
    match rest.getLast? with
    | none => .ok (none, rules)
    | some last =>
      let middle := rest.dropLast
      match parseUnsignedNat first, parseUnsignedNat last with
      | some _, some _ => .error s!"{name} has more than one defense number"
      | some n, none => .ok (some n, rest)
      | none, some n => .ok (some n, first :: middle)
      | none, none => .ok (none, rules)

/-- Printed defense of a battle, and the rules lines that remain (CR 210.1). -/
def detachDefense (name : String) (isBattle : Bool) (lines : List String) :
    Except String (Option Nat × List String) :=
  if !isBattle then .ok (none, lines)
  else
    let (labels, rules) := partitionDefense lines
    if labels.length > 1 then .error s!"{name} has more than one defense number"
    else
      match takeCornerDefense name rules with
      | .error e => .error e
      | .ok (corner, rules) =>
        match labels, corner with
        | [n], none => .ok (some n, rules)
        | [], some n => .ok (some n, rules)
        | [], none => .ok (none, rules)
        | _, _ => .error s!"{name} has more than one defense number"

/-- Record one hand or life modifier, rejecting a second one. -/
def addPrintedModifier (name kind : String) (cur : Option Int) (n : Int) :
    Except String (Option Int) :=
  match cur with
  | some _ => .error s!"{name} has more than one {kind} modifier"
  | none => .ok (some n)

/-- Pull labeled hand and life modifiers out of `lines`, keeping other lines. -/
def partitionVanguardModifiers (name : String) (lines : List String) :
    Except String (Option Int × Option Int × List String) :=
  let rec go : List String → Option Int → Option Int → List String →
      Except String (Option Int × Option Int × List String)
    | [], hand, life, rules => .ok (hand, life, rules.reverse)
    | line :: rest, hand, life, rules =>
      match parseHandLifeLine line with
      | some (h, l) =>
        match addPrintedModifier name "hand" hand h with
        | .error e => .error e
        | .ok hand =>
          match addPrintedModifier name "life" life l with
          | .error e => .error e
          | .ok life => go rest hand life rules
      | none =>
        match parseKeyedModifier line "hand" with
        | some n =>
          match addPrintedModifier name "hand" hand n with
          | .error e => .error e
          | .ok hand => go rest hand life rules
        | none =>
          match parseKeyedModifier line "life" with
          | some n =>
            match addPrintedModifier name "life" life n with
            | .error e => .error e
            | .ok life => go rest hand life rules
          | none =>
            match parseBareModifierPair line with
            | some (h, l) =>
              match addPrintedModifier name "hand" hand h with
              | .error e => .error e
              | .ok hand =>
                match addPrintedModifier name "life" life l with
                | .error e => .error e
                | .ok life => go rest hand life rules
            | none => go rest hand life (line :: rules)
  go lines none none []

/-- Bare modifier lines at the front of `lines`. -/
def takeLeadingModifiers (lines : List String) : List Int × List String :=
  let rec go : List String → List Int → List Int × List String
    | [], acc => (acc.reverse, [])
    | line :: rest, acc =>
      match parseModifier line with
      | some n => go rest (n :: acc)
      | none => (acc.reverse, line :: rest)
  go lines []

/-- Bare modifier lines at the end of `lines`, in printed order. -/
def takeTrailingModifiers (lines : List String) : List String × List Int :=
  let (revMods, revRest) := takeLeadingModifiers lines.reverse
  (revRest.reverse, revMods.reverse)

/-- Assign bare corner numbers that labels did not already name (CR 211.1 / 212.1). -/
def applyCornerModifiers (name : String) (hand life : Option Int) (bare : List Int) :
    Except String (Option Int × Option Int) :=
  match bare, hand, life with
  | [], hand, life => .ok (hand, life)
  | [n], none, some l => .ok (some n, some l)
  | [n], some h, none => .ok (some h, some n)
  | [_], none, none => .error s!"{name} has only one of its hand and life modifiers"
  | [_], some _, some _ => .error s!"{name} has more than one life modifier"
  | [h, l], none, none => .ok (some h, some l)
  | [_, _], some _, _ => .error s!"{name} has more than one hand modifier"
  | [_, _], none, some _ => .error s!"{name} has more than one life modifier"
  | _, _, _ => .error s!"{name} has more than one hand modifier"

/-- Bare hand and life modifiers at the corners of `rules` (CR 211.1 / 212.1). -/
def takeCornerHandLife (name : String) (hand life : Option Int) (rules : List String) :
    Except String (Option Int × Option Int × List String) :=
  let (pre, rest) := takeLeadingModifiers rules
  let (mid, suf) := takeTrailingModifiers rest
  if !pre.isEmpty && !suf.isEmpty then
    match pre, suf, hand, life with
    | [h], [l], none, none => .ok (some h, some l, mid)
    | _, _, some _, _ => .error s!"{name} has more than one hand modifier"
    | _, _, none, some _ => .error s!"{name} has more than one life modifier"
    | _, _, none, none => .error s!"{name} has more than one hand modifier"
  else
    let bare := if pre.isEmpty then suf else pre
    match applyCornerModifiers name hand life bare with
    | .error e => .error e
    | .ok (hand, life) => .ok (hand, life, mid)

/-- Printed hand and life modifiers of a vanguard, and the rules that remain
(CR 211.1 / 212.1). -/
def detachHandLife (name : String) (isVanguard : Bool) (lines : List String) :
    Except String (Option Int × Option Int × List String) :=
  if !isVanguard then .ok (none, none, lines)
  else
    match partitionVanguardModifiers name lines with
    | .error e => .error e
    | .ok (hand, life, rules) => takeCornerHandLife name hand life rules

/-- True when `c` is a minus sign that can introduce a negative loyalty symbol. -/
def isLoyaltyMinus (c : Char) : Bool :=
  isMinusSign c

/-- Sign of a loyalty symbol, then the text after it. -/
def splitLoyaltySign (s : String) : Option Bool × String :=
  if s.startsWith "+" then (some true, (s.drop 1).copy)
  else if !s.isEmpty && isLoyaltyMinus s.front then (some false, (s.drop 1).copy)
  else (none, s)

/-- `N` or `X` at the front of a loyalty symbol. -/
def readLoyaltyMagnitude (s : String) : Option (Bool × Nat × String) :=
  if s.startsWith "X" || s.startsWith "x" then some (true, 0, (s.drop 1).copy)
  else
    match readNatPrefix s.toList with
    | some (n, rest) => some (false, n, String.ofList rest)
    | none => none

/-- Build a loyalty symbol from its sign and magnitude (CR 107.7). -/
def loyaltySymbolOf (sign : Option Bool) (isX : Bool) (n : Nat) : Option LoyaltySymbol :=
  if isX then
    match sign with
    | some true => some .plusX
    | some false => some .minusX
    | none => none
  else if n == 0 then some .zero
  else
    match sign with
    | some true => some (.plus n)
    | some false => some (.minus n)
    | none => none

/-- An activated ability introduced by a loyalty symbol (CR 209.2 / 107.7).
Accepts `[+N]:`, `[-N]:`, `[0]:`, `[+X]:`, `[-X]:` and unbracketed forms. -/
def parseLoyaltyAbilityLine (line : String) : Option (LoyaltySymbol × String) :=
  let line := line.trimAscii.copy
  let (bracketed, rest) :=
    if line.startsWith "[" then (true, (line.drop 1).copy) else (false, line)
  let (sign, rest) := splitLoyaltySign rest
  match readLoyaltyMagnitude rest with
  | none => none
  | some (isX, n, rest) =>
    let rest :=
      if bracketed then
        if rest.startsWith "]" then some ((rest.drop 1).copy) else none
      else some rest
    match rest with
    | none => none
    | some rest =>
      let rest := rest.trimAscii.copy
      if rest.startsWith ":" then
        let effect := (rest.drop 1).trimAscii.copy
        if effect.isEmpty then none
        else (loyaltySymbolOf sign isX n).map fun sym => (sym, effect)
      else none

/-- Parsed header and unparsed rules lines of an Adventure / Prepare sub-face (CR 715). -/
structure SubFaceFrame where
  kind : SubFaceKind
  base : CardDef
  rules : List String
deriving Repr

/-- Parsed header, unparsed rules lines, and sub-faces of one card face (CR 201–212). -/
structure FaceFrame where
  base : CardDef
  rules : List String
  subFaces : Array SubFaceFrame := #[]
deriving Repr

/-- Parsed frame of a full printed card (front face + optional `//` back face, CR 712). -/
structure CardFrame where
  front : FaceFrame
  back? : Option FaceFrame := none
deriving Repr

/-- Stage-1 split of an Adventure (`//ADV//`) or Prepare (`//PREP//`) sub-face block. -/
def splitSubFaceFrame (kind : SubFaceKind) (lines : List String) : Except String SubFaceFrame :=
  match lines with
  | [] => .error "empty sub-face"
  | nameLine :: rest =>
    let (name, costOnName) := splitNameCost nameLine
    let (cost, afterCost) :=
      match costOnName, rest with
      | some cost, rest => (cost, rest)
      | none, line :: rest =>
        match parseManaCost line with
        | some cost => (cost, rest)
        | none => (ManaCost.empty, line :: rest)
      | none, [] => (ManaCost.empty, [])
    match afterCost with
    | [] => .error s!"Sub-face {name} is missing a type line"
    | typeLine :: rules =>
      match parseTypeLine typeLine with
      | .error e => .error e
      | .ok (supers, types, subtypes) =>
        let (colorIndicator, rules) :=
          match rules with
          | line :: rest =>
            match parseColorIndicator line with
            | some cs => (some cs, rest)
            | none => (none, line :: rest)
          | [] => (none, [])
        let initSubtypes :=
          match kind with
          | .adventure => if subtypes.any (· == "Adventure") then subtypes else subtypes.push "Adventure"
          | .prepare => subtypes
        let base : CardDef := {
          name
          manaCost := cost
          colorIndicator
          supertypes := supers
          types
          subtypes := initSubtypes
        }
        .ok { kind, base, rules }

/-- Stage-1 split of one card face (no `//` back face). -/
def splitFaceFrame (lines : List String) : Except String FaceFrame :=
  let lines := lines.filter (· != "")
  match lines with
  | [] => .error "empty card text"
  | nameLine :: rest =>
    let (name, costOnName) := splitNameCost nameLine
    let (cost, afterCost) :=
      match costOnName, rest with
      | some cost, rest => (cost, rest)
      | none, line :: rest =>
        match parseManaCost line with
        | some cost => (cost, rest)
        | none => (ManaCost.empty, line :: rest)
      | none, [] => (ManaCost.empty, [])
    match afterCost with
    | [] => .error s!"{name} is missing a type line"
    | typeLine :: rest =>
      match parseTypeLine typeLine with
      | .error e => .error e
      | .ok (supers, types, subtypes) =>
        let (pt, rest) : (Option PrintedStat × Option PrintedStat) × List String :=
          match rest with
          | line :: rest =>
            match parsePT line with
            | some (p, t) => ((some p, some t), rest)
            | none => ((none, none), line :: rest)
          | [] => ((none, none), [])
        let rec takeExtras (c : CardDef) : List String → CardDef × List String
          | [] => (c, [])
          | line :: rest =>
            if line == "Token" then takeExtras { c with isToken := true } rest
            else if lowerAscii line == "daybound" then takeExtras (c.withKeyword Keyword.daybound) rest
            else
              match parseColorIndicator line with
              | some cs => takeExtras { c with colorIndicator := some cs } rest
              | none => (c, line :: rest)
        let base : CardDef := {
          name, manaCost := cost, supertypes := supers, types, subtypes
          power := pt.1, toughness := pt.2
        }
        let (base, rest) := takeExtras base rest
        let (rules, adv) := splitAdventure rest
        let (rules, prep) := splitPrepare rules
        match detachLoyalty base.name base.isPlaneswalker rules with
        | .error e => .error e
        | .ok (loyalty, rules) =>
        match detachDefense base.name base.isBattle rules with
        | .error e => .error e
        | .ok (defense, rules) =>
        match detachHandLife base.name base.isVanguard rules with
        | .error e => .error e
        | .ok (handModifier, lifeModifier, rules) =>
        let base := { base with
          loyalty := loyalty
          defense := defense
          handModifier := handModifier
          lifeModifier := lifeModifier }
        let sfs : Except String (Array SubFaceFrame) := do
          let mut out : Array SubFaceFrame := #[]
          if let some advLines := adv then
            let sf ← splitSubFaceFrame .adventure advLines
            out := out.push sf
          if let some prepLines := prep then
            let sf ← splitSubFaceFrame .prepare prepLines
            out := out.push sf
          return out
        match sfs with
        | .error e => .error e
        | .ok subFaces => .ok { base, rules, subFaces }

/-- Stage-1 split of a full printed card (front + optional `//` back face). -/
def splitCardFrame (text : String) : Except String CardFrame :=
  let lines := nonEmptyLines text
  let (frontLines, backLines?) := splitBackFace lines
  match splitFaceFrame frontLines with
  | .error e => .error e
  | .ok front =>
    match backLines? with
    | none => .ok { front, back? := none }
    | some backLines =>
      match splitFaceFrame backLines with
      | .error e => .error e
      | .ok back => .ok { front, back? := some back }

end Mtg.Engine.Parser
