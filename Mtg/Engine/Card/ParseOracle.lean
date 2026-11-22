import Std.Data.HashMap
import Std.Data.HashSet
import Mtg.Engine.Card.CardDef
import Mtg.Engine.Card.OracleActivate
import Mtg.Engine.Card.OracleArgs
import Mtg.Engine.Card.FrcParse
import Mtg.Engine.Card.OracleCandidates
import Mtg.Engine.Card.OracleNorm
import Mtg.Engine.Card.Parser.SubGrammars

/-!
# Parsing a full Oracle card

`parseOracleCard` reads one card's printed text — name, mana cost, type line,
power and toughness, and rules text — into a `CardDef`. The rules text is
matched to the abilities the engine models. Parsing fails when a line is not
recognized or an effect would not resolve. The resulting `CardDef` does not
keep the source text.
-/

namespace Mtg.Engine

open OracleNorm
open OracleActivate
open OracleArgs
open OracleCandidates

/-- Parse `{W}`, `{2}`, `{G/U}`, `{X}`, `{C}` from the front of `s`. -/
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

/-- `+1`, `-2`, or `0`, as printed for a vanguard modifier (CR 211.1 / 212.1).

A plus sign adds the number and a minus sign subtracts it. Zero leaves the
total unchanged, and so do `+0` and `-0`. An unsigned number other than zero
is not a modifier. -/
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

/-- One side of a printed power/toughness box (CR 208.1 / 208.2).

`number` is the fixed value, or the constant added to a star. A bare `*`
has `number = none` and `star = true`. `1+*` and `*+1` both have
`number = some 1` and `star = true`. When the star can't be determined,
count it as 0 (CR 208.2a), so the value is `number.getD 0`. -/
structure PrintedStat where
  number : Option Int := none
  star : Bool := false
deriving Repr, Inhabited, BEq

namespace PrintedStat

/-- This stat with an undetermined star counted as 0 (CR 208.2a / 208.5). -/
def undetermined (s : PrintedStat) : Int :=
  s.number.getD 0

end PrintedStat

private def digitValue (c : Char) : Nat :=
  c.toNat - '0'.toNat

/-- Natural number at the front of `cs`. -/
private def readNatPrefix (cs : List Char) : Option (Nat × List Char) :=
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
        -- A star after a number needs a `+`, as in `1+*`. `2*` is not a stat.
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
    match readStarConstant cs with
    | none => none
    | some k =>
      if k == 0 then some { star := true } else some { number := some k, star := true }
  else
    let (neg, digits) :=
      if cs.head? == some '-' then (true, cs.drop 1) else (false, cs)
    match readNatPrefix digits with
    | some (n, []) =>
      let k : Int := if neg then -Int.ofNat n else Int.ofNat n
      some { number := some k }
    | _ => none

/-- `2/2`, `*/*`, `1/*`, or `1+*/1+*` (CR 208.1 / 208.2).

A star is 0 when it can't be determined, so Lost Order of Jarkeld's `1+*`
is 1 off the battlefield (CR 208.2a). `*+1` is the same value as `1+*`. -/
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

/-- True when `line` is the non-keyword CR 509.1b static ability `"~ can't be blocked."` -/
def isCantBeBlockedLine (cardName line : String) : Bool :=
  let prepared := prepareLine cardName line
  let cleaned := dropLeadingThis ((prepared.replace "." "").trimAscii.copy)
  cleaned == "can't be blocked"

/-- Keywords routed through activated-ability handlers (`equip`, `cycling`) stay
out of `keywordLineAbilities` until their catalog consumers migrate. -/
private def isKeywordLineEligible : KeywordAbility → Bool
  | .equip _ _ | .cycling _ _ => false
  | _ => true

/-- Keyword lines (such as `Flying, haste`, `Prowess, prowess`, `Nonbasic landwalk`,
`Legendary landwalk`, `Snow landwalk`, or `Flying, protection from white and from black`),
delegated to `Parser.parseKeywordLine` so the catalog parser and compositional
keyword sub-grammar cannot drift. Retains multiplicity for cumulative keywords
(CR 702.83b / 702.85 / 702.108b) and never matches `"can't be blocked"`
(CR 509.1b static ability). -/
def keywordLineAbilities (_cardName line : String) : Option (Array KeywordAbility) :=
  -- CR 207.4 / 207.2c: strip leading `{CHAOS}` and CR 207.2c ability words
  -- without stripping keyword em-dashes (`Ward—`, `Flashback—`, `Impending N—`).
  let cleaned := stripAbilityWords (stripChaosSymbol line)
  match Parser.parseKeywordLine cleaned with
  | some kws =>
    if kws.all isKeywordLineEligible then some kws else none
  | none => none

def nonEmptyLines (text : String) : List String :=
  text.splitOn "\n" |>.map (·.trimAscii.copy) |>.filter (· != "")

/-- Split a back face introduced by a line that is exactly `//`. -/
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

/-- Pull an Adventure block out of the rules lines. -/
def splitAdventure (lines : List String) : List String × Option (List String) :=
  splitMarked "//ADV//" lines

/-- Pull a prepare-spell block out of the rules lines (Reality Fracture). -/
def splitPrepare (lines : List String) : List String × Option (List String) :=
  splitMarked "//PREP//" lines

/-- Spell-level `Empower Jace N`, and the line with that sentence removed.
Trigger and activated lines are left alone so the loyalty goes on the ability. -/
def spellEmpower (line : String) : Option (Nat × String) :=
  let low := lowerAscii line
  let parts := low.splitOn "empower jace "
  if parts.length != 2 then none
  else
    let beforeLow := parts[0]!
    let afterLow := parts[1]!
    -- `takeWhile` yields a slice; copy it so `.length` is not the deprecated
    -- slice length (`lake build --wfail` treats that warning as a failure).
    let digits := (afterLow.takeWhile Char.isDigit).copy
    if digits.isEmpty then none
    else if beforeLow.contains ':' then none
    else if beforeLow.startsWith "when " || beforeLow.startsWith "whenever " ||
        beforeLow.startsWith "at the " then none
    else
      let n := digits.toNat!
      let before := (line.take beforeLow.length).trimAscii.copy
      let after :=
        (line.drop (beforeLow.length + "empower jace ".length + digits.length)).trimAscii.copy
      let after :=
        if after == "." || after == "" then ""
        else if after.startsWith "." then (after.drop 1).trimAscii.copy
        else after
      let rest :=
        if before.isEmpty then after
        else if after.isEmpty then before
        else s!"{before} {after}"
      some (n, rest.trimAscii.copy)

/-- `behold a Jace or pay {N}` as an additional cost. -/
def beholdOrPay (line : String) : Option (CardSubtype × Nat) :=
  let low := lowerAscii line
  if !(low.startsWith "as an additional cost") || !(low.contains "behold") then none
  else
    let quality : CardSubtype := if low.contains "jace" then .jace else .goblin
    match low.splitOn "{" with
    | _ :: brace :: _ =>
      let digits := brace.takeWhile Char.isDigit
      if digits.isEmpty then none else some (quality, digits.toNat!)
    | _ => none

def romanToken (s : String) : Bool :=
  s.all (fun c => c == 'I' || c == 'V' || c == 'X' || c == ',')

/-- `I — Scry 2.` or `II, III — …`. -/
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

def braceNat (s : String) : Option Nat :=
  match parseManaSymbol s.trimAscii.copy with
  | some (.generic n, rest) => if rest.isEmpty then some n else none
  | _ => none

/-- First `{N}` in `s`. -/
def firstBraceNat (s : String) : Option Nat :=
  let rec go (cs : List Char) : Option Nat :=
    match cs with
    | [] => none
    | '{' :: rest =>
      let digits := rest.takeWhile Char.isDigit
      match rest.dropWhile Char.isDigit with
      | '}' :: _ =>
        if digits.isEmpty then go rest else some (String.ofList digits).toNat!
      | _ => go rest
    | _ :: rest => go rest
  go s.toList

def manaLetters (s : String) : Option (List ManaType) :=
  let rec go (left : String) (acc : List ManaType) : Option (List ManaType) :=
    if left.isEmpty then some acc.reverse
    else if left.startsWith "or " then
      let rest := (left.drop 3).trimAscii.copy
      if rest.length < left.length then go rest acc else none
    else if left.startsWith "and/or " then
      let rest := (left.drop 7).trimAscii.copy
      if rest.length < left.length then go rest acc else none
    else
      match parseManaSymbol left with
      | some (.colored c, rest) =>
        if rest.length < left.length then go rest (.colored c :: acc) else none
      | some (.colorless, rest) =>
        if rest.length < left.length then go rest (.colorless :: acc) else none
      | _ => none
  termination_by left.length
  let s := s.trimAscii.copy
  if s.startsWith "{" then go s [] else none

def isEquipAbility (ab : ActivatedAbility) : Bool :=
  ab.isEquip

def typecyclingLand? (ab : ActivatedAbility) : Option String :=
  if ab.isFromHand && ab.cost.discardSource then
    match ab.tag? with
    | some (.cycling (some t)) => if t == "Plan" then none else some t
    | _ =>
      match ab.effect.body with
      | .player (.searchLibrary spec) =>
        match spec.filter with
        | .hasSubtype (.literal sub) =>
          if sub.englishName == "Plan" then none else some sub.englishName
        | .hasSupertype sup => some sup.englishName
        | .hasType ty => some ty.englishName
        | .all #[.hasSupertype .basic, .hasType .land] => some "Basic land"
        | _ => none
      | _ => none
  else none

private def renderActivatedCostReduction (r : ActivationCostReduction) : String :=
  match r.amount, r.condition? with
  | .const n, some (.exists (.inZones .battlefield (.all #[.hasSupertype .legendary, .hasType .creature, .controlledBy .you]))) =>
    if n > 0 then
      s!" This ability costs \{{n.toNat}} less to activate if you control a legendary creature."
    else ""
  | .aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal .equipment), .controlledBy .you])), none =>
    " This ability costs {1} less to activate for each Equipment you control."
  | .binary .mul (.const n) (.aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal .equipment), .controlledBy .you]))), none =>
    if n > 0 then
      s!" This ability costs \{{n.toNat}} less to activate for each Equipment you control."
    else ""
  | .const n, some (.all #[.exists (.target 0), .forAll (.target 0) (.all #[.hasType .creature, .stat .power .le (.const maxP)])]) =>
    if n > 0 then
      s!" This ability costs \{{n.toNat}} less to activate if it targets a creature with power {maxP} or less."
    else ""
  | _, _ => ""

private def renderActivatedCondition (cond? : Option Condition) (onceEachTurn : Bool) : String :=
  match cond? with
  | some .isYourTurn =>
    if onceEachTurn then " Activate only during your turn and only once each turn."
    else " Activate only during your turn."
  | some cond =>
    let condStr :=
      if cond == ActivatedAbility.condControlsLegendaryCreature then
        " Activate only if you control a legendary creature."
      else if cond == ActivatedAbility.condAttackedWithCreaturesAtLeast 2 then
        " Activate only if you attacked with two or more creatures this turn."
      else if cond == ActivatedAbility.condOpponentDealtNoncombatDamageThisTurn then
        " Activate only if an opponent has been dealt noncombat damage this turn."
      else
        match cond with
        | .exists (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you, .stat .toughness .ge (.const n)])) =>
          if n > 0 then
            s!" Activate only if you control a creature with toughness {n.toNat} or greater."
          else ""
        | .cmp .ge (.aggregate .count .one (.inZones .yourGraveyard (.all #[.isCard, .hasType .creature]))) (.const n) =>
          if n > 0 then
            let cards :=
              if n == 1 then "a creature card"
              else s!"{n.toNat} or more creature cards"
            s!" Activate only if there are {cards} in your graveyard."
          else ""
        | _ => s!" Activate only if {toOracleStr cond}."
    condStr ++ (if onceEachTurn then " Activate only once each turn." else "")
  | none =>
    if onceEachTurn then " Activate only once each turn." else ""

/-- Oracle line for one activated ability, matching the wording catalogs store. -/
def printedActivated (ab : ActivatedAbility) : String :=
  if !ab.printed.isEmpty then ab.printed
  else if ab.manaProduction?.isSome then ab.toOracle {}
  else if isEquipAbility ab then
    let pay := if ab.cost.payLife != 0 then s!", Pay {ab.cost.payLife} life" else ""
    let subtype? :=
      ab.equipSubtype?.orElse fun _ =>
        ab.effect.targetSpec.creatureYouControlSubtype?
    let worthy := ab.isEquipWorthy || ab.effect.targetSpec.isWorthyCreatureYouControl
    match subtype? with
    | some t => s!"Equip {t} {ab.cost.mana}{pay}"
    | none =>
      if worthy then s!"Equip worthy {ab.cost.mana}{pay}"
      else if pay != "" then s!"Equip—{ab.cost.mana}{pay}"
      else s!"Equip {ab.cost.mana}"
  else
    match typecyclingLand? ab with
    | some t => s!"{t}cycling {ab.cost.mana}"
    | none =>
      let redStr := String.join (ab.costReductions.toList.map renderActivatedCostReduction)
      let timing :=
        redStr ++
        (if ab.timing == .sorcery then " Activate only as a sorcery." else "") ++
        renderActivatedCondition ab.condition? (ab.turnLimit? == some 1 && !ab.isBoast)
      let body :=
        if ab.isModal then
          let modes := ab.allModes.toList.map Effect.toNotation
          s!"Choose one — {String.intercalate "; " modes}"
        else ab.effect.toNotation
      s!"{ab.cost.toNotation}: {body}.{timing}"

def spellBody (cardName : String) (e : Effect) : String :=
  let body := e.phrase
  if body.startsWith "deals" || body.startsWith "Deals" then s!"{cardName} {body}" else body

/-- Lines a spell effect contributes, in printed order. -/
def effectLines (cardName : String) (e : Effect) : List String :=
  let fallback :=
    (spellBody cardName e).splitOn "\n" |>.map (·.trimAscii.copy) |>.filter (· != "")
  match e.body with
  | .seq #[
      .permanent (.setTapped (.target 0) true),
      .player (.scry .you (.const scryN)),
      .player (.drawCards .you (.const drawN))
    ] =>
    let s := scryN.toNat
    let d := drawN.toNat
    [s!"Tap target creature. Scry {s}.",
      if d == 1 then "Draw a card." else s!"Draw {d} cards."]
  | .seq #[
      .moveZone (.target 0) (.hand .owner) .returnToHand _,
      .player (.drawCards .you (.const 1))
    ] =>
    if e.targetSpec == .spell then
      ["Return target spell to its owner's hand.", "Draw a card."]
    else fallback
  | .seq #[
      .player (.drawCards .you (.const 1)),
      .life (.lose .you (.const 1)),
      .player (.amass .you subtype (.const n))
    ] =>
    ["You draw a card and lose 1 life.", s!"Amass {pluralizeName subtype.englishName} {n.toNat}."]
  | .seq #[
      .moveZone (.target 0) (.hand .controller) .returnToHand _,
      .player (.amass .you subtype (.const n))
    ] =>
    ["Return up to one target creature card from your graveyard to your hand.",
      s!"Amass {pluralizeName subtype.englishName} {n.toNat}."]
  | .seq #[
      .damage (.deal .this (.objects (.inZones .battlefield (.all #[.hasType .creature, .not (.hasSubtype (.literal sub))]))) (.const n) _),
      .player (.addMana .you { spec := .combination .anyColor (.const m), restriction := some (.onlyForSpells (.hasSubtype sub2) _), .. })
    ] =>
    [s!"{cardName} deals {n.toNat} damage to each non-{sub} creature.",
      s!"Add {englishNumber m.toNat} mana in any combination of colors. Spend this mana only to cast {sub2} spells."]
  | .seq #[
      .installEffect (.applyContinuous .untilEndOfTurn (.target 0) (.grantKeywords k)),
      .installEffect (.applyContinuous .untilEndOfTurn (.target 0) (.applyRule (.combat (.cantBeBlocked .self)))),
      .player (.drawCards .you (.const 1))
    ] =>
    if k == #[Keyword.vigilance] then
      ["Target creature gains vigilance until end of turn and can't be blocked this turn.",
        "Draw a card."]
    else fallback
  | .installEffect (.applyContinuous .untilEndOfTurn (.target 0)
      (.all #[
        .modifyTypes { types := #[.artifact, .creature], .. },
        .setBasePT (some (.const p)) (some (.const t)),
        .grantKeywords #[kw]
      ])) =>
    [s!"Until end of turn, target artifact or creature becomes an artifact creature with base power and toughness {p}/{t} and gains {KeywordAbility.toOracleStr {} kw}.",
      "Draw a card."]
  | _ => fallback

inductive ParsedAbility where
  | static (ab : StaticAbility)
  | triggered (ab : TriggeredAbility)
  | activated (ab : ActivatedAbility)
  | spell (e : Effect)
  | modes (es : Array Effect) (oneOrBoth : Bool) (teamwork : Bool) (twoIf : Option String)
deriving Repr

def applyParsed (c : CardDef) (ab : ParsedAbility) : CardDef :=
  match ab with
  | .static ab => { c with staticAbilities := c.staticAbilities.push ab }
  | .triggered ab => { c with triggeredAbilities := c.triggeredAbilities.push ab }
  | .activated ab => { c with activatedAbilities := c.activatedAbilities.push ab }
  | .spell e => { c with spellEffect := some e }
  | .modes es oneOrBoth teamwork twoIf =>
    let altCountIf? : Option (Condition × ValueExpr × ValueExpr) :=
      if teamwork then
        some (.castPred (.teamworkPaid .this), .const 2, .const 2)
      else
        match twoIf.bind CardSubtype.ofOracle? with
        | some sub =>
          some (.playerPred .you (.controls { zones := .battlefield, pred := .hasSubtype (.literal sub) } (.const 1)),
            .const 1, .const 2)
        | none => none
    let ms : ModalSpec := {
      minModes := .const 1
      maxModes := if oneOrBoth then .const 2 else .const 1
      altCountIf?
      modes := es
    }
    { c with spellEffect := some { body := .chooseModes ms } }

def splitCreatureTypes (s : String) : Array String :=
  let s := s.replace ", or " ", " |>.replace " or " ", "
  (s.splitOn "," |>.map (·.trimAscii.copy) |>.filter (· != "")).toArray

/-- `{2}{G}{U}, {T}, Sacrifice this land: Put two +1/+1 counters on target Elf you control.` -/
def parseSacrificeCounters (line : String) : Option ActivatedAbility :=
  let raw := (stripParentheticals line).trimAscii.copy
  let low := lowerAscii raw
  if !(low.contains "sacrifice this") || !(low.contains "+1/+1 counters on target") then none
  else
    let costText := ((raw.splitOn ":").headD "").splitOn "," |>.headD "" |>.trimAscii.copy
    match parseManaCost costText with
    | none => none
    | some cost =>
      let n :=
        if low.contains "put two " || low.contains "put 2 " then 2 else 1
      let typesText :=
        ((raw.splitOn "on target ").getLastD "").splitOn " you control" |>.headD "" |>.trimAscii.copy
      let types := splitCreatureTypes typesText
      if types.isEmpty then none
      else
        some (activated (Effect.plusOneOnTarget n types) cost
          (tap := low.contains "{t}")
          (sacrificeSource := true)
          (timing := if low.contains "only as a sorcery" then .sorcery else .instant))

/-- `Equip {2}`, `Equip Wizard {1}`, `Equip worthy {1}`, `Equip—{2}, Pay 2 life`. -/
def parseEquipLine (line : String) : Option ActivatedAbility :=
  let raw := (stripParentheticals line).trimAscii.copy
  let low := lowerAscii raw
  if !(low.startsWith "equip") then none
  else
    let payLife :=
      if low.contains "pay " && low.contains "life" then
        match (low.splitOn "pay ").getLastD "" |>.takeWhile Char.isDigit with
        | "" => 0
        | d => d.toNat!
      else 0
    let head :=
      if raw.contains ',' then (raw.splitOn ",").headD raw |>.trimAscii.copy else raw
    let afterEquip := (head.drop "Equip".length).trimAscii.copy
    let afterEquip :=
      if afterEquip.startsWith "—" || afterEquip.startsWith "-" then
        (afterEquip.drop 1).trimAscii.copy
      else afterEquip
    let worthy := (lowerAscii afterEquip).startsWith "worthy"
    let costAndType :=
      if worthy then (afterEquip.drop "worthy".length).trimAscii.copy else afterEquip
    let (subtype, cost?) :=
      match parseManaCost costAndType with
      | some cost => (none, some cost)
      | none =>
        match splitNameCost costAndType with
        | (name, some cost) => (CardSubtype.ofOracle? name, some cost)
        | _ => (none, none)
    match cost? with
    | none => none
    | some cost =>
      let equipPred? : Option ObjectPred :=
        if worthy then some ObjectPred.worthy
        else subtype.map fun s => .hasSubtype (.literal s)
      some (activated (Effect.equipEffect subtype worthy) cost
        (timing := .sorcery) (tag? := some (.equip equipPred?)) (payLife := payLife))

/-- Structural rules (keywords, additional costs, Stage-4 static/cost/ETB/replacement
abilities, Sagas, Equip, and mana abilities). -/
def parseStructural (c : CardDef) (line : String) : Option CardDef :=
  -- CR 207.2a: reminder text is not part of the ability being parsed.
  let raw := dropReminderText line
  let low := lowerAscii raw
  if low.contains "sacrifice this land" && low.contains "create x treasure tokens" then
    let head := (raw.splitOn ",").headD "" |>.trimAscii.copy
    match parseManaCost head with
    | some cost =>
      let ab :=
        activated (Effect.abilityCreateTokensX .treasure) cost
          (tap := low.contains "{t}") (sacrificeSource := true)
      some { c with activatedAbilities := c.activatedAbilities.push ab }
    | none => none
  else if low.startsWith "affinity for " then
    Parser.parseKeywordAbility raw |>.map c.withKeyword
  else if low.contains "cascade" &&
      (((low.replace "," "").splitOn " ").filter (fun w => w != "")).all (fun w => w == "cascade") then
    let n := (low.splitOn "cascade").length - 1
    some (c.withKeywords (Array.replicate n Keyword.cascade))
  else if low.startsWith "kicker " || low.startsWith "kicker—" then
    Parser.parseKeywordAbility raw |>.map c.withKeyword
  else if low.startsWith "gift " then
    Parser.parseKeywordAbility raw |>.map c.withKeyword
  else if low.startsWith "teamwork " then
    Parser.parseKeywordAbility raw |>.map c.withKeyword
  else if low.startsWith "as an additional cost to cast this spell," then
    Parser.parseAdditionalCostSpec raw |>.map fun spec =>
      { c with additionalCosts := c.additionalCosts.push spec }
  else if low.startsWith "ward " || low.startsWith "ward—" || low.startsWith "ward{" then
    let normWard := if low.startsWith "ward{" then "Ward " ++ (raw.drop 4).copy else raw
    Parser.parseKeywordAbility normWard |>.map c.withKeyword
  else if low.startsWith "flashback—" || low.startsWith "flashback " then
    Parser.parseKeywordAbility raw |>.map c.withKeyword
  else if low.startsWith "crew " then
    Parser.parseKeywordAbility raw |>.map c.withKeyword
  else if low.startsWith "toxic " then
    Parser.parseKeywordAbility raw |>.map c.withKeyword
  else if low.startsWith "a deck can have any number of cards named" then
    some { c with anyNumberInDeck := true }
  else if low.contains "sacrifice after" && low.contains "lore counter" then
    -- CR 207.2a / 714.2d: Saga reminder text is ignored; final chapter is computed from chapter triggers.
    some c
  else if low.startsWith "when that mana is spent to cast a creature spell that shares a creature type with your commander, scry " then
    let nStr := ((low.drop "when that mana is spent to cast a creature spell that shares a creature type with your commander, scry ".length).takeWhile Char.isDigit).copy
    let n := if nStr.isEmpty then 1 else nStr.toNat!
    some { c with triggeredAbilities := c.triggeredAbilities.push (TriggeredAbility.onManaSpentCastCommanderTypeScry n) }
  else
    let staticRaw :=
      if low.startsWith "eminence —" || low.startsWith "eminence—" then raw
      else stripAbilityWord raw
    match Parser.parseStaticAbilityLine staticRaw c.name with
    | some abs => some { c with staticAbilities := c.staticAbilities ++ abs }
    | none =>
    match parseSacrificeCounters raw with
    | some ab => some { c with activatedAbilities := c.activatedAbilities.push ab }
    | none =>
    match parseEquipLine raw with
    | some ab => some { c with activatedAbilities := c.activatedAbilities.push ab }
    | none =>
      match Parser.parseManaAbilityLine raw c.name with
      | some ab =>
        -- CR 305.6: basic land types intrinsically grant `{T}: Add {M}`; do not
        -- duplicate that ability in `activatedAbilities`.
        let isIntrinsicBasic :=
          c.isLand && ab.cost == CostSpec.tapOnly && ab.condition?.isNone &&
            ab.turnLimit?.isNone && ab.lifetimeLimit?.isNone &&
            match ab.manaProduction? with
            | some mp =>
              mp.restriction.isNone && mp.riders.isEmpty && mp.damageYou == 0 &&
                match mp.spec with
                | .sequence #[(.colored col, .const 1)] => c.basicLandMana.contains col
                | _ => false
            | none => false
        if isIntrinsicBasic then some c
        else
          let trigAbs :=
            if low.contains "in your commander's color identity" && low.contains "scry" &&
                !c.triggeredAbilities.any (·.isManaSpentCastScry) then
              c.triggeredAbilities.push (TriggeredAbility.onManaSpentCastCommanderTypeScry 1)
            else c.triggeredAbilities
          some { c with
            activatedAbilities := c.activatedAbilities.push ab
            triggeredAbilities := trigAbs }
      | none => none

def skipLine (c : CardDef) (line : String) : Bool :=
  let n := normalizeUnit c.name line
  n.isEmpty || n == "enchant creature" ||
    (c.isLand && c.basicLandMana.any fun col =>
      n == s!"\{t} add \{{lowerAscii col.letter}}")

def matchArgLines (pats : List (List Pat)) (norms : List String) (vals : Array SlotVal) :
    Option (Array SlotVal) :=
  let rec go (pats : List (List Pat)) (norms : List String) (vals : Array SlotVal)
      (seen : List Nat) : Option (Array SlotVal) :=
    match pats with
    | [] => some vals
    | p :: ps =>
      match norms with
      | [] => none
      | line :: rest =>
        match matchPatsSeen p (tokenize line) vals seen with
        | some (vals, seen) => go ps rest vals seen
        | none => none
  go pats norms vals []

/-- Name used when indexing printed abilities. `normalizeUnit` rewrites it to `this`,
the same way a real card name is rewritten. -/
private def indexName : String := "CARDNAME"

/-- A chapter or one-line spell effect with its printed line, normal forms, and
argument holes, prepared once for every card that does not name it. -/
structure EffectProto where
  line : NormLine
  effect : Effect
  args : Array SlotVal
  unitPats : List Pat
  structPats : List Pat

def EffectProto.of (line : String) (e : Effect) : EffectProto :=
  let line := NormLine.of line
  let args := collectEffect e
  { line, effect := e, args
    unitPats := patsOf line.unit args
    structPats := patsOf line.structural args }

/-- One Oracle line normalized for the card being parsed. -/
structure EffectQuery where
  cardName : String
  /-- `nameKeys cardName`. -/
  keys : List String
  unit : String
  unitToks : List String
  structToks : List String

def EffectQuery.of (cardName text : String) : EffectQuery :=
  let unit := normalizeUnit cardName text
  { cardName, keys := nameKeys cardName, unit
    unitToks := tokenize unit
    structToks := tokenize (normalizeStructural cardName text) }

/-- `normalizeUnit` of the prototype line equals `normalizeUnit` of the query. -/
def EffectProto.sameText (p : EffectProto) (q : EffectQuery) : Bool :=
  p.line.unitFor q.cardName q.keys == q.unit

/-- Parse `Nat` / `Int` / `String` holes in the prototype line from the query
and rebuild the effect. -/
def EffectProto.matchText (p : EffectProto) (q : EffectQuery) : Option Effect :=
  let named := mentionsNameKey q.keys p.line.base
  let unitPats :=
    if named then patsOf (normalizeUnit q.cardName p.line.raw) p.args else p.unitPats
  let structPats (_ : Unit) :=
    if named then patsOf (normalizeStructural q.cardName p.line.raw) p.args else p.structPats
  let found := (matchPats unitPats q.unitToks p.args).orElse fun _ =>
    matchPats (structPats ()) q.structToks p.args
  found.map fun vals => if vals == p.args then p.effect else refillEffect p.effect vals

@[irreducible, noinline] def chapterProtos : Thunk (Array EffectProto) :=
  Thunk.mk fun _ => chapterEffects.get.map fun (stored, e) => EffectProto.of stored e

/-- A spell effect as a chapter or mode candidate. `fixed` is its one printed
line when that line never includes the card's name; `effectLines` is
recomputed for the card otherwise. -/
structure SpellProto where
  effect : Effect
  fixed : Option EffectProto
  namesCard : Bool

@[irreducible, noinline] def spellProtos : Thunk (Array SpellProto) :=
  Thunk.mk fun _ => spellEffects.get.map fun e =>
    let lines := effectLines indexName e
    let namesCard := lines.any (·.contains indexName)
    let fixed := match lines with
      | [line] => if namesCard then none else some (EffectProto.of line e)
      | _ => none
    { effect := e, fixed, namesCard }

/-- The one-line prototype of a spell effect on this card, if it has one line. -/
def SpellProto.forCard (p : SpellProto) (cardName : String) : Option EffectProto :=
  if p.namesCard then
    match effectLines cardName p.effect with
    | [line] => some (EffectProto.of line p.effect)
    | _ => none
  else p.fixed

/-- Stored text of the first chapter whose printed line reads as `text`. -/
def chapterStoredText (cardName text : String) : Option String :=
  let q := EffectQuery.of cardName text
  chapterProtos.get.find? (·.sameText q) |>.map (·.line.raw)

/-- First spell prototype whose printed line matches `text`. -/
def firstSpellProto (cardName : String) (f : EffectProto → Option Effect) : Option Effect :=
  spellProtos.get.foldl (fun acc p =>
    match acc with
    | some _ => acc
    | none => (p.forCard cardName).bind f) none

/-- The two clauses of one “, then” sentence, when there is exactly one. -/
def splitOnThen (s : String) : Option (String × String) :=
  match s.splitOn ", then " with
  | [a, b] =>
    let a := a.trimAscii.copy
    let b := b.trimAscii.copy
    if a.isEmpty || b.isEmpty then none else some (a, b)
  | _ => none

/-- Flatten nested `Instruction.seq` steps while preserving order. -/
def instrSteps : Instruction → Array Instruction
  | .seq xs => xs.attach.foldl (fun acc ⟨x, _⟩ => acc ++ instrSteps x) #[]
  | .noop => #[]
  | x => #[x]

/-- Combine instructions into a flat sequence (`.noop` for empty, bare step for singleton). -/
def joinInstructions (xs : List Instruction) : Instruction :=
  let flat := xs.foldl (fun acc x => acc ++ instrSteps x) #[]
  match flat.toList with
  | [] => .noop
  | [x] => x
  | _ => .seq flat

/-- One effect whose steps are `es`, phrased with “, then” between them. -/
def joinThenEffects (es : List Effect) : Effect :=
  match es with
  | [] => {}
  | [e] => e
  | _ =>
    let targeted := es.find? (·.requiresTarget) |>.getD es.head!
    { targeted with
      body := joinInstructions (es.map (·.body))
      resolution? := none
      phrase := String.intercalate ", then " (es.map (·.phrase)) }

/-- First spell prototype that matches `text` and whose instruction passes `ok`.
An earlier prototype can share the printed words and name a different effect
(`Draw two cards` is also the legendary-discard ability). -/
def matchSpellProtoSuchThat (cardName text : String) (ok : Instruction → Bool) : Option Effect :=
  let q := EffectQuery.of cardName text
  spellProtos.get.foldl (fun acc p =>
    match acc with
    | some _ => acc
    | none =>
      match p.forCard cardName with
      | none => none
      | some proto =>
        let matched :=
          if proto.sameText q then some proto.effect else proto.matchText q
        match matched with
        | some e => if ok e.body then some e else none
        | none => none) none

/-- “Draw N cards, then discard a card”, from the `draw` and `discardCards`
prototypes. The discard stays the last step, so its pending choice does not
block a later step. A line that is already one prototype is not split. -/
def matchDrawThenDiscard (cardName text : String) : Option Effect :=
  match splitOnThen text with
  | none => none
  | some (drawText, discardText) =>
    match matchSpellProtoSuchThat cardName drawText (fun i =>
        match i with | .player (.drawCards ..) => true | _ => false),
      matchSpellProtoSuchThat cardName discardText (fun i =>
        match i with | .moveZone _ .graveyard .discard _ => true | _ => false) with
    | some drawE, some discardE => some (joinThenEffects [drawE, discardE])
    | _, _ => none

def matchChapter (cardName text : String) : Option Effect :=
  let q := EffectQuery.of cardName text
  match chapterProtos.get.find? (·.sameText q) with
  | some p => some p.effect
  | none =>
    match chapterProtos.get.findSome? (·.matchText q) with
    | some e => some e
    | none =>
      match firstSpellProto cardName fun p => if p.sameText q then some p.effect else none with
      | some e => some e
      | none =>
        match firstSpellProto cardName (·.matchText q) with
        | some e => some e
        | none => matchDrawThenDiscard cardName text

/-- A mode of a modal triggered ability: a spell or ability effect, else a
Saga chapter effect. -/
def matchTriggerMode (cardName text : String) : Option Effect :=
  let q := EffectQuery.of cardName text
  let firstSpell (f : EffectProto → Option Effect) : Option Effect :=
    spellProtos.get.foldl (fun acc p =>
      match acc with
      | some _ => acc
      | none => (p.forCard cardName).bind f) none
  match firstSpell fun p => if p.sameText q then some p.effect else none with
  | some e => some e
  | none =>
    match firstSpell (·.matchText q) with
    | some e => some e
    | none => matchChapter cardName text

/-- A modal triggered ability (“When/Whenever/At …, choose one/two — • …”),
storing its modes inside `effect.body` as `Instruction.chooseModes` (CR 603.3c / 700.2). -/
def parseTriggerModes (cardName line : String) : Option TriggeredAbility :=
  let raw := line.trimAscii.copy
  let low := lowerAscii raw
  let header := ((raw.splitOn "•").headD "").trimAscii.copy
  let lowHeader := lowerAscii header
  let named := collapseWs (prepareLine cardName header)
  let count :=
    if lowHeader.endsWith "choose one —" then some 1
    else if lowHeader.endsWith "choose two —" then some 2
    else none
  match count with
  | none => none
  | some n =>
    let modes := (raw.splitOn "•").drop 1 |>.map (·.trimAscii.copy) |>.filter (· != "")
    let effects := modes.filterMap fun m => matchTriggerMode cardName (stripAbilityWord m)
    if modes.isEmpty || effects.length != modes.length then none
    else
      let headerPhrase := if n == 2 then "choose two" else "choose one"
      let nExpr : ValueExpr := .const (Int.ofNat n)
      if low.startsWith "when " && named.startsWith "when this enters, choose" then
        some (TriggeredAbility.mkModal .thisEnters effects.toArray
          (word? := some .when) (headerPhrase := headerPhrase)
          (minModes := nExpr) (maxModes := nExpr))
      else
        match Parser.parseTriggerClause header cardName with
        | some hdr =>
          some (TriggeredAbility.mkModal hdr.pattern effects.toArray
            (word? := some hdr.word) (grouping := hdr.grouping)
            (interveningIf? := hdr.interveningIf?) (activeZones := hdr.activeZones)
            (limit := hdr.limit) (headerPhrase := headerPhrase)
            (minModes := nExpr) (maxModes := nExpr))
        | none => none

def parseModes (cardName line : String) : Option ParsedAbility :=
  let raw := line.trimAscii.copy
  let low := lowerAscii raw
  if !(low.contains "choose one") then none
  else if low.startsWith "when " || low.startsWith "whenever " then none
  else if raw.contains "{" && ((raw.splitOn "Choose").headD "").contains "{" then none
  else
    let bullets := raw.splitOn "•" |>.map (·.trimAscii.copy) |>.filter (· != "")
    match bullets with
    | [] => none
    | header :: modes =>
      if modes.isEmpty then none
      else
        let effects := modes.filterMap fun m =>
          let m := stripAbilityWord m
          matchChapter cardName m
        if effects.length != modes.length then none
        else
          let oneOrBoth := low.contains "choose one or both"
          let teamwork := low.contains "using teamwork"
          let twoIf :=
            if low.contains "you may choose two instead" then
              let after :=
                if header.contains "you control a " then
                  (header.splitOn "you control a ").getLastD ""
                else if header.contains "you control an " then
                  (header.splitOn "you control an ").getLastD ""
                else ""
              let t := ((after.splitOn " ").headD "" |>.replace "," "").trimAscii.copy
              if t.isEmpty then none else some t
            else none
          some (.modes effects.toArray oneOrBoth teamwork twoIf)

/-- Lowercase, strip reminders and punctuation, keep the card name. Used to
prefer a literal printed match over a phrase-equivalent one. -/
def lightLine (s : String) : String :=
  collapseWs (keepSignificant (replaceNumberWords (lowerAscii
    (stripAbilityWord (stripChaosSymbol (dropReminderText s))))))

def abilityLines (cardName : String) (ab : ParsedAbility) : List String :=
  match ab with
  | .static a => [StaticAbility.toNotation a]
  | .triggered a =>
    (TriggeredAbility.toNotation a).splitOn "\n" |>.map (·.trimAscii.copy) |>.filter (· != "")
  | .activated a => [printedActivated a]
  | .spell e => effectLines cardName e
  | .modes .. => []

structure IndexedAbility where
  ability : ParsedAbility
  raw : List String
  norm : List String
  light : List String
  priority : Nat
  /-- Position in the catalog. On a score tie, the earlier entry wins. -/
  order : Nat
  args : Array SlotVal
  /-- Holes learned from `normalizeUnit`. -/
  pats : List (List Pat)
  /-- Holes learned before phrase equivalences, so open subtypes stay words. -/
  structPats : List (List Pat)
  /-- `raw` is `abilityLines` of `ability` and does not include `indexName`, so
  those are the ability's lines on every card and `light` is their light form. -/
  ownLines : Bool
  /-- `raw` joined and lowercased, to look for the card's name. -/
  rawLower : String

def collectParsed (ab : ParsedAbility) : Array SlotVal :=
  match ab with
  | .static a => collectStatic a
  | .triggered a => collectTriggered a
  | .activated a => collectActivated a
  | .spell e => collectEffect e
  | .modes .. => #[]

def indexItem (priority order : Nat) (ability : ParsedAbility) (lines : List String) : IndexedAbility :=
  let args := collectParsed ability
  let norm := lines.map (normalizeUnit indexName)
  let structNorm := lines.map (normalizeStructural indexName)
  { ability
    raw := lines
    norm
    light := lines.map lightLine
    priority
    order
    args
    pats := patsOfLines norm args
    structPats := patsOfLines structNorm args
    ownLines := !lines.any (·.contains indexName) && lines == abilityLines indexName ability
    rawLower := lowerAscii (String.intercalate "\n" lines) }

def refillParsed (ab : ParsedAbility) (vals : Array SlotVal) : ParsedAbility :=
  match ab with
  | .static a => .static (refillStatic a vals)
  | .triggered a => .triggered (refillTriggered a vals)
  | .activated a => .activated (refillActivated a vals)
  | .spell e => .spell (refillEffect e vals)
  | .modes es oneOrBoth teamwork twoIf => .modes es oneOrBoth teamwork twoIf

def parsedEq (a b : ParsedAbility) : Bool :=
  match a, b with
  | .static x, .static y => x == y
  | .triggered x, .triggered y => x == y
  | .activated x, .activated y => x == y
  | .spell x, .spell y => x == y
  | .modes es1 a1 b1 c1, .modes es2 a2 b2 c2 =>
    es1 == es2 && a1 == a2 && b1 == b2 && c1 == c2
  | _, _ => false

/-- True when `a` and `b` are the same ability with different argument values. -/
def sameArgShape (a b : IndexedAbility) : Bool :=
  a.priority == b.priority &&
    patKey a.pats == patKey b.pats &&
    patKey a.structPats == patKey b.structPats &&
    a.args.size == b.args.size &&
    parsedEq (refillParsed a.ability b.args) b.ability &&
    parsedEq (refillParsed b.ability a.args) a.ability

def shapeGroup (item : IndexedAbility) : String :=
  s!"{item.priority}|{patKey item.pats}|{patKey item.structPats}"

def insertUnique (out : Array IndexedAbility) (groups : Std.HashMap String (Array Nat))
    (item : IndexedAbility) : Array IndexedAbility × Std.HashMap String (Array Nat) :=
  let key := shapeGroup item
  let prevs := groups.getD key #[]
  let dup := prevs.any fun j =>
    match out[j]? with
    | some prev => sameArgShape prev item
    | none => false
  if dup then (out, groups)
  else (out.push item, groups.insert key (prevs.push out.size))

/-- First word, so `other Goblin creatures` still finds the `Elf` prototype. -/
def headWord (s : String) : String :=
  tokenize s |>.headD ""

/-- First token abstracted, so `Forestcycling {2}` finds `Mountaincycling {2}`. -/
def wildcardHead (s : String) : String :=
  match tokenize s with
  | [] => ""
  | t :: rest =>
    let t := if t.endsWith "cycling" then "$cycling" else "$"
    String.intercalate " " (t :: rest)

/-- Collapse a leading typecycling span, including `Basic landcycling` and
`Time Lordcycling`, so every cycling line of the same cost shares a key. -/
def abstractCyclingLine (s : String) : Option String :=
  let rec go (ts : List String) : Option (List String) :=
    match ts with
    | [] => none
    | t :: rest =>
      if t.endsWith "cycling" && t.length > "cycling".length then
        some ("$cycling" :: rest)
      else go rest
  (go (tokenize s)).map fun ts => String.intercalate " " ts

/-- Collapse a leading subtype (singular, plural, `non-`, or cycling) so
`Time Lords you control` finds `Elves you control`. -/
def abstractSubtypeLine (s : String) : Option String :=
  let toks := tokenize s
  let span? : Option Nat :=
    match matchCyclingSubtype toks with
    | some (_name, n) => some n
    | none =>
      match matchNonSubtype toks with
      | some (_name, n) => some n
      | none =>
        match matchSubtypeForm true toks with
        | some (_name, n) => some n
        | none =>
          match matchSubtypeForm false toks with
          | some (_name, n) => some n
          | none => none
  span?.map fun n => String.intercalate " " ("$sub" :: toks.drop n)

/-- Normalized lines, recomputed when the printed text contains this card's name.
`keys` is `nameKeys cardName`. -/
def candidateNorm (cardName : String) (keys : List String) (item : IndexedAbility) :
    List String :=
  if mentionsNameKey keys item.rawLower then item.raw.map (normalizeUnit cardName) else item.norm

/-- One prototype per shape. Later entries that differ only by `Nat`, `Int`,
`String`, or target-kind arguments are dropped. -/
@[irreducible, noinline] def indexedAbilities : Thunk (Array IndexedAbility) :=
  Thunk.mk fun _ => Id.run do
  let mut out : Array IndexedAbility := #[]
  let mut groups : Std.HashMap String (Array Nat) := {}
  let mut order : Nat := 0
  for e in spellEffects.get do
    let stepped := insertUnique out groups (indexItem 1 order (.spell e) (effectLines indexName e))
    out := stepped.1
    groups := stepped.2
    order := order + 1
  for ab in staticAbilities.get do
    let stepped := insertUnique out groups (indexItem 2 order (.static ab) [StaticAbility.toNotation ab])
    out := stepped.1
    groups := stepped.2
    order := order + 1
  for ab in triggeredAbilities.get do
    let lines := (TriggeredAbility.toNotation ab).splitOn "\n"
      |>.map (·.trimAscii.copy) |>.filter (· != "")
    let stepped := insertUnique out groups (indexItem 3 order (.triggered ab) lines)
    out := stepped.1
    groups := stepped.2
    order := order + 1
  for ab in activatedAbilities.get do
    let stepped := insertUnique out groups (indexItem 4 order (.activated ab) [printedActivated ab])
    out := stepped.1
    groups := stepped.2
    order := order + 1
  out

def pushBucket (m : Std.HashMap String (Array Nat)) (key : String) (i : Nat) :
    Std.HashMap String (Array Nat) :=
  if key.isEmpty then m else m.insert key ((m.getD key #[]).push i)

/-- First-line index so a rules line does not scan every modeled ability. -/
@[irreducible, noinline] def abilityBuckets : Thunk (Std.HashMap String (Array Nat)) :=
  Thunk.mk fun _ => Id.run do
  let mut m : Std.HashMap String (Array Nat) := {}
  let mut i : Nat := 0
  let addOpt (m : Std.HashMap String (Array Nat)) (k : Option String) (i : Nat) :=
    match k with
    | none => m
    | some k =>
      let m := pushBucket m k i
      (lineKeys k).foldl (fun m sk => pushBucket m sk i) m
  let addKeys (m : Std.HashMap String (Array Nat)) (k : String) (i : Nat) :=
    let m := pushBucket m k i
    let m := (lineKeys k).foldl (fun m sk => pushBucket m sk i) m
    let m := pushBucket m (headWord k) i
    let m := (lineKeys (wildcardHead k)).foldl (fun m sk => pushBucket m sk i) m
    let m := addOpt m (abstractCyclingLine k) i
    let m := addOpt m (abstractSubtypeLine k) i
    addOpt m (abstractCounterLine k) i
  for item in indexedAbilities.get do
    match item.light.head? with
    | some k => m := addKeys m k i
    | none => pure ()
    match item.norm.head? with
    | some k => m := addKeys m k i
    | none => pure ()
    match item.raw.head?.map (normalizeStructural indexName) with
    | some k => m := addKeys m k i
    | none => pure ()
    i := i + 1
  return m

/-- Bucket keys for a rules line, given its `lightLine`, `normalizeUnit`, and
`normalizeStructural` forms and the card's `nameKeys`. -/
def lookupKeys (keys : List String) (lit norm struct : String) : List String :=
  let aliased := keys.foldl (fun acc a => acc.replace a (lowerAscii indexName)) lit
  let base := [lit, aliased, norm, struct].foldl (fun acc k =>
    if k.isEmpty || acc.any (· == k) then acc else acc ++ [k]) []
  let wild := (base.map wildcardHead).flatMap lineKeys
  let extra :=
    (base.filterMap abstractCyclingLine) ++
    (base.filterMap abstractSubtypeLine) ++
    (base.filterMap abstractCounterLine) ++
    ((base.filterMap abstractCyclingLine).flatMap lineKeys) ++
    ((base.filterMap abstractSubtypeLine).flatMap lineKeys) ++
    ((base.filterMap abstractCounterLine).flatMap lineKeys)
  (base ++ base.flatMap lineKeys ++ base.map headWord ++ wild ++ extra).foldl
    (fun acc k => if k.isEmpty || acc.any (· == k) then acc else acc ++ [k]) []

/-- Indexed abilities filed under any lookup key of the first rules line, in
key order without repeats. -/
def candidatesFor (keys : List String) (lit norm struct : String) : Array IndexedAbility :=
  let (_, out) := (lookupKeys keys lit norm struct).foldl (fun (seen, out) k =>
    ((abilityBuckets.get).getD k #[]).foldl (fun (seen, out) i =>
      if seen.contains i then (seen, out)
      else
        match (indexedAbilities.get)[i]? with
        | some item => (seen.insert i, out.push item)
        | none => (seen.insert i, out)) (seen, out))
    ((∅ : Std.HashSet Nat), (#[] : Array IndexedAbility))
  out

def listPrefix (pre rest : List String) : Bool :=
  match pre, rest with
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a == b && listPrefix as bs

def adaptLight (cardName : String) (lines : List String) : List String :=
  -- `light` is already lowercased, so the sentinel is `cardname`.
  lines.map fun s => applyReplacements s [(lowerAscii indexName, lowerAscii cardName)]

def coversLight (cardName : String) (ab : ParsedAbility) (lights : List String) : Bool :=
  let lines := (abilityLines cardName ab).map lightLine
  !lines.isEmpty && lines.length <= lights.length && listPrefix lines lights

/-- `coversLight` of the candidate's ability, or of `filled` when arguments were
read from the card. -/
def IndexedAbility.coversLight (item : IndexedAbility) (cardName : String)
    (filled : Option ParsedAbility) (lights : List String) : Bool :=
  match filled with
  | none =>
    if item.ownLines then
      !item.light.isEmpty && item.light.length <= lights.length && listPrefix item.light lights
    else Mtg.Engine.coversLight cardName item.ability lights
  | some ab => Mtg.Engine.coversLight cardName ab lights

def filledAbility (item : IndexedAbility) (norms structNorms : List String) : Option ParsedAbility :=
  let attempt (pats : List (List Pat)) (lines : List String) : Option ParsedAbility :=
    if pats.isEmpty || pats.length > lines.length then none
    else
      match matchArgLines pats lines item.args with
      | none => none
      | some vals =>
        some (if vals == item.args then item.ability else refillParsed item.ability vals)
  (attempt item.pats norms).orElse (fun _ => attempt item.structPats structNorms)

/-- Best modeled ability whose printed lines match `units` at the front.
A literal wording match beats a match that only appears after phrase normalization.
Numeric and text arguments are read from `units` when the line has the same shape. -/
@[irreducible, noinline] def matchModeled (cardName : String) (units : List String) : Option (ParsedAbility × Nat) :=
  let norms := units.map (normalizeUnit cardName)
  let structNorms := units.map (normalizeStructural cardName)
  let lights := units.map lightLine
  let keys := nameKeys cardName
  let candidates :=
    match lights, norms, structNorms with
    | lit :: _, norm :: _, struct :: _ => candidatesFor keys lit norm struct
    | _, _, _ => #[]
  let best := candidates.foldl (fun acc item =>
    let printed := candidateNorm cardName keys item
    let n := printed.length
    let filled := filledAbility item norms structNorms
    let ability := filled.getD item.ability
    let literal : Nat :=
      if n == 0 || n > lights.length then 0
      else if listPrefix (adaptLight cardName item.light) lights ||
          item.coversLight cardName filled lights then 1 else 0
    let exact := n != 0 && n <= norms.length && listPrefix printed norms
    if n == 0 || n > norms.length || (literal == 0 && !exact && filled.isNone) then acc
    else
      match acc with
      | none => some (n, literal, item.priority, item.order, ability)
      | some (bn, bl, bp, bo, _) =>
        if n > bn || (n == bn && (literal > bl ||
            (literal == bl && (item.priority > bp || (item.priority == bp && item.order < bo))))) then
          some (n, literal, item.priority, item.order, ability)
        else acc) none
  best.map fun (n, _, _, _, ab) => (ab, n)

/-- Sentences of one Oracle line, split on a period that ends a sentence. -/
def oracleSentences (line : String) : List String :=
  ((line.splitOn ". ").map fun s =>
    let s := s.trimAscii.copy
    if s.endsWith "." then (s.dropEnd 1).trimAscii.copy else s).filter (· != "")

/-- One spell whose steps are `es` in printed order.
Targeting comes from the step that chooses a target. -/
def joinSpellEffects (es : List Effect) : Effect :=
  match es with
  | [] => {}
  | [e] => e
  | _ =>
    let targeted := es.find? (·.requiresTarget) |>.getD es.head!
    { targeted with
      body := joinInstructions (es.map (·.body))
      resolution? := none
      phrase := String.intercalate ". " (es.map (·.phrase)) }

/-- One sentence as a spell prototype, or as draw-then-discard. -/
def matchSpellSentence (cardName s : String) : Option Effect :=
  match matchModeled cardName [s] with
  | some (.spell e, 1) => some e
  | _ => matchDrawThenDiscard cardName s

/-- `line` is a sequence of spell effects, each sentence already in `spellEffects`,
or a single “draw N cards, then discard a card” sentence. -/
def spellSentenceSequence (cardName line : String) : Option Effect :=
  let sents := oracleSentences line
  let rec go : List String → Option (List Effect)
    | [] => some []
    | s :: rest =>
      match matchSpellSentence cardName s with
      | some e => (go rest).map (e :: ·)
      | none => none
  match sents with
  | [] => none
  | [s] => matchDrawThenDiscard cardName s
  | _ => (go sents).map joinSpellEffects

#guard matchChapter "Bear" "Draw two cards, then discard a card." ==
  some (Effect.drawThenDiscard 2)
#guard matchChapter "Bear" "Draw a card, then discard a card" ==
  some (Effect.drawThenDiscard 1)
#guard matchChapter "Bear" "Discard a card, then draw a card." == none
#guard matchChapter "Bear" (Effect.millThenDraw 3 1).phrase ==
  some (Effect.millThenDraw 3 1)
#guard matchChapter "Bear" Effect.searchTwoBasicsSplit.phrase ==
  some Effect.searchTwoBasicsSplit
#guard spellSentenceSequence "Bear" "Draw two cards, then discard a card." ==
  some (Effect.drawThenDiscard 2)
#guard spellSentenceSequence "Bear"
    "Draw two cards, then discard a card. You gain 3 life." ==
  some (joinSpellEffects [Effect.drawThenDiscard 2, Effect.gainLife 3])

/-- Append later spell lines to `e` when each of them is its own spell effect.
A second targeted step stays a separate ability. -/
partial def extendSpellSequence (cardName : String) (e : Effect) (rest : List String) :
    Effect × List String :=
  match matchModeled cardName rest with
  | some (.spell e2, n) =>
    if n == 0 || n > rest.length || (e.requiresTarget && e2.requiresTarget) then (e, rest)
    else extendSpellSequence cardName (joinSpellEffects [e, e2]) (rest.drop n)
  | _ => (e, rest)

/-- `Loyalty: N` (any case), the labeled form of the corner number. -/
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

/-- Printed loyalty of a planeswalker, and the rules lines that remain (CR 209.1).

The number is `Loyalty: N` or the bare number from the lower right corner.
It may sit before the rules text or after it. A non-planeswalker has no loyalty. -/
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

/-- `Defense: N` (any case), the labeled form of the corner number. -/
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

/-- Printed defense of a battle, and the rules lines that remain (CR 210.1).

The number is `Defense: N` or the bare number from the lower right corner.
It may sit before the rules text or after it. A non-battle has no defense. -/
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

/-- Assign bare corner numbers that labels did not already name.

A pair is hand then life. One number fills whichever corner is still open.
A lone number, when both corners are open, is not a modifier pair. -/
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

/-- Bare hand and life modifiers at the corners of `rules` (CR 211.1 / 212.1).

The hand modifier is the lower left and the life modifier is the lower right,
so a pair is hand then life. The pair may sit before the rules text or after
it, and one corner may sit before the text while the other sits after it. -/
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
(CR 211.1 / 212.1).

Each modifier is `+N`, `-N`, or `0`. Labels (`Hand: +1`, `Life: -2`,
`Hand modifier: +1`, and `Hand +1, Life +10`) may appear on any line. A bare
pair is two corner lines, or `+1 -2` on one line. A non-vanguard has neither. -/
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

/-- Sign of a loyalty symbol, then the text after it.
`some true` is `+`, `some false` is a minus, `none` is unsigned. -/
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

Accepts the rules form `[+N]:`, `[-N]:`, `[0]:`, `[+X]:`, `[-X]:` and the
same symbols without brackets (`+N:`, `−N:`, `0:`). The second component is
the ability text after the colon. -/
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

partial def parseRules (c : CardDef) (lines : List String)
    (_keepUnrecognized : Bool := false) : Except String CardDef :=
  -- CR 207.2a: drop reminder text before any rule is read. A reminder may be
  -- the whole line (basic-land mana, Saga progress, a keyword on its own line).
  -- CR 207.4: the chaos symbol to the left of a chaos ability has no rules
  -- meaning. Drop it before the line is read, as on Towashi.
  -- CR 207.2c: an ability word has no rules meaning. Drop every one before the
  -- line is matched, including a multi-word word and one inside a quote.
  let units :=
    mergeBulletLines
      (lines.map (fun line =>
          let base := stripChaosSymbol (dropReminderText line)
          let lowBase := lowerAscii base
          let keepMechanicPrefix :=
            (lowBase.startsWith "exhaust —" || lowBase.startsWith "exhaust—" ||
             lowBase.startsWith "boast —" || lowBase.startsWith "boast—") &&
              (Parser.parseManaAbilityLine base c.name).isSome
          if keepMechanicPrefix then base else stripAbilityWords base) |>.filter (· != ""))
      |>.flatMap splitKeywordWardLine
  let foldEmpower (c : CardDef) (empowerN? : Option Nat) : CardDef :=
    match empowerN? with
    | none => c
    | some n =>
      match c.spellEffect with
      | some e =>
        { c with spellEffect := some { e with body := joinInstructions [e.body, Instruction.empowerJace n] } }
      | none =>
        { c with spellEffect := some { body := Instruction.empowerJace n, phrase := "" } }
  let rec go (c : CardDef) (empowerN? : Option Nat) (units : List String) : Except String CardDef :=
    let unrecognized (c : CardDef) (line : String) : Except String CardDef :=
      .error s!"unrecognized Oracle line on {c.name}: {line}"
    match units with
    | [] => .ok (foldEmpower c empowerN?)
    | line :: rest =>
      -- A modal line keeps its Empower Jace on the mode that prints it.
      let modal := (lowerAscii line).contains "•"
      let (empowerN?, line) :=
        match if modal then none else spellEmpower line with
        | some (n, leftover) =>
          let amount := match empowerN? with | some k => k | none => n
          (some amount, leftover)
        | none => (empowerN?, line)
      if (line.trimAscii.copy).isEmpty then go c empowerN? rest
      else
      let units := line :: rest
      if skipLine c line then go c empowerN? rest
      else
        match beholdOrPay line with
        | some (sub, n) =>
          go { c with additionalCosts := c.additionalCosts.push (AdditionalCostSpec.mandatory (CostSpec.beholdOrPayGeneric sub n)) } empowerN? rest
        | none =>
        -- CR 606.2: a loyalty symbol in the cost makes this a loyalty ability.
        -- “Planeswalkers you control have "[−N]: …"”: a granted loyalty ability.
        let grantedPrefix := "planeswalkers you control have \""
        let granted? : Option ActivatedAbility :=
          if (lowerAscii line).startsWith grantedPrefix then
            let inner := ((line.drop grantedPrefix.length).trimAscii.copy)
            let inner :=
              if inner.endsWith "\"." then (inner.dropEnd 2).copy
              else if inner.endsWith "\"" then (inner.dropEnd 1).copy
              else inner
            match parseLoyaltyAbilityLine inner with
            | some (sym, effectText) =>
              match matchModeled c.name [effectText] with
              | some (.spell e, 1) => some (activated e (loyalty := some sym))
              | _ => none
            | none => none
          else none
        match granted? with
        | some ab =>
          go { c with staticAbilities := c.staticAbilities.push (StaticAbility.planeswalkersYouControlHave #[ab]) } empowerN? rest
        | none =>
        match parseLoyaltyAbilityLine line with
        | some (sym, effectText) =>
          let jaceSuffix :=
            " Activate only if there are twenty-five or more loyalty counters among Jaces you control."
          let (effectText, cond?) : String × Option Condition :=
            if effectText.endsWith jaceSuffix then
              ((effectText.dropEnd jaceSuffix.length).copy,
               some (ActivatedAbility.condJaceLoyaltyAtLeast 25))
            else (effectText, none)
          match matchModeled c.name (effectText :: rest) with
          | some (.spell e, n) =>
            let more := (effectText :: rest).drop n
            if n > 0 && more.length < (effectText :: rest).length then
              let (e, more) :=
                if n == 1 then extendSpellSequence c.name e more else (e, more)
              let ab : ActivatedAbility := activated e (loyalty := some sym) (condition? := cond?)
              go { c with activatedAbilities := c.activatedAbilities.push ab } empowerN? more
            else unrecognized c line
          | _ =>
            match spellSentenceSequence c.name effectText with
            | some e =>
              let ab : ActivatedAbility := activated e (loyalty := some sym) (condition? := cond?)
              go { c with activatedAbilities := c.activatedAbilities.push ab } empowerN? rest
            | none =>
              match parseFrcLoyaltyEffect effectText with
              | some e =>
                let ab : ActivatedAbility := activated e (loyalty := some sym) (condition? := cond?)
                go { c with activatedAbilities := c.activatedAbilities.push ab } empowerN? rest
              | none => unrecognized c line
        | none =>
        if isCantBeBlockedLine c.name line then
          go { c with staticAbilities := c.staticAbilities.push .cantBeBlocked } empowerN? rest
        else
        match keywordLineAbilities c.name line with
        | some kws =>
          go (c.withKeywords kws) empowerN? rest
        | none =>
          match parseChapterHeader line with
          | some (roman, text) =>
            let printed := (chapterStoredText c.name text).getD text
            match matchChapter c.name text with
            | some e =>
              let ab := TriggeredAbility.sagaChapters (parseChapterNumbers roman) { e with phrase := printed }
              go { c with triggeredAbilities := c.triggeredAbilities.push ab } empowerN? rest
            | none =>
              .error s!"unrecognized chapter on {c.name}: {line}"
          | none =>
            match parseStructural c line with
            | some c => go c empowerN? rest
            | none =>
              match parseTriggerModes c.name line with
              | some ab =>
                go { c with triggeredAbilities := c.triggeredAbilities.push ab } empowerN? rest
              | none =>
              match parseModes c.name line with
              | some ab => go (applyParsed c ab) empowerN? rest
              | none =>
                match matchModeled c.name units with
                | some (.spell e, n) =>
                  let more := units.drop n
                  if n == 0 || more.length == units.length then unrecognized c line
                  else
                    let (e, more) :=
                      if c.isInstantOrSorcery then extendSpellSequence c.name e more
                      else (e, more)
                    go (applyParsed c (.spell e)) empowerN? more
                | some (ab, n) =>
                  let more := units.drop n
                  if more.length < units.length then go (applyParsed c ab) empowerN? more
                  else unrecognized c line
                | none =>
                  match if c.isInstantOrSorcery then spellSentenceSequence c.name line else none with
                  | some e =>
                    let (e, more) := extendSpellSequence c.name e rest
                    go (applyParsed c (.spell e)) empowerN? more
                  | none =>
                    match parseFrcLine c line with
                    | some c => go c empowerN? rest
                    | none =>
                      match Parser.parseNovelStaticAbilityLine line c.name with
                      | some abs => go { c with staticAbilities := c.staticAbilities ++ abs } empowerN? rest
                      | none =>
                        match Parser.parseNovelTriggeredAbilityLines line c.name
                            (fun effText =>
                              matchTriggerMode c.name effText <|>
                              spellSentenceSequence c.name effText <|>
                              Parser.parseInstructionEffect effText c.name) with
                        | some abs => go { c with triggeredAbilities := c.triggeredAbilities ++ abs } empowerN? rest
                        | none =>
                          match if c.isInstantOrSorcery then Parser.parseInstructionEffect line c.name else none with
                          | some e => go (applyParsed c (.spell e)) empowerN? rest
                          | none => unrecognized c line
  go c none units

def parseAdventure (lines : List String) (keepUnrecognized : Bool := false) :
    Except String AdventureFace :=
  match lines with
  | [] => .error "empty Adventure"
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
    | [] => .error s!"Adventure {name} is missing a type line"
    | typeLine :: rules =>
      match parseTypeLine typeLine with
      | .error e => .error e
      | .ok (_, types, subtypes) =>
        let base : CardDef := {
          name
          manaCost := cost
          types
          subtypes := if subtypes.isEmpty then #["Adventure"] else subtypes
        }
        match parseRules base rules keepUnrecognized with
        | .error e => .error e
        | .ok c =>
          .ok {
            name := c.name
            manaCost := c.manaCost
            types := c.types
            subtypes := if c.subtypes.any (· == "Adventure") then c.subtypes else c.subtypes.push "Adventure"
            spellEffect := c.spellEffect
            additionalCosts := c.additionalCosts
            extraLines := #[]
          }

/-- Parse one face (no `//` back face) into a `CardDef`. -/
def parseFace (lines : List String) (keepUnrecognized : Bool := false) :
    Except String CardDef :=
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
        let (pt, rest) :=
          match rest with
          | line :: rest =>
            match parsePT line with
            | some pt => (pt, rest)
            | none => (({}, {}), line :: rest)
          | [] => (({}, {}), [])
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
          power := pt.1.number, toughness := pt.2.number
          powerStar := pt.1.star, toughnessStar := pt.2.star
        }
        let (base, rest) := takeExtras base rest
        let (rules, adv) := splitAdventure rest
        let (rules, prep) := splitPrepare rules
        -- CR 209.1 / 210.1: the loyalty and defense numbers sit in the lower
        -- right corner, so each may be labeled or bare, before the rules text
        -- or after it. CR 211.1 / 212.1: a vanguard's hand modifier is the
        -- lower left corner and its life modifier is the lower right.
        match detachLoyalty base.name base.isPlaneswalker rules with
        | .error e => .error e
        | .ok (loyalty, rules) =>
        match detachDefense base.name base.isBattle rules with
        | .error e => .error e
        | .ok (defense, rules) =>
        match detachHandLife base.name base.isVanguard rules with
        | .error e => .error e
        | .ok (handModifier, lifeModifier, rules) =>
        let base := { base with loyalty := loyalty, defense := defense
                                handModifier := handModifier
                                lifeModifier := lifeModifier }
        match parseRules base rules keepUnrecognized with
        | .error e => .error e
        | .ok c =>
          let withAdv : Except String CardDef :=
            match adv with
            | none => .ok c
            | some advLines =>
              match parseAdventure advLines keepUnrecognized with
              | .error e => .error e
              | .ok a => .ok { c with adventure := some a }
          match withAdv with
          | .error e => .error e
          | .ok c =>
            match prep with
            | none => .ok c
            | some prepLines =>
              match parseAdventure prepLines keepUnrecognized with
              | .error e => .error e
              | .ok a => .ok { c with prepareFace := some a }

/-- Parse the full printed text of one card.

The text is a name line (mana cost may sit on that line or on the next), a
type line, an optional `power/toughness` line, then rules text. A planeswalker's
loyalty number is `Loyalty: N` or the bare corner number, before or after the
rules text (CR 209.1). A loyalty symbol in an activation cost (`[+N]:`,
`+N:`, `[-N]:`, `[0]:`, and the `X` forms) is a loyalty ability (CR 606.2).
A battle's defense number is `Defense: N` or the bare corner number, before
or after the rules text (CR 210.1). A vanguard's hand modifier (lower left)
and life modifier (lower right) are `+N`, `-N`, or `0`, labeled or bare,
before or after the rules text (CR 211.1 / 212.1). A line that is exactly
`//` starts the back face. An Adventure is introduced by `//ADV//`.
A prepare spell is introduced by `//PREP//`. `keepUnrecognized` records a line
the parser does not recognize; the card is still rejected unless every line
is parsed and every effect is modelled. -/
@[irreducible, noinline] def parseOracleCard (text : String)
    (keepUnrecognized : Bool := false) : Except String CardDef :=
  let lines := nonEmptyLines text
  let (front, back) := splitBackFace lines
  let finish (c : CardDef) : Except String CardDef :=
    match c.modellingError? with
    | some e => .error e
    | none => .ok c
  match parseFace front keepUnrecognized with
  | .error e => .error e
  | .ok front =>
    match back with
    | none => finish front
    | some backLines =>
      match parseFace backLines keepUnrecognized with
      | .error e => .error e
      | .ok back => finish { front with otherFace := some back }

/-- Parse a card, keeping unrecognized rules lines as printed text. -/
@[irreducible, noinline] def parseOracleCardKeeping (text : String) : Except String CardDef :=
  parseOracleCard text (keepUnrecognized := true)

/-- `parseOracleCard`, panicking with the line that was not recognized. -/
@[irreducible, noinline] def parseOracleCard! (text : String) : CardDef :=
  match parseOracleCard text with
  | .ok c => c
  | .error e => panic! s!"parseOracleCard: {e}\n---\n{text}"

#guard
  match parseOracleCard
      "Snack\n{B}\nSorcery\nPut a stun counter on up to one target creature. Target player gains 2 life." with
  | .ok c =>
    match c.spellEffect with
    | some e => e.body == (Effect.plusOneUpToOneAndPlayerGainsLife 2 .stun).body
    | none => false
  | .error _ => false

#guard
  match parseOracleCard
      "Snack\n{B}\nSorcery\nPut two first strike counters on up to one target creature. Target player gains 3 life." with
  | .ok c =>
    match c.spellEffect with
    | some e =>
      e.body == (Effect.plusOneUpToOneAndPlayerGainsLife 3 .firstStrike 2).body
    | none => false
  | .error _ => false

#guard
  match parseOracleCard
      "Tidings of War\n{R}\nSorcery\nAmass Goblins 1. If this spell was cast from a graveyard, amass Goblins 3 instead. (To amass Goblins X, put X +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)\nFlashback {3}{R} (You may cast this card from your graveyard for its flashback cost. Then exile it.)" with
  | .ok c =>
    c.flashback == some (ManaCost.ofGenericAndColor 3 .red) &&
      match c.spellEffect with
      | some e => e == Effect.amassGoblinsOrFromGy 1 3
      | none => false
  | .error _ => false

/-- Keyword line used when a card has no stored rules text. -/
def renderKeywordLine (k : Array KeywordAbility) : Option String :=
  match KeywordAbility.renderOracleLines k with
  | [] => none
  | lines => some (String.intercalate "\n" lines)

def renderColors (cs : ColorSet) : String :=
  String.intercalate ", " (Color.all.filter cs.contains |>.map Color.englishName)

/-- Full printed card: name, mana cost, type line, P/T, color indicator,
`Token`, then `rules`. The rules text is not stored on the parsed `CardDef`. -/
def formatPrintedCard (name : String) (manaCost : ManaCost)
    (supertypes : Array Supertype) (types : Array CardType) (subtypes : Array Subtype)
    (power toughness : Option Int) (colorIndicator : Option ColorSet)
    (isToken : Bool) (rules : String)
    (powerStar : Bool := false) (toughnessStar : Bool := false) : String :=
  let cost := if manaCost.symbols.isEmpty then [] else [toString manaCost]
  let isCreature := types.any (· == .creature)
  let pt : List String :=
    match CardDef.formatPowerToughness power toughness powerStar toughnessStar isCreature with
    | some s => [s]
    | none => []
  let color :=
    match colorIndicator with
    | some cs => [s!"Color indicator: {renderColors cs}"]
    | none => []
  let token := if isToken then ["Token"] else []
  let rules := if (rules.trimAscii.copy).isEmpty then [] else [rules]
  String.intercalate "\n"
    ([name] ++ cost ++ [formatTypeLine supertypes types subtypes] ++ pt ++ color ++ token ++ rules)

/-- Full printed text reconstructed from modeled fields. -/
partial def renderFullOracle (c : CardDef) : String :=
  let kwLines := KeywordAbility.renderOracleLines c.keywords
  let hasCyclingKw := c.keywords.any fun | .cycling none _ => true | _ => false
  let cForAbilities :=
    if hasCyclingKw then
      { c with activatedAbilities := c.activatedAbilities.filter fun ab =>
          !(ab.isCycling && ab.effect.body == Instruction.drawFixed 1) }
    else c
  let rules := String.intercalate "\n" (kwLines ++ cForAbilities.structuredAbilityLines)
  let face :=
    formatPrintedCard c.name c.manaCost c.supertypes c.types c.subtypes
      c.power c.toughness c.colorIndicator c.isToken rules
      c.powerStar c.toughnessStar
  let face :=
    match c.loyalty with
    | some n => face ++ s!"\nLoyalty: {n}"
    | none => face
  let face :=
    match c.defense with
    | some n => face ++ s!"\nDefense: {n}"
    | none => face
  let face :=
    match c.handModifier with
    | some n => face ++ s!"\nHand: {renderModifier n}"
    | none => face
  let face :=
    match c.lifeModifier with
    | some n => face ++ s!"\nLife: {renderModifier n}"
    | none => face
  match c.otherFace with
  | none => face
  | some back => face ++ "\n//\n" ++ renderFullOracle back

def firstDiff (a b : String) : String :=
  let rec go : List Char → List Char → Nat → String
    | [], [], _ => "equal"
    | [], _, i => s!"at {i}, parsed ended"
    | _, [], i => s!"at {i}, source ended"
    | x :: xs, y :: ys, i =>
      if x == y then go xs ys (i + 1)
      else
        let preview (cs : List Char) := String.ofList (cs.take 80)
        s!"at {i}: «{preview (x :: xs)}» vs «{preview (y :: ys)}»"
  go a.toList b.toList 0

/-- How `parsed` differs from `source` after forgetting stored Oracle text. -/
def oracleRoundtripDiff (source parsed : CardDef) : Option String :=
  let a := reprStr source
  let b := reprStr parsed
  if a == b then none
  else some s!"{source.name}: {firstDiff a b}"

end Mtg.Engine
