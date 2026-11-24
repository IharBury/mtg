import Mtg.Engine.Card.CardDef
import Mtg.Engine.Card.OracleNorm
import Mtg.Engine.Card.Parser.ParagraphClass

/-!
# Parsing a full Oracle card (CR 108, 113.3, 201–212, 712, 714, 715)

`parseOracleCard` parses one card's full printed Oracle text — name, mana cost,
type line, power and toughness, loyalty/defense/vanguard modifiers, sub-faces,
back faces, and rules paragraphs — into a `CardDef` exclusively through the
five-stage compositional parser under `Mtg.Engine.Card.Parser`:

- Stage 1 (`Parser.FrameSplit`): faces, sub-faces, headers, P/T, corner numbers,
  Saga chapter headers, and loyalty headers.
- Stage 2 (`Parser.Lexer` + `OracleNorm`): reminder-text stripping (CR 207.2a),
  `{CHAOS}` stripping (CR 207.4), mechanic/ability-word splitting (CR 207.2c),
  self-name aliasing, and quote-aware lexing.
- Stage 3 (`Parser.ParagraphClass`): deterministic paragraph classification into
  deck limits, chapters, keywords (including `Equip` and `Cycling`), activated
  abilities, triggered abilities, static abilities, and spell abilities.
- Stage 4 (`Parser.SubGrammars`, `Parser.TokenEmblemGrammar`,
  `Parser.InspectSearchGrammar`, `Parser.InstructionGrammar`,
  `Parser.AbilityGrammar`): compositional grammars for every AST layer.
- Stage 5 (`Parser.DiscourseBind`): cross-sentence anaphora resolution,
  `where X is ...` substitution, and `Instruction.bind` insertion.

Parsing fails cleanly when any line is unrecognized or any effect would not
resolve; the resulting `CardDef` stores only structured ASTs (zero raw rules text).
-/

namespace Mtg.Engine

open OracleNorm

/-! ### Stage-1 Frame & Header Re-Exports -/

abbrev parseManaSymbol := Parser.parseManaSymbol
abbrev parseManaCost := Parser.parseManaCost
abbrev splitNameCost := Parser.splitNameCost
abbrev parseSupertype := Parser.parseSupertype
abbrev parseCardType := Parser.parseCardType
abbrev parseTypeLine := Parser.parseTypeLine
abbrev parseUnsignedNat := Parser.parseUnsignedNat
abbrev isMinusSign := Parser.isMinusSign
abbrev parseModifier := Parser.parseModifier
abbrev renderModifier := Parser.renderModifier
abbrev prefixRest := Parser.prefixRest
abbrev parseKeyedModifier := Parser.parseKeyedModifier
abbrev parseHandLifeLine := Parser.parseHandLifeLine
abbrev parseBareModifierPair := Parser.parseBareModifierPair
abbrev parseStat := Parser.parseStat
abbrev parsePT := Parser.parsePT
abbrev parseColorName := Parser.parseColorName
abbrev parseColorIndicator := Parser.parseColorIndicator
abbrev nonEmptyLines := Parser.nonEmptyLines
abbrev splitBackFace := Parser.splitBackFace
abbrev splitMarked := Parser.splitMarked
abbrev splitAdventure := Parser.splitAdventure
abbrev splitPrepare := Parser.splitPrepare
abbrev parseChapterHeader := Parser.parseChapterHeader
abbrev detachLoyalty := Parser.detachLoyalty
abbrev detachDefense := Parser.detachDefense
abbrev detachHandLife := Parser.detachHandLife
abbrev parseLoyaltyAbilityLine := Parser.parseLoyaltyAbilityLine

/-- True when `line` is the non-keyword CR 509.1b static ability `"~ can't be blocked."` -/
def isCantBeBlockedLine (cardName line : String) : Bool :=
  let prepared := prepareLine cardName line
  let cleaned := dropLeadingThis ((prepared.replace "." "").trimAscii.copy)
  cleaned == "can't be blocked"

/-- Parse a CR 702 keyword line (including `Equip` and `Cycling`) via
`Parser.parseKeywordLine`, stripping leading `{CHAOS}` and CR 207.2c ability
words while retaining cumulative multiplicity (CR 702.83b / 702.85 / 702.108b). -/
def keywordLineAbilities (_cardName line : String) : Option (Array KeywordAbility) :=
  let cleaned := stripAbilityWords (stripChaosSymbol line)
  Parser.parseKeywordLine cleaned

/-! ### Full Compositional Card Parsing -/

/-- Parse the full printed text of one card exclusively through Stages 1–5.

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
A prepare spell is introduced by `//PREP//`. -/
@[irreducible, noinline] def parseOracleCard (text : String) : Except String CardDef :=
  Parser.parseOracleCardCompositional text

/-- `parseOracleCard`, panicking with the line that was not recognized. -/
@[irreducible, noinline] def parseOracleCard! (text : String) : CardDef :=
  match parseOracleCard text with
  | .ok c => c
  | .error e => panic! s!"parseOracleCard: {e}\n---\n{text}"

/-! ### Printed Card Formatting & Structural Round-Trip Diagnostics -/

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
    (power toughness : Option PrintedStat) (colorIndicator : Option ColorSet)
    (isToken : Bool) (rules : String) : String :=
  let cost := if manaCost.symbols.isEmpty then [] else [toString manaCost]
  let isCreature := types.any (· == .creature)
  let pt : List String :=
    match CardDef.formatPowerToughness power toughness isCreature with
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

/-- Canonical full Oracle text reconstructed purely via `ToOracle CardDef`. -/
abbrev renderFullOracle (c : CardDef) : String :=
  CardDef.renderFullOracle c

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

/-- Structural `BEq CardDef` difference between `source` and round-tripped `parsed`. -/
def oracleRoundtripDiff (source parsed : CardDef) : Option String :=
  if source == parsed then none
  else some s!"{source.name}: {firstDiff (reprStr source) (reprStr parsed)}"

end Mtg.Engine
