import Mtg.Engine.Card.Definition
import Mtg.Engine.Card.LineCache

/-!
# Oracle text folding

Case-folding, sentences, mana symbols, keyword lines, and type lines.
Helpers that run on every candidate remember their last result in
`OracleParts.Cache`.
-/

namespace Mtg.Engine

namespace OracleParts

open Cache

/-!
The catalog compiles by evaluating `parseOracleParts` on every card. Each
candidate parser case-folds and splits the same line, so these helpers remember
the last result for a string object (`OracleParts.Cache`). A copy with the same
characters misses and is folded again, which is the same result.

A cache miss runs only the pure body. Those bodies do not call the cached
wrappers, so one lookup does not re-enter another.
-/

def lowerAscii : String → String := CardDef.lowerAscii

def stripReminderParenthetical : String → String := CardDef.stripReminderParenthetical

def stripTrailingPeriod (s : String) : String :=
  let s := s.trimAscii.copy
  if s.endsWith "." then (s.dropEnd 1).trimAscii.copy else s

/-- Trimmed copy of `s`. -/
private def copiedPure (s : String) : String :=
  s.trimAscii.copy

private unsafe def copiedFast (s : String) : String :=
  cachedAt copiedCache s copiedPure

@[noinline, implemented_by copiedFast]
def copied (s : String) : String :=
  copiedPure s

/-- Case-folded Oracle text. -/
private def normPure (s : String) : String :=
  lowerAscii (copiedPure s)

private unsafe def normFast (s : String) : String :=
  cachedAt normCache s normPure

@[noinline, implemented_by normFast]
def norm (s : String) : String :=
  normPure s

/-- Sentences of `text`. A reminder parenthetical is not part of a sentence,
and a trailing period is dropped. -/
private def sentencesPure (text : String) : List String :=
  (stripReminderParenthetical text).splitOn ". "
    |>.map stripTrailingPeriod
    |>.filter (· != "")

private unsafe def sentencesFast (text : String) : List String :=
  cachedAt sentencesCache text sentencesPure

@[noinline, implemented_by sentencesFast]
def sentences (text : String) : List String :=
  sentencesPure text

/-- Rules text of `line` after a reminder parenthetical is removed.
Empty when the line is only a reminder. -/
private def rulesTextPure (line : String) : String :=
  stripTrailingPeriod (stripReminderParenthetical line)

private unsafe def rulesTextFast (line : String) : String :=
  cachedAt rulesTextCache line rulesTextPure

@[noinline, implemented_by rulesTextFast]
def rulesText (line : String) : String :=
  rulesTextPure line

private def normSentencePure (s : String) : String :=
  normPure (stripTrailingPeriod s)

private unsafe def normSentenceFast (s : String) : String :=
  cachedAt normSentenceCache s normSentencePure

@[noinline, implemented_by normSentenceFast]
def normSentence (s : String) : String :=
  normSentencePure s

private def normLinePure (line : String) : String :=
  normPure (rulesTextPure line)

private unsafe def normLineFast (line : String) : String :=
  cachedAt normLineCache line normLinePure

@[noinline, implemented_by normLineFast]
def normLine (line : String) : String :=
  normLinePure line

#guard norm "Smaug — X" == "smaug — x"
#guard normLine "  Flying. " == "flying"
#guard sentences "Draw a card." == ["Draw a card"]
#guard sentences "Draw a card. You gain 1 life." == ["Draw a card", "You gain 1 life"]

/-- `s` is the printed sentence `expected`, ignoring case and a trailing period. -/
def sentenceIs (s expected : String) : Bool :=
  normSentence s == expected

/-- Text after `lead`, when `s` starts with it.
`drop` returns a slice, so the result is copied before any later `splitOn`. -/
def after? (s lead : String) : Option String :=
  if s.startsWith lead then some (s.drop lead.length).trimAscii.copy else none

/-- Text before `tail`, when `s` ends with it. -/
def before? (s tail : String) : Option String :=
  if s.endsWith tail then some (s.dropEnd tail.length).trimAscii.copy else none

/-- Text strictly between `lead` and `tail`. -/
def between? (s lead tail : String) : Option String :=
  (after? s lead).bind fun mid => before? mid tail

/-- Exactly two pieces of `s` around `sep`. Each piece is trimmed and copied.
Zero or several occurrences of `sep` fail. -/
def split2? (s sep : String) : Option (String × String) :=
  match s.splitOn sep with
  | [a, b] => some (copied a, copied b)
  | _ => none

/-- Printed `<cost>: <effect>` after reminder text and a trailing period
are removed. -/
def splitPrintedAbility? (line : String) : Option (String × String) :=
  split2? (rulesText line) ": "

/-- Pieces of `a`, `a or b`, or `a, b, or c`. -/
def orList (s : String) : List String :=
  let normalized := ((norm s).replace ", or " ", ").replace " or " ", "
  normalized.splitOn ", " |>.map copied |>.filter (· != "")

def natOfDigits? (s : String) : Option Nat :=
  let cs := s.toList
  if cs.isEmpty || !cs.all Char.isDigit then none
  else some (cs.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)

/-- A printed positive numeral. Words such as `two` are not numerals, and zero
is not a count. -/
def positiveDigits? (s : String) : Option Nat :=
  (natOfDigits? (copied s)).filter (· != 0)

/-- `one` through `ten`, or a numeral. The numeral is read from case-folded
text, so surrounding spaces do not hide it. -/
def englishSmall? (s : String) : Option Nat :=
  let s := norm s
  match s with
  | "one" => some 1
  | "two" => some 2
  | "three" => some 3
  | "four" => some 4
  | "five" => some 5
  | "six" => some 6
  | "seven" => some 7
  | "eight" => some 8
  | "nine" => some 9
  | "ten" => some 10
  | _ => natOfDigits? s

/-- A printed positive count: `two`, `2`. Zero is not a count. -/
def positiveCount (s : String) : Option Nat :=
  (englishSmall? s).filter (· != 0)

/-- Drop a leading `a` / `an`. The remainder is case-folded. -/
def dropArticle? (s : String) : Option String :=
  let s := norm s
  after? s "an " <|> after? s "a "

def colorOfLetter? (s : String) : Option Color :=
  match lowerAscii s with
  | "w" => some .white
  | "u" => some .blue
  | "b" => some .black
  | "r" => some .red
  | "g" => some .green
  | _ => none

def parseOneSymbol (s : String) : Option ManaSymbol :=
  let s := s.trimAscii.copy
  match natOfDigits? s with
  | some n => some (.generic n)
  | none =>
    match lowerAscii s with
    | "x" => some .x
    | "c" => some .colorless
    | "s" => some .snow
    | _ =>
      match colorOfLetter? s with
      | some c => some (.colored c)
      | none =>
        match split2? s "/" with
        | some (a, b) =>
          match colorOfLetter? a, colorOfLetter? b with
          | some ca, some cb => some (.hybrid ca cb)
          | _, _ => none
        | none => none

/-- Mana symbols in `s`, which may be a whole cost such as `{1}{W}`.
Text other than symbols and spaces makes the parse fail. -/
def parseManaSymbols (s : String) : Option (List ManaSymbol) :=
  go s.toList [] [] false
where
  go : List Char → List ManaSymbol → List Char → Bool → Option (List ManaSymbol)
    | [], acc, _, false => some acc.reverse
    | [], _, _, true => none
    | ' ' :: rest, acc, body, false => go rest acc body false
    | '{' :: rest, acc, _, false => go rest acc [] true
    | '}' :: rest, acc, body, true =>
      match parseOneSymbol (String.ofList body.reverse) with
      | none => none
      | some sym => go rest (sym :: acc) [] false
    | c :: rest, acc, body, true => go rest acc (c :: body) true
    | _ :: _, _, _, false => none

/-- Mana symbols, failing when `s` has none. -/
def nonemptyMana? (s : String) : Option (List ManaSymbol) :=
  (parseManaSymbols s).bind fun syms =>
    if syms.isEmpty then none else some syms

/-- `{N}` as a positive generic cost. Zero and any other symbol are not that cost. -/
def positiveGeneric? (s : String) : Option Nat :=
  match nonemptyMana? s with
  | some [.generic n] => if n == 0 then none else some n
  | _ => none

def keywordOfOracle? (s : String) : Option Keyword :=
  match norm s with
  | "flash" => some .flash
  | "haste" => some .haste
  | "vigilance" => some .vigilance
  | "flying" => some .flying
  | "menace" => some .menace
  | "hexproof" => some .hexproof
  | "indestructible" => some .indestructible
  | "reach" => some .reach
  | "trample" => some .trample
  | "deathtouch" => some .deathtouch
  | "defender" => some .defender
  | "lifelink" => some .lifelink
  | "first strike" => some .firstStrike
  | "islandwalk" => some .islandwalk
  | "storied" => some .storied
  | "double strike" => some .doubleStrike
  | "prowess" => some .prowess
  | "ascend" => some .ascend
  | "shadow" => some .shadow
  | "changeling" => some .changeling
  | "improvise" => some .improvise
  | "boast" => some .boast
  | "cascade" => some .cascade
  | "extort" => some .extort
  | _ => none

/-- A line that is only modeled keywords, e.g. `Lifelink` or `Flying, deathtouch`.
One unrecognized word fails the line. -/
def keywordParts? (line : String) : Option (List CardPart) :=
  let cleaned := rulesText line
  if cleaned.isEmpty then none
  else
    let tokens :=
      cleaned.splitOn "," |>.map (·.trimAscii.copy) |>.filter (· != "")
    if tokens.isEmpty then none
    else
      (tokens.mapM keywordOfOracle?).map fun kws =>
        kws.map fun k => .ability (.keyword k)

def supertypeOfOracle? (s : String) : Option CardSupertype :=
  match lowerAscii s with
  | "basic" => some .basic
  | "legendary" => some .legendary
  | "ongoing" => some .ongoing
  | "snow" => some .snow
  | "world" => some .world
  | _ => none

def cardTypes : List CardType := [
  .artifact, .battle, .creature, .enchantment, .instant, .land,
  .planeswalker, .sorcery, .kindred, .dungeon, .plane, .phenomenon,
  .vanguard, .scheme, .conspiracy
]

def typeOfOracle? (s : String) : Option CardType :=
  let s := lowerAscii s
  let named := fun (name : String) =>
    cardTypes.find? (fun t => lowerAscii t.englishName == name)
  match named s with
  | some t => some t
  | none =>
    if s.endsWith "s" && s.length > 1 then named (s.dropEnd 1).trimAscii.copy else none

def cardSubtypes : List CardSubtype := [
  .adventure, .advisor, .alien, .ape, .arcane, .archer, .army, .artificer,
  .assassin, .aura, .avatar, .barbarian, .bard, .bat, .bear, .beast,
  .berserker, .bird, .cat, .centaur, .citizen, .cleric, .clue, .demigod,
  .detective, .dinosaur, .doctor, .dog, .dragon, .druid, .dwarf, .elder, .elemental,
  .elephant, .elf, .elk, .equipment, .eternal, .food, .forest, .frog, .gamma,
  .gate, .giant, .goblin, .god, .halfling, .hero, .horror, .horse, .human,
  .infinity, .inhuman, .insect, .island, .knight, .kree, .mercenary, .merfolk,
  .minion, .minotaur, .mountain, .mutant, .nightmare, .ninja, .noble, .ogre, .orc,
  .peasant, .performer, .pilot, .pirate, .plains, .plan, .rabbit, .ranger,
  .robot, .rogue, .saga, .samurai, .scientist, .scout, .shaman, .shapeshifter,
  .skrull, .snake, .soldier, .sorcerer, .spider, .spirit, .spy, .squirrel,
  .stone, .swamp, .troll, .treasure, .vampire, .vehicle, .villain, .wall, .warlock,
  .warrior, .whale, .wizard, .wolf, .wraith, .wurm, .zombie
]

def subtypeOfOracle? (s : String) : Option CardSubtype :=
  let s := lowerAscii s
  cardSubtypes.find? (fun st => lowerAscii (toString st) == s)

def partOfTypeWord? (w : String) : Option CardPart :=
  (supertypeOfOracle? w).map CardPart.supertype <|>
    (typeOfOracle? w).map CardPart.type <|>
    (subtypeOfOracle? w).map CardPart.subtype

def isCardTypePart : CardPart → Bool
  | .type _ => true
  | _ => false

/-- A type line such as `Instant — Adventure` or `Legendary Creature — Dwarf Scout`.
Every word must be a supertype, card type, or subtype, and at least one word
must be a card type. Anything else is `none`. -/
def parseTypeLine (line : String) : Option (List CardPart) :=
  let line := stripReminderParenthetical line
  let words := (line.splitOn "—").flatMap fun side =>
    let side := side.trimAscii.copy
    side.splitOn " " |>.filterMap fun w =>
      let w := w.trimAscii.copy
      if w.isEmpty then none else some w
  if words.isEmpty then none
  else
    (words.mapM partOfTypeWord?).bind fun parts =>
      if parts.any isCardTypePart then some parts else none

/-- Split `Concerted Care {1}{W}` into the name and the brace text. -/
def splitNameCost (line : String) : String × String :=
  match line.splitOn "{" with
  | [] => (line.trimAscii.copy, "")
  | name :: rest =>
    if rest.isEmpty then (name.trimAscii.copy, "")
    else (name.trimAscii.copy, "{" ++ String.intercalate "{" rest)

/-- `Concerted Care {1}{W}` as a name and mana cost.
A brace cost that is not mana symbols makes the parse fail. -/
def parseNameAndCost (line : String) : Option (List CardPart) :=
  let line := stripReminderParenthetical line
  let (name, costText) := splitNameCost line
  if name.isEmpty then none
  else if costText.isEmpty then some [.name name]
  else
    match nonemptyMana? costText with
    | some syms => some [.name name, .manaCost syms]
    | none => none

end OracleParts

end Mtg.Engine
