import Mtg.Engine.Card.ChapterEffects

/-!
# Sagas (CR 714)

Printed Saga definitions: Roman-numeral parsing, chapter lines, and the
sacrifice-after bookkeeping.
-/

namespace Mtg.Engine

/-- Parse one Roman chapter numeral (`I`–`VI`). -/
def parseRomanNumeral (s : String) : Nat :=
  match s.replace " " "" with
  | "I" => 1
  | "II" => 2
  | "III" => 3
  | "IV" => 4
  | "V" => 5
  | "VI" => 6
  | _ => 0

/-- Chapter numbers on a printed line (`I`, `III, IV`, `I, II, III, IV`). -/
def parseChapterNumbers (roman : String) : Array Nat :=
  (roman.splitOn ",").toArray |>.map parseRomanNumeral |>.filter (· != 0)

/-- One printed Saga chapter line (`I — …`, `III, IV — …`). -/
structure SagaChapter where
  roman : String
  effect : String
  /-- Chapter numbers this line triggers on. Empty means parse `roman`. -/
  numbers : Array Nat := #[]
  /-- Structured resolution. `none` is reminder-only (tests). -/
  chapterEffect : Option Effect := none
deriving Repr, Inhabited, BEq

namespace SagaChapter

/-- Chapter numbers for triggering (CR 714.3a). -/
def chapterNumbers (ch : SagaChapter) : Array Nat :=
  if ch.numbers.isEmpty then parseChapterNumbers ch.roman else ch.numbers

/-- A catalog chapter with parsed numerals and a real effect. -/
def of (roman effect : String) (e : Effect) : SagaChapter :=
  let e :=
    match e.asChapter? with
    | some _ => e
    | none => Effect.ofChapter (Effect.chapterSpell e)
  { roman, effect, numbers := parseChapterNumbers roman,
    chapterEffect := some e }

end SagaChapter

/-- Roman numeral for a chapter count (`4` → `IV`). `0` is empty. -/
def romanNumeral (n : Nat) : String :=
  Id.run do
    let mut n := n
    let mut acc : String := ""
    let digits : Array (Nat × String) := #[
      (10, "X"), (9, "IX"), (5, "V"), (4, "IV"), (1, "I")
    ]
    for (v, s) in digits do
      while n >= v do
        acc := acc ++ s
        n := n - v
    return acc

/-- Printed Saga (CR 714). The sacrifice point is the final chapter number
(CR 714.2d / 714.4). The parenthetical “Sacrifice after …” line is reminder
text and is not read (CR 207.2a). -/
structure SagaDef where
  /-- Final chapter as a Roman numeral (CR 714.2d). -/
  sacrificeAfter : String
  chapters : Array SagaChapter
deriving Repr, Inhabited, BEq

namespace SagaDef

/-- Greatest chapter number among this Saga's chapter abilities (ruling 291). -/
def finalChapterNumber (s : SagaDef) : Nat :=
  s.chapters.foldl (fun acc ch =>
    ch.chapterNumbers.foldl (fun acc n => max acc n) acc) 0

/-- Chapter lines that trigger when lore becomes `lore` (CR 714.3a). -/
def chaptersForLore (s : SagaDef) (lore : Nat) : Array SagaChapter :=
  s.chapters.filter (fun ch => ch.chapterNumbers.contains lore)

end SagaDef

#guard romanNumeral 0 == ""
#guard romanNumeral 3 == "III"
#guard romanNumeral 4 == "IV"
#guard romanNumeral 9 == "IX"
#guard romanNumeral 14 == "XIV"
#guard parseChapterNumbers "I" == #[1]
#guard parseChapterNumbers "III, IV" == #[3, 4]
#guard parseChapterNumbers "I, II, III, IV" == #[1, 2, 3, 4]
#guard (SagaChapter.of "III, IV" "Add {R}." (Effect.chapterAddMana (.colored .red))).chapterNumbers ==
  #[3, 4]

end Mtg.Engine
