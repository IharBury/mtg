/-!
# Oracle-text normalization

Comparable form of printed Oracle lines. Reminder text, ability words, and
the card's own name are removed so a line can be matched to the ability the
engine models.
-/

namespace Mtg.Engine.OracleNorm

/-- Unique strings, first occurrence kept. -/
def uniqueStrings (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.any (· == x) then acc else acc ++ [x]) []

/-- Collapse runs of whitespace. -/
def collapseWs (s : String) : String :=
  let rec go (cs : List Char) (inSpace : Bool) (acc : List Char) : List Char :=
    match cs with
    | [] => acc.reverse
    | c :: rest =>
      if c == ' ' || c == '\n' || c == '\t' then
        go rest true acc
      else
        let acc := if inSpace && !acc.isEmpty then ' ' :: acc else acc
        go rest false (c :: acc)
  String.ofList (go s.toList false [])

/-- Drop balanced parentheticals, including nested reminder text. -/
def stripParentheticals (s : String) : String :=
  Id.run do
    let mut acc : Array Char := #[]
    let mut depth : Nat := 0
    for c in s.toList do
      if c == '(' then
        depth := depth + 1
      else if c == ')' then
        depth := if depth == 0 then 0 else depth - 1
      else if depth == 0 then
        acc := acc.push c
    return String.ofList acc.toList

/-- If the whole line is a parenthetical (basic-land reminder), unwrap it. -/
def unwrapOuterParens (s : String) : String :=
  let t := s.trimAscii.copy
  if t.startsWith "(" && t.endsWith ")" && t.length >= 2 then
    (t.drop 1 |>.dropEnd 1).trimAscii.copy
  else t

/-- Drop a leading ability word (`Landfall —`, `Ferocious —`). -/
def stripAbilityWord (s : String) : String :=
  match s.splitOn "—" with
  | head :: rest =>
    if rest.isEmpty then s
    else
      let h := head.trimAscii.copy
      let known :=
        h == "Power-up" || h == "Street Justice" || h == "Legal Justice" ||
        h == "Cosmic Awareness" || h == "Unbreakable Skin" || h == "Enrage" ||
        h == "Landfall" || h == "Avian Telepathy" || h == "Seismic Takedown" ||
        h == "Embiggen Fist" || h == "Wasp's Sting" ||
        h == "No One Dies!" || h == "Sonic Attack" ||
        h == "Do You Like Squirrels?" || h == "I LOVE Squirrels!" ||
        h == "Net" || h == "Explosive" || h == "Boomerang" ||
        h == "Solar Beam" || h == "Density Control" || h == "Technopathy" ||
        h == "Trick Arrows" || h == "Radar Sense" ||
        h == "Photographic Reflexes" || h == "Cybernetic Senses" ||
        h == "Designed Only for Killing" ||
        h == "Mental Organism" || h == "Tyrannosaurus Rex" ||
        h == "Ferocious" || h == "Alliance" || h == "Boast" ||
        h == "Threshold"
      if h.isEmpty || (h.contains ' ' && !known) then s
      else (String.intercalate "—" rest).trimAscii.copy
  | [] => s

/-- Lowercase ASCII. -/
def lowerAscii (s : String) : String :=
  s.map Char.toLower

/-- Printed-name variants (`Gandalf, Spark Starter` → `Gandalf`). -/
def nameAliases (name : String) : List String :=
  let trimmed := name.trimAscii.copy
  let beforeComma := (trimmed.splitOn ",").headD trimmed |>.trimAscii.copy
  let first := (beforeComma.splitOn " ").headD beforeComma
  let skipFirst :=
    first == "The" || first == "A" || first == "An" || first == "Of" ||
      first == "Enchanted"
  let aliases :=
    if skipFirst then [trimmed, beforeComma] else [trimmed, beforeComma, first]
  uniqueStrings (aliases.filter (fun s => s.length > 2))

/-- Replace each `old` with `new` in order. -/
def applyReplacements (s : String) (pairs : List (String × String)) : String :=
  pairs.foldl (fun acc p => acc.replace p.fst p.snd) s

/-- Replace an isolated word. -/
def replaceWord (s old new : String) : String :=
  if old.isEmpty then s
  else
    Id.run do
      let chars := s.toList
      let needle := old.toList
      let n := needle.length
      let mut acc : List Char := []
      let mut i : Nat := 0
      while i < chars.length do
        let slice := chars.drop i |>.take n
        let beforeOk := i == 0 || !(chars[i - 1]!.isAlphanum)
        let afterOk :=
          i + n >= chars.length || !(chars[i + n]!.isAlphanum)
        if slice == needle && beforeOk && afterOk then
          acc := acc ++ new.toList
          i := i + n
        else
          acc := acc ++ [chars[i]!]
          i := i + 1
      String.ofList acc

/-- Lowercase, drop reminders, and replace the card's name with `this`. -/
def prepareLine (cardName : String) (s : String) : String :=
  let s := unwrapOuterParens s
  let s := stripParentheticals s
  let s := stripAbilityWord s
  let s := (lowerAscii s).trimAscii.copy
  let aliases := nameAliases cardName |>.map lowerAscii
  let s :=
    aliases.foldl (fun acc a =>
      let acc := acc.replace s!"{a}'s" "this"
      replaceWord acc a "this") s
  applyReplacements s [
    ("this creature's", "this"),
    ("this permanent's", "this"),
    ("this card's", "this"),
    ("this enchantment's", "this"),
    ("this equipment's", "this"),
    ("this artifact's", "this"),
    ("this aura's", "this"),
    ("this spell's", "this"),
    ("this creature", "this"),
    ("this permanent", "this"),
    ("this enchantment", "this"),
    ("this equipment", "this"),
    ("this artifact", "this"),
    ("this aura", "this"),
    ("this card", "this"),
    ("this spell", "this"),
    ("this land", "this"),
    ("this vehicle", "this"),
    ("this saga", "this"),
    ("this token", "this"),
    ("this enter ", "this enters "),
    ("this enter,", "this enters,")
  ]

/-- English number words that appear in Oracle (`two cards`, `three or more`). -/
def replaceNumberWords (s : String) : String :=
  let words : List (String × String) := [
    ("twenty", "20"), ("nineteen", "19"), ("eighteen", "18"),
    ("seventeen", "17"), ("sixteen", "16"), ("fifteen", "15"),
    ("fourteen", "14"), ("thirteen", "13"), ("twelve", "12"),
    ("eleven", "11"), ("ten", "10"), ("nine", "9"), ("eight", "8"),
    ("seven", "7"), ("six", "6"), ("five", "5"), ("four", "4"),
    ("three", "3"), ("two", "2"), ("one", "1")
  ]
  words.foldl (fun acc p => replaceWord acc p.fst p.snd) s

/-- Drop a leading `this ` left over from name replacement. -/
def dropLeadingThis (s : String) : String :=
  let s := s.trimAscii.copy
  if s.startsWith "this " then (s.drop "this ".length).trimAscii.copy else s

/-- Keep letters, digits, mana braces, and P/T signs; other punctuation
becomes a space. Apostrophes are dropped so `can't` is `cant`. -/
def keepSignificant (s : String) : String :=
  String.ofList (s.toList.filterMap (fun c =>
    if c == '\'' then none
    else if c.isAlphanum || c == '{' || c == '}' || c == '/' || c == '+' || c == '-' then
      some c
    else some ' '))

/-- Phrase-level Oracle equivalences after `prepareLine`. -/
def normalizePhrases (s : String) : String :=
  applyReplacements s [
    ("put that card", "put it"),
    ("sacrifice this artifact", "sacrifice"),
    ("sacrifice this creature", "sacrifice"),
    ("sacrifice this land", "sacrifice"),
    ("sacrifice this", "sacrifice"),
    ("sacrifice another creature or artifact", "sacrifice an artifact or creature"),
    ("sacrifice another artifact or creature", "sacrifice an artifact or creature"),
    ("he gains", "this gains"),
    ("she gains", "this gains"),
    ("he deals", "this deals"),
    ("she deals", "this deals"),
    ("it deals", "this deals"),
    ("he fights", "this fights"),
    ("she fights", "this fights"),
    ("tap him", "tap this"),
    ("tap her", "tap this"),
    ("this leave the battlefield", "this leaves the battlefield"),
    ("she connives", "it connives"),
    ("he connives", "it connives"),
    ("he has flying", "it has flying"),
    ("attached to him", "attached to it"),
    ("dealt to him", "dealt to it"),
    ("with him on the battlefield", "with it on the battlefield"),
    ("begin the game with him", "begin the game with it"),
    ("and only once each turn", "activate only once each turn"),
    ("activate only from the graveyard", ""),
    ("activate only from your hand", ""),
    ("if you control a creature with power", "while you control a creature with power"),
    ("other elf creatures you control", "other elves you control"),
    ("other bear creatures you control", "other bears you control"),
    ("other merfolk creatures you control", "other merfolk you control"),
    ("other villain creatures you control", "other villains you control"),
    ("other hero creatures you control", "other heroes you control"),
    ("street justice ", ""),
    ("legal justice ", ""),
    ("trick arrows ", ""),
    ("if her power", "if its power"),
    ("if his power", "if its power"),
    ("enchant creature you control", "enchant creature"),
    ("target player create ", "target player creates "),
    ("destroy target artifact or land", "destroy target land"),
    ("you may play it until the end of your next turn",
      "until the end of your next turn you may play that card"),
    ("this enter ", "this enters "),
    ("counter on him", "counter on this"),
    ("counter on her", "counter on this"),
    ("counter on it", "counter on this"),
    ("shield counter on him", "counter on this"),
    ("shield counter on her", "counter on this"),
    ("shield counter on it", "counter on this")
  ]

/-- Comparable form of one ability unit. -/
def normalizeUnit (cardName : String) (s : String) : String :=
  let s := prepareLine cardName s
  let s := replaceNumberWords s
  let s := normalizePhrases s
  let s := keepSignificant s
  let s := collapseWs s
  dropLeadingThis s

/-- True when `line` is a Gatherer Adventure type line. -/
def isAdventureTypeLine (s : String) : Bool :=
  let t := s.trimAscii.copy
  (t.startsWith "Sorcery" || t.startsWith "Instant") &&
    (t.endsWith "Adventure" || (t.splitOn "Adventure").length > 1)

/-- Attach `•` mode lines to the preceding line. -/
def mergeBulletLines (lines : List String) : List String :=
  lines.foldl (fun acc line =>
    if line.trimAscii.copy.startsWith "•" then
      match acc.reverse with
      | [] => [line]
      | last :: rev => ((last ++ " " ++ line.trimAscii.copy) :: rev).reverse
    else
      acc ++ [line]) []

/-- Join an Adventure name, type line, and effect into one unit. -/
def mergeAdventureBlocks : List String → List String
  | a :: b :: c :: rest =>
    if isAdventureTypeLine b then
      s!"{a} {b} {c}" :: mergeAdventureBlocks rest
    else
      a :: mergeAdventureBlocks (b :: c :: rest)
  | xs => xs

/-- Split `Flying, first strike, ward {1}` into keywords and `Ward {1}.`. -/
def splitKeywordWardLine (s : String) : List String :=
  let t := s.trimAscii.copy
  let lower := lowerAscii t
  if !(lower.contains ", ward {") then [s]
  else
    match t.splitOn ", ward {" with
    | [kws, rest] =>
      let digits := rest.takeWhile Char.isDigit
      if kws.isEmpty || digits.isEmpty then [s]
      else [kws, s!"Ward \{{digits}}."]
    | _ =>
      match t.splitOn ", Ward {" with
      | [kws, rest] =>
        let digits := rest.takeWhile Char.isDigit
        if kws.isEmpty || digits.isEmpty then [s]
        else [kws, s!"Ward \{{digits}}."]
      | _ => [s]

end Mtg.Engine.OracleNorm
