/-!
# Oracle-text normalization

Comparable form of printed Oracle lines. Reminder text (CR 207.2a), ability
words (CR 207.2c), the chaos symbol that introduces a chaos ability (CR 207.4),
and the card's own name are removed so a line can be matched to the ability
the engine models.
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

/-- Drop balanced parentheticals, including nested reminder text.

CR 207.2a: reminder text is parenthetical text in the text box. It may sit on
the same line as an ability or on a line of its own, and it is not rules text.
Oracle plaintext has no italic markup, so a parenthetical is the reminder.
-/
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

/-- Rules text of one printed line, with reminder text removed (CR 207.2a).

A line that is only a parenthetical — a basic-land mana reminder, a Saga
reminder, or a keyword reminder printed on its own line — is empty.
-/
def dropReminderText (s : String) : String :=
  (stripParentheticals s).trimAscii.copy

/-- Ability words (CR 207.2c), in rules order.

An ability word is italicized at the start of an ability. It has no rules
meaning, so Oracle parsing ignores it. Comparison is case-insensitive.
`council's dilemma` is stored with an ASCII apostrophe. Printed Oracle
may use U+2019 instead.
-/
def abilityWords : List String := [
  "adamant", "addendum", "alliance", "battalion", "bloodrush", "celebration",
  "channel", "chroma", "cohort", "constellation", "converge",
  "council's dilemma", "coven", "delirium", "descend 4", "descend 8",
  "disappear", "domain", "eerie", "eminence", "enrage", "exhaust", "fateful hour",
  "fathomless descent", "ferocious", "flurry", "formidable", "grandeur",
  "hellbent", "heroic", "imprint", "infusion", "inspired", "join forces",
  "kinship", "landfall", "lieutenant", "magecraft", "metalcraft", "morbid",
  "opus", "pack tactics", "paradox", "parley", "radiance", "raid", "rally",
  "renew", "repartee", "revolt", "secret council", "spell mastery", "strive",
  "survival", "sweep", "tempting offer", "threshold", "undergrowth", "valiant",
  "vivid", "void", "will of the council"
]

private def foldApos (c : Char) : Char :=
  if c == '\'' || c == Char.ofNat 0x2019 || c == Char.ofNat 0x2018 then '\''
  else c.toLower

private def eqFold (a b : Char) : Bool :=
  foldApos a == foldApos b

/-- A character that may sit inside an ability-word label. -/
private def isAbilityLabelChar (c : Char) : Bool :=
  c.isAlphanum || c == '\'' || c == Char.ofNat 0x2019 || c == Char.ofNat 0x2018

private def skipWs (cs : Array Char) (i : Nat) : Nat :=
  Id.run do
    let mut i := i
    while i < cs.size && (cs[i]! == ' ' || cs[i]! == '\n' || cs[i]! == '\t') do
      i := i + 1
    return i

/-- If `word` labels an ability at `i`, the index just after `word —`. -/
private def matchAbilityWordAt (cs : Array Char) (i : Nat) (word : String) : Option Nat :=
  let w := word.toList.toArray
  let n := w.size
  if n == 0 || i + n > cs.size then
    none
  else
    Id.run do
      let mut ok := true
      let mut k : Nat := 0
      while ok && k < n do
        if eqFold cs[i + k]! w[k]! then
          k := k + 1
        else
          ok := false
      if !ok then
        return none
      let j := skipWs cs (i + n)
      if j >= cs.size || cs[j]! != '—' then
        return none
      return some (skipWs cs (j + 1))

/-- An ability word labels the ability that follows (CR 207.2c). It sits at
the start of the text, or just after a quote, a mode bullet, or the em dash
that opens the ability (`I —`, `"Landfall —`). -/
private def abilityIntro (cs : Array Char) (i : Nat) : Bool :=
  Id.run do
    let mut j := i
    while j != 0 && (cs[j - 1]! == ' ' || cs[j - 1]! == '\n' || cs[j - 1]! == '\t') do
      j := j - 1
    if j == 0 then
      return true
    let c := cs[j - 1]!
    return c == '"' || c == Char.ofNat 0x201C || c == '•' || c == '—'

/-- End index after the longest CR 207.2c ability word at `i`, if one labels
the ability that follows. -/
private def abilityWordEnd (cs : Array Char) (i : Nat) : Option Nat :=
  if !abilityIntro cs i || (i != 0 && isAbilityLabelChar cs[i - 1]!) then
    none
  else
    Id.run do
      let mut best : Option Nat := none
      for w in abilityWords do
        match matchAbilityWordAt cs i w with
        | some stop =>
          if stop > i then
            best := some (match best with
              | none => stop
              | some b => max b stop)
        | none => pure ()
      return best

/-- The chaos symbol `{CHAOS}` (CR 107.12), matched without regard to case. -/
private def chaosSymbolLiteral : Array Char := "{CHAOS}".toList.toArray

private def matchChaosSymbol (cs : Array Char) (i : Nat) : Bool :=
  let lit := chaosSymbolLiteral
  let n := lit.size
  if i + n > cs.size then false
  else
    Id.run do
      let mut ok := true
      let mut k : Nat := 0
      while ok && k < n do
        if eqFold cs[i + k]! lit[k]! then
          k := k + 1
        else
          ok := false
      return ok

/-- A chaos symbol introduces the ability (CR 207.4). It sits at the start of
the text, or just after a quote, a mode bullet, an em dash, or another chaos
symbol. A `{CHAOS}` after a word names a planar-die face (CR 107.12). -/
private def chaosIntro (cs : Array Char) (i : Nat) : Bool :=
  let n := chaosSymbolLiteral.size
  Id.run do
    let mut j := i
    let mut fuel := cs.size + 1
    while fuel != 0 do
      fuel := fuel - 1
      if j != 0 && cs[j - 1]!.isAlphanum then
        return false
      if abilityIntro cs j then
        return true
      let mut k := j
      while k != 0 && (cs[k - 1]! == ' ' || cs[k - 1]! == '\n' || cs[k - 1]! == '\t') do
        k := k - 1
      if k >= n && matchChaosSymbol cs (k - n) then
        j := k - n
      else
        return false
    return false

/-- Drop a chaos symbol that introduces an ability (CR 207.4).

On a plane card the symbol is printed to the left of the ability that
triggers whenever chaos ensues. Towashi's chaos ability is read the same way
with or without a leading `{CHAOS}`. A `{CHAOS}` later in the text still
names a face of the planar die (CR 107.12) and stays.
-/
def stripChaosSymbol (s : String) : String :=
  Id.run do
    let cs := s.toList.toArray
    let mut acc : Array Char := Array.mkEmpty cs.size
    let mut i : Nat := 0
    let mut changed := false
    while i < cs.size do
      if matchChaosSymbol cs i && chaosIntro cs i then
        changed := true
        i := skipWs cs (i + chaosSymbolLiteral.size)
      else
        acc := acc.push cs[i]!
        i := i + 1
    if changed then (String.ofList acc.toList).trimAscii.copy else s

/-- Drop every CR 207.2c ability word (`Landfall —`, `Spell Mastery —`,
`Council's Dilemma —`, `Descend 4 —`), including one quoted inside a later
ability. Other em-dash labels are left alone. -/
def stripAbilityWords (s : String) : String :=
  Id.run do
    let cs := s.toList.toArray
    let mut acc : Array Char := Array.mkEmpty cs.size
    let mut i : Nat := 0
    let mut changed := false
    while i < cs.size do
      match abilityWordEnd cs i with
      | some stop =>
        changed := true
        i := stop
      | none =>
        acc := acc.push cs[i]!
        i := i + 1
    if changed then (String.ofList acc.toList).trimAscii.copy else s

/-- Drop a leading em-dash label that is not rules text.

CR 207.2c ability words are removed wherever they introduce an ability.
Flavor words (CR 207.2d) and keyword labels this engine prints the same way
(`Boast —`, `Power-up —`) are removed once from the front so the remaining
text can be matched. A one-word label is treated the same way.
-/
def stripAbilityWord (s : String) : String :=
  let s := stripAbilityWords s
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

/-- Replace each `old` with `new` in order. Most pairs are absent from a given
line, and `contains` does not copy the string the way `replace` does. -/
def applyReplacements (s : String) (pairs : List (String × String)) : String :=
  pairs.foldl (fun acc p => if acc.contains p.fst then acc.replace p.fst p.snd else acc) s

/-- Replace an isolated word.

Linear in `s` and `new`. The previous list walk dropped a suffix and appended
one character per step, which made Oracle normalization quadratic and dominated
catalog builds.
-/
def replaceWord (s old new : String) : String :=
  if old.isEmpty || !s.contains old then s
  else
    Id.run do
      let chars := s.toList.toArray
      let needle := old.toList.toArray
      let fresh := new.toList.toArray
      let n := needle.size
      let mut acc : Array Char := Array.mkEmpty chars.size
      let mut i : Nat := 0
      while i < chars.size do
        let mut matched := true
        let mut k : Nat := 0
        while matched && k < n do
          if i + k >= chars.size || chars[i + k]! != needle[k]! then
            matched := false
          else
            k := k + 1
        let beforeOk := i == 0 || !(chars[i - 1]!.isAlphanum)
        let afterOk :=
          i + n >= chars.size || !(chars[i + n]!.isAlphanum)
        if matched && beforeOk && afterOk then
          acc := acc ++ fresh
          i := i + n
        else
          acc := acc.push chars[i]!
          i := i + 1
      String.ofList acc.toList

/-- Lowercase, drop reminders, and replace the card's name with `this`. -/
def prepareLine (cardName : String) (s : String) : String :=
  let s := dropReminderText s
  let s := stripChaosSymbol s
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

/-- Comparable form of one ability unit, before phrase equivalences.
Argument parsing uses this so a subtype written out in full (`other Elf
creatures`) stays a hole instead of being rewritten to one fixed plural. -/
def normalizeStructural (cardName : String) (s : String) : String :=
  let s := prepareLine cardName s
  let s := replaceNumberWords s
  let s := keepSignificant s
  let s := collapseWs s
  dropLeadingThis s

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

#guard dropReminderText
  "Menace (This creature can't be blocked except by two or more creatures.)" ==
  "Menace"
#guard dropReminderText
  "(This creature can't be blocked except by two or more creatures.)" == ""
#guard dropReminderText "({T}: Add {U} or {R}.)" == ""
#guard dropReminderText "Menace (outer (inner) still reminder)" == "Menace"
#guard dropReminderText
  "Kicker {1}{R} (You may pay an additional {2}{G} as you cast this spell.)" ==
  "Kicker {1}{R}"
#guard normalizeUnit "Bear"
  "Menace (This creature can't be blocked except by two or more creatures.)" ==
  "menace"
#guard normalizeUnit "Bear"
  "(This creature can't be blocked except by two or more creatures.)" == ""
#guard normalizeUnit "Saga"
  "(As this Saga enters and after your draw step, add a lore counter. Sacrifice after III.)" ==
  ""

-- CR 207.2c: every ability word is ignored, in any case, wherever it labels
-- an ability. A word that merely shares letters with an ability word is not.
#guard abilityWords.length == 62
#guard abilityWords.head? == some "adamant"
#guard abilityWords.getLast? == some "will of the council"
#guard abilityWords.all fun w =>
  stripAbilityWords s!"{w} — Draw a card." == "Draw a card."
#guard abilityWords.all fun w =>
  stripAbilityWords s!"{w.map Char.toUpper} — Draw a card." == "Draw a card."
#guard abilityWords.all fun w =>
  normalizeUnit "Card" s!"{w} — Whenever a land you control enters, draw a card." ==
    normalizeUnit "Card" "Whenever a land you control enters, draw a card."
#guard stripAbilityWords
    ("Council" ++ String.ofList [Char.ofNat 0x2019] ++
      "s Dilemma — Starting with you, each player votes.") ==
  "Starting with you, each player votes."
#guard stripAbilityWords "Descend 4 — {T}: Add {B}{B}." == "{T}: Add {B}{B}."
#guard stripAbilityWords "Descend 8 — {T}: Add {U}{B}." == "{T}: Add {U}{B}."
#guard stripAbilityWords "Descend — This creature gets +1/+1." ==
  "Descend — This creature gets +1/+1."
#guard stripAbilityWords
    "This Saga gains \"Landfall — Whenever a land you control enters, draw a card.\"" ==
  "This Saga gains \"Whenever a land you control enters, draw a card.\""
#guard stripAbilityWords "Ferocious — Landfall — Whenever you attack, draw a card." ==
  "Whenever you attack, draw a card."
#guard stripAbilityWords "Choose one — • Draw a card. • Create a Treasure token." ==
  "Choose one — • Draw a card. • Create a Treasure token."
#guard stripAbilityWords "You have the will of the council in hand." ==
  "You have the will of the council in hand."
#guard stripAbilityWords
    "You have the will of the council — Starting with you, each player votes." ==
  "You have the will of the council — Starting with you, each player votes."
#guard stripAbilityWords "I — Spell Mastery — Draw a card." == "I — Draw a card."
#guard stripAbilityWords "• Pack Tactics — Draw a card." == "• Draw a card."
#guard stripAbilityWords "afraid — draw a card." == "afraid — draw a card."
#guard stripAbilityWords "Boast — {1}: Draw a card." == "Boast — {1}: Draw a card."
#guard stripAbilityWords "Power-up — {4}{W}: Draw a card." ==
  "Power-up — {4}{W}: Draw a card."
#guard stripAbilityWord "Boast — {1}: Draw a card." == "{1}: Draw a card."
#guard stripAbilityWord "Power-up — {4}{W}: Draw a card." == "{4}{W}: Draw a card."
#guard stripAbilityWord "Street Justice — Exile target creature." ==
  "Exile target creature."

-- CR 207.4: the chaos symbol to the left of a chaos ability has no rules
-- meaning. Towashi is read as the ability that follows the symbol.
#guard stripChaosSymbol
    "{CHAOS} Whenever chaos ensues, distribute three +1/+1 counters among one, two, or three target creatures you control." ==
  "Whenever chaos ensues, distribute three +1/+1 counters among one, two, or three target creatures you control."
#guard stripChaosSymbol
    "{chaos} Whenever chaos ensues, distribute three +1/+1 counters among one, two, or three target creatures you control." ==
  "Whenever chaos ensues, distribute three +1/+1 counters among one, two, or three target creatures you control."
#guard stripChaosSymbol "{Chaos}Menace" == "Menace"
#guard stripChaosSymbol "{CHAOS}" == ""
#guard stripChaosSymbol "{CHAOS} {CHAOS} Whenever chaos ensues, draw a card." ==
  "Whenever chaos ensues, draw a card."
#guard stripChaosSymbol
    "This gains \"{CHAOS} Whenever chaos ensues, draw a card.\"" ==
  "This gains \"Whenever chaos ensues, draw a card.\""
#guard stripChaosSymbol "• {CHAOS} Draw a card." == "• Draw a card."
#guard stripChaosSymbol "{C} Whenever chaos ensues, draw a card." ==
  "{C} Whenever chaos ensues, draw a card."
#guard stripChaosSymbol "Whenever you roll {CHAOS}, draw a card." ==
  "Whenever you roll {CHAOS}, draw a card."
#guard stripAbilityWords (stripChaosSymbol
    "{CHAOS} Landfall — Whenever a land you control enters, draw a card.") ==
  "Whenever a land you control enters, draw a card."
#guard normalizeUnit "Towashi"
    "{CHAOS} Whenever chaos ensues, distribute three +1/+1 counters among one, two, or three target creatures you control." ==
  normalizeUnit "Towashi"
    "Whenever chaos ensues, distribute three +1/+1 counters among one, two, or three target creatures you control."
#guard normalizeUnit "Towashi"
    "Whenever you roll {CHAOS}, draw a card." ==
  "whenever you roll {chaos} draw a card"
#guard normalizeUnit "Saga"
    "This Saga gains \"Spell Mastery — Whenever a land you control enters, draw a card.\"" ==
  normalizeUnit "Saga"
    "This Saga gains \"Whenever a land you control enters, draw a card.\""

end Mtg.Engine.OracleNorm
