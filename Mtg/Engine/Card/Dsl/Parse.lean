import Mtg.Engine.Color
import Mtg.Engine.TypeLine
import Mtg.Engine.Card.Dsl.Elements
import Mtg.Engine.Card.Dsl.Compile

/-!
# Parsing printed cards into the DSL

Functions that read Oracle text back into the clause vocabulary.
`parseOracleText` reads a printed card (name, mana cost, type line,
power/toughness, rules text, and an Adventure face) into a
`TraditionalCardDefinition`.
-/

namespace Mtg.Engine

namespace TypeName

def ofCard : CardType → TypeName
  | .artifact => .artifact
  | .battle => .battle
  | .creature => .creature
  | .enchantment => .enchantment
  | .instant => .instant
  | .land => .land
  | .planeswalker => .planeswalker
  | .sorcery => .sorcery
  | .kindred => .kindred
  | .dungeon => .dungeon
  | .plane => .plane
  | .phenomenon => .phenomenon
  | .vanguard => .vanguard
  | .scheme => .scheme
  | .conspiracy => .conspiracy

end TypeName

namespace PrintedKeyword

def all : List PrintedKeyword :=
  [.flash, .haste, .vigilance, .flying, .cantBeBlocked, .menace, .hexproof,
   .indestructible, .reach, .trample, .deathtouch, .defender, .lifelink,
   .firstStrike, .islandwalk, .storied, .doubleStrike, .prowess, .ascend,
   .shadow, .changeling]

def parse (s : String) : Option PrintedKeyword :=
  let s := s.trimAscii.copy.map Char.toLower
  all.find? (fun k => k.oracleName == s)

end PrintedKeyword

/-- Legendary short name: the printed name before the first comma (CR 201.3). -/
private def shortCardName (cardName : String) : String :=
  match cardName.splitOn ", " with
  | head :: _ => if head.isEmpty then cardName else head
  | [] => cardName

/-! Parser: printed card text back into a `.card` clause list. -/

private def cardTypes : List CardType :=
  [.artifact, .battle, .creature, .enchantment, .instant, .land, .planeswalker,
   .sorcery, .kindred, .dungeon, .plane, .phenomenon, .vanguard, .scheme,
   .conspiracy]

private def supertypes : List Supertype :=
  [.basic, .legendary, .ongoing, .snow, .world]

private def parseCardType (s : String) : Option CardType :=
  let s := s.trimAscii.copy.map Char.toLower
  cardTypes.find? (fun t => t.englishName.map Char.toLower == s)

private def parseSupertype (s : String) : Option Supertype :=
  let s := s.trimAscii.copy.map Char.toLower
  supertypes.find? (fun t => t.englishName.map Char.toLower == s)

private def parseCardSubtype (s : String) : Option CardSubtype :=
  match s.trimAscii.copy.map Char.toLower with
  | "dwarf" => some .dwarf
  | "citizen" => some .citizen
  | "scout" => some .scout
  | "insect" => some .insect
  | "adventure" => some .adventure
  | "bird" => some .bird
  | "soldier" => some .soldier
  | "halfling" => some .halfling
  | "rogue" => some .rogue
  | "human" => some .human
  | "cleric" => some .cleric
  | _ => none

private def colorOfLetter : String → Option Color
  | "W" => some .white
  | "U" => some .blue
  | "B" => some .black
  | "R" => some .red
  | "G" => some .green
  | _ => none

private def parseSymbol (body : String) : Option CostSymbol :=
  match body.splitOn "/" with
  | [a, b] => do
    let ca ← colorOfLetter a
    let cb ← colorOfLetter b
    return .hybrid ca cb
  | _ =>
    match colorOfLetter body with
    | some c => some (.mono c)
    | none =>
      match body with
      | "C" => some .colorless
      | "X" => some .x
      | _ =>
        match body.toNat? with
        | some n => some (.generic n)
        | none => none

/-- `inside` is true while reading the body of a `{...}` symbol. -/
private def parseManaChars (cs : List Char) : Option (List CostSymbol) :=
  go cs false [] []
where
  go : List Char → Bool → List Char → List CostSymbol → Option (List CostSymbol)
    | [], false, _, out => some out.reverse
    | [], true, _, _ => none
    | '{' :: rest, false, _, out => go rest true [] out
    | '{' :: _, true, _, _ => none
    | '}' :: rest, true, acc, out =>
      match parseSymbol (String.ofList acc.reverse) with
      | some sym => go rest false [] (sym :: out)
      | none => none
    | '}' :: _, false, _, _ => none
    | c :: rest, true, acc, out => go rest true (c :: acc) out
    | _ :: _, false, _, _ => none

private def parseManaRun (s : String) : Option (List CostSymbol) :=
  parseManaChars s.toList

private def splitNameAndCost (line : String) : Option (String × List CostSymbol) := do
  let line := line.trimAscii.copy
  let tokens := line.splitOn " " |>.filter (· != "")
  match tokens.dropLast, tokens.getLast? with
  | _, none => none
  | init, some last =>
    if last.startsWith "{" then
      let cost ← parseManaRun last
      return (String.intercalate " " init, cost)
    else
      return (line, [])

private def wordsOf (s : String) : List String :=
  s.splitOn " " |>.map (·.trimAscii.copy) |>.filter (· != "")

private def parseTypeWords : List String → Option (List Supertype × List CardType)
  | [] => none
  | w :: rest =>
    match parseSupertype w with
    | some s => do
      let (supers, tys) ← parseTypeWords rest
      return (s :: supers, tys)
    | none => do
      let tys ← (w :: rest).mapM parseCardType
      return ([], tys)

private def splitDash (line : String) : List String :=
  let em := line.splitOn " — "
  if em.length > 1 then em
  else
    let hy := line.splitOn " - "
    if hy.length > 1 then hy else [line]

private def parseTypeLine (line : String) :
    Option (List Supertype × List CardType × List CardSubtype) := do
  match splitDash line with
  | [left] =>
    let (supers, tys) ← parseTypeWords (wordsOf left)
    return (supers, tys, [])
  | [left, right] =>
    let (supers, tys) ← parseTypeWords (wordsOf left)
    let subs ← (wordsOf right).mapM parseCardSubtype
    return (supers, tys, subs)
  | _ => none

private def parseIntToken (s : String) : Option Int :=
  if s.startsWith "-" then
    match (s.drop 1).toNat? with
    | some n => some (- Int.ofNat n)
    | none => none
  else
    match s.toNat? with
    | some n => some (Int.ofNat n)
    | none => none

private def parsePT (line : String) : Option (Int × Int) := do
  match line.splitOn "/" with
  | [a, b] =>
    let p ← parseIntToken (a.trimAscii.copy)
    let t ← parseIntToken (b.trimAscii.copy)
    return (p, t)
  | _ => none

private def stripParens (s : String) : String :=
  let rec go (cs : List Char) (depth : Nat) (acc : List Char) : List Char :=
    match cs with
    | [] => acc.reverse
    | '(' :: rest =>
      let acc :=
        match depth, acc with
        | 0, ' ' :: tail => tail
        | _, _ => acc
      go rest (depth + 1) acc
    | ')' :: rest =>
      let depth := if depth == 0 then 0 else depth - 1
      go rest depth acc
    | c :: rest =>
      if depth == 0 then go rest 0 (c :: acc) else go rest depth acc
  (String.ofList (go s.toList 0 [])).trimAscii.copy

private def stripTrailingDot (s : String) : String :=
  let s := s.trimAscii.copy
  if s.endsWith "." then (s.dropEnd 1).trimAscii.copy else s

private def dropPrefixCI (s pre : String) : Option String :=
  let rec go (a b : List Char) : Option (List Char) :=
    match b, a with
    | [], rest => some rest
    | _ :: _, [] => none
    | p :: ps, c :: cs =>
      if p.toLower == c.toLower then go cs ps else none
  match go s.toList pre.toList with
  | some rest => some (String.ofList rest).trimAscii.copy
  | none => none

private def stripSuffixCI? (s suffix : String) : Option String :=
  let sl := s.map Char.toLower
  let su := suffix.map Char.toLower
  if sl.endsWith su then
    some ((s.dropEnd suffix.length).trimAscii.copy)
  else none

private def splitEnglishList (s : String) : List String :=
  let s := s.replace ", and " ", "
  let s := s.replace " and " ", "
  s.splitOn "," |>.map (·.trimAscii.copy) |>.filter (· != "")

private def parseDisjunction (s : String) : Option (List ObjectRef) := do
  let parts := s.splitOn " or " |>.map (·.trimAscii.copy) |>.filter (· != "")
  match parts with
  | [] => none
  | [one] =>
    let t ← parseCardType one
    return [.cardType (TypeName.ofCard t)]
  | many =>
    let ts ← many.mapM parseCardType
    return [.or (ts.map (fun t => ObjectRef.cardType (TypeName.ofCard t)))]

private def parseNoun (noun : String) : Option (List ObjectRef) := do
  let (core, who) :=
    if let some core := stripSuffixCI? noun " you control" then
      (core, some PlayerRef.you)
    else if let some core := stripSuffixCI? noun " an opponent controls" then
      (core, some PlayerRef.opponent)
    else
      (noun, none)
  let quals ← parseDisjunction (core.map Char.toLower)
  let tail :=
    match who with
    | some p => [ObjectRef.controlledBy p]
    | none => []
  return quals ++ tail

private def parseDuration (s : String) : Option Duration :=
  match s.trimAscii.copy.map Char.toLower with
  | "end of turn" => some .endOfTurn
  | _ => none

private def singularize (s : String) : String :=
  let s := s.trimAscii.copy.map Char.toLower
  if s.endsWith "s" && s.length > 1 then (s.dropEnd 1).copy else s

private def parsePluralDisjunction (s : String) : Option (List ObjectRef) := do
  let parts := s.splitOn " or " |>.map (·.trimAscii.copy) |>.filter (· != "")
  match parts with
  | [] => none
  | [one] =>
    let t ← parseCardType (singularize one)
    return [.cardType (TypeName.ofCard t)]
  | many =>
    let ts ← many.mapM (fun w => parseCardType (singularize w))
    return [.or (ts.map (fun t => ObjectRef.cardType (TypeName.ofCard t)))]

private def parseGetSubject (noun : String) : Option (List ObjectRef) := do
  let (core, who) :=
    if let some core := stripSuffixCI? noun " you control" then
      (core, some PlayerRef.you)
    else if let some core := stripSuffixCI? noun " an opponent controls" then
      (core, some PlayerRef.opponent)
    else
      (noun, none)
  let quals ← parsePluralDisjunction core
  let tail :=
    match who with
    | some p => [ObjectRef.controlledBy p]
    | none => []
  return quals ++ tail

private def parseSignedStat (s : String) : Option Int :=
  let s := s.trimAscii.copy
  if s.startsWith "+" then
    match (s.drop 1).toNat? with
    | some n => some (Int.ofNat n)
    | none => none
  else
    parseIntToken s

private def parseStatMod (s : String) : Option StatMod := do
  match s.splitOn "/" with
  | [a, b] =>
    let p ← parseSignedStat a
    let t ← parseSignedStat b
    return .plusPowerToughness p t
  | _ => none

private def splitOnce (sep : String) (s : String) : Option (String × String) :=
  match s.splitOn sep with
  | head :: tail =>
    if tail.isEmpty then none
    else some (head, String.intercalate sep tail)
  | [] => none

private def parseGetUntil (line : String) : Option TextEffect := do
  let line := stripTrailingDot (stripParens line)
  let (subject, after) ← splitOnce " get " line
  let (bonus, durText) ← splitOnce " until " after
  let dur ← parseDuration durText
  let mod ← parseStatMod bonus
  let quals ← parseGetSubject subject
  return .getUntil quals [mod] dur

private def parseCostFor (line : String) : Option TextEffect := do
  let line := stripTrailingDot (stripParens line)
  let (costText, effectText) ← splitOnce ": " line
  let cost ← parseManaRun costText
  let effect ← parseGetUntil effectText
  return .costFor [.mana cost] [effect]

private def parseGainUntil (line : String) : Option TextEffect := do
  let line := stripTrailingDot (stripParens line)
  let rest ← dropPrefixCI line "target "
  match rest.splitOn " gains " with
  | [noun, after] =>
    let parts := after.splitOn " until "
    let kwText := String.intercalate " until " parts.dropLast
    match parts.getLast? with
    | none => none
    | some durText =>
      if parts.length < 2 then none
      else do
        let dur ← parseDuration durText
        let kws ← (splitEnglishList kwText).mapM PrintedKeyword.parse
        let quals ← parseNoun noun
        return .gainUntil [.target quals] (kws.map GrantedAbility.keyword) dur
  | _ => none

private def parseCountWord (s : String) : Option Nat :=
  match s.trimAscii.copy.map Char.toLower with
  | "one" => some 1
  | "two" => some 2
  | "three" => some 3
  | "four" => some 4
  | "five" => some 5
  | _ => s.toNat?

private def parseTargetCount (s : String) : Option TargetCount := do
  match s.splitOn " or " |>.map (·.trimAscii.copy) |>.filter (· != "") with
  | [a, b] =>
    let lo ← parseCountWord a
    let hi ← parseCountWord b
    return .or lo hi
  | _ => none

/-- `Tap one or two target creatures.` -/
private def parseTap (line : String) : Option TextEffect := do
  let line := stripTrailingDot (stripParens line)
  let rest ← dropPrefixCI line "Tap "
  let (countText, noun) ← splitOnce " target " rest
  let count ← parseTargetCount countText
  let quals ← parseGetSubject noun
  return .tap [.targets count quals]

private def parseMaybeTappedNoun (noun : String) : Option (List ObjectRef) := do
  let (tapped, core) :=
    if let some core := dropPrefixCI noun "tapped " then
      (true, core)
    else
      (false, noun)
  let quals ← parseNoun core
  return (if tapped then [ObjectRef.tapped] else []) ++ quals

private def parseCastIf (s : String) : Option CastIf := do
  let rest ← dropPrefixCI s "it targets "
  let noun :=
    if let some n := dropPrefixCI rest "an " then n
    else if let some n := dropPrefixCI rest "a " then n
    else rest
  let qs ← parseMaybeTappedNoun noun
  return .targeting .it qs

/-- `This spell costs {3} less to cast if it targets a tapped creature.` -/
private def parseCostLess (line : String) : Option TextEffect := do
  let line := stripTrailingDot (stripParens line)
  let rest ← dropPrefixCI line "This spell costs "
  let (costText, condText) ← splitOnce " less to cast if " rest
  let cost ← parseManaRun costText
  let cond ← parseCastIf condText
  return .costLessToCastIf [.this, .spell] cost cond

private def parseTarget (s : String) : Option ObjectRef := do
  let rest ← dropPrefixCI s "target "
  let qs ← parseMaybeTappedNoun rest
  return .target qs

/-- `{Name} deals 5 damage to target creature.` The subject is `.thisCardName`
when it is the card’s name. -/
private def parseDealDamage (cardName : String) (line : String) : Option TextEffect := do
  let line := stripTrailingDot (stripParens line)
  let rest ← dropPrefixCI line s!"{cardName} deals "
  let (nText, tgtText) ← splitOnce " damage to " rest
  let n ← nText.toNat?
  let tgt ← parseTarget tgtText
  return .dealDamage [.thisCardName] n [tgt]

private def parseAttackSubject (s : String) : Option (List ObjectRef) := do
  if let some rest := dropPrefixCI s "this " then
    let t ← parseCardType rest
    return [.this, .cardType (TypeName.ofCard t)]
  else
    parseNoun s

private def parseAttackRestrictions (s : String) : Option (List ObjectRef) :=
  let s := s.trimAscii.copy
  if s.isEmpty then some [] else none

/-- `this creature attacks` with no further restriction. -/
private def parseAttackTrigger (s : String) : Option TriggerExpr := do
  let (subject, rest) ← splitOnce " attacks" s
  let who ← parseAttackSubject subject
  let restrictions ← parseAttackRestrictions rest
  return .attack who restrictions

private def parseGetsSubject (s : String) : Option (List ObjectRef) :=
  match s.trimAscii.copy.map Char.toLower with
  | "it" => some [.it]
  | _ => none

/-- `other creature you control` is `[.other, .cardType .creature, .controlledBy .you]`. -/
private def parseForEachSubject (s : String) : Option (List ObjectRef) := do
  let (other, core) :=
    if let some core := dropPrefixCI s "other " then
      (true, core)
    else
      (false, s)
  let quals ← parseNoun core
  return (if other then [ObjectRef.other] else []) ++ quals

/-- `it gets +1/+1 until end of turn for each other creature you control`. -/
private def parseGetForEachUntil (s : String) : Option TextEffect := do
  let (subject, after) ←
    match splitOnce " gets " s with
    | some pair => some pair
    | none => splitOnce " get " s
  let who ← parseGetsSubject subject
  let (left, eachText) ← splitOnce " for each " after
  let (bonus, durText) ← splitOnce " until " left
  let dur ← parseDuration durText
  let mod ← parseStatMod bonus
  let each ← parseForEachSubject eachText
  return .getForEachUntil who [mod] each dur

private def parseOrdinalWord (s : String) : Option Nat :=
  match s.trimAscii.copy.map Char.toLower with
  | "first" => some 1
  | "second" => some 2
  | "third" => some 3
  | "fourth" => some 4
  | "fifth" => some 5
  | other => other.toNat?

/-- `you draw your second card each turn` is `[.drawCard [.you] [.ordinalEach 2 .turn]]`. -/
private def parseDrawTrigger (s : String) : Option TriggerExpr := do
  let (who, rest) ←
    if let some rest := dropPrefixCI s "you draw your " then
      some (([.you] : List PlayerRef), rest)
    else if let some rest := dropPrefixCI s "an opponent draws their " then
      some (([.opponent] : List PlayerRef), rest)
    else
      none
  let (ordText, period) ← splitOnce " card each " rest
  guard (period == "turn")
  let n ← parseOrdinalWord ordText
  return .drawCard who [.ordinalEach n .turn]

private def parseWheneverTrigger (s : String) : Option TriggerExpr :=
  match parseAttackTrigger s with
  | some trig => some trig
  | none => parseDrawTrigger s

/-- `this creature` is `[.this, .cardType .creature]`. -/
private def parseThisTyped (s : String) : Option (List ObjectRef) := do
  let rest ← dropPrefixCI s "this "
  let t ← parseCardType rest
  return [.this, .cardType (TypeName.ofCard t)]

/-- `put a +1/+1 counter on this creature`. -/
private def parsePutCounter (s : String) : Option TextEffect := do
  let rest ← dropPrefixCI s "put a +1/+1 counter on "
  let objs ← parseThisTyped rest
  return .putCounter 1 .plusOnePlusOne objs

private def parseWheneverEffect (s : String) : Option TextEffect :=
  match parseGetForEachUntil s with
  | some effect => some effect
  | none => parsePutCounter s

/-- `Whenever this creature attacks, it gets +1/+1 until end of turn for each other creature you control.`
`Whenever you draw your second card each turn, put a +1/+1 counter on this creature.` -/
private def parseWhenever (line : String) : Option TextEffect := do
  let line := stripTrailingDot (stripParens line)
  let rest ← dropPrefixCI line "Whenever "
  let (trigText, effectText) ← splitOnce ", " rest
  let trig ← parseWheneverTrigger trigText
  let effect ← parseWheneverEffect effectText
  return .whenever [trig] [effect]

/-- `{short name} enters`, where the short name is the card name before a comma. -/
private def parseEntersTrigger (cardName : String) (s : String) : Option TriggerExpr := do
  let (who, rest) ← splitOnce " enters" s
  guard (rest.trimAscii.copy.isEmpty)
  guard (who == shortCardName cardName)
  return .enter [.thisCardName]

/-- `draw a card` or `draw N cards`. -/
private def parseDrawClause (s : String) : Option TextEffect := do
  let rest ← dropPrefixCI s "draw "
  if rest == "a card" then
    return .draw 1
  else
    let (nText, tail) ← splitOnce " " rest
    guard (tail == "cards")
    let n ← nText.toNat?
    guard (n != 1)
    return .draw n

/-- `When Bilbo Baggins enters, draw a card.` -/
private def parseWhen (cardName : String) (line : String) : Option TextEffect := do
  let line := stripTrailingDot (stripParens line)
  let rest ← dropPrefixCI line "When "
  let (trigText, effectText) ← splitOnce ", " rest
  let trig ← parseEntersTrigger cardName trigText
  let effect ← parseDrawClause effectText
  return .when [trig] [effect]

/-- `Scry 2.` -/
private def parseScry (line : String) : Option TextEffect := do
  let line := stripTrailingDot (stripParens line)
  let rest ← dropPrefixCI line "Scry "
  let n ← rest.toNat?
  return .scry n

private def parseTypeName (s : String) : Option TypeName :=
  match s.trimAscii.copy.map Char.toLower with
  | "equipment" => some .equipment
  | other => (parseCardType other).map TypeName.ofCard

/-- A card type, `.equipment`, or a named subtype such as `.cardSubtype .dwarf`. -/
private def parseQualifierWord (s : String) : Option ObjectRef :=
  match parseCardSubtype s with
  | some sub => some (.cardSubtype sub)
  | none => (parseTypeName s).map ObjectRef.cardType

private def dropArticle (s : String) : Option String :=
  if let some r := dropPrefixCI s "an " then some r
  else if let some r := dropPrefixCI s "a " then some r
  else some s

/-- `Equipment you control` or `Dwarf`, including a leading article. -/
private def parseTypedControlled (s : String) : Option (List ObjectRef) := do
  let noun ← dropArticle s
  let (core, who) :=
    if let some core := stripSuffixCI? noun " you control" then
      (core, some PlayerRef.you)
    else if let some core := stripSuffixCI? noun " an opponent controls" then
      (core, some PlayerRef.opponent)
    else
      (noun, none)
  let qual ← parseQualifierWord core
  let tail :=
    match who with
    | some p => [ObjectRef.controlledBy p]
    | none => []
  return [qual] ++ tail

/-- `Untap target creature you control`. -/
private def parseUntap (s : String) : Option TextEffect := do
  let rest ← dropPrefixCI s "Untap "
  let tgt ← parseTarget rest
  return .untap [tgt]

/-- `It gets +2/+2 until end of turn`, with no “for each” tail. -/
private def parseItGets (s : String) : Option TextEffect := do
  let (subject, after) ← splitOnce " gets " s
  guard (subject.trimAscii.copy.map Char.toLower == "it")
  let (bonus, durText) ← splitOnce " until " after
  guard !((durText.splitOn " ").contains "for")
  let dur ← parseDuration durText
  let mod ← parseStatMod bonus
  return .getUntil [.it] [mod] dur

/-- `you may attach an Equipment you control to it`. -/
private def parseYouMayAttach (s : String) : Option TextEffect := do
  let rest ← dropPrefixCI s "you may attach "
  let (objText, destText) ← splitOnce " to " rest
  let quals ← parseTypedControlled objText
  guard (destText.trimAscii.copy.map Char.toLower == "it")
  return .may [.you] [.attachTo [.oneOf quals] [.it]]

/-- `If it's a Dwarf, you may attach an Equipment you control to it`. -/
private def parseIfMay (s : String) : Option TextEffect := do
  let rest ← dropPrefixCI s "If "
  let (condText, thenText) ← splitOnce ", " rest
  let condRest ←
    match dropPrefixCI condText "it's " with
    | some r => some r
    | none =>
      match dropPrefixCI condText "it’s " with
      | some r => some r
      | none => dropPrefixCI condText "it is "
  let quals ← parseTypedControlled condRest
  let act ← parseYouMayAttach thenText
  return .if [.is [.it] quals] [act]

private def parseSequenceStep (s : String) : Option TextEffect :=
  let s := stripTrailingDot s
  match parseUntap s with
  | some e => some e
  | none =>
    match parseItGets s with
    | some e => some e
    | none => parseIfMay s

/-- Several Oracle sentences in one rules line, as a `.sequence`. -/
private def parseSequence (line : String) : Option TextEffect := do
  let line := stripTrailingDot (stripParens line)
  let parts := line.splitOn ". " |>.map (·.trimAscii.copy) |>.filter (· != "")
  guard (parts.length ≥ 2)
  let steps ← parts.mapM parseSequenceStep
  return .sequence steps

private def parseKeywordLine (line : String) : Option (List TextEffect) := do
  let parts := splitEnglishList line
  if parts.isEmpty then none
  else
    let kws ← parts.mapM PrintedKeyword.parse
    return kws.map TextEffect.keyword

private def parseBody (cardName : String) (lines : List String) : Option (List TextEffect) :=
  lines.foldlM (fun effects line =>
    let cleaned := stripTrailingDot (stripParens line)
    if cleaned.isEmpty then
      pure effects
    else
      match parseSequence cleaned with
      | some e => pure (effects ++ [e])
      | none =>
        match parseWhenever cleaned with
        | some e => pure (effects ++ [e])
        | none =>
          match parseWhen cardName cleaned with
          | some e => pure (effects ++ [e])
          | none =>
            match parseScry cleaned with
            | some e => pure (effects ++ [e])
            | none =>
              match parseCostFor cleaned with
              | some e => pure (effects ++ [e])
              | none =>
                match parseGetUntil cleaned with
                | some e => pure (effects ++ [e])
                | none =>
                  match parseGainUntil cleaned with
                  | some e => pure (effects ++ [e])
                  | none =>
                    match parseTap cleaned with
                    | some e => pure (effects ++ [e])
                    | none =>
                      match parseCostLess cleaned with
                      | some e => pure (effects ++ [e])
                      | none =>
                        match parseDealDamage cardName cleaned with
                        | some e => pure (effects ++ [e])
                        | none =>
                          match parseKeywordLine cleaned with
                          | some ks => pure (effects ++ ks)
                          | none => none) []

private def faceClauses (name : String) (cost : List CostSymbol)
    (supers : List Supertype) (tys : List CardType) (subs : List CardSubtype)
    (pt : Option (Int × Int)) (effects : List TextEffect) : List CardClause :=
  [.name name, .manaCost cost]
    ++ tys.map CardClause.type
    ++ supers.map CardClause.supertype
    ++ subs.map CardClause.subtype
    ++ (match pt with
        | some (p, t) => [CardClause.power p, .toughness t]
        | none => [])
    ++ (match effects with
        | [] => []
        | es => [.textBox es])

private def parseFace (lines : List String) : Option (List CardClause) := do
  let lines := lines.filter (· != "")
  match lines with
  | nameLine :: typeLine :: rest =>
    let (name, cost) ← splitNameAndCost nameLine
    let (supers, tys, subs) ← parseTypeLine typeLine
    let (pt, body) :=
      match rest with
      | p :: more =>
        match parsePT p with
        | some pt => (some pt, more)
        | none => (none, rest)
      | [] => (none, [])
    let effects ← parseBody name body
    return faceClauses name cost supers tys subs pt effects
  | _ => none

private def splitAdventure (lines : List String) :
    List String × Option (List String) :=
  let rec go (acc : List String) : List String → List String × Option (List String)
    | [] => (acc.reverse, none)
    | l :: rest =>
      if l == "//ADV//" then
        (acc.reverse, some rest)
      else if l.startsWith "//ADV//" then
        let extra := (l.drop "//ADV//".length).trimAscii.copy
        let rest := if extra.isEmpty then rest else extra :: rest
        (acc.reverse, some rest)
      else
        go (l :: acc) rest
  go [] lines

/-- Parse a printed card into a traditional-card definition.

The text is the Oracle card as printed: name and mana cost, type line,
optional `power/toughness`, rules text, then an optional `//ADV//` Adventure
face in the same shape. Reminder parentheticals are ignored. The clause list
is emitted in canonical order (name, mana cost, types, supertypes, subtypes,
power, toughness, text box, alternative) so it can be compared to
a definition written in that order. Keyword lines become `.keyword`
instructions in that text box. `Tap one or two target …` becomes `.tap`.
`This spell costs {N} less to cast if it targets …` becomes
`.costLessToCastIf` with `[.this, .spell]`. `{Name} deals N damage to target …` becomes
`.dealDamage` with `.thisCardName` when the subject is the card’s name.
`Whenever this creature attacks, it gets … for each other creature you control`
becomes `.whenever` with `.attack` and `getForEachUntil`.
`Whenever you draw your second card each turn, put a +1/+1 counter on this creature.`
becomes `.whenever` with `.drawCard` and `.putCounter`.
`When {name} enters, draw a card.` becomes `.when` with `.enter` and `.draw`.
`Scry N.` becomes `.scry`.
`Untap target creature you control. It gets … If it's a Dwarf, you may attach
an Equipment you control to it.` becomes `.sequence` with `.untap`, `.getUntil`,
and `.if` with `[.cardSubtype .dwarf]`.
-/
def parseOracleText (text : String) : Option TraditionalCardDefinition := do
  let lines :=
    text.splitOn "\n" |>.map fun l => (l.replace "\r" "").trimAscii.copy
  let (mainLines, adv) := splitAdventure lines
  let main ← parseFace mainLines
  let extra ←
    match adv with
    | none => pure ([] : List CardClause)
    | some advLines =>
      let inner ← parseFace advLines
      pure [CardClause.alternative inner]
  return .card (main ++ extra)

/-! Parser pieces used by the catalog guards. -/

#guard PrintedKeyword.all.all (fun k => PrintedKeyword.parse k.oracleName == some k)

#guard parseManaRun "{1}{W}" == some [.generic 1, .mono .white]

#guard parseManaRun "{W}" == some [.mono .white]

#guard parseGainUntil
    "Target artifact or creature you control gains hexproof and indestructible until end of turn. (Then exile this card. You may cast the creature later from exile.)" ==
  some (.gainUntil
    [.target [.or [.cardType .artifact, .cardType .creature], .controlledBy .you]]
    [.keyword .hexproof, .keyword .indestructible]
    .endOfTurn)

#guard parseCostFor
    "{3}{W}: Creatures you control get +1/+1 until end of turn." ==
  some (.costFor
    [.mana [.generic 3, .mono .white]]
    [.getUntil [.cardType .creature, .controlledBy .you]
      [.plusPowerToughness 1 1] .endOfTurn])

#guard parseKeywordLine "Lifelink" == some [.keyword .lifelink]

#guard parseKeywordLine "Flying, lifelink" == some [.keyword .flying, .keyword .lifelink]

#guard parseTap
    "Tap one or two target creatures. (Then exile this card. You may cast the creature later from exile.)" ==
  some (.tap [.targets (.or 1 2) [.cardType .creature]])

#guard parseCostLess
    "This spell costs {3} less to cast if it targets a tapped creature." ==
  some (.costLessToCastIf [.this, .spell] [.generic 3]
    (.targeting .it [.tapped, .cardType .creature]))

#guard parseDealDamage "Magnificent End"
    "Magnificent End deals 5 damage to target creature." ==
  some (.dealDamage [.thisCardName] 5 [.target [.cardType .creature]])

#guard parseWhenever
    "Whenever this creature attacks, it gets +1/+1 until end of turn for each other creature you control." ==
  some (.whenever
    [.attack [.this, .cardType .creature] []]
    [.getForEachUntil [.it] [.plusPowerToughness 1 1]
      [.other, .cardType .creature, .controlledBy .you] .endOfTurn])

#guard parseWhenever
    "Whenever you draw your second card each turn, put a +1/+1 counter on this creature." ==
  some (.whenever
    [.drawCard [.you] [.ordinalEach 2 .turn]]
    [.putCounter 1 .plusOnePlusOne [.this, .cardType .creature]])

#guard parseSequence
    "Untap target creature you control. It gets +2/+2 until end of turn. If it's a Dwarf, you may attach an Equipment you control to it." ==
  some (.sequence [
    .untap [.target [.cardType .creature, .controlledBy .you]],
    .getUntil [.it] [.plusPowerToughness 2 2] .endOfTurn,
    .if
      [.is [.it] [.cardSubtype .dwarf]]
      [.may [.you] [.attachTo [.oneOf [.cardType .equipment, .controlledBy .you]] [.it]]]])

#guard parseWhen "Bilbo Baggins, Burglar"
    "When Bilbo Baggins enters, draw a card." ==
  some (.when [.enter [.thisCardName]] [.draw 1])

#guard parseScry
    "Scry 2. (Then exile this card. You may cast the creature later from exile.)" ==
  some (.scry 2)

end Mtg.Engine
