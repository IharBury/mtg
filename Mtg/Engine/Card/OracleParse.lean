import Mtg.Engine.Card.Definition

/-!
# Oracle text to card parts

`parseOracleParts` reads printed Oracle text into as many `CardPart`s as
it can. Unrecognized lines are skipped, so a card can be parsed before
the grammar covers every ability.

Currently recognized:

- comma-separated keyword lines (`Lifelink`, `Flying, deathtouch`),
  including a trailing reminder parenthetical
- Gatherer `//ADV//` Adventure faces: `Name {cost}`, a type line, then
  rules text
- mana symbols `{N}`, `{W}` `{U}` `{B}` `{R}` `{G}`, `{C}`, `{X}`, `{S}`,
  and hybrid `{W/U}`
- `Target <permanent type or …> [you control] gains <keywords> until end of turn.`
- `{cost}: <permanents> [you control] get +N/+N until end of turn.`
- `Tap one or two target <permanents>.`
- `Untap target <permanents> [you control].`
- `It gets +P/+T until end of turn.` (the previous target)
- `If it's a <subtype>, you may attach a/an <subtype> you control to it.`
- `This spell costs {N} less to cast if it targets a tapped creature.`
- `<this card> deals N damage to target <permanent type>.`
  The source is `this`, `this <type>`, the card's name, or the short name
  before a comma (`Bilbo Baggins` for `Bilbo Baggins, Burglar`, CR 201.5)
- `Whenever this creature attacks, it gets +P/+T until end of turn for each other creature you control.`
- `When <this card> enters, draw a card.` / `draw N cards.`
  The entering object is `this`, `this <type>`, the card's name, or that short name
- `Scry N.`
-/

namespace Mtg.Engine

namespace OracleParts

def lowerAscii : String → String := CardDef.lowerAscii

def stripReminderParenthetical : String → String := CardDef.stripReminderParenthetical

def stripTrailingPeriod (s : String) : String :=
  let s := s.trimAscii.copy
  if s.endsWith "." then (s.dropEnd 1).trimAscii.copy else s

def natOfDigits? (s : String) : Option Nat :=
  let cs := s.toList
  if cs.isEmpty || !cs.all Char.isDigit then none
  else some (cs.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)

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
        match s.splitOn "/" with
        | [a, b] =>
          match colorOfLetter? a, colorOfLetter? b with
          | some ca, some cb => some (.hybrid ca cb)
          | _, _ => none
        | _ => none

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

def keywordOfOracle? (s : String) : Option Keyword :=
  match lowerAscii (s.trimAscii.copy) with
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
  | _ => none

/-- A line that is only modeled keywords, e.g. `Lifelink` or `Flying, deathtouch`. -/
def keywordParts? (line : String) : Option (List CardPart) :=
  let cleaned := stripTrailingPeriod (stripReminderParenthetical line)
  if cleaned.isEmpty then none
  else
    let tokens :=
      cleaned.splitOn "," |>.map (·.trimAscii.copy) |>.filter (· != "")
    match tokens.foldl (fun acc t =>
      match acc, keywordOfOracle? t with
      | some parts, some k => some (parts ++ [CardPart.ability (.keyword k)])
      | _, _ => none) (some []) with
    | some [] => none
    | parts => parts

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
  .detective, .dinosaur, .doctor, .dog, .dragon, .druid, .dwarf, .elemental,
  .elephant, .elf, .elk, .equipment, .eternal, .food, .forest, .frog, .gamma,
  .gate, .giant, .goblin, .god, .halfling, .hero, .horror, .horse, .human,
  .infinity, .inhuman, .insect, .island, .knight, .kree, .mercenary, .merfolk,
  .minotaur, .mountain, .mutant, .nightmare, .ninja, .noble, .ogre, .orc,
  .peasant, .performer, .pilot, .pirate, .plains, .plan, .rabbit, .ranger,
  .robot, .rogue, .saga, .samurai, .scientist, .scout, .shaman, .shapeshifter,
  .skrull, .snake, .soldier, .sorcerer, .spider, .spirit, .spy, .squirrel,
  .stone, .swamp, .troll, .treasure, .vampire, .vehicle, .villain, .warlock,
  .warrior, .whale, .wizard, .wolf, .wraith, .wurm, .zombie
]

def subtypeOfOracle? (s : String) : Option CardSubtype :=
  let s := lowerAscii s
  cardSubtypes.find? (fun st => lowerAscii (toString st) == s)

def partOfTypeWord? (w : String) : Option CardPart :=
  match supertypeOfOracle? w with
  | some s => some (.supertype s)
  | none =>
    match typeOfOracle? w with
    | some t => some (.type t)
    | none =>
      match subtypeOfOracle? w with
      | some st => some (.subtype st)
      | none => none

def isCardTypePart : CardPart → Bool
  | .type _ => true
  | _ => false

/-- A type line such as `Instant — Adventure` or `Legendary Creature — Dwarf Scout`.
Every word must be a supertype, card type, or subtype, and at least one word
must be a card type. -/
def parseTypeLine (line : String) : List CardPart :=
  let line := stripReminderParenthetical line
  let words := (line.splitOn "—").flatMap fun side =>
    let side := side.trimAscii.copy
    side.splitOn " " |>.filterMap fun w =>
      let w := w.trimAscii.copy
      if w.isEmpty then none else some w
  if words.isEmpty then []
  else
    let parsed := words.map partOfTypeWord?
    if parsed.any (·.isNone) then []
    else
      let parts := parsed.filterMap (fun x => x)
      if parts.any isCardTypePart then parts else []

/-- Split `Concerted Care {1}{W}` into the name and the brace text. -/
def splitNameCost (line : String) : String × String :=
  match line.splitOn "{" with
  | [] => (line.trimAscii.copy, "")
  | name :: rest =>
    if rest.isEmpty then (name.trimAscii.copy, "")
    else (name.trimAscii.copy, "{" ++ String.intercalate "{" rest)

def parseNameAndCost (line : String) : List CardPart :=
  let line := stripReminderParenthetical line
  let (name, costText) := splitNameCost line
  let nameParts : List CardPart := if name.isEmpty then [] else [.name name]
  if costText.isEmpty then nameParts
  else
    match parseManaSymbols costText with
    | some syms =>
      if syms.isEmpty then nameParts else nameParts ++ [.manaCost syms]
    | none => nameParts

def selectorOfTypes : List CardType → Selector
  | [t] => .cardType t
  | ts => .union (ts.map fun t => .cardType t)

/-- Permanent card types joined by `or`, e.g. `artifact or creature`. -/
def typesInPhrase (s : String) : Option (List CardType) :=
  let parts := s.splitOn " or " |>.map (·.trimAscii.copy) |>.filter (· != "")
  let types := parts.map typeOfOracle?
  if parts.isEmpty || types.any (·.isNone) then none
  else
    let ts := types.filterMap (fun x => x)
    if ts.all CardType.isPermanentType then some ts else none

/-- `target artifact or creature you control` as a battlefield selector. -/
def parseTargetPhrase (s : String) : Option Selector :=
  let s := lowerAscii (s.trimAscii.copy)
  let lead := "target "
  if !s.startsWith lead then none
  else
    let rest := (s.drop lead.length).trimAscii.copy
    let youControl := " you control"
    let (obj, controlled) :=
      if rest.endsWith youControl then
        ((rest.dropEnd youControl.length).trimAscii.copy, true)
      else
        (rest, false)
    match typesInPhrase obj with
    | none => none
    | some ts =>
      let tail : List Selector :=
        if controlled then [.controlled (.controller .this)] else []
      some (.intersection ([.permanent, selectorOfTypes ts] ++ tail))

/-- Keywords in `hexproof and indestructible` or `haste, flying, and trample`. -/
def parseKeywordPhrase (s : String) : Option (List Keyword) :=
  let s := lowerAscii (s.trimAscii.copy)
  let commaParts := s.splitOn ", " |>.map (·.trimAscii.copy) |>.filter (· != "")
  let tokens := commaParts.flatMap fun part =>
    let part :=
      if part.startsWith "and " then (part.drop "and ".length).trimAscii.copy else part
    part.splitOn " and " |>.map (·.trimAscii.copy) |>.filter (· != "")
  if tokens.isEmpty then none
  else
    let kws := tokens.map keywordOfOracle?
    if kws.any (·.isNone) then none else some (kws.filterMap (fun x => x))

def gainEffects (n : Nat) (sel : Selector) (kws : List Keyword) : List ContinuousEffect :=
  match kws with
  | [] => []
  | k :: rest =>
    .gainAbility (.target n sel) (.keyword k) ::
      rest.map (fun k => .gainAbility (.targetReference n) (.keyword k))

def parseSignedInt (s : String) : Option Int :=
  let s := s.trimAscii.copy
  let (neg, digits) :=
    if s.startsWith "+" then (false, (s.drop 1).trimAscii.copy)
    else if s.startsWith "-" then (true, (s.drop 1).trimAscii.copy)
    else (false, s)
  match natOfDigits? digits with
  | none => none
  | some n =>
    let i : Int := n
    some (if neg then -i else i)

/-- A printed power and toughness change, such as `+1/+1`. -/
def parsePowerToughness (s : String) : Option (Int × Int) :=
  match s.trimAscii.copy.splitOn "/" with
  | [p, t] =>
    match parseSignedInt p, parseSignedInt t with
    | some p, some t => some (p, t)
    | _, _ => none
  | _ => none

/-- `creatures you control` or `other creature you control` as a battlefield
selector. A trailing `s` on a card type is the plural (`creatures`). -/
def parseControlledPhrase (s : String) : Option Selector :=
  let s := lowerAscii (s.trimAscii.copy)
  let youControl := " you control"
  let (obj0, controlled) :=
    if s.endsWith youControl then
      ((s.dropEnd youControl.length).trimAscii.copy, true)
    else
      (s, false)
  let otherLead := "other "
  let (obj, other) :=
    if obj0.startsWith otherLead then
      ((obj0.drop otherLead.length).trimAscii.copy, true)
    else
      (obj0, false)
  match typesInPhrase obj with
  | none => none
  | some ts =>
    let head : List Selector :=
      (if other then [.not .this] else []) ++ [.permanent, selectorOfTypes ts]
    let tail : List Selector :=
      if controlled then [.controlled (.controller .this)] else []
    some (.intersection (head ++ tail))

/-- `it` / `this creature`, or a controlled-permanent phrase. -/
def parsePumpWho (s : String) : Option Selector :=
  match lowerAscii (s.trimAscii.copy) with
  | "it" | "this" | "this creature" => some (.source .this)
  | _ => parseControlledPhrase s

/-- `<objects> get +P/+T until end of turn [for each <objects>].` -/
def parsePumpUntilEndOfTurn (sentence : String) : Option CardAction :=
  let s := lowerAscii (stripTrailingPeriod sentence)
  let forEachMark := " until end of turn for each "
  let suffix := "until end of turn"
  let (body, among?) :=
    match s.splitOn forEachMark with
    | [pre, among] =>
      let among := among.trimAscii.copy
      if among.isEmpty then (pre.trimAscii.copy, none)
      else (pre.trimAscii.copy, some among)
    | _ =>
      if s.endsWith suffix then
        ((s.dropEnd suffix.length).trimAscii.copy, none)
      else
        ("", none)
  if body.isEmpty && among?.isNone && !s.endsWith suffix then none
  else
    let pieces :=
      match body.splitOn " gets " with
      | [who, pt] => some (who, pt)
      | _ =>
        match body.splitOn " get " with
        | [who, pt] => some (who, pt)
        | _ => none
    match pieces with
    | none => none
    | some (who, pt) =>
      match parsePumpWho who, parsePowerToughness pt, among? with
      | some sel, some (p, t), none =>
        some (.continuous [.addPowerToughness sel (Value.int p) (Value.int t)] .endOfTurn)
      | some sel, some (p, t), some amongText =>
        match parseControlledPhrase amongText with
        | some among =>
          some (.continuous
            [.addPowerToughnessPer sel among (Value.int p) (Value.int t)] .endOfTurn)
        | none => none
      | _, _, _ => none

/-- `Whenever this creature attacks, it gets +1/+1 until end of turn for each
other creature you control.` -/
def parseAttackTriggered (line : String) : Option CardPart :=
  let line := stripTrailingPeriod (stripReminderParenthetical line)
  let s := lowerAscii line
  let lead := "whenever this creature attacks, "
  if !s.startsWith lead then none
  else
    match parsePumpUntilEndOfTurn (line.drop lead.length).trimAscii.copy with
    | some action => some (.ability (.triggered (.attack .this .all) action))
    | none => none

/-- `{3}{W}: Creatures you control get +1/+1 until end of turn.` -/
def parseActivatedAbility (line : String) : Option CardPart :=
  let line := stripTrailingPeriod (stripReminderParenthetical line)
  match line.splitOn ": " with
  | [costText, effect] =>
    match parseManaSymbols costText, parsePumpUntilEndOfTurn effect with
    | some syms, some action =>
      if syms.isEmpty then none
      else some (.ability (.activated [.mana syms] action))
    | _, _ => none
  | _ => none

/-- `This spell costs {3} less to cast if it targets a tapped creature.`
The reduction is a static ability that functions on the stack (CR 604.2). -/
def parseStackCostReduction (line : String) : Option CardPart :=
  let s := lowerAscii (stripTrailingPeriod (stripReminderParenthetical line))
  let lead := "this spell costs "
  let tail := " less to cast if it targets a tapped creature"
  if !s.startsWith lead || !s.endsWith tail then none
  else
    let mid := ((s.drop lead.length).dropEnd tail.length).trimAscii.copy
    match parseManaSymbols mid with
    | some syms =>
      if syms.isEmpty then none
      else
        some (.ability (
          .stackStatic
            (.if
              (.targetsIncludeAny
                .this
                (.intersection [
                  .permanent,
                  .cardType .creature,
                  .tapped]))
              [.reduceCost .this [.mana syms]])))
    | none => none

def englishSmall? (s : String) : Option Nat :=
  match lowerAscii (s.trimAscii.copy) with
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

/-- `one`, `two`, or `one or two`. -/
def parseCountRange (s : String) : Option Range :=
  match s.trimAscii.copy.splitOn " or " with
  | [a, b] =>
    match englishSmall? a, englishSmall? b with
    | some lo, some hi => some (.range (Value.nat lo) (Value.nat hi))
    | _, _ => none
  | [a] =>
    match englishSmall? a with
    | some n => some (.range (Value.nat n) (Value.nat n))
    | none => none
  | _ => none

/-- `Tap one or two target creatures.` The target number is `n`. -/
def parseTap (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := lowerAscii (stripTrailingPeriod sentence)
  let lead := "tap "
  if !s.startsWith lead then none
  else
    let rest := (s.drop lead.length).trimAscii.copy
    match rest.splitOn " target " with
    | [countText, obj] =>
      match parseCountRange countText, typesInPhrase obj with
      | some r, some ts =>
        let sel := .intersection [.permanent, selectorOfTypes ts]
        some (.tap (.targets n r sel), n + 1)
      | _, _ => none
    | _ => none

/-- `Untap target <permanents> [you control].` The target number is `n`. -/
def parseUntap (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := lowerAscii (stripTrailingPeriod sentence)
  let lead := "untap "
  if !s.startsWith lead then none
  else
    match parseTargetPhrase (s.drop lead.length).trimAscii.copy with
    | some sel => some (.untap (.target n sel), n + 1)
    | none => none

/-- `It gets +P/+T until end of turn.` refers to the last target (`n - 1`). -/
def parseItGetsUntilEndOfTurn (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if n <= 1 then none
  else
    let s := lowerAscii (stripTrailingPeriod sentence)
    let lead := "it gets "
    let suffix := " until end of turn"
    if !s.startsWith lead || !s.endsWith suffix then none
    else
      let pt := ((s.drop lead.length).dropEnd suffix.length).trimAscii.copy
      match parsePowerToughness pt with
      | some (p, t) =>
        some (
          .continuous
            [.addPowerToughness (.targetReference (n - 1)) (Value.int p) (Value.int t)]
            .endOfTurn,
          n)
      | none => none

/-- Drop a leading `a` / `an`. -/
def dropArticle? (s : String) : Option String :=
  let s := s.trimAscii.copy
  let sl := lowerAscii s
  if sl.startsWith "an " then some (s.drop 3).trimAscii.copy
  else if sl.startsWith "a " then some (s.drop 2).trimAscii.copy
  else none

/-- `If it's a Dwarf, you may attach an Equipment you control to it.`
The previous target (`n - 1`) is the host. -/
def parseIfItsSubtypeMayAttach (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if n <= 1 then none
  else
    let s := lowerAscii (stripTrailingPeriod sentence)
    let lead := "if it's "
    let mid := ", you may attach "
    let tail := " you control to it"
    if !s.startsWith lead || !s.endsWith tail then none
    else
      let body := ((s.drop lead.length).dropEnd tail.length).trimAscii.copy
      match body.splitOn mid with
      | [hostArt, attachArt] =>
        match dropArticle? hostArt, dropArticle? attachArt with
        | some hostName, some attachName =>
          match subtypeOfOracle? hostName, subtypeOfOracle? attachName with
          | some hostSt, some attachSt =>
            let host := Selector.targetReference (n - 1)
            some (
              .if
                (.anySubtype host hostSt)
                [
                  .optional
                    (.attach
                      (.selected
                        (.controller .this)
                        (.range 1 1)
                        (.intersection [
                          .permanent,
                          .subtype attachSt,
                          .controlled (.controller .this)]))
                      host)
                ],
              n)
          | _, _ => none
        | _, _ => none
      | _ => none

/-- `this` or `this <type>`, such as `this creature` or `this spell`. -/
def isGenericSelf (subject : String) : Bool :=
  let s := lowerAscii (subject.trimAscii.copy)
  if s == "this" then true
  else if !s.startsWith "this " then false
  else
    let rest := (s.drop "this ".length).trimAscii.copy
    if (rest.splitOn " ").length != 1 then false
    else
      (typeOfOracle? rest).isSome || (subtypeOfOracle? rest).isSome ||
        rest == "permanent" || rest == "spell"

/-- The printed name, plus the short name before a comma.
`Bilbo Baggins, Burglar` refers to itself as `Bilbo Baggins` (CR 201.5). -/
def selfNames (cardName : String) : List String :=
  let name := lowerAscii (cardName.trimAscii.copy)
  if name.isEmpty then []
  else
    let short :=
      match name.splitOn "," with
      | head :: _ => head.trimAscii.copy
      | [] => name
    if short.isEmpty || short == name then [name] else [name, short]

/-- `subject` is this card: a generic `this` phrase, or one of `cardName`'s
self-names. -/
def refersToSelf (cardName subject : String) : Bool :=
  let subject := lowerAscii (subject.trimAscii.copy)
  isGenericSelf subject || (selfNames cardName).contains subject

/-- `<this card> deals 5 damage to target creature.` The source must be this
card. The target number is `n`. -/
def parseDealDamage (cardName : String) (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  let s := lowerAscii (stripTrailingPeriod sentence)
  match s.splitOn " deals " with
  | [who, rest] =>
    if !refersToSelf cardName who then none
    else
      match rest.splitOn " damage to target " with
      | [amt, obj] =>
        match natOfDigits? (amt.trimAscii.copy), typesInPhrase obj with
        | some amount, some ts =>
          let sel := .intersection [.permanent, selectorOfTypes ts]
          some (.dealDamage .this (.target n sel) (.nat amount), n + 1)
        | _, _ => none
      | _ => none
  | _ => none

/-- `Target … gains … until end of turn.` The target number is `n`. -/
def parseGainsUntilEndOfTurn (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := lowerAscii (stripTrailingPeriod sentence)
  let suffix := "until end of turn"
  if !s.endsWith suffix then none
  else
    let body := (s.dropEnd suffix.length).trimAscii.copy
    match body.splitOn " gains " with
    | [who, gained] =>
      match parseTargetPhrase who, parseKeywordPhrase gained with
      | some sel, some kws =>
        some (.continuous (gainEffects n sel kws) .endOfTurn, n + 1)
      | _, _ => none
    | _ => none

/-- `a card`, `one card`, or `two cards` as how many cards are drawn. -/
def parseCardCount (s : String) : Option Nat :=
  let s := lowerAscii (s.trimAscii.copy)
  if s == "a card" then some 1
  else
    let counted :=
      if s.endsWith " cards" then
        some ((s.dropEnd " cards".length).trimAscii.copy, true)
      else if s.endsWith " card" then
        some ((s.dropEnd " card".length).trimAscii.copy, false)
      else
        none
    match counted with
    | none => none
    | some (countText, plural) =>
      match englishSmall? countText with
      | some n =>
        if n == 0 then none
        else if n == 1 then
          if plural then none else some n
        else if plural then some n else none
      | none => none

/-- `When Bilbo Baggins enters, draw a card.` The subject is this card. -/
def parseEnterDraw (cardName : String) (line : String) : Option CardPart :=
  let line := stripTrailingPeriod (stripReminderParenthetical line)
  let s := lowerAscii line
  let lead := "when "
  if !s.startsWith lead then none
  else
    match (s.drop lead.length).trimAscii.copy.splitOn " enters, " with
    | [subject, effect] =>
      if !refersToSelf cardName subject || !effect.startsWith "draw " then none
      else
        match parseCardCount (effect.drop "draw ".length).trimAscii.copy with
        | some n =>
          some (.ability
            (.triggered (.enter .this) (.draw (.controller .this) (Value.nat n))))
        | none => none
    | _ => none

/-- `Scry 2.` Does not choose a target, so the target number stays `n`. -/
def parseScry (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := lowerAscii (stripTrailingPeriod sentence)
  let lead := "scry "
  if !s.startsWith lead then none
  else
    match englishSmall? (s.drop lead.length).trimAscii.copy with
    | some k =>
      if k == 0 then none
      else some (.scry (.controller .this) (Value.nat k), n)
    | none => none

def sentences (text : String) : List String :=
  (stripReminderParenthetical text).splitOn ". "
    |>.map stripTrailingPeriod
    |>.filter (· != "")

def actionsFromText (cardName : String) (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  let rec go (ss : List String) (n : Nat) (acc : List CardAction) : List CardAction × Nat :=
    match ss with
    | [] => (acc, n)
    | s :: rest =>
      match parseGainsUntilEndOfTurn s n with
      | some (a, n') => go rest n' (acc ++ [a])
      | none =>
        match parseTap s n with
        | some (a, n') => go rest n' (acc ++ [a])
        | none =>
          match parseUntap s n with
          | some (a, n') => go rest n' (acc ++ [a])
          | none =>
            match parseItGetsUntilEndOfTurn s n with
            | some (a, n') => go rest n' (acc ++ [a])
            | none =>
              match parseIfItsSubtypeMayAttach s n with
              | some (a, n') => go rest n' (acc ++ [a])
              | none =>
                match parseDealDamage cardName s n with
                | some (a, n') => go rest n' (acc ++ [a])
                | none =>
                  match parseScry s n with
                  | some (a, n') => go rest n' (acc ++ [a])
                  | none => go rest n acc
  let (actions, n') := go (sentences text) n []
  if actions.isEmpty then none else some (actions, n')

/-- Split off a Gatherer `//ADV//` Adventure section. A marker that shares
its line with the Adventure name keeps that name. -/
def splitAdventure (lines : List String) : List String × List String :=
  go lines []
where
  go : List String → List String → List String × List String
    | [], acc => (acc.reverse, [])
    | line :: rest, acc =>
      if line == "//ADV//" then (acc.reverse, rest)
      else if line.startsWith "//ADV//" then
        let restLine := (line.drop "//ADV//".length).trimAscii.copy
        let adv := if restLine.isEmpty then rest else restLine :: rest
        (acc.reverse, adv)
      else
        go rest (line :: acc)

def parseMainLines (cardName : String) (lines : List String) (n : Nat) :
    List CardPart × Nat :=
  match lines with
  | [] => ([], n)
  | line :: rest =>
    let (parts, n') :=
      match keywordParts? line with
      | some parts => (parts, n)
      | none =>
        match parseActivatedAbility line with
        | some part => ([part], n)
        | none =>
        match parseStackCostReduction line with
        | some part => ([part], n)
        | none =>
          match parseAttackTriggered line with
          | some part => ([part], n)
          | none =>
            match parseEnterDraw cardName line with
            | some part => ([part], n)
            | none =>
              match actionsFromText cardName line n with
              | some (actions, n') => ([CardPart.actions actions], n')
              | none => ([], n)
    let (more, n'') := parseMainLines cardName rest n'
    (parts ++ more, n'')

def nameOfParts (parts : List CardPart) : Option String :=
  parts.findSome? fun
    | .name n => some n
    | _ => none

def parseAdventure (cardName : String) (lines : List String) (n : Nat) :
    Option (List CardPart) :=
  match lines with
  | [] => none
  | nameLine :: rest =>
    let nameParts := parseNameAndCost nameLine
    let (typeParts, effectLines) :=
      match rest with
      | line :: more =>
        let parsed := parseTypeLine line
        if parsed.isEmpty then ([], rest) else (parsed, more)
      | [] => ([], [])
    -- An Adventure face refers to itself by its own name.
    let faceName := nameOfParts nameParts |>.getD cardName
    let actionParts : List CardPart :=
      match actionsFromText faceName (String.intercalate " " effectLines) n with
      | some (actions, _) => [.actions actions]
      | none => []
    let parts := nameParts ++ typeParts ++ actionParts
    if parts.isEmpty then none else some parts

end OracleParts

open OracleParts

/-- Parse printed Oracle text into `CardPart`s. Keyword lines, Gatherer
`//ADV//` Adventure faces, “gains … until end of turn” effects,
`{cost}: … get +P/+T until end of turn` abilities,
`Tap one or two target creatures` effects,
`Untap target creature you control` plus a following `It gets +P/+T`
and optional `If it's a <subtype>, you may attach …` clause,
stack cost reductions
(`This spell costs {N} less … if it targets a tapped creature`),
`<this card> deals N damage to target creature` effects,
`Whenever this creature attacks, it gets +P/+T until end of turn for each
other creature you control` triggers,
`When <this card> enters, draw a card` triggers, and
`Scry N` effects are read into parts.
`name` is the card being parsed. Text that uses that name, or the short name
before a comma, means this card, as do `this` and `this <type>`.
Lines the grammar does not cover are omitted. -/
def parseOracleParts (name : String) (text : String) : List CardPart :=
  let lines :=
    text.splitOn "\n" |>.map (·.trimAscii.copy) |>.filter (· != "")
  let (main, adv) := splitAdventure lines
  let (mainParts, n) := parseMainLines name main 1
  match parseAdventure name adv n with
  | some alt => mainParts ++ [.alternative alt]
  | none => mainParts

#guard parseOracleParts (name := "") "Lifelink" == [.ability (.keyword .lifelink)]
#guard parseOracleParts (name := "") "Flying, deathtouch" ==
  [.ability (.keyword .flying), .ability (.keyword .deathtouch)]
#guard parseOracleParts (name := "")
  "Reach (This creature can block creatures with flying.)" ==
  [.ability (.keyword .reach)]
#guard parseOracleParts (name := "") "Whenever this creature attacks, draw a card." == []
#guard parseOracleParts (name := "") "When another creature enters, draw a card." == []
#guard parseOracleParts (name := "") "When Bilbo Baggins enters, draw a card." == []
#guard parseOracleParts (name := "Gandalf") "When Bilbo Baggins enters, draw a card." == []
#guard parseOracleParts (name := "Bilbo") "When Bilbo Baggins enters, draw a card." == []
#guard parseOracleParts (name := "Bilbo Baggins, Burglar")
    "When Bilbo Baggins enters, draw a card." ==
  [.ability (.triggered (.enter .this) (.draw (.controller .this) 1))]
#guard parseOracleParts (name := "Bilbo Baggins, Burglar")
    "When Bilbo Baggins, Burglar enters, draw a card." ==
  [.ability (.triggered (.enter .this) (.draw (.controller .this) 1))]
#guard parseOracleParts (name := "") "When this creature enters, draw two cards." ==
  [.ability (.triggered (.enter .this) (.draw (.controller .this) 2))]
#guard parseOracleParts (name := "") "Scry 2." ==
  [.actions [.scry (.controller .this) 2]]
#guard parseOracleParts (name := "")
  "Scry 2. (Then exile this card. You may cast the creature later from exile.)" ==
  [.actions [.scry (.controller .this) 2]]
#guard parseOracleParts (name := "")
  "Target creature you control gains hexproof until end of turn." ==
  [.actions [
    .continuous
      [.gainAbility
        (.target 1 (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)]))
        (.keyword .hexproof)]
      .endOfTurn]]
#guard parseOracleParts (name := "")
  "{3}{W}: Creatures you control get +1/+1 until end of turn." ==
  [.ability (
    .activated
      [.mana [.generic 3, .mono .white]]
      (.continuous
        [.addPowerToughness
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)]) (Value.int 1) (Value.int 1)]
        .endOfTurn))]
#guard parseOracleParts (name := "") "Tap one or two target creatures." ==
  [.actions [
    .tap (.targets 1 (.range 1 2) (.intersection [.permanent, .cardType .creature]))]]
#guard parseOracleParts (name := "") "//ADV//\nSpew Flame {4}{R}\nSorcery — Adventure" ==
  [.alternative [
    .name "Spew Flame",
    .manaCost [.generic 4, .mono .red],
    .type .sorcery,
    .subtype .adventure]]
#guard parseOracleParts (name := "")
  "This spell costs {3} less to cast if it targets a tapped creature." ==
  [.ability (
    .stackStatic
      (.if
        (.targetsIncludeAny
          .this
          (.intersection [
            .permanent,
            .cardType .creature,
            .tapped]))
        [.reduceCost .this [.mana [.generic 3]]]))]
#guard parseOracleParts (name := "") "Magnificent End deals 5 damage to target creature." == []
#guard parseOracleParts (name := "Shock") "Magnificent End deals 5 damage to target creature." == []
#guard parseOracleParts (name := "Magnificent End")
    "Magnificent End deals 5 damage to target creature." ==
  [.actions [
    .dealDamage
      .this
      (.target 1 (.intersection [.permanent, .cardType .creature]))
      (.nat 5)]]
#guard parseOracleParts (name := "") "This spell deals 5 damage to target creature." ==
  [.actions [
    .dealDamage
      .this
      (.target 1 (.intersection [.permanent, .cardType .creature]))
      (.nat 5)]]
#guard parseOracleParts (name := "Smaug, the Great Calamity")
    "//ADV//\nSpew Flame {4}{R}\nSorcery — Adventure\nSpew Flame deals 5 damage to target creature." ==
  [.alternative [
    .name "Spew Flame",
    .manaCost [.generic 4, .mono .red],
    .type .sorcery,
    .subtype .adventure,
    .actions [
      .dealDamage
        .this
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        (.nat 5)]]]
#guard parseOracleParts (name := "")
  "Flying\nWhenever this creature attacks, it gets +1/+1 until end of turn for each other creature you control." ==
  [
    .ability (.keyword .flying),
    .ability (
      .triggered
        (.attack .this .all)
        (.continuous
          [.addPowerToughnessPer
            (.source .this)
            (.intersection [
              .not .this,
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)])
            (Value.int 1)
            (Value.int 1)]
          .endOfTurn))]
#guard parseOracleParts (name := "") "Untap target creature you control." ==
  [.actions [
    .untap
      (.target
        1
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)]))]]
#guard parseOracleParts (name := "")
  "Untap target creature you control. It gets +2/+2 until end of turn. If it's a Dwarf, you may attach an Equipment you control to it." ==
  [.actions [
    .untap
      (.target
        1
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)])),
    .continuous [.addPowerToughness (.targetReference 1) (Value.int 2) (Value.int 2)] .endOfTurn,
    .if
        (.anySubtype (.targetReference 1) .dwarf)
        [
          .optional
            (.attach
              (.selected
                (.controller .this)
                (.range 1 1)
                (.intersection [
                  .permanent,
                  .subtype .equipment,
                  .controlled (.controller .this)]))
              (.targetReference 1))
        ]]]

end Mtg.Engine
