import Mtg.Engine.Card.Definition

/-!
# Oracle text to card parts

`parseOracleParts` reads printed Oracle text into `CardPart`s.
The parse fails when any part of the text is not recognized, so a card
is not compiled with some of its Oracle text missing.

Currently recognized:

- comma-separated keyword lines (`Lifelink`, `Flying, deathtouch`),
  including a trailing reminder parenthetical
- Gatherer `//ADV//` Adventure faces: `Name {cost}`, a type line, then
  rules text
- mana symbols `{N}`, `{W}` `{U}` `{B}` `{R}` `{G}`, `{C}`, `{X}`, `{S}`,
  and hybrid `{W/U}`
- `Target <permanent type or …> [you control] gains <keywords> until end of turn.`
- `{cost}: <permanents> [you control] get +N/+N until end of turn.`
- `Pay N life: <permanents or this creature> get +P/+T until end of turn.`
  A following `Activate only once each turn` limits that ability (CR 602.5).
- `Tap one or two target <permanents>.`
- `Untap target <permanents> [you control].`
- `It gets +P/+T until end of turn.` (the previous target)
- `If it's a <subtype>, you may attach a/an <subtype> you control to it.`
- `This spell costs {N} less to cast if it targets a tapped creature.`
- `This spell costs {N} less to cast if it targets an attacking nontoken creature.`
- `This spell costs {N} less to cast if a creature died this turn.`
  The reduction is a static ability that functions on the stack (CR 604.2).
- `As an additional cost to cast this spell, sacrifice an <permanent type or …> or pay {N}.`
  The sacrifice and that much generic mana are alternatives (CR 601.2b).
  This functions while the spell is on the stack (CR 113.6 / 604.2).
- `Destroy target <permanent type or …>.`
- `Put a +1/+1 counter on up to one target <permanent type>.`
  Up to one target means zero or one (CR 115.1).
- `Target player gains N life.`
- `You gain N life.`
- `<this card> deals N damage to target <permanent type>.`
  The source is `this`, `this <type>`, the card's name, or the short name
  before a comma (`Bilbo Baggins` for `Bilbo Baggins, Burglar`, CR 201.5)
- `Whenever this creature attacks, it gets +P/+T until end of turn for each other creature you control.`
- `Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, you gain N life.`
  The ability word has no rules meaning (CR 207.2c). The “while” clause is
  part of the trigger condition (CR 603.2) and is not checked again on
  resolution. The word may be omitted.
- `When <this card> enters, draw a card.` / `draw N cards.`
  The entering object is `this`, `this <type>`, the card's name, or that short name
- `When <this card> dies, target <permanent type or …> an opponent controls gets P/T until end of turn.`
  The dying object is `this`, `this <type>`, the card's name, or that short name.
  `P/T` is a signed change such as -1 / -1
- `Whenever one or more other creatures die, scry N.`
  Those creatures die at the same time (CR 603.2c).
- `Whenever you draw your second card each turn, put a +1/+1 counter on this creature.`
- `Whenever you draw a card, put a +1/+1 counter on this creature.`
- `When <this card> enters, target opponent sacrifices a creature of their choice.`
  The entering object is `this`, `this <type>`, the card's name, or that short name.
  The opponent chooses which creature to sacrifice (CR 701.17a)
- `When <this card> enters, each opponent discards a card.`
- `When <this card> enters, he deals N damage divided as you choose among one, two, or three targets.`
  The source is a pronoun for the entering object (`he`, `she`, `it`, or `they`)
  or another reference to this card. Its controller divides the damage
  (CR 601.2d). `targets` with no type is any target. The counts are a
  positive contiguous range.
- `When <this card> enters, you may discard a card. If you do, draw N cards.`
  The draw happens only when that discard is taken.
- `Equipped creature gets +P/+T.`
- `Equip {cost}`
  A trailing reminder parenthetical is not rules text (CR 207.2)
- `Scry N.`
- `Target <permanent type> gets +P/+T until end of turn.`
- `Target <permanent type> gets +P/+T and gains <keywords> until end of turn.`
- `Target creature gets +P/+T until end of turn. If that creature would die this turn, exile it instead.`
  The pump and the replacement both last until end of turn. Dying is being
  put into a graveyard from the battlefield (CR 614.1).
- `<permanent types> target player controls get +P/+T until end of turn.`
  `P/T` may be negative, as in -1 / -1
- `Target player draws <count> cards and loses N life.`
- `Choose one —` followed by `•` modes:
  - `Counter target spell unless its controller pays {cost}.`
  - `Draw <count> cards, then discard <count> card(s).`
  - `Target <permanent type> gets +P/+T until end of turn.`
  - `Target <permanent type> gets +P/+T and gains <keywords> until end of turn.`
  - `Target creature gets +P/+T until end of turn. If that creature would die this turn, exile it instead.`
  - `<permanent types> target player controls get +P/+T until end of turn.`
  - `Target player draws <count> cards and loses N life.`
- `Counter target spell. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled.`
- `<this card> can't be blocked.`
  The subject is `this`, `this <type>`, the card's name, or the short name
  before a comma
- `<this card> can't block.`
  The subject is the same as for “can't be blocked”
- `When <this card> enters, exile up to one target card from an opponent's graveyard. Each opponent loses N life.`
- `{cost}, Sacrifice an <permanent type or …>: Return this card from your graveyard to your hand. Activate only as a sorcery.`
  Returning this card from a graveyard functions while the card is in that
  graveyard (CR 113.6), so the ability is `graveyardActivatedIf`
- `Whenever <this card> deals combat damage to a player, draw <count> cards, then discard <count> card(s).`
- `Exchange control of <count> target nonland permanents that share a card type.`
- `Target <permanent type>'s owner puts it on their choice of the top or bottom of their library.`
-/

namespace Mtg.Engine

namespace OracleParts

def lowerAscii : String → String := CardDef.lowerAscii

def stripReminderParenthetical : String → String := CardDef.stripReminderParenthetical

def stripTrailingPeriod (s : String) : String :=
  let s := s.trimAscii.copy
  if s.endsWith "." then (s.dropEnd 1).trimAscii.copy else s

def sentences (text : String) : List String :=
  (stripReminderParenthetical text).splitOn ". "
    |>.map stripTrailingPeriod
    |>.filter (· != "")

/-- Rules text of `line` after a reminder parenthetical is removed.
Empty when the line is only a reminder. -/
def rulesText (line : String) : String :=
  stripTrailingPeriod (stripReminderParenthetical line)

/-- Trimmed copy of `s`. -/
def copied (s : String) : String :=
  s.trimAscii.copy

/-- Case-folded Oracle text. -/
def norm (s : String) : String :=
  lowerAscii (copied s)

def normSentence (s : String) : String :=
  norm (stripTrailingPeriod s)

def normLine (line : String) : String :=
  normSentence (stripReminderParenthetical line)

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

/-- A line that is only modeled keywords, e.g. `Lifelink` or `Flying, deathtouch`.
One unrecognized word fails the line. -/
def keywordParts? (line : String) : Option (List CardPart) :=
  let cleaned := stripTrailingPeriod (stripReminderParenthetical line)
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
  (supertypeOfOracle? w).map CardPart.supertype <|>
    (typeOfOracle? w).map CardPart.type <|>
    (subtypeOfOracle? w).map CardPart.subtype

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
    match words.mapM partOfTypeWord? with
    | none => []
    | some parts => if parts.any isCardTypePart then parts else []

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
    match parseManaSymbols costText with
    | some syms =>
      if syms.isEmpty then none else some [.name name, .manaCost syms]
    | none => none

def selectorOfTypes : List CardType → Selector
  | [t] => .cardType t
  | ts => .union (ts.map fun t => .cardType t)

/-- Permanent card types joined by `or`, e.g. `artifact or creature`. -/
def typesInPhrase (s : String) : Option (List CardType) :=
  let parts := s.splitOn " or " |>.map (·.trimAscii.copy) |>.filter (· != "")
  if parts.isEmpty then none
  else
    match parts.mapM typeOfOracle? with
    | none => none
    | some ts => if ts.all CardType.isPermanentType then some ts else none

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
  if tokens.isEmpty then none else tokens.mapM keywordOfOracle?

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

/-- `Pay 2 life` (CR 118.3). The amount is a printed number. -/
def parsePayLife (s : String) : Option Nat :=
  let s := lowerAscii (s.trimAscii.copy)
  let lead := "pay "
  let tail := " life"
  if !s.startsWith lead || !s.endsWith tail then none
  else
    match natOfDigits? ((s.drop lead.length).dropEnd tail.length).trimAscii.copy with
    | some n => if n == 0 then none else some n
    | none => none

/-- A pump effect, optionally followed by `Activate only once each turn.` -/
def parseActivatedEffect (effect : String) : Option (CardAction × Bool) :=
  let sentences :=
    (stripReminderParenthetical effect).splitOn ". "
      |>.map stripTrailingPeriod
      |>.filter (· != "")
  let pump? (effect : String) (once : Bool) : Option (CardAction × Bool) :=
    match parsePumpUntilEndOfTurn effect with
    | some action => some (action, once)
    | none => none
  match sentences with
  | [effect] => pump? effect false
  | [effect, restrict] =>
    if lowerAscii restrict != "activate only once each turn" then none
    else pump? effect true
  | _ => none

/-- Wrap `action` as an activated ability. `once` is “only once each turn”
(CR 602.5), tracked by ability number `n`. -/
def activatedWithCost (n : Nat) (costs : List Cost) (action : CardAction) (once : Bool) :
    CardPart × Nat :=
  if once then
    (.ability
      (.abilityId n
        (.activatedIf
          (.didNotHappen (.abilityWithIdActivated n) .turnStart)
          costs
          action)),
     n + 1)
  else
    (.ability (.activated costs action), n)

/-- Mana cost, or a life payment when the text is not mana symbols.
An empty brace list fails rather than falling through to life. -/
def parseActivationCost (costText : String) : Option (List Cost) :=
  match parseManaSymbols costText with
  | some syms => if syms.isEmpty then none else some [.mana syms]
  | none => (parsePayLife costText).map fun life => [.life life]

/-- `{3}{W}: Creatures you control get +1/+1 until end of turn.`
Also `Pay 2 life: This creature gets +2/+2 until end of turn. Activate only once each turn.` -/
def parseActivatedAbility (line : String) (n : Nat) : Option (CardPart × Nat) :=
  let line := stripTrailingPeriod (stripReminderParenthetical line)
  match line.splitOn ": " with
  | [costText, effect] =>
    match parseActivatedEffect effect, parseActivationCost costText with
    | some (action, once), some costs =>
      some (activatedWithCost n costs action once)
    | _, _ => none
  | _ => none

/-- The creature named by a stack cost reduction: `a tapped creature` or
`an attacking nontoken creature`. -/
def costReductionTarget? (s : String) : Option Selector :=
  match lowerAscii (s.trimAscii.copy) with
  | "a tapped creature" =>
    some (.intersection [.permanent, .cardType .creature, .tapped])
  | "an attacking nontoken creature" =>
    some (.intersection [
      .permanent,
      .cardType .creature,
      .attacking .all,
      .not .token])
  | _ => none

/-- Nonempty mana cost in `this spell costs {cost} <mark> <condition>`. -/
def costsLessBy? (s mark : String) : Option (List ManaSymbol × String) :=
  match after? s "this spell costs " with
  | none => none
  | some rest =>
    match rest.splitOn mark with
    | [costText, cond] =>
      match parseManaSymbols costText with
      | some syms => if syms.isEmpty then none else some (syms, cond)
      | none => none
    | _ => none

/-- A stack static that reduces this spell's cost when `cond` holds (CR 604.2). -/
def reduceOnStack (cond : Condition) (syms : List ManaSymbol) : CardPart :=
  .ability (.stackStatic (.if cond [.reduceCost .this [.mana syms]]))

/-- `This spell costs {3} less to cast if it targets a tapped creature.`
Also `… an attacking nontoken creature.`
The reduction is a static ability that functions on the stack (CR 604.2). -/
def parseStackCostReduction (line : String) : Option CardPart :=
  match costsLessBy? (normLine line) " less to cast if it targets " with
  | some (syms, targetText) =>
    (costReductionTarget? targetText).map fun among =>
      reduceOnStack (.targetsIncludeAny .this among) syms
  | none => none

/-- `This spell costs {3} less to cast if a creature died this turn.`
The reduction is a static ability that functions on the stack (CR 604.2). -/
def parseCreatureDiedCostReduction (line : String) : Option CardPart :=
  match costsLessBy? (normLine line) " less to cast if " with
  | some (syms, cond) =>
    if cond == "a creature died this turn" then
      some (reduceOnStack (.happened (.die (.cardType .creature)) .turnStart) syms)
    else none
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

/-- A printed positive count: `two`, `2`. Zero is not a count. -/
def positiveCount (s : String) : Option Nat :=
  match englishSmall? s with
  | some n => if n == 0 then none else some n
  | none => none

/-- Life named by `<lead> N life`, such as `you gain 2 life`. -/
def lifeAmount? (s lead : String) : Option Nat :=
  (between? s lead " life").bind positiveCount

/-- `one`, `two`, or `one or two`. A range is ordered from low to high. -/
def parseCountRange (s : String) : Option Range :=
  match s.trimAscii.copy.splitOn " or " with
  | [a, b] =>
    match englishSmall? a, englishSmall? b with
    | some lo, some hi =>
      if lo <= hi then some (.range (Value.nat lo) (Value.nat hi)) else none
    | _, _ => none
  | [a] =>
    match englishSmall? a with
    | some n => some (.range (Value.nat n) (Value.nat n))
    | none => none
  | _ => none

/-- `one, two, or three` as an inclusive contiguous range.
The numbers are positive and listed from low to high with no gaps. -/
def parseContiguousCounts (s : String) : Option (Nat × Nat) :=
  let s := lowerAscii (s.trimAscii.copy)
  let normalized := (s.replace ", or " ", ").replace " or " ", "
  let parts :=
    normalized.splitOn ", " |>.map (·.trimAscii.copy) |>.filter (· != "")
  match parts.mapM englishSmall? with
  | none => none
  | some ns =>
    match ns with
    | [] => none
    | first :: _ =>
      let lo := ns.foldl (fun a b => Nat.min a b) first
      let hi := ns.foldl (fun a b => Nat.max a b) first
      let expected := (List.range (hi + 1)).filter (fun i => i ≥ lo)
      if ns == expected && lo > 0 then some (lo, hi) else none

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

/-- The printed name, the short name before a comma (CR 201.5), and that
name's first word when it is not an article. `Bilbo Baggins, Burglar` refers
to itself as `Bilbo Baggins` or `Bilbo`. `Gollum the Abandoned` refers to
itself as `Gollum`. -/
def selfNames (cardName : String) : List String :=
  let name := lowerAscii (cardName.trimAscii.copy)
  if name.isEmpty then []
  else
    let short :=
      match name.splitOn "," with
      | head :: _ => head.trimAscii.copy
      | [] => name
    let firstWord :=
      match short.splitOn " " with
      | w :: _ => w.trimAscii.copy
      | [] => ""
    let names :=
      if short.isEmpty || short == name then [name] else [name, short]
    if firstWord.isEmpty || firstWord == name || firstWord == short ||
        firstWord == "the" || firstWord == "a" || firstWord == "an" then
      names
    else
      names ++ [firstWord]

/-- `subject` is this card: a generic `this` phrase, or one of `cardName`'s
self-names. -/
def refersToSelf (cardName subject : String) : Bool :=
  let subject := lowerAscii (subject.trimAscii.copy)
  isGenericSelf subject || (selfNames cardName).contains subject

/-- Effect of `when <this card> <mid> <effect>`.
`mid` is the clause boundary, such as ` enters, ` or ` dies, `. -/
def whenSelfEffect? (cardName s mid : String) : Option String :=
  match after? s "when " with
  | none => none
  | some rest =>
    match rest.splitOn mid with
    | [subject, effect] =>
      if !refersToSelf cardName subject then none else some effect
    | _ => none

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

/-- `Target creature gets +2/+2 until end of turn.`
Also `Target creature gets +2/+2 and gains lifelink until end of turn.`
The target number is `n`. A gained keyword refers to that same target. -/
def parseTargetGetsUntilEndOfTurn (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  let s := lowerAscii (stripTrailingPeriod sentence)
  let suffix := " until end of turn"
  if !s.endsWith suffix then none
  else
    let body := (s.dropEnd suffix.length).trimAscii.copy
    match body.splitOn " gets " with
    | [who, rest] =>
      let (ptText, gained?) :=
        match rest.splitOn " and gains " with
        | [pt, gained] => (pt, some gained)
        | _ => (rest, none)
      match parseTargetPhrase who, parsePowerToughness ptText with
      | some sel, some (p, t) =>
        let pump : ContinuousEffect :=
          .addPowerToughness (.target n sel) (Value.int p) (Value.int t)
        match gained? with
        | none => some (.continuous [pump] .endOfTurn, n + 1)
        | some gained =>
          match parseKeywordPhrase gained with
          | some kws =>
            let gains :=
              kws.map fun k =>
                ContinuousEffect.gainAbility (.targetReference n) (.keyword k)
            some (.continuous (pump :: gains) .endOfTurn, n + 1)
          | none => none
      | _, _ => none
    | _ => none

/-- `Creatures target player controls get -1 / -1 until end of turn.`
The player is target `n`. `P/T` may be negative. -/
def parseTargetPlayerControlsGet (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  let s := lowerAscii (stripTrailingPeriod sentence)
  let suffix := " until end of turn"
  let tail := " target player controls"
  if !s.endsWith suffix then none
  else
    let body := (s.dropEnd suffix.length).trimAscii.copy
    let pieces :=
      match body.splitOn " get " with
      | [who, pt] => some (who, pt)
      | _ =>
        match body.splitOn " gets " with
        | [who, pt] => some (who, pt)
        | _ => none
    match pieces with
    | none => none
    | some (who, pt) =>
      if !who.endsWith tail then none
      else
        let obj := (who.dropEnd tail.length).trimAscii.copy
        match typesInPhrase obj, parsePowerToughness pt with
        | some ts, some (p, t) =>
          some (
            .continuous
              [.addPowerToughness
                (.intersection [
                  .permanent,
                  selectorOfTypes ts,
                  .controlled (.target n .player)])
                (Value.int p)
                (Value.int t)]
              .endOfTurn,
            n + 1)
        | _, _ => none

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

/-- `Target player draws two cards and loses 2 life.`
The player is target `n`. -/
def parseTargetPlayerDrawsLosesLife (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  let s := lowerAscii (stripTrailingPeriod sentence)
  let lead := "target player draws "
  let mid := " and loses "
  let tail := " life"
  if !s.startsWith lead || !s.endsWith tail then none
  else
    let body := ((s.drop lead.length).dropEnd tail.length).trimAscii.copy
    match body.splitOn mid with
    | [drawText, lifeText] =>
      match parseCardCount drawText, englishSmall? lifeText with
      | some cards, some life =>
        if life == 0 then none
        else
          some (
            .sequence [
              .draw (.target n .player) (Value.nat cards),
              .loseLife (.targetReference n) (Value.nat life)],
            n + 1)
      | _, _ => none
    | _ => none

/-- `When Bilbo Baggins enters, draw a card.` The subject is this card. -/
def parseEnterDraw (cardName : String) (line : String) : Option CardPart :=
  match whenSelfEffect? cardName (normLine line) " enters, " with
  | some effect =>
    match after? effect "draw " with
    | some count =>
      (parseCardCount count).map fun k =>
        .ability (.triggered (.enter .this) (.draw (.controller .this) (Value.nat k)))
    | none => none
  | none => none

/-- `target creature an opponent controls` as the objects a target matches. -/
def parseOppControlledTarget (s : String) : Option Selector :=
  let s := lowerAscii (s.trimAscii.copy)
  let lead := "target "
  let tail := " an opponent controls"
  if !s.startsWith lead || !s.endsWith tail then none
  else
    let obj := ((s.drop lead.length).dropEnd tail.length).trimAscii.copy
    match typesInPhrase obj with
    | none => none
    | some ts =>
      some (.intersection [
        .permanent,
        selectorOfTypes ts,
        .controlled (.opponent (.controller .this))])

/-- `target <permanents> an opponent controls gets P/T until end of turn.`
The target number is `n`. `P/T` may be negative, as in -1 / -1. -/
def parseOppGetsUntilEndOfTurn (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := lowerAscii (stripTrailingPeriod sentence)
  let suffix := " until end of turn"
  if !s.endsWith suffix then none
  else
    let body := (s.dropEnd suffix.length).trimAscii.copy
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
      match parseOppControlledTarget who, parsePowerToughness pt with
      | some sel, some (p, t) =>
        some (
          .continuous
            [.addPowerToughness (.target n sel) (Value.int p) (Value.int t)]
            .endOfTurn,
          n + 1)
      | _, _ => none

/-- `When this creature dies, target creature an opponent controls gets -1 / -1 until end of turn.`
The dying object is this card. The target number is `n`. -/
def parseDiesOppGets (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match whenSelfEffect? cardName (normLine line) " dies, " with
  | some effect =>
    match parseOppGetsUntilEndOfTurn effect n with
    | some (action, n') =>
      some (.ability (.triggered (.die .this) action), n')
    | none => none
  | none => none

/-- `put a +1/+1 counter on this creature`. `this`, `this creature`, and `it`
are the source of this ability. -/
def parsePutPlusOneOnThis (sentence : String) : Option CardAction :=
  let s := lowerAscii (stripTrailingPeriod sentence)
  let lead := "put a +1/+1 counter on "
  if !s.startsWith lead then none
  else
    match parsePumpWho (s.drop lead.length).trimAscii.copy with
    | some sel =>
      if sel == .source .this then
        some (.putCounter (.source .this) .plusOnePlusOne 1)
      else none
    | none => none

/-- `Whenever you draw your second card each turn, put a +1/+1 counter on this creature.` -/
def parseDrawSecondPlusOne (line : String) : Option CardPart :=
  let line := stripTrailingPeriod (stripReminderParenthetical line)
  let s := lowerAscii line
  let lead := "whenever you draw your second card each turn, "
  if !s.startsWith lead then none
  else
    match parsePutPlusOneOnThis (s.drop lead.length).trimAscii.copy with
    | some action =>
      some (.ability (
        .triggered
          (.ordinal 2 .turnStart (.draw (.controller .this) .all))
          action))
    | none => none

/-- `Whenever you draw a card, put a +1/+1 counter on this creature.` -/
def parseYouDrawPlusOne (line : String) : Option CardPart :=
  let line := stripTrailingPeriod (stripReminderParenthetical line)
  let s := lowerAscii line
  let lead := "whenever you draw a card, "
  if !s.startsWith lead then none
  else
    match parsePutPlusOneOnThis (s.drop lead.length).trimAscii.copy with
    | some action =>
      some (.ability (
        .triggered
          (.draw (.controller .this) .all)
          action))
    | none => none

/-- `Counter target spell unless its controller pays {4}.`
The target number is `n`. -/
def parseCounterUnlessPays (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := lowerAscii (stripTrailingPeriod sentence)
  let lead := "counter target "
  let mid := " unless its controller pays "
  if !s.startsWith lead then none
  else
    let body := (s.drop lead.length).trimAscii.copy
    match body.splitOn mid with
    | [obj, costText] =>
      if obj != "spell" then none
      else
        match parseManaSymbols costText with
        | some syms =>
          if syms.isEmpty then none
          else
            some (
              .preventable
                (.controller (.targetReference n))
                [.mana syms]
                (.counter (.target n .spell)),
              n + 1)
        | none => none
    | _ => none

/-- `Draw two cards, then discard a card.` Does not choose a target. -/
def parseDrawThenDiscard (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := lowerAscii (stripTrailingPeriod sentence)
  let lead := "draw "
  match s.splitOn ", then discard " with
  | [drawPart, discardPart] =>
    if !drawPart.startsWith lead then none
    else
      match
        parseCardCount (drawPart.drop lead.length).trimAscii.copy,
        parseCardCount discardPart with
      | some d, some c =>
        some (
          .sequence [
            .draw (.controller .this) (Value.nat d),
            .discard (.controller .this) (Value.nat c)],
          n)
      | _, _ => none
  | _ => none

/-- `Target creature gets -5 / -5 until end of turn. If that creature would die this turn, exile it instead.`
The pump and the replacement both last until end of turn. Dying is being put
into a graveyard from the battlefield; the replacement exiles that object
instead (CR 614.1). The creature is target `n`. -/
def parsePumpExileIfDies (text : String) (n : Nat) : Option (CardAction × Nat) :=
  match sentences text with
  | [pump, exile] =>
    if lowerAscii exile !=
        "if that creature would die this turn, exile it instead" then none
    else
      match parseTargetGetsUntilEndOfTurn pump n with
      | some (
          .continuous
            [.addPowerToughness
              (.target m (.intersection [.permanent, .cardType .creature])) vp vt]
            .endOfTurn,
          n') =>
        some (
          .continuous
            [.addPowerToughness
              (.target m (.intersection [.permanent, .cardType .creature])) vp vt,
             .replace
               (.putToGraveyard (.targetReference m))
               [.exile (.replacingObject)]]
            .endOfTurn,
          n')
      | _ => none
  | _ => none

/-- One printed mode of a “Choose one” spell. The first success wins. -/
def parseModeAction (text : String) (n : Nat) : Option (CardAction × Nat) :=
  parseCounterUnlessPays text n <|>
    parseDrawThenDiscard text n <|>
    parsePumpExileIfDies text n <|>
    parseTargetPlayerDrawsLosesLife text n <|>
    parseTargetGetsUntilEndOfTurn text n <|>
    parseTargetPlayerControlsGet text n

/-- The text of a `•` mode line, without the bullet. -/
def stripModeBullet (line : String) : Option String :=
  let line := line.trimAscii.copy
  let bullet := "•"
  if line.startsWith bullet then
    some (line.drop bullet.length).trimAscii.copy
  else
    none

/-- `Choose one —` (CR 700.2). -/
def isChooseOneHeader (line : String) : Bool :=
  lowerAscii (stripTrailingPeriod (stripReminderParenthetical line)) == "choose one —"

/-- Parts for a “Choose one” spell with at least one parsed mode.
No modes makes the parse fail rather than dropping the printed choice. -/
def chooseOneParts (modes : List CardAction) : Option (List CardPart) :=
  match modes with
  | [] => none
  | modes => some [.actions [.chooseMode modes]]

/-- `<subject> <tail>` as a static restriction, when `subject` is this card. -/
def staticCant (cardName line tail : String) (restriction : Trigger) : Option CardPart :=
  match before? (normLine line) tail with
  | some subject =>
    if subject.isEmpty || !refersToSelf cardName subject then none
    else some (.ability (.static (.forbid restriction)))
  | none => none

/-- `<this card> can't be blocked.` The subject must be this card. -/
def parseCantBeBlocked (cardName : String) (line : String) : Option CardPart :=
  staticCant cardName line " can't be blocked" (.block .any .this)

/-- `<this card> can't block.` The subject must be this card. This functions
on the battlefield (CR 604.2 / 509.1b), so it is `static`. -/
def parseCantBlock (cardName : String) (line : String) : Option CardPart :=
  staticCant cardName line " can't block" (.block .this .any)

/-- `Whenever <this card> deals combat damage to a player, draw a card, then
discard a card.` The subject must be this card. The effect is the same
draw-then-discard grammar as a modal spell. -/
def parseCombatDamageLoot (cardName : String) (line : String) : Option CardPart :=
  let line := stripTrailingPeriod (stripReminderParenthetical line)
  let s := lowerAscii line
  let lead := "whenever "
  let mid := " deals combat damage to a player, "
  if !s.startsWith lead then none
  else
    match (s.drop lead.length).trimAscii.copy.splitOn mid with
    | [subject, effect] =>
      if subject.isEmpty || !refersToSelf cardName subject then none
      else
        match parseDrawThenDiscard effect 1 with
        | some (action, _) =>
          some (.ability (.triggered (.combatDamage .this .player) action))
        | none => none
    | _ => none

/-- `Exchange control of two target nonland permanents that share a card type.`
The target number is `n`. The noun stays plural, as in the printed template
for a set of permanents. -/
def parseExchangeControlSharingCardType (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  let s := lowerAscii (stripTrailingPeriod sentence)
  let lead := "exchange control of "
  let tail := " that share a card type"
  if !s.startsWith lead || !s.endsWith tail then none
  else
    let mid := ((s.drop lead.length).dropEnd tail.length).trimAscii.copy
    match mid.splitOn " target " with
    | [countText, obj] =>
      if obj != "nonland permanents" then none
      else
        match parseCountRange countText with
        | some r =>
          if r == .range 1 1 then none
          else
            some (
              .exchangeControl
                (.targetSet
                  n
                  r
                  (.intersection [.permanent, .not .land])
                  [.shareCardType]),
              n + 1)
        | none => none
    | _ => none

/-- `Target creature's owner puts it on their choice of the top or bottom of their library.`
The target number is `n`. That creature's owner chooses which library position. -/
def parseOwnerPutsTopOrBottom (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := lowerAscii (stripTrailingPeriod sentence)
  let lead := "target "
  let tail := "'s owner puts it on their choice of the top or bottom of their library"
  if !s.startsWith lead || !s.endsWith tail then none
  else
    let obj := ((s.drop lead.length).dropEnd tail.length).trimAscii.copy
    match typesInPhrase obj with
    | some ts =>
      let sel := .intersection [.permanent, selectorOfTypes ts]
      some (
        .playerSelectAction
          (.owner (.targetReference n))
          (.range 1 1)
          [.putOnTopOfLibrary (.target n sel),
            .putOnBottomOfLibrary (.targetReference n)],
        n + 1)
    | none => none

/-- `Destroy target creature.` The target number is `n`. -/
def parseDestroy (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := lowerAscii (stripTrailingPeriod sentence)
  let lead := "destroy target "
  if !s.startsWith lead then none
  else
    match typesInPhrase (s.drop lead.length).trimAscii.copy with
    | some ts =>
      some (
        .destroy (.target n (.intersection [.permanent, selectorOfTypes ts])),
        n + 1)
    | none => none

/-- `Put a +1/+1 counter on up to one target creature.`
Up to one target is zero or one (CR 115.1). The targets are numbered `n`. -/
def parsePutPlusOneUpToOne (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := lowerAscii (stripTrailingPeriod sentence)
  let lead := "put a +1/+1 counter on up to one target "
  if !s.startsWith lead then none
  else
    match typesInPhrase (s.drop lead.length).trimAscii.copy with
    | some ts =>
      some (
        .putCounter
          (.targets n (.range 0 1) (.intersection [.permanent, selectorOfTypes ts]))
          .plusOnePlusOne
          1,
        n + 1)
    | none => none

/-- `Target player gains 2 life.` The player is target `n`. -/
def parseTargetPlayerGainsLife (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (lifeAmount? (normSentence sentence) "target player gains ").map fun k =>
    (.gainLife (.target n .player) (Value.nat k), n + 1)

/-- `You gain 2 life.` Does not choose a target, so the target number stays `n`. -/
def parseYouGainLife (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (lifeAmount? (normSentence sentence) "you gain ").map fun k =>
    (.gainLife (.controller .this) (Value.nat k), n)

/-- `Scry 2.` Does not choose a target, so the target number stays `n`. -/
def parseScry (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match after? (normSentence sentence) "scry " with
  | some count =>
    (positiveCount count).map fun k => (.scry (.controller .this) (Value.nat k), n)
  | none => none

/-- `Whenever one or more other creatures die, scry 1.`
Those creatures die together, so this is one trigger (CR 603.2c).
The effect is `Scry N`. -/
def parseOtherCreaturesDieScry (line : String) (n : Nat) : Option (CardPart × Nat) :=
  let line := stripTrailingPeriod (stripReminderParenthetical line)
  let s := lowerAscii line
  let lead := "whenever one or more "
  let mid := " die, "
  if !s.startsWith lead then none
  else
    match (s.drop lead.length).trimAscii.copy.splitOn mid with
    | [who, effect] =>
      if who != "other creatures" then none
      else
        match parseControlledPhrase who, parseScry effect n with
        | some among, some (action, n') =>
          some (
            .ability (.triggered (.dieSimultaneously among []) action),
            n')
        | _, _ => none
    | _ => none

/-- `Counter target spell. If a permanent spell is countered this way, exile
it instead of putting it into its owner's graveyard. You may cast that card
without paying its mana cost for as long as it remains exiled.`
The counter and its target are numbered `n`. The exile that replaces the
graveyard is `n + 1`, and the free cast refers to that exiled card. -/
def parseCounterExilePermanentMayCast (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match sentences text with
  | [counter, exile, cast] =>
    if lowerAscii counter != "counter target spell" then none
    else if lowerAscii exile !=
        "if a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard" then
      none
    else if lowerAscii cast !=
        "you may cast that card without paying its mana cost for as long as it remains exiled" then
      none
    else
      let exileId := n + 1
      some (
        [
          .actionId n (.counter (.target n .spell)),
          .continuous
            [.replace
              (.putToGraveyard
                (.intersection [.wasObjectOfAction n, .permanentSpell]))
              [
                .actionId exileId (.exile (.replacingObject)),
                .continuous
                  [.canCastWithoutPayingManaCost
                    (.controller .this)
                    (.wasCreatedByAction exileId)]
                  .endOfGame
              ]]
            .endOfGame
        ],
        exileId)
  | _ => none

/-- One sentence. The first parser that accepts it wins. -/
def parseSentence (cardName sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  parseGainsUntilEndOfTurn sentence n <|>
    parseTap sentence n <|>
    parseUntap sentence n <|>
    parseItGetsUntilEndOfTurn sentence n <|>
    parseIfItsSubtypeMayAttach sentence n <|>
    parseDealDamage cardName sentence n <|>
    parseDestroy sentence n <|>
    parsePutPlusOneUpToOne sentence n <|>
    parseTargetPlayerGainsLife sentence n <|>
    parseYouGainLife sentence n <|>
    parseScry sentence n <|>
    parseOwnerPutsTopOrBottom sentence n <|>
    parseExchangeControlSharingCardType sentence n <|>
    parseTargetGetsUntilEndOfTurn sentence n <|>
    parseTargetPlayerControlsGet sentence n <|>
    parseTargetPlayerDrawsLosesLife sentence n

/-- Every sentence of `text` must parse. An unrecognized sentence fails
the text. No sentences (reminder-only or empty text) succeeds with no actions.
Two multi-sentence templates are tried before the sentence split. -/
def actionsFromText (cardName : String) (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  let rec go (ss : List String) (n : Nat) (acc : List CardAction) :
      Option (List CardAction × Nat) :=
    match ss with
    | [] => some (acc, n)
    | s :: rest =>
      match parseSentence cardName s n with
      | some (a, n') => go rest n' (acc ++ [a])
      | none => none
  parseCounterExilePermanentMayCast text n <|>
    ((parsePumpExileIfDies text n).map fun (action, n') => ([action], n')) <|>
    go (sentences text) n []

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

/-- `As an additional cost to cast this spell, sacrifice an artifact or creature or pay {4}.`
The sacrifice and the generic mana are alternatives announced at CR 601.2b.
The ability functions while this spell is on the stack (CR 113.6 / 604.2). -/
def parseAdditionalCostSacrificeOrPay (line : String) : Option CardPart :=
  let s := lowerAscii (stripTrailingPeriod (stripReminderParenthetical line))
  let lead := "as an additional cost to cast this spell, sacrifice "
  let mid := " or pay "
  if !s.startsWith lead then none
  else
    match (s.drop lead.length).trimAscii.copy.splitOn mid with
    | [obj, costText] =>
      match dropArticle? obj with
      | some obj =>
        match typesInPhrase obj, parseManaSymbols costText with
        | some ts, some [.generic n] =>
          some (.ability (.stackStatic (
            .additionalCost .this
              [.or [
                .sacrificeCount
                  (.intersection [.permanent, selectorOfTypes ts])
                  1,
                .mana [.generic n]]])))
        | _, _ => none
      | none => none
    | _ => none

/-- `Ferocious — Whenever this creature attacks while you control a creature
with power 4 or greater, you gain 2 life.`
`Ferocious` is an ability word (CR 207.2c). The “while” clause is part of
the trigger condition (CR 603.2): it is checked when this creature attacks,
and it is not checked again when the ability resolves. -/
def parseFerociousAttackGainLife (line : String) : Option CardPart :=
  let line := stripTrailingPeriod (stripReminderParenthetical line)
  let s := lowerAscii line
  let s :=
    match s.splitOn "—" with
    | [word, rest] =>
      if word.trimAscii.copy == "ferocious" then rest.trimAscii.copy else s
    | _ => s
  let lead := "whenever this creature attacks while you control a creature with power 4 or greater, "
  if !s.startsWith lead then none
  else
    match parseYouGainLife (s.drop lead.length).trimAscii.copy 0 with
    | some (.gainLife _ k, _) =>
      some (.ability (
        .triggeredWhile
          (.attack .this .all)
          (.any
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this),
              .powerAtLeast (Value.int 4)]))
          (.gainLife (.controller .this) k)))
    | _ => none

/-- `When this Equipment enters, target opponent sacrifices a creature of their choice.`
The entering object is this card. The opponent is target `n` and chooses which
creature to sacrifice (CR 701.17a). -/
def parseEnterTargetOpponentSacrifices (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match whenSelfEffect? cardName (normLine line) " enters, " with
  | none => none
  | some effect =>
    match between? effect "target opponent sacrifices " " of their choice" with
    | none => none
    | some obj =>
      match dropArticle? obj with
      | some named =>
        if named != "creature" then none
        else
          some (
            .ability (
              .triggered
                (.enter .this)
                (.sacrifice
                  (.selected
                    (.target n (.opponent (.controller .this)))
                    (.range 1 1)
                    (.intersection [
                      .permanent,
                      .cardType .creature,
                      .controlled (.targetReference n)])))),
            n + 1)
      | none => none

/-- `Equipped creature gets +2/+1.` The bonus is a static ability of the
Equipment (CR 604.1 / 301.5). -/
def parseEquippedGets (line : String) : Option CardPart :=
  let s := lowerAscii (stripTrailingPeriod (stripReminderParenthetical line))
  let lead := "equipped creature gets "
  if !s.startsWith lead then none
  else
    match parsePowerToughness (s.drop lead.length).trimAscii.copy with
    | some (p, t) =>
      some (.ability
        (.static (.addPowerToughness (.hostOf .this) (Value.int p) (Value.int t))))
    | none => none

/-- `Equip {2}.` Reminder text such as
`({2}: Attach to target creature you control. Equip only as a sorcery.)`
is not rules text (CR 207.2 / 702.6). -/
def parseEquip (line : String) : Option CardPart :=
  let s := lowerAscii (stripTrailingPeriod (stripReminderParenthetical line))
  let lead := "equip "
  if !s.startsWith lead then none
  else
    match parseManaSymbols (s.drop lead.length).trimAscii.copy with
    | some syms =>
      if syms.isEmpty then none
      else some (.ability (.keywordWithCost .equip [.mana syms]))
    | none => none

/-- `Each opponent loses 2 life.` The amount is a printed number. -/
def parseEachOpponentLosesLife (sentence : String) : Option Nat :=
  lifeAmount? (normSentence sentence) "each opponent loses "

/-- `When <this card> enters, exile up to one target card from an opponent's graveyard. Each opponent loses N life.`
Up to one target is zero or one (CR 115.1). That target is numbered `n`. -/
def parseEnterExileOppGyLoseLife (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences (stripReminderParenthetical line) with
  | [enter, lose] =>
    match whenSelfEffect? cardName (lowerAscii enter) " enters, " with
    | some effect =>
      if effect != "exile up to one target card from an opponent's graveyard" then none
      else
        match parseEachOpponentLosesLife lose with
        | some k =>
          some (
            .ability (
              .triggered
                (.enter .this)
                (.sequence [
                  .exile
                    (.targets n (.range 0 1)
                      (.intersection [
                        .inGraveyard,
                        .owner (.opponent (.controller .this))])),
                  .loseLife (.opponent (.controller .this)) (Value.nat k)])),
            n + 1)
        | none => none
    | none => none
  | _ => none

/-- `Sacrifice an artifact or creature` as sacrificing one matching permanent. -/
def parseSacrificeAn (s : String) : Option Cost :=
  let s := lowerAscii (s.trimAscii.copy)
  let lead := "sacrifice "
  if !s.startsWith lead then none
  else
    match dropArticle? (s.drop lead.length).trimAscii.copy with
    | some obj =>
      match typesInPhrase obj with
      | some ts =>
        some (.sacrificeCount (.intersection [.permanent, selectorOfTypes ts]) 1)
      | none => none
    | none => none

/-- One printed cost: mana symbols, or sacrificing one permanent of the
named types. -/
def parsePrintedCost (s : String) : Option Cost :=
  match parseManaSymbols s with
  | some syms => if syms.isEmpty then none else some (.mana syms)
  | none => parseSacrificeAn s

/-- Costs separated by commas, such as `{2}, Sacrifice an artifact or creature`.
One unrecognized cost fails the list. -/
def parsePrintedCosts (s : String) : Option (List Cost) :=
  let parts := s.splitOn ", " |>.map (·.trimAscii.copy) |>.filter (· != "")
  if parts.isEmpty then none else parts.mapM parsePrintedCost

def returnThisFromGraveyardToHand : CardAction :=
  .returnToHand (.intersection [.inGraveyard, .source .this])

def parseReturnThisFromGraveyard (sentence : String) : Option CardAction :=
  if lowerAscii (stripTrailingPeriod sentence) ==
      "return this card from your graveyard to your hand" then
    some returnThisFromGraveyardToHand
  else
    none

/-- `{2}, Sacrifice an artifact or creature: Return this card from your graveyard to your hand. Activate only as a sorcery.`
The effect moves this card out of the graveyard, so the ability functions
there (CR 113.6). “Activate only as a sorcery” is the condition
(CR 307.1 / 117.1a). The ability is `graveyardActivatedIf`. -/
def parseGraveyardReturn (line : String) : Option CardPart :=
  let line := stripReminderParenthetical line
  match line.splitOn ": " with
  | [costText, effect] =>
    match sentences effect with
    | [ret, restrict] =>
      if lowerAscii restrict != "activate only as a sorcery" then none
      else
        match parsePrintedCosts costText, parseReturnThisFromGraveyard ret with
        | some costs, some action =>
          some (.ability (
            .graveyardActivatedIf
              (.timeToCastSorcery (.controller .this))
              costs
              action))
        | _, _ => none
    | _ => none
  | _ => none

/-- `When this creature enters, each opponent discards a card.`
The entering object is this card. -/
def parseEnterEachOpponentDiscards (cardName : String) (line : String) :
    Option CardPart :=
  match whenSelfEffect? cardName (normLine line) " enters, " with
  | some effect =>
    match after? effect "each opponent discards " with
    | some count =>
      (parseCardCount count).map fun k =>
        .ability (.triggered (.enter .this)
          (.discard (.opponent (.controller .this)) (Value.nat k)))
    | none => none
  | none => none

/-- A pronoun for the object named earlier in the same ability. -/
def isPersonalPronoun (s : String) : Bool :=
  match lowerAscii (s.trimAscii.copy) with
  | "he" | "she" | "it" | "they" => true
  | _ => false

/-- `When Gandalf enters, he deals 3 damage divided as you choose among one, two, or three targets.`
The entering object is this card. The damage source is a pronoun for that
object, or another reference to this card. Its controller divides the damage
(CR 601.2d). `targets` with no type is any target. The counts are a positive
contiguous range, and those targets are numbered `n`. -/
def parseEnterDividedDamage (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match before? (normLine line) " targets" with
  | none => none
  | some body =>
    match whenSelfEffect? cardName body " enters, " with
    | none => none
    | some effect =>
      match effect.splitOn " deals " with
      | [who, rest] =>
        let who := who.trimAscii.copy
        if who.isEmpty ||
            !(isPersonalPronoun who || refersToSelf cardName who) then none
        else
          match rest.splitOn " damage divided as you choose among " with
          | [amt, counts] =>
            match englishSmall? (amt.trimAscii.copy), parseContiguousCounts counts with
            | some amount, some (lo, hi) =>
              if amount == 0 then none
              else
                some (
                  .ability (
                    .triggered
                      (.enter .this)
                      (.divideDamage
                        (.controller .this)
                        (.source .this)
                        (.targets
                          n
                          (.range (Value.nat lo) (Value.nat hi))
                          .all)
                        (Value.nat amount))),
                  n + 1)
            | _, _ => none
          | _ => none
      | _ => none

/-- `When this Equipment enters, you may discard a card. If you do, draw two cards.`
The entering object is this card. “If you do” means the draw happens only
when that discard is taken. The discard is action `n`. -/
def parseEnterMayDiscardDraw (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences (stripReminderParenthetical line) with
  | [may, ifYouDo] =>
    match whenSelfEffect? cardName (lowerAscii may) " enters, " with
    | some effect =>
      match after? effect "you may discard " with
      | some discardedText =>
        match parseCardCount discardedText, after? (lowerAscii ifYouDo) "if you do, draw " with
        | some discarded, some drawnText =>
          match parseCardCount drawnText with
          | some drawn =>
            some (
              .ability (
                .triggered
                  (.enter .this)
                  (.sequence [
                    .optional
                      (.actionId n
                        (.discard
                          (.controller .this)
                          (Value.nat discarded))),
                    .if
                      (.happened (.actionWithId n) .gameStart)
                      [.draw (.controller .this) (Value.nat drawn)]])),
              n + 1)
          | none => none
        | _, _ => none
      | none => none
    | none => none
  | _ => none

/-- One card part that does not advance the target number. -/
def sole (part? : Option CardPart) (n : Nat) : Option (List CardPart × Nat) :=
  part?.map fun part => ([part], n)

/-- One card part together with the target number it produced. -/
def carry (parsed : Option (CardPart × Nat)) : Option (List CardPart × Nat) :=
  parsed.map fun (part, n') => ([part], n')

/-- Spell actions. Empty actions are a failed parse, not a blank spell. -/
def spellActions (parsed : Option (List CardAction × Nat)) : Option (List CardPart × Nat) :=
  match parsed with
  | some ([], _) => none
  | some (actions, n') => some ([.actions actions], n')
  | none => none

/-- One non-empty Oracle line. A reminder-only line contributes no parts.
Anything else that the grammar does not cover fails.
The first parser that accepts the line wins. -/
def parseOneLine (cardName : String) (line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  if (rulesText line).isEmpty then some ([], n)
  else
    (keywordParts? line).map (·, n) <|>
    carry (parseActivatedAbility line n) <|>
    sole (parseGraveyardReturn line) n <|>
    carry (parseEnterExileOppGyLoseLife cardName line n) <|>
    sole (parseStackCostReduction line) n <|>
    sole (parseCreatureDiedCostReduction line) n <|>
    sole (parseAttackTriggered line) n <|>
    sole (parseFerociousAttackGainLife line) n <|>
    sole (parseEnterDraw cardName line) n <|>
    sole (parseEnterEachOpponentDiscards cardName line) n <|>
    carry (parseEnterDividedDamage cardName line n) <|>
    carry (parseEnterMayDiscardDraw cardName line n) <|>
    carry (parseEnterTargetOpponentSacrifices cardName line n) <|>
    carry (parseDiesOppGets cardName line n) <|>
    carry (parseOtherCreaturesDieScry line n) <|>
    sole (parseDrawSecondPlusOne line) n <|>
    sole (parseYouDrawPlusOne line) n <|>
    sole (parseCantBeBlocked cardName line) n <|>
    sole (parseCantBlock cardName line) n <|>
    sole (parseCombatDamageLoot cardName line) n <|>
    sole (parseAdditionalCostSacrificeOrPay line) n <|>
    sole (parseEquippedGets line) n <|>
    sole (parseEquip line) n <|>
    spellActions (actionsFromText cardName line n)

mutual
/-- Lines outside a `Choose one —` list. `parseModeLines` reads the list. -/
def parseBodyLines (cardName : String) : List String → Nat → Option (List CardPart × Nat)
  | [], n => some ([], n)
  | line :: rest, n =>
    if isChooseOneHeader line then
      parseModeLines cardName rest n []
    else
      match parseOneLine cardName line n with
      | none => none
      | some (here, nHere) =>
        (parseBodyLines cardName rest nHere).map fun (more, nMore) =>
          (here ++ more, nMore)

/-- `•` modes after `Choose one —`. A later non-mode line ends the list.
No parsed modes fails rather than dropping the printed choice. -/
def parseModeLines (cardName : String) (lines : List String) (n : Nat)
    (acc : List CardAction) : Option (List CardPart × Nat) :=
  match lines with
  | [] => (chooseOneParts acc).map fun parts => (parts, n)
  | line :: rest =>
    match stripModeBullet line with
    | some text =>
      match parseModeAction text n with
      | some (action, n') => parseModeLines cardName rest n' (acc ++ [action])
      | none => none
    | none =>
      match chooseOneParts acc with
      | none => none
      | some head =>
        if isChooseOneHeader line then
          (parseModeLines cardName rest n []).map fun (more, nMore) =>
            (head ++ more, nMore)
        else
          match parseOneLine cardName line n with
          | none => none
          | some (here, nHere) =>
            (parseBodyLines cardName rest nHere).map fun (more, nMore) =>
              (head ++ here ++ more, nMore)
end

/-- Oracle lines, including `Choose one —` lists. -/
def parseMainLines (cardName : String) (lines : List String) (n : Nat) :
    Option (List CardPart × Nat) :=
  parseBodyLines cardName lines n

def nameOfParts (parts : List CardPart) : Option String :=
  parts.findSome? fun
    | .name n => some n
    | _ => none

/-- A Gatherer Adventure face: `Name {cost}`, a type line, then rules text.
A missing name or cost, a line that is not a type line, or effect text the
grammar does not cover makes the parse fail. No effect lines is a face
with no spell effect. -/
def parseAdventure (cardName : String) (lines : List String) (n : Nat) :
    Option (List CardPart) :=
  match lines with
  | [] => none
  | nameLine :: rest =>
    match parseNameAndCost nameLine with
    | none => none
    | some nameParts =>
      match rest with
      | [] => some nameParts
      | typeLine :: effectLines =>
        let typeParts := parseTypeLine typeLine
        if typeParts.isEmpty then none
        else
          -- An Adventure face refers to itself by its own name.
          let faceName := nameOfParts nameParts |>.getD cardName
          match effectLines with
          | [] => some (nameParts ++ typeParts)
          | _ =>
            match actionsFromText faceName (String.intercalate " " effectLines) n with
            | some (actions, _) =>
              if actions.isEmpty then none
              else some (nameParts ++ typeParts ++ [.actions actions])
            | none => none

end OracleParts

open OracleParts

/-- Parse printed Oracle text into `CardPart`s. Keyword lines, Gatherer
`//ADV//` Adventure faces, “gains … until end of turn” effects,
`{cost}: … get +P/+T until end of turn` abilities,
`Pay N life: … get +P/+T until end of turn` abilities, including
`Activate only once each turn`,
`Tap one or two target creatures` effects,
`Untap target creature you control` plus a following `It gets +P/+T`
and optional `If it's a <subtype>, you may attach …` clause,
stack cost reductions
(`This spell costs {N} less … if it targets a tapped creature`,
`an attacking nontoken creature`, or `if a creature died this turn`),
`As an additional cost to cast this spell, sacrifice an <permanent type or …>
or pay {N}` (a static ability of the spell on the stack),
`Destroy target <permanent type or …>` effects,
`Put a +1/+1 counter on up to one target <permanent type>` effects,
`Target player gains N life` and `You gain N life` effects,
`<this card> deals N damage to target creature` effects,
`Whenever this creature attacks, it gets +P/+T until end of turn for each
other creature you control` triggers,
`Ferocious — Whenever this creature attacks while you control a creature with
power 4 or greater, you gain N life` triggers,
`When <this card> enters, draw a card` triggers,
`When <this card> dies, target <permanents> an opponent controls gets P/T until end of turn`
triggers,
`Whenever one or more other creatures die, scry N` triggers,
`Whenever you draw your second card each turn, put a +1/+1 counter on this creature`
triggers,
`Whenever you draw a card, put a +1/+1 counter on this creature`
triggers,
`When <this card> enters, target opponent sacrifices a creature of their choice`
triggers,
`When <this card> enters, each opponent discards a card` triggers,
`When <this card> enters, he deals N damage divided as you choose among one, two, or three targets`
triggers (the source is a pronoun for the entering object, or another
reference to this card; its controller divides the damage; `targets` with no
type is any target),
`When <this card> enters, you may discard a card. If you do, draw N cards`
triggers,
`Equipped creature gets +P/+T` static abilities,
`Equip {cost}` abilities,
`Scry N` effects,
`Target <permanent type> gets +P/+T until end of turn` effects, including
`and gains <keywords>`,
`Target creature gets +P/+T until end of turn. If that creature would die this turn, exile it instead`,
`<permanent types> target player controls get +P/+T until end of turn` effects,
`Target player draws <count> cards and loses N life` effects,
`Choose one —` modals whose `•` modes are those effects or
`Counter target spell unless its controller pays {cost}` or
`Draw <count> cards, then discard <count> card(s)`,
`Counter target spell. If a permanent spell is countered this way, exile it
instead of putting it into its owner's graveyard. You may cast that card
without paying its mana cost for as long as it remains exiled`,
`<this card> can't be blocked`,
`<this card> can't block`,
`When <this card> enters, exile up to one target card from an opponent's graveyard. Each opponent loses N life`,
`{cost}, Sacrifice an <permanent type or …>: Return this card from your graveyard to your hand. Activate only as a sorcery`
(`graveyardActivatedIf`: the ability functions while this card is in a graveyard),
`Whenever <this card> deals combat damage to a player, draw <count> cards,
then discard <count> card(s)`, and
`Exchange control of <count> target nonland permanents that share a card type`, and
`Target <permanent type>'s owner puts it on their choice of the top or bottom of their library`
are read into parts.
`name` is the card being parsed. Text that uses that name, the short name
before a comma (CR 201.5), or that name's first word when it is not an
article, means this card, as do `this` and `this <type>`.
`Gollum the Abandoned` refers to itself as `Gollum`.
Returns `none` when a line, sentence, mode, or Adventure face is not
recognized. Reminder parentheticals are not rules text. Empty text is
`some []`. -/
def parseOracleParts (name : String) (text : String) : Option (List CardPart) :=
  let lines :=
    text.splitOn "\n" |>.map (·.trimAscii.copy) |>.filter (· != "")
  let (main, adv) := splitAdventure lines
  match parseMainLines name main 1 with
  | none => none
  | some (mainParts, n) =>
    match adv with
    | [] => some mainParts
    | _ =>
      match parseAdventure name adv n with
      | none => none
      | some alt => some (mainParts ++ [.alternative alt])

#guard parseOracleParts (name := "") "Lifelink" == some [.ability (.keyword .lifelink)]
#guard parseOracleParts (name := "") "Flying, deathtouch" ==
  some [.ability (.keyword .flying), .ability (.keyword .deathtouch)]
#guard parseOracleParts (name := "")
  "Reach (This creature can block creatures with flying.)" ==
  some [.ability (.keyword .reach)]
#guard parseOracleParts (name := "") "Whenever this creature attacks, draw a card." == none
#guard parseOracleParts (name := "") "When another creature enters, draw a card." == none
#guard parseOracleParts (name := "") "When Bilbo Baggins enters, draw a card." == none
#guard parseOracleParts (name := "Gandalf") "When Bilbo Baggins enters, draw a card." == none
#guard parseOracleParts (name := "Bilbo") "When Bilbo Baggins enters, draw a card." == none
#guard parseOracleParts (name := "Bilbo Baggins, Burglar")
    "When Bilbo Baggins enters, draw a card." ==
  some [.ability (.triggered (.enter .this) (.draw (.controller .this) 1))]
#guard parseOracleParts (name := "Bilbo Baggins, Burglar")
    "When Bilbo Baggins, Burglar enters, draw a card." ==
  some [.ability (.triggered (.enter .this) (.draw (.controller .this) 1))]
#guard parseOracleParts (name := "") "When this creature enters, draw two cards." ==
  some [.ability (.triggered (.enter .this) (.draw (.controller .this) 2))]
#guard parseOracleParts (name := "")
  "Whenever you draw your second card each turn, draw a card." == none
#guard parseOracleParts (name := "")
  "Whenever you draw your second card each turn, put a +1/+1 counter on target creature." == none
#guard parseOracleParts (name := "Lakeshore Apothecary")
  "Whenever you draw your second card each turn, put a +1/+1 counter on this creature." ==
  some [.ability (
    .triggered
      (.ordinal 2 .turnStart (.draw (.controller .this) .all))
      (.putCounter (.source .this) .plusOnePlusOne 1))]
#guard parseOracleParts (name := "")
  "Whenever you draw a card, draw a card." == none
#guard parseOracleParts (name := "")
  "Whenever you draw a card, put a +1/+1 counter on target creature." == none
#guard parseOracleParts (name := "")
  "Whenever you draw a card, if you control another Hero, put a +1/+1 counter on this creature." == none
#guard parseOracleParts (name := "Ravenhill Flock")
  "Whenever you draw a card, put a +1/+1 counter on this creature." ==
  some [.ability (
    .triggered
      (.draw (.controller .this) .all)
      (.putCounter (.source .this) .plusOnePlusOne 1))]
#guard parseOracleParts (name := "Ravenhill Flock")
  "Flying\nWhenever you draw a card, put a +1/+1 counter on this creature." ==
  some [
    .ability (.keyword .flying),
    .ability (
      .triggered
        (.draw (.controller .this) .all)
        (.putCounter (.source .this) .plusOnePlusOne 1))]
#guard parseOracleParts (name := "") "Scry 2." ==
  some [.actions [.scry (.controller .this) 2]]
#guard parseOracleParts (name := "")
  "Scry 2. (Then exile this card. You may cast the creature later from exile.)" ==
  some [.actions [.scry (.controller .this) 2]]
#guard parseOracleParts (name := "")
  "Target creature you control gains hexproof until end of turn." ==
  some [.actions [
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
  some [.ability (
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
  some [.actions [
    .tap (.targets 1 (.range 1 2) (.intersection [.permanent, .cardType .creature]))]]
#guard parseOracleParts (name := "") "Tap two or one target creatures." == none
#guard parseOracleParts (name := "") "//ADV//\nSpew Flame {4}{R}\nSorcery — Adventure" ==
  some [.alternative [
    .name "Spew Flame",
    .manaCost [.generic 4, .mono .red],
    .type .sorcery,
    .subtype .adventure]]
#guard parseOracleParts (name := "")
  "This spell costs {3} less to cast if it targets a tapped creature." ==
  some [.ability (
    .stackStatic
      (.if
        (.targetsIncludeAny
          .this
          (.intersection [
            .permanent,
            .cardType .creature,
            .tapped]))
        [.reduceCost .this [.mana [.generic 3]]]))]
#guard parseOracleParts (name := "")
  "This spell costs {1} less to cast if it targets an attacking nontoken creature." ==
  some [.ability (
    .stackStatic
      (.if
        (.targetsIncludeAny
          .this
          (.intersection [
            .permanent,
            .cardType .creature,
            .attacking .all,
            .not .token]))
        [.reduceCost .this [.mana [.generic 1]]]))]
#guard parseOracleParts (name := "")
  "This spell costs {1} less to cast if it targets an attacking creature." == none
#guard parseOracleParts (name := "") "Magnificent End deals 5 damage to target creature." == none
#guard parseOracleParts (name := "Shock") "Magnificent End deals 5 damage to target creature." == none
#guard parseOracleParts (name := "Magnificent End")
    "Magnificent End deals 5 damage to target creature." ==
  some [.actions [
    .dealDamage
      .this
      (.target 1 (.intersection [.permanent, .cardType .creature]))
      (.nat 5)]]
#guard parseOracleParts (name := "") "This spell deals 5 damage to target creature." ==
  some [.actions [
    .dealDamage
      .this
      (.target 1 (.intersection [.permanent, .cardType .creature]))
      (.nat 5)]]
#guard parseOracleParts (name := "Smaug, the Great Calamity")
    "//ADV//\nSpew Flame {4}{R}\nSorcery — Adventure\nSpew Flame deals 5 damage to target creature." ==
  some [.alternative [
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
  some [
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
  some [.actions [
    .untap
      (.target
        1
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)]))]]
#guard parseOracleParts (name := "")
  "Untap target creature you control. It gets +2/+2 until end of turn. If it's a Dwarf, you may attach an Equipment you control to it." ==
  some [.actions [
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
#guard parseOracleParts (name := "Confusticate and Bebother")
  "Choose one —\n• Counter target spell unless its controller pays {4}.\n• Draw two cards, then discard a card." ==
  some [.actions [
    .chooseMode [
      .preventable (.controller (.targetReference 1)) [.mana [.generic 4]]
        (.counter (.target 1 .spell)),
      .sequence [
        .draw (.controller .this) 2,
        .discard (.controller .this) 1]]]]
#guard parseOracleParts (name := "")
  "Choose one —\n• Counter target spell unless its controller pays {4}.\n• Gain control of target creature." == none
#guard parseOracleParts (name := "")
  "Counter target spell unless its controller pays {4}." == none
#guard parseOracleParts (name := "") "" == some []
#guard parseOracleParts (name := "") "(This is reminder text.)" == some []
#guard parseOracleParts (name := "") "Lifelink\nDraw a card." == none
#guard parseOracleParts (name := "") "Scry 2. Draw a card." == none
#guard parseOracleParts (name := "")
  "Untap target creature you control. Draw a card." == none
#guard parseOracleParts (name := "")
  "Flying\n//ADV//\nSpew Flame {4}{R}\nSorcery — Adventure\nDraw a card." == none
#guard parseOracleParts (name := "") "//ADV//\nSpew Flame {Z}\nSorcery — Adventure" == none
#guard parseOracleParts (name := "") "//ADV//\nSpew Flame {4}{R}\nNot a type" == none
#guard parseOracleParts (name := "")
  "Choose one —\n• Gain control of target creature.\n• Draw two cards, then discard a card." == none
#guard parseOracleParts (name := "Thranduil's Decree")
  "Counter target spell. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled." ==
  some [.actions [
    .actionId 1 (.counter (.target 1 .spell)),
    .continuous
      [.replace
        (.putToGraveyard (.intersection [.wasObjectOfAction 1, .permanentSpell]))
        [.actionId 2 (.exile (.replacingObject)),
          .continuous
            [.canCastWithoutPayingManaCost (.controller .this) (.wasCreatedByAction 2)]
            .endOfGame]]
      .endOfGame]]
#guard parseOracleParts (name := "") "Counter target spell." == none
#guard parseOracleParts (name := "Thranduil's Decree")
  "Counter target spell. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. Draw a card." == none
#guard parseOracleParts (name := "Bilbo, Luckwearer") "Bilbo can't be blocked." ==
  some [.ability (.static (.forbid (.block .any .this)))]
#guard parseOracleParts (name := "") "This creature can't be blocked." ==
  some [.ability (.static (.forbid (.block .any .this)))]
#guard parseOracleParts (name := "Gandalf") "Bilbo can't be blocked." == none
#guard parseOracleParts (name := "Bilbo, Luckwearer")
  "Bilbo can't be blocked by Goblins." == none
#guard parseOracleParts (name := "Bilbo, Luckwearer")
  "Whenever Bilbo deals combat damage to a player, draw a card, then discard a card." ==
  some [.ability (
    .triggered
      (.combatDamage .this .player)
      (.sequence [
        .draw (.controller .this) 1,
        .discard (.controller .this) 1]))]
#guard parseOracleParts (name := "Gandalf")
  "Whenever Bilbo deals combat damage to a player, draw a card, then discard a card." == none
#guard parseOracleParts (name := "Bilbo, Luckwearer")
  "Whenever Bilbo deals combat damage to a player, draw a card." == none
#guard parseOracleParts (name := "")
  "Exchange control of two target nonland permanents that share a card type." ==
  some [.actions [
    .exchangeControl
      (.targetSet
        1
        (.range 2 2)
        (.intersection [.permanent, .not .land])
        [.shareCardType])]]
#guard parseOracleParts (name := "")
  "Exchange control of one target nonland permanent that share a card type." == none
#guard parseOracleParts (name := "")
  "Exchange control of two target creatures that share a card type." == none
#guard parseOracleParts (name := "Bilbo, Luckwearer")
  "Bilbo can't be blocked.\nWhenever Bilbo deals combat damage to a player, draw a card, then discard a card.\n//ADV//\nBurglar's Plot {4}{U}\nSorcery — Adventure\nExchange control of two target nonland permanents that share a card type. (Then exile this card. You may cast the creature later from exile.)" ==
  some [
    .ability (.static (.forbid (.block .any .this))),
    .ability (
      .triggered
        (.combatDamage .this .player)
        (.sequence [
          .draw (.controller .this) 1,
          .discard (.controller .this) 1])),
    .alternative [
      .name "Burglar's Plot",
      .manaCost [.generic 4, .mono .blue],
      .type .sorcery,
      .subtype .adventure,
      .actions [
        .exchangeControl
          (.targetSet
            1
            (.range 2 2)
            (.intersection [.permanent, .not .land])
            [.shareCardType])]]]
#guard parseOracleParts (name := "")
  "Target creature's owner puts it on their choice of the top or bottom of their library." ==
  some [.actions [
    .playerSelectAction (.owner (.targetReference 1)) (.range 1 1)
      [.putOnTopOfLibrary
        (.target 1 (.intersection [.permanent, .cardType .creature])),
        .putOnBottomOfLibrary (.targetReference 1)]]]
#guard parseOracleParts (name := "")
  "When this creature dies, target creature an opponent controls gets -1/-1 until end of turn." ==
  some [.ability (
    .triggered
      (.die .this)
      (.continuous
        [.addPowerToughness
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.opponent (.controller .this))])) (Value.int (-1)) (Value.int (-1))]
        .endOfTurn))]
#guard parseOracleParts (name := "Front Porch Sentries")
  "When Front Porch Sentries dies, target creature an opponent controls gets -1/-1 until end of turn." ==
  some [.ability (
    .triggered
      (.die .this)
      (.continuous
        [.addPowerToughness
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.opponent (.controller .this))])) (Value.int (-1)) (Value.int (-1))]
        .endOfTurn))]
#guard parseOracleParts (name := "")
  "When this creature dies, target creature an opponent controls gets +1/+1 until end of turn." ==
  some [.ability (
    .triggered
      (.die .this)
      (.continuous
        [.addPowerToughness
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.opponent (.controller .this))])) (Value.int 1) (Value.int 1)]
        .endOfTurn))]
#guard parseOracleParts (name := "Gandalf")
  "When Front Porch Sentries dies, target creature an opponent controls gets -1/-1 until end of turn." == none
#guard parseOracleParts (name := "")
  "When another creature dies, target creature an opponent controls gets -1/-1 until end of turn." == none
#guard parseOracleParts (name := "")
  "Whenever this creature dies, target creature an opponent controls gets -1/-1 until end of turn." == none
#guard parseOracleParts (name := "")
  "When this creature dies, target creature you control gets -1/-1 until end of turn." == none
#guard parseOracleParts (name := "")
  "When this creature dies, target creature an opponent controls gets -1/-1." == none
#guard parseOracleParts (name := "")
  "When this creature dies, draw a card." == none
#guard parseOracleParts (name := "")
  "Whenever one or more other creatures die, scry 1." ==
  some [.ability (
    .triggered
      (.dieSimultaneously (.intersection [.not .this, .permanent, .cardType .creature]) [])
      (.scry (.controller .this) 1))]
#guard parseOracleParts (name := "Great Fierce Bee")
  "Whenever one or more other creatures die, scry 1. (Look at the top card of your library. You may put that card on the bottom.)" ==
  some [.ability (
    .triggered
      (.dieSimultaneously (.intersection [.not .this, .permanent, .cardType .creature]) [])
      (.scry (.controller .this) 1))]
#guard parseOracleParts (name := "")
  "Whenever one or more other creatures die, scry 2." ==
  some [.ability (
    .triggered
      (.dieSimultaneously (.intersection [.not .this, .permanent, .cardType .creature]) [])
      (.scry (.controller .this) 2))]
#guard parseOracleParts (name := "Great Fierce Bee")
  "Flying\nWhenever one or more other creatures die, scry 1. (Look at the top card of your library. You may put that card on the bottom.)" ==
  some [
    .ability (.keyword .flying),
    .ability (
      .triggered
        (.dieSimultaneously (.intersection [.not .this, .permanent, .cardType .creature]) [])
        (.scry (.controller .this) 1))]
#guard parseOracleParts (name := "")
  "Whenever one or more creatures die, scry 1." == none
#guard parseOracleParts (name := "")
  "Whenever one or more other creatures you control die, scry 1." == none
#guard parseOracleParts (name := "")
  "When one or more other creatures die, scry 1." == none
#guard parseOracleParts (name := "")
  "Whenever another creature dies, scry 1." == none
#guard parseOracleParts (name := "")
  "Whenever one or more other creatures die, draw a card." == none
#guard parseOracleParts (name := "")
  "Whenever one or more other creatures die, scry 0." == none
#guard parseOracleParts (name := "")
  "Whenever one or more other creatures die." == none
#guard parseOracleParts (name := "")
  "Target spell's owner puts it on their choice of the top or bottom of their library." == none
#guard parseOracleParts (name := "")
  "Target creature's owner puts it on top of their library." == none
#guard parseOracleParts (name := "Uneasy Partings")
  "This spell costs {1} less to cast if it targets an attacking nontoken creature.\nTarget creature's owner puts it on their choice of the top or bottom of their library." ==
  some [
    .ability (
      .stackStatic
        (.if
          (.targetsIncludeAny
            .this
            (.intersection [
              .permanent,
              .cardType .creature,
              .attacking .all,
              .not .token]))
          [.reduceCost .this [.mana [.generic 1]]])),
    .actions [
      .playerSelectAction (.owner (.targetReference 1)) (.range 1 1)
        [.putOnTopOfLibrary
          (.target 1 (.intersection [.permanent, .cardType .creature])),
          .putOnBottomOfLibrary (.targetReference 1)]]]
#guard parseOracleParts (name := "") "Destroy target creature." ==
  some [.actions [
    .destroy (.target 1 (.intersection [.permanent, .cardType .creature]))]]
#guard parseOracleParts (name := "") "Destroy target spell." == none
#guard parseOracleParts (name := "") "Destroy target creature with flying." == none
#guard parseOracleParts (name := "")
  "As an additional cost to cast this spell, sacrifice an artifact or creature or pay {4}." ==
  some [.ability (.stackStatic (
    .additionalCost .this
      [.or [
        .sacrificeCount
          (.intersection [
            .permanent,
            .union [.cardType .artifact, .cardType .creature]])
          1,
        .mana [.generic 4]]]))]
#guard parseOracleParts (name := "")
  "As an additional cost to cast this spell, sacrifice an artifact or creature." == none
#guard parseOracleParts (name := "")
  "As an additional cost to cast this spell, sacrifice artifact or creature or pay {4}." == none
#guard parseOracleParts (name := "")
  "As an additional cost to cast this spell, discard a card or pay {4}." == none
#guard parseOracleParts (name := "")
  "As an additional cost to cast this spell, sacrifice an artifact or creature or pay {4}{B}." == none
#guard parseOracleParts (name := "Stir Up Trouble")
  "As an additional cost to cast this spell, sacrifice an artifact or creature or pay {4}.\nDestroy target creature." ==
  some [
    .ability (.stackStatic (
      .additionalCost .this
        [.or [
          .sacrificeCount
            (.intersection [
              .permanent,
              .union [.cardType .artifact, .cardType .creature]])
            1,
          .mana [.generic 4]]])),
    .actions [
      .destroy
        (.target 1 (.intersection [.permanent, .cardType .creature]))]]
#guard parseOracleParts (name := "Desolation Prowler")
  "Pay 2 life: This creature gets +2/+2 until end of turn. Activate only once each turn." ==
  some [.ability (
    .abilityId 1
      (.activatedIf
        (.didNotHappen (.abilityWithIdActivated 1) .turnStart)
        [.life 2]
        (.continuous
          [.addPowerToughness (.source .this) (Value.int 2) (Value.int 2)]
          .endOfTurn)))]
#guard parseOracleParts (name := "")
  "Pay 2 life: This creature gets +2/+2 until end of turn." ==
  some [.ability (
    .activated
      [.life 2]
      (.continuous
        [.addPowerToughness (.source .this) (Value.int 2) (Value.int 2)]
        .endOfTurn))]
#guard parseOracleParts (name := "")
  "Pay 2 life: This creature gets +2/+2 until end of turn. Activate only twice each turn." == none
#guard parseOracleParts (name := "")
  "Pay 0 life: This creature gets +2/+2 until end of turn." == none
#guard parseOracleParts (name := "") "Pay 2 life: Draw a card." == none
#guard parseOracleParts (name := "Ravening Warg")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, you gain 2 life." ==
  some [.ability (
    .triggeredWhile
      (.attack .this .all)
      (.any
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this),
          .powerAtLeast (Value.int 4)]))
      (.gainLife (.controller .this) 2))]
#guard parseOracleParts (name := "Ravening Warg")
  "Whenever this creature attacks while you control a creature with power 4 or greater, you gain 2 life." ==
  parseOracleParts (name := "Ravening Warg")
    "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, you gain 2 life."
#guard parseOracleParts (name := "")
  "Whenever this creature attacks while you control a creature with power 3 or greater, you gain 2 life." == none
#guard parseOracleParts (name := "")
  "Landfall — Whenever this creature attacks while you control a creature with power 4 or greater, you gain 2 life." == none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks, you gain 2 life." == none
#guard parseOracleParts (name := "")
  "Put a +1/+1 counter on up to one target creature. Target player gains 2 life." ==
  some [.actions [
    .putCounter
      (.targets 1 (.range 0 1) (.intersection [.permanent, .cardType .creature]))
      .plusOnePlusOne
      1,
    .gainLife (.target 2 .player) 2]]
#guard parseOracleParts (name := "") "Put a +1/+1 counter on target creature." == none
#guard parseOracleParts (name := "")
  "Put two +1/+1 counters on up to one target creature." == none
#guard parseOracleParts (name := "") "Target opponent gains 2 life." == none
#guard parseOracleParts (name := "") "You gain 0 life." == none
#guard parseOracleParts (name := "") "You gain 2 life." ==
  some [.actions [.gainLife (.controller .this) 2]]
#guard parseOracleParts (name := "Gollum, Silent Slinker")
  "Menace (This creature can't be blocked except by two or more creatures.)\n//ADV//\nMeager Meal {B}\nSorcery — Adventure\nPut a +1/+1 counter on up to one target creature. Target player gains 2 life. (Then exile this card. You may cast the creature later from exile.)" ==
  some [
    .ability (.keyword .menace),
    .alternative [
      .name "Meager Meal",
      .manaCost [.mono .black],
      .type .sorcery,
      .subtype .adventure,
      .actions [
        .putCounter
          (.targets 1 (.range 0 1) (.intersection [.permanent, .cardType .creature]))
          .plusOnePlusOne
          1,
        .gainLife (.target 2 .player) 2]]]
#guard parseOracleParts (name := "Dreaded Bat-Cloud")
  "This spell costs {3} less to cast if a creature died this turn.\nFlying, deathtouch" ==
  some [
    .ability (
      .stackStatic
        (.if
          (.happened (.die (.cardType .creature)) .turnStart)
          [.reduceCost .this [.mana [.generic 3]]])),
    .ability (.keyword .flying),
    .ability (.keyword .deathtouch)]
#guard parseOracleParts (name := "")
  "This spell costs {3} less to cast if a creature you control died this turn." == none
#guard parseOracleParts (name := "")
  "This spell costs {3} less to cast if two creatures died this turn." == none
#guard parseOracleParts (name := "")
  "When this Equipment enters, target opponent sacrifices a creature of their choice." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.sacrifice
        (.selected
          (.target 1 (.opponent (.controller .this)))
          (.range 1 1)
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.targetReference 1)]))))]
#guard parseOracleParts (name := "Crude Bent Blade")
  "When Crude Bent Blade enters, target opponent sacrifices a creature of their choice." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.sacrifice
        (.selected
          (.target 1 (.opponent (.controller .this)))
          (.range 1 1)
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.targetReference 1)]))))]
#guard parseOracleParts (name := "Gandalf")
  "When Crude Bent Blade enters, target opponent sacrifices a creature of their choice." == none
#guard parseOracleParts (name := "")
  "When this Equipment enters, target opponent sacrifices a creature." == none
#guard parseOracleParts (name := "")
  "When another Equipment enters, target opponent sacrifices a creature of their choice." == none
#guard parseOracleParts (name := "")
  "When this Equipment enters, target opponent sacrifices an artifact of their choice." == none
#guard parseOracleParts (name := "") "Equipped creature gets +2/+1." ==
  some [.ability (.static (.addPowerToughness (.hostOf .this) (Value.int 2) (Value.int 1)))]
#guard parseOracleParts (name := "") "Equipped creature gets +2/+1 until end of turn." == none
#guard parseOracleParts (name := "") "Equipped creature gets +2/+1 and has flying." == none
#guard parseOracleParts (name := "") "Equip {2}" ==
  some [.ability (.keywordWithCost .equip [.mana [.generic 2]])]
#guard parseOracleParts (name := "")
  "Equip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)" ==
  some [.ability (.keywordWithCost .equip [.mana [.generic 2]])]
#guard parseOracleParts (name := "") "Equip" == none
#guard parseOracleParts (name := "") "Equip {2}: Draw a card." == none
#guard parseOracleParts (name := "Crude Bent Blade")
  "When this Equipment enters, target opponent sacrifices a creature of their choice.\nEquipped creature gets +2/+1.\nEquip {2} ({2}: Attach to target creature you control. Equip only as a sorcery.)" ==
  some [
    .ability (
      .triggered
        (.enter .this)
        (.sacrifice
          (.selected
            (.target 1 (.opponent (.controller .this)))
            (.range 1 1)
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.targetReference 1)])))),
    .ability (.static (.addPowerToughness (.hostOf .this) (Value.int 2) (Value.int 1))),
    .ability (.keywordWithCost .equip [.mana [.generic 2]])]

#guard parseOracleParts (name := "Gollum the Abandoned") "Gollum can't block." ==
  some [.ability (.static (.forbid (.block .this .any)))]
#guard parseOracleParts (name := "Gollum the Abandoned") "When Gollum enters, draw a card." ==
  some [.ability (.triggered (.enter .this) (.draw (.controller .this) 1))]
#guard parseOracleParts (name := "Gandalf") "Gollum can't block." == none
#guard parseOracleParts (name := "Gandalf") "When Gollum enters, draw a card." == none
#guard parseOracleParts (name := "") "This creature can't block." ==
  some [.ability (.static (.forbid (.block .this .any)))]
#guard parseOracleParts (name := "") "This creature can't block unless you control a Goblin." ==
  none
#guard parseOracleParts (name := "Gollum the Abandoned")
  "When Gollum enters, exile up to one target card from an opponent's graveyard. Each opponent loses 2 life." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.sequence [
        .exile
          (.targets 1 (.range 0 1)
            (.intersection [.inGraveyard, .owner (.opponent (.controller .this))])),
        .loseLife (.opponent (.controller .this)) 2]))]
#guard parseOracleParts (name := "")
  "When this creature enters, exile up to one target card from an opponent's graveyard. Each opponent loses 2 life." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.sequence [
        .exile
          (.targets 1 (.range 0 1)
            (.intersection [.inGraveyard, .owner (.opponent (.controller .this))])),
        .loseLife (.opponent (.controller .this)) 2]))]
#guard parseOracleParts (name := "Gollum the Abandoned")
  "When Bilbo enters, exile up to one target card from an opponent's graveyard. Each opponent loses 2 life." ==
  none
#guard parseOracleParts (name := "")
  "When this creature enters, exile up to one target creature card from an opponent's graveyard. Each opponent loses 2 life." ==
  none
#guard parseOracleParts (name := "")
  "{2}, Sacrifice an artifact or creature: Return this card from your graveyard to your hand. Activate only as a sorcery." ==
  some [.ability (
    .graveyardActivatedIf
      (.timeToCastSorcery (.controller .this))
      [.mana [.generic 2],
        .sacrificeCount
          (.intersection [
            .permanent,
            .union [.cardType .artifact, .cardType .creature]])
          1]
      (.returnToHand (.intersection [.inGraveyard, .source .this])))]
#guard parseOracleParts (name := "")
  "{2}, Sacrifice an artifact or creature: Return this card from your graveyard to your hand." ==
  none
#guard parseOracleParts (name := "")
  "{2}: Return this card from your graveyard to the battlefield." == none
#guard parseOracleParts (name := "Gollum the Abandoned")
  "Gollum can't block.\nWhen Gollum enters, exile up to one target card from an opponent's graveyard. Each opponent loses 2 life.\n{2}, Sacrifice an artifact or creature: Return this card from your graveyard to your hand. Activate only as a sorcery." ==
  some [
    .ability (.static (.forbid (.block .this .any))),
    .ability (
      .triggered
        (.enter .this)
        (.sequence [
          .exile
            (.targets 1 (.range 0 1)
              (.intersection [.inGraveyard, .owner (.opponent (.controller .this))])),
          .loseLife (.opponent (.controller .this)) 2])),
    .ability (
      .graveyardActivatedIf
        (.timeToCastSorcery (.controller .this))
        [.mana [.generic 2],
          .sacrificeCount
            (.intersection [
              .permanent,
              .union [.cardType .artifact, .cardType .creature]])
            1]
        (.returnToHand (.intersection [.inGraveyard, .source .this])))]

#guard parseOracleParts (name := "")
  "Target creature gets +2/+2 and gains lifelink until end of turn." ==
  some [.actions [
    .continuous
      [.addPowerToughness
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        (Value.int 2) (Value.int 2),
       .gainAbility (.targetReference 1) (.keyword .lifelink)]
      .endOfTurn]]
#guard parseOracleParts (name := "")
  "Target creature gets +2/+2 and has lifelink until end of turn." == none
#guard parseOracleParts (name := "")
  "Target creature gets -5/-5 until end of turn. If that creature would die this turn, exile it instead." ==
  some [.actions [
    .continuous
      [.addPowerToughness
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        (Value.int (-5)) (Value.int (-5)),
       .replace
         (.putToGraveyard (.targetReference 1))
         [.exile (.replacingObject)]]
      .endOfTurn]]
#guard parseOracleParts (name := "")
  "Target creature gets -5/-5 until end of turn. Exile it instead." == none
#guard parseOracleParts (name := "")
  "Creatures target player controls get -1/-1 until end of turn." ==
  some [.actions [
    .continuous
      [.addPowerToughness
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.target 1 .player)])
        (Value.int (-1)) (Value.int (-1))]
      .endOfTurn]]
#guard parseOracleParts (name := "")
  "Creatures target player controls get -1/-1." == none
#guard parseOracleParts (name := "")
  "Target player draws two cards and loses 2 life." ==
  some [.actions [
    .sequence [
      .draw (.target 1 .player) 2,
      .loseLife (.targetReference 1) 2]]]
#guard parseOracleParts (name := "")
  "Target player draws two cards and gains 2 life." == none
#guard parseOracleParts (name := "")
  "Choose one —\n• Target creature gets -5/-5 until end of turn. If that creature would die this turn, exile it instead.\n• Creatures target player controls get -1/-1 until end of turn." ==
  some [.actions [
    .chooseMode [
      .continuous
        [.addPowerToughness
          (.target 1 (.intersection [.permanent, .cardType .creature]))
          (Value.int (-5)) (Value.int (-5)),
         .replace
           (.putToGraveyard (.targetReference 1))
           [.exile (.replacingObject)]]
        .endOfTurn,
      .continuous
        [.addPowerToughness
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.target 2 .player)])
          (Value.int (-1)) (Value.int (-1))]
        .endOfTurn]]]
#guard parseOracleParts (name := "")
  "Choose one —\n• Target player draws two cards and loses 2 life.\n• Target creature gets +2/+2 and gains lifelink until end of turn." ==
  some [.actions [
    .chooseMode [
      .sequence [
        .draw (.target 1 .player) 2,
        .loseLife (.targetReference 1) 2],
      .continuous
        [.addPowerToughness
          (.target 2 (.intersection [.permanent, .cardType .creature]))
          (Value.int 2) (Value.int 2),
         .gainAbility (.targetReference 2) (.keyword .lifelink)]
        .endOfTurn]]]
#guard parseOracleParts (name := "")
  "Choose one —\n• Target creature gets -5/-5 until end of turn. If that creature would die this turn, exile it instead.\n• Gain control of target creature." ==
  none
#guard parseOracleParts (name := "")
  "When this creature enters, each opponent discards a card." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.discard (.opponent (.controller .this)) 1))]
#guard parseOracleParts (name := "")
  "When another creature enters, each opponent discards a card." == none
#guard parseOracleParts (name := "")
  "When this creature enters, each opponent discards a card of their choice." == none
#guard parseOracleParts (name := "Gandalf, Spark Starter")
  "When Gandalf enters, he deals 3 damage divided as you choose among one, two, or three targets." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.divideDamage
        (.controller .this)
        (.source .this)
        (.targets 1 (.range 1 3) .all)
        3))]
#guard parseOracleParts (name := "Gandalf, Spark Starter")
  "Reach\nWhen Gandalf enters, he deals 3 damage divided as you choose among one, two, or three targets." ==
  some [
    .ability (.keyword .reach),
    .ability (
      .triggered
        (.enter .this)
        (.divideDamage
          (.controller .this)
          (.source .this)
          (.targets 1 (.range 1 3) .all)
          3))]
#guard parseOracleParts (name := "Gandalf")
  "When Bilbo enters, he deals 3 damage divided as you choose among one, two, or three targets." ==
  none
#guard parseOracleParts (name := "Gandalf, Spark Starter")
  "When Gandalf enters, Bilbo deals 3 damage divided as you choose among one, two, or three targets." ==
  none
#guard parseOracleParts (name := "Gandalf, Spark Starter")
  "When Gandalf enters, he deals 3 damage divided as you choose among one or four targets." == none
#guard parseOracleParts (name := "Gandalf, Spark Starter")
  "When Gandalf enters, he deals 0 damage divided as you choose among one, two, or three targets." ==
  none
#guard parseOracleParts (name := "Gandalf, Spark Starter")
  "When Gandalf enters, he deals 3 damage divided as you choose among one, two, or three target creatures." ==
  none
#guard parseOracleParts (name := "")
  "When this Equipment enters, you may discard a card. If you do, draw two cards." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.sequence [
        .optional
          (.actionId 1 (.discard (.controller .this) 1)),
        .if (.happened (.actionWithId 1) .gameStart) [.draw (.controller .this) 2]]))]
#guard parseOracleParts (name := "")
  "When this Equipment enters, you may discard a card. Draw two cards." == none
#guard parseOracleParts (name := "")
  "When this Equipment enters, discard a card. If you do, draw two cards." == none
#guard parseOracleParts (name := "")
  "When this Equipment enters, you may discard a card. If you do, draw two cards.\nEquipped creature gets +2/+0.\nEquip {3} ({3}: Attach to target creature you control. Equip only as a sorcery.)" ==
  some [
    .ability (
      .triggered
        (.enter .this)
        (.sequence [
          .optional
            (.actionId 1 (.discard (.controller .this) 1)),
          .if (.happened (.actionWithId 1) .gameStart) [.draw (.controller .this) 2]])),
    .ability (.static (.addPowerToughness (.hostOf .this) (Value.int 2) (Value.int 0))),
    .ability (.keywordWithCost .equip [.mana [.generic 3]])]
#guard parseOracleParts (name := "Smaug, the Great Calamity")
  "Flying\n//ADV//\nSpew Flame {4}{R}\nSorcery — Adventure\nSpew Flame deals 5 damage to target creature. (Then exile this card. You may cast the creature later from exile.)" ==
  some [
    .ability (.keyword .flying),
    .alternative [
      .name "Spew Flame",
      .manaCost [.generic 4, .mono .red],
      .type .sorcery,
      .subtype .adventure,
      .actions [
        .dealDamage
          .this
          (.target 1 (.intersection [.permanent, .cardType .creature]))
          (.nat 5)]]]

end Mtg.Engine
