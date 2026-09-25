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
- `{cost}: Put <count> +1/+1 counters on this creature.`
  One counter is `a` or `one` with the singular noun; more than one uses the plural.
- `Sacrifice another <permanent type or …>: Exile the top card of your library. You may play it until the end of your next turn. Activate only during your turn and only once each turn.`
  `another` excludes this object. The activation limit is that timing restriction
  (CR 602.5). The exiled card may be played until the end of your next turn
  (CR 611.2a).
- `{cost}: <this> becomes a <subtype> creature in addition to its other types and gains "<static>".`
  `<this>` is `this`, `this <type>`, the card's name, or the short name before a comma.
  No duration is printed, so the effect lasts until the end of the game (CR 611.2a).
  The quoted text is a static ability this object gains. The static ability recognized
  here is `This creature's power and toughness are each equal to the number of lands you control`
  (CR 208.2a / 604.3). A reminder such as `(This effect doesn't end.)` is not rules text.
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
- `Destroy target <permanent type or …> [with <keyword> | with power N or greater].`
  `N` is a positive printed number. The permanent must have at least that much power.
- `Put a +1/+1 counter on up to one target <permanent type>.`
  Up to one target means zero or one (CR 115.1).
- `Target player gains N life.`
- `You gain N life.`
- `<this card> deals N damage to target <permanent type>.`
  The source is `this`, `this <type>`, the card's name, or the short name
  before a comma (`Bilbo Baggins` for `Bilbo Baggins, Burglar`, CR 201.5).
  `N` is a positive printed number.
- `Whenever this creature attacks, it gets +P/+T until end of turn for each other creature you control.`
- `Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, you gain N life.`
  The ability word has no rules meaning (CR 207.2c). The “while” clause is
  part of the trigger condition (CR 603.2) and is not checked again on
  resolution. The word may be omitted.
- `Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, this creature gets +P/+T until end of turn.`
  The same ability word and “while” clause. The bonus is on this creature.
- `Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +P/+0 and creatures you control gain trample.`
  The same ability word and “while” clause. The bonus and trample both last
  until end of turn. Toughness is unchanged, and the power bonus is not zero.
- `Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, put a +1/+1 counter on each creature you control.`
  The same ability word and “while” clause. One counter goes on each of those creatures.
- `Ferocious — Whenever you attack while you control a creature with power 4 or greater, you draw a card and lose 1 life.`
  The ability word may be omitted. “Whenever you attack” is one trigger when
  creatures you control attack at the same time (CR 508.3 / 603.2d). The
  “while” clause is part of that trigger condition.
- `Ferocious — At the beginning of combat on your turn, if you control a creature with power 4 or greater, put a +1/+1 counter on this creature.`
  The ability word may be omitted. Beginning of combat is CR 507.1. The “if”
  is an intervening if (CR 603.4): it is checked when combat begins and again
  when the ability resolves.
- `Landfall — Whenever a land you control enters, put a +1/+1 counter on target <permanent type> you control.`
  `Landfall` is an ability word (CR 207.2c) and may be omitted.
- `Landfall — Whenever a land you control enters, this creature gets +P/+T until end of turn.`
  `Landfall` may be omitted. The bonus is on this creature and lasts until end of turn.
- `Whenever another Elf you control enters, this creature gets +1/+1 until end of turn.`
  `another` excludes this object.
- `{T}: Add X mana of any one color, where X is <this>'s power. Spend this mana only to cast Elf spells and activate abilities of Elf sources.`
  `<this>` is `this creature` or the card's name. The tap symbol is the cost (CR 107.5).
  That mana can be spent only on Elf spells and activated abilities of Elf sources.
- `<this>'s power and toughness are each equal to the number of lands you control.`
  A characteristic-defining ability (CR 208.2a / 604.3). `<this>` is `this creature`
  or the card's name.
- `You may play an additional land this turn.`
- `When <this card> enters, search your library for a Forest card, put that card onto the battlefield, then shuffle.`
  The entering object is `this`, `this <type>`, the card's name, or the short name
  before a comma.
- `When <this card> enters, draw a card.` / `draw N cards.`
  The entering object is `this`, `this <type>`, the card's name, or that short name
- `When <this card> enters, put a +1/+1 counter on target <permanent type>.`
  The entering object is the same. The counter goes on that target.
- `When <this card> enters, recruit.`
  Recruit is a keyword action of this card's controller. A trailing reminder
  parenthetical is not rules text (CR 207.2).
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
- `Target <permanent> you control deals damage equal to its power to target <permanent> an opponent controls.`
- `Whenever <this card> attacks, choose up to one other target <permanent type> you control. Its base power and toughness become equal to <this card>'s power and toughness until end of turn.`
  The attacker is `this`, `this <type>`, the card's name, or the short name
  before a comma. Up to one target means zero or one (CR 115.1).
- `Choose one —` followed by `•` modes:
  - `Counter target spell unless its controller pays {cost}.`
  - `Draw <count> cards, then discard <count> card(s).`
  - `Target <permanent type> gets +P/+T until end of turn.`
  - `Target <permanent type> gets +P/+T and gains <keywords> until end of turn.`
  - `Target creature gets +P/+T until end of turn. If that creature would die this turn, exile it instead.`
  - `<permanent types> target player controls get +P/+T until end of turn.`
  - `Target player draws <count> cards and loses N life.`
  - `Destroy target <permanent type or …> [with <keyword> | with power N or greater].`
  - `Destroy target <permanent type or …>. You gain N life.`
  - `<permanents> you control get +P/+T until end of turn.`
  - `Until end of turn, target creature becomes an artifact in addition to its other types and gains indestructible.`
    A trailing reminder parenthetical is not rules text (CR 207.2).
  - `Put a +1/+1 counter on target <permanent> [you control]. It gains <keywords> until end of turn.`
- `Counter target spell. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled.`
- `<this card> can't be blocked.`
  The subject is `this`, `this <type>`, the card's name, or the short name
  before a comma
- `<this card> can't be blocked by tokens.`
  The subject is the same. Tokens cannot be declared as blockers for it.
- `<this card> can't block.`
  The subject is the same as for “can't be blocked”
- `When <this card> enters, exile up to one target card from an opponent's graveyard. Each opponent loses N life.`
- `{cost}, Sacrifice an <permanent type or …>: Return this card from your graveyard to your hand. Activate only as a sorcery.`
  Returning this card from a graveyard functions while the card is in that
  graveyard (CR 113.6), so the ability is `graveyardActivatedIf`
- `Whenever <this card> deals combat damage to a player, draw <count> cards, then discard <count> card(s).`
- `Exchange control of <count> target nonland permanents that share a card type.`
- `Target <permanent type>'s owner puts it on their choice of the top or bottom of their library.`
- `<this> enters tapped.`
  A replacement effect (CR 614.1). `<this>` is `this`, `this <permanent type>`,
  the card's name, or the short name before a comma.
- `{T}: Add {A} or {B}.`
  Two or more colored or colorless symbols, joined by `or`. The tap symbol is
  the cost (CR 107.5). The player adds one of them.
- `{cost}: Target creature can't be blocked this turn.`
  The restriction lasts until end of turn.
- `Put <count> +1/+1 counters on target <creature type> [you control].`
  One counter is `a` or `one` with the singular noun; more than one uses the
  plural. A creature type is `Elf`, `Goblin or Orc`, or `Bear, Spider, or Wolf`:
  a creature of those subtypes. Costs separated by commas may include mana,
  `{T}`, and `Sacrifice <this>`. `Activate only as a sorcery` is the timing
  restriction (CR 602.5a).
- `{T}, Sacrifice <this>: Search your library for a basic land card, put it onto the battlefield tapped, then shuffle.`
- `<type>cycling {cost}`
  Typecycling (CR 702.29). `<type>` is a subtype (`Halflingcycling`), a card
  type, or supertypes plus a type (`Basic landcycling`). A trailing reminder
  parenthetical is not rules text.
- `When <this> enters, you gain N life.`
- `When <this> enters, untap another target creature you control. If that creature is a <subtype>, put a +1/+1 counter on it.`
- `When <this card> dies, recruit.`
  Recruit is a keyword action of this card's controller. A trailing reminder
  parenthetical is not rules text (CR 207.2).
- `When <this card> enters, scry N.`
  `N` is a positive printed number.
- `When <this card> enters, create a Treasure token.`
  `create a tapped Treasure token` creates that token tapped (CR 110.5).
- `When <this card> enters, exile the top card of your library. Until the end of your next turn, you may play that card.`
  The exiled card may be played until the end of your next turn (CR 611.2a).
- `{cost}: Add one mana of any color.`
  Costs separated by commas may include mana, `{T}`, and `Sacrifice <this>`.
- `{cost}: Destroy target permanent.`
  The same costs. The permanent is one target.
- `<this>'s power is equal to the number of creatures you control.`
  A characteristic-defining ability (CR 208.2a / 604.3). `<this>` is `this creature`
  or the card's name. Toughness is not changed.
- `This spell can't be countered.`
  Countering this spell is forbidden. The ability functions while this spell
  is on the stack (CR 113.6b).
- `Whenever you cast a noncreature spell, amass <subtype>s N.`
  Amass is a keyword action of this card's controller (CR 701.45). The
  subtype is printed in the plural (`Goblins`). `N` is a positive count.
  A trailing reminder parenthetical is not rules text (CR 207.2).
- `When <this card> enters, amass <subtype>s N.`
  The entering object is `this`, `this <type>`, the card's name, or the short
  name before a comma. Amass is the same keyword action.
- `When <this card> dies, amass <subtype>s N.`
  The dying object is the same. Amass is the same keyword action.
- `Whenever you attack, amass <subtype>s N.`
  “Whenever you attack” is one trigger when creatures you control attack at
  the same time (CR 508.3 / 603.2d).
- `You may cast this spell as though it had flash if you control a <subtype>.`
  The permission is checked as you begin to cast this spell, before the card
  is put onto the stack (CR 601.3 / 702.8). `you` is the player who would cast
  it (`Selector.caster`), not necessarily its controller or owner. The spell
  does not gain flash.
- `<permanents> get +P/+T.`
  No duration is printed, so this is a static ability (CR 604.2 / 613.4c).
  A zero bonus is omitted. `+0/+0` is not an effect. `until end of turn` is a
  different ability.
- `Whenever <this card> enters or attacks, recruit.`
  Recruit is a keyword action of this card's controller. A trailing reminder
  parenthetical is not rules text (CR 207.2).
- `You draw a card and lose 1 life.`
  One card and 1 life. The player is this spell's controller.
- `Amass <subtype>s N.`
  Amass is a keyword action of this spell's controller (CR 701.45). The
  subtype is printed in the plural (`Goblins`). `N` is a positive count.
  A trailing reminder parenthetical is not rules text (CR 207.2).
- `Return up to one target <card type> card from your graveyard to your hand.`
  Up to one target means zero or one (CR 115.1). The card is in your graveyard.
- `Counter target spell. If that spell's mana value was N or less, recruit.`
  The spell is one target. Its mana value is recorded before it is
  countered, while it is still on the stack, so the chosen value of `{X}`
  counts (CR 202.3 / 202.3e / 107.3a). Recruit happens only when that
  recorded value is less than or equal to `N`. Recruit is a keyword action
  of this spell's controller.
  A trailing reminder parenthetical is not rules text (CR 207.2).
  Successive spell lines are one effect, in printed order.
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

def selectorOfTypes : List CardType → Selector
  | [t] => .cardType t
  | ts => .union (ts.map fun t => .cardType t)

/-- A permanent of `ts`, plus any further constraints. -/
def permanentWith (ts : List CardType) (more : List Selector := []) : Selector :=
  .intersection ([.permanent, selectorOfTypes ts] ++ more)

/-- Controlled by this object's controller (`you control`). -/
def youControl : Selector :=
  .controlled (.controller .this)

/-- Text before a trailing `you control`, and whether that phrase was present. -/
def splitYouControl (s : String) : String × Bool :=
  match before? s " you control" with
  | some obj => (obj, true)
  | none => (s, false)

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
  (after? (norm s) "target ").bind fun rest =>
    let (obj, controlled) := splitYouControl rest
    (typesInPhrase obj).map fun ts =>
      permanentWith ts (if controlled then [youControl] else [])

/-- Creature subtypes in `Elf`, `Goblin or Orc`, or `Bear, Spider, or Wolf`. -/
def parseSubtypeList (s : String) : Option (List CardSubtype) :=
  let normalized := ((norm s).replace ", or " ", ").replace " or " ", "
  let parts := normalized.splitOn ", " |>.map copied |>.filter (· != "")
  if parts.isEmpty then none else parts.mapM subtypeOfOracle?

/-- One subtype, or a union when several are printed. -/
def subtypeSelector : List CardSubtype → Selector
  | [st] => .subtype st
  | sts => .union (sts.map fun st => .subtype st)

/-- `target creature you control`, `another target creature you control`, or
`target Elf you control`. A creature type is a creature of those subtypes.
`another` excludes this object. -/
def parseBattlefieldTarget (s : String) : Option Selector :=
  let s := norm s
  let opened :=
    match after? s "another target " with
    | some rest => some (true, rest)
    | none =>
      match after? s "target " with
      | some rest => some (false, rest)
      | none => none
  opened.bind fun (another, rest) =>
    let (obj, controlled) := splitYouControl rest
    let head : List Selector :=
      (if another then [.not .this] else []) ++ [.permanent]
    let tail : List Selector := if controlled then [youControl] else []
    match typesInPhrase obj with
    | some ts => some (.intersection (head ++ [selectorOfTypes ts] ++ tail))
    | none =>
      (parseSubtypeList obj).map fun sts =>
        .intersection (head ++ [.cardType .creature, subtypeSelector sts] ++ tail)

/-- Keywords in `hexproof and indestructible` or `haste, flying, and trample`. -/
def parseKeywordPhrase (s : String) : Option (List Keyword) :=
  let commaParts := (norm s).splitOn ", " |>.map copied |>.filter (· != "")
  let tokens := commaParts.flatMap fun part =>
    let part := (after? part "and ").getD part
    part.splitOn " and " |>.map copied |>.filter (· != "")
  if tokens.isEmpty then none else tokens.mapM keywordOfOracle?

/-- Each keyword as an ability gained by `sel`. -/
def keywordGains (sel : Selector) (kws : List Keyword) : List ContinuousEffect :=
  kws.map fun k => .gainAbility sel (.keyword k)

/-- Keywords gained by target `n`. The first keyword declares the target.
Later keywords refer to that same target. -/
def gainEffects (n : Nat) (sel : Selector) (kws : List Keyword) : List ContinuousEffect :=
  match kws with
  | [] => []
  | k :: rest =>
    .gainAbility (.target n sel) (.keyword k) ::
      keywordGains (.targetReference n) rest

def parseSignedInt (s : String) : Option Int :=
  let s := copied s
  let (neg, digits) :=
    match after? s "+" with
    | some d => (false, d)
    | none =>
      match after? s "-" with
      | some d => (true, d)
      | none => (false, s)
  match natOfDigits? digits with
  | none => none
  | some n =>
    let i : Int := n
    some (if neg then -i else i)

/-- A printed power and toughness change, such as `+1/+1`. -/
def parsePowerToughness (s : String) : Option (Int × Int) :=
  match split2? s "/" with
  | some (p, t) =>
    match parseSignedInt p, parseSignedInt t with
    | some p, some t => some (p, t)
    | _, _ => none
  | none => none

/-- `creatures you control` or `other creature you control` as a battlefield
selector. A trailing `s` on a card type is the plural (`creatures`). -/
def parseControlledPhrase (s : String) : Option Selector :=
  let s := norm s
  let (obj0, controlled) := splitYouControl s
  let (obj, other) :=
    match after? obj0 "other " with
    | some obj => (obj, true)
    | none => (obj0, false)
  match typesInPhrase obj with
  | none => none
  | some ts =>
    let head : List Selector :=
      (if other then [.not .this] else []) ++ [.permanent, selectorOfTypes ts]
    let tail : List Selector :=
      if controlled then [youControl] else []
    some (.intersection (head ++ tail))

/-- `it` / `this creature`, or a controlled-permanent phrase. -/
def parsePumpWho (s : String) : Option Selector :=
  match norm s with
  | "it" | "this" | "this creature" => some (.source .this)
  | _ => parseControlledPhrase s

/-- `who gets pt` or `who get pt`. -/
def splitGets? (s : String) : Option (String × String) :=
  split2? s " gets " <|> split2? s " get "

/-- `who gets pt`. The plural `get` is a different printed verb. -/
def splitGetsOnly? (s : String) : Option (String × String) :=
  split2? s " gets "

/-- `+P/+T` and the keywords of an optional `and gains` clause.
No `and gains` is an empty keyword list. An unrecognized keyword fails. -/
def ptAndGains? (s : String) : Option (Int × Int × List Keyword) :=
  let (ptText, kws?) :=
    match split2? s " and gains " with
    | none => (s, some ([] : List Keyword))
    | some (pt, gained) => (pt, parseKeywordPhrase gained)
  match parsePowerToughness ptText, kws? with
  | some (p, t), some kws => some (p, t, kws)
  | _, _ => none

/-- Subject, power, and toughness of `<who> <split> <pt> until end of turn`. -/
def whoPtUntilEnd? (sentence : String)
    (split : String → Option (String × String)) : Option (String × Int × Int) :=
  (before? (normSentence sentence) " until end of turn").bind split |>.bind
    fun (who, ptText) =>
      (parsePowerToughness ptText).map fun (p, t) => (who, p, t)

/-- Text before `until end of turn`, and an optional `for each …` clause.
A sentence that does not end that way fails. -/
def splitUntilEnd? (s : String) : Option (String × Option String) :=
  match split2? s " until end of turn for each " with
  | some (pre, among) =>
    some (pre, if among.isEmpty then none else some among)
  | none =>
    (before? s "until end of turn").map fun body => (body, none)

/-- `+P/+T` as `addPower` and `addToughness`. A zero bonus is omitted.
The first effect declares any targets in `sel`. Later effects use
`targetReference`. `powerValue` and `toughnessValue` build the amounts. -/
def scaledPowerToughness (sel : Selector) (p t : Int)
    (powerValue : Int → Value) (toughnessValue : Int → Value) : List ContinuousEffect :=
  let power :=
    if p == 0 then [] else [.addPower sel (powerValue p)]
  let later := if power.isEmpty then sel else sel.referenceTargets
  let toughness :=
    if t == 0 then [] else [.addToughness later (toughnessValue t)]
  power ++ toughness

/-- `+P/+T` as a flat integer bonus. A zero bonus is omitted. -/
def flatPowerToughness (sel : Selector) (p t : Int) : List ContinuousEffect :=
  scaledPowerToughness sel p t Value.int Value.int

/-- `+P/+T` until end of turn, optionally once per `among`.
A zero bonus is omitted. `+0/+0` is not an effect. -/
def pumpUntilEnd (sel : Selector) (p t : Int) (among : Option Selector) :
    Option CardAction :=
  let effects :=
    match among with
    | none => flatPowerToughness sel p t
    | some among =>
      scaledPowerToughness sel p t
        (fun n => Value.timesCount n among)
        (fun n => Value.timesCount n (if p == 0 then among else among.referenceTargets))
  if effects.isEmpty then none else some (.continuous effects .endOfTurn)

/-- `+P/+T` on target `n` until end of turn, plus keywords on that same target.
No keywords is only the power and toughness change. An empty change fails. -/
def pumpGainsUntilEnd (n : Nat) (sel : Selector) (p t : Int)
    (kws : List Keyword) : Option (CardAction × Nat) :=
  let effects :=
    flatPowerToughness (.target n sel) p t ++ keywordGains (.targetReference n) kws
  if effects.isEmpty then none
  else some (.continuous effects .endOfTurn, n + 1)

/-- `<objects> get +P/+T until end of turn [for each <objects>].` -/
def parsePumpUntilEndOfTurn (sentence : String) : Option CardAction :=
  (splitUntilEnd? (normSentence sentence)).bind fun (body, among?) =>
    (splitGets? body).bind fun (who, pt) =>
      match parsePumpWho who, parsePowerToughness pt with
      | some sel, some (p, t) =>
        match among? with
        | none => pumpUntilEnd sel p t none
        | some amongText =>
          (parseControlledPhrase amongText).bind fun among =>
            pumpUntilEnd sel p t (some among)
      | _, _ => none

/-- This creature gets +P/+T until end of turn. -/
def sourceGetsUntilEnd? (action : CardAction) : Option (Int × Int) :=
  match action with
  | .continuous effects .endOfTurn => CardAction.leftoverSourcePump? effects
  | _ => none

/-- `lead` then a pump of this creature until end of turn, as `event`.
`accept` chooses which +P/+T is this ability. -/
def triggeredSourcePump (line lead : String) (event : Trigger)
    (accept : Int × Int → Bool) : Option CardPart :=
  (after? line lead).bind parsePumpUntilEndOfTurn |>.bind fun action =>
    (sourceGetsUntilEnd? action).bind fun pt =>
      if accept pt then some (.ability (.triggered event action)) else none

/-- Wrap a parsed effect as a triggered ability. -/
def onTrigger (event : Trigger) (action? : Option CardAction) : Option CardPart :=
  action?.map fun action => .ability (.triggered event action)

/-- `Whenever this creature attacks, it gets +1/+1 until end of turn for each
other creature you control.` -/
def parseAttackTriggered (line : String) : Option CardPart :=
  onTrigger (.attack .this .all)
    ((after? (normLine line) "whenever this creature attacks, ").bind parsePumpUntilEndOfTurn)

/-- `Pay 2 life` (CR 118.3). The amount is a printed number. -/
def parsePayLife (s : String) : Option Nat :=
  (between? (norm s) "pay " " life").bind positiveDigits?

/-- How many +1/+1 counters a printed `a` / `one` / `three` names.
`a` is one counter. Zero is not a count. -/
def counterCount? (s : String) : Option Nat :=
  if norm s == "a" then some 1 else positiveCount s

/-- A printed count that agrees with its noun.
One (`a`, `one`, `1`) takes the singular. Any larger count takes the plural. -/
def nounCount? (countText : String) (plural : Bool) : Option Nat :=
  (counterCount? countText).bind fun n =>
    if (n == 1) == plural then none else some n

/-- `Put a +1/+1 counter on this creature` or
`Put three +1/+1 counters on this creature`.
One counter uses the singular noun; more than one uses the plural.
`this`, `this creature`, and `it` are the source of this ability. -/
def parsePutCountersOnThis (sentence : String) : Option CardAction :=
  match after? (normSentence sentence) "put " with
  | none => none
  | some rest =>
    let split :=
      (split2? rest " +1/+1 counters on ").map (fun (c, w) => (c, true, w)) <|>
        (split2? rest " +1/+1 counter on ").map (fun (c, w) => (c, false, w))
    match split with
    | none => none
    | some (countText, plural, who) =>
      match nounCount? countText plural, parsePumpWho who with
      | some n, some sel =>
        if sel != .source .this then none
        else some (.putCounter (.source .this) .plusOnePlusOne n)
      | _, _ => none

/-- Exile the top card of your library; you may play that card until the end
of your next turn. The exile is action `n`. -/
def exileTopPlayUntilEndOfNextTurn (n : Nat) : CardAction :=
  .sequence [
    .actionId n (.exile (.topOfLibrary (.controller .this))),
    .continuous
      [.canPlay (.controller .this) (.wasCreatedByAction n)]
      (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])]

/-- `Exile the top card of your library. You may play it until the end of your next turn.` -/
def parseExileTopMayPlay (ss : List String) (n : Nat) : Option (CardAction × Nat) :=
  match ss with
  | [exile, play] =>
    if !sentenceIs exile "exile the top card of your library" then none
    else if !sentenceIs play "you may play it until the end of your next turn" then none
    else some (exileTopPlayUntilEndOfNextTurn n, n + 1)
  | _ => none

/-- A printed limit on when an activated ability may be activated (CR 602.5). -/
inductive ActivateLimit where
  | unlimited
  | onceEachTurn
  | duringYourTurn
  | duringYourTurnOnce
  /-- `Activate only as a sorcery` (CR 602.5a). -/
  | asSorcery

def parseActivateLimit (s : String) : ActivateLimit :=
  match normSentence s with
  | "activate only once each turn" => .onceEachTurn
  | "activate only during your turn" => .duringYourTurn
  | "activate only during your turn and only once each turn" => .duringYourTurnOnce
  | "activate only as a sorcery" => .asSorcery
  | _ => .unlimited

/-- Drop a trailing activation limit. A sentence that is not a limit stays
part of the effect. -/
def splitActivateLimit : List String → List String × ActivateLimit
  | [] => ([], .unlimited)
  | [s] =>
    match parseActivateLimit s with
    | .unlimited => ([s], .unlimited)
    | lim => ([], lim)
  | s :: rest =>
    let (body, lim) := splitActivateLimit rest
    (s :: body, lim)

/-- `Sacrifice another creature or artifact`: one other permanent of those
types. `another` excludes this object. -/
def parseSacrificeAnother (s : String) : Option Cost :=
  match after? (norm s) "sacrifice another " with
  | some obj =>
    (typesInPhrase obj).map fun ts =>
      .sacrificeCount
        (.intersection [.not .this, .permanent, selectorOfTypes ts])
        1
  | none => none

/-- `Sacrifice an artifact or creature` as sacrificing one matching permanent. -/
def parseSacrificeAn (s : String) : Option Cost :=
  match (after? (norm s) "sacrifice ").bind dropArticle? with
  | some obj =>
    (typesInPhrase obj).map fun ts => .sacrificeCount (permanentWith ts) 1
  | none => none

/-- `this` or `this <type>`, such as `this creature` or `this spell`. -/
def isGenericSelf (subject : String) : Bool :=
  let s := norm subject
  if s == "this" then true
  else
    match after? s "this " with
    | none => false
    | some rest =>
      if (rest.splitOn " ").length != 1 then false
      else
        (typeOfOracle? rest).isSome || (subtypeOfOracle? rest).isSome ||
          rest == "permanent" || rest == "spell"

/-- The printed name, the short name before a comma (CR 201.5), and that
name's first word when it is not an article. `Bilbo Baggins, Burglar` refers
to itself as `Bilbo Baggins` or `Bilbo`. `Gollum the Abandoned` refers to
itself as `Gollum`. -/
def selfNames (cardName : String) : List String :=
  let name := norm cardName
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
  isGenericSelf subject || (selfNames cardName).contains (norm subject)

/-- `Sacrifice this land`: sacrifice this object. -/
def parseSacrificeThis (cardName s : String) : Option Cost :=
  (after? (norm s) "sacrifice ").bind fun obj =>
    if refersToSelf cardName obj then some (.sacrifice .this) else none

/-- One printed cost: mana symbols, the tap symbol, or sacrificing a permanent. -/
def parsePrintedCost (cardName s : String) : Option Cost :=
  if norm s == "{t}" then some .tapSymbol
  else
    match nonemptyMana? s with
    | some syms => some (.mana syms)
    | none =>
      parseSacrificeThis cardName s <|> parseSacrificeAn s <|> parseSacrificeAnother s

/-- Costs separated by commas, such as `{2}{G}{U}, {T}, Sacrifice this land`.
One unrecognized cost fails the list. -/
def parsePrintedCosts (cardName s : String) : Option (List Cost) :=
  let parts := s.splitOn ", " |>.map (·.trimAscii.copy) |>.filter (· != "")
  if parts.isEmpty then none else parts.mapM (parsePrintedCost cardName)

/-- Wrap `action` as an activated ability.
`once each turn` is tracked by ability number `n` (CR 602.5).
`nAfter` is the next number after effects inside `action`.
`Activate only as a sorcery` is `activatedIf` of sorcery timing (CR 602.5a). -/
def activatedWithCost (n : Nat) (costs : List Cost) (action : CardAction)
    (limit : ActivateLimit) (nAfter : Nat) : CardPart × Nat :=
  match limit with
  | .asSorcery =>
    (.ability (.activatedIf (.timeToCastSorcery (.controller .this)) costs action), nAfter)
  | .unlimited | .onceEachTurn | .duringYourTurn | .duringYourTurnOnce =>
    let once :=
      match limit with
      | .onceEachTurn | .duringYourTurnOnce => true
      | .duringYourTurn | .unlimited | .asSorcery => false
    let onYourTurn :=
      match limit with
      | .duringYourTurn | .duringYourTurnOnce => true
      | .onceEachTurn | .unlimited | .asSorcery => false
    let notYet := Condition.didNotHappen (.abilityWithIdActivated n) .turnStart
    let yourTurn := Condition.turn (.controller .this)
    let cond? : Option Condition :=
      match onYourTurn, once with
      | false, false => none
      | true, false => some yourTurn
      | false, true => some notYet
      | true, true => some (.and yourTurn notYet)
    let ability : Ability :=
      match cond? with
      | none => .activated costs action
      | some cond => .activatedIf cond costs action
    let ability := if once then Ability.abilityId n ability else ability
    let next := if once then max nAfter (n + 1) else nAfter
    (.ability ability, next)

/-- Mana cost, a life payment, sacrificing another permanent, or a
comma-separated list of printed costs (`{2}{G}{U}, {T}, Sacrifice this land`).
An empty brace list fails rather than falling through. Sacrificing a permanent
that is not `another` or `this`, and is not one item of a comma-separated
list, is not an activation cost here. -/
def parseActivationCost (cardName costText : String) : Option (List Cost) :=
  (nonemptyMana? costText).map (fun syms => [.mana syms]) <|>
    (parsePayLife costText).map (fun life => [.life life]) <|>
    (parseSacrificeAnother costText).map (fun c => [c]) <|>
    if (costText.splitOn ", ").length < 2 then none
    else parsePrintedCosts cardName costText

/-- The creature named by a stack cost reduction: `a tapped creature` or
`an attacking nontoken creature`. -/
def costReductionTarget? (s : String) : Option Selector :=
  match norm s with
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
    match split2? rest mark with
    | some (costText, cond) =>
      (nonemptyMana? costText).map fun syms => (syms, cond)
    | none => none

/-- A stack static that reduces this spell's cost when `cond` holds (CR 604.2). -/
def reduceOnStack (cond : Condition) (syms : List ManaSymbol) : CardPart :=
  .ability (.stackStatic (.if cond [.reduceCost .this [.mana syms]]))

/-- `This spell costs {3} less to cast if it targets a tapped creature.`
Also `… an attacking nontoken creature.`
Also `… if a creature died this turn.`
The reduction is a static ability that functions on the stack (CR 604.2). -/
def parseCostReduction (line : String) : Option CardPart :=
  (costsLessBy? (normLine line) " less to cast if ").bind fun (syms, cond) =>
    let cond? : Option Condition :=
      match after? cond "it targets " with
      | some targetText =>
        (costReductionTarget? targetText).map fun among =>
          .targetsIncludeAny .this among
      | none =>
        if cond == "a creature died this turn" then
          some (.happened (.die (.cardType .creature)) .turnStart)
        else none
    cond?.map (reduceOnStack · syms)

/-- Life named by `<lead> N life`, such as `you gain 2 life`. -/
def lifeAmount? (s lead : String) : Option Nat :=
  (between? s lead " life").bind positiveCount

/-- `one`, `two`, or `one or two`. A range is ordered from low to high.
Zero is not a count. -/
def parseCountRange (s : String) : Option Range :=
  match split2? s " or " with
  | some (a, b) =>
    match positiveCount a, positiveCount b with
    | some lo, some hi =>
      if lo <= hi then some (.range (Value.nat lo) (Value.nat hi)) else none
    | _, _ => none
  | none =>
    (positiveCount s).map fun n => .range (Value.nat n) (Value.nat n)

/-- `one, two, or three` as an inclusive contiguous range.
The numbers are positive and listed from low to high with no gaps. -/
def parseContiguousCounts (s : String) : Option (Nat × Nat) :=
  let s := norm s
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
  match (after? (normSentence sentence) "tap ").bind (split2? · " target ") with
  | some (countText, obj) =>
    match parseCountRange countText, typesInPhrase obj with
    | some r, some ts =>
      some (.tap (.targets n r (permanentWith ts)), n + 1)
    | _, _ => none
  | none => none

/-- `Untap target <permanents> [you control].` The target number is `n`. -/
def parseUntap (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match (after? (normSentence sentence) "untap ").bind parseTargetPhrase with
  | some sel => some (.untap (.target n sel), n + 1)
  | none => none

/-- `It gets +P/+T until end of turn.` refers to the last target (`n - 1`). -/
def parseItGetsUntilEndOfTurn (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if n <= 1 then none
  else
    (whoPtUntilEnd? sentence splitGetsOnly?).bind fun (who, p, t) =>
      if who != "it" then none
      else
        (pumpUntilEnd (.targetReference (n - 1)) p t none).map fun action =>
          (action, n)

/-- `If it's a Dwarf, you may attach an Equipment you control to it.`
The previous target (`n - 1`) is the host. -/
def parseIfItsSubtypeMayAttach (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if n <= 1 then none
  else
    (between? (normSentence sentence) "if it's " " you control to it").bind
        (split2? · ", you may attach ") |>.bind fun (hostArt, attachArt) =>
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
                        youControl]))
                    host)
              ],
            n)
        | _, _ => none
      | _, _ => none

/-- Lands this object's controller controls. -/
def landsYouControl : Selector :=
  permanentWith [.land] [youControl]

/-- `This creature's power and toughness are each equal to the number of lands you control.`
A characteristic-defining ability (CR 208.2a / 604.3). Power and toughness are
each a static ability set to the number of lands you control. -/
def powerToughnessEqualLandsAbilities : List Ability := [
  .static (.setPower .this (.count landsYouControl)),
  .static (.setToughness .this (.count landsYouControl))
]

/-- The printed clause after `<this>'s`. -/
def landsCharacteristicSuffix : String :=
  "power and toughness are each equal to the number of lands you control"

def parsePowerToughnessEqualLands (text : String) : Option (List Ability) :=
  if sentenceIs text ("this creature's " ++ landsCharacteristicSuffix) then
    some powerToughnessEqualLandsAbilities
  else none

/-- `a Bear creature in addition to its other types` as that creature subtype. -/
def parseAddedCreatureSubtype (s : String) : Option CardSubtype :=
  (before? (norm s) " creature in addition to its other types").bind dropArticle?
    |>.bind subtypeOfOracle?

/-- `<this> becomes a Bear creature in addition to its other types and gains "…"`.
The subject is this card. No duration is printed, so the effect lasts until
the end of the game (CR 611.2a). The quotation is a static ability this
object gains. -/
def parseBecomeAndGainStatic (cardName : String) (sentence : String) : Option CardAction :=
  (split2? (normSentence sentence) " becomes ").bind fun (subject, rest) =>
    if !refersToSelf cardName subject then none
    else
      (split2? rest " and gains \"").bind fun (become, quoted) =>
        (before? quoted "\"").bind fun abilityText =>
          match parseAddedCreatureSubtype become, parsePowerToughnessEqualLands abilityText with
          | some st, some [power, toughness] =>
            some (.continuous
              [.gainType .this .creature,
                .gainSubtype .this st,
                .gainAbility .this power,
                .gainAbility .this toughness]
              .endOfGame)
          | _, _ => none

/-- `Target creature can't be blocked this turn.` The target is `n`.
The restriction lasts until end of turn. -/
def parseTargetCantBeBlocked (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (before? (normSentence sentence) " can't be blocked this turn").bind fun who =>
    (parseBattlefieldTarget who).map fun sel =>
      (.continuous [.forbid (.block .any (.target n sel))] .endOfTurn, n + 1)

/-- `Put two +1/+1 counters on target Elf you control.`
One counter uses the singular noun. A creature type is a creature of those
subtypes. The target is `n`. -/
def parsePutCountersOnTarget (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match after? (normSentence sentence) "put " with
  | none => none
  | some rest =>
    let split :=
      (split2? rest " +1/+1 counters on ").map (fun (c, w) => (c, true, w)) <|>
        (split2? rest " +1/+1 counter on ").map (fun (c, w) => (c, false, w))
    match split with
    | some (countText, plural, who) =>
      match nounCount? countText plural, parseBattlefieldTarget who with
      | some k, some sel =>
        -- A creature type (`Elf`, `Goblin or Orc`), not a card type (`creature`).
        if sel.includedSubtypes.isEmpty then none
        else some (.putCounter (.target n sel) .plusOnePlusOne k, n + 1)
      | _, _ => none
    | none => none

/-- `Search your library for a basic land card, put it onto the battlefield tapped, then shuffle.`
Does not choose a target, so the target number stays `n`. -/
def parseSearchBasicLandTapped (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if sentenceIs sentence
      "search your library for a basic land card, put it onto the battlefield tapped, then shuffle" then
    some (
      .searchLibraryThenShuffle
        (.controller .this)
        [
          .putOntoBattlefieldInState
            (.selected
              (.controller .this)
              (.range 1 1)
              (.intersection [.inLibrary, .cardType .land, .supertype .basic]))
            [.tapped]],
      n)
  else none

/-- `Add one mana of any color.` The player chooses one of the five colors
(CR 106.4). Does not choose a target, so the target number stays `n`. -/
def parseAddOneManaOfAnyColor (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if sentenceIs sentence "add one mana of any color" then
    some (.addManaOfOneColor (.controller .this) ManaSymbol.anyColor 1, n)
  else none

/-- `Destroy target permanent.` The target number is `n`. -/
def parseDestroyTargetPermanent (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if sentenceIs sentence "destroy target permanent" then
    some (.destroy (.target n .permanent), n + 1)
  else none

/-- A pump, counters, a targeted restriction, a library search, becoming a
creature that gains a static ability, adding one mana of any color, destroying
a permanent, or exiling the top card to play later, optionally followed by an
activation limit. -/
def parseActivatedEffect (cardName : String) (effect : String) (n : Nat) :
    Option (CardAction × ActivateLimit × Nat) :=
  let (body, limit) := splitActivateLimit (sentences effect)
  match body with
  | [one] =>
    let targeted :=
      parseTargetCantBeBlocked one n <|>
        parsePutCountersOnTarget one n <|>
        parseSearchBasicLandTapped one n <|>
        parseDestroyTargetPermanent one n
    let plain :=
      (parsePumpUntilEndOfTurn one <|> parsePutCountersOnThis one <|>
          parseBecomeAndGainStatic cardName one).map (fun action => (action, n)) <|>
        parseAddOneManaOfAnyColor one n
    (targeted <|> plain).map fun (action, n') => (action, limit, n')
  | _ =>
    (parseExileTopMayPlay body n).map fun (action, n') => (action, limit, n')

/-- `{3}{W}: Creatures you control get +1/+1 until end of turn.`
Also `Pay 2 life: This creature gets +2/+2 until end of turn. Activate only once each turn.`
And `Sacrifice another creature or artifact: Exile the top card of your library. You may play it until the end of your next turn. Activate only during your turn and only once each turn.`
And `{5}{G}{G}: This enchantment becomes a Bear creature in addition to its other types and gains "…"`.
And `{1}, {T}: Add one mana of any color.`
And `{7}, {T}, Sacrifice this artifact: Destroy target permanent.` -/
def parseActivatedAbility (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (split2? (stripTrailingPeriod (stripReminderParenthetical line)) ": ").bind
    fun (costText, effect) =>
      match parseActivatedEffect cardName effect n, parseActivationCost cardName costText with
      | some (action, limit, n'), some costs =>
        some (activatedWithCost n costs action limit n')
      | _, _ => none

/-- Effect of `<word> <this card> <mid> <effect>`.
`word` is `when` or `whenever`. `mid` is the clause boundary, such as
` enters, `. -/
def triggerSelfEffect? (cardName word s mid : String) : Option String :=
  (after? s (word ++ " ")).bind (split2? · mid) |>.bind fun (subject, effect) =>
    if refersToSelf cardName subject then some effect else none

/-- Effect of `when <this card> <mid> <effect>`.
`mid` is the clause boundary, such as ` enters, ` or ` dies, `. -/
def whenSelfEffect? (cardName s mid : String) : Option String :=
  triggerSelfEffect? cardName "when" s mid

/-- `when <this card> <mid> <effect>` as a triggered ability.
`mid` is the clause boundary, such as ` enters, `. -/
def onSelfTrigger (cardName line mid : String) (event : Trigger)
    (effect? : String → Option CardAction) : Option CardPart :=
  onTrigger event ((whenSelfEffect? cardName (normLine line) mid).bind effect?)

/-- Same as `onSelfTrigger`, keeping the target number the effect parser returns. -/
def onSelfTriggerN (cardName line mid : String) (event : Trigger)
    (effect? : String → Option (CardAction × Nat)) : Option (CardPart × Nat) :=
  ((whenSelfEffect? cardName (normLine line) mid).bind effect?).map
    fun (action, n') => (.ability (.triggered event action), n')

/-- `<this card> deals 5 damage to target creature.` The source must be this
card. The target number is `n`. -/
def parseDealDamage (cardName : String) (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " deals ").bind fun (who, rest) =>
    if !refersToSelf cardName who then none
    else
      (split2? rest " damage to target ").bind fun (amt, obj) =>
        match positiveDigits? amt, typesInPhrase obj with
        | some amount, some ts =>
          some (.dealDamage .this (.target n (permanentWith ts)) (.nat amount), n + 1)
        | _, _ => none

/-- `Target … gains … until end of turn.` The target number is `n`. -/
def parseGainsUntilEndOfTurn (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match (before? (normSentence sentence) "until end of turn").bind (split2? · " gains ") with
  | some (who, gained) =>
    match parseTargetPhrase who, parseKeywordPhrase gained with
    | some sel, some kws =>
      some (.continuous (gainEffects n sel kws) .endOfTurn, n + 1)
    | _, _ => none
  | none => none

/-- `Target creature gets +2/+2 until end of turn.`
Also `Target creature gets +2/+2 and gains lifelink until end of turn.`
The target number is `n`. A gained keyword refers to that same target. -/
def parseTargetGetsUntilEndOfTurn (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (before? (normSentence sentence) " until end of turn").bind splitGetsOnly? |>.bind
    fun (who, rest) =>
      match parseTargetPhrase who, ptAndGains? rest with
      | some sel, some (p, t, kws) => pumpGainsUntilEnd n sel p t kws
      | _, _ => none

/-- `Creatures target player controls get -1 / -1 until end of turn.`
The player is target `n`. `P/T` may be negative. -/
def parseTargetPlayerControlsGet (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (whoPtUntilEnd? sentence splitGets?).bind fun (who, p, t) =>
    ((before? who " target player controls").bind typesInPhrase).bind fun ts =>
      (pumpUntilEnd (permanentWith ts [.controlled (.target n .player)]) p t none).map
        fun action => (action, n + 1)

/-- `a card`, `one card`, or `two cards` as how many cards are drawn.
One card is singular. More than one is plural. -/
def parseCardCount (s : String) : Option Nat :=
  let s := norm s
  match before? s " cards" with
  | some countText => nounCount? countText true
  | none =>
    match before? s " card" with
    | some countText => nounCount? countText false
    | none => none

/-- `Target player draws two cards and loses 2 life.`
The player is target `n`. -/
def parseTargetPlayerDrawsLosesLife (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  match (between? (normSentence sentence) "target player draws " " life").bind
      (split2? · " and loses ") with
  | some (drawText, lifeText) =>
    match parseCardCount drawText, positiveCount lifeText with
    | some cards, some life =>
      some (
        .sequence [
          .draw (.target n .player) (Value.nat cards),
          .loseLife (.targetReference n) (Value.nat life)],
        n + 1)
    | _, _ => none
  | none => none

/-- `When Bilbo Baggins enters, draw a card.` The subject is this card. -/
def parseEnterDraw (cardName : String) (line : String) : Option CardPart :=
  onSelfTrigger cardName line " enters, " (.enter .this) fun effect =>
    (after? effect "draw ").bind parseCardCount |>.map fun k =>
      .draw (.controller .this) (Value.nat k)

/-- `target creature an opponent controls` as the objects a target matches. -/
def parseOppControlledTarget (s : String) : Option Selector :=
  match (between? (norm s) "target " " an opponent controls").bind typesInPhrase with
  | some ts =>
    some (permanentWith ts [.controlled (.opponent (.controller .this))])
  | none => none

/-- `target <permanents> an opponent controls gets P/T until end of turn.`
The target number is `n`. `P/T` may be negative, as in -1 / -1. -/
def parseOppGetsUntilEndOfTurn (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (whoPtUntilEnd? sentence splitGets?).bind fun (who, p, t) =>
    (parseOppControlledTarget who).bind fun sel =>
      (pumpUntilEnd (.target n sel) p t none).map fun action => (action, n + 1)

/-- `When this creature dies, target creature an opponent controls gets -1 / -1 until end of turn.`
The dying object is this card. The target number is `n`. -/
def parseDiesOppGets (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onSelfTriggerN cardName line " dies, " (.die .this) (parseOppGetsUntilEndOfTurn · n)

/-- `put a +1/+1 counter on this creature`. `this`, `this creature`, and `it`
are the source of this ability. -/
def parsePutPlusOneOnThis (sentence : String) : Option CardAction :=
  (after? (normSentence sentence) "put a +1/+1 counter on ").bind fun who =>
    if parsePumpWho who == some (.source .this) then
      some (.putCounter (.source .this) .plusOnePlusOne 1)
    else none

/-- `Whenever you draw your second card each turn, put a +1/+1 counter on this creature.` -/
def parseDrawSecondPlusOne (line : String) : Option CardPart :=
  onTrigger (.ordinal 2 .turnStart (.draw (.controller .this) .all))
    ((after? (normLine line) "whenever you draw your second card each turn, ").bind
      parsePutPlusOneOnThis)

/-- `Whenever you draw a card, put a +1/+1 counter on this creature.` -/
def parseYouDrawPlusOne (line : String) : Option CardPart :=
  onTrigger (.draw (.controller .this) .all)
    ((after? (normLine line) "whenever you draw a card, ").bind parsePutPlusOneOnThis)

/-- `Counter target spell unless its controller pays {4}.`
The target number is `n`. -/
def parseCounterUnlessPays (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match (after? (normSentence sentence) "counter target ").bind
      (split2? · " unless its controller pays ") with
  | some (obj, costText) =>
    if obj != "spell" then none
    else
      match nonemptyMana? costText with
      | some syms =>
        some (
          .preventable
            (.controller (.targetReference n))
            [.mana syms]
            (.counter (.target n .spell)),
          n + 1)
      | none => none
  | none => none

/-- `Draw two cards, then discard a card.` Does not choose a target. -/
def parseDrawThenDiscard (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match split2? (normSentence sentence) ", then discard " with
  | some (drawPart, discardPart) =>
    match (after? drawPart "draw ").bind parseCardCount, parseCardCount discardPart with
    | some d, some c =>
      some (
        .sequence [
          .draw (.controller .this) (Value.nat d),
          .discard (.controller .this) (Value.nat c)],
        n)
    | _, _ => none
  | none => none

/-- `Target creature gets -5 / -5 until end of turn. If that creature would die this turn, exile it instead.`
The pump and the replacement both last until end of turn. Dying is being put
into a graveyard from the battlefield; the replacement exiles that object
instead (CR 614.1). The creature is target `n`. -/
def parsePumpExileIfDies (text : String) (n : Nat) : Option (CardAction × Nat) :=
  match sentences text with
  | [pump, exile] =>
    if !sentenceIs exile "if that creature would die this turn, exile it instead" then none
    else
      match parseTargetGetsUntilEndOfTurn pump n with
      | some (.continuous effects .endOfTurn, n') =>
        match ContinuousEffect.addedPT? effects, ContinuousEffect.targetingSelector? effects with
        | some _, some (.target m (.intersection [.permanent, .cardType .creature])) =>
          some (
            .continuous
              (effects ++
                [.replace
                  (.putToGraveyard (.targetReference m))
                  [.exile (.replacingObject)]])
              .endOfTurn,
            n')
        | _, _ => none
      | _ => none
  | _ => none

/-- `Target creature you control deals damage equal to its power to target creature an opponent controls.`
The source is target `n`; the recipient is target `n + 1`. -/
def parseDealsDamageEqualToPower (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  match split2? (normSentence sentence) " deals damage equal to its power to " with
  | some (src, dest) =>
    if (before? src " you control").isNone then none
    else
      match parseTargetPhrase src, parseOppControlledTarget dest with
      | some srcSel, some destSel =>
        some (
          .dealDamageEqualToPower
            (.target n srcSel)
            (.target (n + 1) destSel),
          n + 2)
      | _, _ => none
  | none => none

/-- `Put a +1/+1 counter on target creature you control.`
The target is numbered `n`. -/
def parsePutPlusOneOnTarget (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  match after? (normSentence sentence) "put a +1/+1 counter on " with
  | some who =>
    (parseTargetPhrase who).map fun sel =>
      (.putCounter (.target n sel) .plusOnePlusOne 1, n + 1)
  | none => none

/-- `It gains trample and hexproof until end of turn.`
The keywords are gained by the target already numbered `targetId`. -/
def parseItGainsKeywords (sentence : String) (targetId : Nat) : Option CardAction :=
  (between? (normSentence sentence) "it gains " " until end of turn").bind
    fun gained =>
      (parseKeywordPhrase gained).map fun kws =>
        .continuous (keywordGains (.targetReference targetId) kws) .endOfTurn

/-- `Put a +1/+1 counter on target creature you control. It gains trample and hexproof until end of turn.`
The counter and the keywords share target `n`. -/
def parsePutPlusOneThenGains (text : String) (n : Nat) : Option (CardAction × Nat) :=
  match sentences text with
  | [put, gains] =>
    match parsePutPlusOneOnTarget put n, parseItGainsKeywords gains n with
    | some (putAction, n'), some gain =>
      some (.sequence [putAction, gain], n')
    | _, _ => none
  | _ => none

/-- `Destroy target creature`, `Destroy target creature with flying`, or
`Destroy target creature with power 4 or greater.`
The target number is `n`. `with` names one keyword the permanent must have,
or `power N or greater`. `N` is a positive printed number. -/
def parseDestroy (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "destroy target ").bind fun rest =>
    let destroyed (ts : List CardType) (tail : List Selector) : CardAction × Nat :=
      (.destroy (.target n (permanentWith ts tail)), n + 1)
    let withPower :=
      (split2? rest " with power ").bind fun (obj, powerText) =>
        (before? powerText " or greater").bind positiveCount |>.bind fun p =>
          (typesInPhrase obj).map fun ts =>
            destroyed ts [.powerAtLeast (Value.int (p : Int))]
    let withKeyword :=
      (split2? rest " with ").bind fun (obj, kwText) =>
        (keywordOfOracle? kwText).bind fun k =>
          (typesInPhrase obj).map fun ts => destroyed ts [.keyword k]
    let plain :=
      (typesInPhrase rest).map fun ts => destroyed ts []
    withPower <|> withKeyword <|> plain

/-- `Destroy target artifact or enchantment. You gain 2 life.`
The destroy chooses target `n`. Gaining life does not. `N` is a positive count. -/
def parseDestroyThenGainLife (text : String) (n : Nat) : Option (CardAction × Nat) :=
  match sentences text with
  | [destroy, gain] =>
    match parseDestroy destroy n, lifeAmount? (normSentence gain) "you gain " with
    | some (destroyed, n'), some k =>
      some (.sequence [destroyed, .gainLife (.controller .this) (Value.nat k)], n')
    | _, _ => none
  | _ => none

/-- `Until end of turn, target creature becomes an artifact in addition to its
other types and gains indestructible.`
The target is `n`. The type and indestructible both last until end of turn.
A reminder parenthetical is not rules text (CR 207.2). -/
def parseBecomeArtifactIndestructible (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (after? (normLine sentence) "until end of turn, ").bind fun rest =>
    (split2? rest " becomes ").bind fun (who, become) =>
      (split2? become " and gains ").bind fun (typeText, gained) =>
        if typeText != "an artifact in addition to its other types" then none
        else
          match parseTargetPhrase who, parseKeywordPhrase gained with
          | some sel, some [.indestructible] =>
            if sel != permanentWith [.creature] then none
            else
              some (
                .continuous
                  [.gainType (.target n sel) .artifact,
                    .gainAbility (.targetReference n) (.keyword .indestructible)]
                .endOfTurn,
                n + 1)
          | _, _ => none

/-- One printed mode of a “Choose one” spell. The first success wins. -/
def parseModeAction (text : String) (n : Nat) : Option (CardAction × Nat) :=
  parseCounterUnlessPays text n <|>
    parseDrawThenDiscard text n <|>
    parsePumpExileIfDies text n <|>
    parseTargetPlayerDrawsLosesLife text n <|>
    parseTargetGetsUntilEndOfTurn text n <|>
    parseTargetPlayerControlsGet text n <|>
    parseDestroyThenGainLife text n <|>
    parseBecomeArtifactIndestructible text n <|>
    parseDestroy text n <|>
    parsePutPlusOneThenGains text n <|>
    (parsePumpUntilEndOfTurn text).map (·, n)

/-- The text of a `•` mode line, without the bullet. -/
def stripModeBullet (line : String) : Option String :=
  after? (copied line) "•"

/-- `Choose one —` (CR 700.2). -/
def isChooseOneHeader (line : String) : Bool :=
  normLine line == "choose one —"

/-- Parts for a “Choose one” spell with at least one parsed mode.
No modes makes the parse fail rather than dropping the printed choice. -/
def chooseOneParts (modes : List CardAction) : Option (List CardPart) :=
  match modes with
  | [] => none
  | modes => some [.actions [.chooseMode modes]]

/-- `<subject> <tail>` as a static restriction, when `subject` is this card. -/
def staticCant (cardName line tail : String) (restriction : Trigger) : Option CardPart :=
  (before? (normLine line) tail).bind fun subject =>
    if subject.isEmpty || !refersToSelf cardName subject then none
    else some (.ability (.static (.forbid restriction)))

/-- `<this card> can't be blocked by tokens.` The subject must be this card. -/
def parseCantBeBlockedByTokens (cardName : String) (line : String) : Option CardPart :=
  staticCant cardName line " can't be blocked by tokens" (.block .token .this)

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
  onTrigger (.combatDamage .this .player)
    ((triggerSelfEffect? cardName "whenever" (normLine line)
        " deals combat damage to a player, ").bind fun effect =>
      (parseDrawThenDiscard effect 1).map fun (action, _) => action)

/-- `Exchange control of two target nonland permanents that share a card type.`
The target number is `n`. The noun stays plural, as in the printed template
for a set of permanents. -/
def parseExchangeControlSharingCardType (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  match (between? (normSentence sentence)
      "exchange control of " " that share a card type").bind
      (split2? · " target ") with
  | some (countText, obj) =>
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
  | none => none

/-- `Target creature's owner puts it on their choice of the top or bottom of their library.`
The target number is `n`. That creature's owner chooses which library position. -/
def parseOwnerPutsTopOrBottom (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match (between? (normSentence sentence) "target "
      "'s owner puts it on their choice of the top or bottom of their library").bind
      typesInPhrase with
  | some ts =>
    let sel := permanentWith ts
    some (
      .playerSelectAction
        (.owner (.targetReference n))
        (.range 1 1)
        [.putOnTopOfLibrary (.target n sel),
          .putOnBottomOfLibrary (.targetReference n)],
      n + 1)
  | none => none

/-- `Put a +1/+1 counter on up to one target creature.`
Up to one target is zero or one (CR 115.1). The targets are numbered `n`. -/
def parsePutPlusOneUpToOne (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match (after? (normSentence sentence) "put a +1/+1 counter on up to one target ").bind
      typesInPhrase with
  | some ts =>
    some (
      .putCounter
        (.targets n (.range 0 1) (permanentWith ts))
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
  (after? (normLine line) "whenever one or more ").bind (split2? · " die, ") |>.bind
    fun (who, effect) =>
      if who != "other creatures" then none
      else
        match parseControlledPhrase who, parseScry effect n with
        | some among, some (action, n') =>
          some (.ability (.triggered (.dieSimultaneously among []) action), n')
        | _, _ => none

/-- `Counter target spell. If a permanent spell is countered this way, exile
it instead of putting it into its owner's graveyard. You may cast that card
without paying its mana cost for as long as it remains exiled.`
The counter and its target are numbered `n`. The exile that replaces the
graveyard is `n + 1`, and the free cast refers to that exiled card. -/
def parseCounterExilePermanentMayCast (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match sentences text with
  | [counter, exile, cast] =>
    if !sentenceIs counter "counter target spell" then none
    else if !sentenceIs exile
        "if a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard" then
      none
    else if !sentenceIs cast
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

/-- `If that spell's mana value was 2 or less, recruit.`
`N` is a positive printed number. Recruit is the effect of that check. -/
def recruitIfSpellMvAtMost? (sentence : String) : Option Nat :=
  (between? (normSentence sentence)
      "if that spell's mana value was " " or less, recruit").bind positiveCount

/-- `Counter target spell. If that spell's mana value was N or less, recruit.`
The spell is target `n`. Before it is countered, value variable `n` records
the greatest mana value of that target, which on the stack includes the
chosen `{X}` (CR 202.3e). Recruit happens only when that variable is less
than or equal to `N`. -/
def parseCounterThenRecruitIfMv (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match sentences text with
  | [counter, cond] =>
    if !sentenceIs counter "counter target spell" then none
    else
      (recruitIfSpellMvAtMost? cond).map fun k =>
        ([
          .defineValueVariable n (.greatestManaValue (.target n .spell)),
          .counter (.targetReference n),
          .if (.lessOrEqual (.variable n) (.nat k))
            [.keyword (.controller .this) .recruit]
        ], n + 1)
  | _ => none

/-- `You may play an additional land this turn.` One extra land play, until end of turn
(CR 305.2b). -/
def parseAdditionalLand (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if sentenceIs sentence "you may play an additional land this turn" then
    some (
      .continuous
        [.increaseLandPlayLimit (.controller .this) (Value.nat 1)]
        .endOfTurn,
      n)
  else none

/-- `You draw a card and lose 1 life.` One card and 1 life. -/
def parseYouDrawCardLoseLife (sentence : String) : Option CardAction :=
  match (after? (normSentence sentence) "you draw ").bind (split2? · " and lose ") with
  | some (drawText, lifeText) =>
    match parseCardCount drawText, lifeAmount? ("lose " ++ lifeText) "lose " with
    | some 1, some 1 =>
      some (.sequence [
        .draw (.controller .this) 1,
        .loseLife (.controller .this) 1])
    | _, _ => none
  | none => none

/-- The subtype printed in `amass Goblins`: the plural drops a trailing `s`. -/
def amassSubtype? (s : String) : Option CardSubtype :=
  if s.endsWith "s" && s.length > 1 then subtypeOfOracle? (s.dropEnd 1).copy else none

/-- `Amass Goblins 1.` The controller amasses that subtype that many (CR 701.45).
The subtype is plural. `N` is a positive count. -/
def parseAmass (sentence : String) : Option CardAction :=
  (after? (normSentence sentence) "amass ").bind fun rest =>
    (split2? rest " ").bind fun (typeText, nText) =>
      match amassSubtype? typeText, positiveCount nText with
      | some st, some n =>
        some (.keyword (.controller .this) (.amass st (.nat n)))
      | _, _ => none

/-- `Return up to one target creature card from your graveyard to your hand.`
Up to one target is zero or one (CR 115.1). That card is in your graveyard.
The target is numbered `n`. -/
def parseReturnUpToOneFromYourGraveyard (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (between? (normSentence sentence)
      "return up to one target " " from your graveyard to your hand").bind
    fun obj =>
      (before? obj " card").bind typeOfOracle? |>.map fun t =>
        (.returnToHand
          (.targets n (.range 0 1)
            (.intersection [
              .inGraveyard,
              .cardType t,
              .owner (.controller .this)])),
         n + 1)

/-- A parsed action that does not choose a new target. -/
def unchanged (parsed : Option CardAction) (n : Nat) : Option (CardAction × Nat) :=
  parsed.map (·, n)

/-- One sentence. The first parser that accepts it wins. -/
def parseSentence (cardName sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  parseGainsUntilEndOfTurn sentence n <|>
    parseTap sentence n <|>
    parseUntap sentence n <|>
    parseItGetsUntilEndOfTurn sentence n <|>
    parseIfItsSubtypeMayAttach sentence n <|>
    parseDealDamage cardName sentence n <|>
    parseDealsDamageEqualToPower sentence n <|>
    parseDestroy sentence n <|>
    parsePutPlusOneUpToOne sentence n <|>
    parseTargetPlayerGainsLife sentence n <|>
    parseYouGainLife sentence n <|>
    unchanged (parseYouDrawCardLoseLife sentence) n <|>
    unchanged (parseAmass sentence) n <|>
    parseReturnUpToOneFromYourGraveyard sentence n <|>
    parseAdditionalLand sentence n <|>
    parseScry sentence n <|>
    parseOwnerPutsTopOrBottom sentence n <|>
    parseExchangeControlSharingCardType sentence n <|>
    parseTargetGetsUntilEndOfTurn sentence n <|>
    parseTargetPlayerControlsGet sentence n <|>
    parseTargetPlayerDrawsLosesLife sentence n

/-- Every sentence of `text` must parse. An unrecognized sentence fails
the text. No sentences (reminder-only or empty text) succeeds with no actions.
Multi-sentence templates are tried before the sentence split. -/
def actionsFromText (cardName : String) (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  let oneAction (parsed : Option (CardAction × Nat)) : Option (List CardAction × Nat) :=
    parsed.map fun (action, n') => ([action], n')
  parseCounterExilePermanentMayCast text n <|>
    parseCounterThenRecruitIfMv text n <|>
    oneAction (parsePumpExileIfDies text n) <|>
    oneAction (parsePutPlusOneThenGains text n) <|>
    List.foldlM (fun (acc, n) s =>
      (parseSentence cardName s n).map fun (a, n') => (acc ++ [a], n'))
      ([], n) (sentences text)

/-- Split off a Gatherer `//ADV//` Adventure section. A marker that shares
its line with the Adventure name keeps that name. -/
def splitAdventure (lines : List String) : List String × List String :=
  go lines []
where
  go : List String → List String → List String × List String
    | [], acc => (acc.reverse, [])
    | line :: rest, acc =>
      if line == "//ADV//" then (acc.reverse, rest)
      else
        match after? line "//ADV//" with
        | some restLine =>
          let adv := if restLine.isEmpty then rest else restLine :: rest
          (acc.reverse, adv)
        | none => go rest (line :: acc)

/-- `As an additional cost to cast this spell, sacrifice an artifact or creature or pay {4}.`
The sacrifice and the generic mana are alternatives announced at CR 601.2b.
The ability functions while this spell is on the stack (CR 113.6 / 604.2). -/
def parseAdditionalCostSacrificeOrPay (line : String) : Option CardPart :=
  match (after? (normLine line)
      "as an additional cost to cast this spell, sacrifice ").bind
      (split2? · " or pay ") with
  | some (obj, costText) =>
    match (dropArticle? obj).bind typesInPhrase, parseManaSymbols costText with
    | some ts, some [.generic k] =>
      some (.ability (.stackStatic (
        .additionalCost .this
          [.or [
            .sacrificeCount (permanentWith ts) 1,
            .mana [.generic k]]])))
    | _, _ => none
  | none => none

/-- Drop a leading ability word (`Ferocious —`) when that word is present.
Any other dash stays part of the text. -/
def withoutAbilityWord (s word : String) : String :=
  match split2? s "—" with
  | some (w, rest) => if w == word then rest else s
  | none => s

/-- Creatures this object's controller controls. -/
def creaturesYouControl : Selector :=
  permanentWith [.creature] [youControl]

/-- A creature you control with power 4 or greater. -/
def ferociousCreature : Selector :=
  permanentWith [.creature] [youControl, .powerAtLeast (Value.int 4)]

/-- `until end of turn, this creature gets +P/+0 and creatures you control gain trample.`
The bonus and trample both last until end of turn. A zero power, or any
toughness change, is a different ability. -/
def parseSourceGetsAndTeamTrample (effect : String) : Option CardAction :=
  (after? (norm effect) "until end of turn, ").bind fun rest =>
    (split2? rest " and creatures you control gain ").bind fun (pump, gained) =>
      (splitGetsOnly? pump).bind fun (who, ptText) =>
        if parsePumpWho who != some (.source .this) then none
        else
          match parsePowerToughness ptText, parseKeywordPhrase gained with
          | some (p, 0), some [.trample] =>
            if p == 0 then none
            else
              some (.continuous
                [.addPower (.source .this) (Value.int p),
                  .gainAbility creaturesYouControl (.keyword .trample)]
                .endOfTurn)
          | _, _ => none

/-- `Put a +1/+1 counter on each creature you control.`
One counter uses the singular noun. `each` is every creature you control. -/
def parsePutPlusOneOnEachYouControl (sentence : String) : Option CardAction :=
  match (after? (normSentence sentence) "put ").bind
      (split2? · " +1/+1 counter on each ") with
  | some (countText, who) =>
    match nounCount? countText false, parseControlledPhrase who with
    | some 1, some sel =>
      if sel == creaturesYouControl then
        some (.putCounter creaturesYouControl .plusOnePlusOne 1)
      else none
    | _, _ => none
  | none => none

/-- `Ferocious — Whenever this creature attacks while you control a creature
with power 4 or greater, <effect>.`
`Ferocious` is an ability word (CR 207.2c) and may be omitted. The “while”
clause is part of the trigger condition (CR 603.2): it is checked when this
creature attacks, and it is not checked again when the ability resolves.
The effect is gaining life, this creature getting +P/+T until end of turn,
this creature getting +P/+0 and your creatures gaining trample until end of
turn, or a +1/+1 counter on each creature you control. -/
def parseFerociousThisAttacks (line : String) : Option CardPart :=
  let s := withoutAbilityWord (normLine line) "ferocious"
  let lead :=
    "whenever this creature attacks while you control a creature with power 4 or greater, "
  (after? s lead).bind fun effect =>
    let gainLife :=
      match parseYouGainLife effect 0 with
      | some (.gainLife _ k, _) => some (.gainLife (.controller .this) k)
      | _ => none
    let pump :=
      (parsePumpUntilEndOfTurn effect).bind fun action =>
        (sourceGetsUntilEnd? action).map fun _ => action
    (gainLife <|> pump <|>
        parseSourceGetsAndTeamTrample effect <|>
        parsePutPlusOneOnEachYouControl effect).map fun action =>
      .ability (.triggeredWhile (.attack .this .all) (.any ferociousCreature) action)

/-- `Ferocious — Whenever you attack while you control a creature with power
4 or greater, you draw a card and lose 1 life.`
`Ferocious` may be omitted (CR 207.2c). “Whenever you attack” is one trigger
when creatures you control attack at the same time (CR 508.3 / 603.2d). -/
def parseFerociousYouAttack (line : String) : Option CardPart :=
  let s := withoutAbilityWord (normLine line) "ferocious"
  let lead :=
    "whenever you attack while you control a creature with power 4 or greater, "
  (after? s lead).bind parseYouDrawCardLoseLife |>.map fun action =>
    .ability (.triggeredWhile
      (.attackSimultaneously creaturesYouControl .all [])
      (.any ferociousCreature)
      action)

/-- `Ferocious — At the beginning of combat on your turn, if you control a
creature with power 4 or greater, put a +1/+1 counter on this creature.`
`Ferocious` may be omitted (CR 207.2c). Beginning of combat is CR 507.1.
The “if” is an intervening if (CR 603.4). -/
def parseFerociousBeginCombat (line : String) : Option CardPart :=
  let s := withoutAbilityWord (normLine line) "ferocious"
  let lead :=
    "at the beginning of combat on your turn, if you control a creature with power 4 or greater, "
  (after? s lead).bind parsePutPlusOneOnThis |>.map fun action =>
    .ability (.triggered (.combatStart (.controller .this))
      (.if (.any ferociousCreature) [action]))

/-- `Landfall — Whenever a land you control enters, <effect>.`
`Landfall` is an ability word (CR 207.2c) and may be omitted.
The effect is `this creature gets +P/+T until end of turn`, or
`put a +1/+1 counter on target <permanent> you control`.
`you control` is required on that target; a bare target is a different ability.
The target, when there is one, is `n`. -/
def parseLandYouControlEnters (line : String) (n : Nat) : Option (CardPart × Nat) :=
  (after? (withoutAbilityWord (normLine line) "landfall")
      "whenever a land you control enters, ").bind fun effect =>
    let triggered (action : CardAction) (n' : Nat) : Option (CardPart × Nat) :=
      some (.ability (.triggered (.enter landsYouControl) action), n')
    match parsePumpUntilEndOfTurn effect with
    | some action =>
      match sourceGetsUntilEnd? action with
      | some _ => triggered action n
      | none => none
    | none =>
      if !effect.endsWith " you control" then none
      else
        (parsePutPlusOneOnTarget effect n).bind fun (action, n') =>
          triggered action n'

/-- `When this Equipment enters, target opponent sacrifices a creature of their choice.`
The entering object is this card. The opponent is target `n` and chooses which
creature to sacrifice (CR 701.17a). -/
def parseEnterTargetOpponentSacrifices (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (whenSelfEffect? cardName (normLine line) " enters, ").bind fun effect =>
    (between? effect "target opponent sacrifices " " of their choice").bind fun obj =>
      (dropArticle? obj).bind fun named =>
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
                    (permanentWith [.creature] [.controlled (.targetReference n)])))),
            n + 1)

/-- `Equipped creature gets +2/+1.` The bonus is a static ability of the
Equipment (CR 604.1 / 301.5). -/
def parseEquippedGets (line : String) : Option (List CardPart) :=
  match (after? (normLine line) "equipped creature gets ").bind parsePowerToughness with
  | some (p, t) =>
    let parts :=
      (flatPowerToughness (.hostOf .this) p t).map fun e =>
        (.ability (.static e) : CardPart)
    if parts.isEmpty then none else some parts
  | none => none

/-- `Equip {2}.` Reminder text such as
`({2}: Attach to target creature you control. Equip only as a sorcery.)`
is not rules text (CR 207.2 / 702.6). -/
def parseEquip (line : String) : Option CardPart :=
  match (after? (normLine line) "equip ").bind nonemptyMana? with
  | some syms => some (.ability (.keywordWithCost .equip [.mana syms]))
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
    (whenSelfEffect? cardName (norm enter) " enters, ").bind fun effect =>
      if effect != "exile up to one target card from an opponent's graveyard" then none
      else
        (parseEachOpponentLosesLife lose).map fun k =>
          (.ability (
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
  | _ => none

def returnThisFromGraveyardToHand : CardAction :=
  .returnToHand (.intersection [.inGraveyard, .source .this])

def parseReturnThisFromGraveyard (sentence : String) : Option CardAction :=
  if sentenceIs sentence "return this card from your graveyard to your hand" then
    some returnThisFromGraveyardToHand
  else
    none

/-- `{2}, Sacrifice an artifact or creature: Return this card from your graveyard to your hand. Activate only as a sorcery.`
The effect moves this card out of the graveyard, so the ability functions
there (CR 113.6). “Activate only as a sorcery” is the condition
(CR 307.1 / 117.1a). The ability is `graveyardActivatedIf`. -/
def parseGraveyardReturn (line : String) : Option CardPart :=
  (split2? (stripReminderParenthetical line) ": ").bind fun (costText, effect) =>
    match sentences effect with
    | [ret, restrict] =>
      if !sentenceIs restrict "activate only as a sorcery" then none
      else
        match parsePrintedCosts "" costText, parseReturnThisFromGraveyard ret with
        | some costs, some action =>
          some (.ability (
            .graveyardActivatedIf
              (.timeToCastSorcery (.controller .this))
              costs
              action))
        | _, _ => none
    | _ => none

/-- `When this creature enters, each opponent discards a card.`
The entering object is this card. -/
def parseEnterEachOpponentDiscards (cardName : String) (line : String) :
    Option CardPart :=
  onSelfTrigger cardName line " enters, " (.enter .this) fun effect =>
    (after? effect "each opponent discards ").bind parseCardCount |>.map fun k =>
      .discard (.opponent (.controller .this)) (Value.nat k)

/-- A pronoun for the object named earlier in the same ability. -/
def isPersonalPronoun (s : String) : Bool :=
  match norm s with
  | "he" | "she" | "it" | "they" => true
  | _ => false

/-- `When Gandalf enters, he deals 3 damage divided as you choose among one, two, or three targets.`
The entering object is this card. The damage source is a pronoun for that
object, or another reference to this card. Its controller divides the damage
(CR 601.2d). `targets` with no type is any target. The counts are a positive
contiguous range, and those targets are numbered `n`. -/
def parseEnterDividedDamage (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (before? (normLine line) " targets").bind fun body =>
    (whenSelfEffect? cardName body " enters, ").bind fun effect =>
      (split2? effect " deals ").bind fun (who, rest) =>
        if who.isEmpty || !(isPersonalPronoun who || refersToSelf cardName who) then none
        else
          (split2? rest " damage divided as you choose among ").bind fun (amt, counts) =>
            match positiveCount amt, parseContiguousCounts counts with
            | some amount, some (lo, hi) =>
              some (
                .ability (
                  .triggered
                    (.enter .this)
                    (.divideDamage
                      (.controller .this)
                      (.source .this)
                      (.targets n (.range (Value.nat lo) (Value.nat hi)) .all)
                      (Value.nat amount))),
                n + 1)
            | _, _ => none

/-- `When this Equipment enters, you may discard a card. If you do, draw two cards.`
The entering object is this card. “If you do” means the draw happens only
when that discard is taken. The discard is action `n`. -/
def parseEnterMayDiscardDraw (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences (stripReminderParenthetical line) with
  | [may, ifYouDo] =>
    (whenSelfEffect? cardName (norm may) " enters, ").bind fun effect =>
      (after? effect "you may discard ").bind fun discardedText =>
        match parseCardCount discardedText,
            (after? (norm ifYouDo) "if you do, draw ").bind parseCardCount with
        | some discarded, some drawn =>
          some (
            .ability (
              .triggered
                (.enter .this)
                (.sequence [
                  .optional
                    (.actionId n
                      (.discard (.controller .this) (Value.nat discarded))),
                  .if
                    (.happened (.actionWithId n) .gameStart)
                    [.draw (.controller .this) (Value.nat drawn)]])),
            n + 1)
        | _, _ => none
  | _ => none

/-- `Galion's` or `this creature's` names this card. -/
def possessiveSelf (cardName whose : String) : Bool :=
  (before? (norm whose) "'s").any (refersToSelf cardName)

/-- `up to one other target creature you control` as zero or one other
permanent of those types you control (CR 115.1). -/
def parseUpToOneOtherYouControl (s : String) : Option Selector :=
  (between? (norm s) "up to one other target " " you control").bind fun obj =>
    parseControlledPhrase ("other " ++ obj ++ " you control")

/-- `Whenever Galion attacks, choose up to one other target creature you control. Its base power and toughness become equal to Galion's power and toughness until end of turn.`
The attacker is this card. The chosen creature is target `n`. -/
def parseAttackSetBasePT (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences (stripReminderParenthetical line) with
  | [attack, become] =>
    (triggerSelfEffect? cardName "whenever" (norm attack) " attacks, ").bind fun effect =>
      (after? effect "choose ").bind parseUpToOneOtherYouControl |>.bind fun among =>
        (between? (normSentence become)
            "its base power and toughness become equal to "
            " power and toughness until end of turn").bind fun whose =>
          if !possessiveSelf cardName whose then none
          else
            some (
              .ability (
                .triggered
                  (.attack .this .all)
                  (.continuous
                    [.setBasePower
                      (.targets n (.range 0 1) among)
                      (Value.greatestPower (.source .this)),
                     .setBaseToughness
                      (.targetReference n)
                      (Value.greatestToughness (.source .this))]
                    .endOfTurn)),
              n + 1)
  | _ => none

/-- `Whenever another Elf you control enters, this creature gets +1/+1 until end of turn.`
`another` excludes this object. -/
def parseAnotherElfEntersGets (line : String) : Option CardPart :=
  triggeredSourcePump (normLine line) "whenever another elf you control enters, "
    (.enter
      (.intersection [
        .not .this,
        .permanent,
        .subtype .elf,
        youControl]))
    (· == (1, 1))

/-- `{T}: Add X mana of any one color, where X is this creature's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources.`
The tap symbol is the cost. X is this creature's power. The produced mana is
action `n`. -/
def parseTapAddAnyColorEqualToPower (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (split2? (stripTrailingPeriod (stripReminderParenthetical line)) ": ").bind
    fun (costText, effect) =>
      if norm costText != "{t}" then none
      else
        match sentences effect with
        | [add, spend] =>
          (after? (normSentence add) "add x mana of any one color, where x is ").bind
              (before? · " power") |>.bind fun whose =>
            if possessiveSelf cardName whose &&
                sentenceIs spend
                  "spend this mana only to cast elf spells and activate abilities of elf sources" then
              some (
                .ability (
                  .activated
                    [.tapSymbol]
                    (.sequence [
                      .actionId n
                        (.addManaOfOneColor
                          (.controller .this)
                          ManaSymbol.anyColor
                          (.greatestPower .this)),
                      .continuous
                        [.forbid
                          (.spendManaCreatedByAction n
                            (.not
                              (.or
                                (.castSpell (.subtype .elf))
                                (.activateAbility (.subtype .elf)))))]
                        .endOfTurn])),
                n + 1)
            else none
        | _ => none

/-- `<this>'s power and toughness are each equal to the number of lands you control.`
A characteristic-defining ability (CR 208.2a / 604.3). -/
def parseLandsCharacteristic (cardName : String) (line : String) : Option (List CardPart) :=
  (before? (normLine line) (" " ++ landsCharacteristicSuffix)).bind fun whose =>
    if possessiveSelf cardName whose then
      some (powerToughnessEqualLandsAbilities.map fun a => .ability a)
    else none

/-- The printed clause after `<this>'s`. -/
def creaturesPowerSuffix : String :=
  "power is equal to the number of creatures you control"

/-- `<this>'s power is equal to the number of creatures you control.`
A characteristic-defining ability (CR 208.2a / 604.3). Power is set to that
count. Toughness is not changed. -/
def parseCreaturesPowerCharacteristic (cardName : String) (line : String) :
    Option (List CardPart) :=
  (before? (normLine line) (" " ++ creaturesPowerSuffix)).bind fun whose =>
    if possessiveSelf cardName whose then
      some [.ability (.static (.setPower .this (.count creaturesYouControl)))]
    else none

/-- `When this creature enters, search your library for a Forest card, put that card onto the battlefield, then shuffle.`
The entering object is this card. -/
def parseEnterSearchForest (cardName : String) (line : String) : Option CardPart :=
  onSelfTrigger cardName line " enters, " (.enter .this) fun effect =>
    if sentenceIs effect
        "search your library for a forest card, put that card onto the battlefield, then shuffle" then
      some (.searchLibraryThenShuffle
        (.controller .this)
        [.putOntoBattlefield
          (.selected
            (.controller .this)
            (.range 1 1)
            (.intersection [.inLibrary, .subtype .forest]))])
    else none

/-- One card part that does not advance the target number. -/
def sole (part? : Option CardPart) (n : Nat) : Option (List CardPart × Nat) :=
  part?.map fun part => ([part], n)

/-- One card part together with the target number it produced. -/
def carry (parsed : Option (CardPart × Nat)) : Option (List CardPart × Nat) :=
  parsed.map fun (part, n') => ([part], n')

/-- Spell actions. Empty actions are a failed parse, not a blank spell. -/
def spellActions (parsed : Option (List CardAction × Nat)) : Option (List CardPart × Nat) :=
  parsed.bind fun (actions, n') =>
    if actions.isEmpty then none else some ([.actions actions], n')

/-- `<this> enters tapped.` A replacement effect (CR 614.1). A spell does not
enter the battlefield. -/
def parseEntersTapped (cardName line : String) : Option CardPart :=
  (before? (normLine line) " enters tapped").bind fun subject =>
    if subject.isEmpty || norm subject == "this spell" ||
        !refersToSelf cardName subject then
      none
    else
      some (.ability (.static (.replace (.enter .this)
        [.putOntoBattlefieldInState .this [.tapped]])))

/-- One colored or colorless symbol that can be added to a mana pool. -/
def addableSymbol? (s : String) : Option ManaSymbol :=
  match parseManaSymbols s with
  | some [sym] =>
    match CardAction.addedManaType? sym with
    | some _ => some sym
    | none => none
  | _ => none

/-- `Add {G} or {U}`: the player chooses one listed symbol. -/
def parseAddOneOf (effect : String) : Option (List CardAction) :=
  (after? (normSentence effect) "add ").bind fun rest =>
    let options := rest.splitOn " or " |>.map copied |>.filter (· != "")
    if options.length < 2 then none
    else
      options.mapM fun opt =>
        (addableSymbol? opt).map fun sym => .addMana (.controller .this) [sym]

/-- `{T}: Add {G} or {U}.` The tap symbol is the cost (CR 107.5). -/
def parseTapAddOneOf (line : String) : Option CardPart :=
  (split2? (stripTrailingPeriod (stripReminderParenthetical line)) ": ").bind
    fun (costText, effect) =>
      if norm costText != "{t}" then none
      else
        (parseAddOneOf effect).map fun actions =>
          .ability (.activated [.tapSymbol]
            (.playerSelectAction (.controller .this) (.range 1 1) actions))

/-- One word of a typecycling type phrase. -/
def addCyclingWord
    (acc : Option (List CardSupertype × List CardType × List CardSubtype))
    (w : String) : Option (List CardSupertype × List CardType × List CardSubtype) :=
  acc.bind fun (sups, tys, sts) =>
    match supertypeOfOracle? w with
    | some s => some (sups ++ [s], tys, sts)
    | none =>
      match typeOfOracle? w with
      | some t => some (sups, tys ++ [t], sts)
      | none =>
        match subtypeOfOracle? w with
        | some st => some (sups, tys, sts ++ [st])
        | none => none

/-- `Halfling` or `Basic land` as the type a cycling ability searches for. -/
def parseCyclingWords (phrase : String) :
    Option (List CardSupertype × List CardType × List CardSubtype) :=
  let words := (norm phrase).splitOn " " |>.map copied |>.filter (· != "")
  if words.isEmpty then none
  else
    match words.foldl addCyclingWord (some ([], [], [])) with
    | some (sups, tys, sts) =>
      if tys.isEmpty && sts.isEmpty then none else some (sups, tys, sts)
    | none => none

/-- `Halflingcycling {4}`. Reminder text is not rules text (CR 702.29). -/
def parseTypecycling (line : String) : Option CardPart :=
  let line := stripTrailingPeriod (stripReminderParenthetical line)
  let (phrase, costText) := splitNameCost line
  if costText.isEmpty then none
  else
    (before? (norm phrase) "cycling").bind fun kind =>
      match parseCyclingWords kind, nonemptyMana? costText with
      | some (sups, tys, sts), some syms =>
        some (.ability (.keywordWithCost (.typecycling sups tys sts) [.mana syms]))
      | _, _ => none

/-- `When this Equipment enters, you gain 2 life.` The entering object is this card. -/
def parseEnterYouGainLife (cardName line : String) : Option CardPart :=
  onSelfTrigger cardName line " enters, " (.enter .this) fun effect =>
    match parseYouGainLife effect 0 with
    | some (action, _) => some action
    | none => none

/-- `When this creature enters, untap another target creature you control. If that creature is a Bear, put a +1/+1 counter on it.`
The creature is target `n`. `another` excludes this object. -/
def parseEnterUntapPlusOneIfSubtype (cardName line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences (stripReminderParenthetical line) with
  | [enter, ifSubtype] =>
    (whenSelfEffect? cardName (norm enter) " enters, ").bind fun effect =>
      (after? effect "untap ").bind parseBattlefieldTarget |>.bind fun sel =>
        if !sel.shape.anotherCreatureYouControl then none
        else
          (between? (normSentence ifSubtype)
              "if that creature is " ", put a +1/+1 counter on it").bind
            dropArticle? |>.bind subtypeOfOracle? |>.map fun st =>
            (.ability (
              .triggered
                (.enter .this)
                (.sequence [
                  .untap (.target n sel),
                  .if
                    (.anySubtype (.targetReference n) st)
                    [.putCounter (.targetReference n) .plusOnePlusOne 1]])),
             n + 1)
  | _ => none

/-- `When <this card> enters, recruit.`
Recruit is a keyword action of this card's controller. A reminder
parenthetical is not rules text (CR 207.2). -/
def parseEnterRecruit (cardName : String) (line : String) : Option CardPart :=
  onSelfTrigger cardName line " enters, " (.enter .this) fun effect =>
    if effect == "recruit" then some (.keyword (.controller .this) .recruit) else none

/-- `When <this card> dies, recruit.`
Recruit is a keyword action of this card's controller. A reminder
parenthetical is not rules text (CR 207.2). -/
def parseDiesRecruit (cardName : String) (line : String) : Option CardPart :=
  onSelfTrigger cardName line " dies, " (.die .this) fun effect =>
    if effect == "recruit" then some (.keyword (.controller .this) .recruit) else none

/-- `When <this card> enters, scry N.`
`N` is a positive printed number. A reminder parenthetical is not rules text. -/
def parseEnterScry (cardName : String) (line : String) : Option CardPart :=
  onSelfTrigger cardName line " enters, " (.enter .this) fun effect =>
    match parseScry effect 0 with
    | some (action, _) => some action
    | none => none

/-- `create a Treasure token` or `create a tapped Treasure token`.
A tapped token enters tapped (CR 110.5). -/
def parseCreateTreasure (sentence : String) : Option CardAction :=
  match normSentence sentence with
  | "create a tapped treasure token" =>
    some (.createTokens (.controller .this) 1 PredefinedToken.treasureToken [.tapped])
  | "create a treasure token" =>
    some (.createTokens (.controller .this) 1 PredefinedToken.treasureToken)
  | _ => none

/-- `When <this card> enters, create a Treasure token.`
Also `create a tapped Treasure token`. -/
def parseEnterCreateTreasure (cardName : String) (line : String) : Option CardPart :=
  onSelfTrigger cardName line " enters, " (.enter .this) parseCreateTreasure

/-- `When <this card> enters, exile the top card of your library. Until the end of your next turn, you may play that card.`
The exile is action `n`. The exiled card may be played until the end of your
next turn (CR 611.2a). -/
def parseEnterExileTopMayPlay (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences (stripReminderParenthetical line) with
  | [enter, play] =>
    (whenSelfEffect? cardName (norm enter) " enters, ").bind fun effect =>
      if !sentenceIs effect "exile the top card of your library" then none
      else if !sentenceIs play
          "until the end of your next turn, you may play that card" then none
      else
        some (
          .ability (.triggered (.enter .this) (exileTopPlayUntilEndOfNextTurn n)),
          n + 1)
  | _ => none

/-- `This spell can't be countered.`
Countering this spell is forbidden. The ability functions while this spell
is on the stack (CR 113.6b). -/
def parseCantBeCountered (line : String) : Option CardPart :=
  if sentenceIs (rulesText line) "this spell can't be countered" then
    some (.ability (.stackStatic (.forbid (.counter .this))))
  else none

/-- A noncreature spell this object's controller casts. -/
def noncreatureSpellYouCast : Selector :=
  .intersection [.spell, .not (.cardType .creature), youControl]

/-- `Whenever you cast a noncreature spell, amass Goblins 1.`
Amass is a keyword action of this card's controller. A reminder
parenthetical is not rules text (CR 207.2). -/
def parseYouCastNoncreatureAmass (line : String) : Option CardPart :=
  onTrigger (.castSpell noncreatureSpellYouCast)
    ((after? (normLine line) "whenever you cast a noncreature spell, ").bind parseAmass)

/-- `When <this card> enters, amass Goblins 1.`
The entering object is this card. -/
def parseEnterAmass (cardName : String) (line : String) : Option CardPart :=
  onSelfTrigger cardName line " enters, " (.enter .this) parseAmass

/-- `When <this card> dies, amass Goblins 4.`
The dying object is this card. -/
def parseDiesAmass (cardName : String) (line : String) : Option CardPart :=
  onSelfTrigger cardName line " dies, " (.die .this) parseAmass

/-- `Whenever you attack, amass Goblins 2.`
“Whenever you attack” is one trigger when creatures you control attack at
the same time (CR 508.3 / 603.2d). -/
def parseYouAttackAmass (line : String) : Option CardPart :=
  onTrigger (.attackSimultaneously creaturesYouControl .all [])
    ((after? (normLine line) "whenever you attack, ").bind parseAmass)

/-- `You may cast this spell as though it had flash if you control a Human.`
The permission is checked as you begin to cast this spell, before the card
is put onto the stack (CR 601.3 / 702.8). `you` is `Selector.caster`, the
player who would cast the spell. The spell does not gain flash. -/
def parseCastAsThoughFlash (line : String) : Option CardPart :=
  (after? (normLine line)
      "you may cast this spell as though it had flash if you control ").bind
    dropArticle? |>.bind subtypeOfOracle? |>.map fun st =>
      .ability (.everywhereStatic (
        .canBeCastAsThoughWithFlashIf
          .this
          (.any (.intersection [.permanent, .subtype st, .controlled .caster]))))

/-- `<permanents> get +P/+T.` No duration is printed, so this is a static
ability (CR 604.2 / 613.4c). A zero bonus is omitted. `+0/+0` is not an
effect. A bonus that lasts until end of turn is a different ability. -/
def parseStaticGets (line : String) : Option (List CardPart) :=
  let s := normLine line
  if (split2? s " until end of turn").isSome then none
  else
    (splitGets? s).bind fun (who, ptText) =>
      match parseControlledPhrase who, parsePowerToughness ptText with
      | some sel, some (p, t) =>
        let effects := flatPowerToughness sel p t
        if effects.isEmpty then none
        else some (effects.map fun e => .ability (.static e))
      | _, _ => none

/-- `Whenever <this card> enters or attacks, recruit.`
Recruit is a keyword action of this card's controller. A reminder
parenthetical is not rules text (CR 207.2). -/
def parseEnterOrAttackRecruit (cardName : String) (line : String) : Option CardPart :=
  (triggerSelfEffect? cardName "whenever" (normLine line) " enters or attacks, ").bind
    fun effect =>
      if effect == "recruit" then
        some (.ability (.triggered
          (.or (.enter .this) (.attack .this .all))
          (.keyword (.controller .this) .recruit)))
      else none

/-- `When <this card> enters, put a +1/+1 counter on target <permanent>.`
The entering object is this card. The target is `n`. -/
def parseEnterPutPlusOneOnTarget (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onSelfTriggerN cardName line " enters, " (.enter .this) (parsePutPlusOneOnTarget · n)

/-- One non-empty Oracle line. A reminder-only line contributes no parts.
Anything else that the grammar does not cover fails.
The first parser that accepts the line wins. -/
def parseOneLine (cardName : String) (line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  if (rulesText line).isEmpty then some ([], n)
  else
    (keywordParts? line).map (·, n) <|>
    sole (parseEntersTapped cardName line) n <|>
    sole (parseTypecycling line) n <|>
    carry (parseActivatedAbility cardName line n) <|>
    sole (parseTapAddOneOf line) n <|>
    carry (parseTapAddAnyColorEqualToPower cardName line n) <|>
    sole (parseAnotherElfEntersGets line) n <|>
    carry (parseLandYouControlEnters line n) <|>
    (parseLandsCharacteristic cardName line).map (·, n) <|>
    (parseCreaturesPowerCharacteristic cardName line).map (·, n) <|>
    sole (parseCantBeCountered line) n <|>
    sole (parseCastAsThoughFlash line) n <|>
    (parseStaticGets line).map (·, n) <|>
    sole (parseYouCastNoncreatureAmass line) n <|>
    sole (parseYouAttackAmass line) n <|>
    sole (parseEnterOrAttackRecruit cardName line) n <|>
    sole (parseEnterAmass cardName line) n <|>
    sole (parseDiesAmass cardName line) n <|>
    sole (parseEnterSearchForest cardName line) n <|>
    sole (parseGraveyardReturn line) n <|>
    carry (parseEnterExileOppGyLoseLife cardName line n) <|>
    sole (parseCostReduction line) n <|>
    sole (parseAttackTriggered line) n <|>
    carry (parseAttackSetBasePT cardName line n) <|>
    sole (parseFerociousThisAttacks line) n <|>
    sole (parseFerociousYouAttack line) n <|>
    sole (parseFerociousBeginCombat line) n <|>
    sole (parseEnterYouGainLife cardName line) n <|>
    carry (parseEnterUntapPlusOneIfSubtype cardName line n) <|>
    sole (parseEnterRecruit cardName line) n <|>
    sole (parseDiesRecruit cardName line) n <|>
    sole (parseEnterScry cardName line) n <|>
    sole (parseEnterCreateTreasure cardName line) n <|>
    carry (parseEnterExileTopMayPlay cardName line n) <|>
    carry (parseEnterPutPlusOneOnTarget cardName line n) <|>
    sole (parseEnterDraw cardName line) n <|>
    sole (parseEnterEachOpponentDiscards cardName line) n <|>
    carry (parseEnterDividedDamage cardName line n) <|>
    carry (parseEnterMayDiscardDraw cardName line n) <|>
    carry (parseEnterTargetOpponentSacrifices cardName line n) <|>
    carry (parseDiesOppGets cardName line n) <|>
    carry (parseOtherCreaturesDieScry line n) <|>
    sole (parseDrawSecondPlusOne line) n <|>
    sole (parseYouDrawPlusOne line) n <|>
    sole (parseCantBeBlockedByTokens cardName line) n <|>
    sole (parseCantBeBlocked cardName line) n <|>
    sole (parseCantBlock cardName line) n <|>
    sole (parseCombatDamageLoot cardName line) n <|>
    sole (parseAdditionalCostSacrificeOrPay line) n <|>
    (parseEquippedGets line).map (·, n) <|>
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
      (parseOneLine cardName line n).bind fun (here, nHere) =>
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
      (parseModeAction text n).bind fun (action, n') =>
        parseModeLines cardName rest n' (acc ++ [action])
    | none =>
      (chooseOneParts acc).bind fun head =>
        if isChooseOneHeader line then
          (parseModeLines cardName rest n []).map fun (more, nMore) =>
            (head ++ more, nMore)
        else
          (parseOneLine cardName line n).bind fun (here, nHere) =>
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
    (parseNameAndCost nameLine).bind fun nameParts =>
      match rest with
      | [] => some nameParts
      | typeLine :: effectLines =>
        (parseTypeLine typeLine).bind fun typeParts =>
          -- An Adventure face refers to itself by its own name.
          let faceName := nameOfParts nameParts |>.getD cardName
          match effectLines with
          | [] => some (nameParts ++ typeParts)
          | _ =>
            (actionsFromText faceName (String.intercalate " " effectLines) n).bind
              fun (actions, _) =>
                if actions.isEmpty then none
                else some (nameParts ++ typeParts ++ [.actions actions])

/-- Steps of a sequence, in order. A sequence is those steps. -/
def flattenAction : CardAction → List CardAction
  | .sequence as => as.flatMap flattenAction
  | action => [action]

/-- Successive spell lines are one effect, in printed order. -/
def mergeConsecutiveActions (parts : List CardPart) : List CardPart :=
  go parts []
where
  go : List CardPart → List CardPart → List CardPart
    | [], acc => acc.reverse
    | .actions here :: rest, .actions earlier :: acc =>
      go rest
        (.actions (earlier.flatMap flattenAction ++ here.flatMap flattenAction) :: acc)
    | part :: rest, acc => go rest (part :: acc)

end OracleParts

open OracleParts

/-- Parse printed Oracle text into `CardPart`s.
The patterns this accepts are the module's recognized Oracle text.
`name` is the card being parsed. Text that uses that name, the short name
before a comma (CR 201.5), or that name's first word when it is not an
article, means this card, as do `this` and `this <type>`.
`Gollum the Abandoned` refers to itself as `Gollum`.
Returns `none` when a line, sentence, mode, or Adventure face is not
recognized. Reminder parentheticals are not rules text. Empty text is
`some []`. Successive spell lines are one effect, in printed order. -/
def parseOracleParts (name : String) (text : String) : Option (List CardPart) :=
  let lines :=
    text.splitOn "\n" |>.map (·.trimAscii.copy) |>.filter (· != "")
  let (main, adv) := splitAdventure lines
  (parseMainLines name main 1).bind fun (mainParts, n) =>
    let mainParts := mergeConsecutiveActions mainParts
    match adv with
    | [] => some mainParts
    | _ =>
      (parseAdventure name adv n).map fun alt =>
        mainParts ++ [.alternative alt]

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
        [.addPower
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)]) (Value.int 1),
         .addToughness
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)]) (Value.int 1)]
        .endOfTurn))]
#guard parseOracleParts (name := "") "Tap one or two target creatures." ==
  some [.actions [
    .tap (.targets 1 (.range 1 2) (.intersection [.permanent, .cardType .creature]))]]
#guard parseOracleParts (name := "") "Tap two or one target creatures." == none
#guard parseOracleParts (name := "") "Tap 0 target creatures." == none
#guard parseOracleParts (name := "") "Tap 0 or 1 target creatures." == none
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
#guard parseOracleParts (name := "") "This spell deals 0 damage to target creature." == none
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
#guard
  let others : Selector :=
    .intersection [
      .not .this,
      .permanent,
      .cardType .creature,
      .controlled (.controller .this)]
  parseOracleParts (name := "")
    "Flying\nWhenever this creature attacks, it gets +1/+1 until end of turn for each other creature you control." ==
  some [
    .ability (.keyword .flying),
    .ability (
      .triggered
        (.attack .this .all)
        (.continuous
          [.addPower (.source .this) (Value.count others),
           .addToughness (.source .this) (Value.count others)]
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
    .continuous [.addPower (.targetReference 1) (Value.int 2),
                 .addToughness (.targetReference 1) (Value.int 2)] .endOfTurn,
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
  "Exchange control of 0 target nonland permanents that share a card type." == none
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
        [.addPower
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.opponent (.controller .this))])) (Value.int (-1)),
         .addToughness
          (.targetReference 1) (Value.int (-1))]
        .endOfTurn))]
#guard parseOracleParts (name := "Front Porch Sentries")
  "When Front Porch Sentries dies, target creature an opponent controls gets -1/-1 until end of turn." ==
  some [.ability (
    .triggered
      (.die .this)
      (.continuous
        [.addPower
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.opponent (.controller .this))])) (Value.int (-1)),
         .addToughness
          (.targetReference 1) (Value.int (-1))]
        .endOfTurn))]
#guard parseOracleParts (name := "")
  "When this creature dies, target creature an opponent controls gets +1/+1 until end of turn." ==
  some [.ability (
    .triggered
      (.die .this)
      (.continuous
        [.addPower
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.opponent (.controller .this))])) (Value.int 1),
         .addToughness
          (.targetReference 1) (Value.int 1)]
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
#guard parseOracleParts (name := "") "Destroy target creature with flying." ==
  some [.actions [
    .destroy
      (.target 1
        (.intersection [
          .permanent,
          .cardType .creature,
          .keyword .flying]))]]
#guard parseOracleParts (name := "") "Destroy target creature with power 4 or greater." ==
  some [.actions [
    .destroy
      (.target 1
        (.intersection [
          .permanent,
          .cardType .creature,
          .powerAtLeast (Value.int 4)]))]]
#guard parseOracleParts (name := "") "Destroy target creature with power 0 or greater." == none
#guard parseOracleParts (name := "") "Destroy target creature with power 4 or less." == none
#guard parseOracleParts (name := "") "Destroy target creature with power 4." == none
#guard parseOracleParts (name := "") "Destroy target creature with haste and flying." == none
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
          [.addPower (.source .this) (Value.int 2),
           .addToughness (.source .this) (Value.int 2)]
          .endOfTurn)))]
#guard parseOracleParts (name := "")
  "Pay 2 life: This creature gets +2/+2 until end of turn." ==
  some [.ability (
    .activated
      [.life 2]
      (.continuous
        [.addPower (.source .this) (Value.int 2),
         .addToughness (.source .this) (Value.int 2)]
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
  some [.ability (.static (.addPower (.hostOf .this) (Value.int 2))),
.ability (.static (.addToughness (.hostOf .this) (Value.int 1)))]
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
    .ability (.static (.addPower (.hostOf .this) (Value.int 2))),
    .ability (.static (.addToughness (.hostOf .this) (Value.int 1))),
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
      [.addPower
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        (Value.int 2),
       .addToughness
        (.targetReference 1)
        (Value.int 2),
       .gainAbility (.targetReference 1) (.keyword .lifelink)]
      .endOfTurn]]
#guard parseOracleParts (name := "")
  "Target creature gets +2/+2 and has lifelink until end of turn." == none
#guard parseOracleParts (name := "") "Target creature gets +0/+0 until end of turn." == none
#guard parseOracleParts (name := "") "Target creature gets +0/+1 until end of turn." ==
  some [.actions [
    .continuous
      [.addToughness
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        (Value.int 1)]
      .endOfTurn]]
#guard parseOracleParts (name := "")
  "{W}: This creature gets +0/+0 until end of turn." == none
#guard parseOracleParts (name := "")
  "Target creature gets -5/-5 until end of turn. If that creature would die this turn, exile it instead." ==
  some [.actions [
    .continuous
      [.addPower
        (.target 1 (.intersection [.permanent, .cardType .creature]))
        (Value.int (-5)),
       .addToughness
        (.targetReference 1)
        (Value.int (-5)),
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
      [.addPower
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.target 1 .player)])
        (Value.int (-1)),
       .addToughness
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.targetReference 1)])
        (Value.int (-1))]
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
        [.addPower
          (.target 1 (.intersection [.permanent, .cardType .creature]))
          (Value.int (-5)),
         .addToughness
          (.targetReference 1)
          (Value.int (-5)),
         .replace
           (.putToGraveyard (.targetReference 1))
           [.exile (.replacingObject)]]
        .endOfTurn,
      .continuous
        [.addPower
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.target 2 .player)])
          (Value.int (-1)),
         .addToughness
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.targetReference 2)])
          (Value.int (-1))]
        .endOfTurn]]]
#guard parseOracleParts (name := "")
  "Choose one —\n• Target player draws two cards and loses 2 life.\n• Target creature gets +2/+2 and gains lifelink until end of turn." ==
  some [.actions [
    .chooseMode [
      .sequence [
        .draw (.target 1 .player) 2,
        .loseLife (.targetReference 1) 2],
      .continuous
        [.addPower
          (.target 2 (.intersection [.permanent, .cardType .creature]))
          (Value.int 2),
         .addToughness
          (.targetReference 2)
          (Value.int 2),
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
    .ability (.static (.addPower (.hostOf .this) (Value.int 2))),
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

#guard parseOracleParts (name := "")
  "{5}{G}{G}: Put three +1/+1 counters on this creature." ==
  some [.ability (
    .activated
      [.mana [.generic 5, .mono .green, .mono .green]]
      (.putCounter (.source .this) .plusOnePlusOne 3))]
#guard parseOracleParts (name := "")
  "{1}: Put a +1/+1 counter on this creature." ==
  some [.ability (
    .activated [.mana [.generic 1]] (.putCounter (.source .this) .plusOnePlusOne 1))]
#guard parseOracleParts (name := "")
  "{1}: Put three +1/+1 counter on this creature." == none
#guard parseOracleParts (name := "")
  "{1}: Put a +1/+1 counters on this creature." == none
#guard parseOracleParts (name := "")
  "{1}: Put three +1/+1 counters on target creature." == none
#guard parseOracleParts (name := "")
  "Sacrifice another creature or artifact: Exile the top card of your library. You may play it until the end of your next turn. Activate only during your turn and only once each turn." ==
  some [.ability (
    .abilityId 1
      (.activatedIf
        (.and
          (.turn (.controller .this))
          (.didNotHappen (.abilityWithIdActivated 1) .turnStart))
        [.sacrificeCount
          (.intersection [
            .not .this,
            .permanent,
            .union [.cardType .creature, .cardType .artifact]])
          1]
        (.sequence [
          .actionId 1 (.exile (.topOfLibrary (.controller .this))),
          .continuous
            [.canPlay (.controller .this) (.wasCreatedByAction 1)]
            (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])])))]
#guard parseOracleParts (name := "")
  "Sacrifice a creature or artifact: Exile the top card of your library. You may play it until the end of your next turn. Activate only during your turn and only once each turn." ==
  none
#guard parseOracleParts (name := "")
  "Sacrifice another creature or artifact: Exile the top card of your library. You may play it until end of turn. Activate only during your turn and only once each turn." ==
  none
#guard parseOracleParts (name := "")
  "Target creature you control deals damage equal to its power to target creature an opponent controls." ==
  some [.actions [
    .dealDamageEqualToPower
      (.target 1
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)]))
      (.target 2
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.opponent (.controller .this))]))]]
#guard parseOracleParts (name := "")
  "Target creature deals damage equal to its power to target creature an opponent controls." ==
  none
#guard parseOracleParts (name := "Galion, Elvenking's Butler")
  "Whenever Galion attacks, choose up to one other target creature you control. Its base power and toughness become equal to Galion's power and toughness until end of turn." ==
  some [.ability (
    .triggered
      (.attack .this .all)
      (.continuous
        [.setBasePower
          (.targets 1 (.range 0 1)
            (.intersection [
              .not .this,
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)]))
          (Value.greatestPower (.source .this)),
         .setBaseToughness
          (.targetReference 1)
          (Value.greatestToughness (.source .this))]
        .endOfTurn))]
#guard parseOracleParts (name := "Galion, Elvenking's Butler")
  "Whenever this creature attacks, choose up to one other target creature you control. Its base power and toughness become equal to this creature's power and toughness until end of turn." ==
  parseOracleParts (name := "Galion, Elvenking's Butler")
    "Whenever Galion attacks, choose up to one other target creature you control. Its base power and toughness become equal to Galion's power and toughness until end of turn."
#guard parseOracleParts (name := "Gandalf")
  "Whenever Galion attacks, choose up to one other target creature you control. Its base power and toughness become equal to Galion's power and toughness until end of turn." ==
  none
#guard parseOracleParts (name := "Galion, Elvenking's Butler")
  "Whenever Galion attacks, choose up to one target creature you control. Its base power and toughness become equal to Galion's power and toughness until end of turn." ==
  none
#guard parseOracleParts (name := "")
  "Choose one —\n• Destroy target creature with flying.\n• Put a +1/+1 counter on target creature you control. It gains trample and hexproof until end of turn. (It can't be the target of spells or abilities your opponents control.)" ==
  some [.actions [
    .chooseMode [
      .destroy
        (.target 1
          (.intersection [
            .permanent,
            .cardType .creature,
            .keyword .flying])),
      .sequence [
        .putCounter
          (.target 2
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)]))
          .plusOnePlusOne
          1,
        .continuous
          [.gainAbility (.targetReference 2) (.keyword .trample),
            .gainAbility (.targetReference 2) (.keyword .hexproof)]
          .endOfTurn]]]]
#guard parseOracleParts (name := "")
  "Put a +1/+1 counter on target creature you control. It gets trample until end of turn." ==
  none
#guard parseOracleParts (name := "")
  "Choose one —\n• Put a +1/+1 counter on target creature you control." == none
#guard parseOracleParts (name := "Beorn's Hospitality")
  "Landfall — Whenever a land you control enters, put a +1/+1 counter on target creature you control.\n{5}{G}{G}: This enchantment becomes a Bear creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\" (This effect doesn't end.)" ==
  some [
    .ability (
      .triggered
        (.enter
          (.intersection [
            .permanent,
            .cardType .land,
            .controlled (.controller .this)]))
        (.putCounter
          (.target
            1
            (.intersection [
              .permanent,
              .cardType .creature,
              .controlled (.controller .this)]))
          .plusOnePlusOne
          1)),
    .ability (
      .activated
        [.mana [.generic 5, .mono .green, .mono .green]]
        (.continuous
          [.gainType .this .creature,
            .gainSubtype .this .bear,
            .gainAbility
              .this
              (.static
                (.setPower
                  .this
                  (.count
                    (.intersection [
                      .permanent,
                      .cardType .land,
                      .controlled (.controller .this)])))),
            .gainAbility
              .this
              (.static
                (.setToughness
                  .this
                  (.count
                    (.intersection [
                      .permanent,
                      .cardType .land,
                      .controlled (.controller .this)]))))]
          .endOfGame))]
#guard parseOracleParts (name := "")
  "Whenever a land you control enters, put a +1/+1 counter on target creature you control." ==
  parseOracleParts (name := "")
    "Landfall — Whenever a land you control enters, put a +1/+1 counter on target creature you control."
#guard parseOracleParts (name := "")
  "{1}{G}: This enchantment becomes an Elf creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\"" ==
  some [.ability (
    .activated
      [.mana [.generic 1, .mono .green]]
      (.continuous
        [.gainType .this .creature,
          .gainSubtype .this .elf,
          .gainAbility
            .this
            (.static
              (.setPower
                .this
                (.count
                  (.intersection [
                    .permanent,
                    .cardType .land,
                    .controlled (.controller .this)])))),
          .gainAbility
            .this
            (.static
              (.setToughness
                .this
                (.count
                  (.intersection [
                    .permanent,
                    .cardType .land,
                    .controlled (.controller .this)]))))]
        .endOfGame))]
#guard parseOracleParts (name := "")
  "Landfall — Whenever a land enters, put a +1/+1 counter on target creature you control." == none
#guard parseOracleParts (name := "")
  "Whenever a land you control enters, put a +1/+1 counter on target creature." == none
#guard parseOracleParts (name := "Gandalf")
  "{5}{G}{G}: Beorn's Hospitality becomes a Bear creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\"" ==
  none
#guard parseOracleParts (name := "")
  "{5}{G}{G}: This enchantment becomes a Bear creature in addition to its other types and its power and toughness are each equal to the number of lands you control." ==
  none
#guard parseOracleParts (name := "")
  "{1}{G}: This enchantment becomes a Bear creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\" until end of turn." ==
  none
#guard englishSmall? " 2 " == some 2
#guard englishSmall? "Two" == some 2
#guard positiveCount "0" == none
#guard positiveCount " 3 " == some 3
#guard parseOracleParts (name := "") "When this creature enters, draw one card." ==
  parseOracleParts (name := "") "When this creature enters, draw a card."
#guard parseOracleParts (name := "") "When this creature enters, draw 1 card." ==
  parseOracleParts (name := "") "When this creature enters, draw a card."
#guard parseOracleParts (name := "") "When this creature enters, draw a cards." == none
#guard parseOracleParts (name := "") "When this creature enters, draw one cards." == none
#guard parseOracleParts (name := "")
  "Sacrifice a creature: This creature gets +1/+1 until end of turn." == none
#guard parseOracleParts (name := "") "Reach, trample, haste" ==
  some [
    .ability (.keyword .reach),
    .ability (.keyword .trample),
    .ability (.keyword .haste)]
#guard parseOracleParts (name := "") "Reach, deathtouch" ==
  some [.ability (.keyword .reach), .ability (.keyword .deathtouch)]
#guard parseOracleParts (name := "")
  "Whenever another Elf you control enters, this creature gets +1/+1 until end of turn." ==
  some [.ability (
    .triggered
      (.enter
        (.intersection [
          .not .this,
          .permanent,
          .subtype .elf,
          .controlled (.controller .this)]))
      (.continuous
        [.addPower (.source .this) (Value.int 1),
         .addToughness (.source .this) (Value.int 1)]
        .endOfTurn))]
#guard parseOracleParts (name := "")
  "Whenever another Bear you control enters, this creature gets +1/+1 until end of turn." == none
#guard parseOracleParts (name := "")
  "Whenever another Elf you control enters, this creature gets +2/+2 until end of turn." == none
#guard parseOracleParts (name := "")
  "Landfall — Whenever a land you control enters, this creature gets +1/+1 until end of turn." ==
  some [.ability (
    .triggered
      (.enter
        (.intersection [
          .permanent,
          .cardType .land,
          .controlled (.controller .this)]))
      (.continuous
        [.addPower (.source .this) (Value.int 1),
         .addToughness (.source .this) (Value.int 1)]
        .endOfTurn))]
#guard parseOracleParts (name := "")
  "Whenever a land you control enters, this creature gets +1/+1 until end of turn." ==
  parseOracleParts (name := "")
    "Landfall — Whenever a land you control enters, this creature gets +1/+1 until end of turn."
#guard parseOracleParts (name := "")
  "Landfall — Whenever a land you control enters, creatures you control get +1/+1 until end of turn." ==
  none
#guard parseOracleParts (name := "Woodland Weavemaster")
  "{T}: Add X mana of any one color, where X is this creature's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources." ==
  some [.ability (
    .activated
      [.tapSymbol]
      (.sequence [
        .actionId 1
          (.addManaOfOneColor
            (.controller .this)
            ManaSymbol.anyColor
            (.greatestPower .this)),
        .continuous
          [.forbid
            (.spendManaCreatedByAction 1
              (.not
                (.or
                  (.castSpell (.subtype .elf))
                  (.activateAbility (.subtype .elf)))))]
          .endOfTurn]))]
#guard parseOracleParts (name := "Woodland Weavemaster")
  "{T}: Add X mana of any one color, where X is Woodland Weavemaster's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources." ==
  parseOracleParts (name := "Woodland Weavemaster")
    "{T}: Add X mana of any one color, where X is this creature's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources."
#guard parseOracleParts (name := "Gandalf")
  "{T}: Add X mana of any one color, where X is Woodland Weavemaster's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources." ==
  none
#guard parseOracleParts (name := "Mirkwood Pathmaker")
  "Mirkwood Pathmaker's power and toughness are each equal to the number of lands you control." ==
  some [
    .ability (
      .static
        (.setPower
          .this
          (.count
            (.intersection [
              .permanent,
              .cardType .land,
              .controlled (.controller .this)])))),
    .ability (
      .static
        (.setToughness
          .this
          (.count
            (.intersection [
              .permanent,
              .cardType .land,
              .controlled (.controller .this)]))))]
#guard parseOracleParts (name := "")
  "This creature's power and toughness are each equal to the number of lands you control." ==
  parseOracleParts (name := "Mirkwood Pathmaker")
    "Mirkwood Pathmaker's power and toughness are each equal to the number of lands you control."
#guard parseOracleParts (name := "Gandalf")
  "Mirkwood Pathmaker's power and toughness are each equal to the number of lands you control." ==
  none
#guard parseOracleParts (name := "") "You may play an additional land this turn." ==
  some [.actions [
    .continuous
      [.increaseLandPlayLimit (.controller .this) (Value.nat 1)]
      .endOfTurn]]
#guard parseOracleParts (name := "") "You may play two additional lands this turn." == none
#guard parseOracleParts (name := "")
  "When this creature enters, search your library for a Forest card, put that card onto the battlefield, then shuffle." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.searchLibraryThenShuffle
        (.controller .this)
        [.putOntoBattlefield
          (.selected
            (.controller .this)
            (.range 1 1)
            (.intersection [.inLibrary, .subtype .forest]))]))]
#guard parseOracleParts (name := "Wood Elves")
  "When Wood Elves enters, search your library for a Forest card, put that card onto the battlefield, then shuffle." ==
  parseOracleParts (name := "")
    "When this creature enters, search your library for a Forest card, put that card onto the battlefield, then shuffle."
#guard parseOracleParts (name := "")
  "When this creature enters, search your library for an Island card, put that card onto the battlefield, then shuffle." ==
  none
#guard parseOracleParts (name := "")
  "Trample\n//ADV//\nTill and Tend {1}{G}\nSorcery — Adventure\nYou may play an additional land this turn. (Then exile this card. You may cast the creature later from exile.)" ==
  some [
    .ability (.keyword .trample),
    .alternative [
      .name "Till and Tend",
      .manaCost [.generic 1, .mono .green],
      .type .sorcery,
      .subtype .adventure,
      .actions [
        .continuous
          [.increaseLandPlayLimit (.controller .this) (Value.nat 1)]
          .endOfTurn]]]
#guard parseOracleParts (name := "Elvenking's Halls") "This land enters tapped." ==
  some [.ability (.static (.replace (.enter .this)
    [.putOntoBattlefieldInState .this [.tapped]]))]
#guard parseOracleParts (name := "") "This spell enters tapped." == none
#guard parseOracleParts (name := "") "This land enters." == none
#guard parseOracleParts (name := "") "{T}: Add {G} or {U}." ==
  some [.ability (.activated [.tapSymbol]
    (.playerSelectAction (.controller .this) (.range 1 1)
      [.addMana (.controller .this) [.mono .green],
       .addMana (.controller .this) [.mono .blue]]))]
#guard parseOracleParts (name := "") "{T}: Add {G}." == none
#guard parseOracleParts (name := "") "{T}: Add {2} or {G}." == none
#guard parseOracleParts (name := "")
  "{4}{U}: Target creature can't be blocked this turn." ==
  some [.ability (.activated [.mana [.generic 4, .mono .blue]]
    (.continuous
      [.forbid (.block .any
        (.target 1 (.intersection [.permanent, .cardType .creature])))]
      .endOfTurn))]
#guard parseOracleParts (name := "")
  "{2}{G}{U}, {T}, Sacrifice this land: Put two +1/+1 counters on target Elf you control. Activate only as a sorcery." ==
  some [.ability (.activatedIf (.timeToCastSorcery (.controller .this))
    [.mana [.generic 2, .mono .green, .mono .blue], .tapSymbol, .sacrifice .this]
    (.putCounter
      (.target 1 (.intersection
        [.permanent, .cardType .creature, .subtype .elf, .controlled (.controller .this)]))
      .plusOnePlusOne 2))]
#guard parseOracleParts (name := "")
  "{2}{B}{R}, {T}, Sacrifice this land: Put two +1/+1 counters on target Goblin or Orc you control. Activate only as a sorcery." ==
  some [.ability (.activatedIf (.timeToCastSorcery (.controller .this))
    [.mana [.generic 2, .mono .black, .mono .red], .tapSymbol, .sacrifice .this]
    (.putCounter
      (.target 1 (.intersection [
        .permanent, .cardType .creature,
        .union [.subtype .goblin, .subtype .orc],
        .controlled (.controller .this)]))
      .plusOnePlusOne 2))]
#guard parseOracleParts (name := "")
  "{2}{B}{G}, {T}, Sacrifice this land: Put two +1/+1 counter on target Bear, Spider, or Wolf you control. Activate only as a sorcery." ==
  none
#guard parseOracleParts (name := "")
  "{T}, Sacrifice this land: Search your library for a basic land card, put it onto the battlefield tapped, then shuffle." ==
  some [.ability (.activated [.tapSymbol, .sacrifice .this]
    (.searchLibraryThenShuffle (.controller .this)
      [.putOntoBattlefieldInState
        (.selected (.controller .this) (.range 1 1)
          (.intersection [.inLibrary, .cardType .land, .supertype .basic]))
        [.tapped]]))]
#guard parseOracleParts (name := "")
  "Halflingcycling {4} ({4}, Discard this card: Search your library for a Halfling card, reveal it, put it into your hand, then shuffle.)" ==
  some [.ability (.keywordWithCost (.typecycling [] [] [.halfling]) [.mana [.generic 4]])]
#guard parseOracleParts (name := "") "Halflingcycling" == none
#guard parseOracleParts (name := "") "Cycling {2}" == none
#guard parseOracleParts (name := "") "Basic landcycling {2}" ==
  some [.ability (.keywordWithCost (.typecycling [.basic] [.land] []) [.mana [.generic 2]])]
#guard parseOracleParts (name := "")
  "When this Equipment enters, you gain 2 life." ==
  some [.ability (.triggered (.enter .this) (.gainLife (.controller .this) 2))]
#guard parseOracleParts (name := "")
  "When this Equipment enters, target player gains 2 life." == none
#guard parseOracleParts (name := "")
  "When this creature enters, untap another target creature you control. If that creature is a Bear, put a +1/+1 counter on it." ==
  some [.ability (.triggered (.enter .this)
    (.sequence [
      .untap (.target 1 (.intersection [
        .not .this, .permanent, .cardType .creature, .controlled (.controller .this)])),
      .if (.anySubtype (.targetReference 1) .bear)
        [.putCounter (.targetReference 1) .plusOnePlusOne 1]]))]
#guard parseOracleParts (name := "")
  "When this creature enters, untap target creature you control. If that creature is a Bear, put a +1/+1 counter on it." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, this creature gets +2/+2 until end of turn." ==
  some [.ability (.triggeredWhile (.attack .this .all)
    (.any (.intersection [
      .permanent, .cardType .creature, .controlled (.controller .this),
      .powerAtLeast (Value.int 4)]))
    (.continuous
      [.addPower (.source .this) (Value.int 2), .addToughness (.source .this) (Value.int 2)]
      .endOfTurn))]
#guard parseOracleParts (name := "")
  "Whenever this creature attacks while you control a creature with power 4 or greater, this creature gets +2/+2 until end of turn." ==
  parseOracleParts (name := "")
    "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, this creature gets +2/+2 until end of turn."
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, creatures you control get +2/+2 until end of turn." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +1/+0 and creatures you control gain trample." ==
  some [.ability (.triggeredWhile (.attack .this .all)
    (.any (.intersection [
      .permanent, .cardType .creature, .controlled (.controller .this),
      .powerAtLeast (Value.int 4)]))
    (.continuous
      [.addPower (.source .this) (Value.int 1),
        .gainAbility
          (.intersection [
            .permanent, .cardType .creature, .controlled (.controller .this)])
          (.keyword .trample)]
      .endOfTurn))]
#guard parseOracleParts (name := "")
  "Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +1/+0 and creatures you control gain trample." ==
  parseOracleParts (name := "")
    "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +1/+0 and creatures you control gain trample."
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +0/+0 and creatures you control gain trample." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +1/+1 and creatures you control gain trample." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, until end of turn, this creature gets +1/+0 and creatures you control gain haste." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, put a +1/+1 counter on each creature you control." ==
  some [.ability (.triggeredWhile (.attack .this .all)
    (.any (.intersection [
      .permanent, .cardType .creature, .controlled (.controller .this),
      .powerAtLeast (Value.int 4)]))
    (.putCounter
      (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this)])
      .plusOnePlusOne
      1))]
#guard parseOracleParts (name := "")
  "Ferocious — Whenever this creature attacks while you control a creature with power 4 or greater, put two +1/+1 counters on each creature you control." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever you attack while you control a creature with power 4 or greater, you draw a card and lose 1 life." ==
  some [.ability (.triggeredWhile
    (.attackSimultaneously
      (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this)])
      .all
      [])
    (.any (.intersection [
      .permanent, .cardType .creature, .controlled (.controller .this),
      .powerAtLeast (Value.int 4)]))
    (.sequence [
      .draw (.controller .this) 1,
      .loseLife (.controller .this) 1]))]
#guard parseOracleParts (name := "")
  "Whenever you attack while you control a creature with power 4 or greater, you draw a card and lose 1 life." ==
  parseOracleParts (name := "")
    "Ferocious — Whenever you attack while you control a creature with power 4 or greater, you draw a card and lose 1 life."
#guard parseOracleParts (name := "")
  "Ferocious — Whenever you attack while you control a creature with power 4 or greater, you draw two cards and lose 1 life." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — Whenever you attack while you control a creature with power 4 or greater, you gain 2 life." ==
  none
#guard parseOracleParts (name := "")
  "Ferocious — At the beginning of combat on your turn, if you control a creature with power 4 or greater, put a +1/+1 counter on this creature." ==
  some [.ability (.triggered
    (.combatStart (.controller .this))
    (.if
      (.any (.intersection [
        .permanent, .cardType .creature, .controlled (.controller .this),
        .powerAtLeast (Value.int 4)]))
      [.putCounter (.source .this) .plusOnePlusOne 1]))]
#guard parseOracleParts (name := "")
  "At the beginning of combat on your turn, if you control a creature with power 4 or greater, put a +1/+1 counter on this creature." ==
  parseOracleParts (name := "")
    "Ferocious — At the beginning of combat on your turn, if you control a creature with power 4 or greater, put a +1/+1 counter on this creature."
#guard parseOracleParts (name := "")
  "Ferocious — At the beginning of combat on your turn, put a +1/+1 counter on this creature." ==
  none
#guard parseOracleParts (name := "")
  "Choose one —\n• Creatures you control get +2/+1 until end of turn.\n• Destroy target artifact or enchantment. You gain 2 life." ==
  some [.actions [.chooseMode [
    .continuous
      [.addPower
        (.intersection [
          .permanent, .cardType .creature, .controlled (.controller .this)])
        (Value.int 2),
       .addToughness
        (.intersection [
          .permanent, .cardType .creature, .controlled (.controller .this)])
        (Value.int 1)]
      .endOfTurn,
    .sequence [
      .destroy
        (.target 1
          (.intersection [
            .permanent,
            .union [.cardType .artifact, .cardType .enchantment]])),
      .gainLife (.controller .this) 2]]]]
#guard parseOracleParts (name := "")
  "Choose one —\n• Destroy target creature with power 4 or greater.\n• Until end of turn, target creature becomes an artifact in addition to its other types and gains indestructible. (Damage and effects that say \"destroy\" don't destroy it.)" ==
  some [.actions [.chooseMode [
    .destroy
      (.target 1
        (.intersection [
          .permanent, .cardType .creature, .powerAtLeast (Value.int 4)])),
    .continuous
      [.gainType
        (.target 2 (.intersection [.permanent, .cardType .creature]))
        .artifact,
       .gainAbility (.targetReference 2) (.keyword .indestructible)]
      .endOfTurn]]]
#guard parseOracleParts (name := "")
  "Until end of turn, target artifact becomes an artifact in addition to its other types and gains indestructible." ==
  none
#guard parseOracleParts (name := "") "This creature can't be blocked by tokens." ==
  some [.ability (.static (.forbid (.block .token .this)))]
#guard parseOracleParts (name := "Duskwatch Hunter")
  "Duskwatch Hunter can't be blocked by tokens." ==
  parseOracleParts (name := "") "This creature can't be blocked by tokens."
#guard parseOracleParts (name := "") "This creature can't be blocked by Goblins." == none
#guard parseOracleParts (name := "")
  "When this creature enters, put a +1/+1 counter on target creature." ==
  some [.ability (.triggered (.enter .this)
    (.putCounter
      (.target 1 (.intersection [.permanent, .cardType .creature]))
      .plusOnePlusOne
      1))]
#guard parseOracleParts (name := "")
  "When this creature enters, put a +1/+1 counter on target Elf." == none
#guard parseOracleParts (name := "")
  "When this creature enters, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)" ==
  some [.ability (.triggered (.enter .this) (.keyword (.controller .this) .recruit))]
#guard parseOracleParts (name := "Patient Instructor")
  "When Patient Instructor enters, recruit." ==
  parseOracleParts (name := "") "When this creature enters, recruit."
#guard parseOracleParts (name := "Gandalf") "When Patient Instructor enters, recruit." == none
#guard parseOracleParts (name := "")
  "Vigilance\nWhen this creature enters, recruit." ==
  some [
    .ability (.keyword .vigilance),
    .ability (.triggered (.enter .this) (.keyword (.controller .this) .recruit))]
#guard parseOracleParts (name := "")
  "Flying\nWhen this creature enters, recruit." ==
  some [
    .ability (.keyword .flying),
    .ability (.triggered (.enter .this) (.keyword (.controller .this) .recruit))]
#guard parseOracleParts (name := "")
  "When this creature dies, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)" ==
  some [.ability (.triggered (.die .this) (.keyword (.controller .this) .recruit))]
#guard parseOracleParts (name := "Lake-town Lookout")
  "When Lake-town Lookout dies, recruit." ==
  parseOracleParts (name := "") "When this creature dies, recruit."
#guard parseOracleParts (name := "Gandalf") "When Lake-town Lookout dies, recruit." == none
#guard parseOracleParts (name := "") "When this creature dies, draw a card." == none
#guard parseOracleParts (name := "") "When another creature dies, recruit." == none
#guard parseOracleParts (name := "")
  "When this artifact enters, scry 2. (Look at the top two cards of your library, then put any number of them on the bottom and the rest on top in any order.)" ==
  some [.ability (.triggered (.enter .this) (.scry (.controller .this) 2))]
#guard parseOracleParts (name := "") "When this creature enters, scry 0." == none
#guard parseOracleParts (name := "") "When this artifact enters, scry two." ==
  some [.ability (.triggered (.enter .this) (.scry (.controller .this) 2))]
#guard parseOracleParts (name := "")
  "{1}, {T}: Add one mana of any color." ==
  some [.ability (
    .activated
      [.mana [.generic 1], .tapSymbol]
      (.addManaOfOneColor (.controller .this) ManaSymbol.anyColor 1))]
#guard parseOracleParts (name := "") "Add one mana of any color." == none
#guard parseOracleParts (name := "") "{T}: Add one mana of any color." == none
#guard parseOracleParts (name := "Giant's Boulder")
  "{7}, {T}, Sacrifice this artifact: Destroy target permanent." ==
  some [.ability (
    .activated
      [.mana [.generic 7], .tapSymbol, .sacrifice .this]
      (.destroy (.target 1 .permanent)))]
#guard parseOracleParts (name := "Giant's Boulder")
  "{7}, {T}, Sacrifice Giant's Boulder: Destroy target permanent." ==
  parseOracleParts (name := "Giant's Boulder")
    "{7}, {T}, Sacrifice this artifact: Destroy target permanent."
#guard parseOracleParts (name := "") "Destroy target permanent." == none
#guard parseOracleParts (name := "")
  "When this creature enters, create a tapped Treasure token. (It's an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")" ==
  some [.ability (
    .triggered
      (.enter .this)
      (.createTokens (.controller .this) 1 PredefinedToken.treasureToken [.tapped]))]
#guard parseOracleParts (name := "Dori, Bearer of Friends")
  "When Dori enters, create a Treasure token." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.createTokens (.controller .this) 1 PredefinedToken.treasureToken))]
#guard parseOracleParts (name := "Gandalf")
  "When Dori enters, create a Treasure token." == none
#guard parseOracleParts (name := "")
  "When this creature enters, create two Treasure tokens." == none
#guard parseOracleParts (name := "")
  "When this creature enters, create a tapped Food token." == none
#guard parseOracleParts (name := "Esgaroth Garrison")
  "Esgaroth Garrison's power is equal to the number of creatures you control." ==
  some [.ability (
    .static
      (.setPower
        .this
        (.count
          (.intersection [
            .permanent,
            .cardType .creature,
            .controlled (.controller .this)]))))]
#guard parseOracleParts (name := "")
  "This creature's power is equal to the number of creatures you control." ==
  parseOracleParts (name := "Esgaroth Garrison")
    "Esgaroth Garrison's power is equal to the number of creatures you control."
#guard parseOracleParts (name := "Gandalf")
  "Esgaroth Garrison's power is equal to the number of creatures you control." == none
#guard parseOracleParts (name := "")
  "This creature's toughness is equal to the number of creatures you control." == none
#guard parseOracleParts (name := "")
  "When this creature enters, exile the top card of your library. Until the end of your next turn, you may play that card." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.sequence [
        .actionId 1 (.exile (.topOfLibrary (.controller .this))),
        .continuous
          [.canPlay (.controller .this) (.wasCreatedByAction 1)]
          (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])]))]
#guard parseOracleParts (name := "")
  "When this creature enters, exile the top card of your library." == none
#guard parseOracleParts (name := "")
  "When this creature enters, exile the top card of your library. You may play it until the end of your next turn." == none
#guard parseOracleParts (name := "") "This spell can't be countered." ==
  some [.ability (.stackStatic (.forbid (.counter .this)))]
#guard parseOracleParts (name := "")
  "This spell can't be countered. (It can't be countered.)" ==
  parseOracleParts (name := "") "This spell can't be countered."
#guard parseOracleParts (name := "") "This creature can't be countered." == none
#guard parseOracleParts (name := "") "Hexproof, haste" ==
  some [.ability (.keyword .hexproof), .ability (.keyword .haste)]
#guard parseOracleParts (name := "")
  "Whenever you cast a noncreature spell, amass Goblins 1. (Put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)" ==
  some [.ability (
    .triggered
      (.castSpell
        (.intersection [
          .spell,
          .not (.cardType .creature),
          .controlled (.controller .this)]))
      (.keyword (.controller .this) (.amass .goblin (.nat 1))))]
#guard parseOracleParts (name := "")
  "Whenever you cast a creature spell, amass Goblins 1." == none
#guard parseOracleParts (name := "") "Whenever you cast a noncreature spell, amass Goblin 1." == none
#guard parseOracleParts (name := "") "Whenever you cast a noncreature spell, amass Goblins 0." == none
#guard parseOracleParts (name := "")
  "When this creature enters, amass Goblins 1." ==
  some [.ability (
    .triggered
      (.enter .this)
      (.keyword (.controller .this) (.amass .goblin (.nat 1))))]
#guard parseOracleParts (name := "Goblin-town Flunkies")
  "When Goblin-town Flunkies enters, amass Goblins 1." ==
  parseOracleParts (name := "") "When this creature enters, amass Goblins 1."
#guard parseOracleParts (name := "Gandalf")
  "When Goblin-town Flunkies enters, amass Goblins 1." == none
#guard parseOracleParts (name := "")
  "When this creature dies, amass Goblins 4." ==
  some [.ability (
    .triggered
      (.die .this)
      (.keyword (.controller .this) (.amass .goblin (.nat 4))))]
#guard parseOracleParts (name := "")
  "Whenever you attack, amass Goblins 2." ==
  some [.ability (
    .triggered
      (.attackSimultaneously
        (.intersection [
          .permanent,
          .cardType .creature,
          .controlled (.controller .this)])
        .all
        [])
      (.keyword (.controller .this) (.amass .goblin (.nat 2))))]
#guard parseOracleParts (name := "")
  "Whenever you attack while you control a Goblin, amass Goblins 2." == none
#guard parseOracleParts (name := "")
  "You may cast this spell as though it had flash if you control a Human." ==
  some [.ability (.everywhereStatic (
    .canBeCastAsThoughWithFlashIf
      .this
      (.any (.intersection [
        .permanent, .subtype .human, .controlled .caster]))))]
#guard parseOracleParts (name := "")
  "You may cast this spell as though it had flash if you control Human." == none
#guard parseOracleParts (name := "")
  "You may cast this spell as though it had flash if you control an Elf." ==
  some [.ability (.everywhereStatic (
    .canBeCastAsThoughWithFlashIf
      .this
      (.any (.intersection [
        .permanent, .subtype .elf, .controlled .caster]))))]
#guard parseOracleParts (name := "") "Other creatures you control get +1/+1." ==
  some [
    .ability (.static (.addPower
      (.intersection [
        .not .this,
        .permanent,
        .cardType .creature,
        .controlled (.controller .this)]) (Value.int 1))),
    .ability (.static (.addToughness
      (.intersection [
        .not .this,
        .permanent,
        .cardType .creature,
        .controlled (.controller .this)]) (Value.int 1)))]
#guard parseOracleParts (name := "") "Other creatures you control get +0/+0." == none
#guard parseOracleParts (name := "")
  "Other creatures you control get +1/+1 until end of turn." == none
#guard parseOracleParts (name := "")
  "Whenever this creature enters or attacks, recruit." ==
  some [.ability (
    .triggered
      (.or (.enter .this) (.attack .this .all))
      (.keyword (.controller .this) .recruit))]
#guard parseOracleParts (name := "Bard's Company")
  "Whenever Bard's Company enters or attacks, recruit." ==
  parseOracleParts (name := "") "Whenever this creature enters or attacks, recruit."
#guard parseOracleParts (name := "Gandalf")
  "Whenever Bard's Company enters or attacks, recruit." == none
#guard parseOracleParts (name := "")
  "Whenever this creature enters or attacks, draw a card." == none
#guard parseOracleParts (name := "") "You draw a card and lose 1 life." ==
  some [.actions [
    .sequence [
      .draw (.controller .this) 1,
      .loseLife (.controller .this) 1]]]
#guard parseOracleParts (name := "") "You draw two cards and lose 1 life." == none
#guard parseOracleParts (name := "") "You draw a card and lose 2 life." == none
#guard parseOracleParts (name := "") "Amass Goblins 2." ==
  some [.actions [.keyword (.controller .this) (.amass .goblin (.nat 2))]]
#guard parseOracleParts (name := "")
  "Amass Goblins 2. (Put two +1/+1 counters on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)" ==
  parseOracleParts (name := "") "Amass Goblins 2."
#guard parseOracleParts (name := "") "Amass Goblin 2." == none
#guard parseOracleParts (name := "") "Amass Goblins 0." == none
#guard parseOracleParts (name := "")
  "You draw a card and lose 1 life.\nAmass Goblins 2." ==
  some [.actions [
    .draw (.controller .this) 1,
    .loseLife (.controller .this) 1,
    .keyword (.controller .this) (.amass .goblin (.nat 2))]]
#guard parseOracleParts (name := "")
  "Return up to one target creature card from your graveyard to your hand." ==
  some [.actions [
    .returnToHand
      (.targets 1 (.range 0 1)
        (.intersection [
          .inGraveyard,
          .cardType .creature,
          .owner (.controller .this)]))]]
#guard parseOracleParts (name := "")
  "Return up to one target creature from your graveyard to your hand." == none
#guard parseOracleParts (name := "")
  "Return target creature card from your graveyard to your hand." == none
#guard parseOracleParts (name := "")
  "Return up to one target creature card from your graveyard to your hand.\nAmass Goblins 3." ==
  some [.actions [
    .returnToHand
      (.targets 1 (.range 0 1)
        (.intersection [
          .inGraveyard,
          .cardType .creature,
          .owner (.controller .this)])),
    .keyword (.controller .this) (.amass .goblin (.nat 3))]]
#guard parseOracleParts (name := "")
  "Counter target spell. If that spell's mana value was 2 or less, recruit." ==
  some [.actions [
    .defineValueVariable 1 (.greatestManaValue (.target 1 .spell)),
    .counter (.targetReference 1),
    .if (.lessOrEqual (.variable 1) 2)
      [.keyword (.controller .this) .recruit]]]
#guard parseOracleParts (name := "")
  "Counter target spell. If that spell's mana value was 2 or less, recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)" ==
  parseOracleParts (name := "")
    "Counter target spell. If that spell's mana value was 2 or less, recruit."
#guard parseOracleParts (name := "")
  "Counter target spell. If that spell's mana value was 2 or less, draw a card." == none
#guard parseOracleParts (name := "")
  "Counter target spell. If that spell's mana value was 0 or less, recruit." == none
#guard parseOracleParts (name := "")
  "Counter target creature. If that spell's mana value was 2 or less, recruit." == none

end Mtg.Engine
