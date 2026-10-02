import Mtg.Engine.Mana
import Mtg.Engine.TypeLine
import Mtg.Engine.Card.Keywords
import Mtg.Engine.Card.Text
import Mtg.Engine.Card.CardDef
import Mtg.Engine.Card.SpellEffects

/-!
# Traditional card DSL

A list-shaped definition language for a traditional Magic card: one face,
plus an optional Adventure. `TraditionalCardDefinition.card` is the clause
list. `toCardDef` compiles it into the engine's `CardDef`. Activated
abilities are a `.costFor` instruction in `.textBox`. `parseOracleText`
reads a printed card (name, mana cost, type line, power/toughness, rules
text, and an Adventure face) back into that clause list.
-/

namespace Mtg.Engine

/-- `Color` is compared by its `DecidableEq` instance. -/
instance : BEq Color where
  beq a b := decide (a = b)

/-- A mana symbol in a DSL cost. `.mono` is one colored mana; `.generic` is
`{n}`. -/
inductive CostSymbol where
  | generic (n : Nat)
  | mono (c : Color)
  | colorless
  | hybrid (a b : Color)
  | x
  deriving Repr, BEq

namespace CostSymbol

def toManaSymbol : CostSymbol → ManaSymbol
  | .generic n => .generic n
  | .mono c => .colored c
  | .colorless => .colorless
  | .hybrid a b => .hybrid a b
  | .x => .x

def toManaCost (ms : List CostSymbol) : ManaCost :=
  { symbols := ms.toArray.map toManaSymbol }

end CostSymbol

/-- A subtype written `.subtype .dwarf`. Add a constructor here to name
another subtype in the DSL. -/
inductive CardSubtype where
  | dwarf
  | citizen
  | scout
  | adventure
  deriving Repr, BEq, DecidableEq

namespace CardSubtype

def printed : CardSubtype → String
  | .dwarf => "Dwarf"
  | .citizen => "Citizen"
  | .scout => "Scout"
  | .adventure => "Adventure"

end CardSubtype

/-- One printed keyword, in the vocabulary `Keywords` already models. -/
inductive PrintedKeyword where
  | flash
  | haste
  | vigilance
  | flying
  | cantBeBlocked
  | menace
  | hexproof
  | indestructible
  | reach
  | trample
  | deathtouch
  | defender
  | lifelink
  | firstStrike
  | islandwalk
  | storied
  | doubleStrike
  | prowess
  | ascend
  | shadow
  | changeling
  deriving Repr, BEq, DecidableEq

namespace PrintedKeyword

def toKeywords : PrintedKeyword → Keywords
  | .flash => Keyword.flash
  | .haste => Keyword.haste
  | .vigilance => Keyword.vigilance
  | .flying => Keyword.flying
  | .cantBeBlocked => Keyword.cantBeBlocked
  | .menace => Keyword.menace
  | .hexproof => Keyword.hexproof
  | .indestructible => Keyword.indestructible
  | .reach => Keyword.reach
  | .trample => Keyword.trample
  | .deathtouch => Keyword.deathtouch
  | .defender => Keyword.defender
  | .lifelink => Keyword.lifelink
  | .firstStrike => Keyword.firstStrike
  | .islandwalk => Keyword.islandwalk
  | .storied => Keyword.storied
  | .doubleStrike => Keyword.doubleStrike
  | .prowess => Keyword.prowess
  | .ascend => Keyword.ascend
  | .shadow => Keyword.shadow
  | .changeling => Keyword.changeling

/-- Lowercase Oracle name, matching `Keywords.toList`. -/
def oracleName : PrintedKeyword → String
  | .flash => "flash"
  | .haste => "haste"
  | .vigilance => "vigilance"
  | .flying => "flying"
  | .cantBeBlocked => "can't be blocked"
  | .menace => "menace"
  | .hexproof => "hexproof"
  | .indestructible => "indestructible"
  | .reach => "reach"
  | .trample => "trample"
  | .deathtouch => "deathtouch"
  | .defender => "defender"
  | .lifelink => "lifelink"
  | .firstStrike => "first strike"
  | .islandwalk => "islandwalk"
  | .storied => "storied"
  | .doubleStrike => "double strike"
  | .prowess => "prowess"
  | .ascend => "ascend"
  | .shadow => "shadow"
  | .changeling => "changeling"

def all : List PrintedKeyword :=
  [.flash, .haste, .vigilance, .flying, .cantBeBlocked, .menace, .hexproof,
   .indestructible, .reach, .trample, .deathtouch, .defender, .lifelink,
   .firstStrike, .islandwalk, .storied, .doubleStrike, .prowess, .ascend,
   .shadow, .changeling]

def parse (s : String) : Option PrintedKeyword :=
  let s := s.trimAscii.copy.map Char.toLower
  all.find? (fun k => k.oracleName == s)

end PrintedKeyword

/-- An ability of the card itself, as opposed to a spell effect in the text box. -/
inductive CardAbility where
  | keyword (k : PrintedKeyword)
  deriving Repr, BEq

/-- Whose control a target predicate talks about. -/
inductive PlayerRef where
  | you
  | opponent
  deriving Repr, BEq

/-- A predicate inside `.target`, `.getUntil`, or `.or`. A list of these is
a conjunction. -/
inductive ObjectQualifier where
  | cardType (t : CardType)
  | controlledBy (p : PlayerRef)
  | or (qs : List ObjectQualifier)
  deriving Repr, BEq

namespace ObjectQualifier

/-- `.creature` in a qualifier list. -/
def creature : ObjectQualifier := .cardType .creature

end ObjectQualifier

/-- One instance of the word “target”. -/
inductive TargetExpr where
  | target (qs : List ObjectQualifier)
  deriving Repr, BEq

/-- A keyword the text box grants. -/
inductive GrantedAbility where
  | keyword (k : PrintedKeyword)
  deriving Repr, BEq

/-- How long a text-box effect lasts. -/
inductive Duration where
  | endOfTurn
  deriving Repr, BEq

/-- A printed power and toughness change. `.plusPowerToughness +1 +1` is `+1/+1`. -/
inductive StatMod where
  | plusPowerToughness (power toughness : Int)
  deriving Repr, BEq

/-- `+n` in `.plusPowerToughness +1 +1` is the positive integer `n`.
Ordinary constructor application (`.plusPowerToughness p t`) still works. -/
syntax plusBonus := "+" num
scoped syntax ".plusPowerToughness" (plusBonus <|> term:max) (plusBonus <|> term:max) : term
macro_rules
  | `(.plusPowerToughness +$p:num +$t:num) => `(StatMod.plusPowerToughness $p $t)
  | `(.plusPowerToughness $p:term $t:term) => `(StatMod.plusPowerToughness $p $t)

/-- One cost of an activated ability written in `.costFor`. -/
inductive PrintedCost where
  | mana (ms : List CostSymbol)
  deriving Repr, BEq

/-- One instruction in a `.textBox`. -/
inductive TextEffect where
  | gainUntil (targets : List TargetExpr) (gains : List GrantedAbility) (dur : Duration)
  /-- Matching objects get these changes until `dur`. -/
  | getUntil (qs : List ObjectQualifier) (mods : List StatMod) (dur : Duration)
  /-- An activated ability: pay `costs`, then follow `effects` (`{3}{W}: …`). -/
  | costFor (costs : List PrintedCost) (effects : List TextEffect)
  deriving Repr, BEq

/-- One clause in `.card` or `.alternative`. -/
inductive CardClause where
  | name (s : String)
  | manaCost (ms : List CostSymbol)
  | type (t : CardType)
  | supertype (s : Supertype)
  | subtype (s : CardSubtype)
  | power (n : Int)
  | toughness (n : Int)
  | ability (a : CardAbility)
  | textBox (effects : List TextEffect)
  | alternative (clauses : List CardClause)
  deriving Repr, BEq

/-- A traditional card, written `.card [ clauses ]`. -/
inductive TraditionalCardDefinition where
  | card (clauses : List CardClause)
  deriving Repr, BEq

/-! Interpretation into `CardDef`. -/

private structure FaceBuild where
  name : String := ""
  manaCost : List CostSymbol := []
  types : List CardType := []
  supertypes : List Supertype := []
  subtypes : List CardSubtype := []
  power : Option Int := none
  toughness : Option Int := none
  abilities : List CardAbility := []
  textBox : List TextEffect := []

private def FaceBuild.add (f : FaceBuild) : CardClause → FaceBuild
  | .name s => { f with name := s }
  | .manaCost m => { f with manaCost := m }
  | .type t => { f with types := f.types ++ [t] }
  | .supertype s => { f with supertypes := f.supertypes ++ [s] }
  | .subtype s => { f with subtypes := f.subtypes ++ [s] }
  | .power n => { f with power := some n }
  | .toughness n => { f with toughness := some n }
  | .ability a => { f with abilities := f.abilities ++ [a] }
  | .textBox es => { f with textBox := f.textBox ++ es }
  | .alternative _ => f

private def foldFace (clauses : List CardClause) : FaceBuild :=
  clauses.foldl FaceBuild.add {}

private def lastAlternative (clauses : List CardClause) : Option (List CardClause) :=
  clauses.foldl (fun acc c =>
    match c with
    | .alternative inner => some inner
    | _ => acc) none

private def keywordsOfAbilities (abilities : List CardAbility) : Keywords :=
  abilities.foldl (fun acc a =>
    match a with
    | .keyword k => acc.merge k.toKeywords) Keywords.none

private def keywordsOfGranted (gs : List GrantedAbility) : Keywords :=
  gs.foldl (fun acc g =>
    match g with
    | .keyword k => acc.merge k.toKeywords) Keywords.none

private def cardTypeNoun (t : CardType) : String :=
  t.englishName.map Char.toLower

private def ObjectQualifier.toPhrase : ObjectQualifier → String
  | .cardType t => cardTypeNoun t
  | .controlledBy .you => "you control"
  | .controlledBy .opponent => "an opponent controls"
  | .or qs => orJoin (qs.map toPhrase)

private def qualifiersPhrase (qs : List ObjectQualifier) : String :=
  String.intercalate " " (qs.map ObjectQualifier.toPhrase)

private def TargetExpr.toPhrase : TargetExpr → String
  | .target qs => s!"target {qualifiersPhrase qs}"

private def joinTargets (ts : List String) : String :=
  match ts with
  | [] => "target permanent"
  | [a] => a
  | [a, b] => s!"{a} and {b}"
  | many => String.intercalate ", " many

private def durationPhrase : Duration → String
  | .endOfTurn => "until end of turn"

private def pluralQualifier : ObjectQualifier → String
  | .cardType t =>
    let n := cardTypeNoun t
    if n.endsWith "s" then n else s!"{n}s"
  | .controlledBy .you => "you control"
  | .controlledBy .opponent => "an opponent controls"
  | .or qs => orJoin (qs.map pluralQualifier)

private def statModPhrase : StatMod → String
  | .plusPowerToughness p t => s!"{signedStat p}/{signedStat t}"

private def printedCostPhrase : PrintedCost → String
  | .mana ms => (CostSymbol.toManaCost ms).toNotation

private def gainUntilSentence (targets : List TargetExpr) (gains : List GrantedAbility)
    (dur : Duration) : String :=
  let subject := capitalizeAscii (joinTargets (targets.map TargetExpr.toPhrase))
  let kws := (keywordsOfGranted gains).joinedAnd
  s!"{subject} gains {kws} {durationPhrase dur}."

private def getUntilSentence (qs : List ObjectQualifier) (mods : List StatMod)
    (dur : Duration) : String :=
  let subject := capitalizeAscii (String.intercalate " " (qs.map pluralQualifier))
  let bonus := String.intercalate " and " (mods.map statModPhrase)
  s!"{subject} get {bonus} {durationPhrase dur}."

/-- A text-box effect nested under `.costFor`, printed without a further cost. -/
private def nestedEffectSentence : TextEffect → Option String
  | .gainUntil targets gains dur => some (gainUntilSentence targets gains dur)
  | .getUntil qs mods dur => some (getUntilSentence qs mods dur)
  | .costFor _ _ => none

/-- Oracle sentence for a text-box effect, without reminder text. -/
private def textEffectSentence : TextEffect → String
  | .gainUntil targets gains dur => gainUntilSentence targets gains dur
  | .getUntil qs mods dur => getUntilSentence qs mods dur
  | .costFor costs effects =>
    let cost := String.intercalate ", " (costs.map printedCostPhrase)
    let body := String.intercalate " " (effects.filterMap nestedEffectSentence)
    s!"{cost}: {body}"

/-- Map a spell text-box effect onto the engine's `Effect` vocabulary. -/
private def textEffectToEffect : TextEffect → Option Effect
  | .gainUntil
      [.target [.or [.cardType .artifact, .cardType .creature], .controlledBy .you]]
      [.keyword .hexproof, .keyword .indestructible]
      .endOfTurn =>
    some Effect.grantHexproofIndestructible
  | _ => none

private def creaturesYouControl (qs : List ObjectQualifier) : Bool :=
  qs == [.cardType .creature, .controlledBy .you]

private def pumpEffect : TextEffect → Option Effect
  | .getUntil qs [.plusPowerToughness p t] .endOfTurn =>
    if creaturesYouControl qs then some (Effect.abilityCreaturesYouControlGet p t) else none
  | _ => none

private def costsToActivation (costs : List PrintedCost) : ActivationCost :=
  costs.foldl (fun acc c =>
    match c with
    | .mana ms =>
      { acc with
        mana := { symbols := acc.mana.symbols ++ (CostSymbol.toManaCost ms).symbols } })
    {}

/-- Map `.costFor` onto a non-mana activated ability. -/
private def textEffectToActivated : TextEffect → Option ActivatedAbility
  | .costFor costs effects =>
    match effects.filterMap pumpEffect with
    | effect :: _ => some { cost := costsToActivation costs, effect }
    | [] => none
  | _ => none

private def adventureReminder : String :=
  "(Then exile this card. You may cast the creature later from exile.)"

private def keywordLine (k : Keywords) : Option String :=
  let s := toString k
  if s.isEmpty then none else some (capitalizeAscii s)

private def headerLines (f : FaceBuild) : List String :=
  let cost := (CostSymbol.toManaCost f.manaCost).toNotation
  let nameLine := if cost.isEmpty then f.name else s!"{f.name} {cost}"
  let typeLine :=
    formatTypeLine f.supertypes.toArray f.types.toArray
      (f.subtypes.toArray.map CardSubtype.printed)
  [nameLine, typeLine]

private def effectLines (f : FaceBuild) : List String :=
  let lines := f.textBox.map textEffectSentence
  let remind := f.subtypes.any (· == .adventure)
  match lines.dropLast, lines.getLast? with
  | _, none => []
  | init, some last =>
    let last := if remind then s!"{last} {adventureReminder}" else last
    init ++ [last]

/-- Rules text stored on the creature face, including the `//ADV//` block. -/
private def rulesOracle (main : FaceBuild) (alt : Option FaceBuild) : String :=
  let kw :=
    match keywordLine (keywordsOfAbilities main.abilities) with
    | some s => [s]
    | none => []
  let adv :=
    match alt with
    | none => []
    | some a => ["//ADV//"] ++ headerLines a ++ effectLines a
  String.intercalate "\n" (kw ++ main.textBox.map textEffectSentence ++ adv)

private def FaceBuild.toAdventure (f : FaceBuild) : AdventureFace :=
  { name := f.name
    manaCost := CostSymbol.toManaCost f.manaCost
    types := if f.types.isEmpty then #[.sorcery] else f.types.toArray
    subtypes :=
      if f.subtypes.isEmpty then #["Adventure"]
      else f.subtypes.toArray.map CardSubtype.printed
    oracleText := String.intercalate "\n" (effectLines f)
    spellEffect := (f.textBox.filterMap textEffectToEffect).head? }

private def FaceBuild.toCard (f : FaceBuild) (oracleText : String)
    (adventure : Option AdventureFace) : CardDef :=
  { name := f.name
    manaCost := CostSymbol.toManaCost f.manaCost
    types := f.types.toArray
    subtypes := f.subtypes.toArray.map CardSubtype.printed
    supertypes := f.supertypes.toArray
    oracleText
    power := f.power
    toughness := f.toughness
    keywords := keywordsOfAbilities f.abilities
    spellEffect := (f.textBox.filterMap textEffectToEffect).head?
    activatedAbilities := (f.textBox.filterMap textEffectToActivated).toArray
    adventure }

/-- Compiled engine card. Adventure rules text keeps the CR 715 reminder. -/
def TraditionalCardDefinition.toCardDef : TraditionalCardDefinition → CardDef
  | .card clauses =>
    let main := foldFace clauses
    let alt := (lastAlternative clauses).map foldFace
    main.toCard (rulesOracle main alt) (alt.map FaceBuild.toAdventure)

instance : Coe TraditionalCardDefinition CardDef where
  coe := TraditionalCardDefinition.toCardDef

/-- Append DSL cards to engine cards. `++` fixes its argument types before
element coercions run, so this instance compiles the left-hand array. -/
instance : HAppend (Array TraditionalCardDefinition) (Array CardDef) (Array CardDef) where
  hAppend as bs := as.map (·.toCardDef) ++ bs

def TraditionalCardDefinition.oracleText (c : TraditionalCardDefinition) : String :=
  c.toCardDef.oracleText

def TraditionalCardDefinition.colors (c : TraditionalCardDefinition) : ColorSet :=
  c.toCardDef.colors

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
  | "adventure" => some .adventure
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

private def parseDisjunction (s : String) : Option (List ObjectQualifier) := do
  let parts := s.splitOn " or " |>.map (·.trimAscii.copy) |>.filter (· != "")
  match parts with
  | [] => none
  | [one] =>
    let t ← parseCardType one
    return [.cardType t]
  | many =>
    let ts ← many.mapM parseCardType
    return [.or (ts.map ObjectQualifier.cardType)]

private def parseNoun (noun : String) : Option (List ObjectQualifier) := do
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
    | some p => [ObjectQualifier.controlledBy p]
    | none => []
  return quals ++ tail

private def parseDuration (s : String) : Option Duration :=
  match s.trimAscii.copy.map Char.toLower with
  | "end of turn" => some .endOfTurn
  | _ => none

private def singularize (s : String) : String :=
  let s := s.trimAscii.copy.map Char.toLower
  if s.endsWith "s" && s.length > 1 then (s.dropEnd 1).copy else s

private def parsePluralDisjunction (s : String) : Option (List ObjectQualifier) := do
  let parts := s.splitOn " or " |>.map (·.trimAscii.copy) |>.filter (· != "")
  match parts with
  | [] => none
  | [one] =>
    let t ← parseCardType (singularize one)
    return [.cardType t]
  | many =>
    let ts ← many.mapM (fun w => parseCardType (singularize w))
    return [.or (ts.map ObjectQualifier.cardType)]

private def parseGetSubject (noun : String) : Option (List ObjectQualifier) := do
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
    | some p => [ObjectQualifier.controlledBy p]
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

private def parseKeywordLine (line : String) : Option (List CardAbility) := do
  let parts := splitEnglishList line
  if parts.isEmpty then none
  else
    let kws ← parts.mapM PrintedKeyword.parse
    return kws.map CardAbility.keyword

private def parseBody (lines : List String) :
    Option (List CardAbility × List TextEffect) :=
  lines.foldlM (fun acc line =>
    let (abilities, effects) := acc
    let cleaned := stripTrailingDot (stripParens line)
    if cleaned.isEmpty then
      pure acc
    else
      match parseCostFor cleaned with
      | some e => pure (abilities, effects ++ [e])
      | none =>
        match parseGetUntil cleaned with
        | some e => pure (abilities, effects ++ [e])
        | none =>
          match parseGainUntil cleaned with
          | some e => pure (abilities, effects ++ [e])
          | none =>
            match parseKeywordLine cleaned with
            | some ks => pure (abilities ++ ks, effects)
            | none => none) ([], [])

private def faceClauses (name : String) (cost : List CostSymbol)
    (supers : List Supertype) (tys : List CardType) (subs : List CardSubtype)
    (pt : Option (Int × Int)) (abilities : List CardAbility)
    (effects : List TextEffect) : List CardClause :=
  [.name name, .manaCost cost]
    ++ tys.map CardClause.type
    ++ supers.map CardClause.supertype
    ++ subs.map CardClause.subtype
    ++ (match pt with
        | some (p, t) => [CardClause.power p, .toughness t]
        | none => [])
    ++ abilities.map CardClause.ability
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
    let (abilities, effects) ← parseBody body
    return faceClauses name cost supers tys subs pt abilities effects
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
power, toughness, abilities, text box, alternative) so it can be compared to
a definition written in that order.
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

/-! Parser pieces used by the Bofur guard. -/

#guard PrintedKeyword.all.all (fun k => PrintedKeyword.parse k.oracleName == some k)
#guard parseManaRun "{1}{W}" == some [.generic 1, .mono .white]
#guard parseManaRun "{W}" == some [.mono .white]
#guard textEffectSentence (.gainUntil
    [.target [.or [.cardType .artifact, .cardType .creature], .controlledBy .you]]
    [.keyword .hexproof, .keyword .indestructible]
    .endOfTurn) ==
  "Target artifact or creature you control gains hexproof and indestructible until end of turn."
#guard parseGainUntil
    "Target artifact or creature you control gains hexproof and indestructible until end of turn. (Then exile this card. You may cast the creature later from exile.)" ==
  some (.gainUntil
    [.target [.or [.cardType .artifact, .cardType .creature], .controlledBy .you]]
    [.keyword .hexproof, .keyword .indestructible]
    .endOfTurn)
#guard (.plusPowerToughness +1 +1 : StatMod) == .plusPowerToughness 1 1
#guard textEffectSentence (.costFor
    [.mana [.generic 3, .mono .white]]
    [.getUntil [.creature, .controlledBy .you]
      [.plusPowerToughness +1 +1] .endOfTurn]) ==
  "{3}{W}: Creatures you control get +1/+1 until end of turn."
#guard parseCostFor
    "{3}{W}: Creatures you control get +1/+1 until end of turn." ==
  some (.costFor
    [.mana [.generic 3, .mono .white]]
    [.getUntil [.cardType .creature, .controlledBy .you]
      [.plusPowerToughness 1 1] .endOfTurn])

end Mtg.Engine
