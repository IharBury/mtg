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
list. `toCardDef` compiles it into the engine's `CardDef`. Printed
keywords are a `.keyword` instruction in `.textBox`, activated
abilities are a `.costFor` instruction in `.textBox`, tapping spells
are a `.tap` instruction in `.textBox`, cost reductions are a
`.costLessToCastIf` instruction in `.textBox`, damage is a
`.dealDamage` instruction in `.textBox`, triggered abilities are a
`.whenever` instruction in `.textBox`, and a spell that resolves as
several sentences is a `.sequence` in `.textBox`. `parseOracleText` reads a
printed card (name, mana cost, type line, power/toughness, rules text,
and an Adventure face) back into that clause list.
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
  | insect
  | adventure
  | bird
  | soldier
  deriving Repr, BEq, DecidableEq

namespace CardSubtype

def printed : CardSubtype → String
  | .dwarf => "Dwarf"
  | .citizen => "Citizen"
  | .scout => "Scout"
  | .insect => "Insect"
  | .adventure => "Adventure"
  | .bird => "Bird"
  | .soldier => "Soldier"

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

/-- Whose control a target predicate talks about. -/
inductive PlayerRef where
  | you
  | opponent
  deriving Repr, BEq

/-- A type word in `.cardType`. Card types (`.creature`) and the subtypes this
DSL names (`.dwarf`, `.equipment`) share the constructor, so
`.cardType .creature` and `.cardType .dwarf` both elaborate. -/
inductive TypeName where
  | artifact
  | battle
  | creature
  | enchantment
  | instant
  | land
  | planeswalker
  | sorcery
  | kindred
  | dungeon
  | plane
  | phenomenon
  | vanguard
  | scheme
  | conspiracy
  | dwarf
  | equipment
  deriving Repr, BEq, DecidableEq

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

def toCard? : TypeName → Option CardType
  | .artifact => some .artifact
  | .battle => some .battle
  | .creature => some .creature
  | .enchantment => some .enchantment
  | .instant => some .instant
  | .land => some .land
  | .planeswalker => some .planeswalker
  | .sorcery => some .sorcery
  | .kindred => some .kindred
  | .dungeon => some .dungeon
  | .plane => some .plane
  | .phenomenon => some .phenomenon
  | .vanguard => some .vanguard
  | .scheme => some .scheme
  | .conspiracy => some .conspiracy
  | .dwarf => none
  | .equipment => none

/-- Printed word. Card types stay lowercase (`creature`); subtypes keep Oracle
capitalization (`Dwarf`, `Equipment`). -/
def phrase : TypeName → String
  | .dwarf => "Dwarf"
  | .equipment => "Equipment"
  | t =>
    match t.toCard? with
    | some c => c.englishName.map Char.toLower
    | none => ""

end TypeName

/-- A predicate inside `.target`, `.getUntil`, `.or`, or `.attack`. A list of
these is a conjunction. `.this` is this object; `.other` excludes it.
`.it` is the object named earlier (`It gets +2/+2`). -/
inductive ObjectQualifier where
  | cardType (t : TypeName)
  | controlledBy (p : PlayerRef)
  | or (qs : List ObjectQualifier)
  | tapped
  | this
  | other
  | it
  deriving Repr, BEq

namespace ObjectQualifier

/-- `.creature` in a qualifier list. -/
def creature : ObjectQualifier := .cardType .creature

end ObjectQualifier

/-- How many objects one targeting phrase names. `.or 1 2` is “one or two”. -/
inductive TargetCount where
  | or (lo hi : Nat)
  deriving Repr, BEq

/-- One instance of the word “target”. `.targets (.or 1 2) [.cardType .creature]`
is “one or two target creatures”. -/
inductive TargetExpr where
  | target (qs : List ObjectQualifier)
  | targets (count : TargetCount) (qs : List ObjectQualifier)
  deriving Repr, BEq

/-- A keyword the text box grants. -/
inductive GrantedAbility where
  | keyword (k : PrintedKeyword)
  deriving Repr, BEq

/-- How long a text-box effect lasts. -/
inductive Duration where
  | endOfTurn
  deriving Repr, BEq

/-- One event in `.whenever`. `[.attack [.this, .cardType .creature] []]` is
“this creature attacks”. The second list is a further restriction on that
attack; empty means any attack. -/
inductive TriggerExpr where
  | attack (who : List ObjectQualifier) (restrictions : List ObjectQualifier)
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

/-- A word of the subject a cost reduction describes.
`[.this, .spell]` is “this spell”. -/
inductive CostSubject where
  | this
  | spell
  deriving Repr, BEq

/-- The object a casting condition names. `.it` is the spell’s target. -/
inductive ConditionRef where
  | it
  deriving Repr, BEq

/-- When a cost reduction applies.
`.targeting .it [.tapped, .cardType .creature]` is “if it targets a tapped creature”. -/
inductive CastIf where
  | targeting (obj : ConditionRef) (qs : List ObjectQualifier)
  deriving Repr, BEq

/-- Who deals damage. `.thisCardName` prints the card’s name. -/
inductive DamageSubject where
  | thisCardName
  deriving Repr, BEq

/-- An object named without the word “target”.
`.oneOf [.cardType .equipment, .controlledBy .you]` is “an Equipment you control”.
`.it` is the object named earlier. -/
inductive ObjectExpr where
  | oneOf (qs : List ObjectQualifier)
  | it
  deriving Repr, BEq

/-- A condition in `.if`. `[.is [.it] [.cardType .dwarf]]` is “it's a Dwarf”. -/
inductive TextCondition where
  | is (subj : List ConditionRef) (qs : List ObjectQualifier)
  deriving Repr, BEq

/-- One instruction in a `.textBox`. -/
inductive TextEffect where
  /-- A printed keyword ability of this face (`Lifelink`). -/
  | keyword (k : PrintedKeyword)
  | gainUntil (targets : List TargetExpr) (gains : List GrantedAbility) (dur : Duration)
  /-- Matching objects get these changes until `dur`.
  `[.it]` is the object named earlier (`It gets +2/+2`). -/
  | getUntil (qs : List ObjectQualifier) (mods : List StatMod) (dur : Duration)
  /-- An activated ability: pay `costs`, then follow `effects` (`{3}{W}: …`). -/
  | costFor (costs : List PrintedCost) (effects : List TextEffect)
  /-- Tap the named targets (`Tap one or two target creatures`). -/
  | tap (targets : List TargetExpr)
  /-- These words cost `discount` less to cast when `cond` holds.
  `[.this, .spell]` is “This spell costs …”. -/
  | costLessToCastIf (subjects : List CostSubject) (discount : List CostSymbol) (cond : CastIf)
  /-- `subjects` deal `n` damage to `targets`. -/
  | dealDamage (subjects : List DamageSubject) (n : Nat) (targets : List TargetExpr)
  /-- When `events` happen, follow `effects`.
  `[.attack [.this, .cardType .creature] []]` is “this creature attacks”. -/
  | whenever (events : List TriggerExpr) (effects : List TextEffect)
  /-- `who` gets `mods` until `dur` for each object matching `each`.
  `[.it]` is “it”. `[.other, .cardType .creature, .controlledBy .you]` is
  “each other creature you control”. -/
  | getForEachUntil (who : List ConditionRef) (mods : List StatMod)
      (each : List ObjectQualifier) (dur : Duration)
  /-- Do these effects in order, printed as one paragraph. -/
  | sequence (effects : List TextEffect)
  /-- Untap the named targets (`Untap target creature you control`). -/
  | untap (targets : List TargetExpr)
  /-- When `conds` hold, follow `effects`.
  `[.is [.it] [.cardType .dwarf]]` is “if it's a Dwarf”. -/
  | «if» (conds : List TextCondition) (effects : List TextEffect)
  /-- `who` may do `effects` (`you may …`). -/
  | may (who : List PlayerRef) (effects : List TextEffect)
  /-- Attach `what` to `dest`. -/
  | attachTo (what dest : List ObjectExpr)
  deriving Repr, BEq

/-- `getForEachUntil [.it] mods each dur` is “it gets … until … for each …”.
Written without a leading dot so it can sit in a `.whenever` effect list. -/
def getForEachUntil (who : List ConditionRef) (mods : List StatMod)
    (each : List ObjectQualifier) (dur : Duration) : TextEffect :=
  TextEffect.getForEachUntil who mods each dur

/-- One clause in `.card` or `.alternative`. -/
inductive CardClause where
  | name (s : String)
  | manaCost (ms : List CostSymbol)
  | type (t : CardType)
  | supertype (s : Supertype)
  | subtype (s : CardSubtype)
  | power (n : Int)
  | toughness (n : Int)
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
  textBox : List TextEffect := []

private def FaceBuild.add (f : FaceBuild) : CardClause → FaceBuild
  | .name s => { f with name := s }
  | .manaCost m => { f with manaCost := m }
  | .type t => { f with types := f.types ++ [t] }
  | .supertype s => { f with supertypes := f.supertypes ++ [s] }
  | .subtype s => { f with subtypes := f.subtypes ++ [s] }
  | .power n => { f with power := some n }
  | .toughness n => { f with toughness := some n }
  | .textBox es => { f with textBox := f.textBox ++ es }
  | .alternative _ => f

private def foldFace (clauses : List CardClause) : FaceBuild :=
  clauses.foldl FaceBuild.add {}

private def lastAlternative (clauses : List CardClause) : Option (List CardClause) :=
  clauses.foldl (fun acc c =>
    match c with
    | .alternative inner => some inner
    | _ => acc) none

/-- Keyword abilities printed on this face. -/
private def keywordsOfText (es : List TextEffect) : Keywords :=
  es.foldl (fun acc e =>
    match e with
    | .keyword k => acc.merge k.toKeywords
    | _ => acc) Keywords.none

private def keywordsOfGranted (gs : List GrantedAbility) : Keywords :=
  gs.foldl (fun acc g =>
    match g with
    | .keyword k => acc.merge k.toKeywords) Keywords.none

private def ObjectQualifier.toPhrase : ObjectQualifier → String
  | .cardType t => t.phrase
  | .controlledBy .you => "you control"
  | .controlledBy .opponent => "an opponent controls"
  | .or qs => orJoin (qs.map toPhrase)
  | .tapped => "tapped"
  | .this => "this"
  | .other => "other"
  | .it => "it"

private def qualifiersPhrase (qs : List ObjectQualifier) : String :=
  String.intercalate " " (qs.map ObjectQualifier.toPhrase)

/-- English word for a targeting count. `1` is “one”; larger counts reuse
`englishNumber`. -/
private def countWord (n : Nat) : String :=
  match n with
  | 1 => "one"
  | n => englishNumber n

private def countPhrase : TargetCount → String
  | .or lo hi => s!"{countWord lo} or {countWord hi}"

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
    match t.toCard? with
    | some _ =>
      let n := t.phrase
      if n.endsWith "s" then n else s!"{n}s"
    | none => t.phrase
  | .controlledBy .you => "you control"
  | .controlledBy .opponent => "an opponent controls"
  | .or qs => orJoin (qs.map pluralQualifier)
  | .tapped => "tapped"
  | .this => "this"
  | .other => "other"
  | .it => "it"

/-- Singular words of a qualifier list, in order (`this creature`). -/
private def qualifierWords (qs : List ObjectQualifier) : String :=
  String.intercalate " " (qs.map ObjectQualifier.toPhrase)

private def TriggerExpr.toPhrase : TriggerExpr → String
  | .attack who restrictions =>
    let extra :=
      if restrictions.isEmpty then ""
      else s!" {qualifierWords restrictions}"
    s!"{qualifierWords who} attacks{extra}"

private def targetNoun (plural : Bool) (qs : List ObjectQualifier) : String :=
  if plural then String.intercalate " " (qs.map pluralQualifier)
  else qualifiersPhrase qs

private def TargetExpr.toPhrase : TargetExpr → String
  | .target qs => s!"target {qualifiersPhrase qs}"
  | .targets count qs =>
    let plural :=
      match count with
      | .or _ hi => hi > 1
    s!"{countPhrase count} target {targetNoun plural qs}"

private def tapSentence (ts : List TargetExpr) : String :=
  s!"Tap {joinTargets (ts.map TargetExpr.toPhrase)}."

private def untapSentence (ts : List TargetExpr) : String :=
  s!"Untap {joinTargets (ts.map TargetExpr.toPhrase)}."

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
  let bonus := String.intercalate " and " (mods.map statModPhrase)
  if qs == [.it] then
    s!"It gets {bonus} {durationPhrase dur}."
  else
    let subject := capitalizeAscii (String.intercalate " " (qs.map pluralQualifier))
    s!"{subject} get {bonus} {durationPhrase dur}."

private def costSubjectWord : CostSubject → String
  | .this => "this"
  | .spell => "spell"

private def castIfPhrase : CastIf → String
  | .targeting .it qs =>
    let noun := qualifiersPhrase qs
    s!"it targets {indefinite noun} {noun}"

private def costLessSentence (subjects : List CostSubject) (discount : List CostSymbol)
    (cond : CastIf) : String :=
  let subject := capitalizeAscii (String.intercalate " " (subjects.map costSubjectWord))
  let cost := (CostSymbol.toManaCost discount).toNotation
  s!"{subject} costs {cost} less to cast if {castIfPhrase cond}."

private def damageSubjectPhrase (cardName : String) : DamageSubject → String
  | .thisCardName => cardName

private def dealDamageSentence (cardName : String) (subjects : List DamageSubject)
    (n : Nat) (targets : List TargetExpr) : String :=
  let source := String.intercalate " and " (subjects.map (damageSubjectPhrase cardName))
  s!"{source} deals {n} damage to {joinTargets (targets.map TargetExpr.toPhrase)}."

private def conditionRefWord : ConditionRef → String
  | .it => "it"

private def playerPhrase : PlayerRef → String
  | .you => "you"
  | .opponent => "an opponent"

private def objectExprPhrase : ObjectExpr → String
  | .it => "it"
  | .oneOf qs =>
    let noun := qualifiersPhrase qs
    s!"{indefinite noun} {noun}"

private def objectExprsPhrase (xs : List ObjectExpr) : String :=
  String.intercalate " and " (xs.map objectExprPhrase)

private def attachClause (what dest : List ObjectExpr) : String :=
  s!"attach {objectExprsPhrase what} to {objectExprsPhrase dest}"

/-- An action inside `.may`, without the actor and without a final period. -/
private def optionalAction : TextEffect → String
  | .attachTo what dest => attachClause what dest
  | .untap targets => s!"untap {joinTargets (targets.map TargetExpr.toPhrase)}"
  | _ => ""

private def mayClause (who : List PlayerRef) (effects : List TextEffect) : String :=
  let actor := String.intercalate " and " (who.map playerPhrase)
  let action := String.intercalate " " (effects.map optionalAction)
  s!"{actor} may {action}"

private def isClause : TextCondition → String
  | .is subj qs =>
    let who := String.intercalate " " (subj.map conditionRefWord)
    let noun := qualifiersPhrase qs
    if who == "it" then s!"it's {indefinite noun} {noun}"
    else s!"{who} is {indefinite noun} {noun}"

private def thenClause : TextEffect → String
  | .may who es => mayClause who es
  | .attachTo what dest => attachClause what dest
  | _ => ""

private def ifSentence (conds : List TextCondition) (effects : List TextEffect) : String :=
  let cond := String.intercalate " and " (conds.map isClause)
  let body := String.intercalate " " (effects.map thenClause)
  s!"If {cond}, {body}."

/-- “it gets +1/+1 until end of turn for each other creature you control”. -/
private def getForEachClause (who : List ConditionRef) (mods : List StatMod)
    (each : List ObjectQualifier) (dur : Duration) : String :=
  let subject := String.intercalate " " (who.map conditionRefWord)
  let verb := if who.length == 1 then "gets" else "get"
  let bonus := String.intercalate " and " (mods.map statModPhrase)
  s!"{subject} {verb} {bonus} {durationPhrase dur} for each {qualifierWords each}"

private def wheneverBody : TextEffect → Option String
  | .getForEachUntil who mods each dur => some (getForEachClause who mods each dur)
  | _ => none

private def wheneverSentence (events : List TriggerExpr) (effects : List TextEffect) : String :=
  let trig := String.intercalate " and " (events.map TriggerExpr.toPhrase)
  let body := String.intercalate " " (effects.filterMap wheneverBody)
  s!"Whenever {trig}, {body}."

/-- A text-box effect nested under `.costFor`, printed without a further cost. -/
private def nestedEffectSentence (cardName : String) : TextEffect → Option String
  | .keyword _ => none
  | .gainUntil targets gains dur => some (gainUntilSentence targets gains dur)
  | .getUntil qs mods dur => some (getUntilSentence qs mods dur)
  | .costFor _ _ => none
  | .tap targets => some (tapSentence targets)
  | .costLessToCastIf subjects discount cond =>
    some (costLessSentence subjects discount cond)
  | .dealDamage subjects n targets =>
    some (dealDamageSentence cardName subjects n targets)
  | .whenever events effects => some (wheneverSentence events effects)
  | .getForEachUntil who mods each dur =>
    some s!"{capitalizeAscii (getForEachClause who mods each dur)}."
  | .sequence es =>
    some (String.intercalate " " (es.filterMap (nestedEffectSentence cardName)))
  | .untap targets => some (untapSentence targets)
  | .if conds effects => some (ifSentence conds effects)
  | .may who effects => some s!"{capitalizeAscii (mayClause who effects)}."
  | .attachTo what dest => some s!"{capitalizeAscii (attachClause what dest)}."

/-- One Oracle line for consecutive printed keywords (`Flying, lifelink`). -/
private def keywordRunLine (ks : List PrintedKeyword) : String :=
  capitalizeAscii (String.intercalate ", " (ks.map PrintedKeyword.oracleName))

/-- Oracle sentence for a text-box effect, without reminder text.
`cardName` is substituted for `.thisCardName`. -/
private def textEffectSentence (cardName : String) : TextEffect → String :=
  go
where
  go : TextEffect → String
    | .keyword k => keywordRunLine [k]
    | .gainUntil targets gains dur => gainUntilSentence targets gains dur
    | .getUntil qs mods dur => getUntilSentence qs mods dur
    | .costFor costs effects =>
      let cost := String.intercalate ", " (costs.map printedCostPhrase)
      let body := String.intercalate " " (effects.filterMap (nestedEffectSentence cardName))
      s!"{cost}: {body}"
    | .tap targets => tapSentence targets
    | .costLessToCastIf subjects discount cond =>
      costLessSentence subjects discount cond
    | .dealDamage subjects n targets =>
      dealDamageSentence cardName subjects n targets
    | .whenever events effects => wheneverSentence events effects
    | .getForEachUntil who mods each dur =>
      s!"{capitalizeAscii (getForEachClause who mods each dur)}."
    | .sequence es => String.intercalate " " (es.map go)
    | .untap targets => untapSentence targets
    | .if conds effects => ifSentence conds effects
    | .may who effects => s!"{capitalizeAscii (mayClause who effects)}."
    | .attachTo what dest => s!"{capitalizeAscii (attachClause what dest)}."

/-- Map a spell text-box effect onto the engine's `Effect` vocabulary. -/
private def textEffectToEffect : TextEffect → Option Effect
  | .gainUntil
      [.target [.or [.cardType .artifact, .cardType .creature], .controlledBy .you]]
      [.keyword .hexproof, .keyword .indestructible]
      .endOfTurn =>
    some Effect.grantHexproofIndestructible
  | .tap [.targets (.or 1 2) [.cardType .creature]] =>
    some Effect.tapOneOrTwoCreatures
  | .dealDamage [.thisCardName] n [.target [.cardType .creature]] =>
    some (Effect.dealDamageToCreature n)
  | .sequence
      [.untap [.target [.cardType .creature, .controlledBy .you]],
       .getUntil [.it] [.plusPowerToughness p t] .endOfTurn,
       .if
         [.is [.it] [.cardType .dwarf]]
         [.may [.you]
           [.attachTo [.oneOf [.cardType .equipment, .controlledBy .you]] [.it]]]] =>
    some (Effect.untapPumpMaybeAttach p t)
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

/-- Map `.whenever` onto a triggered ability the engine already resolves. -/
private def textEffectToTriggered : TextEffect → Option TriggeredAbility
  | .whenever
      [.attack [.this, .cardType .creature] []]
      [.getForEachUntil [.it] [.plusPowerToughness 1 1]
        [.other, .cardType .creature, .controlledBy .you] .endOfTurn] =>
    some .onAttackPumpForEachOtherCreature
  | _ => none

/-- Map `.costFor` onto a non-mana activated ability. -/
private def textEffectToActivated : TextEffect → Option ActivatedAbility
  | .costFor costs effects =>
    match effects.filterMap pumpEffect with
    | effect :: _ => some { cost := costsToActivation costs, effect }
    | [] => none
  | _ => none

private def adventureReminder : String :=
  "(Then exile this card. You may cast the creature later from exile.)"

/-- Generic mana in a discount such as `[.generic 3]`. -/
private def genericMana (ms : List CostSymbol) : Nat :=
  ms.foldl (fun n s =>
    match s with
    | .generic k => n + k
    | _ => n) 0

/-- `{n}` less when the spell targets a tapped creature. -/
private def tappedCreatureReduction (es : List TextEffect) : Nat :=
  es.foldl (fun n e =>
    match e with
    | .costLessToCastIf [.this, .spell] discount
        (.targeting .it [.tapped, .cardType .creature]) =>
      n + genericMana discount
    | _ => n) 0

/-- Rules-text lines for a text box. Consecutive keywords share one line. -/
private def renderText (cardName : String) (es : List TextEffect) : List String :=
  let (lines, pending) := es.foldl (fun (acc : List String × List PrintedKeyword) e =>
    let (lines, ks) := acc
    match e with
    | .keyword k => (lines, ks ++ [k])
    | other =>
      let lines := if ks.isEmpty then lines else lines ++ [keywordRunLine ks]
      (lines ++ [textEffectSentence cardName other], [])) ([], [])
  if pending.isEmpty then lines else lines ++ [keywordRunLine pending]

private def headerLines (f : FaceBuild) : List String :=
  let cost := (CostSymbol.toManaCost f.manaCost).toNotation
  let nameLine := if cost.isEmpty then f.name else s!"{f.name} {cost}"
  let typeLine :=
    formatTypeLine f.supertypes.toArray f.types.toArray
      (f.subtypes.toArray.map CardSubtype.printed)
  [nameLine, typeLine]

private def effectLines (f : FaceBuild) : List String :=
  let lines := renderText f.name f.textBox
  let remind := f.subtypes.any (· == .adventure)
  match lines.dropLast, lines.getLast? with
  | _, none => []
  | init, some last =>
    let last := if remind then s!"{last} {adventureReminder}" else last
    init ++ [last]

/-- Rules text stored on the creature face, including the `//ADV//` block. -/
private def rulesOracle (main : FaceBuild) (alt : Option FaceBuild) : String :=
  let adv :=
    match alt with
    | none => []
    | some a => ["//ADV//"] ++ headerLines a ++ effectLines a
  String.intercalate "\n" (renderText main.name main.textBox ++ adv)

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
    keywords := keywordsOfText f.textBox
    spellEffect := (f.textBox.filterMap textEffectToEffect).head?
    costReductionIfTargetTapped := tappedCreatureReduction f.textBox
    activatedAbilities := (f.textBox.filterMap textEffectToActivated).toArray
    triggeredAbilities := (f.textBox.filterMap textEffectToTriggered).toArray
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

/-- Append engine cards to DSL cards. Deck lists interleave the two. -/
instance : HAppend (Array CardDef) (Array TraditionalCardDefinition) (Array CardDef) where
  hAppend as bs := as ++ bs.map (·.toCardDef)

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
  | "insect" => some .insect
  | "adventure" => some .adventure
  | "bird" => some .bird
  | "soldier" => some .soldier
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
    return [.cardType (TypeName.ofCard t)]
  | many =>
    let ts ← many.mapM parseCardType
    return [.or (ts.map (fun t => ObjectQualifier.cardType (TypeName.ofCard t)))]

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
    return [.cardType (TypeName.ofCard t)]
  | many =>
    let ts ← many.mapM (fun w => parseCardType (singularize w))
    return [.or (ts.map (fun t => ObjectQualifier.cardType (TypeName.ofCard t)))]

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

private def parseMaybeTappedNoun (noun : String) : Option (List ObjectQualifier) := do
  let (tapped, core) :=
    if let some core := dropPrefixCI noun "tapped " then
      (true, core)
    else
      (false, noun)
  let quals ← parseNoun core
  return (if tapped then [ObjectQualifier.tapped] else []) ++ quals

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

private def parseTargetExpr (s : String) : Option TargetExpr := do
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
  let tgt ← parseTargetExpr tgtText
  return .dealDamage [.thisCardName] n [tgt]

private def parseAttackSubject (s : String) : Option (List ObjectQualifier) := do
  if let some rest := dropPrefixCI s "this " then
    let t ← parseCardType rest
    return [.this, .cardType (TypeName.ofCard t)]
  else
    parseNoun s

private def parseAttackRestrictions (s : String) : Option (List ObjectQualifier) :=
  let s := s.trimAscii.copy
  if s.isEmpty then some [] else none

/-- `this creature attacks` with no further restriction. -/
private def parseAttackTrigger (s : String) : Option TriggerExpr := do
  let (subject, rest) ← splitOnce " attacks" s
  let who ← parseAttackSubject subject
  let restrictions ← parseAttackRestrictions rest
  return .attack who restrictions

private def parseGetsSubject (s : String) : Option (List ConditionRef) :=
  match s.trimAscii.copy.map Char.toLower with
  | "it" => some [.it]
  | _ => none

/-- `other creature you control` is `[.other, .cardType .creature, .controlledBy .you]`. -/
private def parseForEachSubject (s : String) : Option (List ObjectQualifier) := do
  let (other, core) :=
    if let some core := dropPrefixCI s "other " then
      (true, core)
    else
      (false, s)
  let quals ← parseNoun core
  return (if other then [ObjectQualifier.other] else []) ++ quals

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

/-- `Whenever this creature attacks, it gets +1/+1 until end of turn for each other creature you control.` -/
private def parseWhenever (line : String) : Option TextEffect := do
  let line := stripTrailingDot (stripParens line)
  let rest ← dropPrefixCI line "Whenever "
  let (trigText, effectText) ← splitOnce ", " rest
  let trig ← parseAttackTrigger trigText
  let effect ← parseGetForEachUntil effectText
  return .whenever [trig] [effect]

private def parseTypeName (s : String) : Option TypeName :=
  match s.trimAscii.copy.map Char.toLower with
  | "dwarf" => some .dwarf
  | "equipment" => some .equipment
  | other => (parseCardType other).map TypeName.ofCard

private def dropArticle (s : String) : Option String :=
  if let some r := dropPrefixCI s "an " then some r
  else if let some r := dropPrefixCI s "a " then some r
  else some s

/-- `Equipment you control` or `Dwarf`, including a leading article. -/
private def parseTypedControlled (s : String) : Option (List ObjectQualifier) := do
  let noun ← dropArticle s
  let (core, who) :=
    if let some core := stripSuffixCI? noun " you control" then
      (core, some PlayerRef.you)
    else if let some core := stripSuffixCI? noun " an opponent controls" then
      (core, some PlayerRef.opponent)
    else
      (noun, none)
  let t ← parseTypeName core
  let tail :=
    match who with
    | some p => [ObjectQualifier.controlledBy p]
    | none => []
  return [.cardType t] ++ tail

/-- `Untap target creature you control`. -/
private def parseUntap (s : String) : Option TextEffect := do
  let rest ← dropPrefixCI s "Untap "
  let tgt ← parseTargetExpr rest
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
`Untap target creature you control. It gets … If it's a Dwarf, you may attach
an Equipment you control to it.` becomes `.sequence` with `.untap`, `.getUntil`,
and `.if`.
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
#guard textEffectSentence "" (.gainUntil
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
#guard textEffectSentence "" (.costFor
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
#guard keywordRunLine [.lifelink] == "Lifelink"
#guard renderText "" [.keyword .flying, .keyword .lifelink] == ["Flying, lifelink"]
#guard parseKeywordLine "Lifelink" == some [.keyword .lifelink]
#guard parseKeywordLine "Flying, lifelink" == some [.keyword .flying, .keyword .lifelink]
#guard textEffectSentence "" (.tap [.targets (.or 1 2) [.cardType .creature]]) ==
  "Tap one or two target creatures."
#guard parseTap
    "Tap one or two target creatures. (Then exile this card. You may cast the creature later from exile.)" ==
  some (.tap [.targets (.or 1 2) [.cardType .creature]])
#guard textEffectSentence "Magnificent End"
    (.costLessToCastIf [.this, .spell] [.generic 3]
      (.targeting .it [.tapped, .cardType .creature])) ==
  "This spell costs {3} less to cast if it targets a tapped creature."
#guard textEffectSentence "Magnificent End"
    (.dealDamage [.thisCardName] 5 [.target [.cardType .creature]]) ==
  "Magnificent End deals 5 damage to target creature."
#guard parseCostLess
    "This spell costs {3} less to cast if it targets a tapped creature." ==
  some (.costLessToCastIf [.this, .spell] [.generic 3]
    (.targeting .it [.tapped, .cardType .creature]))
#guard parseDealDamage "Magnificent End"
    "Magnificent End deals 5 damage to target creature." ==
  some (.dealDamage [.thisCardName] 5 [.target [.cardType .creature]])
#guard textEffectSentence "Eagle of the Great Shelf" (.whenever
    [.attack [.this, .cardType .creature] []]
    [getForEachUntil [.it] [.plusPowerToughness +1 +1]
      [.other, .cardType .creature, .controlledBy .you] .endOfTurn]) ==
  "Whenever this creature attacks, it gets +1/+1 until end of turn for each other creature you control."
#guard parseWhenever
    "Whenever this creature attacks, it gets +1/+1 until end of turn for each other creature you control." ==
  some (.whenever
    [.attack [.this, .cardType .creature] []]
    [.getForEachUntil [.it] [.plusPowerToughness 1 1]
      [.other, .cardType .creature, .controlledBy .you] .endOfTurn])
#guard textEffectSentence "Vow to Erebor" (.sequence [
    .untap [.target [.cardType .creature, .controlledBy .you]],
    .getUntil [.it] [.plusPowerToughness +2 +2] .endOfTurn,
    .if
      [.is [.it] [.cardType .dwarf]]
      [.may [.you] [.attachTo [.oneOf [.cardType .equipment, .controlledBy .you]] [.it]]]]) ==
  "Untap target creature you control. It gets +2/+2 until end of turn. If it's a Dwarf, you may attach an Equipment you control to it."
#guard parseSequence
    "Untap target creature you control. It gets +2/+2 until end of turn. If it's a Dwarf, you may attach an Equipment you control to it." ==
  some (.sequence [
    .untap [.target [.cardType .creature, .controlledBy .you]],
    .getUntil [.it] [.plusPowerToughness 2 2] .endOfTurn,
    .if
      [.is [.it] [.cardType .dwarf]]
      [.may [.you] [.attachTo [.oneOf [.cardType .equipment, .controlledBy .you]] [.it]]]])

end Mtg.Engine
