import Mtg.Engine.Mana
import Mtg.Engine.TypeLine
import Mtg.Engine.Card.Keywords
import Mtg.Engine.Card.Text
import Mtg.Engine.Card.CardDef
import Mtg.Engine.Card.SpellEffects
import Mtg.Engine.Card.Dsl.Elements

/-!
# Compiling DSL cards

Functions on the clause vocabulary. `TraditionalCardDefinition.toCardDef`
turns a clause list into the engine's `CardDef`, including the Oracle text
those clauses print.
-/

namespace Mtg.Engine

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

namespace CardSubtype

def printed : CardSubtype → String
  | .dwarf => "Dwarf"
  | .citizen => "Citizen"
  | .scout => "Scout"
  | .insect => "Insect"
  | .adventure => "Adventure"
  | .bird => "Bird"
  | .soldier => "Soldier"
  | .halfling => "Halfling"
  | .rogue => "Rogue"
  | .human => "Human"
  | .cleric => "Cleric"

end CardSubtype

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

end PrintedKeyword

namespace TypeName

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
  | .equipment => none

/-- Printed word. Card types stay lowercase (`creature`); `.equipment` keeps
Oracle capitalization (`Equipment`). -/
def phrase : TypeName → String
  | .equipment => "Equipment"
  | t =>
    match t.toCard? with
    | some c => c.englishName.map Char.toLower
    | none => ""

end TypeName

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

/-- Legendary short name: the printed name before the first comma (CR 201.3). -/
private def shortCardName (cardName : String) : String :=
  match cardName.splitOn ", " with
  | head :: _ => if head.isEmpty then cardName else head
  | [] => cardName

/-- Printed word for one `ObjectRef`. `plural` pluralizes a card type
(`creature` / `creatures`). `.thisCardName` prints the legendary short name.
`.oneOf` adds an indefinite article (`an Equipment you control`). -/
private def objectPhrase (cardName : String) (plural : Bool) : ObjectRef → String
  | .cardType t =>
    if plural then
      match t.toCard? with
      | some _ =>
        let n := t.phrase
        if n.endsWith "s" then n else s!"{n}s"
      | none => t.phrase
    else
      t.phrase
  | .cardSubtype s => s.printed
  | .controlledBy .you => "you control"
  | .controlledBy .opponent => "an opponent controls"
  | .or qs => orJoin (qs.map (objectPhrase cardName plural))
  | .tapped => "tapped"
  | .this => "this"
  | .other => "other"
  | .it => "it"
  | .spell => if plural then "spells" else "spell"
  | .permanentSpell => "permanent spell"
  | .thatCard => "that card"
  | .thisCardName => shortCardName cardName
  | .oneOf qs =>
    let noun := String.intercalate " " (qs.map (objectPhrase cardName false))
    s!"{indefinite noun} {noun}"
  | .target qs =>
    s!"target {String.intercalate " " (qs.map (objectPhrase cardName false))}"
  | .targets count qs =>
    let many :=
      match count with
      | .or _ hi => hi > 1
    s!"{countPhrase count} target {String.intercalate " " (qs.map (objectPhrase cardName many))}"

/-- Words of a reference list, in order (`this creature`). -/
private def joinPhrases (cardName : String) (plural : Bool) (qs : List ObjectRef) : String :=
  String.intercalate " " (qs.map (objectPhrase cardName plural))

private def playerPhrase : PlayerRef → String
  | .you => "you"
  | .opponent => "an opponent"

private def drawVerb (who : List PlayerRef) : String :=
  if who == [.you] then "draw" else "draws"

private def drawPossessive (who : List PlayerRef) : String :=
  if who == [.you] then "your" else "their"

private def ordinalWord (n : Nat) : String :=
  match n with
  | 1 => "first"
  | 2 => "second"
  | 3 => "third"
  | 4 => "fourth"
  | 5 => "fifth"
  | n => toString n

private def eachPeriodPhrase : EachPeriod → String
  | .turn => "turn"

private def drawWatchPhrase (who : List PlayerRef) : DrawWatch → String
  | .ordinalEach n period =>
    s!"{drawPossessive who} {ordinalWord n} card each {eachPeriodPhrase period}"

/-- What was drawn. An empty watch list is any card (“a card”). -/
private def drawnPhrase (who : List PlayerRef) (which : List DrawWatch) : String :=
  match which with
  | [] => "a card"
  | ws => String.intercalate " " (ws.map (drawWatchPhrase who))

/-- Subject of `.creatureAttack`. The event supplies “creature”, so `who`
does not store `.cardType .creature`. Control phrases follow the noun
(`creature you control`). -/
private def creatureAttackSubject (cardName : String) (who : List ObjectRef) : String :=
  let (before, after) := who.span fun r =>
    match r with
    | .controlledBy _ => false
    | _ => true
  let pre := joinPhrases cardName false before
  let post := joinPhrases cardName false after
  let noun := if pre.isEmpty then "creature" else s!"{pre} creature"
  if post.isEmpty then noun else s!"{noun} {post}"

private def TriggerExpr.phrase (cardName : String) : TriggerExpr → String
  | .creatureAttack who restrictions =>
    let extra :=
      if restrictions.isEmpty then ""
      else s!" {joinPhrases cardName false restrictions}"
    s!"{creatureAttackSubject cardName who} attacks{extra}"
  | .permanentEnter who =>
    s!"{joinPhrases cardName false who} enters"
  | .drawCard who which =>
    let actor := String.intercalate " and " (who.map playerPhrase)
    s!"{actor} {drawVerb who} {drawnPhrase who which}"

private def tapSentence (cardName : String) (ts : List ObjectRef) : String :=
  s!"Tap {joinTargets (ts.map (objectPhrase cardName false))}."

private def untapSentence (cardName : String) (ts : List ObjectRef) : String :=
  s!"Untap {joinTargets (ts.map (objectPhrase cardName false))}."

private def statModPhrase : StatMod → String
  | .plusPowerToughness p t => s!"{signedStat p}/{signedStat t}"

private def printedCostPhrase : PrintedCost → String
  | .mana ms => (CostSymbol.toManaCost ms).toNotation

private def gainUntilSentence (cardName : String) (targets : List ObjectRef)
    (gains : List GrantedAbility) (dur : Duration) : String :=
  let subject := capitalizeAscii (joinTargets (targets.map (objectPhrase cardName false)))
  let kws := (keywordsOfGranted gains).joinedAnd
  s!"{subject} gains {kws} {durationPhrase dur}."

private def getUntilSentence (cardName : String) (qs : List ObjectRef) (mods : List StatMod)
    (dur : Duration) : String :=
  let bonus := String.intercalate " and " (mods.map statModPhrase)
  if qs == [.it] then
    s!"It gets {bonus} {durationPhrase dur}."
  else
    let subject := capitalizeAscii (joinPhrases cardName true qs)
    s!"{subject} get {bonus} {durationPhrase dur}."

private def costLessClause (cardName : String) (subjects : List ObjectRef)
    (discount : List CostSymbol) : String :=
  let subject := capitalizeAscii (joinPhrases cardName false subjects)
  let cost := (CostSymbol.toManaCost discount).toNotation
  s!"{subject} costs {cost} less to cast"

private def dealDamageSentence (cardName : String) (subjects : List ObjectRef)
    (n : Nat) (targets : List ObjectRef) : String :=
  let source := String.intercalate " and " (subjects.map (objectPhrase cardName false))
  s!"{source} deals {n} damage to {joinTargets (targets.map (objectPhrase cardName false))}."

private def objectExprsPhrase (cardName : String) (xs : List ObjectRef) : String :=
  String.intercalate " and " (xs.map (objectPhrase cardName false))

private def attachClause (cardName : String) (what dest : List ObjectRef) : String :=
  s!"attach {objectExprsPhrase cardName what} to {objectExprsPhrase cardName dest}"

private def possessorPhrase (cardName : String) : ZoneOwner → String
  | .owner objs =>
    let who := joinPhrases cardName false objs
    if who == "it" then "its owner" else s!"the owner of {who}"

private def zonePhrase (cardName : String) (ws : List ZoneWord) : String :=
  let place := String.intercalate " " (ws.filterMap fun w =>
    match w with
    | .graveyard => some "graveyard"
    | .exiled => some "exiled"
    | .belongingTo _ => none)
  let owners := ws.filterMap fun w =>
    match w with
    | .belongingTo who =>
      some (String.intercalate " and " (who.map (possessorPhrase cardName)))
    | _ => none
  match owners with
  | [] => place
  | _ =>
    let owner := String.intercalate " and " owners
    if place.isEmpty then owner else s!"{owner}'s {place}"

private def putIntoClause (cardName : String) (obj : List ObjectRef) (dest : List ZoneWord) : String :=
  s!"putting {joinPhrases cardName false obj} into {zonePhrase cardName dest}"

private def exileClause (cardName : String) (obj : List ObjectRef) : String :=
  s!"exile {joinPhrases cardName false obj}"

private def avoidedClause (cardName : String) : TextEffect → String
  | .putInto obj dest => putIntoClause cardName obj dest
  | _ => ""

private def replacementClause (cardName : String) : TextEffect → String
  | .exile obj => exileClause cardName obj
  | _ => ""

private def insteadOfClause (cardName : String) (avoided done : List TextEffect) : String :=
  let replacement := String.intercalate " " (done.map (replacementClause cardName))
  let original := String.intercalate " " (avoided.map (avoidedClause cardName))
  s!"{replacement} instead of {original}"

private def mannerPhrase : CastManner → String
  | .withoutPayingManaCost => "without paying its mana cost"

private def mayCastSoClause (cardName : String) (who : List PlayerRef) (what : List ObjectRef)
    (how : List CastManner) : String :=
  let actor := String.intercalate " and " (who.map playerPhrase)
  let obj := joinPhrases cardName false what
  let pay := String.intercalate " " (how.map mannerPhrase)
  s!"{actor} may cast {obj} {pay}"

private def remainsClause (cardName : String) (obj : List ObjectRef) (state : List ZoneWord) : String :=
  s!"{joinPhrases cardName false obj} remains {zonePhrase cardName state}"

private def durationAction (cardName : String) : TextEffect → String
  | .mayCastSo who what how => mayCastSoClause cardName who what how
  | _ => ""

private def durationCond (cardName : String) : TextEffect → String
  | .remains obj state => remainsClause cardName obj state
  | _ => ""

private def asLongAsClause (cardName : String) (action cond : List TextEffect) : String :=
  let act := String.intercalate " " (action.map (durationAction cardName))
  let while_ := String.intercalate " " (cond.map (durationCond cardName))
  s!"{act} for as long as {while_}"

private def putIntoSentence (cardName : String) (obj : List ObjectRef) (dest : List ZoneWord) : String :=
  s!"Put {joinPhrases cardName false obj} into {zonePhrase cardName dest}."

private def exileSentence (cardName : String) (obj : List ObjectRef) : String :=
  s!"{capitalizeAscii (exileClause cardName obj)}."

private def insteadOfSentence (cardName : String) (avoided done : List TextEffect) : String :=
  s!"{capitalizeAscii (insteadOfClause cardName avoided done)}."

private def mayCastSoSentence (cardName : String) (who : List PlayerRef) (what : List ObjectRef)
    (how : List CastManner) : String :=
  s!"{capitalizeAscii (mayCastSoClause cardName who what how)}."

private def remainsSentence (cardName : String) (obj : List ObjectRef) (state : List ZoneWord) : String :=
  s!"{capitalizeAscii (remainsClause cardName obj state)}."

private def asLongAsSentence (cardName : String) (action cond : List TextEffect) : String :=
  s!"{capitalizeAscii (asLongAsClause cardName action cond)}."

/-- An action inside `.may`, without the actor and without a final period. -/
private def optionalAction (cardName : String) : TextEffect → String
  | .attachTo what dest => attachClause cardName what dest
  | .untap targets => s!"untap {joinTargets (targets.map (objectPhrase cardName false))}"
  | _ => ""

private def mayClause (cardName : String) (who : List PlayerRef) (effects : List TextEffect) : String :=
  let actor := String.intercalate " and " (who.map playerPhrase)
  let action := String.intercalate " " (effects.map (optionalAction cardName))
  s!"{actor} may {action}"

private def isClause (cardName : String) : TextCondition → String
  | .is subj qs =>
    let who := joinPhrases cardName false subj
    let noun := joinPhrases cardName false qs
    if who == "it" then s!"it's {indefinite noun} {noun}"
    else s!"{who} is {indefinite noun} {noun}"
  | .counteredThisWay qs =>
    let noun := joinPhrases cardName false qs
    s!"{indefinite noun} {noun} is countered this way"
  | .targeting subj qs =>
    let who := joinPhrases cardName false subj
    let noun := joinPhrases cardName false qs
    s!"{who} targets {indefinite noun} {noun}"

/-- A subject already named in the cost-reduction clause is “it”. -/
private def costLessCond (cardName : String) (subjects : List ObjectRef) : TextCondition → String
  | .targeting subj qs =>
    let actor := if subj == subjects then "it" else joinPhrases cardName false subj
    let noun := joinPhrases cardName false qs
    s!"{actor} targets {indefinite noun} {noun}"
  | other => isClause cardName other

private def thenClause (cardName : String) : TextEffect → String
  | .may who es => mayClause cardName who es
  | .attachTo what dest => attachClause cardName what dest
  | .insteadOf avoided done => insteadOfClause cardName avoided done
  | _ => ""

/-- `.asLongAs` prints as its own sentence after the “If …” sentence. -/
private def followsIf : TextEffect → Bool
  | .asLongAs _ _ => true
  | _ => false

private def ifSentence (cardName : String) (conds : List TextCondition)
    (effects : List TextEffect) : String :=
  match effects with
  | [.costLessToCast subjects discount] =>
    let cond := String.intercalate " and " (conds.map (costLessCond cardName subjects))
    s!"{costLessClause cardName subjects discount} if {cond}."
  | _ =>
    let cond := String.intercalate " and " (conds.map (isClause cardName))
    let inline := effects.filter fun e => not (followsIf e)
    let trailing := effects.filter followsIf
    let body := String.intercalate " " (inline.map (thenClause cardName))
    let head :=
      if inline.isEmpty then s!"If {cond}." else s!"If {cond}, {body}."
    let rest := trailing.map fun e =>
      match e with
      | .asLongAs action dur => asLongAsSentence cardName action dur
      | _ => ""
    String.intercalate " " (head :: rest.filter (· != ""))

/-- “put a +1/+1 counter on this creature”. -/
private def putCounterClause (cardName : String) (n : Nat) (kind : CounterKind)
    (objects : List ObjectRef) : String :=
  let counters :=
    match kind with
    | .plusOnePlusOne => plusOnePlusOneCountersPhrase n
  s!"put {counters} on {joinPhrases cardName false objects}"

/-- “it gets +1/+1 until end of turn for each other creature you control”. -/
private def getForEachClause (cardName : String) (who : List ObjectRef) (mods : List StatMod)
    (each : List ObjectRef) (dur : Duration) : String :=
  let subject := joinPhrases cardName false who
  let verb := if who.length == 1 then "gets" else "get"
  let bonus := String.intercalate " and " (mods.map statModPhrase)
  s!"{subject} {verb} {bonus} {durationPhrase dur} for each {joinPhrases cardName false each}"

private def wheneverBody (cardName : String) : TextEffect → Option String
  | .getForEachUntil who mods each dur => some (getForEachClause cardName who mods each dur)
  | .putCounter n kind objects => some (putCounterClause cardName n kind objects)
  | _ => none

private def wheneverSentence (cardName : String) (events : List TriggerExpr)
    (effects : List TextEffect) : String :=
  let trig := String.intercalate " and " (events.map (TriggerExpr.phrase cardName))
  let body := String.intercalate " " (effects.filterMap (wheneverBody cardName))
  s!"Whenever {trig}, {body}."

private def drawClause (n : Nat) : String :=
  s!"draw {cardPhrase n}"

private def whenBody : TextEffect → Option String
  | .draw n => some (drawClause n)
  | _ => none

private def whenSentence (cardName : String) (events : List TriggerExpr)
    (effects : List TextEffect) : String :=
  let trig := String.intercalate " and " (events.map (TriggerExpr.phrase cardName))
  let body := String.intercalate " " (effects.filterMap whenBody)
  s!"When {trig}, {body}."

private def scrySentence (n : Nat) : String :=
  s!"Scry {n}."

/-- English for `n` cards (`a card`, `two cards`). “Draw …, then discard” uses words. -/
private def cardCountPhrase (n : Nat) : String :=
  if n == 1 then "a card" else s!"{englishNumber n} cards"

private def discardSentence (n : Nat) : String :=
  s!"Discard {cardCountPhrase n}."

private def counterSentence (cardName : String) (targets : List ObjectRef) : String :=
  s!"Counter {joinTargets (targets.map (objectPhrase cardName false))}."

/-- `.sequence [.draw n, .discard d]` prints “Draw …, then discard …”. -/
private def drawThenDiscardSentence (n d : Nat) : String :=
  s!"Draw {cardCountPhrase n}, then discard {cardCountPhrase d}."

private def payerPhrase (cardName : String) : Payer → String
  | .controller obj =>
    match obj with
    | .it => "its controller"
    | named => s!"{objectPhrase cardName false named}'s controller"

/-- Lowercase action inside `.unlessPay` (`counter target spell`). -/
private def unlessAction (cardName : String) : TextEffect → String
  | .counter targets =>
    s!"counter {joinTargets (targets.map (objectPhrase cardName false))}"
  | _ => ""

private def unlessPaySentence (cardName : String) (actions : List TextEffect)
    (who : List Payer) (costs : List PrintedCost) : String :=
  let action := capitalizeAscii (String.intercalate " " (actions.map (unlessAction cardName)))
  let payer := String.intercalate " and " (who.map (payerPhrase cardName))
  let cost := String.intercalate ", " (costs.map printedCostPhrase)
  s!"{action} unless {payer} pays {cost}."

private def chooseHeader (n : Nat) : String :=
  s!"Choose {countWord n} —"

/-- A text-box effect nested under `.costFor`, printed without a further cost. -/
private def nestedEffectSentence (cardName : String) : TextEffect → Option String
  | .keyword _ => none
  | .gainUntil targets gains dur => some (gainUntilSentence cardName targets gains dur)
  | .getUntil qs mods dur => some (getUntilSentence cardName qs mods dur)
  | .costFor _ _ => none
  | .tap targets => some (tapSentence cardName targets)
  | .costLessToCast subjects discount =>
    some s!"{costLessClause cardName subjects discount}."
  | .dealDamage subjects n targets =>
    some (dealDamageSentence cardName subjects n targets)
  | .whenever events effects => some (wheneverSentence cardName events effects)
  | .when events effects => some (whenSentence cardName events effects)
  | .draw n => some s!"Draw {cardPhrase n}."
  | .scry n => some (scrySentence n)
  | .getForEachUntil who mods each dur =>
    some s!"{capitalizeAscii (getForEachClause cardName who mods each dur)}."
  | .sequence [.draw n, .discard d] => some (drawThenDiscardSentence n d)
  | .sequence es =>
    some (String.intercalate " " (es.filterMap (nestedEffectSentence cardName)))
  | .untap targets => some (untapSentence cardName targets)
  | .if conds effects => some (ifSentence cardName conds effects)
  | .may who effects => some s!"{capitalizeAscii (mayClause cardName who effects)}."
  | .attachTo what dest => some s!"{capitalizeAscii (attachClause cardName what dest)}."
  | .putCounter n kind objects =>
    some s!"{capitalizeAscii (putCounterClause cardName n kind objects)}."
  | .counter targets => some (counterSentence cardName targets)
  | .putInto obj dest => some (putIntoSentence cardName obj dest)
  | .exile obj => some (exileSentence cardName obj)
  | .insteadOf avoided done => some (insteadOfSentence cardName avoided done)
  | .mayCastSo who what how => some (mayCastSoSentence cardName who what how)
  | .remains obj state => some (remainsSentence cardName obj state)
  | .asLongAs action dur => some (asLongAsSentence cardName action dur)
  | .discard n => some (discardSentence n)
  | .unlessPay actions who costs => some (unlessPaySentence cardName actions who costs)
  | .chooseMode n modes =>
    some <| String.intercalate "\n" <|
      chooseHeader n :: (modes.filterMap (nestedEffectSentence cardName)).map (s!"• {·}")

/-- One Oracle line for consecutive printed keywords (`Flying, lifelink`). -/
private def keywordRunLine (ks : List PrintedKeyword) : String :=
  capitalizeAscii (String.intercalate ", " (ks.map PrintedKeyword.oracleName))

/-- Oracle sentence for a text-box effect, without reminder text.
`cardName` is substituted for `.thisCardName`, shortened before a comma. -/
private def textEffectSentence (cardName : String) : TextEffect → String :=
  go
where
  go : TextEffect → String
    | .keyword k => keywordRunLine [k]
    | .gainUntil targets gains dur => gainUntilSentence cardName targets gains dur
    | .getUntil qs mods dur => getUntilSentence cardName qs mods dur
    | .costFor costs effects =>
      let cost := String.intercalate ", " (costs.map printedCostPhrase)
      let body := String.intercalate " " (effects.filterMap (nestedEffectSentence cardName))
      s!"{cost}: {body}"
    | .tap targets => tapSentence cardName targets
    | .costLessToCast subjects discount =>
      s!"{costLessClause cardName subjects discount}."
    | .dealDamage subjects n targets =>
      dealDamageSentence cardName subjects n targets
    | .whenever events effects => wheneverSentence cardName events effects
    | .when events effects => whenSentence cardName events effects
    | .draw n => s!"Draw {cardPhrase n}."
    | .scry n => scrySentence n
    | .getForEachUntil who mods each dur =>
      s!"{capitalizeAscii (getForEachClause cardName who mods each dur)}."
    | .sequence [.draw n, .discard d] => drawThenDiscardSentence n d
    | .sequence es => String.intercalate " " (es.map go)
    | .untap targets => untapSentence cardName targets
    | .if conds effects => ifSentence cardName conds effects
    | .may who effects => s!"{capitalizeAscii (mayClause cardName who effects)}."
    | .attachTo what dest => s!"{capitalizeAscii (attachClause cardName what dest)}."
    | .putCounter n kind objects =>
      s!"{capitalizeAscii (putCounterClause cardName n kind objects)}."
    | .counter targets => counterSentence cardName targets
    | .putInto obj dest => putIntoSentence cardName obj dest
    | .exile obj => exileSentence cardName obj
    | .insteadOf avoided done => insteadOfSentence cardName avoided done
    | .mayCastSo who what how => mayCastSoSentence cardName who what how
    | .remains obj state => remainsSentence cardName obj state
    | .asLongAs action dur => asLongAsSentence cardName action dur
    | .discard n => discardSentence n
    | .unlessPay actions who costs => unlessPaySentence cardName actions who costs
    | .chooseMode n modes =>
      String.intercalate "\n" (chooseHeader n :: (modes.map go).map (s!"• {·}"))

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
  | .scry n => some (Effect.scry n)
  | .sequence
      [.untap [.target [.cardType .creature, .controlledBy .you]],
       .getUntil [.it] [.plusPowerToughness p t] .endOfTurn,
       .if
         [.is [.it] [.cardSubtype .dwarf]]
         [.may [.you]
           [.attachTo [.oneOf [.cardType .equipment, .controlledBy .you]] [.it]]]] =>
    some (Effect.untapPumpMaybeAttach p t)
  | .sequence [.draw n, .discard 1] =>
    some (Effect.drawThenDiscard n)
  | .unlessPay
      [.counter [.target [.spell]]]
      [.controller .it]
      [.mana [.generic n]] =>
    some (Effect.counterUnlessPays n)
  | .sequence
      [.counter [.target [.spell]],
       .if
         [.counteredThisWay [.permanentSpell]]
         [.insteadOf
            [.putInto [.it] [.graveyard, .belongingTo [.owner [.it]]]]
            [.exile [.it]],
          .asLongAs
            [.mayCastSo [.you] [.thatCard] [.withoutPayingManaCost]]
            [.remains [.it] [.exiled]]]] =>
    some Effect.counterExilePermanentMayCast
  | _ => none

private def creaturesYouControl (qs : List ObjectRef) : Bool :=
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

/-- Map `.whenever` and `.when` onto a triggered ability the engine already resolves. -/
private def textEffectToTriggered : TextEffect → Option TriggeredAbility
  | .whenever
      [.creatureAttack [.this] []]
      [.getForEachUntil [.it] [.plusPowerToughness 1 1]
        [.other, .cardType .creature, .controlledBy .you] .endOfTurn] =>
    some .onAttackPumpForEachOtherCreature
  | .when
      [.permanentEnter [.thisCardName]]
      [.draw n] =>
    some (.onEnterDraw n)
  | .whenever
      [.drawCard [.you] []]
      [.putCounter 1 .plusOnePlusOne [.this, .cardType .creature]] =>
    some .onDrawPlusOne
  | .whenever
      [.drawCard [.you] [.ordinalEach 2 .turn]]
      [.putCounter 1 .plusOnePlusOne [.this, .cardType .creature]] =>
    some .onDrawSecondPlusOne
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

/-- Modes of a `.choose` text box, in printed order. -/
private def spellModesOf (es : List TextEffect) : Array Effect :=
  es.foldl (fun acc e =>
    match e with
    | .chooseMode _ modes => acc ++ (modes.filterMap textEffectToEffect).toArray
    | _ => acc) #[]

/-- `{n}` less when the spell targets a tapped creature. -/
private def tappedCreatureReduction (es : List TextEffect) : Nat :=
  es.foldl (fun n e =>
    match e with
    | .if
        [.targeting [.this, .spell] [.tapped, .cardType .creature]]
        [.costLessToCast [.this, .spell] discount] =>
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
    spellModes := spellModesOf f.textBox
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

/-! Oracle sentences for the clause vocabulary. -/

#guard textEffectSentence "" (.gainUntil
    [.target [.or [.cardType .artifact, .cardType .creature], .controlledBy .you]]
    [.keyword .hexproof, .keyword .indestructible]
    .endOfTurn) ==
  "Target artifact or creature you control gains hexproof and indestructible until end of turn."

#guard textEffectSentence "" (.costFor
    [.mana [.generic 3, .mono .white]]
    [.getUntil [.cardType .creature, .controlledBy .you]
      [.plusPowerToughness (+1) (+1)] .endOfTurn]) ==
  "{3}{W}: Creatures you control get +1/+1 until end of turn."

#guard keywordRunLine [.lifelink] == "Lifelink"

#guard renderText "" [.keyword .flying, .keyword .lifelink] == ["Flying, lifelink"]

#guard textEffectSentence "" (.tap [.targets (.or 1 2) [.cardType .creature]]) ==
  "Tap one or two target creatures."

#guard textEffectSentence "Magnificent End"
    (.if
      [.targeting [.this, .spell] [.tapped, .cardType .creature]]
      [.costLessToCast [.this, .spell] [.generic 3]]) ==
  "This spell costs {3} less to cast if it targets a tapped creature."

#guard textEffectSentence "Magnificent End"
    (.dealDamage [.thisCardName] 5 [.target [.cardType .creature]]) ==
  "Magnificent End deals 5 damage to target creature."

#guard textEffectSentence "Eagle of the Great Shelf" (.whenever
    [.creatureAttack [.this] []]
    [getForEachUntil [.it] [.plusPowerToughness (+1) (+1)]
      [.other, .cardType .creature, .controlledBy .you] .endOfTurn]) ==
  "Whenever this creature attacks, it gets +1/+1 until end of turn for each other creature you control."

#guard textEffectSentence "Vow to Erebor" (.sequence [
    .untap [.target [.cardType .creature, .controlledBy .you]],
    .getUntil [.it] [.plusPowerToughness (+2) (+2)] .endOfTurn,
    .if
      [.is [.it] [.cardSubtype .dwarf]]
      [.may [.you] [.attachTo [.oneOf [.cardType .equipment, .controlledBy .you]] [.it]]]]) ==
  "Untap target creature you control. It gets +2/+2 until end of turn. If it's a Dwarf, you may attach an Equipment you control to it."

#guard shortCardName "Bilbo Baggins, Burglar" == "Bilbo Baggins"

#guard textEffectSentence "Bilbo Baggins, Burglar" (.when
    [.permanentEnter [.thisCardName]]
    [.draw 1]) ==
  "When Bilbo Baggins enters, draw a card."

#guard textEffectSentence "Take a Glance" (.scry 2) == "Scry 2."

#guard textEffectSentence "Lakeshore Apothecary" (.whenever
    [.drawCard [.you] [.ordinalEach 2 .turn]]
    [.putCounter 1 .plusOnePlusOne [.this, .cardType .creature]]) ==
  "Whenever you draw your second card each turn, put a +1/+1 counter on this creature."

#guard textEffectSentence "Ravenhill Flock" (.whenever
    [.drawCard [.you] []]
    [.putCounter 1 .plusOnePlusOne [.this, .cardType .creature]]) ==
  "Whenever you draw a card, put a +1/+1 counter on this creature."

#guard textEffectSentence "" (.whenever
    [.drawCard [.opponent] []]
    [.putCounter 1 .plusOnePlusOne [.this, .cardType .creature]]) ==
  "Whenever an opponent draws a card, put a +1/+1 counter on this creature."

#guard textEffectSentence ""
    (.unlessPay [.counter [.target [.spell]]] [.controller .it] [.mana [.generic 4]]) ==
  "Counter target spell unless its controller pays {4}."

#guard textEffectSentence "" (.sequence [.draw 2, .discard 1]) ==
  "Draw two cards, then discard a card."

#guard textEffectSentence "" (.chooseMode 1 [
    .unlessPay [.counter [.target [.spell]]] [.controller .it] [.mana [.generic 4]],
    .sequence [.draw 2, .discard 1]]) ==
  "Choose one —\n• Counter target spell unless its controller pays {4}.\n• Draw two cards, then discard a card."

#guard textEffectSentence "" (.sequence [
    .counter [.target [.spell]],
    .if
      [.counteredThisWay [.permanentSpell]]
      [.insteadOf
         [.putInto [.it] [.graveyard, .belongingTo [.owner [.it]]]]
         [.exile [.it]],
       .asLongAs
         [.mayCastSo [.you] [.thatCard] [.withoutPayingManaCost]]
         [.remains [.it] [.exiled]]]]) ==
  "Counter target spell. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled."

end Mtg.Engine
