import Mtg.Engine.Card.OracleParse.Phrases

/-!
# Activation costs

Printed costs, activation limits, counters placed on this permanent, and
cost reductions that function on the stack.
-/

namespace Mtg.Engine

namespace OracleParts

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

/-- Count and object of `put <count> +1/+1 counter(s) on <who>`.
One counter uses the singular noun; more than one uses the plural. -/
def parsePutPlusOneOn? (sentence : String) : Option (Nat × String) :=
  (after? (normSentence sentence) "put ").bind fun rest =>
    let counted :=
      (split2? rest " +1/+1 counters on ").map (fun (c, w) => (c, true, w)) <|>
        (split2? rest " +1/+1 counter on ").map (fun (c, w) => (c, false, w))
    match counted with
    | some (countText, plural, who) =>
      (nounCount? countText plural).map fun k => (k, who)
    | none => none

/-- `Put a +1/+1 counter on this creature` or
`Put three +1/+1 counters on this creature`.
One counter uses the singular noun; more than one uses the plural.
`this`, `this creature`, and `it` are the source of this ability. -/
def parsePutCountersOnThis (sentence : String) : Option CardAction :=
  (parsePutPlusOneOn? sentence).bind fun (k, who) =>
    match parsePumpWho who with
    | some sel =>
      if sel == .source .this then
        some (.putCounter (.source .this) .plusOnePlusOne (.int k))
      else none
    | none => none

/-- Exile the top card of your library; you may play that card until the end
of your next turn. The exile is action `n`. -/
def exileTopPlayUntilEndOfNextTurn (n : Nat) : CardAction :=
  .sequence [
    .actionId n (.exile (.topOfLibrary (.controller .this) 1)),
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

/-- `once each turn`, including that limit combined with your turn. -/
def ActivateLimit.limitsOnce : ActivateLimit → Bool
  | .onceEachTurn | .duringYourTurnOnce => true
  | .unlimited | .duringYourTurn | .asSorcery => false

/-- `during your turn`, including that limit combined with once each turn. -/
def ActivateLimit.limitsToYourTurn : ActivateLimit → Bool
  | .duringYourTurn | .duringYourTurnOnce => true
  | .unlimited | .onceEachTurn | .asSorcery => false

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

/-- Another permanent of subtype `st` that this object's controller controls. -/
def anotherSubtypeYouControl (st : CardSubtype) : Selector :=
  .intersection [.not .this, .zone .battlefield, .subtype st, youControl]

/-- `Sacrifice another creature or artifact`: one other permanent of those
types. `Sacrifice another Goblin`: one other permanent of that subtype you
control. `another` excludes this object. -/
def parseSacrificeAnother (s : String) : Option Cost :=
  match after? (norm s) "sacrifice another " with
  | some obj =>
    match typesInPhrase obj with
    | some ts =>
      some (.sacrificeCount
        (.intersection [.not .this, .zone .battlefield, selectorOfTypes ts])
        1)
    | none =>
      (subtypeOfOracle? obj).map fun st =>
        .sacrificeCount (anotherSubtypeYouControl st) 1
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
          rest == "permanent" || rest == "spell" || rest == "token"

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

/-- `Discard a card`: this object's controller discards one card they own
from a hand (CR 701.8). -/
def discardOneCardFromHand : Cost :=
  .discard
    (.selected
      (.controller .this)
      (.range 1 1)
      (.intersection [.zone .hand, .owner (.controller .this)]))

/-- `Discard a card` as a printed cost. -/
def parseDiscardACard (s : String) : Option Cost :=
  if norm s == "discard a card" then some discardOneCardFromHand else none

/-- One printed cost: mana symbols, the tap symbol, sacrificing a permanent,
or discarding a card. -/
def parsePrintedCost (cardName s : String) : Option Cost :=
  if norm s == "{t}" then some .tapSymbol
  else
    match nonemptyMana? s with
    | some syms => some (.mana syms)
    | none =>
      parseSacrificeThis cardName s <|> parseSacrificeAn s <|>
        parseSacrificeAnother s <|> parseDiscardACard s

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
    let once := limit.limitsOnce
    let onYourTurn := limit.limitsToYourTurn
    let notYet := Condition.not (.happened (.abilityWithIdActivated n) .turnStart)
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
    some (.intersection [.zone .battlefield, .cardType .creature, .tapped])
  | "an attacking nontoken creature" =>
    some (.intersection [
      .zone .battlefield,
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
          .any (extendIntersection [] among [.isTargetOf .this])
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
      if lo <= hi then some (.range (Value.int lo) (Value.int hi)) else none
    | _, _ => none
  | none =>
    (positiveCount s).map fun n => .range (Value.int n) (Value.int n)

/-- `one, two, or three` as an inclusive contiguous range.
The numbers are positive and listed from low to high with no gaps. -/
def parseContiguousCounts (s : String) : Option (Nat × Nat) :=
  match (orList s).mapM englishSmall? with
  | none => none
  | some ns =>
    match ns with
    | [] => none
    | first :: _ =>
      let lo := ns.foldl (fun a b => Nat.min a b) first
      let hi := ns.foldl (fun a b => Nat.max a b) first
      let expected := (List.range (hi + 1)).filter (fun i => i ≥ lo)
      if ns == expected && lo > 0 then some (lo, hi) else none

end OracleParts

end Mtg.Engine
