import Mtg.Engine.Card.OracleParse.Text

/-!
# Selectors and pumps

Battlefield phrases, power and toughness changes, and the wrappers that
turn a parsed effect into a triggered ability.
-/

namespace Mtg.Engine

namespace OracleParts

def selectorOfTypes : List CardType → Selector
  | [t] => .cardType t
  | ts => .union (ts.map fun t => .cardType t)

/-- A permanent of `ts`, plus any further constraints. -/
def permanentWith (ts : List CardType) (more : List Selector := []) : Selector :=
  .intersection ([.permanent, selectorOfTypes ts] ++ more)

/-- Controlled by this object's controller (`you control`). -/
def youControl : Selector :=
  .controlled (.controller .this)

/-- `front` and `back` added around `sel`.
An intersection keeps its parts. Anything else becomes one piece of a new
intersection. -/
def extendIntersection (front : List Selector) (sel : Selector) (back : List Selector) :
    Selector :=
  match sel with
  | .intersection parts => .intersection (front ++ parts ++ back)
  | other => .intersection (front ++ [other] ++ back)

/-- `sel` among objects this object's controller controls. -/
def andYouControl (sel : Selector) : Selector :=
  extendIntersection [] sel [youControl]

/-- Equipment this object's controller controls. -/
def equipmentYouControl : Selector :=
  .intersection [.permanent, .subtype .equipment, youControl]

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
  let parts := orList s
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

/-- Static `+P/+T` parts. A zero bonus is omitted. `+0/+0` is not an effect. -/
def staticPowerToughness (sel : Selector) (p t : Int) : Option (List CardPart) :=
  let effects := flatPowerToughness sel p t
  if effects.isEmpty then none
  else some (effects.map fun e => .ability (.static e))

/-- `effects` while `cond` holds. No effects is not an ability. -/
def staticWhile (cond : Condition) (effects : List ContinuousEffect) : Option CardPart :=
  if effects.isEmpty then none
  else some (.ability (.static (.if cond effects)))

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

/-- Same as `onTrigger`, keeping the target number the effect parser returns. -/
def onTriggerN (event : Trigger) (parsed : Option (CardAction × Nat)) :
    Option (CardPart × Nat) :=
  parsed.map fun (action, n') => (.ability (.triggered event action), n')

/-- The action from a sentence parser, dropping the target number it returns. -/
def actionOf (parsed : Option (CardAction × Nat)) : Option CardAction :=
  parsed.map fun (action, _) => action

/-- `Whenever this creature attacks, it gets +1/+1 until end of turn for each
other creature you control.` -/
def parseAttackTriggered (line : String) : Option CardPart :=
  onTrigger (.attack .this .all)
    ((after? (normLine line) "whenever this creature attacks, ").bind parsePumpUntilEndOfTurn)

end OracleParts

end Mtg.Engine
