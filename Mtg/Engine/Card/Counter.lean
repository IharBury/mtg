import Mtg.Engine.Card.Text

/-!
# Counters (CR 122)

The counter kinds a permanent can carry. `SpellResolution.countersOnCreatureTargets`
puts any one of them; `Status` stores each kind in its own field.
-/

namespace Mtg.Engine

/-- A keyword counter a permanent can have (CR 122.1b). -/
inductive KeywordCounter where
  | trample
  | indestructible
  | lifelink
  | shadow
  | haste
  | vigilance
  | flying
  | menace
  | reach
  | deathtouch
  | firstStrike
  | doubleStrike
deriving Repr, Inhabited, BEq, DecidableEq

/-- A rule-defined non-keyword counter a permanent can have (CR 122.1c–d / CR 306.5 / CR 714). -/
inductive RuleCounter where
  | loyalty
  | stun
  | shield
  | finality
  | lore
  | time
deriving Repr, Inhabited, BEq, DecidableEq

/-- A named ability or card counter a permanent can have (CR 122.1). -/
inductive NamedCounter where
  | hope
  | charge
  | plan
  | burden
  | quest
  | invasion
  | influence
  | hone
  | story
deriving Repr, Inhabited, BEq, DecidableEq

/-- A kind of counter a permanent can have (CR 122.1), grouped by CR 122 counter category. -/
inductive CounterKind where
  /-- Power/toughness counter: +1/+1 (`plus = true`) or minus-one (`plus = false`, CR 122.1a). -/
  | pt (plus : Bool := true)
  /-- Keyword counter (CR 122.1b). -/
  | keyword (k : KeywordCounter)
  /-- Rule-defined counter (loyalty, stun, shield, finality, lore, time; CR 122.1c–d / CR 306.5 / CR 714). -/
  | rule (k : RuleCounter)
  /-- Named ability or card counter (CR 122.1). -/
  | named (k : NamedCounter)
deriving Repr, Inhabited, BEq, DecidableEq

namespace CounterKind

@[match_pattern] abbrev plusOnePlusOne : CounterKind := .pt true
@[match_pattern] abbrev minusOneMinusOne : CounterKind := .pt false
@[match_pattern] abbrev loyalty : CounterKind := .rule .loyalty
@[match_pattern] abbrev hope : CounterKind := .named .hope
@[match_pattern] abbrev charge : CounterKind := .named .charge
@[match_pattern] abbrev stun : CounterKind := .rule .stun
@[match_pattern] abbrev shield : CounterKind := .rule .shield
@[match_pattern] abbrev finality : CounterKind := .rule .finality
@[match_pattern] abbrev plan : CounterKind := .named .plan
@[match_pattern] abbrev burden : CounterKind := .named .burden
@[match_pattern] abbrev quest : CounterKind := .named .quest
@[match_pattern] abbrev invasion : CounterKind := .named .invasion
@[match_pattern] abbrev influence : CounterKind := .named .influence
@[match_pattern] abbrev trample : CounterKind := .keyword .trample
@[match_pattern] abbrev indestructible : CounterKind := .keyword .indestructible
@[match_pattern] abbrev lifelink : CounterKind := .keyword .lifelink
@[match_pattern] abbrev hone : CounterKind := .named .hone
@[match_pattern] abbrev shadow : CounterKind := .keyword .shadow
@[match_pattern] abbrev lore : CounterKind := .rule .lore
@[match_pattern] abbrev story : CounterKind := .named .story
@[match_pattern] abbrev time : CounterKind := .rule .time
@[match_pattern] abbrev haste : CounterKind := .keyword .haste
@[match_pattern] abbrev vigilance : CounterKind := .keyword .vigilance
@[match_pattern] abbrev flying : CounterKind := .keyword .flying
@[match_pattern] abbrev menace : CounterKind := .keyword .menace
@[match_pattern] abbrev reach : CounterKind := .keyword .reach
@[match_pattern] abbrev deathtouch : CounterKind := .keyword .deathtouch
@[match_pattern] abbrev firstStrike : CounterKind := .keyword .firstStrike
@[match_pattern] abbrev doubleStrike : CounterKind := .keyword .doubleStrike

/-- Oracle name of this counter, without the word `counter` (`+1/+1`, `stun`,
`first strike`). -/
def oracleName : CounterKind → String
  | .plusOnePlusOne => "+1/+1"
  | .minusOneMinusOne => "-1/-1"
  | .loyalty => "loyalty"
  | .hope => "hope"
  | .charge => "charge"
  | .stun => "stun"
  | .shield => "shield"
  | .finality => "finality"
  | .plan => "plan"
  | .burden => "burden"
  | .quest => "quest"
  | .invasion => "invasion"
  | .influence => "influence"
  | .trample => "trample"
  | .indestructible => "indestructible"
  | .lifelink => "lifelink"
  | .hone => "hone"
  | .shadow => "shadow"
  | .lore => "lore"
  | .story => "story"
  | .time => "time"
  | .haste => "haste"
  | .vigilance => "vigilance"
  | .flying => "flying"
  | .menace => "menace"
  | .reach => "reach"
  | .deathtouch => "deathtouch"
  | .firstStrike => "first strike"
  | .doubleStrike => "double strike"

/-- Every counter kind, in constructor order. -/
def all : List CounterKind := [
  .plusOnePlusOne, .minusOneMinusOne, .loyalty, .hope, .charge, .stun, .shield,
  .finality, .plan, .burden, .quest, .invasion, .influence, .trample,
  .indestructible, .lifelink, .hone, .shadow, .lore, .story, .time, .haste,
  .vigilance, .flying, .menace, .reach, .deathtouch, .firstStrike, .doubleStrike
]

private def words (s : String) : List String :=
  s.splitOn " " |>.filter (· != "")

/-- English for putting `n` counters of this kind (`a stun counter`,
`two` is printed as a digit: `2 shield counters`). -/
def countersPhrase (kind : CounterKind) (n : Nat) : String :=
  let name := kind.oracleName
  if n == 1 then s!"{indefinite name} {name} counter" else s!"{n} {name} counters"

/-- Longest kind name at the front of `toks`. -/
def ofPrefix (toks : List String) : Option (CounterKind × Nat) :=
  all.foldl (fun best k =>
    let name := words k.oracleName
    if name.isPrefixOf toks then
      match best with
      | none => some (k, name.length)
      | some (_, n) => if name.length > n then some (k, name.length) else best
    else best) none

/-- `a`/`an`/`N` plus a counter name plus `counter` or `counters`.
The third component is how many tokens were consumed. -/
def matchPhrase (toks : List String) : Option (Nat × CounterKind × Nat) :=
  match toks with
  | article :: rest =>
    let counted : Option (Nat × List String) :=
      if article == "a" || article == "an" then some (1, rest)
      else if !article.isEmpty && article.all Char.isDigit then some (article.toNat!, rest)
      else none
    match counted with
    | none => none
    | some (n, afterCount) =>
      match ofPrefix afterCount with
      | none => none
      | some (k, nameLen) =>
        match afterCount.drop nameLen with
        | word :: _ =>
          if word == "counter" || word == "counters" then
            some (n, k, 1 + nameLen + 1)
          else none
        | [] => none
  | [] => none

#guard (.plusOnePlusOne : CounterKind).countersPhrase 1 == plusOnePlusOneCountersPhrase 1
#guard (.plusOnePlusOne : CounterKind).countersPhrase 3 == plusOnePlusOneCountersPhrase 3
#guard (.stun : CounterKind).countersPhrase 1 == "a stun counter"
#guard (.shield : CounterKind).countersPhrase 2 == "2 shield counters"
#guard (.indestructible : CounterKind).countersPhrase 1 == "an indestructible counter"
#guard (.firstStrike : CounterKind).countersPhrase 1 == "a first strike counter"
#guard (.minusOneMinusOne : CounterKind).countersPhrase 1 == "a -1/-1 counter"

#guard all.all fun k =>
  match matchPhrase (words (k.countersPhrase 1)) with
  | some (1, k', _) => k' == k
  | _ => false

#guard all.all fun k =>
  match matchPhrase (words (k.countersPhrase 4)) with
  | some (4, k', _) => k' == k
  | _ => false

#guard matchPhrase ["counter", "target", "spell"] == none
#guard matchPhrase ["a", "target", "creature"] == none

end CounterKind

end Mtg.Engine
