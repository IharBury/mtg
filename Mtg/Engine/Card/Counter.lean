import Mtg.Engine.Card.Text

/-!
# Counters (CR 122)

The counter kinds a permanent can carry. `SpellResolution.countersOnCreatureTargets`
puts any one of them; `Status` stores each kind in its own field.
-/

namespace Mtg.Engine

/-- A kind of counter a permanent can have (CR 122.1). Keyword counters other
than trample, lifelink, and indestructible share `KeywordCounters`. -/
inductive CounterKind where
  | plusOnePlusOne
  | minusOneMinusOne
  | loyalty
  | hope
  | charge
  | stun
  | shield
  | finality
  | plan
  | burden
  | quest
  | invasion
  | influence
  | trample
  | indestructible
  | lifelink
  | hone
  | shadow
  | lore
  | story
  | time
  | haste
  | vigilance
  | flying
  | menace
  | reach
  | deathtouch
  | firstStrike
  | doubleStrike
deriving Repr, Inhabited, BEq, DecidableEq

namespace CounterKind

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
