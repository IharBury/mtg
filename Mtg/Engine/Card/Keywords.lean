import Mtg.Engine.TypeLine

/-!
# Keyword abilities (CR 702)

The keyword flags a card can carry, the merge/print helpers, and the
single-keyword `Keyword.*` values. `Keyword.amass` and `Keyword.connive`
take a `Value`, `Range.range` takes `Value` bounds, and `Selector` names
both, so `Keyword`, `Value`, `Range`, `Selector`, and `Trigger` are
mutual.
-/

namespace Mtg.Engine

/-- Keyword abilities that the engine currently understands. -/
structure Keywords where
  flash : Bool := false
  haste : Bool := false
  vigilance : Bool := false
  flying : Bool := false
  /-- This creature can't be blocked. Not a CR 702 keyword; printed as
  `.ability (.static (.forbid (.block .any .this)))` and also granted
  until end of turn. -/
  cantBeBlocked : Bool := false
  /-- This creature can't be blocked except by two or more creatures (CR 702.111). -/
  menace : Bool := false
  hexproof : Bool := false
  indestructible : Bool := false
  reach : Bool := false
  trample : Bool := false
  deathtouch : Bool := false
  defender : Bool := false
  /-- Damage this source deals causes its controller to gain that much life (CR 702.15). -/
  lifelink : Bool := false
  /-- This creature deals combat damage before creatures without first strike
  (CR 702.7). -/
  firstStrike : Bool := false
  /-- This creature can't be blocked as long as the defending player controls
  an Island (CR 702.14). -/
  islandwalk : Bool := false
  /-- Storied (HOB): if you control three or more artifacts, legendaries,
  and/or Sagas, you have an enduring story for the rest of the game. -/
  storied : Bool := false
  /-- This creature deals both first-strike and regular combat damage (CR 702.4). -/
  doubleStrike : Bool := false
  /-- Prowess (CR 702.108). -/
  prowess : Bool := false
  /-- Ascend (CR 702.131). -/
  ascend : Bool := false
  /-- Shadow (CR 702.27): can block or be blocked by only creatures with shadow. -/
  shadow : Bool := false
  /-- Changeling (CR 702.72): this object has all creature types. -/
  changeling : Bool := false
deriving BEq, Repr, Inhabited

namespace Keywords

def none : Keywords := {}

/-- One modeled keyword: how to read it, write it, and print its Oracle name.
`merge` and `toList` fold this table so a new keyword is one row here plus a
field on `Keywords` and a `Keyword.*` value. -/
structure Field where
  get : Keywords → Bool
  set : Keywords → Bool → Keywords
  name : String

def fields : List Field := [
  ⟨(·.flash), fun k b => { k with flash := b }, "flash"⟩,
  ⟨(·.haste), fun k b => { k with haste := b }, "haste"⟩,
  ⟨(·.vigilance), fun k b => { k with vigilance := b }, "vigilance"⟩,
  ⟨(·.flying), fun k b => { k with flying := b }, "flying"⟩,
  ⟨(·.cantBeBlocked), fun k b => { k with cantBeBlocked := b }, "can't be blocked"⟩,
  ⟨(·.menace), fun k b => { k with menace := b }, "menace"⟩,
  ⟨(·.hexproof), fun k b => { k with hexproof := b }, "hexproof"⟩,
  ⟨(·.indestructible), fun k b => { k with indestructible := b }, "indestructible"⟩,
  ⟨(·.reach), fun k b => { k with reach := b }, "reach"⟩,
  ⟨(·.trample), fun k b => { k with trample := b }, "trample"⟩,
  ⟨(·.deathtouch), fun k b => { k with deathtouch := b }, "deathtouch"⟩,
  ⟨(·.defender), fun k b => { k with defender := b }, "defender"⟩,
  ⟨(·.lifelink), fun k b => { k with lifelink := b }, "lifelink"⟩,
  ⟨(·.firstStrike), fun k b => { k with firstStrike := b }, "first strike"⟩,
  ⟨(·.islandwalk), fun k b => { k with islandwalk := b }, "islandwalk"⟩,
  ⟨(·.storied), fun k b => { k with storied := b }, "storied"⟩,
  ⟨(·.doubleStrike), fun k b => { k with doubleStrike := b }, "double strike"⟩,
  ⟨(·.prowess), fun k b => { k with prowess := b }, "prowess"⟩,
  ⟨(·.ascend), fun k b => { k with ascend := b }, "ascend"⟩,
  ⟨(·.shadow), fun k b => { k with shadow := b }, "shadow"⟩,
  ⟨(·.changeling), fun k b => { k with changeling := b }, "changeling"⟩
]

/-- Union of two keyword sets (printed or granted). -/
def merge (a b : Keywords) : Keywords :=
  fields.foldl (fun acc f => f.set acc (f.get a || f.get b)) none

/-- Union of every keyword set in `ks`. -/
def mergeAll (ks : Array Keywords) : Keywords :=
  ks.foldl merge none

/-- `name` when `b` is true, otherwise nothing. -/
def flag (b : Bool) (name : String) : List String :=
  if b then [name] else []

def toList (k : Keywords) : List String :=
  fields.foldl (fun acc f => acc ++ flag (f.get k) f.name) []

/-- Oracle-style keyword list for ability sentences: one keyword prints as
itself, two join with `and`, more join with commas. Sites whose printed
wording orders keywords differently special-case before falling back here. -/
def joinedAnd (k : Keywords) : String :=
  match k.toList with
  | [a, b] => s!"{a} and {b}"
  | ks => String.intercalate ", " ks

instance : ToString Keywords where
  toString k :=
    let ks := k.toList
    if ks.isEmpty then "" else String.intercalate ", " ks

end Keywords

/-- A constraint on a set of selected objects, not on each object alone. -/
inductive SetPredicate where
  /-- The objects share a card type with each other. -/
  | shareCardType
  /-- The set contains at least this many objects. -/
  | countAtLeast : Nat → SetPredicate
deriving Repr, Inhabited, BEq

/-- Kind of counter (CR 122.1). Used by `CardAction.putCounter` and
`Trigger.putCountersSimultaneously`. -/
inductive CounterKind where
  /-- A +1/+1 counter. -/
  | plusOnePlusOne
deriving Repr, Inhabited, BEq

-- `Keyword.amass` / `Keyword.connive` take a `Value`, `Value` names a
-- `Selector`, a `Selector` may name a `Keyword` or a `Range`, and
-- `Range.range` takes `Value` bounds, so these five inductives are
-- mutual. Triggers name selectors, and selectors may ask who was the
-- subject of a trigger.
mutual
/-- One modeled keyword ability (CR 702). Coerces to a `Keywords` singleton
so existing `keywords := Keyword.lifelink` call sites keep working. -/
inductive Keyword where
  | flash
  | haste
  | vigilance
  | flying
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
  /-- Equip (CR 702.6): printed with a cost, e.g. Equip {2}. -/
  | equip
  /-- Enchant (CR 702.5): printed with a target, e.g. Enchant creature. -/
  | enchant
  /-- Typecycling (CR 702.29): printed with a cost, e.g. Halflingcycling {4}
  or Basic landcycling {2}. -/
  | typecycling : List CardSupertype → List CardType → List CardSubtype → Keyword
  /-- Recruit (HOB keyword action): draw, then discard; if a nonland was
  discarded, create a 1/1 white Human Soldier creature token. -/
  | recruit
  /-- Amass <subtype> N (CR 701.45): put N +1/+1 counters on an Army you
  control. It's also the given subtype. If you don't control an Army,
  create a 0/0 black Army creature token of that subtype first. -/
  | amass : CardSubtype → Value → Keyword
  /-- Connive N (CR 701.48): draw N cards, then discard N cards. For each
  nonland card discarded this way, put a +1/+1 counter on the conniving
  creature. Printed “connives” is connive 1. -/
  | connive : Value → Keyword
  /-- A Saga chapter ability (CR 714.2), numbered from I. Printed with
  `Ability.keywordWithEffect`. -/
  | chapter : Nat → Keyword
deriving Repr, Inhabited, BEq

/-- A number that is either a printed constant or computed from game
state. -/
inductive Value where
  /-- A printed natural-number amount. -/
  | nat : Nat → Value
  /-- A printed integer amount. -/
  | int : Int → Value
  /-- The value of X (CR 107.3). -/
  | x : Value
  /-- The greatest mana value among selected objects (CR 202.3). -/
  | greatestManaValue : Selector → Value
  /-- The greatest toughness among selected objects (CR 208). -/
  | greatestToughness : Selector → Value
  /-- The greatest power among selected objects (CR 208). -/
  | greatestPower : Selector → Value
deriving Repr, Inhabited, BEq

/-- How many objects a `.targets` selector may choose. -/
inductive Range where
  | range : Value → Value → Range
deriving Repr, Inhabited, BEq

/-- Whom or what a spell or ability refers to (CR 109.5 / 113.7 / 115.1). -/
inductive Selector where
  /-- This spell or ability (CR 113.7). -/
  | this
  /-- The source of the given object (CR 113.7). -/
  | source : Selector → Selector
  /-- The controller of the given object (CR 109.5). -/
  | controller : Selector → Selector
  /-- A numbered target matching the given selector (CR 115.1). Later
  effects may refer to it with `targetReference`. The number is unique
  within a `TraditionalCardDefinition`, including `targets` /
  `targetSet`. -/
  | target : Nat → Selector → Selector
  /-- Numbered targets matching the given selector, with a count range.
  The number is unique within a `TraditionalCardDefinition`, including
  `target` / `targetSet`. -/
  | targets : Nat → Range → Selector → Selector
  /-- Numbered targets matching the given selector, with a count range
  and extra constraints that apply to the set as a whole. The number is
  unique within a `TraditionalCardDefinition`, including `target` /
  `targets`. -/
  | targetSet : Nat → Range → Selector → List SetPredicate → Selector
  /-- Objects that do not match the given selector. -/
  | not : Selector → Selector
  /-- The target previously declared with `target`, `targets`, or
  `targetSet` of this number. -/
  | targetReference : Nat → Selector
  /-- The given player chooses objects matching the given selector at
  resolution, with a count range (not targeting; CR 608.2d). -/
  | selected : Selector → Range → Selector → Selector
  | intersection : List Selector → Selector
  | all
  | cardType : CardType → Selector
  | union : List Selector → Selector
  /-- A permanent (CR 110.1). -/
  | permanent
  /-- Objects whose controller is the given player. -/
  | controlled : Selector → Selector
  /-- A tapped permanent (CR 110.5). -/
  | tapped
  /-- An object with the given keyword (CR 702). -/
  | keyword : Keyword → Selector
  /-- A keyword ability of the given keyword (CR 702). -/
  | keywordAbility : Keyword → Selector
  /-- Objects with power at least this value (CR 208). -/
  | powerAtLeast : Value → Selector
  /-- Printed subtype (CR 205.3). -/
  | subtype : CardSubtype → Selector
  /-- A spell on the stack (CR 112.1). -/
  | spell
  /-- A permanent spell (CR 110.4 / 112.1). -/
  | permanentSpell
  /-- An object that has a target matching the given selector (CR 115.1). -/
  | hasTarget : Selector → Selector
  /-- An object that is a target of the given object (CR 115.1). -/
  | isTargetOf : Selector → Selector
  /-- A player (CR 102). -/
  | player
  /-- Opponents of the given player (CR 102.2). -/
  | opponent : Selector → Selector
  /-- The owner of the given object (CR 108.3). -/
  | owner : Selector → Selector
  /-- A permanent attacking objects matching the given selector (CR 508). -/
  | attacking : Selector → Selector
  /-- Permanents blocking the given permanents (CR 509). -/
  | blocking : Selector → Selector
  /-- A token (CR 111.1). -/
  | token
  /-- The object of the numbered action. -/
  | wasObjectOfAction : Nat → Selector
  /-- The object of this triggered ability. -/
  | wasObjectOfThisTrigger
  /-- The object a replacement effect is replacing. -/
  | replacingObject : Selector
  /-- An object created by the numbered action. -/
  | wasCreatedByAction : Nat → Selector
  /-- The permanent the given object is attached to (CR 301.5 / 303.4). -/
  | hostOf : Selector → Selector
  /-- An object in a graveyard (CR 404). -/
  | inGraveyard
  /-- An object that was the object of the first event since the second
  event. -/
  | wasObjectSince : Trigger → Trigger → Selector
  /-- An object in a library (CR 401). -/
  | inLibrary
  /-- An object in a hand (CR 402). -/
  | inHand
  /-- An object in exile (CR 406). -/
  | inExile
  /-- Objects with the given supertype (CR 205.4). -/
  | supertype : CardSupertype → Selector
  /-- Objects bound to this numbered variable. -/
  | variable : Nat → Selector
  /-- The top card of the selected player's library (CR 401). -/
  | topOfLibrary : Selector → Selector
deriving Repr, Inhabited, BEq

/-- When a continuous effect ends, when a triggered ability fires, or
what a replacement effect intercepts. -/
inductive Trigger where
  | endOfGame
  | endOfTurn
  /-- At the end of the selected player's turn (CR 514.3). -/
  | endOfPlayerTurn : Selector → Trigger
  /-- At the beginning of combat on the selected player's turn (CR 507.1). -/
  | combatStart : Selector → Trigger
  /-- From the start of the turn (a window bound for `happened`). -/
  | turnStart
  /-- From the start of the game (a window bound for `happened`). -/
  | gameStart
  /-- Whenever the selected object attacks, restricted by the given
  selector. -/
  | attack : Selector → Selector → Trigger
  /-- When the selected object enters. -/
  | enter : Selector → Trigger
  /-- Whenever the selected player draws a card matching the given
  selector. -/
  | draw : Selector → Selector → Trigger
  /-- The nth occurrence of the inner trigger, counted from the given
  window. -/
  | ordinal : Nat → Trigger → Trigger → Trigger
  /-- Whenever the selected object deals combat damage to objects matching
  the given selector. -/
  | combatDamage : Selector → Selector → Trigger
  /-- Whenever the selected object would deal damage to objects matching
  the given selector (CR 120). -/
  | damage : Selector → Selector → Trigger
  /-- The selected object would be put into a graveyard (CR 614). -/
  | putToGraveyard : Selector → Trigger
  /-- Whenever a matching card leaves a graveyard (CR 404). -/
  | leaveGraveyard : Selector → Trigger
  /-- Whenever the selected object is returned to its owner's hand. -/
  | returnToHand : Selector → Trigger
  /-- Whenever the selected player discards a card (CR 701.8). -/
  | discard : Selector → Trigger
  /-- When one or more counters of the given kind are put on the selected
  objects at the same time (CR 122). -/
  | putCountersSimultaneously : Selector → CounterKind → Trigger
  /-- The first selector blocks the second (CR 509). -/
  | block : Selector → Selector → Trigger
  /-- When the selected object or objects die (CR 700.4). -/
  | die : Selector → Trigger
  /-- When objects matching the selector die at the same time, with
  set-wide predicates (CR 700.4 / 603.2d). -/
  | dieSimultaneously : Selector → List SetPredicate → Trigger
  /-- Whenever objects matching the first selector attack objects matching
  the second at the same time, with set-wide predicates
  (CR 508.3 / 603.2d). -/
  | attackSimultaneously : Selector → Selector → List SetPredicate → Trigger
  /-- The numbered ability was activated (CR 602.2). -/
  | abilityWithIdActivated : Nat → Trigger
  /-- The numbered action occurred. -/
  | actionWithId : Nat → Trigger
  /-- The selected player chose the numbered mode (CR 700.2). -/
  | modeWithIdChosen : Selector → Nat → Trigger
  /-- Mana created by the numbered action is spent to pay for the given
  event (CR 106.10). -/
  | spendManaCreatedByAction : Nat → Trigger → Trigger
  /-- A spell matching the selector is cast (CR 601). -/
  | castSpell : Selector → Trigger
  /-- An activated ability of a source matching the selector is activated
  (CR 602). -/
  | activateAbility : Selector → Trigger
  /-- After the listed triggers have occurred in order. -/
  | sequence : List Trigger → Trigger
  /-- The given trigger does not occur. -/
  | not : Trigger → Trigger
  /-- Either trigger occurs. -/
  | or : Trigger → Trigger → Trigger
deriving Repr, Inhabited, BEq
end

namespace Value

instance : ToString Value where
  toString
    | .nat n => toString n
    | .int n => toString n
    | .x => "X"
    | .greatestManaValue _ | .greatestToughness _ | .greatestPower _ => "X"

instance (n : Nat) : OfNat Value n where
  ofNat := .nat n

#guard toString (Value.nat 3) == "3"
#guard toString (Value.int (-2)) == "-2"
#guard toString Value.x == "X"
#guard toString (Value.greatestManaValue .this) == "X"
#guard toString (Value.greatestToughness .this) == "X"
#guard toString (Value.greatestPower .this) == "X"
#guard (1 : Value) == Value.nat 1
#guard Value.x != Value.nat 1

end Value

namespace Range

#guard Range.range 0 1 == .range (Value.nat 0) (Value.nat 1)
#guard Range.range Value.x 1 != Range.range 0 1

end Range

namespace Keyword

/-- The type-line phrase a typecycling ability searches for, e.g. `Halfling`
or `Basic land`. -/
def typecyclingPhrase (supertypes : List CardSupertype) (types : List CardType)
    (subtypes : List CardSubtype) : String :=
  String.intercalate " "
    (supertypes.map toString ++
      types.map (fun t => t.englishName.toLower) ++
      subtypes.map toString)

/-- Singleton `Keywords` value for this keyword. -/
def toKeywords : Keyword → Keywords
  | .flash => { Keywords.none with flash := true }
  | .haste => { Keywords.none with haste := true }
  | .vigilance => { Keywords.none with vigilance := true }
  | .flying => { Keywords.none with flying := true }
  | .menace => { Keywords.none with menace := true }
  | .hexproof => { Keywords.none with hexproof := true }
  | .indestructible => { Keywords.none with indestructible := true }
  | .reach => { Keywords.none with reach := true }
  | .trample => { Keywords.none with trample := true }
  | .deathtouch => { Keywords.none with deathtouch := true }
  | .defender => { Keywords.none with defender := true }
  | .lifelink => { Keywords.none with lifelink := true }
  | .firstStrike => { Keywords.none with firstStrike := true }
  | .islandwalk => { Keywords.none with islandwalk := true }
  | .storied => { Keywords.none with storied := true }
  | .doubleStrike => { Keywords.none with doubleStrike := true }
  | .prowess => { Keywords.none with prowess := true }
  | .ascend => { Keywords.none with ascend := true }
  | .shadow => { Keywords.none with shadow := true }
  | .changeling => { Keywords.none with changeling := true }
  | .equip | .enchant | .typecycling _ _ _ | .recruit | .amass _ _
  | .connive _ | .chapter _ =>
    Keywords.none

/-- Union of two single keywords. -/
def merge (a b : Keyword) : Keywords :=
  a.toKeywords.merge b.toKeywords

instance : Coe Keyword Keywords where
  coe := toKeywords

instance : ToString Keyword where
  toString
    | .typecycling supertypes types subtypes =>
      s!"{typecyclingPhrase supertypes types subtypes}cycling"
    | .recruit => "recruit"
    | .amass st n => s!"amass {st}s {n}"
    | .connive n => s!"connive {n}"
    | .chapter n =>
      let roman :=
        match n with
        | 1 => "I"
        | 2 => "II"
        | 3 => "III"
        | 4 => "IV"
        | 5 => "V"
        | 6 => "VI"
        | n => toString n
      s!"chapter {roman}"
    | k => toString k.toKeywords

end Keyword

end Mtg.Engine
