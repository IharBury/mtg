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
  /-- The objects' total power is at least this number.
  Checked when the simultaneous event happens, so the ability does not
  trigger when the total is lower. Power after that event does not count. -/
  | totalPowerAtLeast : Nat → SetPredicate
deriving Repr, Inhabited, BEq

/-- Kind of counter (CR 122.1). Used by `CardAction.putCounter` and
`Trigger.putCountersSimultaneously`. Each printed counter name in the
supported catalog is its own constructor. Lore counters are Saga chapters
(`Keyword.chapter`). -/
inductive CounterKind where
  /-- A +1/+1 counter. -/
  | plusOnePlusOne
  /-- A burden counter. -/
  | burden
  /-- A deathtouch counter (CR 122.1b). -/
  | deathtouch
  /-- A double strike counter (CR 122.1b). -/
  | doubleStrike
  /-- A finality counter. -/
  | finality
  /-- A first strike counter (CR 122.1b). -/
  | firstStrike
  /-- A flying counter (CR 122.1b). -/
  | flying
  /-- A haste counter (CR 122.1b). -/
  | haste
  /-- A hone counter. -/
  | hone
  /-- A hope counter. -/
  | hope
  /-- An indestructible counter (CR 122.1b). -/
  | indestructible
  /-- An influence counter. -/
  | influence
  /-- An invasion counter. -/
  | invasion
  /-- A lifelink counter (CR 122.1b). -/
  | lifelink
  /-- A menace counter (CR 122.1b). -/
  | menace
  /-- A plan counter. -/
  | plan
  /-- A quest counter. -/
  | quest
  /-- A reach counter (CR 122.1b). -/
  | reach
  /-- A shadow counter (CR 122.1b). -/
  | shadow
  /-- A shield counter. -/
  | shield
  /-- A stun counter. -/
  | stun
  /-- A trample counter (CR 122.1b). -/
  | trample
  /-- A vigilance counter (CR 122.1b). -/
  | vigilance
deriving Repr, Inhabited, BEq

/-- The gift a spell may promise an opponent (CR 702.174d–i). -/
inductive Gift where
  /-- The chosen player creates a Food token (CR 702.174d). -/
  | food
  /-- The chosen player draws a card (CR 702.174e). -/
  | card
  /-- The chosen player creates a tapped 1/1 blue Fish (CR 702.174f). -/
  | tappedFish
  /-- The chosen player takes an extra turn after this one (CR 702.174g). -/
  | extraTurn
  /-- The chosen player creates a Treasure token (CR 702.174h). -/
  | treasure
  /-- The chosen player creates an 8/8 blue Octopus (CR 702.174i). -/
  | octopus
deriving Repr, Inhabited, BEq

/-- Printed phrase for a gift, keyword word first. -/
def Gift.phrase : Gift → String
  | .food => "gift a Food"
  | .card => "gift a card"
  | .tappedFish => "gift a tapped Fish"
  | .extraTurn => "gift an extra turn"
  | .treasure => "gift a Treasure"
  | .octopus => "gift an Octopus"

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
  /-- Behold a subtype (CR 701.4): reveal a card of that subtype from your
  hand or choose a permanent you control of that subtype. Printed
  `behold an Elf`. “If a [quality] was beheld” is whether this action
  happened (CR 701.4b). -/
  | behold : CardSubtype → Keyword
  /-- A Saga chapter ability (CR 714.2), numbered from I. Printed with
  `Ability.keywordWithEffect`. -/
  | chapter : Nat → Keyword
  /-- Flashback (CR 702.34): printed with a cost, e.g. Flashback {4}{W}.
  The card may be cast from a graveyard for that cost, then is exiled. -/
  | flashback
  /-- Ward (CR 702.21): printed with a cost, e.g. Ward {2}. -/
  | ward
  /-- Crew N (CR 702.122): tap that many creatures you control. This permanent
  becomes an artifact creature until end of turn. The number is not a mana cost. -/
  | crew : Nat → Keyword
  /-- Teamwork N (CR 702.194): as an additional cost to cast this spell, you
  may tap any number of creatures you control with total power N or more.
  The number is not a mana cost. -/
  | teamwork : Nat → Keyword
  /-- Improvise (CR 702.126): each artifact tapped after mana abilities are
  activated pays for {1}. -/
  | improvise
  /-- Kicker (CR 702.32): you may pay an additional cost as you cast this
  spell. Printed with that cost, e.g. Kicker {2}{W}, via `keywordWithCost`. -/
  | kicker
  /-- Affinity for the given card types and subtypes (CR 702.40). This spell
  costs {1} less to cast for each permanent of those characteristics its
  controller controls. Types print in the plural (`artifacts`); subtypes
  print as their English plural (`Elves`). -/
  | affinity : List CardType → List CardSubtype → Keyword
  /-- Boast: activate only if this creature attacked this turn and only once
  each turn. -/
  | boast
  /-- Cascade: when you cast this spell, exile cards from the top of your
  library until you exile a nonland card that costs less. You may cast that
  card without paying its mana cost. Each printed instance is one ability. -/
  | cascade
  /-- Extort (CR 702.83): whenever you cast a spell, you may pay {W/B}. If you
  do, each opponent loses 1 life and you gain that much life. -/
  | extort
  /-- Sneak: you may cast this spell for its sneak cost if you also return an
  unblocked attacker you control to its owner's hand during the declare
  blockers step. It enters tapped and attacking. Printed with that cost,
  e.g. Sneak {1}{B}{B}, via `keywordWithCost`. -/
  | sneak
  /-- Gift (CR 702.174): as an additional cost to cast this spell, you may
  promise the listed gift to an opponent. If you do, that opponent gets the
  gift when this instant or sorcery begins resolving, before its other
  effects, or when this permanent enters. Printed as `Gift a Food`,
  `Gift a card`, `Gift a tapped Fish`, `Gift an extra turn`,
  `Gift a Treasure`, or `Gift an Octopus`. -/
  | gift : Gift → Keyword
  /-- Harness (CR 701.64): a keyword action. “Harness [this permanent]”
  means “If this permanent isn’t harnessed, it becomes harnessed.”
  Harnessed is a designation, not a copiable value, and it lasts until
  the permanent leaves the battlefield. Printed as the effect of an
  activated ability, e.g. `{5}{W}, {T}: Harness The Mind Stone`. -/
  | harness
  /-- ∞ (Infinity) (CR 702.186): a keyword ability. “∞ — [Ability]” means
  “As long as this permanent is harnessed, it has [ability].” Printed
  with that ability via `Ability.keywordWithAbility`. -/
  | infinity
deriving Repr, Inhabited, BEq

/-- A number that is either a printed constant or computed from game
state. -/
inductive Value where
  /-- A printed integer amount. A natural number is a non-negative integer. -/
  | int : Int → Value
  /-- The value of X (CR 107.3). -/
  | x : Value
  /-- The greatest mana value among selected objects (CR 202.3). -/
  | greatestManaValue : Selector → Value
  /-- The greatest toughness among selected objects (CR 208). -/
  | greatestToughness : Selector → Value
  /-- The greatest power among selected objects (CR 208). -/
  | greatestPower : Selector → Value
  /-- The number of objects matching the selector. -/
  | count : Selector → Value
  /-- The total power of objects matching the selector (CR 208). -/
  | totalPower : Selector → Value
  /-- The product of two values. -/
  | product : Value → Value → Value
  /-- The value recorded by `defineValueVariable` with this number.
  The record is the value when that action resolved. -/
  | variable : Nat → Value
  /-- The greatest amount of mana spent to cast a spell among selected
  spells (CR 601.2h). Cost increases, reductions, and alternative costs
  change each amount. A spell's mana value does not. One spell is that
  amount. Several spells use the greatest. -/
  | greatestManaSpent : Selector → Value
  /-- Excess damage dealt by the numbered action (CR 120.4a). -/
  | excessDamageOfActionWithId : Nat → Value
deriving Repr, Inhabited, BEq

/-- How many objects a `.targets` selector may choose. -/
inductive Range where
  /-- Inclusive lower and upper bounds. -/
  | range : Value → Value → Range
  /-- Any number of objects (0 to unbounded). -/
  | any : Range
  /-- At least this many objects (unbounded high bound). -/
  | from : Value → Range
deriving Repr, Inhabited, BEq

/-- A zone named in Oracle text, without a player (CR 400.1).
`your hand` is the hand of this object's controller. -/
inductive ZoneKind where
  | library
  | hand
  | battlefield
  | graveyard
  | stack
  | exile
  | command
deriving Repr, Inhabited, BEq

/-- Whom or what a spell or ability refers to (CR 109.5 / 113.7 / 115.1). -/
inductive Selector where
  /-- This spell or ability (CR 113.7). -/
  | this
  /-- The source of the given object (CR 113.7). -/
  | source : Selector → Selector
  /-- The controller of the given object (CR 109.5). -/
  | controller : Selector → Selector
  /-- The player who would cast this spell. Not necessarily its controller
  or owner (CR 601.2 / 109.5). -/
  | caster
  /-- A numbered target matching the given selector (CR 115.1). Later
  effects may refer to it with `targetReference`. The number is unique
  within a `TraditionalCardDefinition`, including `targets` /
  `targetSet`. Action ids are a separate sequence. -/
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
  /-- An object in the named zone (CR 400.1). `.battlefield` is a permanent
  (CR 110.1). -/
  | zone : ZoneKind → Selector
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
  /-- Objects with power at most this value (CR 208). -/
  | powerAtMost : Value → Selector
  /-- An object with a counter of the given kind (CR 122). -/
  | hasCounter : CounterKind → Selector
  /-- Printed subtype (CR 205.3). -/
  | subtype : CardSubtype → Selector
  /-- A spell on the stack (CR 112.1). -/
  | spell
  /-- An ability on the stack (CR 113 / 115.1). -/
  | ability
  /-- The ability numbered by `Ability.abilityId`. “This ability” is that
  ability, not the card it is printed on. -/
  | abilityWithId : Nat → Selector
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
  /-- A selector argument of the trigger numbered by `Trigger.triggerId`.
  The first `Nat` is the selector id. The second is the trigger argument
  ordinal; `1` is the first selector argument. -/
  | wasArgumentOfTrigger : Nat → Nat → Selector
  /-- The object a replacement effect is replacing. -/
  | replacingObject : Selector
  /-- An object created by the numbered action. -/
  | wasCreatedByAction : Nat → Selector
  /-- An object affected by the numbered action. Moving a card onto the
  battlefield makes a new object (CR 400.7). This is that permanent.
  A selector variable bound to the card before the move still names the
  object that left its previous zone. -/
  | affectedByAction : Nat → Selector
  /-- The permanent the given object is attached to (CR 301.5 / 303.4). -/
  | hostOf : Selector → Selector
  /-- An object that was the object of the first event since the second
  event. -/
  | wasObjectSince : Trigger → Trigger → Selector
  /-- Objects with the given supertype (CR 205.4). -/
  | supertype : CardSupertype → Selector
  /-- Objects bound to this numbered variable. -/
  | variable : Nat → Selector
  /-- The top cards of the selected player's library (CR 401). The value is
  how many. One is the top card. -/
  | topOfLibrary : Selector → Value → Selector
  /-- Objects of the creature type chosen by the numbered
  `CardAction.chooseCreatureType` action (CR 205.3m / 607.2d). -/
  | hasCreatureTypeChosenByAction : Nat → Selector
  /-- Objects whose mana value is at most this value (CR 202.3). -/
  | manaValueAtMost : Value → Selector
  /-- This spell was cast from the named zone (CR 601.2).
  `.hand` is “from your hand”. `.not (.castFromZone .hand)` is “from
  anywhere other than your hand”. -/
  | castFromZone : ZoneKind → Selector
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
  /-- At the beginning of the selected player's upkeep (CR 503.1). -/
  | upkeep : Selector → Trigger
  /-- At the beginning of the selected player's end step (CR 513.1). -/
  | endStep : Selector → Trigger
  /-- At the beginning of the selected player's draw step (CR 504.1).
  A window for the cards drawn in that step. -/
  | drawStep : Selector → Trigger
  /-- From the start of the turn (a window bound for `happened`). -/
  | turnStart
  /-- From the start of the game (a window bound for `happened`). -/
  | gameStart
  /-- Whenever the selected object attacks, restricted by the given
  selector. -/
  | attack : Selector → Selector → Trigger
  /-- When the selected object enters. -/
  | enter : Selector → Trigger
  /-- When one or more objects matching the selector enter at the same time,
  with set-wide predicates (CR 603.2c). One trigger for that group.
  `Trigger.enter` fires once per object. -/
  | enterSimultaneously : Selector → List SetPredicate → Trigger
  /-- Tokens matching the selector would be created (CR 111). One event for
  that creation. `replace` of this trigger replaces it (CR 614).
  `Selector.replacingObject` is those tokens. -/
  | createTokens : Selector → Trigger
  /-- A triggered ability of a source matching the selector triggers
  (CR 603.2). `replace` of this trigger replaces that triggering.
  `duplicateReplacingTrigger` makes that ability trigger the given number
  of times instead of once. -/
  | abilityTriggers : Selector → Trigger
  /-- Whenever the selected player draws a card matching the given
  selector. `replace` of this trigger is “if that player would draw” that
  card (CR 614). `Selector.all` is any card. -/
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
  /-- When one or more objects matching the first selector deal damage to
  objects matching the second at the same time, with set-wide predicates
  (CR 120 / 603.2c). One trigger for that simultaneous damage. Combat
  damage and noncombat damage both count. -/
  | damageSimultaneously : Selector → Selector → List SetPredicate → Trigger
  /-- The selected object would be put into a graveyard (CR 614). -/
  | putToGraveyard : Selector → Trigger
  /-- Whenever a matching card leaves a graveyard (CR 404). -/
  | leaveGraveyard : Selector → Trigger
  /-- The selected permanent leaves the battlefield. -/
  | leaveBattlefield : Selector → Trigger
  /-- Whenever the selected object is returned to its owner's hand. -/
  | returnToHand : Selector → Trigger
  /-- Whenever the selected player discards a card (CR 701.8). -/
  | discard : Selector → Trigger
  /-- When the selected player puts one or more counters of the given kind
  on the selected objects at the same time (CR 122 / 603.2c). The first
  selector is that player (`Selector.controller .this` is “you”). -/
  | putCountersSimultaneously : Selector → Selector → CounterKind → Trigger
  /-- The first selector blocks the second (CR 509). -/
  | block : Selector → Selector → Trigger
  /-- When the selected object or objects die (CR 700.4). -/
  | die : Selector → Trigger
  /-- When objects matching the selector die at the same time, with
  set-wide predicates (CR 700.4 / 603.2d). -/
  | dieSimultaneously : Selector → List SetPredicate → Trigger
  /-- Whenever the selected permanents are sacrificed (CR 701.17).
  The player who sacrifices them is their controller. “You sacrifice a
  token” is a token this object's controller sacrifices. -/
  | sacrifice : Selector → Trigger
  /-- Whenever objects matching the first selector attack objects matching
  the second at the same time, with set-wide predicates
  (CR 508.3 / 603.2d). -/
  | attackSimultaneously : Selector → Selector → List SetPredicate → Trigger
  /-- The numbered ability was activated (CR 602.2). -/
  | abilityWithIdActivated : Nat → Trigger
  /-- The numbered ability has finished resolving (CR 608). `Ability.abilityId`
  numbers that ability. A condition checked while that ability is resolving
  does not count this resolution. -/
  | abilityWithIdResolved : Nat → Trigger
  /-- The numbered action occurred. -/
  | actionWithId : Nat → Trigger
  /-- The numbered action dealt excess damage (CR 120.4a).
  How much is `Value.excessDamageOfActionWithId` of that action. -/
  | actionWithIdDealtExcessDamage : Nat → Trigger
  /-- Number this trigger so later clauses can refer to its selector
  arguments. -/
  | triggerId : Nat → Trigger → Trigger
  /-- The selected player chose the numbered mode (CR 700.2). -/
  | modeWithIdChosen : Selector → Nat → Trigger
  /-- Mana created by the numbered action is spent to pay for the given
  event (CR 106.10). -/
  | spendManaCreatedByAction : Nat → Trigger → Trigger
  /-- Mana from a source matching the selector was spent to pay for the
  given event. The payment happens before that event (CR 601.2h). In a
  `sequence`, `wasArgumentOfTrigger` comes after the `triggerId` it names.
  An ability that triggers once when the event occurs ends on that event,
  so it does not trigger once for each mana spent. -/
  | spendManaFrom : Selector → Trigger → Trigger
  /-- A spell matching the selector is cast (CR 601). -/
  | castSpell : Selector → Trigger
  /-- A spell matching the selector is cast from a graveyard
  (CR 601.2 / 702.34). -/
  | castSpellFromGraveyard : Selector → Trigger
  /-- The selected spell's gift was promised as it was cast (CR 702.174k). -/
  | giftPromised : Selector → Trigger
  /-- The selected spell is countered (CR 701.5). -/
  | counter : Selector → Trigger
  /-- The selected player activates an activated ability of a source
  matching the given selector (CR 602). The first selector is that player.
  Another player's activation is a different event. -/
  | activateAbility : Selector → Selector → Trigger
  /-- After the listed triggers have occurred in order. -/
  | sequence : List Trigger → Trigger
  /-- The given trigger does not occur. -/
  | not : Trigger → Trigger
  /-- Either trigger occurs. -/
  | or : Trigger → Trigger → Trigger
  /-- `spellOrAbility` targets `object` (CR 115.10a / 603.2).
  The first selector is the spell or ability. The second is the target.
  One trigger, even if that spell or ability targets `object` more than once. -/
  | target : Selector → Selector → Trigger
  /-- At the beginning of the selected player's precombat main phase (CR 505.1). -/
  | precombatMainPhase : Selector → Trigger
deriving Repr, Inhabited, BEq
end

namespace Value

instance : ToString Value where
  toString
    | .int n => toString n
    | .x => "X"
    | .count _ | .totalPower _ | .greatestManaValue _ | .greatestToughness _
    | .greatestPower _ | .product _ _ | .variable _ | .greatestManaSpent _
    | .excessDamageOfActionWithId _ => "X"

instance (n : Nat) : OfNat Value n where
  ofNat := .int n

/-- `n` times the number of objects matching the selector.
Zero is the constant zero and one is the count. Neither is a product. -/
def timesCount (n : Int) (among : Selector) : Value :=
  if n == 0 then .int 0
  else if n == 1 then .count among
  else .product (.count among) (.int n)

#guard toString (Value.int 3) == "3"
#guard toString (Value.int (-2)) == "-2"
#guard toString Value.x == "X"
#guard toString (Value.greatestManaValue .this) == "X"
#guard toString (Value.greatestToughness .this) == "X"
#guard toString (Value.greatestPower .this) == "X"
#guard toString (Value.count .this) == "X"
#guard toString (Value.product (Value.count .this) 2) == "X"
#guard toString (Value.variable 1) == "X"
#guard toString (Value.greatestManaSpent .this) == "X"
#guard toString (Value.excessDamageOfActionWithId 1) == "X"
#guard Value.timesCount 1 .this == Value.count .this
#guard Value.timesCount 2 .this == Value.product (Value.count .this) (Value.int 2)
#guard Value.timesCount 0 .this == Value.int 0
#guard Value.product 2 3 != Value.int 6
#guard (1 : Value) == Value.int 1
#guard Value.x != Value.int 1

end Value

namespace Range

#guard Range.range 0 1 == .range (Value.int 0) (Value.int 1)
#guard Range.range Value.x 1 != Range.range 0 1
#guard Range.any == .any
#guard Range.any != Range.range 0 0
#guard Range.from 1 == .from (Value.int 1)
#guard Range.from Value.x != Range.from 1
#guard Range.from 1 != Range.range 1 1
#guard Range.from 0 != Range.any

end Range

namespace Keyword

/-- English plural of a printed name, keeping its capitalization.
`Elf` is `Elves`. A name that already ends in `s` stays unchanged. -/
def pluralName (s : String) : String :=
  match s with
  | "Army" => "Armies"
  | "Elf" => "Elves"
  | "Wolf" => "Wolves"
  | "Dwarf" => "Dwarves"
  | "Hero" => "Heroes"
  | "Merfolk" => "Merfolk"
  | s => if s.endsWith "s" then s else s ++ "s"

/-- Characteristics an affinity ability counts, e.g. `artifacts` or `Elves`.
An empty list of both is an empty phrase. -/
def affinityPhrase (types : List CardType) (subtypes : List CardSubtype) : String :=
  let typeWords := types.map fun t =>
    let name := t.englishName.toLower
    if name.endsWith "s" then name else name ++ "s"
  let subtypeWords := subtypes.map fun st => pluralName (toString st)
  String.intercalate " " (typeWords ++ subtypeWords)

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
  | .connive _ | .chapter _ | .flashback | .ward | .crew _
  | .teamwork _ | .improvise | .kicker | .affinity _ _ | .boast | .cascade
  | .extort | .sneak | .gift _ | .behold _ | .harness | .infinity =>
    Keywords.none

/-- Union of two single keywords. -/
def merge (a b : Keyword) : Keywords :=
  a.toKeywords.merge b.toKeywords

instance : Coe Keyword Keywords where
  coe := toKeywords

/-- Printed “behold an Elf” / “behold a Goblin” (CR 701.4). -/
def beholdPhrase (st : CardSubtype) : String :=
  let name := toString st
  let article :=
    match name.toList with
    | c :: _ =>
      match c.toLower with
      | 'a' | 'e' | 'i' | 'o' | 'u' => "an"
      | _ => "a"
    | [] => "a"
  s!"behold {article} {name}"

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
    | .flashback => "flashback"
    | .ward => "ward"
    | .crew n => s!"crew {n}"
    | .teamwork n => s!"teamwork {n}"
    | .improvise => "improvise"
    | .kicker => "kicker"
    | .affinity types subtypes =>
      let phrase := affinityPhrase types subtypes
      if phrase.isEmpty then "affinity" else s!"affinity for {phrase}"
    | .boast => "boast"
    | .cascade => "cascade"
    | .extort => "extort"
    | .sneak => "sneak"
    | .gift g => g.phrase
    | .behold st => beholdPhrase st
    | .harness => "harness"
    | .infinity => "∞"
    | k => toString k.toKeywords

#guard pluralName "Elf" == "Elves"
#guard pluralName "Hero" == "Heroes"
#guard pluralName "Merfolk" == "Merfolk"
#guard pluralName "Goblin" == "Goblins"
#guard affinityPhrase [.artifact] [] == "artifacts"
#guard affinityPhrase [] [.elf] == "Elves"
#guard affinityPhrase [] [] == ""
#guard (Keyword.teamwork 2).toKeywords == Keywords.none
#guard Keyword.improvise.toKeywords == Keywords.none
#guard Keyword.kicker.toKeywords == Keywords.none
#guard (Keyword.affinity [] [.elf]).toKeywords == Keywords.none
#guard Keyword.boast.toKeywords == Keywords.none
#guard Keyword.cascade.toKeywords == Keywords.none
#guard Keyword.extort.toKeywords == Keywords.none
#guard Keyword.sneak.toKeywords == Keywords.none
#guard toString (Keyword.teamwork 2) == "teamwork 2"
#guard toString Keyword.improvise == "improvise"
#guard toString Keyword.kicker == "kicker"
#guard toString (Keyword.affinity [] [.elf]) == "affinity for Elves"
#guard toString (Keyword.affinity [.artifact] []) == "affinity for artifacts"
#guard toString (Keyword.affinity [] []) == "affinity"
#guard toString Keyword.boast == "boast"
#guard toString Keyword.cascade == "cascade"
#guard toString Keyword.extort == "extort"
#guard toString Keyword.sneak == "sneak"
#guard (Keyword.gift .treasure).toKeywords == Keywords.none
#guard (Keyword.gift .food).toKeywords == Keywords.none
#guard toString (Keyword.gift .food) == "gift a Food"
#guard toString (Keyword.gift .card) == "gift a card"
#guard toString (Keyword.gift .tappedFish) == "gift a tapped Fish"
#guard toString (Keyword.gift .extraTurn) == "gift an extra turn"
#guard toString (Keyword.gift .treasure) == "gift a Treasure"
#guard toString (Keyword.gift .octopus) == "gift an Octopus"
#guard Keyword.harness.toKeywords == Keywords.none
#guard Keyword.infinity.toKeywords == Keywords.none
#guard toString Keyword.harness == "harness"
#guard toString Keyword.infinity == "∞"
#guard (Keyword.behold .elf).toKeywords == Keywords.none
#guard (Keyword.behold .goblin).toKeywords == Keywords.none
#guard toString (Keyword.behold .elf) == "behold an Elf"
#guard toString (Keyword.behold .goblin) == "behold a Goblin"
#guard toString (Keyword.behold .orc) == "behold an Orc"

end Keyword

end Mtg.Engine
