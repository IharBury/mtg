import Mtg.Engine.Color
import Mtg.Engine.TypeLine

/-!
# DSL elements

Clause vocabulary for a traditional Magic card: one face, plus an optional
Adventure. `TraditionalCardDefinition.card` is the clause list. Printed
keywords are a `.keyword` instruction in `.textBox`, activated
abilities are a `.costFor` instruction in `.textBox`, tapping spells
are a `.tap` instruction in `.textBox`, cost reductions are a
`.costLessToCastIf` instruction in `.textBox`, damage is a
`.dealDamage` instruction in `.textBox`, triggered abilities are a
`.whenever` or `.when` instruction in `.textBox`, scry spells are a
`.scry` instruction in `.textBox`, putting counters is a `.putCounter`
instruction in `.textBox`, and a spell that resolves as
several sentences is a `.sequence` in `.textBox`.
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
  | halfling
  | rogue
  | human
  | cleric
  deriving Repr, BEq, DecidableEq

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

/-- Whose control a target predicate talks about. -/
inductive PlayerRef where
  | you
  | opponent
  deriving Repr, BEq

/-- A type word in `.cardType`. Card types (`.creature`) and `.equipment`
share the constructor. Creature subtypes use `.cardSubtype` instead
(`[.cardSubtype .dwarf]`). -/
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
  | equipment
  deriving Repr, BEq, DecidableEq

/-- How many objects one targeting phrase names. `.or 1 2` is “one or two”. -/
inductive TargetCount where
  | or (lo hi : Nat)
  deriving Repr, BEq

/-- A reference to an object in rules text. A list is read in order: `.or` is a
disjunction, and the other words are a conjunction.

`.target [.cardType .creature]` is “target creature”.
`.targets (.or 1 2) [.cardType .creature]` is “one or two target creatures”.
`[.this, .cardType .creature]` is “this creature”. `[.this, .spell]` is
“this spell”. `.it` is the object named earlier (`It gets +2/+2`).
`.thisCardName` prints this card’s name. `.other` excludes this object. -/
inductive ObjectRef where
  | cardType (t : TypeName)
  | cardSubtype (s : CardSubtype)
  | controlledBy (p : PlayerRef)
  | or (qs : List ObjectRef)
  | tapped
  | this
  | other
  | it
  | spell
  | thisCardName
  | target (qs : List ObjectRef)
  | targets (count : TargetCount) (qs : List ObjectRef)
  deriving Repr, BEq

namespace ObjectRef

/-- `.creature` in a reference list. -/
def creature : ObjectRef := .cardType .creature

end ObjectRef

/-- A keyword the text box grants. -/
inductive GrantedAbility where
  | keyword (k : PrintedKeyword)
  deriving Repr, BEq

/-- How long a text-box effect lasts. -/
inductive Duration where
  | endOfTurn
  deriving Repr, BEq

/-- A card name printed in rules text. `.thisCardName` is this card’s name,
shortened before a comma (`Bilbo Baggins` on Bilbo Baggins, Burglar). -/
inductive PrintedName where
  | thisCardName
  deriving Repr, BEq

/-- Which draw a trigger watches.
`.secondEachTurn` is “your/their second card each turn”. -/
inductive DrawOrdinal where
  | secondEachTurn
  deriving Repr, BEq

/-- One event in `.whenever` or `.when`.
`[.attack [.this, .cardType .creature] []]` is “this creature attacks”.
The second list is a further restriction on that attack; empty means any
attack. `[.enter [.thisCardName]]` is “{name} enters”.
`[.draw [.you] .secondEachTurn]` is “you draw your second card each turn”. -/
inductive TriggerExpr where
  | attack (who : List ObjectRef) (restrictions : List ObjectRef)
  | enter (who : List PrintedName)
  | draw (who : List PlayerRef) (which : DrawOrdinal)
  deriving Repr, BEq

/-- A printed power and toughness change. `.plusPowerToughness +1 +1` is `+1/+1`. -/
inductive StatMod where
  | plusPowerToughness (power toughness : Int)
  deriving Repr, BEq

/-- A counter a text-box effect puts on an object.
`.plusOnePlusOne` is a +1/+1 counter. -/
inductive CounterKind where
  | plusOnePlusOne
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

/-- When a cost reduction applies.
`.targeting .it [.tapped, .cardType .creature]` is “if it targets a tapped creature”. -/
inductive CastIf where
  | targeting (obj : ObjectRef) (qs : List ObjectRef)
  deriving Repr, BEq

/-- An object named without the word “target”.
`.oneOf [.cardType .equipment, .controlledBy .you]` is “an Equipment you control”.
`.it` is the object named earlier. -/
inductive ObjectExpr where
  | oneOf (qs : List ObjectRef)
  | it
  deriving Repr, BEq

/-- A condition in `.if`. `[.is [.it] [.cardSubtype .dwarf]]` is “it's a Dwarf”. -/
inductive TextCondition where
  | is (subj : List ObjectRef) (qs : List ObjectRef)
  deriving Repr, BEq

/-- One instruction in a `.textBox`. -/
inductive TextEffect where
  /-- A printed keyword ability of this face (`Lifelink`). -/
  | keyword (k : PrintedKeyword)
  | gainUntil (targets : List ObjectRef) (gains : List GrantedAbility) (dur : Duration)
  /-- Matching objects get these changes until `dur`.
  `[.it]` is the object named earlier (`It gets +2/+2`). -/
  | getUntil (qs : List ObjectRef) (mods : List StatMod) (dur : Duration)
  /-- An activated ability: pay `costs`, then follow `effects` (`{3}{W}: …`). -/
  | costFor (costs : List PrintedCost) (effects : List TextEffect)
  /-- Tap the named targets (`Tap one or two target creatures`). -/
  | tap (targets : List ObjectRef)
  /-- These words cost `discount` less to cast when `cond` holds.
  `[.this, .spell]` is “This spell costs …”. -/
  | costLessToCastIf (subjects : List ObjectRef) (discount : List CostSymbol) (cond : CastIf)
  /-- `subjects` deal `n` damage to `targets`. -/
  | dealDamage (subjects : List ObjectRef) (n : Nat) (targets : List ObjectRef)
  /-- When `events` happen, follow `effects`.
  `[.attack [.this, .cardType .creature] []]` is “this creature attacks”. -/
  | whenever (events : List TriggerExpr) (effects : List TextEffect)
  /-- When `events` happen, follow `effects`.
  `[.enter [.thisCardName]]` with `[.draw 1]` is “When {name} enters, draw a card”. -/
  | when (events : List TriggerExpr) (effects : List TextEffect)
  /-- Draw `n` cards (`draw a card`). -/
  | draw (n : Nat)
  /-- Look at the top `n` cards of your library (`Scry 2`). -/
  | scry (n : Nat)
  /-- `who` gets `mods` until `dur` for each object matching `each`.
  `[.it]` is “it”. `[.other, .cardType .creature, .controlledBy .you]` is
  “each other creature you control”. -/
  | getForEachUntil (who : List ObjectRef) (mods : List StatMod)
      (each : List ObjectRef) (dur : Duration)
  /-- Do these effects in order, printed as one paragraph. -/
  | sequence (effects : List TextEffect)
  /-- Untap the named targets (`Untap target creature you control`). -/
  | untap (targets : List ObjectRef)
  /-- When `conds` hold, follow `effects`.
  `[.is [.it] [.cardSubtype .dwarf]]` is “if it's a Dwarf”. -/
  | «if» (conds : List TextCondition) (effects : List TextEffect)
  /-- `who` may do `effects` (`you may …`). -/
  | may (who : List PlayerRef) (effects : List TextEffect)
  /-- Attach `what` to `dest`. -/
  | attachTo (what dest : List ObjectExpr)
  /-- Put `n` counters of `kind` on `objects`.
  `.putCounter 1 .plusOnePlusOne [.this, .cardType .creature]` is
  “put a +1/+1 counter on this creature”. -/
  | putCounter (n : Nat) (kind : CounterKind) (objects : List ObjectRef)
  deriving Repr, BEq

/-- `getForEachUntil [.it] mods each dur` is “it gets … until … for each …”.
Written without a leading dot so it can sit in a `.whenever` effect list. -/
def getForEachUntil (who : List ObjectRef) (mods : List StatMod)
    (each : List ObjectRef) (dur : Duration) : TextEffect :=
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

#guard (.plusPowerToughness +1 +1 : StatMod) == .plusPowerToughness 1 1

end Mtg.Engine
