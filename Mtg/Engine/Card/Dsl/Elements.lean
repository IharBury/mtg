import Mtg.Engine.Color
import Mtg.Engine.TypeLine

/-!
# DSL elements

Clause vocabulary for a traditional Magic card: one face, plus an optional
Adventure. `TraditionalCardDefinition.card` is the clause list. Printed
keywords are a `.keyword` instruction in `.textBox`, activated
abilities are a `.costFor` instruction in `.textBox`, tapping spells
are a `.tap` instruction in `.textBox`, cost reductions are
`.costLessToCast` inside `.if` in `.textBox`, damage is a
`.dealDamage` instruction in `.textBox`, triggered abilities are a
`.whenever` or `.when` instruction in `.textBox`, scry spells are a
`.scry` instruction in `.textBox`, putting counters is a `.putCounter`
instruction in `.textBox`, a spell that resolves as
several sentences is a `.sequence` in `.textBox`, countering
is a `.counter` in `.textBox`, doing effects unless a player
pays is a `.unlessPay` in `.textBox`, and a modal spell is a
`.chooseMode` in `.textBox`. Doing one effect instead of another is
`.insteadOf`. A permission that lasts while a condition holds is
`.asLongAs`. “A permanent spell is countered this way” is
`.counteredThisWay [.permanentSpell]` inside `.if`.
`{name} can't be blocked` is `.cannot (.block [] [.thisCardName])`.
Combat damage is `.dealSuchDamage` inside `.whenever`. Exchanging control is
`.exchangeControl`.
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

`.controlledBy [.you]` is “you control”. `.controlledBy [.opponent]` is
“an opponent controls”.
`.oneOf [.cardType .equipment, .controlledBy [.you]]` is “an Equipment you control”.
`.target [.cardType .creature]` is “target creature”.
`.targets (.or 1 2) [.cardType .creature]` is “one or two target creatures”.
`[.this, .cardType .creature]` is “this creature”. `[.this, .spell]` is
“this spell”. `.thatTarget` is the target named earlier (`It gets +2/+2`).
`.innerTarget` is the target of this effect (`its controller`).
`.permanentSpell` is “permanent spell”.
`.thatExiled` is the card exiled this way (`that card`, then `it remains exiled`).
`.thisCardName` prints this card’s name, shortened before a comma
(`Bilbo` on Bilbo, Luckwearer). `.player` is “a player”.
`.nonland` is “nonland”. `.permanent` is “permanent”.
`.sharingCardType` is “share a card type”.
`.targetsWhich 2 [.nonland, .permanent] [.sharingCardType]` is
“two target nonland permanents that share a card type”.
`.other` excludes this object. -/
inductive ObjectRef where
  | cardType (t : TypeName)
  | cardSubtype (s : CardSubtype)
  | controlledBy (ps : List PlayerRef)
  | or (qs : List ObjectRef)
  | tapped
  | this
  | other
  | thatTarget
  | innerTarget
  | spell
  | permanentSpell
  | thatExiled
  | thisCardName
  | player
  | nonland
  | permanent
  | sharingCardType
  | oneOf (qs : List ObjectRef)
  | target (qs : List ObjectRef)
  | targets (count : TargetCount) (qs : List ObjectRef)
  /-- `n` targets described by `qs`, restricted by `which`.
  `.targetsWhich 2 [.nonland, .permanent] [.sharingCardType]` is
  “two target nonland permanents that share a card type”. -/
  | targetsWhich (n : Nat) (qs : List ObjectRef) (which : List ObjectRef)
  deriving Repr, BEq

/-- Who pays in `.unlessPay`. `.controller .innerTarget` is “its controller”. -/
inductive Payer where
  | controller (obj : ObjectRef)
  deriving Repr, BEq

/-- A keyword the text box grants. -/
inductive GrantedAbility where
  | keyword (k : PrintedKeyword)
  deriving Repr, BEq

/-- How long a text-box effect lasts. -/
inductive Duration where
  | endOfTurn
  deriving Repr, BEq

/-- The period in “each turn”. `.turn` is one turn. -/
inductive EachPeriod where
  | turn
  deriving Repr, BEq

/-- A kind of damage in `.dealSuchDamage`. `.combat` is combat damage. -/
inductive DamageKind where
  | combat
  deriving Repr, BEq, DecidableEq

/-- One restriction on which draw a trigger watches.
`.ordinalEach 2 .turn` is “the second card each turn”. -/
inductive DrawWatch where
  | ordinalEach (n : Nat) (period : EachPeriod)
  deriving Repr, BEq

/-- One event in `.whenever` or `.when`.
`[.creatureAttack [.this] []]` is “this creature attacks”.
The creature type is the event, so `who` does not repeat `.cardType .creature`.
The second list is a further restriction on that attack; empty means any
attack. `[.permanentEnter [.thisCardName]]` is “{name} enters”.
`[.drawCard [.you] []]` is “you draw a card”. An empty watch list means any card.
`[.drawCard [.you] [.ordinalEach 2 .turn]]` is “you draw your second card each turn”.
`[.dealSuchDamage [.thisCardName] [.player] [.combat]]` is
“{name} deals combat damage to a player”. -/
inductive TriggerExpr where
  | creatureAttack (who : List ObjectRef) (restrictions : List ObjectRef)
  | permanentEnter (who : List ObjectRef)
  | drawCard (who : List PlayerRef) (which : List DrawWatch)
  | dealSuchDamage (who : List ObjectRef) (toWhom : List ObjectRef) (kinds : List DamageKind)
  deriving Repr, BEq

/-- A printed power and toughness change. `.plusPowerToughness 1 1` is `+1/+1`. -/
inductive StatMod where
  | plusPowerToughness (power toughness : Int)
  deriving Repr, BEq

/-- A counter a text-box effect puts on an object.
`.plusOnePlusOne` is a +1/+1 counter. -/
inductive CounterKind where
  | plusOnePlusOne
  deriving Repr, BEq

/-- One cost of an activated ability written in `.costFor`. -/
inductive PrintedCost where
  | mana (ms : List CostSymbol)
  deriving Repr, BEq

/-- A condition in `.if`. `[.is [.thatTarget] [.cardSubtype .dwarf]]` is “it's a Dwarf”.
`[.counteredThisWay [.permanentSpell]]` is “a permanent spell is countered this way”.
`[.targeting [.this, .spell] [.tapped, .cardType .creature]]` is
“it targets a tapped creature” once this spell has been named. -/
inductive TextCondition where
  | is (subj : List ObjectRef) (qs : List ObjectRef)
  | counteredThisWay (qs : List ObjectRef)
  | targeting (subj : List ObjectRef) (qs : List ObjectRef)
  deriving Repr, BEq

/-- Whose zone `.belongingTo` names. `.owner [.thatTarget]` is “its owner”. -/
inductive ZoneOwner where
  | owner (obj : List ObjectRef)
  deriving Repr, BEq

/-- A zone or state word. `.graveyard` is “graveyard”. `.exiled` is “exiled”.
`.belongingTo [.owner [.thatTarget]]` beside `.graveyard` is “its owner's graveyard”. -/
inductive ZoneWord where
  | graveyard
  | exiled
  | belongingTo (who : List ZoneOwner)
  deriving Repr, BEq

/-- How `.mayCastSo` is paid.
`.withoutPayingManaCost` is “without paying its mana cost”. -/
inductive CastManner where
  | withoutPayingManaCost
  deriving Repr, BEq

/-- What `.cannot` forbids.
`.block [] [.thisCardName]` is “{name} can't be blocked”.
The first list names who could block; empty means any blocker. -/
inductive CannotExpr where
  | block (byWhom : List ObjectRef) (who : List ObjectRef)
  deriving Repr, BEq

/-- One instruction in a `.textBox`. -/
inductive TextEffect where
  /-- A printed keyword ability of this face (`Lifelink`). -/
  | keyword (k : PrintedKeyword)
  | gainUntil (targets : List ObjectRef) (gains : List GrantedAbility) (dur : Duration)
  /-- Matching objects get these changes until `dur`.
  `[.thatTarget]` is the target named earlier (`It gets +2/+2`). -/
  | getUntil (qs : List ObjectRef) (mods : List StatMod) (dur : Duration)
  /-- An activated ability: pay `costs`, then follow `effects` (`{3}{W}: …`). -/
  | costFor (costs : List PrintedCost) (effects : List TextEffect)
  /-- Tap the named targets (`Tap one or two target creatures`). -/
  | tap (targets : List ObjectRef)
  /-- `subjects` cost `discount` less to cast.
  `[.costLessToCast [.this, .spell] [.generic 3]]` is “This spell costs {3} less to cast”. -/
  | costLessToCast (subjects : List ObjectRef) (discount : List CostSymbol)
  /-- `subjects` deal `n` damage to `targets`. -/
  | dealDamage (subjects : List ObjectRef) (n : Nat) (targets : List ObjectRef)
  /-- When `events` happen, follow `effects`.
  `[.creatureAttack [.this] []]` is “this creature attacks”. -/
  | whenever (events : List TriggerExpr) (effects : List TextEffect)
  /-- When `events` happen, follow `effects`.
  `[.permanentEnter [.thisCardName]]` with `[.draw 1]` is “When {name} enters, draw a card”. -/
  | when (events : List TriggerExpr) (effects : List TextEffect)
  /-- Draw `n` cards (`draw a card`). -/
  | draw (n : Nat)
  /-- Look at the top `n` cards of your library (`Scry 2`). -/
  | scry (n : Nat)
  /-- `who` gets `mods` until `dur` for each object matching `each`.
  `[.this, .cardType .creature]` is “it” after “this creature attacks”.
  `[.other, .cardType .creature, .controlledBy [.you]]` is
  “each other creature you control”. -/
  | getForEachUntil (who : List ObjectRef) (mods : List StatMod)
      (each : List ObjectRef) (dur : Duration)
  /-- Do these effects in order, printed as one paragraph. -/
  | sequence (effects : List TextEffect)
  /-- Untap the named targets (`Untap target creature you control`). -/
  | untap (targets : List ObjectRef)
  /-- When `conds` hold, follow `effects`.
  `[.is [.thatTarget] [.cardSubtype .dwarf]]` is “if it's a Dwarf”.
  `[.targeting [.this, .spell] [.tapped, .cardType .creature]]` with
  `[.costLessToCast [.this, .spell] [.generic 3]]` is
  “This spell costs {3} less to cast if it targets a tapped creature”. -/
  | «if» (conds : List TextCondition) (effects : List TextEffect)
  /-- `who` may do `effects` (`you may …`). -/
  | may (who : List PlayerRef) (effects : List TextEffect)
  /-- Put `obj` into `dest`.
  `.putInto [.thatTarget] [.graveyard, .belongingTo [.owner [.thatTarget]]]` is
  “putting it into its owner's graveyard”. -/
  | putInto (obj : List ObjectRef) (dest : List ZoneWord)
  /-- Exile `obj`. `.exile [.thatTarget]` is “exile it”. -/
  | exile (obj : List ObjectRef)
  /-- Do `done` instead of `avoided`.
  `.insteadOf [.putInto [.thatTarget] [.graveyard, .belongingTo [.owner [.thatTarget]]]] [.exile [.thatTarget]]` is
  “exile it instead of putting it into its owner's graveyard”. -/
  | insteadOf (avoided done : List TextEffect)
  /-- `who` may cast `what` by `how`.
  `.mayCastSo [.you] [.thatExiled] [.withoutPayingManaCost]` is
  “you may cast that card without paying its mana cost”. -/
  | mayCastSo (who : List PlayerRef) (what : List ObjectRef) (how : List CastManner)
  /-- `obj` remains in `state`. `.remains [.thatExiled] [.exiled]` is “it remains exiled”. -/
  | remains (obj : List ObjectRef) (state : List ZoneWord)
  /-- `action` while `cond` holds. The condition is written first.
  `.asLongAs [.remains [.thatExiled] [.exiled]] [.mayCastSo [.you] [.thatExiled] [.withoutPayingManaCost]]` is
  “you may cast that card without paying its mana cost for as long as it remains exiled”. -/
  | asLongAs (cond action : List TextEffect)
  /-- Attach `what` to `dest`.
  `[.oneOf [.cardType .equipment, .controlledBy [.you]]]` to `[.thatTarget]` is
  “attach an Equipment you control to it”. -/
  | attachTo (what dest : List ObjectRef)
  /-- Put `n` counters of `kind` on `objects`.
  `.putCounter 1 .plusOnePlusOne [.this, .cardType .creature]` is
  “put a +1/+1 counter on this creature”. -/
  | putCounter (n : Nat) (kind : CounterKind) (objects : List ObjectRef)
  /-- Counter `targets`. `.counter [.target [.spell]]` is “counter target spell”. -/
  | counter (targets : List ObjectRef)
  /-- Discard `n` cards. -/
  | discard (n : Nat)
  /-- `who` pays `costs`, or else do `actions`.
  `.unlessPay [.controller .innerTarget] [.mana [.generic 4]] [.counter [.target [.spell]]]` is
  “Counter target spell unless its controller pays {4}.” -/
  | unlessPay (who : List Payer) (costs : List PrintedCost) (actions : List TextEffect)
  /-- Choose `n` of these modes. `.chooseMode 1` is “Choose one —”.
  Each mode is one bullet. `.sequence [.draw 2, .discard 1]` inside a mode is
  “Draw two cards, then discard a card.” -/
  | chooseMode (n : Nat) (modes : List TextEffect)
  /-- `{who} can't be blocked`.
  `.cannot (.block [] [.thisCardName])` is “Bilbo can't be blocked”. -/
  | cannot (what : CannotExpr)
  /-- Exchange control of `objects`.
  `.exchangeControl [.targetsWhich 2 [.nonland, .permanent] [.sharingCardType]]` is
  “Exchange control of two target nonland permanents that share a card type”. -/
  | exchangeControl (objects : List ObjectRef)
  deriving Repr, BEq

/-- `getForEachUntil [.this, .cardType .creature] mods each dur` is
“it gets … until … for each …”.
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

end Mtg.Engine
