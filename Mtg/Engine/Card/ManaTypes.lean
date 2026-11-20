import Mtg.Engine.Card.Primitives

/-!
# Runtime Mana Types and Spending Restrictions (Layer 0 — CR 106, 605)

Layer-0 evaluated mana types (`ManaType`, `ManaOutput`) and pure compositional
mana spending restrictions (`ManaObjectPred`, `ManaAbilityPred`,
`SpellRiderSpec`, `ManaSpend`, `ManaSpendRestriction`), anchored to the
25 September 2026 Comprehensive Rules (CR 106.1, 106.6, 106.12, 605).

Kept below `Mtg.Engine.Mana` (and below `Mtg.Engine.Card.Expr`) so `ManaPool`
cost payment (`canPay` / `pay?`) stays pure, `Game`-free, and strictly acyclic
while `Mtg.Engine.Card.ManaSpec` generalizes `ManaSpec` / `ManaPoolPalette`
over `ValueExpr`, `ObjectExpr`, and `PlayerExpr`.
-/

namespace Mtg.Engine

/-- A type of mana that can exist in a mana pool (CR 106.1b). -/
inductive ManaType where
  | colored (color : Color)
  | colorless
deriving DecidableEq, Repr, Inhabited, BEq

namespace ManaType

def letter : ManaType → String
  | .colored c => c.letter
  | .colorless => "C"

instance : ToString ManaType where
  toString
    | .colored c => toString c
    | .colorless => "colorless"

end ManaType

/-- One mana of each of the five colors (CR 105.1 / 106.1a). -/
def anyColorMana : Array ManaType :=
  (Color.all.map ManaType.colored).toArray

/-- The evaluated mana a mana ability can add (CR 106.1). -/
inductive ManaOutput where
  /-- Exactly these mana. -/
  | fixed (mana : Array ManaType)
  /-- `amount` mana of one type chosen from `types`. -/
  | oneOf (types : Array ManaType) (amount : Nat)
  /-- `amount` mana in any combination of `types`. -/
  | combination (types : Array ManaType) (amount : Nat)
  /-- One mana of a color (or type when `includeColorless` is true, e.g.
  Reflecting Pool, CR 106.7) among `allowed`; naming an absent type adds no
  mana (CR 106.1, e.g. Mox Amber, Arcane Signet, Exotic Orchard). -/
  | colorAmong (allowed : Array ManaType) (includeColorless : Bool := false)
deriving DecidableEq, Repr, Inhabited, BEq

namespace ManaOutput

private def filterAmong (allowed : Array ManaType) (includeColorless : Bool) : Array ManaType :=
  if includeColorless then allowed
  else allowed.filter (fun | .colored _ => true | .colorless => false)

/-- Mana types this output can include. -/
def types : ManaOutput → Array ManaType
  | .fixed m => m.foldl (fun acc t => if acc.contains t then acc else acc.push t) #[]
  | .oneOf ts n | .combination ts n => if n == 0 then #[] else ts
  | .colorAmong _ includeColorless =>
    if includeColorless then anyColorMana.push .colorless else anyColorMana

/-- Mana types this output can actually produce a positive amount of (CR 106.7).
Unlike `types`, `.colorAmong allowed` only includes types present in `allowed`. -/
def producibleTypes : ManaOutput → Array ManaType
  | .fixed m => m.foldl (fun acc t => if acc.contains t then acc else acc.push t) #[]
  | .oneOf ts n | .combination ts n => if n == 0 then #[] else ts
  | .colorAmong allowed includeColorless =>
    (filterAmong allowed includeColorless).foldl
      (fun acc t => if acc.contains t then acc else acc.push t) #[]

/-- The mana added when the player names `t`: all of it `t` where the
ability allows a choice. -/
def withType (out : ManaOutput) (t : ManaType) : Option (Array ManaType) :=
  match out with
  | .fixed m => if m.contains t then some m else none
  | .oneOf ts n | .combination ts n =>
    if ts.contains t then some (Array.replicate n t) else none
  | .colorAmong allowed includeColorless =>
    match t with
    | .colored _ => some (if allowed.contains t then #[t] else #[])
    | .colorless =>
      if includeColorless then some (if allowed.contains .colorless then #[.colorless] else #[])
      else none

/-- Distinct multisets of `n` mana types chosen from `ts` in `ts` index order. -/
def multisetChoices (ts : Array ManaType) (n : Nat) : Array (Array ManaType) :=
  let rec go (startIdx rem : Nat) (acc : Array ManaType) : Array (Array ManaType) :=
    match rem with
    | 0 => #[acc]
    | rem' + 1 => Id.run do
      let mut out : Array (Array ManaType) := #[]
      for idx in [startIdx : ts.size] do
        out := out ++ go idx rem' (acc.push ts[idx]!)
      return out
  if n == 0 then #[#[]]
  else if ts.isEmpty then #[]
  else go 0 n #[]

/-- All distinct non-empty mana tuples this output can add (including mixed-color
tuples for `.combination ts n`, CR 106.1). -/
def allChoices (out : ManaOutput)
    (dedupTypes : Array ManaType → Array ManaType := id) : Array (Array ManaType) :=
  match out with
  | .fixed m => if m.isEmpty then #[] else #[m]
  | .oneOf ts n =>
    if n == 0 then #[]
    else (dedupTypes ts).map (fun t => Array.replicate n t)
  | .combination ts n =>
    if n == 0 then #[]
    else multisetChoices (dedupTypes ts) n
  | .colorAmong allowed includeColorless =>
    (dedupTypes (filterAmong allowed includeColorless)).map (fun t => #[t])

/-- Whether the ability can add exactly `mana`. -/
def allows (out : ManaOutput) (mana : Array ManaType) : Bool :=
  let count (a : Array ManaType) (t : ManaType) := (a.filter (· == t)).size
  match out with
  | .fixed m => m.size == mana.size && m.all (fun t => count m t == count mana t)
  | .oneOf ts n =>
    mana.size == n &&
      (match mana[0]? with
       | some t => ts.contains t && mana.all (· == t)
       | none => true)
  | .combination ts n => mana.size == n && mana.all ts.contains
  | .colorAmong allowed includeColorless =>
    let ok := filterAmong allowed includeColorless
    mana.isEmpty || (mana.size == 1 && mana.all ok.contains)

/-- How much mana this output adds. -/
def amount : ManaOutput → Nat
  | .fixed m => m.size
  | .oneOf ts n | .combination ts n => if ts.isEmpty then 0 else n
  | .colorAmong allowed includeColorless =>
    if (filterAmong allowed includeColorless).isEmpty then 0 else 1

end ManaOutput

/-- Mana symbols `{W}`/`{G}`/`{C}` are not color words and are unchanged by Layer 3
text-changing effects (CR 107.4 / 612.2). -/
instance : HasTextChange ManaOutput where
  applyTextChanges _ out := out

/-- Bonus effect rider granted to a spell cast using mana carrying this restriction
or rider (CR 106.6 / 106.12). -/
inductive SpellRiderSpec where
  /-- "and that spell can't be countered" (CR 106.6 / 101.2). -/
  | cantBeCountered
  /-- "if that mana is spent on a creature spell, it gains haste" (CR 106.6). -/
  | gainsHaste
  /-- "that creature enters with `n` additional +1/+1 counter(s) on it" (CR 106.6 / 614.1c). -/
  | entersWithPlusOneCounters (n : Nat := 1)
deriving DecidableEq, Repr, Inhabited, BEq

namespace SpellRiderSpec

/-- Trailing clause appended inside a `Spend this mana only to cast ...` sentence. -/
def toClause : SpellRiderSpec → String
  | .cantBeCountered => ", and that spell can't be countered"
  | .gainsHaste => ", and that creature gains haste"
  | .entersWithPlusOneCounters 1 =>
    ", and that creature enters with an additional +1/+1 counter on it"
  | .entersWithPlusOneCounters n =>
    s!", and that creature enters with {n} additional +1/+1 counters on it"

/-- Standalone sentence for an unrestricted mana rider (CR 106.6). -/
def toStandaloneSentence : SpellRiderSpec → String
  | .cantBeCountered => "If that mana is spent on a spell, that spell can't be countered."
  | .gainsHaste => "If that mana is spent on a creature spell, it gains haste."
  | .entersWithPlusOneCounters 1 =>
    "If that mana is spent to cast a creature spell, that creature enters with an additional +1/+1 counter on it."
  | .entersWithPlusOneCounters n =>
    s!"If that mana is spent to cast a creature spell, that creature enters with {n} additional +1/+1 counters on it."

end SpellRiderSpec

/-- Boolean predicate over an object's types, supertypes, and subtypes for
compositional mana spending restrictions (CR 106.6). -/
inductive ManaObjectPred where
  | any
  | hasType (cardType : CardType)
  | hasSupertype (supertype : Supertype)
  | hasSubtype (subtype : CardSubtype)
  | not (pred : ManaObjectPred)
  | and (lhs rhs : ManaObjectPred)
  | or (lhs rhs : ManaObjectPred)
deriving DecidableEq, Repr, Inhabited, BEq

namespace ManaObjectPred

/-- Conjunction of predicates (empty array = `.any`). -/
def allOf (ps : Array ManaObjectPred) : ManaObjectPred :=
  match ps.toList with
  | [] => .any
  | [p] => p
  | p :: rest => rest.foldl .and p

/-- Right-associated disjunction of predicates (empty array = `.not .any`). -/
def anyOf (ps : Array ManaObjectPred) : ManaObjectPred :=
  let rec go : List ManaObjectPred → ManaObjectPred
    | [] => .not .any
    | [p] => p
    | p :: rest => .or p (go rest)
  go ps.toList

/-- Evaluate `pred` against an object's `(types, supertypes, subtypes)`. -/
def satisfies (pred : ManaObjectPred) (types : Array CardType)
    (supertypes : Array Supertype) (subtypes : Array CardSubtype) : Bool :=
  match pred with
  | .any => true
  | .hasType t => types.contains t
  | .hasSupertype s => supertypes.contains s
  | .hasSubtype s => subtypes.contains s
  | .not p => !p.satisfies types supertypes subtypes
  | .and a b => a.satisfies types supertypes subtypes && b.satisfies types supertypes subtypes
  | .or a b => a.satisfies types supertypes subtypes || b.satisfies types supertypes subtypes

private def cardTypeWord : CardType → String
  | .artifact => "artifact"
  | .battle => "battle"
  | .conspiracy => "conspiracy"
  | .creature => "creature"
  | .dungeon => "dungeon"
  | .enchantment => "enchantment"
  | .instant => "instant"
  | .kindred => "kindred"
  | .land => "land"
  | .phenomenon => "phenomenon"
  | .plane => "plane"
  | .planeswalker => "planeswalker"
  | .scheme => "scheme"
  | .sorcery => "sorcery"
  | .vanguard => "vanguard"

private def supertypeWord : Supertype → String
  | .basic => "basic"
  | .legendary => "legendary"
  | .ongoing => "ongoing"
  | .snow => "snow"
  | .world => "world"

/-- Short English modifier phrase for `pred` (used in `ManaSpendRestriction.label`). -/
def label : ManaObjectPred → String
  | .any => "any"
  | .hasType t => cardTypeWord t
  | .hasSupertype s => supertypeWord s
  | .hasSubtype s => toString s
  | .not (.hasType t) => s!"non{cardTypeWord t}"
  | .not (.hasSupertype s) => s!"non{supertypeWord s}"
  | .not (.hasSubtype s) => s!"non-{s}"
  | .not p => s!"non-({p.label})"
  | .and a b => s!"{a.label} {b.label}"
  | .or a (.or b c) => s!"{a.label}, {b.label}, and {c.label}"
  | .or a b => s!"{a.label} or {b.label}"

end ManaObjectPred

instance : HasTextChange ManaObjectPred where
  applyTextChanges tcs p :=
    if tcs.isEmpty then p
    else
      let rec go : ManaObjectPred → ManaObjectPred
        | .hasSubtype s => .hasSubtype (HasTextChange.applyTextChanges tcs s)
        | .not inner => .not (go inner)
        | .and a b => .and (go a) (go b)
        | .or a b => .or (go a) (go b)
        | other => other
      go p

/-- What a payment is for, as far as `ManaSpendRestriction` checks care (CR 106.6).
The default is a non-spell payment (such as an activated ability or tax). -/
structure ManaSpend where
  spell : Bool := false
  fromHand : Bool := false
  /-- Zone the spell is being cast from, when known (CR 106.6). -/
  castFromZone : Option ZoneKind := none
  /-- Supertypes of the spell being cast. -/
  supertypes : Array Supertype := #[]
  /-- Card types of the spell being cast. -/
  types : Array CardType := #[]
  /-- Subtypes of the spell being cast. -/
  subtypes : Array CardSubtype := #[]
  /-- Card types of the source of an activated ability being paid for. -/
  abilitySourceTypes : Array CardType := #[]
  /-- Supertypes of the source of an activated ability being paid for. -/
  abilitySourceSupertypes : Array Supertype := #[]
  /-- Subtypes of the source of an activated ability being paid for. -/
  abilitySourceSubtypes : Array CardSubtype := #[]
  /-- Activating an equip ability. -/
  equip : Bool := false
deriving DecidableEq, Repr, Inhabited, BEq

namespace ManaSpend

/-- Default non-spell, non-ability mana payment (e.g. ward, attack tax, resolution pay). -/
def nonSpell : ManaSpend := {}

/-- Mana payment context for casting a spell (CR 106.6). -/
def forSpell (types : Array CardType := #[]) (supertypes : Array Supertype := #[])
    (subtypes : Array CardSubtype := #[]) (fromHand : Bool := false)
    (castFromZone : Option ZoneKind := none) : ManaSpend :=
  { spell := true
    fromHand := fromHand || castFromZone == some .hand
    castFromZone := castFromZone.orElse (fun _ => if fromHand then some .hand else none)
    supertypes, types, subtypes }

/-- Mana payment context for activating an ability (CR 106.6). -/
def forAbility (sourceTypes : Array CardType := #[])
    (sourceSupertypes : Array Supertype := #[])
    (sourceSubtypes : Array CardSubtype := #[])
    (equip : Bool := false) : ManaSpend :=
  { abilitySourceTypes := sourceTypes
    abilitySourceSupertypes := sourceSupertypes
    abilitySourceSubtypes := sourceSubtypes
    equip }

def hasSupertype (s : ManaSpend) (sup : Supertype) : Bool :=
  s.supertypes.any (· == sup)

def legendary (s : ManaSpend) : Bool :=
  s.hasSupertype .legendary

def hasType (s : ManaSpend) (t : CardType) : Bool :=
  s.types.any (· == t)

def planeswalker (s : ManaSpend) : Bool :=
  s.hasType .planeswalker

def noncreature (s : ManaSpend) : Bool :=
  !s.hasType .creature

def artifact (s : ManaSpend) : Bool :=
  s.hasType .artifact

end ManaSpend

/-- Predicate over an activated ability being paid for with restricted mana (CR 106.6). -/
inductive ManaAbilityPred where
  | equip
  | sourceMatches (pred : ManaObjectPred)
deriving DecidableEq, Repr, Inhabited, BEq

namespace ManaAbilityPred

def satisfies (p : ManaAbilityPred) (s : ManaSpend) : Bool :=
  match p with
  | .equip => s.equip
  | .sourceMatches pred =>
    !s.spell && pred.satisfies s.abilitySourceTypes s.abilitySourceSupertypes s.abilitySourceSubtypes

def label : ManaAbilityPred → String
  | .equip => "equip abilities"
  | .sourceMatches pred => s!"abilities of {pred.label} sources"

end ManaAbilityPred

instance : HasTextChange ManaAbilityPred where
  applyTextChanges tcs p :=
    if tcs.isEmpty then p
    else
      match p with
      | .equip => .equip
      | .sourceMatches pred => .sourceMatches (HasTextChange.applyTextChanges tcs pred)

/-- Compositional mana spending restriction and optional spell rider (CR 106.6).
Unrestricted mana is represented as `Option.none : Option ManaSpendRestriction`. -/
inductive ManaSpendRestriction where
  /-- Spend only to cast spells matching `pred`, optionally granting `riders` (CR 106.6). -/
  | onlyForSpells (pred : ManaObjectPred) (riders : Array SpellRiderSpec := #[])
  /-- Spend only to activate abilities matching `pred` (CR 106.6). -/
  | onlyForAbilities (pred : ManaAbilityPred)
  /-- Spend only to cast spells matching `spellPred` or activate abilities matching `abilityPred`. -/
  | onlyForSpellsOrAbilities (spellPred : ManaObjectPred) (abilityPred : ManaAbilityPred)
      (riders : Array SpellRiderSpec := #[])
  /-- Cannot be spent to cast spells matching `pred` (CR 106.6, e.g. nonartifact spells). -/
  | cantSpendOnSpells (pred : ManaObjectPred)
  /-- Cannot be spent to cast spells from `zone` (CR 106.6, e.g. from hand). -/
  | notFromZone (zone : ZoneKind)
deriving DecidableEq, Repr, Inhabited, BEq

namespace ManaSpendRestriction

/-- Spend only to cast spells of `subtype` (CR 106.6). -/
def subtypeSpell (subtype : CardSubtype) : ManaSpendRestriction :=
  .onlyForSpells (.hasSubtype subtype)

/-- Spend only to cast spells of `subtype` or activate abilities of `subtype` sources (CR 106.6). -/
def subtypeSpellOrSource (subtype : CardSubtype) : ManaSpendRestriction :=
  .onlyForSpellsOrAbilities (.hasSubtype subtype) (.sourceMatches (.hasSubtype subtype))

/-- Spend only to cast `<subtype>`, Equipment, and Saga spells (CR 106.6). -/
def subtypeEquipmentSagaSpell (subtype : CardSubtype) : ManaSpendRestriction :=
  .onlyForSpells (.or (.hasSubtype subtype) (.or (.hasSubtype .equipment) (.hasSubtype .saga)))

/-- Spend only on Elf spells and abilities (CR 106.6). -/
def elf : ManaSpendRestriction := subtypeSpellOrSource .elf

/-- Spend only on Hero spells and abilities (CR 106.6). -/
def hero : ManaSpendRestriction := subtypeSpellOrSource .hero

/-- Spend only on Villain spells and abilities (CR 106.6). -/
def villain : ManaSpendRestriction := subtypeSpellOrSource .villain

/-- Spend only to cast instant or sorcery spells (CR 106.6). -/
def instantOrSorcery : ManaSpendRestriction :=
  .onlyForSpells (.or (.hasType .instant) (.hasType .sorcery))

/-- Cannot be spent to cast a nonartifact spell (CR 106.6). -/
def cantNonartifact : ManaSpendRestriction :=
  .cantSpendOnSpells (.not (.hasType .artifact))

/-- Spend only to activate abilities of creature sources (CR 106.6). -/
def creatureSource : ManaSpendRestriction :=
  .onlyForAbilities (.sourceMatches (.hasType .creature))

/-- Cannot be spent to cast spells from your hand (CR 106.6). -/
def notSpellsFromHand : ManaSpendRestriction :=
  .notFromZone .hand

/-- Spend only to cast planeswalker spells (CR 106.6). -/
def planeswalkerSpell : ManaSpendRestriction :=
  .onlyForSpells (.hasType .planeswalker)

/-- Spend only to cast noncreature spells (CR 106.6). -/
def noncreatureSpell : ManaSpendRestriction :=
  .onlyForSpells (.not (.hasType .creature))

/-- Spend only to cast a legendary spell, which then can't be countered (CR 106.6 / 106.12). -/
def legendarySpell : ManaSpendRestriction :=
  .onlyForSpells (.hasSupertype .legendary) #[.cantBeCountered]

/-- Spend only to cast Dwarf, Equipment, and Saga spells (CR 106.6). -/
def dwarfEquipmentSagaSpell : ManaSpendRestriction :=
  subtypeEquipmentSagaSpell .dwarf

/-- Spend only to cast Equipment spells or activate equip abilities (CR 106.6). -/
def equipmentOrEquip : ManaSpendRestriction :=
  .onlyForSpellsOrAbilities (.hasSubtype .equipment) .equip

/-- Spend only to cast artifact spells (CR 106.6). -/
def artifactSpell : ManaSpendRestriction :=
  .onlyForSpells (.hasType .artifact)

/-- Spend only to cast Dragon spells (CR 106.6). -/
def dragonSpell : ManaSpendRestriction :=
  subtypeSpell .dragon

/-- Spell riders carried by this spending restriction (CR 106.6 / 106.12). -/
def riders : ManaSpendRestriction → Array SpellRiderSpec
  | .onlyForSpells _ rs | .onlyForSpellsOrAbilities _ _ rs => rs
  | .onlyForAbilities _ | .cantSpendOnSpells _ | .notFromZone _ => #[]

/-- Whether this restriction grants `rider` to spells cast with this mana (CR 106.6). -/
def grantsRider (r : ManaSpendRestriction) (rider : SpellRiderSpec) : Bool :=
  r.riders.contains rider

/-- Whether `r` is a narrow positive restriction (spent before broad negative
restrictions and unrestricted mana, CR 106.6). -/
def isNarrow : ManaSpendRestriction → Bool
  | .onlyForSpells _ _ | .onlyForAbilities _ | .onlyForSpellsOrAbilities _ _ _ => true
  | .cantSpendOnSpells _ | .notFromZone _ => false

/-- Pure evaluation of whether mana restricted by `r` may pay for `s` (CR 106.6). -/
def allows (r : ManaSpendRestriction) (s : ManaSpend) : Bool :=
  match r with
  | .onlyForSpells pred _ =>
    s.spell && pred.satisfies s.types s.supertypes s.subtypes
  | .onlyForAbilities pred =>
    pred.satisfies s
  | .onlyForSpellsOrAbilities spellPred abPred _ =>
    (s.spell && spellPred.satisfies s.types s.supertypes s.subtypes) || abPred.satisfies s
  | .cantSpendOnSpells pred =>
    !(s.spell && pred.satisfies s.types s.supertypes s.subtypes)
  | .notFromZone z =>
    if !s.spell then true
    else
      match z with
      | .hand => !(s.fromHand || s.castFromZone == some .hand)
      | other => s.castFromZone != some other

/-- Short human-readable label for a spending restriction (used in logs and pool notation). -/
def label : ManaSpendRestriction → String
  | .onlyForSpells pred _ => s!"{pred.label} spells"
  | .onlyForAbilities pred => pred.label
  | .onlyForSpellsOrAbilities (.hasSubtype s1) (.sourceMatches (.hasSubtype s2)) _ =>
    if s1 == s2 then s!"{s1} spells and abilities"
    else s!"{s1} spells and abilities of {s2} sources"
  | .onlyForSpellsOrAbilities (.hasSubtype .equipment) .equip _ =>
    "Equipment spells and equip abilities"
  | .onlyForSpellsOrAbilities sp ab _ => s!"{sp.label} spells and {ab.label}"
  | .cantSpendOnSpells (.not (.hasType .artifact)) => "not a nonartifact spell"
  | .cantSpendOnSpells pred => s!"not {pred.label} spells"
  | .notFromZone .hand => "not spells from hand"
  | .notFromZone z => s!"not spells from {z}"

/-- Parenthesized log note for an optional mana spending restriction. -/
def note : Option ManaSpendRestriction → String
  | none => ""
  | some r => s!" ({r.label})"

private def indefArticle (s : String) : String :=
  match s.toList with
  | c :: _ =>
    let lc := c.toLower
    if lc == 'a' || lc == 'e' || lc == 'i' || lc == 'o' || lc == 'u' then "an" else "a"
  | [] => "a"

/-- Canonical Oracle sentence for `r` (round-trips with `parseOracle?`, CR 106.6). -/
def toOracleSentence (r : ManaSpendRestriction) : String :=
  let riderText (rs : Array SpellRiderSpec) : String :=
    String.join (rs.toList.map SpellRiderSpec.toClause)
  match r with
  | .onlyForSpells pred rs =>
    let objPhrase :=
      match pred with
      | .or _ (.or _ _) => s!"{pred.label} spells"
      | .hasSubtype _ =>
        if rs.isEmpty then s!"{pred.label} spells"
        else s!"{indefArticle pred.label} {pred.label} spell"
      | _ =>
        if rs.isEmpty then s!"{indefArticle pred.label} {pred.label} spell"
        else s!"{indefArticle pred.label} {pred.label} spell"
    s!"Spend this mana only to cast {objPhrase}{riderText rs}."
  | .onlyForAbilities pred =>
    s!"Spend this mana only to activate {pred.label}."
  | .onlyForSpellsOrAbilities sp ab rs =>
    let abClause :=
      match ab with
      | .equip => "or activate equip abilities"
      | .sourceMatches ap => s!"and activate abilities of {ap.label} sources"
    s!"Spend this mana only to cast {sp.label} spells {abClause}{riderText rs}."
  | .cantSpendOnSpells (.not (.hasType .artifact)) =>
    "This mana can't be spent to cast a nonartifact spell."
  | .cantSpendOnSpells pred =>
    s!"This mana can't be spent to cast {indefArticle pred.label} {pred.label} spell."
  | .notFromZone .hand =>
    "This mana can't be spent to cast spells from your hand."
  | .notFromZone z =>
    s!"This mana can't be spent to cast spells from your {z}."

private def parsePredAtom? (raw : String) : Option ManaObjectPred :=
  let s := raw.trimAscii.copy
  let low := s.map Char.toLower
  match low with
  | "noncreature" => some (.not (.hasType .creature))
  | "nonartifact" => some (.not (.hasType .artifact))
  | "nonland" => some (.not (.hasType .land))
  | "nonlegendary" => some (.not (.hasSupertype .legendary))
  | "legendary" => some (.hasSupertype .legendary)
  | "basic" => some (.hasSupertype .basic)
  | "snow" => some (.hasSupertype .snow)
  | "artifact" => some (.hasType .artifact)
  | "battle" => some (.hasType .battle)
  | "creature" => some (.hasType .creature)
  | "enchantment" => some (.hasType .enchantment)
  | "instant" => some (.hasType .instant)
  | "kindred" => some (.hasType .kindred)
  | "land" => some (.hasType .land)
  | "planeswalker" => some (.hasType .planeswalker)
  | "sorcery" => some (.hasType .sorcery)
  | _ => (CardSubtype.ofOracle? s).map ManaObjectPred.hasSubtype

private def stripArticle (s : String) : String :=
  let s := s.trimAscii.copy
  let low := s.map Char.toLower
  if low.startsWith "an " then (s.drop 3).trimAscii.copy
  else if low.startsWith "a " then (s.drop 2).trimAscii.copy
  else s

private def parseSpellPredList? (raw : String) : Option ManaObjectPred :=
  let s := stripArticle raw
  let splitComma := s.splitOn ","
  let parts := splitComma.foldl (fun acc seg =>
    let seg := seg.trimAscii.copy
    if seg.isEmpty then acc
    else
      let segLow := seg.map Char.toLower
      let seg :=
        if segLow.startsWith "and " then (seg.drop 4).trimAscii.copy
        else if segLow.startsWith "or " then (seg.drop 3).trimAscii.copy
        else seg
      let subParts :=
        if (seg.map Char.toLower).contains " or " then
          seg.splitOn " or "
        else if (seg.map Char.toLower).contains " and " then
          seg.splitOn " and "
        else [seg]
      acc ++ (subParts.map (fun x => x.trimAscii.copy) |>.filter (!·.isEmpty))) []
  if parts.isEmpty then none
  else
    let rec go : List String → Option ManaObjectPred
      | [] => none
      | [x] =>
        match parsePredAtom? x with
        | some p => some p
        | none =>
          -- Support multi-word conjunctions like `"legendary creature"` or `"artifact creature"`.
          let words := (x.splitOn " ").filter (!·.isEmpty)
          if words.length ≥ 2 then
            (words.mapM parsePredAtom?).map (fun ps => ManaObjectPred.allOf ps.toArray)
          else none
      | x :: rest =>
        match parsePredAtom? x, go rest with
        | some a, some b => some (.or a b)
        | _, _ => none
    go parts

private def parseSmallCount (s : String) : Option Nat :=
  let low := s.trimAscii.copy.map Char.toLower
  match low with
  | "a" | "an" | "one" => some 1
  | "two" => some 2
  | "three" => some 3
  | "four" => some 4
  | "five" => some 5
  | _ => if !low.isEmpty && low.all Char.isDigit then low.toNat? else none

/-- Parse a trailing rider clause such as `", and that spell can't be countered"`,
`", and that creature gains haste"`, or
`", and that creature enters with an additional +1/+1 counter on it"`. -/
private def stripRiders (s : String) : String × Array SpellRiderSpec := Id.run do
  let mut cur := s.trimAscii.copy
  let mut rs : Array SpellRiderSpec := #[]
  let mut progress := true
  while progress do
    progress := false
    let low := cur.map Char.toLower
    if low.endsWith ", and that spell can't be countered" then
      cur := (cur.take (cur.length - ", and that spell can't be countered".length)).trimAscii.copy
      rs := #[.cantBeCountered] ++ rs
      progress := true
    else if low.endsWith ", and that creature gains haste" then
      cur := (cur.take (cur.length - ", and that creature gains haste".length)).trimAscii.copy
      rs := #[.gainsHaste] ++ rs
      progress := true
    else if low.endsWith ", and it gains haste" then
      cur := (cur.take (cur.length - ", and it gains haste".length)).trimAscii.copy
      rs := #[.gainsHaste] ++ rs
      progress := true
    else
      let marker := ", and that creature enters with "
      match low.splitOn marker with
      | [lhs, rhs] =>
        if rhs.contains "additional +1/+1 counter" then
          let countTok := ((rhs.splitOn " additional +1/+1 counter").headD "").trimAscii.copy
          if let some n := parseSmallCount countTok then
            cur := (cur.take lhs.length).trimAscii.copy
            rs := #[.entersWithPlusOneCounters n] ++ rs
            progress := true
      | _ => pure ()
  return (cur, rs)

private def parseAbilityClause? (raw : String) : Option ManaAbilityPred :=
  let s := raw.trimAscii.copy
  let low := s.map Char.toLower
  let s :=
    if low.startsWith "to activate " then (s.drop "to activate ".length).trimAscii.copy
    else if low.startsWith "activate " then (s.drop "activate ".length).trimAscii.copy
    else s
  let low := s.map Char.toLower
  if low == "equip abilities" || low == "an equip ability" then
    some .equip
  else
    let afterOf? : Option String :=
      if low.startsWith "abilities of " then some (s.drop "abilities of ".length).trimAscii.copy
      else if low.startsWith "an ability of " then some (s.drop "an ability of ".length).trimAscii.copy
      else if low.startsWith "activated abilities of " then
        some (s.drop "activated abilities of ".length).trimAscii.copy
      else none
    afterOf?.bind fun tail =>
      let tailLow := tail.map Char.toLower
      let stem? :=
        if tailLow.endsWith " sources" then
          some (tail.take (tail.length - " sources".length)).trimAscii.copy
        else if tailLow.endsWith " source" then
          some (tail.take (tail.length - " source".length)).trimAscii.copy
        else none
      stem?.bind fun stem =>
        (parseSpellPredList? stem).map ManaAbilityPred.sourceMatches

private def parseSpellClause? (raw : String) : Option ManaObjectPred :=
  let s := raw.trimAscii.copy
  let low := s.map Char.toLower
  let s :=
    if low.startsWith "to cast " then (s.drop "to cast ".length).trimAscii.copy
    else if low.startsWith "cast " then (s.drop "cast ".length).trimAscii.copy
    else s
  let low := s.map Char.toLower
  let stem? : Option String :=
    if low.endsWith " spells" then
      some (s.take (s.length - " spells".length)).trimAscii.copy
    else if low.endsWith " spell" then
      some (s.take (s.length - " spell".length)).trimAscii.copy
    else none
  stem?.bind parseSpellPredList?

private def parseZoneWord? (raw : String) : Option ZoneKind :=
  match raw.trimAscii.copy.map Char.toLower with
  | "hand" | "your hand" => some .hand
  | "graveyard" | "your graveyard" => some .graveyard
  | "exile" => some .exile
  | "library" | "your library" => some .library
  | "command zone" => some .command
  | _ => none

/-- Parse an Oracle spending-restriction sentence or clause into a structured
`ManaSpendRestriction` at card parse time (CR 106.6). Accepts both full
sentences (`"Spend this mana only to cast ..."`, `"This mana can't be spent to
cast ..."`) and clause fragments (`"Dwarf, Equipment, and Saga spells"`,
`"a legendary spell, and that spell can't be countered"`,
`"Equipment spells or activate equip abilities"`, `"not spells from hand"`). -/
def parseOracle? (raw : String) : Option ManaSpendRestriction := Id.run do
  let s := (raw.replace "." "").trimAscii.copy
  let low := s.map Char.toLower
  if s.isEmpty then return none

  -- 1. Negative `"This mana can't be spent to cast ..."` / `"not ..."` clauses.
  if let some rest :=
      if low.startsWith "this mana can't be spent to cast " then
        some (s.drop "this mana can't be spent to cast ".length).trimAscii.copy
      else if low.startsWith "not to cast " then
        some (s.drop "not to cast ".length).trimAscii.copy
      else if low.startsWith "not " then
        some (s.drop "not ".length).trimAscii.copy
      else none then
    let rLow := rest.map Char.toLower
    if rLow.startsWith "spells from " then
      let zStr := (rest.drop "spells from ".length).trimAscii.copy
      if let some z := parseZoneWord? zStr then
        return some (.notFromZone z)
    if let some pred := parseSpellClause? rest then
      return some (.cantSpendOnSpells pred)
    if rLow == "nonartifact spell" || rLow == "a nonartifact spell" then
      return some .cantNonartifact
    return none

  if (low.contains "from your hand" || low.contains "from hand") &&
      (low.contains "not" || low.contains "can't") then
    return some .notSpellsFromHand

  -- 2. Strip optional `"Spend this mana only "` / `"Spend this mana only to "` prefix.
  let body :=
    if low.startsWith "spend this mana only to " then
      (s.drop "spend this mana only to ".length).trimAscii.copy
    else if low.startsWith "spend this mana only " then
      (s.drop "spend this mana only ".length).trimAscii.copy
    else s
  let (core, riders) := stripRiders body
  let coreLow := core.map Char.toLower

  -- 3. Short-hand `"<Subtype> spells and abilities"`.
  if coreLow.endsWith " spells and abilities" then
    let stem := (core.take (core.length - " spells and abilities".length)).trimAscii.copy
    if let some sub := CardSubtype.ofOracle? stem then
      return some (.onlyForSpellsOrAbilities (.hasSubtype sub) (.sourceMatches (.hasSubtype sub)) riders)

  -- 4. Combined `"cast <spell> [or/and] [to] activate <ability>"`.
  let splitAct? : Option (String × String) :=
    let markers := [
      " or to activate ", " and to activate ",
      " or activate ", " and activate "
    ]
    markers.findSome? fun m =>
      match coreLow.splitOn m with
      | [lhs, _] =>
        let rhs := (core.drop (lhs.length + m.length)).trimAscii.copy
        some ((core.take lhs.length).trimAscii.copy, "activate " ++ rhs)
      | _ => none
  if let some (spStr, abStr) := splitAct? then
    if let some sp := parseSpellClause? spStr then
      if let some ab := parseAbilityClause? abStr then
        return some (.onlyForSpellsOrAbilities sp ab riders)

  if coreLow == "equipment spells and equip abilities" then
    return some (.onlyForSpellsOrAbilities (.hasSubtype .equipment) .equip riders)

  -- 5. Pure ability restriction (`"activate abilities of creature sources"`, `"equip abilities"`).
  if let some ab := parseAbilityClause? core then
    return some (.onlyForAbilities ab)

  -- 6. Pure spell restriction (`"cast ... spell(s)"`, `"Dragon spells"`, `"Dwarf, Equipment, and Saga spells"`).
  if let some sp := parseSpellClause? core then
    return some (.onlyForSpells sp riders)

  return none

end ManaSpendRestriction

instance : HasTextChange ManaSpendRestriction where
  applyTextChanges tcs r :=
    if tcs.isEmpty then r
    else
      match r with
      | .onlyForSpells pred riders =>
        .onlyForSpells (HasTextChange.applyTextChanges tcs pred) riders
      | .onlyForAbilities pred =>
        .onlyForAbilities (HasTextChange.applyTextChanges tcs pred)
      | .onlyForSpellsOrAbilities sp ab riders =>
        .onlyForSpellsOrAbilities (HasTextChange.applyTextChanges tcs sp)
          (HasTextChange.applyTextChanges tcs ab) riders
      | .cantSpendOnSpells pred =>
        .cantSpendOnSpells (HasTextChange.applyTextChanges tcs pred)
      | .notFromZone z => .notFromZone z

end Mtg.Engine
