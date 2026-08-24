import Mtg.Engine.Color
import Mtg.Engine.Mana
import Mtg.Engine.TypeLine

/-!
# Card characteristics (CR 108, 109.3, section 2)

A card’s Oracle characteristics: name, mana cost, color, type line, rules
text, and (when applicable) power, toughness, and keywords we currently
model.
-/

namespace Mtg.Engine

/-- Keyword abilities that the engine currently understands. -/
structure Keywords where
  haste : Bool := false
  flying : Bool := false
  reach : Bool := false
  trample : Bool := false
  deathtouch : Bool := false
  defender : Bool := false
deriving BEq, Repr, Inhabited

namespace Keywords

def none : Keywords := {}

def toList (k : Keywords) : List String :=
  (if k.haste then ["haste"] else []) ++
  (if k.flying then ["flying"] else []) ++
  (if k.reach then ["reach"] else []) ++
  (if k.trample then ["trample"] else []) ++
  (if k.deathtouch then ["deathtouch"] else []) ++
  (if k.defender then ["defender"] else [])

instance : ToString Keywords where
  toString k :=
    let ks := k.toList
    if ks.isEmpty then "" else String.intercalate ", " ks

end Keywords

/-- One-shot effect of a spell on resolution. Targeting is stored on the stack object. -/
inductive SpellEffect where
  /-- Deal `amount` damage to the chosen target (player or creature). -/
  | dealDamage (amount : Nat)
  /-- Target creature gets +P/+T until end of turn. -/
  | pump (power toughness : Int)
deriving Repr, Inhabited, BEq

/-- Printed (Oracle) characteristics of a card. -/
structure CardDef where
  name : String
  manaCost : ManaCost := ManaCost.empty
  types : Array CardType
  subtypes : Array Subtype := #[]
  supertypes : Array Supertype := #[]
  oracleText : String := ""
  power : Option Int := none
  toughness : Option Int := none
  loyalty : Option Int := none
  /-- Explicit color indicator, if any (CR 107.13 / 202.2). -/
  colorIndicator : Option ColorSet := none
  keywords : Keywords := Keywords.none
  spellEffect : Option SpellEffect := none
  /-- Additional `{T}: Add _` abilities that are not implied by basic land types. -/
  tapAddMana : Array ManaType := #[]
deriving Repr, Inhabited

namespace CardDef

/-- Color from color indicator, otherwise from mana cost (CR 202.2). -/
def colors (c : CardDef) : ColorSet :=
  match c.colorIndicator with
  | some cs => cs
  | none => c.manaCost.colors

def isLand (c : CardDef) : Bool := c.types.any (· == .land)
def isCreature (c : CardDef) : Bool := c.types.any (· == .creature)
def isInstant (c : CardDef) : Bool := c.types.any (· == .instant)
def isSorcery (c : CardDef) : Bool := c.types.any (· == .sorcery)
def isPermanentCard (c : CardDef) : Bool := c.types.any CardType.isPermanentType

/-- Timing of a sorcery: also the default for permanent spells without flash (CR 302.1, 307.1). -/
def hasSorcerySpeed (c : CardDef) : Bool :=
  !c.isInstant && !c.isLand

def hasInstantSpeed (c : CardDef) : Bool :=
  c.isInstant

def manaValue (c : CardDef) : Nat := c.manaCost.manaValue

/-- Basic land types on this card produce the corresponding mana (CR 305.6). -/
def basicLandMana (c : CardDef) : Array Color :=
  c.subtypes.filterMap manaForBasicLandType

/-- All `{T}: Add` mana types this card can produce. -/
def manaAbilities (c : CardDef) : Array ManaType :=
  c.basicLandMana.map ManaType.colored ++ c.tapAddMana

def typeLine (c : CardDef) : String :=
  let super := String.intercalate " " (c.supertypes.toList.map toString)
  let types := String.intercalate " " (c.types.toList.map toString)
  let sub := String.intercalate " " c.subtypes.toList
  let head :=
    if super.isEmpty then types else s!"{super} {types}"
  if sub.isEmpty then head else s!"{head} — {sub}"

def ptString (c : CardDef) : String :=
  match c.power, c.toughness with
  | some p, some t => s!"{p}/{t}"
  | _, _ => ""

def summary (c : CardDef) : String :=
  let cost := toString c.manaCost
  let pt := c.ptString
  let kw := toString c.keywords
  let extras :=
    [pt, kw].filter (fun s => !s.isEmpty) |> fun xs =>
      if xs.isEmpty then "" else " " ++ String.intercalate " " xs
  s!"{c.name} {cost} {c.typeLine}{extras}"

instance : ToString CardDef where
  toString := summary

end CardDef

/-- Constructed-play four-of rule applies to non-basic-land English names (CR 100.2a). -/
def isBasicLandCard (c : CardDef) : Bool :=
  c.isLand && c.supertypes.any (· == .basic)

end Mtg.Engine
