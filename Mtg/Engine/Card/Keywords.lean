/-!
# Keyword abilities (CR 702)

The keyword flags a card can carry, the merge/print helpers, and the
single-keyword `Keyword.*` values.
-/

namespace Mtg.Engine

/-- Keyword abilities that the engine currently understands. -/
structure Keywords where
  flash : Bool := false
  haste : Bool := false
  vigilance : Bool := false
  flying : Bool := false
  /-- This creature can't be blocked (printed or granted until end of turn). -/
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

/-- One modeled keyword ability (CR 702). Coerces to a `Keywords` singleton
so existing `keywords := Keyword.lifelink` call sites keep working. -/
inductive Keyword where
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
  /-- Equip (CR 702.6): printed with a cost, e.g. Equip {2}. -/
  | equip
deriving DecidableEq, Repr, Inhabited, BEq

namespace Keyword

/-- Singleton `Keywords` value for this keyword. -/
def toKeywords : Keyword → Keywords
  | .flash => { Keywords.none with flash := true }
  | .haste => { Keywords.none with haste := true }
  | .vigilance => { Keywords.none with vigilance := true }
  | .flying => { Keywords.none with flying := true }
  | .cantBeBlocked => { Keywords.none with cantBeBlocked := true }
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
  | .equip => Keywords.none

/-- Union of two single keywords. -/
def merge (a b : Keyword) : Keywords :=
  a.toKeywords.merge b.toKeywords

instance : Coe Keyword Keywords where
  coe := toKeywords

instance : ToString Keyword where
  toString k := toString k.toKeywords

end Keyword

end Mtg.Engine
