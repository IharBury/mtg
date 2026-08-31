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

/- Singleton keyword values. Named separately from `Keywords` so they do not
clash with the structure fields of the same name. Combine with `Keywords.merge`. -/
namespace Keyword
def flash : Keywords := { Keywords.none with flash := true }
def haste : Keywords := { Keywords.none with haste := true }
def vigilance : Keywords := { Keywords.none with vigilance := true }
def flying : Keywords := { Keywords.none with flying := true }
def cantBeBlocked : Keywords := { Keywords.none with cantBeBlocked := true }
def menace : Keywords := { Keywords.none with menace := true }
def hexproof : Keywords := { Keywords.none with hexproof := true }
def indestructible : Keywords := { Keywords.none with indestructible := true }
def reach : Keywords := { Keywords.none with reach := true }
def trample : Keywords := { Keywords.none with trample := true }
def deathtouch : Keywords := { Keywords.none with deathtouch := true }
def defender : Keywords := { Keywords.none with defender := true }
def lifelink : Keywords := { Keywords.none with lifelink := true }
def firstStrike : Keywords := { Keywords.none with firstStrike := true }
def islandwalk : Keywords := { Keywords.none with islandwalk := true }
def storied : Keywords := { Keywords.none with storied := true }
def doubleStrike : Keywords := { Keywords.none with doubleStrike := true }
def prowess : Keywords := { Keywords.none with prowess := true }
def ascend : Keywords := { Keywords.none with ascend := true }
def shadow : Keywords := { Keywords.none with shadow := true }
def changeling : Keywords := { Keywords.none with changeling := true }
end Keyword

end Mtg.Engine
