import Mtg.Engine.Color
import Mtg.Engine.TypeLine
import Mtg.Engine.Zone
import Mtg.Engine.Turn

/-!
# Shared CR Primitives (Layer 0)

Canonical value-level Comprehensive Rules (effective 25 September 2026) enums
and algebraic primitives shared by `Mtg.Engine.Card` and `Mtg.Engine.Game`.
Keeping these types in `Mtg.Engine.Card` lets ability ASTs align directly with
`RulesEvent`, `EventCause`, and CR 613 layer evaluation while keeping
`Mtg.Engine.Card` strictly independent of `Mtg.Engine.Game`.
-/

namespace Mtg.Engine

/-- Owner-parametric zone kind corresponding to `Zone` (CR 400.1). -/
inductive ZoneKind where
  /-- Per-player hidden library zone (CR 401). -/
  | library
  /-- Per-player hidden hand zone (CR 402). -/
  | hand
  /-- Shared public battlefield zone (CR 403). -/
  | battlefield
  /-- Per-player public graveyard zone (CR 404). -/
  | graveyard
  /-- Shared public stack zone (CR 405). -/
  | stack
  /-- Shared public exile zone (CR 406). -/
  | exile
  /-- Shared public command zone (CR 408). -/
  | command
  /-- Legacy ante zone (CR 407). -/
  | ante
  /-- Cards outside the game, e.g. sideboards (CR 400.11b). -/
  | outside
deriving DecidableEq, Repr, Inhabited, BEq

namespace ZoneKind

/-- Whether zones of this kind are public (CR 400.2). -/
def isPublic : ZoneKind → Bool
  | .library | .hand | .outside => false
  | .battlefield | .graveyard | .stack | .exile | .command | .ante => true

/-- Whether zones of this kind are hidden (CR 400.2). -/
def isHidden (k : ZoneKind) : Bool := !k.isPublic

/-- Whether each player has their own zone of this kind (CR 400.1). -/
def isOwned : ZoneKind → Bool
  | .library | .hand | .graveyard => true
  | _ => false

/-- Instantiate a `ZoneKind` for an owning player when owner-scoped (CR 400.1). -/
def toZone (k : ZoneKind) (owner : PlayerId) : Zone :=
  match k with
  | .library => .library owner
  | .hand => .hand owner
  | .battlefield => .battlefield
  | .graveyard => .graveyard owner
  | .stack => .stack
  | .exile => .exile
  | .command => .command
  | .ante => .ante
  | .outside => .outside owner

def englishName : ZoneKind → String
  | .library => "library"
  | .hand => "hand"
  | .battlefield => "battlefield"
  | .graveyard => "graveyard"
  | .stack => "stack"
  | .exile => "exile"
  | .command => "command"
  | .ante => "ante"
  | .outside => "outside the game"

instance : ToString ZoneKind where
  toString := englishName

end ZoneKind

/-- Project a concrete `Zone` to its owner-parametric `ZoneKind` (CR 400.1). -/
def Zone.kind : Zone → ZoneKind
  | .library _ => .library
  | .hand _ => .hand
  | .battlefield => .battlefield
  | .graveyard _ => .graveyard
  | .stack => .stack
  | .exile => .exile
  | .command => .command
  | .ante => .ante
  | .outside _ => .outside

/-- Why an object moved between zones (CR 400.6, 121.1, 701.8, 701.9, 701.17, 701.21). -/
inductive ZoneVerb where
  | cast
  | draw (nth : Nat) (firstOfOwnDrawStep : Bool := false)
  | discard
  | mill
  | sacrifice
  | destroy
  | exile
  | counter
  | resolve
  | put
  | returnToHand
  | shuffleIntoLibrary
  | playLand
deriving DecidableEq, Repr, Inhabited, BEq

/-- Where an object is placed in a library when moving to `.library _` (CR 401). -/
inductive LibraryPosition where
  | top
  | bottom
  | fromTop (offset : Nat)
  | shuffledIn
deriving DecidableEq, Repr, Inhabited, BEq

/-- Parameter-free designation tag for card-level predicates and filters
(CR 400.7 / 701.15b / 701.54b). -/
inductive PermanentDesignationTag where
  | ringBearer
  | goaded
  | prepared
  | harnessed
deriving DecidableEq, Repr, Inhabited, BEq

/-- Designations a permanent can have on the battlefield (CR 400.7 / 701.15b / 701.54b). -/
inductive PermanentDesignation where
  | ringBearer                                                  -- CR 701.54a
  | goaded (byPlayer : PlayerId) (untilNextTurn : Bool := true) -- CR 701.15b
  | prepared                                                    -- set mechanic
  | harnessed                                                   -- set mechanic
deriving DecidableEq, Repr, Inhabited, BEq

/-- Project a concrete `PermanentDesignation` to its parameter-free `PermanentDesignationTag`. -/
def PermanentDesignation.tag : PermanentDesignation → PermanentDesignationTag
  | .ringBearer => .ringBearer
  | .goaded _ _ => .goaded
  | .prepared => .prepared
  | .harnessed => .harnessed

/-- Lasting player designations (CR 702.131). -/
inductive PlayerDesignation where
  | citysBlessing
  | enduringStory
deriving DecidableEq, Repr, Inhabited, BEq

/-- A cost payment kind (CR 118, 601.2h, 602.2b, 606.4). -/
inductive CostKind where
  | mana                -- CR 118.3
  | tap                 -- CR 118.3 / 602.2b ({T} symbol or "Tap an untapped …")
  | untap               -- CR 118.3 ({Q} symbol)
  | life                -- CR 118.3 / 119.4 ("Pay N life")
  | sacrifice           -- CR 118.3 / 701.21
  | discard             -- CR 118.3 / 701.9
  | exile               -- CR 118.3 / 406
  | removeCounters      -- CR 118.3 / 122.1
  | loyalty             -- CR 606.4 (+N, -N, 0 on a planeswalker)
  | collectEvidence     -- CR 701.59
  | behold              -- CR 701.4
  | waterbend           -- CR 701.67
  | convoke             -- CR 702.51
  | delve               -- CR 702.66
  | emerge              -- CR 702.119
  | casualty            -- CR 702.153
  | bargain             -- CR 702.166
  | ward                -- CR 702.21
  | teamwork            -- CR 702.194
  | returnToHand        -- CR 118.3 / 702.190a (sneak / return permanent to hand)
  | putCounters         -- CR 118.3 / 122.1
  | cycle               -- CR 702.29
deriving DecidableEq, Repr, Inhabited, BEq

/-- Priority tiers for choosing among multiple applicable replacement or
prevention effects on the same event (CR 616.1a–e). -/
inductive ReplacementTier where
  /-- CR 616.1a: Self-replacement effects of a resolving spell or ability (CR 614.15). -/
  | self
  /-- CR 616.1b: Effects modifying under whose control an object enters the battlefield. -/
  | control
  /-- CR 616.1c: Effects making an object become a copy as it enters the battlefield. -/
  | copy
  /-- CR 616.1d: Effects causing an object to enter the battlefield with its back face up. -/
  | backFaceUp
  /-- CR 303.4f–g: Choosing an object for a non-cast Aura to enchant as it enters. -/
  | auraHost
  /-- CR 616.1e: Any other applicable replacement or prevention effect. -/
  | other
deriving DecidableEq, Repr, Inhabited, BEq

/-- Numeric priority rank for `ReplacementTier` (CR 616.1a–e): smaller ranks
apply first. -/
def ReplacementTier.rank : ReplacementTier → Nat
  | .self => 0
  | .control => 1
  | .copy => 2
  | .backFaceUp => 3
  | .auraHost => 4
  | .other => 5

/-- Mode for Layer 4 (types) and Layer 5 (colors) continuous effects (CR 205.1a–b / 613.1d–e). -/
inductive SetOrAdd where
  /-- Replace existing types/subtypes/colors with the given set (CR 205.1a). -/
  | set
  /-- Add the given types/subtypes/colors in addition to existing ones (CR 205.1b). -/
  | add
  /-- Add the given subtypes in addition to existing ones, deduplicating if already present. -/
  | addDedup
  /-- Replace existing creature subtypes with the given subtypes while keeping noncreature subtypes (CR 205.1a). -/
  | setAndKeepNoncreatureSubtypes
deriving DecidableEq, Repr, Inhabited, BEq

/-- Whether `sub` is correlated with at least one card type in `ts` (CR 205.3d). -/
def CardSubtype.isCorrelatedWith (ts : Array CardType) (sub : CardSubtype) : Bool :=
  match sub.kind with
  | .artifact => ts.contains .artifact
  | .enchantment => ts.contains .enchantment
  | .land => ts.contains .land
  | .planeswalker => ts.contains .planeswalker
  | .spell => ts.contains .instant || ts.contains .sorcery
  | .creature => ts.contains .creature || ts.contains .kindred
  | .planar => ts.contains .plane
  | .dungeon => ts.contains .dungeon
  | .battle => ts.contains .battle

/-- Basic land subtype to the color of mana its CR 305.6 intrinsic mana ability produces. -/
def CardSubtype.basicLandManaColor? : CardSubtype → Option Color
  | .plains => some .white
  | .island => some .blue
  | .swamp => some .black
  | .mountain => some .red
  | .forest => some .green
  | _ => none

/-- True when `sub` is one of the five basic land types (CR 305.6). -/
def CardSubtype.isBasicLandType (sub : CardSubtype) : Bool :=
  sub.basicLandManaColor?.isSome

/-- Compositional Layer 4 type/subtype/supertype modification (CR 205.1a–b / 205.3d / 613.1d). -/
structure TypeSetMod where
  mode : SetOrAdd := .add
  types : Array CardType := #[]
  subtypes : Array CardSubtype := #[]
  supertypes : Array Supertype := #[]
  removeTypes : Array CardType := #[]
  removeSubtypes : Array CardSubtype := #[]
  removeSupertypes : Array Supertype := #[]
deriving DecidableEq, Repr, Inhabited, BEq

namespace TypeSetMod

private def pushDedup {α : Type} [BEq α] (acc elems : Array α) : Array α :=
  elems.foldl (fun a x => if a.contains x then a else a.push x) acc

/-- Apply a compositional Layer 4 type/subtype/supertype modification, enforcing
CR 205.3d subtype correlation whenever card types are replaced or removed and
CR 305.7 / 205.3m land-only subtype replacement when setting land subtypes
without replacing card types. -/
def apply (m : TypeSetMod) (ts : Array CardType) (subs : Array CardSubtype)
    (sups : Array Supertype) : Array CardType × Array CardSubtype × Array Supertype :=
  match m.mode with
  | .set =>
    let ts1 := if m.types.isEmpty then ts else m.types
    let ts' := if m.removeTypes.isEmpty then ts1 else ts1.filter (!m.removeTypes.contains ·)
    let subs1 :=
      if !m.subtypes.isEmpty then
        if m.types.isEmpty && m.subtypes.all (·.kind == .land) then
          subs.filter (fun s => s.kind != .land && CardSubtype.isCorrelatedWith ts' s) ++ m.subtypes
        else m.subtypes
      else subs.filter (CardSubtype.isCorrelatedWith ts')
    let subs' := if m.removeSubtypes.isEmpty then subs1 else subs1.filter (!m.removeSubtypes.contains ·)
    let sups1 := if m.supertypes.isEmpty then sups else m.supertypes
    let sups' := if m.removeSupertypes.isEmpty then sups1 else sups1.filter (!m.removeSupertypes.contains ·)
    (ts', subs', sups')
  | .add =>
    let ts1 := if m.removeTypes.isEmpty then ts else ts.filter (!m.removeTypes.contains ·)
    let ts' := pushDedup ts1 m.types
    let subs1 := if m.removeTypes.isEmpty then subs else subs.filter (CardSubtype.isCorrelatedWith ts')
    let subs2 := if m.removeSubtypes.isEmpty then subs1 else subs1.filter (!m.removeSubtypes.contains ·)
    let sups1 := if m.removeSupertypes.isEmpty then sups else sups.filter (!m.removeSupertypes.contains ·)
    (ts', subs2 ++ m.subtypes, pushDedup sups1 m.supertypes)
  | .addDedup =>
    let ts1 := if m.removeTypes.isEmpty then ts else ts.filter (!m.removeTypes.contains ·)
    let ts' := pushDedup ts1 m.types
    let subs1 := if m.removeTypes.isEmpty then subs else subs.filter (CardSubtype.isCorrelatedWith ts')
    let subs2 := if m.removeSubtypes.isEmpty then subs1 else subs1.filter (!m.removeSubtypes.contains ·)
    let sups1 := if m.removeSupertypes.isEmpty then sups else sups.filter (!m.removeSupertypes.contains ·)
    (ts', pushDedup subs2 m.subtypes, pushDedup sups1 m.supertypes)
  | .setAndKeepNoncreatureSubtypes =>
    let ts1 := if m.removeTypes.isEmpty then ts else ts.filter (!m.removeTypes.contains ·)
    let ts' := pushDedup ts1 m.types
    let subs1 :=
      subs.filter (fun s =>
        s.isNoncreature && (m.removeTypes.isEmpty || CardSubtype.isCorrelatedWith ts' s))
    let subs2 := if m.removeSubtypes.isEmpty then subs1 else subs1.filter (!m.removeSubtypes.contains ·)
    let sups1 := if m.removeSupertypes.isEmpty then sups else sups.filter (!m.removeSupertypes.contains ·)
    (ts', subs2 ++ m.subtypes, pushDedup sups1 m.supertypes)

end TypeSetMod

/-- Compositional Layer 5 color modification (CR 202.2 / 613.1e). -/
structure ColorSetMod where
  mode : SetOrAdd := .add
  colors : ColorSet := ColorSet.empty
  removeColors : ColorSet := ColorSet.empty
deriving DecidableEq, Repr, Inhabited, BEq

namespace ColorSetMod

/-- Apply a compositional Layer 5 color modification (CR 613.1e). -/
def apply (m : ColorSetMod) (cur : ColorSet) : ColorSet :=
  let base :=
    match m.mode with
    | .set => m.colors
    | .add | .addDedup => ColorSet.union cur m.colors
    | .setAndKeepNoncreatureSubtypes => cur
  ColorSet.diff base m.removeColors

end ColorSetMod

/-- Layer 3 text-changing effect (CR 612 / 613.1c). -/
inductive TextChange where
  | replaceCreatureType (fromSub toSub : CardSubtype)
  | replaceColorWord (fromCol toCol : Color)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Functorial Layer 3 text-change application (CR 612.2 / 613.1c).
Every ability, filter, token spec, mana restriction, and expression AST node
implements this class so Layer 3 text changes transform printed text uniformly. -/
class HasTextChange (α : Type) where
  applyTextChanges : Array TextChange → α → α

instance : HasTextChange CardSubtype where
  applyTextChanges tcs sub :=
    if tcs.isEmpty then sub
    else
      tcs.foldl (fun cur tc =>
        match tc with
        | .replaceCreatureType fromSub toSub => if cur == fromSub then toSub else cur
        | .replaceColorWord _ _ => cur) sub

instance : HasTextChange Color where
  applyTextChanges tcs c :=
    if tcs.isEmpty then c
    else
      tcs.foldl (fun cur tc =>
        match tc with
        | .replaceColorWord fromC toC => if cur == fromC then toC else cur
        | .replaceCreatureType _ _ => cur) c

instance : HasTextChange ColorSet where
  applyTextChanges tcs cs :=
    if tcs.isEmpty || cs.isColorless then cs
    else ColorSet.ofList (cs.toList.map (HasTextChange.applyTextChanges tcs))

instance {α : Type} [HasTextChange α] : HasTextChange (Option α) where
  applyTextChanges tcs x :=
    if tcs.isEmpty then x else x.map (HasTextChange.applyTextChanges tcs)

instance {α : Type} [HasTextChange α] : HasTextChange (Array α) where
  applyTextChanges tcs xs :=
    if tcs.isEmpty || xs.isEmpty then xs else xs.map (HasTextChange.applyTextChanges tcs)

instance {α : Type} [HasTextChange α] : HasTextChange (List α) where
  applyTextChanges tcs xs :=
    if tcs.isEmpty || xs.isEmpty then xs else xs.map (HasTextChange.applyTextChanges tcs)

instance {α β : Type} [HasTextChange α] [HasTextChange β] : HasTextChange (α × β) where
  applyTextChanges tcs pair :=
    if tcs.isEmpty then pair
    else (HasTextChange.applyTextChanges tcs pair.1, HasTextChange.applyTextChanges tcs pair.2)

instance : HasTextChange TypeSetMod where
  applyTextChanges tcs m :=
    if tcs.isEmpty then m
    else
      { m with
        subtypes := HasTextChange.applyTextChanges tcs m.subtypes
        removeSubtypes := HasTextChange.applyTextChanges tcs m.removeSubtypes }

instance : HasTextChange ColorSetMod where
  applyTextChanges tcs m :=
    if tcs.isEmpty then m
    else
      { m with
        colors := HasTextChange.applyTextChanges tcs m.colors
        removeColors := HasTextChange.applyTextChanges tcs m.removeColors }

/-- Apply a sequence of Layer 3 text changes to a `CardSubtype` (CR 612.2 / 613.1c). -/
def TextChange.applySubtype (tcs : Array TextChange) (sub : CardSubtype) : CardSubtype :=
  HasTextChange.applyTextChanges tcs sub

/-- Apply a sequence of Layer 3 text changes to a `Color` word (CR 612.2 / 613.1c). -/
def TextChange.applyColor (tcs : Array TextChange) (c : Color) : Color :=
  HasTextChange.applyTextChanges tcs c

/-- English plural used in Oracle-style reminders (`Orc` → `Orcs`).
Known subtypes use the CR 205.3 spelling, including irregular plurals. -/
def pluralSubtype (s : String) : String :=
  pluralizeName s

#guard pluralSubtype "Orc" == "Orcs"
#guard pluralSubtype "Wolf" == "Wolves"
#guard pluralSubtype "Army" == "Armies"
#guard pluralSubtype "Hero" == "Heroes"
#guard pluralSubtype "Merfolk" == "Merfolk"

/-- Join subtype names for Oracle-style lord reminders (`Orc` and `Goblin`). -/
def joinedSubtypes (subtypes : Array CardSubtype) (each : CardSubtype → String := CardSubtype.englishName) : String :=
  String.intercalate " and " (subtypes.toList.map each)

end Mtg.Engine
