import Mtg.Engine
import Mtg.Engine.Catalog
import Mtg.Engine.Oracle

/-!
# Deck list files

Parse a text deck list whose card names are in `supportedCatalogCards`.
Each non-empty, non-comment line is a card name, optionally preceded by a
copy count (`4 Lightning Bolt` or `4x Lightning Bolt`). Lines that are
exactly `Deck` or `Sideboard` are section headers; sideboard cards are
ignored.
-/

namespace Mtg.Demo

open Mtg.Engine
open Mtg.Engine.Catalog

/-- First supported catalog card whose English name matches, ignoring case. -/
def supportedCard? (name : String) : Option CardDef :=
  let lower := name.map Char.toLower
  match supportedCatalogCards.find? (fun c => c.name == name) with
  | some c => some c
  | none => supportedCatalogCards.find? (fun c => c.name.map Char.toLower == lower)

/-- Leading copy count and the remaining card name, if the line starts with
a number and a separator (`4 Name` or `4x Name`). -/
def parseDeckCountPrefix (s : String) : Option (Nat × String) :=
  let cs := s.toList
  let digits := cs.takeWhile Char.isDigit
  if digits.isEmpty then
    none
  else
    match String.ofList digits |>.toNat? with
    | none => none
    | some n =>
      let rest := cs.drop digits.length
      match rest with
      | [] => none
      | c :: rest' =>
        if c.isWhitespace then
          let name := String.ofList rest' |>.trimAscii.copy
          if name.isEmpty then none else some (n, name)
        else if c == 'x' || c == 'X' then
          match rest' with
          | [] => none
          | d :: rest'' =>
            if d.isWhitespace then
              let name := String.ofList rest'' |>.trimAscii.copy
              if name.isEmpty then none else some (n, name)
            else none
        else none

/-- `none` for blank lines, `#` comments, and `Deck` / `Sideboard` headers. -/
def deckListEntry? (raw : String) : Option (Nat × String) :=
  let line := raw.trimAscii.copy
  if line.isEmpty || line.startsWith "#" then
    none
  else
    let lower := line.map Char.toLower
    if lower == "deck" || lower == "sideboard" then
      none
    else
      match parseDeckCountPrefix line with
      | some p => some p
      | none => some (1, line)

/-- True after a `Sideboard` header until a later `Deck` header. -/
def isSideboardHeader (raw : String) : Bool :=
  raw.trimAscii.copy.map Char.toLower == "sideboard"

def isDeckHeader (raw : String) : Bool :=
  raw.trimAscii.copy.map Char.toLower == "deck"

/-- Expand a deck list into catalog cards. Sideboard lines are omitted. -/
def parseDeckList (lines : Array String) : Except String (Array CardDef) := do
  let mut cards : Array CardDef := #[]
  let mut sideboard := false
  let mut i : Nat := 0
  for raw in lines do
    i := i + 1
    if isSideboardHeader raw then
      sideboard := true
    else if isDeckHeader raw then
      sideboard := false
    else if !sideboard then
      match deckListEntry? raw with
      | none => pure ()
      | some (n, name) =>
        if n == 0 then
          throw s!"line {i}: count must be at least 1"
        match supportedCard? name with
        | none => throw s!"line {i}: unsupported card: {name}"
        | some c => cards := cards ++ copies n c
  if cards.isEmpty then
    throw "Deck list is empty"
  return cards

/-- Read a deck list file and resolve every name against the supported catalog. -/
def loadDeckListFile (path : String) : IO (Except String (Array CardDef)) := do
  try
    let lines ← IO.FS.lines path
    match parseDeckList lines with
    | .ok cards => return .ok cards
    | .error e => return .error s!"Deck list {path}: {e}"
  catch e =>
    return .error s!"Failed to read deck list {path}: {e}"

#guard (supportedCard? "Lightning Bolt").isSome
#guard (supportedCard? "lightning bolt").isSome
#guard (supportedCard? "Mountain").isSome
#guard (supportedCard? "Bofur, Reliable Guardian").isSome
#guard (supportedCard? "Elvish Archdruid").isSome
#guard (supportedCard? "Black Lotus").isNone
#guard (supportedCard? "Treasure").isNone

#guard
  match parseDeckCountPrefix "4 Lightning Bolt" with
  | some (4, "Lightning Bolt") => true
  | _ => false

#guard
  match parseDeckCountPrefix "4x Mountain" with
  | some (4, "Mountain") => true
  | _ => false

#guard
  match parseDeckCountPrefix "16X Forest" with
  | some (16, "Forest") => true
  | _ => false

#guard parseDeckCountPrefix "Lightning Bolt" == none
#guard parseDeckCountPrefix "4" == none
#guard parseDeckCountPrefix "4x" == none

#guard deckListEntry? "" == none
#guard deckListEntry? "  " == none
#guard deckListEntry? "# comment" == none
#guard deckListEntry? "Deck" == none
#guard deckListEntry? "Sideboard" == none
#guard deckListEntry? "Lightning Bolt" == some (1, "Lightning Bolt")
#guard deckListEntry? "2 Shock" == some (2, "Shock")

#guard
  match parseDeckList #["4 Lightning Bolt", "20 Mountain"] with
  | .ok cards =>
    cards.size == 24 &&
    cards[0]!.name == "Lightning Bolt" &&
    cards[4]!.name == "Mountain"
  | .error _ => false

#guard
  match parseDeckList #["# comment", "", "Shock"] with
  | .ok cards => cards.size == 1 && cards[0]!.name == "Shock"
  | _ => false

#guard
  match parseDeckList #["1x Giant Growth"] with
  | .ok cards => cards.size == 1 && cards[0]!.name == "Giant Growth"
  | _ => false

#guard
  match parseDeckList #["black lotus"] with
  | .error msg => msg == "line 1: unsupported card: black lotus"
  | _ => false

#guard
  match parseDeckList #["# only comments"] with
  | .error msg => msg == "Deck list is empty"
  | _ => false

#guard
  match parseDeckList #["0 Mountain"] with
  | .error msg => msg == "line 1: count must be at least 1"
  | _ => false

#guard
  match parseDeckList #["Deck", "2 Lightning Bolt", "Sideboard", "1 Shock"] with
  | .ok cards =>
    cards.size == 2 && cards.all (fun c => c.name == "Lightning Bolt")
  | _ => false

#guard
  match parseDeckList #["40 Forest"] with
  | .ok cards => cards.size == 40 && cards.all (fun c => c.name == "Forest")
  | _ => false

end Mtg.Demo
