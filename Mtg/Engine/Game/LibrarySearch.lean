import Mtg.Engine.Game.Pumps

/-!
# Searching the library (CR 701.19)

Finding cards in the library, search-to-battlefield and search-to-hand
resolutions, and exiling the top of the library for play. The player chooses
which cards to find (CR 701.19b).
-/

namespace Mtg.Engine
namespace Game

/-- Drop a leading "a " so logs read "finds no Forest card". -/
def searchNoun (kind : String) : String :=
  match kind.dropPrefix? "a " with
  | some rest => rest.toString
  | none => kind

/-- What still happens after the library is shuffled. -/
def searchAfter (p : PlayerId) : Option FraNext → AfterRandom
  | some (.gainLife n) => .gainLife p n
  | _ => .none

/-- True when failing to find still shuffles. Searching only the hand does not
(Last Light of Durin's Day). -/
def shufflesWhenNoneFound : SearchDest → Bool
  | .battlefieldFromHandOrLibrary => false
  | _ => true

/-- First library card of `p` whose printed characteristics satisfy `pred`
(bottom of the library first). -/
def findLibraryCard? (g : Game) (p : PlayerId) (pred : CardDef → Bool) : Option ObjectId :=
  (g.player p).library.find? (fun id =>
    match g.findObject? id with
    | some o => pred o.printed
    | none => false)

/-- Put `id` onto the battlefield under `p`. Lands can tap immediately. -/
def placeSearched (g : Game) (p : PlayerId) (id : ObjectId) (tapped : Bool) :
    Game × Option ObjectId :=
  match g.findObject? id with
  | none => (g, none)
  | some o =>
    let name := o.name
    let sick := !o.printed.isLand
    let (g, newId) := g.putOntoBattlefield id p (tapped := tapped) (summoningSick := sick)
    let phrase := if tapped then " onto the battlefield tapped" else " onto the battlefield"
    let g := g.logMsg s!"{(g.player p).name} puts {name}{phrase}"
    let entered := g.object! newId
    let g :=
      if entered.printed.isLand then g.afterLandEnters entered
      else g.afterPermanentEnters entered
    (g, some newId)

/-- Reveal `id` and put it into `p`'s hand. -/
def placeSearchedHand (g : Game) (p : PlayerId) (id : ObjectId) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    let name := o.name
    let (g, _) := g.move id (.hand p) none
    g.logMsg s!"{(g.player p).name} reveals {name} and puts it into their hand"

/-- Put `id` into its owner's graveyard. -/
def placeSearchedGraveyard (g : Game) (id : ObjectId) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    let name := o.name
    let (g, _) := g.move id (.graveyard o.owner) none
    g.logMsg s!"{name} is put into {(g.player o.owner).name}'s graveyard"

/-- Exile `id` and link the exiled card to `source`. -/
def exileSearchedLinked (g : Game) (p : PlayerId) (id : ObjectId)
    (source : Option ObjectId) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    let name := o.name
    let (g, newId) := g.move id .exile none
    let g :=
      match source.bind g.findObject? with
      | some src =>
        g.setObject { src with linkedExile := src.linkedExile.push newId }
      | none => g
    g.logMsg s!"{(g.player p).name} exiles {name}"

/-- Behold `subtype`. If you do, untap the land this search just found. -/
def beholdAndMaybeUntap (g : Game) (p : PlayerId) (landId : ObjectId) (subtype : String) : Game :=
  let g := g.beholdQuality p subtype
  if !g.qualityWasBeheld p subtype then g
  else
    match g.findObject? landId with
    | some o =>
      if o.isOnBattlefield && o.status.tapped && o.status.stun == 0 &&
          !g.hostCantBecomeUntapped o then
        let g := g.setObject { o with status := { o.status with tapped := false } }
        g.logMsg s!"{o.name} untaps"
      else g
    | none => g

/-- Run a search's post-shuffle action when the shuffle did not pause. -/
def applySearchAfter (g : Game) : Game :=
  let after := g.afterRandom
  let g := { g with afterRandom := .none }
  match after with
  | .putOnTop p ids => g.putIdsOnTop p ids
  | .beholdUntap p landId subtype => g.beholdAndMaybeUntap p landId subtype
  | other => { g with afterRandom := other }

/-- Shuffle, then run `onDone`. A `--norandom` pause keeps `onDone` until the
host supplies the order. An as-enters choice already waiting is restored when
the shuffle does not pause. -/
def shuffleThen (g : Game) (p : PlayerId) (onDone : AfterRandom) : Game :=
  let saved := g.pending
  let g := { g with pending := .none }
  let g := g.requestShuffle p onDone
  if g.pendingRandom?.isSome then g
  else
    let g := g.continueIfShuffled
    let g := g.applySearchAfter
    if g.pending == .none then { g with pending := saved } else g

/-- Send the chosen cards to `dest`, shuffle, then do `after`. An empty `ids`
is "chooses not to find" (CR 701.19b). -/
def finishLibrarySearch (g : Game) (p : PlayerId) (ids : Array ObjectId)
    (dest : SearchDest) (after : Option FraNext) (kind : String) : Game :=
  let noun := searchNoun kind
  if ids.isEmpty then
    let g := g.logMsg s!"{(g.player p).name} chooses not to find a {noun}"
    if shufflesWhenNoneFound dest then g.shuffleThen p (searchAfter p after) else g
  else
    match dest with
    | .battlefield tapped =>
      let g := ids.foldl (fun g id => (g.placeSearched p id tapped).1) g
      g.shuffleThen p (searchAfter p after)
    | .hand =>
      let g := ids.foldl (fun g id => g.placeSearchedHand p id) g
      g.shuffleThen p (searchAfter p after)
    | .graveyard =>
      let g := ids.foldl (fun g id => g.placeSearchedGraveyard id) g
      g.shuffleThen p (searchAfter p after)
    | .topAfterShuffle =>
      let g := ids.foldl (fun g id =>
        match g.findObject? id with
        | some o => g.logMsg s!"{(g.player p).name} reveals {o.name}"
        | none => g) g
      g.shuffleThen p (.putOnTop p ids)
    | .exileLinked source =>
      let g := ids.foldl (fun g id => g.exileSearchedLinked p id source) g
      g.shuffleThen p (searchAfter p after)
    | .battlefieldTappedThenHand =>
      let g :=
        match ids[0]? with
        | some id => (g.placeSearched p id true).1
        | none => g
      let g := (ids.extract 1 ids.size).foldl (fun g id => g.placeSearchedHand p id) g
      g.shuffleThen p (searchAfter p after)
    | .battlefieldTappedBeholdUntap subtype =>
      match ids[0]? with
      | none => g.shuffleThen p (searchAfter p after)
      | some id =>
        let (g, newId) := g.placeSearched p id true
        match newId with
        | some landId => g.shuffleThen p (.beholdUntap p landId subtype)
        | none => g.shuffleThen p (searchAfter p after)
    | .battlefieldFromHandOrLibrary =>
      let fromLibrary := ids.any (fun id =>
        (g.findObject? id).any (·.zone == .library p))
      let g := ids.foldl (fun g id => (g.placeSearched p id false).1) g
      if fromLibrary then g.shuffleThen p (searchAfter p after) else g

/-- Search `p`'s library for up to `count` cards matching `pred` (CR 701.19).
The player chooses which, or none (CR 701.19b). `optional` may skip the
search entirely, and then the library is not shuffled. -/
def beginLibrarySearch (g : Game) (p : PlayerId) (pred : CardDef → Bool) (kind : String)
    (dest : SearchDest) (count : Nat := 1) (after : Option FraNext := none)
    (alsoHand : Bool := false) (optional : Bool := false) : Game :=
  let keep (id : ObjectId) := (g.findObject? id).any (pred ·.printed)
  let pl := g.player p
  let eligible := (if alsoHand then pl.hand.filter keep else #[]) ++ pl.library.filter keep
  if optional then
    { g with pending := .fraChoice p (.maySearchLibrary eligible count dest after kind) }.logMsg
      s!"{pl.name} may search for {kind}"
  else if eligible.isEmpty then
    (g.logMsg s!"{pl.name} finds no {searchNoun kind}").shuffleThen p (searchAfter p after)
  else
    { g with pending := .fraChoice p (.searchLibrary eligible count dest after kind) }.logMsg
      s!"{pl.name} searches for {kind}"

/-- Search `p`'s library for a card matching `pred` and put it onto the
battlefield (tapped if `tapped`), then shuffle (CR 701.19). -/
def resolveSearchLibrary (g : Game) (p : PlayerId) (pred : CardDef → Bool)
    (tapped : Bool) (kind : String) : Game :=
  g.beginLibrarySearch p pred kind (.battlefield tapped)

/-- Search `p`'s library for a basic land card, put it onto the battlefield
tapped, then shuffle (CR 701.19). -/
def resolveSearchBasicLandTapped (g : Game) (p : PlayerId) : Game :=
  g.resolveSearchLibrary p isBasicLandCard true "a basic land card"

/-- Search `p`'s library for a Forest card, put it onto the battlefield, then
shuffle (CR 701.19 / 305.7). -/
def resolveSearchForest (g : Game) (p : PlayerId) : Game :=
  g.resolveSearchLibrary p isForestCard false "a Forest card"

/-- Search `p`'s library for a card matching `pred`, reveal it, put it into
their hand, then shuffle. -/
def resolveLibrarySearchToHand (g : Game) (p : PlayerId)
    (pred : CardDef → Bool) (kind : String) : Game :=
  g.beginLibrarySearch p pred kind .hand

/-- Search `p`'s library for a card with land type `landType`, reveal it, put
it into their hand, then shuffle (CR 701.19 / 702.29). -/
def resolveSearchLandTypeToHand (g : Game) (p : PlayerId) (landType : String) : Game :=
  g.resolveLibrarySearchToHand p (fun c => c.hasSubtype landType) s!"{landType} card"

/-- Search `p`'s library for a basic land, put it into their hand, then shuffle. -/
def resolveSearchBasicLandToHand (g : Game) (p : PlayerId) : Game :=
  g.resolveLibrarySearchToHand p isBasicLandCard "basic land card"

/-- Exile the top card of `p`'s library and grant permission to play it until
the end of that player's next turn (CR 701.14). -/
def resolveExileTopPlayUntilEndOfNextTurn (g : Game) (p : PlayerId) : Game :=
  let pl := g.player p
  if pl.library.isEmpty then
    g.logMsg s!"{pl.name} has no cards in their library to exile"
  else
    let top := pl.library.back!
    let cardName := (g.object! top).name
    let (g, newId) := g.move top .exile none
    let o := g.object! newId
    let g := g.setObject { o with
      playPermission := some { player := p, turnEndsRemaining := 2 } }
    g.logMsg
      s!"{pl.name} exiles {cardName} and may play it until the end of their next turn"

end Game
end Mtg.Engine
