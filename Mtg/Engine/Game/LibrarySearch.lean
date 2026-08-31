import Mtg.Engine.Game.Pumps

/-!
# Searching the library (CR 701.19)

Finding cards in the library, search-to-battlefield and search-to-hand
resolutions, and exiling the top of the library for play.
-/

namespace Mtg.Engine
namespace Game

/-- First library card of `p` whose printed characteristics satisfy `pred`
(bottom of the library first). -/
def findLibraryCard? (g : Game) (p : PlayerId) (pred : CardDef → Bool) : Option ObjectId :=
  (g.player p).library.find? (fun id =>
    match g.findObject? id with
    | some o => pred o.printed
    | none => false)

/-- Search `p`'s library for a card matching `pred`, apply `onFound` or log a
miss, then shuffle (CR 701.19). Picks the first matching card in library
order (bottom first). -/
def resolveLibrarySearch (g : Game) (p : PlayerId) (pred : CardDef → Bool)
    (kind : String) (onFound : Game → ObjectId → Game) (find := true) : Game :=
  let pl := g.player p
  let g :=
    if !find then
      g.logMsg s!"{pl.name} chooses not to find a {kind}"
    else
      match g.findLibraryCard? p pred with
      | none => g.logMsg s!"{pl.name} searches their library and finds no {kind}"
      | some id => onFound g id
  g.shuffleLibrary p

/-- Search `p`'s library for a card matching `pred`, put it onto the battlefield
(tapped if `tapped`), then shuffle (CR 701.19). Picks the first matching card
in library order (bottom first). -/
def resolveSearchLibrary (g : Game) (p : PlayerId) (pred : CardDef → Bool)
    (tapped : Bool) (kind : String) (find := true) : Game :=
  g.resolveLibrarySearch p pred kind (find := find) fun g landId =>
    let landName := (g.object! landId).name
    let (g, newId) := g.putOntoBattlefield landId p (tapped := tapped)
      (summoningSick := false)
    let suffix := if tapped then " tapped" else ""
    let g := g.logMsg
      s!"{(g.player p).name} puts {landName} onto the battlefield{suffix}"
    g.afterLandEnters (g.object! newId)

/-- Search `p`'s library for a basic land card, put it onto the battlefield
tapped, then shuffle (CR 701.19). -/
def resolveSearchBasicLandTapped (g : Game) (p : PlayerId) : Game :=
  g.resolveSearchLibrary p isBasicLandCard true "basic land card"

/-- Search `p`'s library for a Forest card, put it onto the battlefield, then
shuffle (CR 701.19 / 305.7). -/
def resolveSearchForest (g : Game) (p : PlayerId) (find := true) : Game :=
  g.resolveSearchLibrary p isForestCard false "Forest card" (find := find)

/-- Search `p`'s library for a card matching `pred`, reveal it, put it into
their hand, then shuffle. -/
def resolveLibrarySearchToHand (g : Game) (p : PlayerId)
    (pred : CardDef → Bool) (kind : String) : Game :=
  g.resolveLibrarySearch p pred kind fun g cardId =>
    let cardName := (g.object! cardId).name
    let (g, _) := g.move cardId (.hand p) none
    g.logMsg s!"{(g.player p).name} reveals {cardName} and puts it into their hand"

/-- Search `p`'s library for a card with land type `landType`, reveal it, put
it into their hand, then shuffle (CR 701.19 / 702.29). Picks the first matching
card in library order (bottom first). -/
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
