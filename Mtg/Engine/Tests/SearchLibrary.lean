import Mtg.Engine.Fixture

/-!
# `TriggerResolution.searchLibrary`

A Forest onto the battlefield, a basic land into hand, a basic land you
may put on top, and a Dragon from hand or library are `searchLibrary`.
What happens to the found card is a `TriggerResolution`. Printed pairs
keep their phrases. Another library find searches that way. Any other
follow-up is resolved itself, and those follow-ups do nothing on their
own.
-/

namespace Mtg.Engine.SearchLibraryTests

open Mtg.Engine
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def forest : CardDef := {
  name := "Search Forest"
  types := #[.land]
  supertypes := #[.basic]
  subtypes := #["Forest"]
}

def mountain : CardDef := {
  name := "Search Mountain"
  types := #[.land]
  supertypes := #[.basic]
  subtypes := #["Mountain"]
}

def canopy : CardDef := {
  name := "Search Canopy"
  types := #[.land]
  subtypes := #["Forest", "Island"]
}

def dragon : CardDef := {
  name := "Search Dragon"
  types := #[.creature]
  subtypes := #["Dragon"]
  power := some 4
  toughness := some 4
}

def handDragon : CardDef := {
  name := "Hand Dragon"
  types := #[.creature]
  subtypes := #["Dragon"]
  power := some 3
  toughness := some 3
}

def drake : CardDef := {
  name := "Search Drake"
  types := #[.creature]
  subtypes := #["Drake"]
  power := some 2
  toughness := some 2
}

def light : CardDef := {
  name := "Search Light"
  types := #[.enchantment]
}

def putInHand (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.hand p) none {} (fun id _ =>
    #[.pushHand id])

def putOnLibrary (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.library p) none {} (fun id _ =>
    #[.pushLibrary id])

/-- Replace `p`'s library. The last card is on top. -/
def onlyLibrary (g : Game) (p : PlayerId) (cards : List CardDef) : Game :=
  cards.foldl (fun g c => putOnLibrary g c p)
    (g.changePlayer p (.library #[]))

def emptyHand (g : Game) (p : PlayerId) : Game :=
  g.changePlayer p (.hand #[])

def inHand (g : Game) (p : PlayerId) (name : String) : Bool :=
  (g.player p).hand.any (fun id => (g.findObject? id).any (·.name == name))

def inLibrary (g : Game) (p : PlayerId) (name : String) : Bool :=
  (g.player p).library.any (fun id => (g.findObject? id).any (·.name == name))

def inGraveyard (g : Game) (p : PlayerId) (name : String) : Bool :=
  (g.player p).graveyard.any (fun id => (g.findObject? id).any (·.name == name))

def onBattlefield (g : Game) (name : String) : Bool :=
  g.battlefield.any (·.name == name)

def permanent (g : Game) (name : String) : GameObject :=
  match g.battlefield.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing {name}"

def shuffledSince (before : Nat) (g : Game) : Bool :=
  (g.log.extract before g.log.size).any (fun s => mentions s "shuffles their library")

def step (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none) : Game :=
  g.applyTriggeredAbility caster (.onEnterDraw 1) sourceId #[]
    (resolutionOverride := some r)

/-- Answer an optional search, then take the first eligible card. -/
def takeSearch (g : Game) : Game :=
  match g.pending, g.actor with
  | .fraChoice _ (.maySearchLibrary eligible ..), some p =>
    if eligible.isEmpty then mustApply g p .decline
    else
      let g := mustApply g p .accept
      match g.pending, g.actor with
      | .fraChoice _ (.searchLibrary ids n ..), some q =>
        if ids.isEmpty then mustApply g q .decline
        else mustApply g q (.choosePermanents (ids.extract 0 n))
      | _, _ => g
  | .fraChoice _ (.searchLibrary eligible count ..), some p =>
    if eligible.isEmpty then mustApply g p .decline
    else mustApply g p (.choosePermanents (eligible.extract 0 count))
  | _, _ => g

def declineSearch (g : Game) : Game :=
  match g.pending, g.actor with
  | .fraChoice _ _, some p => mustApply g p .decline
  | _, _ => g

def withQuest (n : Nat) : Game :=
  let g := addPermanent afterDraw light caster caster
  let o := lastPermanent g
  g.changeStatus o.id (.quest n)

#guard isForestCard forest && isBasicLandCard forest
#guard isBasicLandCard mountain && !isForestCard mountain
#guard isForestCard canopy && !isBasicLandCard canopy
#guard dragon.subtypes.contains "Dragon" && !drake.subtypes.contains "Dragon"

/- A Forest enters untapped, without summoning sickness, and without
spending a land play. A Mountain stays in the library. The library is
shuffled. An empty library finds nothing and still shuffles. -/
#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [mountain, forest]
  let played := g0.loggedLandsPlayed caster
  let before := g0.log.size
  let g := takeSearch (step g0 (.searchLibrary (.put .forest)))
  onBattlefield g "Search Forest" && !onBattlefield g "Search Mountain" &&
    inLibrary g caster "Search Mountain" && !inLibrary g caster "Search Forest" &&
    !(permanent g "Search Forest").status.tapped &&
    !(permanent g "Search Forest").status.summoningSick &&
    g.loggedLandsPlayed caster == played &&
    shuffledSince before g &&
    logContains g "searches for a Forest card" &&
    logContains g "puts Search Forest onto the battlefield" &&
    !logContains g "onto the battlefield tapped"

#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [canopy]
  let g := takeSearch (step g0 (.searchLibrary (.put .forest)))
  onBattlefield g "Search Canopy" &&
    !(permanent g "Search Canopy").status.tapped &&
    logContains g "puts Search Canopy onto the battlefield"

#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [mountain]
  let before := g0.log.size
  let g := step g0 (.searchLibrary (.put .forest))
  g.pending == .none && !onBattlefield g "Search Mountain" &&
    inLibrary g caster "Search Mountain" && shuffledSince before g &&
    logContains g "finds no Forest card"

/- Failing to find still shuffles. The Forest stays in the library. -/
#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [forest]
  let before := g0.log.size
  let g := declineSearch (step g0 (.searchLibrary (.put .forest)))
  !onBattlefield g "Search Forest" && inLibrary g caster "Search Forest" &&
    shuffledSince before g &&
    logContains g "chooses not to find a Forest card"

/- A basic land is revealed and put into hand. A nonbasic Forest is not
a basic land, so that search finds nothing and shuffles. -/
#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [forest, mountain]
  let before := g0.log.size
  let g := takeSearch (step g0 (.searchLibrary (.returnToHand .basicLand)))
  inHand g caster "Search Forest" && !onBattlefield g "Search Forest" &&
    inLibrary g caster "Search Mountain" && shuffledSince before g &&
    logContains g "searches for basic land card" &&
    logContains g "reveals Search Forest and puts it into their hand"

#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [canopy]
  let before := g0.log.size
  let g := step g0 (.searchLibrary (.returnToHand .basicLand))
  g.pending == .none && inLibrary g caster "Search Canopy" &&
    !inHand g caster "Search Canopy" && shuffledSince before g &&
    logContains g "finds no basic land card"

/- You may put a basic land on top. Declining does not shuffle. Accepting
an empty library finds nothing and does shuffle. -/
#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [forest, mountain]
  let found := (g0.player caster).library[0]!
  let before := g0.log.size
  let g := takeSearch (step g0 (.searchLibrary (.put .basicLandOnTop)))
  (g.player caster).library.back? == some found &&
    inLibrary g caster "Search Mountain" && inLibrary g caster "Search Forest" &&
    !onBattlefield g "Search Forest" && shuffledSince before g &&
    logContains g "may search for a basic land card" &&
    logContains g "reveals Search Forest" &&
    logContains g "on top of their library"

#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [forest, mountain]
  let lib := (g0.player caster).library
  let before := g0.log.size
  let g := declineSearch (step g0 (.searchLibrary (.put .basicLandOnTop)))
  (g.player caster).library == lib && !shuffledSince before g &&
    logContains g "doesn't search their library"

#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster []
  let before := g0.log.size
  let offered := step g0 (.searchLibrary (.put .basicLandOnTop))
  let g := mustApply offered caster .accept
  g.pending == .none && shuffledSince before g &&
    logContains g "finds no basic land card"

/- A Dragon from hand enters and the library is not shuffled. A Dragon
from the library does shuffle. A Drake, and a Dragon another player has,
are not found. Choosing not to find does not shuffle. An empty hand and
library still shuffles, as an empty search does. -/
#guard
  let g0 := putInHand (onlyLibrary (emptyHand afterDraw caster) caster [drake]) dragon caster
  let before := g0.log.size
  let g := takeSearch (step g0 (.searchLibrary (.put .dragon)))
  onBattlefield g "Search Dragon" && !inHand g caster "Search Dragon" &&
    inLibrary g caster "Search Drake" && !onBattlefield g "Search Drake" &&
    (permanent g "Search Dragon").status.summoningSick &&
    !(permanent g "Search Dragon").status.tapped &&
    !shuffledSince before g &&
    logContains g "searches for a Dragon card" &&
    logContains g "puts Search Dragon onto the battlefield"

#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [drake, dragon]
  let before := g0.log.size
  let g := takeSearch (step g0 (.searchLibrary (.put .dragon)))
  onBattlefield g "Search Dragon" && inLibrary g caster "Search Drake" &&
    shuffledSince before g &&
    logContains g "puts Search Dragon onto the battlefield"

#guard
  let g0 := putInHand (onlyLibrary (emptyHand afterDraw caster) caster [dragon])
    handDragon caster
  let libId := (g0.player caster).library.back!
  let before := g0.log.size
  let offered := step g0 (.searchLibrary (.put .dragon))
  let fromHand := takeSearch offered
  let fromLib := mustApply offered caster (.choosePermanents #[libId])
  onBattlefield fromHand "Hand Dragon" && inLibrary fromHand caster "Search Dragon" &&
    !shuffledSince before fromHand &&
    onBattlefield fromLib "Search Dragon" && inHand fromLib caster "Hand Dragon" &&
    shuffledSince before fromLib

#guard
  let g0 := putInHand (onlyLibrary (emptyHand afterDraw caster) caster []) dragon opp
  let g0 := onlyLibrary g0 opp [dragon]
  let before := g0.log.size
  let g := step g0 (.searchLibrary (.put .dragon))
  g.pending == .none && !onBattlefield g "Search Dragon" &&
    inHand g opp "Search Dragon" && inLibrary g opp "Search Dragon" &&
    shuffledSince before g && logContains g "finds no Dragon card"

#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [dragon]
  let before := g0.log.size
  let g := declineSearch (step g0 (.searchLibrary (.put .dragon)))
  !onBattlefield g "Search Dragon" && inLibrary g caster "Search Dragon" &&
    !shuffledSince before g &&
    logContains g "chooses not to find a Dragon card"

/- Six quest counters sacrifice the source and search. Fewer than six
do not. A missing source does not search. -/
#guard
  let g0 := onlyLibrary (emptyHand (withQuest 5) caster) caster [dragon]
  let src := lastPermanent g0
  let before := g0.log.size
  let g := takeSearch (g0.applyTriggeredAbility caster .onMountainEntersQuestThenDragon
    (some src.id))
  !onBattlefield g "Search Light" && inGraveyard g caster "Search Light" &&
    onBattlefield g "Search Dragon" && shuffledSince before g &&
    logContains g "gets a quest counter (6)" &&
    logContains g "Search Light is sacrificed"

#guard
  let g0 := onlyLibrary (emptyHand (withQuest 4) caster) caster [dragon]
  let src := lastPermanent g0
  let before := g0.log.size
  let g := g0.applyTriggeredAbility caster .onMountainEntersQuestThenDragon (some src.id)
  onBattlefield g "Search Light" && (permanent g "Search Light").status.quest == 5 &&
    inLibrary g caster "Search Dragon" && !shuffledSince before g &&
    g.pending == .none && logContains g "gets a quest counter (5)"

#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [dragon]
  let before := g0.log.size
  let g := step g0 (TriggeredAbility.resolution .onMountainEntersQuestThenDragon)
  !onBattlefield g "Search Dragon" && inLibrary g caster "Search Dragon" &&
    !shuffledSince before g &&
    logContains g "The triggered ability's source is no longer in play"

/- A library find that is not the printed pair still searches.
A follow-up that is not a find is resolved itself. -/
#guard
  let g0 := putInHand (onlyLibrary (emptyHand afterDraw caster) caster
    [forest, mountain, dragon]) handDragon caster
  let g := takeSearch (step g0 (.searchLibrary (.put .forest .tapped)))
  onBattlefield g "Search Forest" && (permanent g "Search Forest").status.tapped &&
    inLibrary g caster "Search Mountain" && !onBattlefield g "Search Mountain"

#guard
  let g0 := putInHand (onlyLibrary (emptyHand afterDraw caster) caster
    [forest, mountain, dragon]) handDragon caster
  let g := takeSearch (step g0 (.searchLibrary (.put .dragon .tapped)))
  let handOn := onBattlefield g "Hand Dragon"
  let libOn := onBattlefield g "Search Dragon"
  (handOn || libOn) && !(handOn && libOn) &&
    (if handOn then (permanent g "Hand Dragon").status.tapped
     else (permanent g "Search Dragon").status.tapped)

#guard
  let g0 := putInHand (onlyLibrary (emptyHand afterDraw caster) caster
    [forest, mountain, dragon]) handDragon caster
  let g := takeSearch (step g0 (.searchLibrary (.put .basicLandOnTop .tapped)))
  let forestOn := onBattlefield g "Search Forest"
  let mountainOn := onBattlefield g "Search Mountain"
  (forestOn || mountainOn) && !(forestOn && mountainOn) &&
    (if forestOn then (permanent g "Search Forest").status.tapped
     else (permanent g "Search Mountain").status.tapped) &&
    !onBattlefield g "Search Dragon"

#guard
  let g0 := putInHand (onlyLibrary (emptyHand afterDraw caster) caster
    [forest, mountain, dragon]) handDragon caster
  let g := takeSearch (step g0
    (.searchLibrary (.returnToHand .basicLand .returnedPermanent)))
  (inHand g caster "Search Forest" || inHand g caster "Search Mountain") &&
    !onBattlefield g "Search Forest" && !onBattlefield g "Search Mountain" &&
    !g.returnedPermanentThisWay

#guard
  let g0 := putInHand (onlyLibrary (emptyHand afterDraw caster) caster
    [forest, mountain, dragon]) handDragon caster
  let g := step g0 (.searchLibrary (.draw (.fixed 1)))
  inHand g caster "Search Dragon" && !inLibrary g caster "Search Dragon" &&
    inLibrary g caster "Search Forest"

#guard
  let g0 := putInHand (onlyLibrary (emptyHand afterDraw caster) caster
    [forest, mountain, dragon]) handDragon caster
  let g := step g0 (.searchLibrary (.returnToHand .graveyardCard))
  (g.player caster).library == (g0.player caster).library &&
    (g.player caster).hand == (g0.player caster).hand &&
    logContains g "no longer legal"

#guard
  let g0 := putInHand (onlyLibrary (emptyHand afterDraw caster) caster
    [forest, mountain, dragon]) handDragon caster
  let quiet := [
    .searchLibrary (.put .linkedExile),
    .searchLibrary (.may (.put .basicLandOnTop) (.sequence []))]
  quiet.all fun r =>
    let g := step g0 r
    (g.player caster).library == (g0.player caster).library &&
      (g.player caster).hand == (g0.player caster).hand &&
      g.battlefield.size == g0.battlefield.size &&
      g.pending == .none && g.log.size == g0.log.size

/- The follow-up resolutions do nothing on their own. `searchLibrary` is
what searches. -/
#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [forest, mountain, dragon]
  let alone := [
    .put .forest,
    .put .basicLandOnTop,
    .put .dragon,
    .returnToHand .basicLand]
  alone.all fun r =>
    let g := step g0 r
    (g.player caster).library == (g0.player caster).library &&
      !onBattlefield g "Search Forest" && !onBattlefield g "Search Dragon" &&
      g.pending == .none && g.log.size == g0.log.size

/- Printed phrases and resolutions stay with the combination that produces them. -/
#guard TriggeredAbility.resolution .onEnterSearchForest ==
  .searchLibrary (.put .forest)
#guard TriggeredAbility.resolution .onEnterSearchBasicToHand ==
  .searchLibrary (.returnToHand .basicLand)
#guard TriggeredAbility.resolution (.onEnterGainLifeSearchBasicOnTop 2) ==
  .sequence [.gainLife (.fixed 2), .searchLibrary (.put .basicLandOnTop)]
#guard TriggeredAbility.resolution .onMountainEntersQuestThenDragon ==
  .sequence [
    .putCounters (.ofKind .quest) .source,
    .«if» ((.atLeast (.count .questCounters) (.fixed 6)))
      (.sequence [
        .sacrifice (.sacrificedSource .movedAsSacrificed),
        .searchLibrary (.put .dragon)])]
#guard (SharedTrigger.timing .searchLibrary).resolution ==
  .searchLibrary (.put .forest)
#guard (SharedTrigger.timing .searchBasicLandToHand).resolution ==
  .searchLibrary (.returnToHand .basicLand)
#guard TriggeredAbility.resolutionPhrase
    { resolution := .searchLibrary (.put .forest) } ==
  "search your library for a Forest card, put that card onto the battlefield, then shuffle"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .searchLibrary (.returnToHand .basicLand) } ==
  "search your library for a basic land card, reveal it, put it into your hand, then shuffle"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .searchLibrary (.put .basicLandOnTop) } ==
  "you may search your library for a basic land card, reveal it, then shuffle and put that card on top"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .searchLibrary (.put .dragon) } ==
  "search your hand and/or library for a Dragon card and put it onto the battlefield"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .searchLibrary (.draw (.fixed 1)) } ==
  "search your library"
#guard TriggeredAbility.resolutionPhrase { resolution := .put .basicLandOnTop } ==
  "put that card on top of your library"
#guard TriggeredAbility.resolutionPhrase { resolution := .returnToHand .basicLand } ==
  "put it into your hand"
#guard TriggeredAbility.toNotation .onEnterSearchForest ==
  "When this permanent enters, search your library for a Forest card, put that card onto the battlefield, then shuffle."
#guard TriggeredAbility.toNotation .onEnterSearchBasicToHand ==
  "When this permanent enters, search your library for a basic land card, reveal it, put it into your hand, then shuffle."
#guard TriggeredAbility.toNotation (.onEnterGainLifeSearchBasicOnTop 2) ==
  "When this permanent enters, you gain 2 life. You may search your library for a basic land card, reveal it, then shuffle and put that card on top."
#guard TriggeredAbility.toNotation .onMountainEntersQuestThenDragon ==
  "Whenever a Mountain you control enters, put a quest counter on this enchantment. If it has six or more quest counters on it, sacrifice it. If you do, search your hand and/or library for a Dragon card and put it onto the battlefield. If you search your library this way, shuffle."

end Mtg.Engine.SearchLibraryTests
