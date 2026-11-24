import Mtg.Engine.Tests.Builders
import Mtg.Engine.Fixture

/-!
# Unified library-search instructions (`PlayerOp.searchLibrary`)

A Forest onto the battlefield, a basic land into hand, a basic land you
may put on top, and a Dragon from hand or library all execute via
`PlayerOp.searchLibrary` in `Game/Interpreter.lean`. Printed phrases stay
intact and changeling cards match creature subtypes in hand and library
(CR 702.73a).
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
  power := some (.fixed 4)
  toughness := some (.fixed 4)
}

def handDragon : CardDef := {
  name := "Hand Dragon"
  types := #[.creature]
  subtypes := #["Dragon"]
  power := some (.fixed 3)
  toughness := some (.fixed 3)
}

def drake : CardDef := {
  name := "Search Drake"
  types := #[.creature]
  subtypes := #["Drake"]
  power := some (.fixed 2)
  toughness := some (.fixed 2)
}

def light : CardDef := {
  name := "Search Light"
  types := #[.enchantment]
}

def putInHand (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.hand p)

def putOnLibrary (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.library p)

/-- Replace `p`'s library. The last card is on top. -/
def onlyLibrary (g : Game) (p : PlayerId) (cards : List CardDef) : Game :=
  cards.foldl (fun g c => putOnLibrary g c p)
    (emptyLibrary g p)

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

def searchForestTapped : Effect :=
  { body := .player (.searchLibrary {
      zones := .libraryOf .you
      filter := .hasSubtype (.literal .forest)
      count := .upTo (.const 1)
      dest := .battlefield .controller
      mods := { tapped := true }
      reveal := false
      shuffle := true
    }) }

def searchBasicOnTop : Effect :=
  { body := .player (.searchLibrary {
      zones := .libraryOf .you
      filter := .all #[.hasSupertype .basic, .hasType .land]
      count := .upTo (.const 1)
      dest := .library .owner .top
      reveal := true
      shuffle := true
    }) }

def searchDragon (tapped : Bool := false) : Effect :=
  { body := .player (.searchLibrary {
      zones := { zones := #[.hand, .library], owner := .ofPlayer .you }
      filter := .hasSubtype (.literal .dragon)
      count := .upTo (.const 1)
      dest := .battlefield .controller
      mods := { tapped }
      reveal := false
      shuffle := true
    }) }

def stepEffect (g : Game) (e : Effect) (sourceId : Option ObjectId := none) : Game :=
  g.applyTriggeredAbility caster (TriggeredAbility.mkTrigger .thisEnters e) sourceId #[]

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
  g.recordPutCounters o.id .quest n

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
  let g := takeSearch (stepEffect g0 Effect.triggerSearchForest)
  onBattlefield g "Search Forest" && !onBattlefield g "Search Mountain" &&
    inLibrary g caster "Search Mountain" && !inLibrary g caster "Search Forest" &&
    !(permanent g "Search Forest").status.tapped &&
    !g.hasSummoningSickness (permanent g "Search Forest") &&
    g.loggedLandsPlayed caster == played &&
    shuffledSince before g &&
    logContains g "puts Search Forest onto the battlefield" &&
    !logContains g "onto the battlefield tapped"

#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [canopy]
  let g := takeSearch (stepEffect g0 Effect.triggerSearchForest)
  onBattlefield g "Search Canopy" &&
    !(permanent g "Search Canopy").status.tapped &&
    logContains g "puts Search Canopy onto the battlefield"

#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [mountain]
  let before := g0.log.size
  let g := stepEffect g0 Effect.triggerSearchForest
  g.pending == .none && !onBattlefield g "Search Mountain" &&
    inLibrary g caster "Search Mountain" && shuffledSince before g

/- Failing to find still shuffles. The Forest stays in the library. -/
#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [forest]
  let before := g0.log.size
  let g := declineSearch (stepEffect g0 Effect.triggerSearchForest)
  !onBattlefield g "Search Forest" && inLibrary g caster "Search Forest" &&
    shuffledSince before g

/- A basic land is revealed and put into hand. A nonbasic Forest is not
a basic land, so that search finds nothing and shuffles. -/
#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [forest, mountain]
  let before := g0.log.size
  let g := takeSearch (stepEffect g0 Effect.triggerSearchBasicLandToHand)
  inHand g caster "Search Forest" && !onBattlefield g "Search Forest" &&
    inLibrary g caster "Search Mountain" && shuffledSince before g &&
    logContains g "reveals Search Forest and puts it into their hand"

#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [canopy]
  let before := g0.log.size
  let g := stepEffect g0 Effect.triggerSearchBasicLandToHand
  g.pending == .none && inLibrary g caster "Search Canopy" &&
    !inHand g caster "Search Canopy" && shuffledSince before g

/- You may put a basic land on top. Declining does not shuffle. Accepting
an empty library finds nothing and does shuffle. -/
#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [forest, mountain]
  let found := (g0.player caster).library[0]!
  let before := g0.log.size
  let g := takeSearch (stepEffect g0 searchBasicOnTop)
  (g.player caster).library.back? == some found &&
    inLibrary g caster "Search Mountain" && inLibrary g caster "Search Forest" &&
    !onBattlefield g "Search Forest" && shuffledSince before g &&
    logContains g "reveals Search Forest" &&
    logContains g "on top of their library"

#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [forest, mountain]
  let lib := (g0.player caster).library
  let before := g0.log.size
  let g := declineSearch (stepEffect g0 searchBasicOnTop)
  (g.player caster).library == lib && !shuffledSince before g &&
    logContains g "doesn't search their library"

#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster []
  let before := g0.log.size
  let offered := stepEffect g0 searchBasicOnTop
  let g := mustApply offered caster .accept
  g.pending == .none && shuffledSince before g

/- A Dragon from hand enters and the library is not shuffled. A Dragon
from the library does shuffle. A Drake, and a Dragon another player has,
are not found. Choosing not to find still shuffles. An empty hand and
library still shuffles. -/
#guard
  let g0 := putInHand (onlyLibrary (emptyHand afterDraw caster) caster [drake]) dragon caster
  let before := g0.log.size
  let g := takeSearch (stepEffect g0 (searchDragon))
  onBattlefield g "Search Dragon" && !inHand g caster "Search Dragon" &&
    inLibrary g caster "Search Drake" && !onBattlefield g "Search Drake" &&
    (permanent g "Search Dragon").status.summoningSick &&
    !(permanent g "Search Dragon").status.tapped &&
    !shuffledSince before g &&
    logContains g "puts Search Dragon onto the battlefield"

#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [drake, dragon]
  let before := g0.log.size
  let g := takeSearch (stepEffect g0 (searchDragon))
  onBattlefield g "Search Dragon" && inLibrary g caster "Search Drake" &&
    shuffledSince before g &&
    logContains g "puts Search Dragon onto the battlefield"

#guard
  let g0 := putInHand (onlyLibrary (emptyHand afterDraw caster) caster [dragon])
    handDragon caster
  let libId := (g0.player caster).library.back!
  let before := g0.log.size
  let offered := stepEffect g0 (searchDragon)
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
  let g := stepEffect g0 (searchDragon)
  g.pending == .none && !onBattlefield g "Search Dragon" &&
    inHand g opp "Search Dragon" && inLibrary g opp "Search Dragon" &&
    shuffledSince before g

#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [dragon]
  let before := g0.log.size
  let g := declineSearch (stepEffect g0 (searchDragon))
  !onBattlefield g "Search Dragon" && inLibrary g caster "Search Dragon" &&
    shuffledSince before g

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
    logContains g "Search Light is sacrificed"

#guard
  let g0 := onlyLibrary (emptyHand (withQuest 4) caster) caster [dragon]
  let src := lastPermanent g0
  let before := g0.log.size
  let g := g0.applyTriggeredAbility caster .onMountainEntersQuestThenDragon (some src.id)
  onBattlefield g "Search Light" && (permanent g "Search Light").status.quest == 5 &&
    inLibrary g caster "Search Dragon" && !shuffledSince before g &&
    g.pending == .none

#guard
  let g0 := onlyLibrary (emptyHand afterDraw caster) caster [dragon]
  let before := g0.log.size
  let g := g0.applyTriggeredAbility caster .onMountainEntersQuestThenDragon none
  !onBattlefield g "Search Dragon" && inLibrary g caster "Search Dragon" &&
    !shuffledSince before g

/- Tapped search variants put the found permanent onto the battlefield tapped. -/
#guard
  let g0 := putInHand (onlyLibrary (emptyHand afterDraw caster) caster
    [forest, mountain, dragon]) handDragon caster
  let g := takeSearch (stepEffect g0 searchForestTapped)
  onBattlefield g "Search Forest" && (permanent g "Search Forest").status.tapped &&
    inLibrary g caster "Search Mountain" && !onBattlefield g "Search Mountain"

/- Printed phrases and notations stay intact. -/
#guard TriggeredAbility.onEnterSearchForest.effect.body == Effect.triggerSearchForest.body
#guard TriggeredAbility.onEnterSearchBasicToHand.effect.body == Effect.triggerSearchBasicLandToHand.body
#guard (TriggeredAbility.onEnterGainLifeSearchBasicOnTop 2).effect.body ==
  (Effect.triggerGainLifeSearchBasicOnTop 2).body
#guard TriggeredAbility.onMountainEntersQuestThenDragon.effect.body ==
  Effect.triggerMountainQuestDragon.body
#guard TriggeredAbility.resolutionPhrase Effect.triggerSearchForest ==
  "search your library for a Forest card, put that card onto the battlefield, then shuffle"
#guard TriggeredAbility.resolutionPhrase Effect.triggerSearchBasicLandToHand ==
  "search your library for a basic land card, reveal it, put it into your hand, then shuffle"
#guard TriggeredAbility.toNotation .onEnterSearchForest ==
  "When this permanent enters, search your library for a Forest card, put that card onto the battlefield, then shuffle."
#guard TriggeredAbility.toNotation .onEnterSearchBasicToHand ==
  "When this permanent enters, search your library for a basic land card, reveal it, put it into your hand, then shuffle."
#guard TriggeredAbility.toNotation (.onEnterGainLifeSearchBasicOnTop 2) ==
  "When this permanent enters, you gain 2 life. You may search your library for a basic land card, reveal it, then shuffle and put that card on top."
#guard TriggeredAbility.toNotation .onMountainEntersQuestThenDragon ==
  "Whenever a Mountain you control enters, put a quest counter on this enchantment. If it has six or more quest counters on it, sacrifice it. If you do, search your hand and/or library for a Dragon card and put it onto the battlefield. If you search your library this way, shuffle."

/- CR 702.73a: Off-battlefield changeling creature cards have all creature types
in library and hand (such as Dragon), and do not have noncreature land subtypes
(such as Forest). -/
def changelingCard : CardDef := {
  name := "Search Changeling"
  types := #[.creature]
  subtypes := #["Shapeshifter"]
  keywords := #[Keyword.changeling]
  power := some (.fixed 2)
  toughness := some (.fixed 2)
}

#guard changelingCard.hasSubtype .dragon && !changelingCard.hasSubtype .forest

#guard
  let gLib0 := onlyLibrary (emptyHand afterDraw caster) caster [mountain, changelingCard]
  let gLib := takeSearch (stepEffect gLib0 (searchDragon))
  let gHand0 := putInHand (onlyLibrary (emptyHand afterDraw caster) caster [mountain]) changelingCard caster
  let gHand := takeSearch (stepEffect gHand0 (searchDragon))
  let gForest := takeSearch (stepEffect gLib0 Effect.triggerSearchForest)
  onBattlefield gLib "Search Changeling" &&
    !inLibrary gLib caster "Search Changeling" &&
    onBattlefield gHand "Search Changeling" &&
    !inHand gHand caster "Search Changeling" &&
    !onBattlefield gForest "Search Changeling" &&
    inLibrary gForest caster "Search Changeling"

end Mtg.Engine.SearchLibraryTests
