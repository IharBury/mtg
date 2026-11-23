import Mtg.Engine.Fixture

/-!
# Unified library inspection instructions (`PlayerInstr.inspectLibrary`)

Reveal top N and put a random creature onto the battlefield, reveal until a
creature (battlefield if MV ≤ lands, else hand), reveal until a Saga,
Gríma's exile until instant/sorcery for free cast, and Black Widow's exile
until nonland all execute through `PlayerInstr.inspectLibrary`.
-/

namespace Mtg.Engine.RevealLibraryTests

open Mtg.Engine
open Mtg.Engine.Tests hiding afterDraw

def afterDraw : Game := Mtg.Engine.Tests.afterDraw.change (.pushContinuationFrame {})

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def bear : CardDef := {
  name := "Reveal Bear"
  types := #[.creature]
  power := some 2
  toughness := some 2
}

def elf : CardDef := {
  name := "Reveal Elf"
  types := #[.creature]
  power := some 1
  toughness := some 1
}

def costly : CardDef := {
  name := "Costly Bear"
  manaCost := ManaCost.ofGeneric 2
  types := #[.creature]
  power := some 2
  toughness := some 2
}

def plot : CardDef := {
  name := "Reveal Plot"
  types := #[.land]
}

def relic : CardDef := {
  name := "Reveal Relic"
  types := #[.artifact]
}

def bolt : CardDef := {
  name := "Reveal Bolt"
  types := #[.instant]
}

def tale : CardDef := {
  name := "Reveal Tale"
  types := #[.enchantment]
  subtypes := #["Saga"]
  triggeredAbilities := #[TriggeredAbility.sagaChapter 1 (Effect.gainLife 1)]
}

def spy : CardDef := {
  name := "Widow Source"
  types := #[.creature]
  power := some 1
  toughness := some 2
}

def putOnLibrary (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.library p)

/-- Replace `p`'s library. The last card is on top. -/
def onlyLibrary (g : Game) (p : PlayerId) (cards : List CardDef) : Game :=
  cards.foldl (fun g c => putOnLibrary g c p)
    (emptyLibrary g p)

def withLands (g : Game) (n : Nat) : Game :=
  (List.range n).foldl (fun g _ => addPermanent g plot caster caster) g

def stepRaw (g : Game) (ab : TriggeredAbility)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[]) : Game :=
  g.applyTriggeredAbility caster ab sourceId targets

def step (g : Game) (ab : TriggeredAbility)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[]) : Game :=
  (stepRaw g ab sourceId targets).resolveRandom

def libNames (g : Game) (p : PlayerId) : List String :=
  (g.player p).library.toList.map fun id =>
    (g.findObject? id).map (·.name) |>.getD ""

def inLib (g : Game) (p : PlayerId) (name : String) : Bool :=
  libNames g p |>.contains name

def inHand (g : Game) (p : PlayerId) (name : String) : Bool :=
  (g.player p).hand.any (fun id => (g.findObject? id).any (·.name == name))

def inExile (g : Game) (name : String) : Bool :=
  g.objects.any (fun o => o.name == name && o.zone == .exile)

def onBattlefield (g : Game) (name : String) : Bool :=
  g.battlefield.any (·.name == name)

def libId (g : Game) (p : PlayerId) (name : String) : ObjectId :=
  match (g.player p).library.find? (fun id => (g.findObject? id).any (·.name == name)) with
  | some id => id
  | none => panic! s!"missing {name}"

def ordered (g : Game) (ids : Array ObjectId := #[]) : Game :=
  match g.supplyOrder ids with
  | .ok g => g
  | .error e => panic! e

def spyId (g : Game) : ObjectId :=
  match g.battlefield.find? (·.name == "Widow Source") with
  | some o => o.id
  | none => panic! "missing Widow Source"

def noteHit (g : Game) (p : PlayerId) : Game :=
  let g :=
    if onBattlefield g "Widow Source" then g
    else addPermanent g spy caster caster
  g.noteCombatDamageTo p (g.snapshot (g.object! (spyId g)))

/- Reveal top N, put a random creature onto the battlefield, rest on bottom. -/
#guard
  let g0 := onlyLibrary (onlyLibrary afterDraw caster [relic, plot, bear]) opp [bolt]
  let g := step g0 (.onDiesRevealTopPutRandomCreature 2)
  onBattlefield g "Reveal Bear" && !inLib g caster "Reveal Bear" &&
    libNames g caster == ["Reveal Plot", "Reveal Relic"] &&
    libNames g opp == ["Reveal Bolt"]

#guard
  let g0 := onlyLibrary afterDraw caster [relic, plot]
  let g := step g0 (.onDiesRevealTopPutRandomCreature 1)
  !onBattlefield g "Reveal Plot" &&
    libNames g caster == ["Reveal Plot", "Reveal Relic"]

#guard
  let g0 := onlyLibrary afterDraw caster [plot, bear]
  let g := step g0 (.onDiesRevealTopPutRandomCreature 5)
  onBattlefield g "Reveal Bear" && libNames g caster == ["Reveal Plot"]

#guard
  let g0 := onlyLibrary afterDraw caster [plot, bear, elf]
  let g := stepRaw g0 (.onDiesRevealTopPutRandomCreature 3)
  let bearId := libId g caster "Reveal Bear"
  let elfId := libId g caster "Reveal Elf"
  let waiting :=
    match g.pending with
    | .resolveRandom (.chooseObject ids) =>
      ids == #[bearId, elfId] && !onBattlefield g "Reveal Bear" && !onBattlefield g "Reveal Elf"
    | _ => false
  let g := ordered g #[elfId]
  waiting && onBattlefield g "Reveal Elf" && !onBattlefield g "Reveal Bear"

#guard
  let g0 := onlyLibrary afterDraw caster [plot, bear, elf]
  let g := step g0 (.onDiesRevealTopPutRandomCreature 3)
  let bears := onBattlefield g "Reveal Bear"
  let elves := onBattlefield g "Reveal Elf"
  bears != elves && inLib g caster "Reveal Plot"

/- Reveal until a creature: MV ≤ lands enters battlefield, otherwise hand. -/
#guard
  let g0 := onlyLibrary afterDraw caster [elf, plot, bear]
  let g := step g0 .onNontokenYouControlDiesRevealCreature
  onBattlefield g "Reveal Bear" && !inHand g caster "Reveal Bear" &&
    libNames g caster == ["Reveal Elf", "Reveal Plot"]

#guard
  let g0 := onlyLibrary afterDraw caster [plot, costly]
  let g := step g0 .onNontokenYouControlDiesRevealCreature
  inHand g caster "Costly Bear" && !onBattlefield g "Costly Bear" &&
    libNames g caster == ["Reveal Plot"]

#guard
  let g0 := withLands (onlyLibrary afterDraw caster [plot, costly]) 2
  let g := step g0 .onNontokenYouControlDiesRevealCreature
  onBattlefield g "Costly Bear" && !inHand g caster "Costly Bear"

#guard
  let g0 := withLands (onlyLibrary afterDraw caster [costly]) 1
  let g := step g0 .onNontokenYouControlDiesRevealCreature
  inHand g caster "Costly Bear" && !onBattlefield g "Costly Bear"

#guard
  let g0 := onlyLibrary afterDraw caster []
  let g := step g0 .onNontokenYouControlDiesRevealCreature
  (g.player caster).library.isEmpty

/- Reveal until a Saga: Saga enters battlefield, rest on bottom. -/
#guard
  let g0 := onlyLibrary afterDraw caster [relic, plot, tale]
  let g := step g0 .onFinalSagaChapterRevealSaga
  onBattlefield g "Reveal Tale" &&
    libNames g caster == ["Reveal Relic", "Reveal Plot"]

#guard
  let g0 := onlyLibrary afterDraw caster [tale]
  let g := step g0 .onFinalSagaChapterRevealSaga
  onBattlefield g "Reveal Tale" && (g.player caster).library.isEmpty

#guard
  let g0 := onlyLibrary afterDraw caster [bolt, plot]
  let g := step g0 .onFinalSagaChapterRevealSaga
  !onBattlefield g "Reveal Bolt" && !onBattlefield g "Reveal Plot" &&
    inLib g caster "Reveal Bolt" && inLib g caster "Reveal Plot"

/- Gríma: damaged player exiles until instant or sorcery and offers free cast. -/
#guard
  let g0 := onlyLibrary (onlyLibrary afterDraw opp [relic, bolt]) caster [bear]
  let g0 := noteHit g0 opp
  let g := step g0 .onCombatDamageImpulseInstantSorcery
  inExile g "Reveal Bolt" && inLib g opp "Reveal Relic" &&
    libNames g caster == ["Reveal Bear"] &&
    g.pending != .none

#guard
  let g0 := onlyLibrary afterDraw opp [plot, bolt]
  let g0 := noteHit g0 opp
  let g := step g0 .onCombatDamageImpulseInstantSorcery
  inExile g "Reveal Bolt" && g.pending != .none

/- Black Widow: damaged player exiles until nonland; may put +1/+1 counter or cast exiled card. -/
#guard
  let g0 := onlyLibrary (addPermanent afterDraw spy caster caster) opp [plot, bolt]
  let src := spyId g0
  let g := step g0 (.onWatch Effect.watchCombatDamageExileUntilNonland) (some src) #[Target.player opp]
  let declined := mustApply g caster .decline
  inExile g "Reveal Bolt" && libNames g opp == ["Reveal Plot"] &&
    (declined.objects.any fun o =>
      o.name == "Reveal Bolt" && o.zone == .exile && (declined.playPermission o).isSome)

#guard
  let g0 := onlyLibrary afterDraw opp [plot, bolt]
  let g := step g0 (.onWatch Effect.watchCombatDamageExileUntilNonland) none #[Target.player opp]
  inExile g "Reveal Bolt" && libNames g opp == ["Reveal Plot"] &&
    (g.objects.any fun o =>
      o.name == "Reveal Bolt" && o.zone == .exile && (g.playPermission o).isSome)

/- Printed notations stay intact. -/
#guard TriggeredAbility.toNotation (.onDiesRevealTopPutRandomCreature 4) ==
  s!"When this artifact is put into a graveyard from the battlefield, reveal the top 4 cards of your library. Put a random creature card from among them onto the battlefield. {restOnBottomRandomPhrase}."
#guard TriggeredAbility.toNotation .onNontokenYouControlDiesRevealCreature ==
  s!"Whenever a nontoken creature you control dies, reveal cards from the top of your library until you reveal a creature card. If its mana value is less than or equal to the number of lands you control, put it onto the battlefield. Otherwise, put it into your hand. {restOnBottomRandomPhrase}. This ability triggers only once each turn."
#guard TriggeredAbility.toNotation .onFinalSagaChapterRevealSaga ==
  "Whenever the final chapter ability of a Saga you control resolves, reveal cards from the top of your library until you reveal a Saga card. Put that card onto the battlefield and the rest on the bottom of your library in a random order. This ability triggers only once each turn."
#guard TriggeredAbility.toNotation .onCombatDamageImpulseInstantSorcery ==
  "Whenever Gríma deals combat damage to a player, that player exiles cards from the top of their library until they exile an instant or sorcery card. You may cast that card without paying its mana cost. Then that player puts the exiled cards that weren't cast this way on the bottom of their library in a random order."

end Mtg.Engine.RevealLibraryTests
