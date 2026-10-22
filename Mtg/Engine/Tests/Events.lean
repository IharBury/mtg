import Mtg.Engine.Fixture

/-!
# Game events

Each change that happens is a `GameEvent` on `Game.events`. A condition
asks that log whether the action happened. A trigger matches the change
that happened. A replacement matches the change that would happen, and the
replaced change is not recorded.
-/

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def me : PlayerId := ⟨0⟩

def bear : CardDef :=
  creature "Event Bear" ManaCost.empty #["Bear"] 2 2

def hero : CardDef :=
  creature "Event Hero" ManaCost.empty #["Hero"] 2 2

def holds (g : Game) (cond : TriggeredAbility.ConditionSelector) : Game × Bool :=
  g.triggerIfHolds me (.onEnterDraw 1) none #[] none cond

def quiet (g : Game) : Game :=
  let g := { g with events := #[] }
  g.modifyPlayer me fun pl =>
    { pl with
      cardsDrawnThisTurn := 0
      scriedThisTurn := false
      surveilledThisTurn := false
      artifactEnteredThisTurn := false
      attackedWithHeroThisTurn := false
      heroEnteredThisTurn := false }

/- Drawing is recorded, and the draw condition reads the log after the
turn counter is cleared. -/
#guard
  let g := quiet afterDraw
  let (_, noDraw) := holds g (.atLeast .cardsDrawnThisTurn (.fixed 1))
  let g := (g.record (GameEvent.drew g.turnNumber me ⟨9⟩ 1)).record
    (GameEvent.drew g.turnNumber me ⟨8⟩ 2)
  let (_, two) := holds g (.atLeast .cardsDrawnThisTurn (.fixed 2))
  let (_, three) := holds g (.atLeast .cardsDrawnThisTurn (.fixed 3))
  let flagged := quiet afterDraw |>.modifyPlayer me (fun pl => { pl with cardsDrawnThisTurn := 5 })
  let (_, ignored) := holds flagged (.atLeast .cardsDrawnThisTurn (.fixed 1))
  !noDraw && two && !three && g.loggedDraws me == 2 && !ignored

/- Scrying and surveilling are the look events. Scry 0 does not count. -/
#guard
  let g := quiet afterDraw
  let (_, noScry) := holds g .scriedThisTurn
  let (_, noSurveil) := holds g .surveilledThisTurn
  let g := g.record (GameEvent.looked g.turnNumber me 0)
  let (_, zero) := holds g .scriedThisTurn
  let g := g.record (GameEvent.looked g.turnNumber me 2)
  let (_, scried) := holds g .scriedThisTurn
  let g := g.record (GameEvent.looked g.turnNumber me 1 true)
  let (_, surveilled) := holds g .surveilledThisTurn
  !noScry && !noSurveil && !zero && scried && surveilled

/- An artifact that entered is in the log, including after the flag is clear. -/
#guard
  let g := quiet afterDraw
  let (_, no) := holds g .artifactEnteredThisTurn
  let entered := GameEvent.moved g.turnNumber
    { id := ⟨4⟩, controller := some me, owner := me, artifact := true } .stack .battlefield
  let g := g.record entered
  let (_, yes) := holds g .artifactEnteredThisTurn
  !no && yes && entered.watches .wouldEnterBattlefield

/- A Hero that left after attacking still counts, from the attack event. -/
#guard
  let g := quiet afterDraw
  let attack := GameEvent.attacked g.turnNumber me
    { id := ⟨5⟩, controller := some me, owner := me, creature := true, subtypes := #["Hero"] } ⟨1⟩
  let g := g.record attack
  let (_, yes) := holds g (.attackedWithSubtype "Hero")
  let (_, no) := holds g (.attackedWithSubtype "Goblin")
  yes && !no && attack.matchesTrigger me ⟨5⟩ .attacking

/- A second draw matches the second-card triggers and not a first-card one.
A creature moving to a graveyard matches dies, and not once it is exiled
instead. -/
#guard
  let second := GameEvent.drew 1 me ⟨1⟩ 2
  let death := GameEvent.moved 1
    { id := ⟨7⟩, controller := some me, owner := me, creature := true } .battlefield (.graveyard me)
  let exiled := death.withDestination .exile false
  second.matchesTrigger me ⟨0⟩ .youDraw &&
    second.matchesTrigger me ⟨0⟩ .youDrawSecondCard &&
    second.matchesTrigger ⟨1⟩ ⟨0⟩ .opponentDrawsSecondCard &&
    !second.matchesTrigger ⟨1⟩ ⟨0⟩ .youDraw &&
    death.matchesTrigger me ⟨7⟩ .dying &&
    death.watches .wouldDie &&
    !exiled.isCreatureToGraveyard &&
    !exiled.watches .wouldDie &&
    (GameEvent.looked 1 me 3).matchesTrigger me ⟨0⟩ .youScry

/- The engine records a real draw and a real death, and an exile replacement
records the exile instead of the death. -/
#guard
  let g0 := quiet afterDraw
  let before := g0.events.size
  let g := g0.draw me 1
  let drew := g.events.any fun e =>
    match e.change with
    | .drew p _ _ _ => p == me
    | _ => false
  let g := addPermanent g bear me me
  let b := (g.battlefield.filter (·.name == "Event Bear"))[0]!
  let (g, id) := g.move b.id (.graveyard me) none
  let died :=
    match g.events.back? with
    | some e => e.isCreatureToGraveyard && (g.object! id).zone == .graveyard me
    | none => false
  let g := addPermanent g hero me me
  let h := (g.battlefield.filter (·.name == "Event Hero"))[0]!
  let g := g.setObject { h with status := { h.status with untilEotExileIfDies := true } }
  let (g, id) := g.move h.id (.graveyard me) none
  let replaced :=
    (g.object! id).zone == .exile &&
      match g.events.back? with
      | some e => !e.isCreatureToGraveyard &&
          match e.change with
          | .moved _ _ .exile _ _ => true
          | _ => false
      | none => false
  g.events.size > before && drew && died && replaced

end Mtg.Engine.EventTests
