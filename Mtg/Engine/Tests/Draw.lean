import Mtg.Engine.Tests.Builders
import Mtg.Engine.Fixture

/-!
# Unified `PlayerOp.drawCards`

A fixed count, one card per tapped Human, one card per fat graveyard, the
discarded hand, mana spent to cast the triggering spell, and the opponent's
offer to have you draw.
-/

namespace Mtg.Engine.DrawTests

open Mtg.Engine
open Mtg.Engine.Tests hiding afterDraw

def afterDraw : Game := Mtg.Engine.Tests.afterDraw.change (.pushContinuationFrame {})

def caster : PlayerId := ⟨0⟩
def opponent : PlayerId := ⟨1⟩

def pebble : CardDef := { name := "Pebble", types := #[.artifact] }
def humanDef : CardDef :=
  { name := "Town Human", types := #[.creature], subtypes := #["Human"], power := some (.fixed 1), toughness := some (.fixed 1) }

def handSize (g : Game) (p : PlayerId) : Nat :=
  (g.player p).hand.size

def pebbleOf (g : Game) : GameObject :=
  match g.battlefield.find? (·.name == "Pebble") with
  | some o => o
  | none => panic! "missing Pebble"

/-- A resolving ability whose cause recorded `spent` mana. -/
def withSpent (spent : Nat) : Game :=
  let g := addPermanent afterDraw pebble caster caster
  let src := pebbleOf g
  let causeId : ObjectId := ⟨911⟩
  let g := g.record (GameEvent.manaSpent g.turnNumber caster (Array.replicate spent { mana := .colorless }) (forObject := some causeId))
  let g := g.record (GameEvent.spellCast g.turnNumber caster
    { id := some causeId, controller := some caster, owner := caster } (.hand caster))
  let abId : ObjectId := ⟨g.nextObjectId⟩
  let g := g.record (GameEvent.triggerPutOnStack g.turnNumber abId (g.snapshot src) caster
    (spec := { sourceId := some src.id, fraCauseId := some causeId, fraCauseStatus := some {} }))
  g.change (.resolvingAbility (some abId))

def drawStep (g : Game) (i : Instruction) : Game :=
  g.applyTriggeredAbility caster (TriggeredAbility.ofPattern .thisEnters i) none

/- The controller draws the printed count. -/
#guard
  let before := handSize afterDraw caster
  let g := afterDraw.applyTriggeredAbility caster (.onEnterDraw 2) none
  handSize g caster == before + 2

/- Each Human tapped by the previous step is one card. Zero taps draw nothing. -/
#guard
  let g0 := addPermanent (addPermanent afterDraw humanDef caster caster) humanDef caster caster
  let humans := (g0.permanentsOf caster).filter (fun o => g0.hasSubtype o .human) |>.map (·.id)
  let before := handSize g0 caster
  let g1 := g0.applyTriggeredAbility caster .onAttackTapHumansDraw none
  let g2 := mustApply g1 caster (.choosePermanents humans)
  g1.pending == .tapHumans caster && handSize g2 caster == before + 2

#guard
  let g0 := addPermanent afterDraw humanDef caster caster
  let before := handSize g0 caster
  let g1 := g0.applyTriggeredAbility caster .onAttackTapHumansDraw none
  let g2 := mustApply g1 caster .decline
  g1.pending == .tapHumans caster && handSize g2 caster == before

/- One card for each graveyard with seven or more cards. -/
#guard
  let before := handSize afterDraw caster
  let g := (afterDraw.mill caster 7).applyTriggeredAbility caster
    .onDiesDrawPerFatGraveyard none
  handSize g caster == before + 1

#guard
  let before := handSize afterDraw caster
  let g := afterDraw.applyTriggeredAbility caster .onDiesDrawPerFatGraveyard none
  handSize g caster == before && logContains g "draws no cards"

/- Balin's discarded-hand count is the draw count. A declined discard draws nothing. -/
#guard
  let before := handSize afterDraw caster
  let g1 := afterDraw.applyTriggeredAbility caster (.onThisOrAnotherSubtypeEntersDiscardHand "Dwarf") none
  let g2 := mustApply g1 caster .accept
  handSize g2 caster == before

#guard
  let before := handSize afterDraw caster
  let g1 := afterDraw.applyTriggeredAbility caster (.onThisOrAnotherSubtypeEntersDiscardHand "Dwarf") none
  let g2 := mustApply g1 caster .decline
  handSize g2 caster == before

/- Mana spent to cast the triggering spell is the draw count. -/
#guard
  let g0 := withSpent 4
  let before := handSize g0 caster
  let g := drawStep g0 (Instruction.draw (.manaSpent .triggerSubject))
  handSize g caster == before + 4

#guard
  let g0 := withSpent 0
  let g := drawStep g0 (Instruction.draw (.manaSpent .triggerSubject))
  handSize g caster == handSize g0 caster

/- Palantír offers the targeted opponent to let you draw (after scrying 2). -/
#guard
  let g0 := addPermanent afterDraw pebble caster caster
  let sid := (pebbleOf g0).id
  let g1 := g0.applyTriggeredAbility caster .onYourEndStepPalantir (some sid) #[.player opponent]
  let lib := (g1.player caster).library
  let top2 := #[lib[lib.size - 1]!, lib[lib.size - 2]!]
  let g2 := mustApply g1 caster (.scry top2 #[])
  match g2.pending with
  | .fraChoice p (.palantirMayDraw c id) => p == opponent && c == caster && id == sid
  | _ => false

/- You may draw X and discard two when mana was spent. -/
#guard
  let g := (withSpent 4).applyTriggeredAbility caster
    .onCastNoncreatureMayDrawXDiscard2 none
  match g.pending with
  | .fraChoice p (.mayDrawThenDiscard 4 2) => p == caster
  | _ => false

#guard
  let g := (withSpent 0).applyTriggeredAbility caster
    .onCastNoncreatureMayDrawXDiscard2 none
  g.pending == .none && logContains g "No mana was spent to cast that spell"

/- CR 101.4 / 121.2 / 121.2c: triggered multi-opponent draws are unbatched
per card, share one `.oneShotEffect` cause, and draw in APNAP order. -/
#guard
  let g3 :=
    match Start.start {
      seats := #[{ name := "P0", deck := testRedDeck },
                 { name := "P1", deck := testRedDeck },
                 { name := "P2", deck := testRedDeck }]
      startingPlayer := some 2
      seed := 11 } with
    | .ok g => keepOpeningHands g 16
    | .error e => panic! e
  let startIdx := g3.events.size
  let gAfter := g3.applyAbilityEffect ⟨0⟩ { body := Instruction.drawFixed 1 .opponents } #[] none
  let drawEvs := (gAfter.events.extract startIdx gAfter.events.size).filter fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ _ _ (.draw _ _) _ _ _)) => true
    | _ => false
  let drawers := drawEvs.filterMap fun e =>
    match e.change with
    | .rules (.zone (.moved _ _ _ _ (.draw _ _) p _ _)) => p
    | _ => none
  drawEvs.size == 2 &&
    drawers == #[⟨2⟩, ⟨1⟩] &&
    drawEvs[0]!.batch.isSome &&
    drawEvs[0]!.batch != drawEvs[1]!.batch &&
    drawEvs[0]!.cause?.isSome &&
    drawEvs[0]!.cause? == drawEvs[1]!.cause?

end Mtg.Engine.DrawTests
