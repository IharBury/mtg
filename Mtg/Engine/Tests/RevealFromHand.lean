import Mtg.Engine.Tests.Builders
import Mtg.Engine.Fixture

/-!
# Unified reveal-from-hand instructions (`PlayerInstr.reveal`)

Cloak and Dagger reveals an opponent's hand and exiles a nonland card from
it or the chosen creature until the source leaves. Klaw reveals 1 + creature
cards in your graveyard from target player's hand and discards one.
-/

namespace Mtg.Engine.RevealFromHandTests

open Mtg.Engine
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def sourceCard : CardDef := {
  name := "Cloak Source"
  types := #[.creature]
  power := some (.fixed 2)
  toughness := some (.fixed 2)
}

def bear : CardDef := {
  name := "Reveal Bear"
  types := #[.creature]
  power := some (.fixed 2)
  toughness := some (.fixed 2)
}

def spell : CardDef := {
  name := "Reveal Bolt"
  types := #[.instant]
}

def plot : CardDef := {
  name := "Reveal Plot"
  types := #[.land]
}

def obj (g : Game) (name : String) : GameObject :=
  match g.battlefield.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing {name}"

def anyObj (g : Game) (name : String) : GameObject :=
  match g.objects.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing {name}"

def onBattlefield (g : Game) (name : String) : Bool :=
  g.battlefield.any (·.name == name)

def inHand (g : Game) (p : PlayerId) (name : String) : Bool :=
  (g.player p).hand.any (fun id => (g.findObject? id).any (·.name == name))

def inExile (g : Game) (name : String) : Bool :=
  g.objects.any (fun o => o.name == name && o.zone == .exile)

def handSize (g : Game) (p : PlayerId) : Nat :=
  (g.player p).hand.size

def putInHand (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.hand p)

def putInGraveyard (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.graveyard p)

def clearHand (g : Game) (p : PlayerId) : Game :=
  (g.player p).hand.foldl (fun g id => (g.move id (.library p) none).1) g

def withSource (g : Game) : Game :=
  addPermanent g sourceCard caster caster

def cloakAbility : TriggeredAbility :=
  .onEnter Effect.enterRevealHandExileUntilLeaves

def klawAbility : TriggeredAbility :=
  .onEnter Effect.enterRevealDiscardFromHand

/- The chosen creature an opponent controls is exiled until the source
leaves, and returns when the source leaves. Choosing none only reveals. -/
#guard
  let g0 := addPermanent (withSource afterDraw) bear opp opp
  let src := obj g0 "Cloak Source"
  let victim := obj g0 "Reveal Bear"
  let g := g0.applyTriggeredAbility caster cloakAbility (some src.id)
    #[Target.player opp, Target.permanent victim.id]
  inExile g "Reveal Bear" && !onBattlefield g "Reveal Bear" &&
    (obj g "Cloak Source").linkedExile.size == 1 &&
    logContains g "reveals their hand" &&
    (let (g, _) := g.move (obj g "Cloak Source").id (.graveyard caster) none
     onBattlefield g "Reveal Bear" && logContains g "returns to the battlefield")

#guard
  let g0 := addPermanent (withSource afterDraw) bear opp opp
  let src := obj g0 "Cloak Source"
  let g := g0.applyTriggeredAbility caster cloakAbility (some src.id) #[Target.player opp]
  onBattlefield g "Reveal Bear" && !inExile g "Reveal Bear" &&
    (obj g "Cloak Source").linkedExile.isEmpty &&
    logContains g "reveals their hand"

/- A source that has already left still reveals; nothing is exiled. -/
#guard
  let g0 := addPermanent (withSource afterDraw) bear opp opp
  let src := obj g0 "Cloak Source"
  let victim := obj g0 "Reveal Bear"
  let (g1, _) := g0.move src.id (.graveyard caster) none
  let g := g1.applyTriggeredAbility caster cloakAbility (some src.id)
    #[Target.player opp, Target.permanent victim.id]
  onBattlefield g "Reveal Bear" && !inExile g "Reveal Bear" &&
    logContains g "reveals their hand"

/- A creature the announced opponent does not control is not exiled. -/
#guard
  let g0 := addPermanent (withSource afterDraw) bear caster caster
  let src := obj g0 "Cloak Source"
  let victim := obj g0 "Reveal Bear"
  let g := g0.applyTriggeredAbility caster cloakAbility (some src.id)
    #[Target.player opp, Target.permanent victim.id]
  onBattlefield g "Reveal Bear" && !inExile g "Reveal Bear" &&
    logContains g "reveals their hand"

/- A nonland card from the announced player's hand is exiled until the
source leaves, then returns to that hand. A land stays put. -/
#guard
  let g0 := putInHand (withSource afterDraw) spell opp
  let src := obj g0 "Cloak Source"
  let card := anyObj g0 "Reveal Bolt"
  let g := g0.applyTriggeredAbility caster cloakAbility (some src.id)
    #[Target.player opp, Target.card card.id]
  inExile g "Reveal Bolt" && !inHand g opp "Reveal Bolt" &&
    (obj g "Cloak Source").linkedExile.size == 1 &&
    (let (g, _) := g.move (obj g "Cloak Source").id (.graveyard caster) none
     inHand g opp "Reveal Bolt")

#guard
  let g0 := putInHand (withSource afterDraw) plot opp
  let src := obj g0 "Cloak Source"
  let card := anyObj g0 "Reveal Plot"
  let g := g0.applyTriggeredAbility caster cloakAbility (some src.id)
    #[Target.player opp, Target.card card.id]
  inHand g opp "Reveal Plot" && !inExile g "Reveal Plot" &&
    (obj g "Cloak Source").linkedExile.isEmpty

/- The announced player reveals 1 + creature cards in the controller's graveyard. -/
#guard
  let g0 := afterDraw
  let n := handSize g0 opp
  let g := g0.applyTriggeredAbility caster klawAbility none #[Target.player opp]
  n > 1 && handSize g opp == n &&
    logContains g "reveals 1 card(s) (all, if fewer than 1)"

#guard
  let g0 := putInGraveyard (putInGraveyard afterDraw bear caster) bear caster
  let g0 := putInGraveyard g0 spell caster
  let n := handSize g0 opp
  let g := g0.applyTriggeredAbility caster klawAbility none #[Target.player opp]
  n > 3 && handSize g opp == n &&
    logContains g "reveals 3 card(s) (all, if fewer than 3)"

#guard
  let g0 := clearHand afterDraw opp
  let g0 := putInHand g0 spell opp
  let g0 := putInGraveyard (putInGraveyard g0 bear caster) bear caster
  let g := g0.applyTriggeredAbility caster klawAbility none #[Target.player opp]
  handSize g opp == 1 && inHand g opp "Reveal Bolt" &&
    logContains g "reveals 1 card(s) (all, if fewer than 3)"

#guard
  let g := afterDraw.applyTriggeredAbility caster klawAbility none #[]
  handSize g opp == handSize afterDraw opp

/- Printed notations and target metadata stay intact. -/
#guard TriggeredAbility.toNotation cloakAbility ==
  "When this permanent enters, choose target opponent and up to one target creature they control. They reveal their hand. You may exile a nonland card from their hand or the chosen creature until this leaves the battlefield."
#guard TriggeredAbility.toNotation klawAbility ==
  "When this permanent enters, target player reveals a number of cards from their hand equal to one plus the number of creature cards in your graveyard. You choose one of them. That player discards that card."
#guard Effect.enterRevealHandExileUntilLeaves.allowsZeroTargets
#guard !Effect.enterRevealDiscardFromHand.allowsZeroTargets

end Mtg.Engine.RevealFromHandTests
