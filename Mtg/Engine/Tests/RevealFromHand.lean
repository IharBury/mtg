import Mtg.Engine.Fixture

/-!
# `TriggerResolution.revealFromHand`

The opponent reveals their hand, and a nonland card from it or the chosen
creature may be exiled until the source leaves. The announced player
reveals one card plus one for each creature card in the controller's
graveyard, and discards the chosen card. How many cards are revealed, and
what happens next, are arguments.
-/

namespace Mtg.Engine.RevealFromHandTests

open Mtg.Engine
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def sourceCard : CardDef := {
  name := "Cloak Source"
  types := #[.creature]
  power := some 2
  toughness := some 2
}

def bear : CardDef := {
  name := "Reveal Bear"
  types := #[.creature]
  power := some 2
  toughness := some 2
}

def spell : CardDef := {
  name := "Reveal Bolt"
  types := #[.instant]
}

def plot : CardDef := {
  name := "Reveal Plot"
  types := #[.land]
}

def exileUntil : TriggeredAbility.TriggerResolution :=
  .revealFromHand .hand (.exile .target .untilSourceLeaves)

def countedDiscard : TriggeredAbility.TriggerResolution :=
  .revealFromHand .onePlusCreatureCards (.discard (.cards 1 .targetOpponent))

def step (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[])
    (ab : TriggeredAbility := .onEnterDraw 1) : Game :=
  g.applyTriggeredAbility caster ab sourceId targets
    (resolutionOverride := some r)

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
  insertObject g card p (.hand p) none {} (fun id pl =>
    { pl with hand := pl.hand.push id })

def putInGraveyard (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.graveyard p) none {} (fun id pl =>
    { pl with graveyard := pl.graveyard.push id })

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
  let g := step g0 exileUntil (some src.id)
    #[Target.player opp, Target.permanent victim.id]
  inExile g "Reveal Bear" && !onBattlefield g "Reveal Bear" &&
    (obj g "Cloak Source").linkedExile.size == 1 &&
    logContains g "reveals their hand" &&
    logContains g "exiled until the source leaves" &&
    (let (g, _) := g.move (obj g "Cloak Source").id (.graveyard caster) none
     onBattlefield g "Reveal Bear" && logContains g "returns to the battlefield")

#guard
  let g0 := addPermanent (withSource afterDraw) bear opp opp
  let src := obj g0 "Cloak Source"
  let g := step g0 exileUntil (some src.id) #[Target.player opp]
  onBattlefield g "Reveal Bear" && !inExile g "Reveal Bear" &&
    (obj g "Cloak Source").linkedExile.isEmpty &&
    logContains g "reveals their hand"

/- A source that has already left still reveals. Nothing is exiled.
A creature the announced opponent does not control is illegal, and the
hand is still revealed. -/
#guard
  let g0 := addPermanent (withSource afterDraw) bear opp opp
  let src := obj g0 "Cloak Source"
  let victim := obj g0 "Reveal Bear"
  let (g1, _) := g0.move src.id (.graveyard caster) none
  let g := step g1 exileUntil (some src.id)
    #[Target.player opp, Target.permanent victim.id]
  onBattlefield g "Reveal Bear" && !inExile g "Reveal Bear" &&
    logContains g "reveals their hand" &&
    logContains g "Cloak and Dagger have left the battlefield. Nothing is exiled."

#guard
  let g0 := addPermanent (withSource afterDraw) bear caster caster
  let src := obj g0 "Cloak Source"
  let victim := obj g0 "Reveal Bear"
  let g := step g0 exileUntil (some src.id)
    #[Target.player opp, Target.permanent victim.id]
  onBattlefield g "Reveal Bear" && !inExile g "Reveal Bear" &&
    logContains g "illegal target" && logContains g "reveals their hand"

/- A nonland card from the announced player's hand is exiled until the
source leaves, then returns to that hand. A land, and a card from another
hand, stay put. -/
#guard
  let g0 := putInHand (withSource afterDraw) spell opp
  let src := obj g0 "Cloak Source"
  let card := anyObj g0 "Reveal Bolt"
  let g := step g0 exileUntil (some src.id)
    #[Target.player opp, Target.card card.id]
  inExile g "Reveal Bolt" && !inHand g opp "Reveal Bolt" &&
    (obj g "Cloak Source").linkedExile.size == 1 &&
    (let (g, _) := g.move (obj g "Cloak Source").id (.graveyard caster) none
     inHand g opp "Reveal Bolt" && logContains g "returns to Nissa's hand")

#guard
  let g0 := putInHand (withSource afterDraw) plot opp
  let src := obj g0 "Cloak Source"
  let card := anyObj g0 "Reveal Plot"
  let g := step g0 exileUntil (some src.id)
    #[Target.player opp, Target.card card.id]
  inHand g opp "Reveal Plot" && !inExile g "Reveal Plot" &&
    (obj g "Cloak Source").linkedExile.isEmpty &&
    logContains g "reveals their hand"

#guard
  let g0 := putInHand (withSource afterDraw) spell caster
  let src := obj g0 "Cloak Source"
  let card := anyObj g0 "Reveal Bolt"
  let g := step g0 exileUntil (some src.id)
    #[Target.player opp, Target.card card.id]
  inHand g caster "Reveal Bolt" && !inExile g "Reveal Bolt"

/- With no announced player, the first opponent's hand is revealed. -/
#guard
  let g0 := withSource afterDraw
  let before := handSize g0 opp
  let g := step g0 exileUntil (some (obj g0 "Cloak Source").id)
  before > 0 && handSize g opp == before && logContains g "reveals their hand" &&
    logContains g "Nissa"

/- The announced player reveals one card, plus one for each creature card
in the controller's graveyard. A smaller hand is revealed in full. The
cards stay in hand. A missing player reveals nothing. -/
#guard
  let g0 := afterDraw
  let n := handSize g0 opp
  let g := step g0 countedDiscard (targets := #[Target.player opp])
  n > 1 && handSize g opp == n &&
    logContains g "reveals their hand" &&
    logContains g "reveals 1 card(s) (all, if fewer than 1)"

#guard
  let g0 := putInGraveyard (putInGraveyard afterDraw bear caster) bear caster
  let g0 := putInGraveyard g0 spell caster
  let n := handSize g0 opp
  let g := step g0 countedDiscard (targets := #[Target.player opp])
  n > 3 && handSize g opp == n &&
    logContains g "reveals 3 card(s) (all, if fewer than 3)"

#guard
  let g0 := clearHand afterDraw opp
  let g0 := putInHand g0 spell opp
  let g0 := putInGraveyard (putInGraveyard g0 bear caster) bear caster
  let g := step g0 countedDiscard (targets := #[Target.player opp])
  handSize g opp == 1 && inHand g opp "Reveal Bolt" &&
    logContains g "reveals 1 card(s) (all, if fewer than 3)"

#guard
  let g := step afterDraw countedDiscard
  handSize g opp == handSize afterDraw opp && g.log == afterDraw.log

/- Revealing a hand, then discarding, asks the announced player to
discard. Revealing that count, then exiling until the source leaves,
exiles the chosen creature. -/
#guard
  let g0 := addPermanent (withSource afterDraw) bear opp opp
  let src := obj g0 "Cloak Source"
  let victim := obj g0 "Reveal Bear"
  let targets := #[Target.player opp, Target.permanent victim.id]
  let crossed := step g0 (.revealFromHand .hand (.discard (.cards 1 .targetOpponent)))
    (some src.id) targets
  onBattlefield crossed "Reveal Bear" && !inExile crossed "Reveal Bear" &&
    logContains crossed "reveals their hand" &&
    match crossed.pending with
    | .chooseDiscardCard p _ => p == opp
    | _ => false

#guard
  let g0 := addPermanent (withSource afterDraw) bear opp opp
  let src := obj g0 "Cloak Source"
  let victim := obj g0 "Reveal Bear"
  let ab : TriggeredAbility :=
    .triggered .enter (Effect.ofTrigger (.onPermanent .creature .exile))
  let swapped := step g0
    (.revealFromHand .onePlusCreatureCards (.exile .target .untilSourceLeaves))
    (some src.id) #[Target.permanent victim.id] ab
  inExile swapped "Reveal Bear" && !onBattlefield swapped "Reveal Bear" &&
    logContains swapped "reveals" &&
    (obj swapped "Cloak Source").linkedExile.size == 1

#guard TriggeredAbility.resolution cloakAbility == exileUntil
#guard TriggeredAbility.resolution klawAbility == countedDiscard

#guard
  let g0 := addPermanent (withSource afterDraw) bear opp opp
  let src := obj g0 "Cloak Source"
  let victim := obj g0 "Reveal Bear"
  let g := g0.applyTriggeredAbility caster cloakAbility (some src.id)
    #[Target.player opp, Target.permanent victim.id]
  inExile g "Reveal Bear" && (obj g "Cloak Source").linkedExile.size == 1

#guard
  let g0 := clearHand afterDraw opp
  let g0 := putInHand g0 spell opp
  let g := g0.applyTriggeredAbility caster klawAbility none #[Target.player opp]
  handSize g opp == 1 &&
    logContains g "reveals 1 card(s) (all, if fewer than 1)"

#guard TriggeredAbility.resolutionPhrase { resolution := exileUntil } ==
  "choose target opponent and up to one target creature they control. They reveal their hand. You may exile a nonland card from their hand or the chosen creature until this leaves the battlefield"
#guard TriggeredAbility.resolutionPhrase (SharedTrigger.timing (.enter .revealDiscardFromHand)) ==
  "target player reveals a number of cards from their hand equal to one plus the number of creature cards in your graveyard. You choose one of them. That player discards that card"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .revealFromHand .hand (.discard (.cards 1 .targetOpponent)) } ==
  "reveal cards from their hand"
#guard TriggeredAbility.resolutionPhrase
    { resolution :=
        .revealFromHand .onePlusCreatureCards (.exile .target .untilSourceLeaves) } ==
  "reveal cards from their hand"

#guard TriggeredAbility.toNotation cloakAbility ==
  "When this permanent enters, choose target opponent and up to one target creature they control. They reveal their hand. You may exile a nonland card from their hand or the chosen creature until this leaves the battlefield."
#guard TriggeredAbility.toNotation klawAbility ==
  "When this permanent enters, target player reveals a number of cards from their hand equal to one plus the number of creature cards in your graveyard. You choose one of them. That player discards that card."

#guard (SharedTrigger.timing (.enter .revealHandExileUntilLeaves)).resolution ==
  exileUntil
#guard (SharedTrigger.timing (.enter .revealDiscardFromHand)).resolution ==
  countedDiscard
#guard (SharedTrigger.timing (.enter .revealHandExileUntilLeaves)).allowsZeroTargets
#guard !(SharedTrigger.timing (.enter .revealDiscardFromHand)).allowsZeroTargets

end Mtg.Engine.RevealFromHandTests
