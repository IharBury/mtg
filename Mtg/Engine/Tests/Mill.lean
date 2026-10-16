import Mtg.Engine.Fixture

/-!
# `TriggerResolution.mill`

The controller, the announced player, and the player who lost life mill
cards. The controller can remember the cards milled, and each opponent's
mill can be seen by the next step. How many is a `NumberSelector` and who
mills is a `PlayerSelector`. Any other selector mills nothing.
-/

namespace Mtg.Engine.MillTests

open Mtg.Engine
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def elf : CardDef := {
  name := "Mill Elf"
  types := #[.creature]
  subtypes := #["Elf"]
  power := some 1
  toughness := some 1
}

def relic : CardDef := {
  name := "Mill Relic"
  types := #[.artifact]
}

def bolt : CardDef := {
  name := "Mill Bolt"
  types := #[.instant]
}

def plot : CardDef := {
  name := "Mill Plot"
  types := #[.land]
}

def putInGraveyard (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.graveyard p) none {} (fun id pl =>
    { pl with graveyard := pl.graveyard.push id })

def putOnLibrary (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.library p) none {} (fun id pl =>
    { pl with library := pl.library.push id })

/-- Replace `p`'s library. The last card is on top. -/
def onlyLibrary (g : Game) (p : PlayerId) (cards : List CardDef) : Game :=
  cards.foldl (fun g c => putOnLibrary g c p)
    (g.modifyPlayer p (fun pl => { pl with library := #[] }))

def libSize (g : Game) (p : PlayerId) : Nat :=
  (g.player p).library.size

def inHand (g : Game) (p : PlayerId) (name : String) : Bool :=
  (g.player p).hand.any (fun id => (g.findObject? id).any (·.name == name))

def inGraveyard (g : Game) (p : PlayerId) (name : String) : Bool :=
  (g.player p).graveyard.any (fun id => (g.findObject? id).any (·.name == name))

def noted (g : Game) (name : String) : Bool :=
  g.milledIdsThisWay.any (fun id => (g.findObject? id).any (·.name == name))

def permanentId (g : Game) (name : String) : ObjectId :=
  match g.battlefield.find? (·.name == name) with
  | some o => o.id
  | none => panic! s!"missing {name}"

def step (g : Game) (r : TriggeredAbility.TriggerResolution)
    (targets : Array Target := #[])
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none)
    (ab : TriggeredAbility := .onEnterDraw 1) : Game :=
  g.applyTriggeredAbility caster ab none targets
    (lastKnownPower := lastKnownPower) (lastKnownToughness := lastKnownToughness)
    (resolutionOverride := some r)

def playerMill : TriggeredAbility := .onDrawSecondMillPlayer 1

/- The controller mills the top cards and leaves both notes alone. -/
#guard
  let marked := putInGraveyard afterDraw relic caster
  let old := (marked.player caster).graveyard.back!
  let g0 := {
    putOnLibrary (putOnLibrary marked elf caster) bolt caster with
    milledIdsThisWay := #[old]
    opponentsMilledThisWay := true }
  let g := step g0 (.mill (.fixed 2))
  inGraveyard g caster "Mill Bolt" && inGraveyard g caster "Mill Elf" &&
    libSize g caster == libSize g0 caster - 2 &&
    libSize g opp == libSize g0 opp &&
    noted g "Mill Relic" && !noted g "Mill Elf" && !noted g "Mill Bolt" &&
    g.opponentsMilledThisWay &&
    logContains g "Chandra mills Mill Bolt" &&
    logContains g "Chandra mills Mill Elf"

/- Milling zero cards changes nothing. A short library mills what it has,
then logs that it is empty. -/
#guard
  let g0 := putOnLibrary afterDraw elf caster
  let g := step g0 (.mill (.fixed 0))
  libSize g caster == libSize g0 caster && g.log.size == g0.log.size &&
    g.milledIdsThisWay.isEmpty

#guard
  let g0 := onlyLibrary afterDraw caster [elf]
  let g := step g0 (.mill (.fixed 3))
  inGraveyard g caster "Mill Elf" && libSize g caster == 0 &&
    logContains g "Chandra mills Mill Elf" &&
    logContains g "Chandra mills nothing (empty library)"

#guard
  let g0 := onlyLibrary afterDraw caster []
  let g := step g0 (.mill (.fixed 2))
  libSize g caster == 0 && g.milledIdsThisWay.isEmpty &&
    logContains g "Chandra mills nothing (empty library)"

/- The announced player mills, including the controller. The ability's
target kind decides who is legal. -/
#guard
  let g0 := putOnLibrary afterDraw bolt opp
  let g := step g0 (.mill (.fixed 1) .target) #[Target.player opp] (ab := playerMill)
  inGraveyard g opp "Mill Bolt" && libSize g caster == libSize g0 caster &&
    logContains g "Nissa mills Mill Bolt" && g.milledIdsThisWay.isEmpty &&
    !g.opponentsMilledThisWay

#guard
  let g0 := putOnLibrary afterDraw elf caster
  let g := step g0 (.mill (.fixed 1) .target) #[Target.player caster] (ab := playerMill)
  inGraveyard g caster "Mill Elf" && logContains g "Chandra mills Mill Elf"

#guard
  let g0 := putOnLibrary afterDraw bolt opp
  let g := step g0 (.mill (.fixed 1) .target) (ab := playerMill)
  !inGraveyard g opp "Mill Bolt" && libSize g opp == libSize g0 opp &&
    logContains g "The target is no longer legal"

#guard
  let g0 := addPermanent (putOnLibrary afterDraw bolt opp) relic caster caster
  let g := step g0 (.mill (.fixed 1) .target) #[Target.permanent (permanentId g0 "Mill Relic")]
    (ab := playerMill)
  !inGraveyard g opp "Mill Bolt" &&
    logContains g "The target is no longer legal"

#guard
  let g0 := putOnLibrary afterDraw bolt opp
  let g0 := g0.setPlayer { g0.player opp with lost := true }
  let g := step g0 (.mill (.fixed 1) .target) #[Target.player opp] (ab := playerMill)
  !inGraveyard g opp "Mill Bolt" &&
    logContains g "The target is no longer legal"

#guard
  let g0 := putOnLibrary afterDraw bolt opp
  let g0 := g0.setPlayer { g0.player opp with protectionFromEverything := true }
  let g := step g0 (.mill (.fixed 1) .target) #[Target.player opp] (ab := playerMill)
  !inGraveyard g opp "Mill Bolt" &&
    logContains g "The target is no longer legal"

#guard
  let g0 := putOnLibrary afterDraw bolt opp
  let g := step g0 (.mill (.fixed 1) .target) #[Target.player opp]
  !inGraveyard g opp "Mill Bolt" &&
    logContains g "The target is no longer legal"

/- The player who lost life mills that many. The count is the last-known
power, and the seat is the last-known toughness. -/
#guard
  let g0 := putOnLibrary (putOnLibrary afterDraw elf opp) bolt opp
  let g := step g0 (.mill .thatManyLost .thatPlayer)
    (lastKnownPower := some 2) (lastKnownToughness := some 1)
  inGraveyard g opp "Mill Bolt" && inGraveyard g opp "Mill Elf" &&
    libSize g opp == libSize g0 opp - 2 &&
    libSize g caster == libSize g0 caster &&
    logContains g "Nissa mills Mill Bolt" &&
    g.milledIdsThisWay.isEmpty && !g.opponentsMilledThisWay

#guard
  let g0 := putOnLibrary afterDraw elf caster
  let g := step g0 (.mill .thatManyLost .thatPlayer)
    (lastKnownPower := some 1) (lastKnownToughness := some 0)
  inGraveyard g caster "Mill Elf" && logContains g "Chandra mills Mill Elf"

#guard
  let g0 := putOnLibrary afterDraw elf opp
  let missingPower := step g0 (.mill .thatManyLost .thatPlayer)
    (lastKnownToughness := some 1)
  let missingSeat := step g0 (.mill .thatManyLost .thatPlayer)
    (lastKnownPower := some 1)
  let neither := step g0 (.mill .thatManyLost .thatPlayer)
  let zero := step g0 (.mill .thatManyLost .thatPlayer)
    (lastKnownPower := some 0) (lastKnownToughness := some 1)
  let negative := step g0 (.mill .thatManyLost .thatPlayer)
    (lastKnownPower := some (-1)) (lastKnownToughness := some 1)
  !inGraveyard missingPower opp "Mill Elf" &&
    missingPower.log.size == g0.log.size &&
    !inGraveyard missingSeat opp "Mill Elf" &&
    missingSeat.log.size == g0.log.size &&
    !inGraveyard neither opp "Mill Elf" &&
    !inGraveyard zero opp "Mill Elf" && zero.log.size == g0.log.size &&
    !inGraveyard negative opp "Mill Elf" && negative.log.size == g0.log.size

/- Remembering the milled cards records only cards that entered the
graveyard this way. An empty or short library still records what was milled. -/
#guard
  let marked := putInGraveyard afterDraw relic caster
  let old := (marked.player caster).graveyard.back!
  let g0 := {
    putOnLibrary (putOnLibrary marked plot caster) elf caster with
    milledIdsThisWay := #[old]
    opponentsMilledThisWay := true }
  let g := step g0 (.mill (.fixed 2) (note := .milledCards))
  noted g "Mill Elf" && noted g "Mill Plot" && !noted g "Mill Relic" &&
    g.milledIdsThisWay.size == 2 && g.opponentsMilledThisWay &&
    inGraveyard g caster "Mill Elf" && inGraveyard g caster "Mill Plot"

#guard
  let g0 := onlyLibrary afterDraw caster [elf]
  let g := step g0 (.mill (.fixed 4) (note := .milledCards))
  noted g "Mill Elf" && g.milledIdsThisWay.size == 1 &&
    logContains g "mills nothing (empty library)"

#guard
  let g0 := { onlyLibrary afterDraw caster [] with milledIdsThisWay := #[⟨0⟩] }
  let g := step g0 (.mill (.fixed 2) (note := .milledCards))
  g.milledIdsThisWay.isEmpty &&
    logContains g "mills nothing (empty library)"

/- Cards of the noted subtype return to hand. A card already in the
graveyard, and a milled card of another type, stay there. The note is
then cleared. -/
#guard
  let g0 := putInGraveyard (onlyLibrary afterDraw caster [relic, elf]) elf caster
  let oldElf :=
    (g0.player caster).graveyard.any (fun id =>
      (g0.findObject? id).any (·.name == "Mill Elf"))
  let g := step g0
    (.sequence [.mill (.fixed 2) (note := .milledCards), .returnToHand (.milledSubtype "Elf")])
  oldElf && inHand g caster "Mill Elf" &&
    inGraveyard g caster "Mill Relic" &&
    inGraveyard g caster "Mill Elf" &&
    g.milledIdsThisWay.isEmpty &&
    logContains g "Mill Elf is put into Chandra's hand"

#guard
  let g0 := onlyLibrary afterDraw caster [relic]
  let g := step g0
    (.sequence [.mill (.fixed 1) (note := .milledCards), .returnToHand (.milledSubtype "Elf")])
  !inHand g caster "Mill Relic" && inGraveyard g caster "Mill Relic" &&
    g.milledIdsThisWay.isEmpty

/- Each opponent mills, and the next step sees whether a card was milled.
A lost opponent is not milled. The controller's earlier note stays. -/
#guard
  let marked := putInGraveyard afterDraw relic caster
  let old := (marked.player caster).graveyard.back!
  let g0 := {
    onlyLibrary marked opp [plot, bolt] with
    milledIdsThisWay := #[old]
    opponentsMilledThisWay := false }
  let g := step g0 (.mill (.fixed 2) .eachOpponent (note := .opponentsMilled))
  inGraveyard g opp "Mill Bolt" && inGraveyard g opp "Mill Plot" &&
    libSize g caster == libSize g0 caster &&
    g.opponentsMilledThisWay && noted g "Mill Relic" &&
    !noted g "Mill Bolt" &&
    logContains g "Nissa mills Mill Bolt" &&
    logContains g "Nissa mills Mill Plot"

#guard
  let g0 := onlyLibrary afterDraw opp []
  let g := step g0 (.mill (.fixed 2) .eachOpponent (note := .opponentsMilled))
  !g.opponentsMilledThisWay &&
    logContains g "Nissa mills nothing (empty library)"

#guard
  let g0 := onlyLibrary afterDraw opp [bolt]
  let g := step g0 (.mill (.fixed 0) .eachOpponent (note := .opponentsMilled))
  !g.opponentsMilledThisWay && !inGraveyard g opp "Mill Bolt" &&
    g.log.size == g0.log.size

#guard
  let g0 := onlyLibrary afterDraw opp [bolt]
  let g0 := g0.setPlayer { g0.player opp with lost := true }
  let g := step g0 (.mill (.fixed 2) .eachOpponent (note := .opponentsMilled))
  !g.opponentsMilledThisWay && !inGraveyard g opp "Mill Bolt" &&
    g.log.size == g0.log.size

/- With no legal card to copy, the following step removes the reflexive
ability and clears the note. -/
#guard
  let g0 := onlyLibrary afterDraw opp [plot]
  let g := step g0 (.sequence [
    .mill (.fixed 1) .eachOpponent (note := .opponentsMilled),
    .«if» .opponentsMilled (.queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying))])
  inGraveyard g opp "Mill Plot" && !g.opponentsMilledThisWay &&
    logContains g "reflexive ability has no legal target and is removed"

#guard
  let g0 := onlyLibrary afterDraw opp []
  let g := step g0 (.sequence [
    .mill (.fixed 2) .eachOpponent (note := .opponentsMilled),
    .«if» .opponentsMilled (.queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying))])
  !g.opponentsMilledThisWay && g.stack.isEmpty &&
    !(logContains g "reflexive ability")

/- A combination that is not printed mills nothing. -/
#guard
  let g0 := {
    putOnLibrary (putOnLibrary afterDraw elf caster) bolt opp with
    milledIdsThisWay := #[⟨1⟩]
    opponentsMilledThisWay := true }
  let crossed := [
    .mill (.fixed 2) .target (note := .milledCards),
    .mill (.fixed 2) .eachOpponent,
    .mill .thatManyLost,
    .mill (.fixed 2) .thatPlayer,
    .mill (.fixed 2) .eachOpponent .milledCards,
    .mill (.fixed 2) .you .opponentsMilled,
    .mill .perOtherCreature]
  crossed.all fun r =>
    let g := step g0 r #[Target.player opp]
      (lastKnownPower := some 2) (lastKnownToughness := some 1)
      (ab := playerMill)
    libSize g caster == libSize g0 caster &&
      libSize g opp == libSize g0 opp &&
      g.milledIdsThisWay == #[⟨1⟩] && g.opponentsMilledThisWay &&
      g.log.size == g0.log.size

/- Printed phrases and resolutions stay with the combination that produces them. -/
#guard TriggeredAbility.resolution (.onDrawSecondMillPlayer 3) == .mill (.fixed 3) .target
#guard TriggeredAbility.resolution .onPlayerLosesLifeMillThatMany ==
  .mill .thatManyLost .thatPlayer
#guard TriggeredAbility.resolution (.onEnterMillThenSubtypeToHand 4 "Elf") ==
  .sequence [.mill (.fixed 4) (note := .milledCards), .returnToHand (.milledSubtype "Elf")]
#guard TriggeredAbility.resolution .onCastSecondSpellMillThenCopy ==
  .sequence [
    .mill (.fixed 2) .eachOpponent (note := .opponentsMilled),
    .«if» .opponentsMilled (.queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying))]
#guard TriggeredAbility.resolution .onEnterVillainIfGyElseMill ==
  .ifElse (.creatureCardsInGraveyardAtLeast 2)
    (.createTokens .villain21menace 1 true) (.mill (.fixed 2))
#guard TriggeredAbility.resolutionPhrase { resolution := .mill (.fixed 4) } == "mill 4 cards"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .mill (.fixed 4) (note := .milledCards) } == "mill 4 cards"
#guard TriggeredAbility.resolutionPhrase
    { targeting := .of .player, resolution := .mill (.fixed 3) .target } ==
  "target player mills 3 cards"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .mill .thatManyLost .thatPlayer } ==
  "that player mills that many cards"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .mill (.fixed 2) .eachOpponent (note := .opponentsMilled) } ==
  "each opponent mills 2 cards"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .mill (.fixed 2) .target (note := .milledCards) } == "mill"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .mill .perOtherCreature } == "mill"
#guard TriggeredAbility.toNotation (.onDrawSecondMillPlayer 3) ==
  "Whenever you draw your second card each turn, target player mills 3 cards."
#guard TriggeredAbility.toNotation .onPlayerLosesLifeMillThatMany ==
  "Whenever a player loses life, that player mills that many cards."
#guard TriggeredAbility.toNotation (.onEnterMillThenSubtypeToHand 4 "Elf") ==
  "When this permanent enters, mill 4 cards, then put all Elf cards from among them into your hand."
#guard TriggeredAbility.toNotation .onCastSecondSpellMillThenCopy ==
  "Whenever you cast your second spell each turn, each opponent mills two cards. When one or more cards are milled this way, exile target enchantment, instant, or sorcery card with equal or lesser mana value than that spell from an opponent's graveyard. Copy the exiled card. You may cast the copy without paying its mana cost."

end Mtg.Engine.MillTests
