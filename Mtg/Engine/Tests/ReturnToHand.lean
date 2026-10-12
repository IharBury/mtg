import Mtg.Engine.Fixture

/-!
# `TriggerResolution.returnToHand`

A graveyard card, a permanent to its owner's hand, a graveyard permanent
card, milled cards of a subtype, and the source from its owner's graveyard.
-/

namespace Mtg.Engine.ReturnToHandTests

open Mtg.Engine
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def owner : PlayerId := ⟨1⟩

def bear : CardDef := {
  name := "Grave Bear"
  types := #[.creature]
  subtypes := #["Elf"]
  power := some 2
  toughness := some 2
}

def relic : CardDef := {
  name := "Grave Relic"
  types := #[.artifact]
}

def spark : CardDef := {
  name := "Grave Spark"
  types := #[.instant]
}

def plot : CardDef := {
  name := "Grave Plot"
  types := #[.land]
}

def putInHand (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.hand p) none {} (fun id pl => { pl with hand := pl.hand.push id })

def putInGraveyard (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.graveyard p) none {} (fun id pl =>
    { pl with graveyard := pl.graveyard.push id })

def putOnLibrary (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.library p) none {} (fun id pl =>
    { pl with library := pl.library.push id })

def namedIn (g : Game) (ids : Array ObjectId) (name : String) : ObjectId :=
  match ids.find? (fun id => (g.findObject? id).any (·.name == name)) with
  | some id => id
  | none => panic! s!"missing {name}"

def inHand (g : Game) (p : PlayerId) (name : String) : Bool :=
  (g.player p).hand.any (fun id => (g.findObject? id).any (·.name == name))

def inGraveyard (g : Game) (p : PlayerId) (name : String) : Bool :=
  (g.player p).graveyard.any (fun id => (g.findObject? id).any (·.name == name))

def onBattlefield (g : Game) (name : String) : Bool :=
  g.battlefield.any (·.name == name)

def permanentId (g : Game) (name : String) : ObjectId :=
  match g.battlefield.find? (·.name == name) with
  | some o => o.id
  | none => panic! s!"missing {name}"

def step (g : Game) (ab : TriggeredAbility) (sourceId : Option ObjectId := none)
    (targets : Array Target := #[])
    (r : Option TriggeredAbility.TriggerResolution := none) : Game :=
  g.applyTriggeredAbility caster ab sourceId targets (resolutionOverride := r)

/- A graveyard creature card returns to the controller's hand. A card that
has left the graveyard is reported and stays where it is. -/
#guard
  let g0 := putInGraveyard afterDraw bear caster
  let id := namedIn g0 (g0.player caster).graveyard "Grave Bear"
  let g := step g0 .onEnterReturnCreatureFromGyToHand none #[Target.card id]
    (some (.returnToHand .graveyardCard))
  inHand g caster "Grave Bear" && !inGraveyard g caster "Grave Bear" &&
    logContains g "Grave Bear is returned to Chandra's hand"

#guard
  let g0 := putInHand afterDraw bear caster
  let id := namedIn g0 (g0.player caster).hand "Grave Bear"
  let g := step g0 .onEnterReturnCreatureFromGyToHand none #[Target.card id]
    (some (.returnToHand .graveyardCard))
  inHand g caster "Grave Bear" &&
    logContains g "The target is no longer in the graveyard" &&
    !(logContains g "is returned")

/- The announced permanent returns to its owner's hand and the return is
noted. No target, or an illegal one, clears that note and moves nothing. -/
#guard
  let g0 := addPermanent afterDraw relic owner caster
  let id := permanentId g0 "Grave Relic"
  let src := addPermanent g0 bear caster caster
  let g := step src .onEnterReturnOtherPlusOne (some (permanentId src "Grave Bear"))
    #[Target.permanent id]
    (some (.returnToHand .permanent .owner .returnedPermanent))
  !onBattlefield g "Grave Relic" && inHand g owner "Grave Relic" &&
    !inHand g caster "Grave Relic" && g.returnedPermanentThisWay &&
    logContains g "Grave Relic is returned to Nissa's hand"

#guard
  let g0 := { addPermanent afterDraw relic caster caster with
    returnedPermanentThisWay := true }
  let g := step g0 (.onEnter Effect.enterReturnNonlandNontoken)
    (r := some (.returnToHand .permanent .owner .returnedPermanent))
  onBattlefield g "Grave Relic" && !g.returnedPermanentThisWay &&
    !(logContains g "is returned")

#guard
  let g0 := addPermanent afterDraw plot caster caster
  let id := permanentId g0 "Grave Plot"
  let g := step g0 (.onEnter Effect.enterReturnNonlandNontoken) none
    #[Target.permanent id]
    (some (.returnToHand .permanent .owner .returnedPermanent))
  onBattlefield g "Grave Plot" && !g.returnedPermanentThisWay &&
    logContains g "The target is no longer legal"

/- A graveyard permanent card returns to the controller. An instant in the
graveyard, or no target, is not returned. -/
#guard
  let g0 := putInGraveyard afterDraw relic caster
  let id := namedIn g0 (g0.player caster).graveyard "Grave Relic"
  let g := step g0 (.onEnter Effect.enterReturnGyPermanentThisTurn) none
    #[Target.card id] (some (.returnToHand .graveyardPermanent))
  inHand g caster "Grave Relic" && !inGraveyard g caster "Grave Relic" &&
    logContains g "Grave Relic is returned to Chandra's hand"

#guard
  let g0 := putInGraveyard afterDraw spark caster
  let id := namedIn g0 (g0.player caster).graveyard "Grave Spark"
  let g := step g0 (.onEnter Effect.enterReturnGyPermanentThisTurn) none
    #[Target.card id] (some (.returnToHand .graveyardPermanent))
  inGraveyard g caster "Grave Spark" && !inHand g caster "Grave Spark" &&
    logContains g "The target is no longer legal"

#guard
  let g := step afterDraw (.onEnter Effect.enterReturnGyPermanentThisTurn)
    (r := some (.returnToHand .graveyardPermanent))
  logContains g "The target is no longer legal"

/- Milled cards of the subtype are put into the controller's hand. Other
milled cards stay, and the note is cleared. -/
#guard
  let g0 := putInGraveyard (putInGraveyard afterDraw bear caster) relic caster
  let elf := namedIn g0 (g0.player caster).graveyard "Grave Bear"
  let art := namedIn g0 (g0.player caster).graveyard "Grave Relic"
  let g0 := { g0 with milledIdsThisWay := #[elf, art] }
  let g := step g0 (.onEnterMillThenSubtypeToHand 2 "Elf")
    (r := some (.returnToHand (.milledSubtype "Elf")))
  inHand g caster "Grave Bear" && inGraveyard g caster "Grave Relic" &&
    !inHand g caster "Grave Relic" && g.milledIdsThisWay.isEmpty &&
    logContains g "Grave Bear is put into Chandra's hand" &&
    !(logContains g "Grave Relic is put into")

#guard
  let g0 := putOnLibrary (putOnLibrary afterDraw relic caster) bear caster
  let g := step g0 (.onEnterMillThenSubtypeToHand 2 "Elf")
  inHand g caster "Grave Bear" && inGraveyard g caster "Grave Relic" &&
    g.milledIdsThisWay.isEmpty &&
    logContains g "Grave Bear is put into Chandra's hand"

/- The source returns from its owner's graveyard to that player's hand.
A source that has left, or no source, is reported. -/
#guard
  let g0 := putInGraveyard afterDraw relic owner
  let id := namedIn g0 (g0.player owner).graveyard "Grave Relic"
  let g := step g0 .onLandYouControlEntersPayReturnFromGy (some id)
    (r := some (.returnToHand .source .owner))
  inHand g owner "Grave Relic" && !inGraveyard g owner "Grave Relic" &&
    !inHand g caster "Grave Relic" &&
    logContains g "Grave Relic is returned to Nissa's hand"

#guard
  let g0 := addPermanent afterDraw relic caster caster
  let id := permanentId g0 "Grave Relic"
  let g := step g0 .onLandYouControlEntersPayReturnFromGy (some id)
    (r := some (.returnToHand .source .owner))
  onBattlefield g "Grave Relic" &&
    logContains g "Grave Relic is no longer in the graveyard"

#guard
  let g := step afterDraw .onLandYouControlEntersPayReturnFromGy
    (r := some (.returnToHand .source .owner))
  logContains g "The ability's source is no longer in the graveyard"

#guard TriggeredAbility.resolution (.onEnter Effect.enterReturnGyPermanentThisTurn) ==
  .returnToHand .graveyardPermanent

#guard TriggeredAbility.resolution (.onEnter Effect.enterReturnNonlandNontoken) ==
  .returnToHand .permanent .owner .returnedPermanent

#guard TriggeredAbility.toNotation (.onEnter Effect.enterReturnGyPermanentThisTurn) ==
  "When this permanent enters, choose target permanent card in your graveyard that was put there from anywhere this turn. Return it to your hand."

#guard TriggeredAbility.toNotation (.onEnter Effect.enterReturnNonlandNontoken) ==
  "When this permanent enters, return up to one target nonland, nontoken permanent to its owner's hand."

#guard TriggeredAbility.toNotation (.onEnterMillThenSubtypeToHand 4 "Elf") ==
  "When this permanent enters, mill 4 cards, then put all Elf cards from among them into your hand."

#guard TriggeredAbility.toNotation .onLandYouControlEntersPayReturnFromGy ==
  "Landfall — Whenever a land you control enters, you may pay {1}{G}{U}. If you do, return this card from your graveyard to your hand."

end Mtg.Engine.ReturnToHandTests
