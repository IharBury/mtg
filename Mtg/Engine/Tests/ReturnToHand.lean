import Mtg.Engine.Fixture

/-!
# Unified return-to-hand instructions (`Instruction.moveZone ... (.hand ...)`)

A graveyard creature card, a permanent to its owner's hand, a graveyard
permanent card put there this turn, milled cards of a subtype, and the source
from its owner's graveyard all execute through `Game/Interpreter.lean`.
-/

namespace Mtg.Engine.ReturnToHandTests

open Mtg.Engine
open Mtg.Engine.Tests hiding afterDraw

def afterDraw : Game := Mtg.Engine.Tests.afterDraw.change (.pushContinuationFrame {})

def caster : PlayerId := ⟨0⟩
def owner : PlayerId := ⟨1⟩

def bear : CardDef := {
  name := "Grave Bear"
  types := #[.creature]
  subtypes := #["Elf"]
  power := some (.fixed 2)
  toughness := some (.fixed 2)
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
  insertObject g card p (.hand p)

def putInGraveyard (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.graveyard p)

def putOnLibrary (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.library p)

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
    (targets : Array Target := #[]) : Game :=
  g.applyTriggeredAbility caster ab sourceId targets

/- A graveyard creature card returns to the controller's hand. A card that
has left the graveyard is not returned. -/
#guard
  let g0 := putInGraveyard afterDraw bear caster
  let id := namedIn g0 (g0.player caster).graveyard "Grave Bear"
  let g := step g0 .onEnterReturnCreatureFromGyToHand none #[Target.card id]
  inHand g caster "Grave Bear" && !inGraveyard g caster "Grave Bear"

#guard
  let g0 := putInHand afterDraw bear caster
  let id := namedIn g0 (g0.player caster).hand "Grave Bear"
  let g := step g0 .onEnterReturnCreatureFromGyToHand none #[Target.card id]
  inHand g caster "Grave Bear" && !(logContains g "is returned")

/- The announced permanent returns to its owner's hand and puts a +1/+1 counter
on the source when `onEnterReturnOtherPlusOne` resolves. -/
#guard
  let g0 := addPermanent afterDraw relic owner caster
  let id := permanentId g0 "Grave Relic"
  let src := addPermanent g0 bear caster caster
  let sid := permanentId src "Grave Bear"
  let g := step src .onEnterReturnOtherPlusOne (some sid) #[Target.permanent id]
  !onBattlefield g "Grave Relic" && inHand g owner "Grave Relic" &&
    !inHand g caster "Grave Relic" &&
    (g.object! sid).status.plusOnePlusOne == 1

#guard
  let g0 := addPermanent afterDraw relic caster caster
  let g := step g0 (.onEnter Effect.enterReturnNonlandNontoken)
  onBattlefield g "Grave Relic"

#guard
  let g0 := addPermanent afterDraw plot caster caster
  let id := permanentId g0 "Grave Plot"
  let g := step g0 (.onEnter Effect.enterReturnNonlandNontoken) none #[Target.permanent id]
  onBattlefield g "Grave Plot"

/- A graveyard permanent card returns to the controller. An instant in the
graveyard, or no target, is not returned. -/
#guard
  let g0 := putInGraveyard afterDraw relic caster
  let id := namedIn g0 (g0.player caster).graveyard "Grave Relic"
  let g := step g0 (.onEnter Effect.enterReturnGyPermanentThisTurn) none #[Target.card id]
  inHand g caster "Grave Relic" && !inGraveyard g caster "Grave Relic"

#guard
  let g0 := putInGraveyard afterDraw spark caster
  let id := namedIn g0 (g0.player caster).graveyard "Grave Spark"
  let g := step g0 (.onEnter Effect.enterReturnGyPermanentThisTurn) none #[Target.card id]
  inGraveyard g caster "Grave Spark" && !inHand g caster "Grave Spark"

#guard
  let g := step afterDraw (.onEnter Effect.enterReturnGyPermanentThisTurn)
  g.pending == .none

/- Milled cards of the subtype are put into the controller's hand. Other
milled cards stay in the graveyard. -/
#guard
  let g0 := putOnLibrary (putOnLibrary afterDraw relic caster) bear caster
  let g := step g0 (.onEnterMillThenSubtypeToHand 2 "Elf")
  inHand g caster "Grave Bear" && inGraveyard g caster "Grave Relic" &&
    !inHand g caster "Grave Relic"

/- The source returns from its owner's graveyard to that player's hand after paying. -/
#guard
  let g0 := putInGraveyard afterDraw relic owner
  let id := namedIn g0 (g0.player owner).graveyard "Grave Relic"
  let g0 := ((g0.addMana caster (.colored .green) 2).addMana caster (.colored .blue) 1)
  let offered := step g0 .onLandYouControlEntersPayReturnFromGy (some id)
  let g := mustApply offered caster .accept
  inHand g owner "Grave Relic" && !inGraveyard g owner "Grave Relic" &&
    !inHand g caster "Grave Relic"

#guard
  let g0 := addPermanent afterDraw relic caster caster
  let id := permanentId g0 "Grave Relic"
  let g0 := ((g0.addMana caster (.colored .green) 2).addMana caster (.colored .blue) 1)
  let g := step g0 .onLandYouControlEntersPayReturnFromGy (some id)
  onBattlefield g "Grave Relic"

/- Printed notations stay intact. -/
#guard TriggeredAbility.toNotation (.onEnter Effect.enterReturnGyPermanentThisTurn) ==
  "When this permanent enters, choose target permanent card in your graveyard that was put there from anywhere this turn. Return it to your hand."

#guard TriggeredAbility.toNotation (.onEnter Effect.enterReturnNonlandNontoken) ==
  "When this permanent enters, return up to one target nonland, nontoken permanent to its owner's hand."

#guard TriggeredAbility.toNotation (.onEnterMillThenSubtypeToHand 4 "Elf") ==
  "When this permanent enters, mill 4 cards, then put all Elf cards from among them into your hand."

#guard TriggeredAbility.toNotation .onLandYouControlEntersPayReturnFromGy ==
  "Whenever a land you control enters, you may pay {1}{G}{U}. If you do, return this card from your graveyard to its owner's hand."

end Mtg.Engine.ReturnToHandTests
