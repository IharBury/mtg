import Mtg.Engine.Fixture

/-!
# `TriggerResolution.chooseModes`

Alliance chooses one unused mode this turn. Gollum chooses one unused mode
for the source's lifetime. Chosen up-to-X modes resolve in printed order.
-/

namespace Mtg.Engine.ModeTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opponent : PlayerId := ⟨1⟩

def ally : CardDef :=
  creature "Test Ally" (ManaCost.ofGeneric 1) #["Elf"] 1 1

def allyOf (g : Game) : GameObject :=
  match g.battlefield.find? (·.name == "Test Ally") with
  | some o => o
  | none => panic! "missing Test Ally"

def handSize (g : Game) (p : PlayerId) : Nat :=
  (g.player p).hand.size

def modeStep (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[]) : Game :=
  g.applyTriggeredAbility caster (.onEnterDraw 1) sourceId targets
    (resolutionOverride := some r)

def withModes (modes : Array Nat) : Game :=
  let g := addPermanent afterDraw ally caster caster
  g.mapObjectStatus (allyOf g) (fun s => { s with chosenModes := modes })

def allianceModes : TriggeredAbility.TriggerResolution :=
  .chooseModes TriggeredAbility.TriggerResolution.allianceModes .oneUnusedThisTurn

def gollumModes : TriggeredAbility.TriggerResolution :=
  .chooseModes TriggeredAbility.TriggerResolution.gollumModes .oneUnused

def upToXModes : TriggeredAbility.TriggerResolution :=
  .chooseModes TriggeredAbility.TriggerResolution.upToXModes .alreadyChosen

/- The printed abilities are these three combinations. -/
#guard TriggeredAbility.resolution .onAnotherCreatureYouControlEntersAlliance ==
  allianceModes

#guard TriggeredAbility.resolution .onOpponentCastsChosenParityModes ==
  gollumModes

#guard TriggeredAbility.resolution (.onEnter Effect.enterChooseUpToXModes) ==
  upToXModes

#guard TriggeredAbility.resolutionPhrase
    { resolution := allianceModes } ==
  "choose one that hasn't been chosen this turn — • Add {G}{G}{G}. • Put a +1/+1 counter on each creature you control. • Scry 2, then draw a card"

#guard TriggeredAbility.resolutionPhrase
    { resolution := gollumModes } ==
  "choose one that hasn't been chosen — • Put a +1/+1 counter on Gollum. • Each opponent loses 2 life and you gain 2 life. • Draw a card"

#guard TriggeredAbility.resolutionPhrase
    { resolution := upToXModes } ==
  "choose up to X — • Discard a card, then draw a card. • Target opponent loses 2 life. • Destroy target token. • Each player sacrifices a creature of their choice"

#guard TriggeredAbility.resolutionPhrase
    { resolution := .chooseModes TriggeredAbility.TriggerResolution.hydeModes
        .plusOneOrRemoveCounter } ==
  "choose one — put a +1/+1 counter on this, or remove a counter from a creature you control and draw a card"

/- Alliance offers the modes still unused this turn. All three chosen
removes the ability. A missing source does the same. -/
#guard
  let g0 := addPermanent afterDraw ally caster caster
  let src := allyOf g0
  let g := modeStep g0 (allianceModes) (some src.id)
  match g.pending with
  | .fraChoice p (.allianceMode sid available) =>
    p == caster && sid == src.id && available == #[0, 1, 2]
  | _ => false

#guard
  let g0 := addPermanent afterDraw ally caster caster
  let g0 := g0.mapObjectStatus (allyOf g0) (fun s =>
    { s with allianceModesChosen := #[0, 1, 2] })
  let g := modeStep g0 (allianceModes)
    (some (allyOf g0).id)
  g.pending == .none && logContains g "all three modes have been chosen" &&
    (g.player caster).manaPool.green == 0

#guard
  let g := modeStep afterDraw (allianceModes)
  g.pending == .none && logContains g "removed from the stack with no effect"

/- Adding mana, counters on each creature, and scry-then-draw are the
three Alliance modes. The source remembers the choice. -/
#guard
  let g0 := addPermanent afterDraw ally caster caster
  let g := modeStep g0 (allianceModes)
    (some (allyOf g0).id)
  let g := mustApply g caster (.chooseMode 0)
  (g.player caster).manaPool.green == 3 &&
    (allyOf g).status.allianceModesChosen == #[0] &&
    logContains g "adds mana"

#guard
  let g0 := addPermanent (addPermanent afterDraw ally caster caster) ally caster caster
  let g := modeStep g0 (allianceModes)
    (some (allyOf g0).id)
  let g := mustApply g caster (.chooseMode 1)
  (g.battlefield.filter (·.isCreature)).all (·.status.plusOnePlusOne == 1) &&
    (allyOf g).status.allianceModesChosen == #[1]

#guard
  let g0 := addPermanent afterDraw ally caster caster
  let before := handSize g0 caster
  let g := modeStep g0 (allianceModes)
    (some (allyOf g0).id)
  let g := mustApply g caster (.chooseMode 2)
  let g := applyIdle g
  match g.pending with
  | .scry .. => false
  | _ =>
    handSize g caster == before + 1 &&
      (allyOf g).status.allianceModesChosen == #[2]

/- Gollum offers one unused mode. The choice lasts for the source's
lifetime, and spending every mode leaves the source on the battlefield. -/
#guard
  let g0 := addPermanent afterDraw ally caster caster
  let src := allyOf g0
  let g := modeStep g0 (gollumModes) (some src.id)
  match g.pending with
  | .fraChoice p (.gollumMode sid available) =>
    p == caster && sid == src.id && available == #[0, 1, 2]
  | _ => false

#guard
  let g0 := addPermanent afterDraw ally caster caster
  let g := modeStep g0 (gollumModes) (some (allyOf g0).id)
  let g := mustApply g caster (.chooseMode 0)
  (allyOf g).status.plusOnePlusOne == 1 &&
    (allyOf g).status.chosenModes == #[0]

#guard
  let g0 := addPermanent afterDraw ally caster caster
  let g := modeStep g0 (gollumModes) (some (allyOf g0).id)
  let g := mustApply g caster (.chooseMode 1)
  (g.player opponent).life == 18 && (g.player caster).life == 22 &&
    (allyOf g).status.chosenModes == #[1]

#guard
  let g0 := addPermanent afterDraw ally caster caster
  let before := handSize g0 caster
  let g := modeStep g0 (gollumModes) (some (allyOf g0).id)
  let g := mustApply g caster (.chooseMode 2)
  handSize g caster == before + 1 && (allyOf g).status.chosenModes == #[2]

#guard
  let g0 := addPermanent afterDraw ally caster caster
  let g0 := g0.mapObjectStatus (allyOf g0) (fun s =>
    { s with chosenModes := #[0, 1, 2] })
  let g := modeStep g0 (gollumModes) (some (allyOf g0).id)
  g.battlefield.any (·.name == "Test Ally") && g.pending == .none &&
    logContains g "all three modes have been chosen"

/- Chosen up-to-X modes run in printed order. Destroying the token first
means the sacrifice mode finds it already gone. -/
#guard
  let g0 := withModes #[0]
  let before := handSize g0 caster
  let g := modeStep g0 (upToXModes) (some (allyOf g0).id)
  handSize g caster == before + 1 &&
    match g.pending with
    | .chooseDiscardCard p _ => p == caster
    | _ => false

#guard
  let g0 := withModes #[1]
  let g := modeStep g0 (upToXModes) (some (allyOf g0).id)
  (g.player opponent).life == 18 && (g.player caster).life == 20

#guard
  let g0 := addPermanent afterDraw ally caster caster
  let (g0, tok) := g0.createToken caster Game.soldier11whiteToken
  let g0 := g0.mapObjectStatus (allyOf g0) (fun s => { s with chosenModes := #[2, 3] })
  let g := modeStep g0 (upToXModes) (some (allyOf g0).id)
    #[Target.permanent tok.id, Target.permanent tok.id]
  !g.battlefield.any (fun o => o.id == tok.id) &&
    logContains g "can't be sacrificed"

#guard
  let g0 := addPermanent afterDraw ally caster caster
  let (g0, tok) := g0.createToken caster Game.soldier11whiteToken
  let g := modeStep g0 (upToXModes) (some (allyOf g0).id)
    #[Target.permanent tok.id, Target.permanent tok.id]
  g.battlefield.any (fun o => o.id == tok.id) &&
    !logContains g "can't be sacrificed"

/- The named abilities resolve through the same constructor. -/
#guard
  let g0 := addPermanent afterDraw ally caster caster
  let g := g0.applyTriggeredAbility caster
    .onAnotherCreatureYouControlEntersAlliance (some (allyOf g0).id)
  match g.pending with
  | .fraChoice _ (.allianceMode _ available) => available == #[0, 1, 2]
  | _ => false

#guard
  let g0 := addPermanent afterDraw ally caster caster
  let g := g0.applyTriggeredAbility caster .onOpponentCastsChosenParityModes
    (some (allyOf g0).id)
  match g.pending with
  | .fraChoice _ (.gollumMode _ available) => available == #[0, 1, 2]
  | _ => false

#guard
  let g0 := addPermanent afterDraw ally caster caster
  let (g0, tok) := g0.createToken caster Game.soldier11whiteToken
  let g0 := g0.mapObjectStatus (allyOf g0) (fun s => { s with chosenModes := #[2, 3] })
  let g := g0.applyTriggeredAbility caster (.onEnter Effect.enterChooseUpToXModes)
    (some (allyOf g0).id) #[Target.permanent tok.id, Target.permanent tok.id]
  !g.battlefield.any (fun o => o.id == tok.id) &&
    logContains g "can't be sacrificed"

end Mtg.Engine.ModeTests
