import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.RealityFracture
import Mtg.Engine.FraOracleTests
import Mtg.Engine.FraOracleTests2
import Mtg.Engine.Game
import Mtg.Engine.OracleData
import Mtg.Engine.Tests.Auras
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns

/-!
# Engine behavior for Reality Fracture (FRA) judge rulings (part 6)

Tam, the Possibility: proliferating X times (CR 701.34).
-/

namespace Mtg.Engine.FraRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

/-- Chandra controls Tam, a Jace token, and Ajani Resolute (two planeswalker
types). Nissa controls Grizzly Bears with a +1/+1 counter and a shield
counter, and has one poison counter. -/
def tamBoard : Game :=
  let g := addPermanent (afterDraw.empowerJace ⟨0⟩ 2) tamThePossibility ⟨0⟩ ⟨0⟩
  let g := enterPermanent g ajaniResolute ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := g.mapObjectStatus (namedPermanent g "Grizzly Bears") (fun s =>
    { s.addPlusOnePlusOne 1 with shield := 1 })
  let g := g.modifyPlayer ⟨1⟩ (fun pl => { pl with poison := 1 })
  [Color.white, .blue, .black, .red, .green].foldl (fun g c => withMana g ⟨0⟩ c 1) g

def tamActivated : Game :=
  let g := mustApply tamBoard ⟨0⟩ (.activate (namedPermanent tamBoard "Tam, the Possibility").id 0)
  mustApply g ⟨0⟩ .pay

/- Ruling 883: players may respond while the ability is on the stack. -/
#guard tamActivated.stack.size == 1
#guard (mustApply tamActivated ⟨0⟩ .pass).hasPriority ⟨1⟩
#guard (fraRuling 883).comment.contains "Players can respond to a spell or ability"

/-- Ruling 878: X is determined as the ability resolves: two types. -/
def tamResolving : Game := passBoth tamActivated

#guard tamResolving.pending == .chooseProliferate ⟨0⟩ 2
#guard (fraRuling 878).comment.contains "determined only once"

/- Ruling 880: no player can act between proliferations. -/
#guard !tamResolving.hasPriority ⟨0⟩ && !tamResolving.hasPriority ⟨1⟩
#guard (fraRuling 880).comment.contains "players can't respond between proliferating"

/-- Ruling 881: an opponent's permanent and an opponent can be chosen.
Ruling 879: each kind of counter already there gets another. -/
def tamFirst : Game :=
  mustApply tamResolving ⟨0⟩ (.targets #[
    .permanent (namedPermanent tamResolving "Grizzly Bears").id,
    .permanent (jaceTokenOf tamResolving).id,
    .player ⟨1⟩])

#guard (namedPermanent tamFirst "Grizzly Bears").status.plusOnePlusOne == 2
#guard (namedPermanent tamFirst "Grizzly Bears").status.shield == 2
#guard (jaceTokenOf tamFirst).status.loyaltyCounters == 3
#guard (tamFirst.player ⟨1⟩).poison == 2
#guard tamFirst.pending == .chooseProliferate ⟨0⟩ 1
#guard (fraRuling 879).comment.contains "it must get one of each kind of counter it already has"
#guard (fraRuling 881).comment.contains "including ones controlled by opponents"

/- Ruling 881: cards in other zones, and permanents without counters,
can't be chosen. -/
#guard
  let g := addToGraveyard tamFirst grizzlyBears ⟨0⟩
  let card := graveyardCard g ⟨0⟩ "Grizzly Bears"
  !(g.apply ⟨0⟩ (.targets #[.permanent card.id])).isOk &&
    !(g.apply ⟨0⟩ (.targets #[.card card.id])).isOk
#guard !(tamFirst.apply ⟨0⟩
  (.targets #[.permanent (namedPermanent tamFirst "Tam, the Possibility").id])).isOk
#guard (fraRuling 881).comment.contains "You can't choose cards in any zone other than the battlefield"

/-- Ruling 878: X stays 2 even if a planeswalker leaves before the second
proliferation. Rulings 882 / 886: the second time may choose nothing. -/
def tamSecond : Game :=
  let ajani := namedPermanent tamFirst "Ajani Resolute"
  let (g, _) := tamFirst.move ajani.id (.graveyard ⟨0⟩) none
  mustApply g ⟨0⟩ (.targets #[])

#guard tamSecond.pending == .none
#guard (namedPermanent tamSecond "Grizzly Bears").status.plusOnePlusOne == 2
#guard (jaceTokenOf tamSecond).status.loyaltyCounters == 3
#guard (fraRuling 882).comment.contains "you don't have to choose any permanents at all"
#guard (fraRuling 886).comment.contains "you don't have to choose the same set"

end Mtg.Engine.FraRulingTests
