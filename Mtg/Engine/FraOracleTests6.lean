import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.RealityFracture
import Mtg.Engine.FraOracleTests
import Mtg.Engine.FraOracleTests2
import Mtg.Engine.FraOracleTests4
import Mtg.Engine.Tests.Abilities
import Mtg.Engine.Game
import Mtg.Engine.OracleData
import Mtg.Engine.Tests.Auras
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns

/-!
# Engine behavior for Reality Fracture (FRA) judge rulings (part 6)

Tam, the Possibility: proliferating X times (CR 701.34). Winter, Team
Player: convoke (CR 702.51) and its cast trigger.
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

/-!
## Winter, Team Player and convoke (rulings 863–869)
-/

/-- Chandra holds Winter and two red mana, and controls three Cadets that
entered this turn. -/
def winterInHand : Game :=
  let g := (emptyHand afterDraw ⟨0⟩).createKindTokens ⟨0⟩ .cadet 3
  withRedMana (addToHand g winterTeamPlayer ⟨0⟩) ⟨0⟩ 2

def winterProposed : Game :=
  mustApply winterInHand ⟨0⟩ (.cast (handCardNamed winterInHand ⟨0⟩ "Winter, Team Player").id)

def cadetIds (g : Game) : Array ObjectId :=
  (g.battlefield.filter (fun o => o.name == "Cadet")).map (·.id)

/-- Ruling 867: creatures that entered this turn can convoke. Ruling 869:
convoke pays part of the total cost; Winter's mana value is still 5. -/
def winterConvoked : Game := mustApply winterProposed ⟨0⟩ (.choosePermanents (cadetIds winterProposed))

#guard winterConvoked.battlefield.all (fun o => o.name != "Cadet" || o.status.tapped)
#guard
  match winterConvoked.proposedSpell with
  | some prop => prop.cost.manaValue == 2 && prop.cost.coloredCount .red == 1
  | none => false
#guard
  let g := passBoth (mustApply winterConvoked ⟨0⟩ .pay)
  g.battlefield.any (fun o => o.name == "Winter, Team Player") &&
    g.objectManaValue (namedPermanent g "Winter, Team Player") == 5
#guard (fraRuling 867).comment.contains "even one you haven't controlled continuously"
#guard (fraRuling 869).comment.contains "Convoke doesn't change a spell's mana cost or mana value"

/- A reversed cast untaps the convoking creatures (CR 733.1). -/
#guard
  let g := { winterConvoked with
    proposedSpell := winterConvoked.proposedSpell.map (fun p =>
      { p with cost := p.cost.addGeneric 9 }) }
  let g := mustApply g ⟨0⟩ .pay
  g.battlefield.all (fun o => o.name != "Cadet" || !o.status.tapped)

/-- Ruling 865: a multicolored creature pays {1} or one mana of its colors. -/
def testRedGreenBear : CardDef :=
  creature "Test Gruul Bear" (ManaCost.ofColors [.red, .green]) #["Bear"] 2 2

#guard
  let g := addPermanent winterInHand testRedGreenBear ⟨0⟩ ⟨0⟩
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Winter, Team Player").id)
  let g := mustApply g ⟨0⟩ (.choosePermanents #[(namedPermanent g "Test Gruul Bear").id])
  match g.proposedSpell with
  | some prop => prop.cost.coloredCount .red == 0 && prop.cost.manaValue == 4
  | none => false
#guard (fraRuling 865).comment.contains "one mana of your choice of any of that creature's colors"

/- Ruling 863: a creature tapped for mana can't also convoke. -/
#guard
  let g := addPermanent winterInHand llanowarElves ⟨0⟩ ⟨0⟩
  let elves := namedPermanent g "Llanowar Elves"
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Winter, Team Player").id)
  let g := mustApply g ⟨0⟩ (.tapForMana elves.id (.colored .green))
  rejects g ⟨0⟩ (.choosePermanents #[elves.id]) "already tapped"
#guard (fraRuling 863).comment.contains "You won't be able to tap it again for convoke"

/- Ruling 864: convoke works with an alternative cost. A Bestial Incursion
with convoke cast with flashback has its {5}{G} paid by convoke. -/
#guard
  let card := { bestialIncursion with keywords := Keyword.convoke }
  let g := addToGraveyard ((emptyHand afterDraw ⟨0⟩).createKindTokens ⟨0⟩ .cadet 5) card ⟨0⟩
  let g := withGreenMana g ⟨0⟩ 1
  let g := mustApply g ⟨0⟩ (.cast (graveyardCard g ⟨0⟩ "Bestial Incursion").id)
  let g := mustApply g ⟨0⟩ (.choosePermanents (cadetIds g))
  match g.proposedSpell with
  | some prop => prop.cost.manaValue == 1 && prop.cost.coloredCount .green == 1
  | none => false
#guard (fraRuling 864).comment.contains "it can be used in conjunction with alternative costs"

/- Ruling 866: an attacking creature tapped to convoke stays attacking.
Blossom-Blessed Angel has vigilance, so it is untapped while attacking. -/
#guard
  let shockConvoke := { shock with manaCost := ManaCost.ofGeneric 1, keywords := Keyword.convoke }
  let g := addPermanent (emptyHand afterDraw ⟨0⟩) blossomBlessedAngel ⟨0⟩ ⟨0⟩
  let g := addToHand g shockConvoke ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Blossom-Blessed Angel").id])
  let g := proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Shock").id (.player ⟨1⟩)
  let g := mustApply g ⟨0⟩ (.choosePermanents #[(namedPermanent g "Blossom-Blessed Angel").id])
  let g := mustApply g ⟨0⟩ .pay
  let angel := namedPermanent g "Blossom-Blessed Angel"
  angel.status.tapped && angel.status.attacking
#guard (fraRuling 866).comment.contains "won't cause that creature to stop attacking or blocking"

/- Ruling 868: Winter's trigger resolves before the spell. -/
#guard
  let g := castShockAtNissa (addPermanent afterDraw winterTeamPlayer ⟨0⟩ ⟨0⟩)
  let g := passBoth g
  topOfStack g == "Shock" &&
    g.power (namedPermanent g "Winter, Team Player") == 4
#guard (fraRuling 868).comment.contains "resolves before the spell that caused it to trigger"

end Mtg.Engine.FraRulingTests
