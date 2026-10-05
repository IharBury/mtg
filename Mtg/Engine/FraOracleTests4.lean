import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.RealityFracture
import Mtg.Engine.FraOracleTests
import Mtg.Engine.FraOracleTests2
import Mtg.Engine.Game
import Mtg.Engine.OracleData
import Mtg.Engine.Tests.Abilities
import Mtg.Engine.Tests.Auras
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns

/-!
# Engine behavior for Reality Fracture (FRA) judge rulings (part 4)

Loyalty-activation triggers (Way of the Mind Sculptor, Ajani Unrelenting),
cast triggers (Plan for All Outcomes, Vraska, Soul of Stone, Danitha),
Draconic Visitor, Lyra, Tetsuko, Koth, and Hall of Echoes.
-/

namespace Mtg.Engine.FraRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

/-- The top stack object's name, if any. -/
def topOfStack (g : Game) : String :=
  match g.stack.back? with
  | some e => (g.object! e.objectId).name
  | none => ""

/-- Cast Shock at Nissa from Chandra's hand and stop after paying. -/
def castShockAtNissa (g : Game) : Game :=
  let g := withRedMana (addToHand g shock ⟨0⟩) ⟨0⟩ 1
  let g := proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Shock").id (.player ⟨1⟩)
  mustApply g ⟨0⟩ .pay

/-!
## Loyalty-activation triggers (rulings 847 / 853)
-/

/-- Ruling 847: removing two or more loyalty counters triggers Way of the
Mind Sculptor, and its draw resolves before the loyalty ability. -/
def mindSculptorMinusThree : Game :=
  let g := addPermanent (afterDraw.empowerJace ⟨0⟩ 5) wayOfTheMindSculptor ⟨0⟩ ⟨0⟩
  mustApply g ⟨0⟩ (.activate (jaceTokenOf g).id 1)

#guard mindSculptorMinusThree.stack.size == 2
#guard mentions (topOfStack mindSculptorMinusThree) "Way of the Mind Sculptor"
#guard
  let hand := (mindSculptorMinusThree.player ⟨0⟩).hand.size
  let g := passBoth mindSculptorMinusThree
  (g.player ⟨0⟩).hand.size == hand + 1 && g.stack.size == 1
#guard (fraRuling 847).comment.contains "draw the card before the loyalty ability"

/- Removing one counter doesn't trigger it (intervening “if”). -/
#guard
  let g := addPermanent (afterDraw.empowerJace ⟨0⟩ 5) wayOfTheMindSculptor ⟨0⟩ ⟨0⟩
  let g := mustApply g ⟨0⟩ (.activate (jaceTokenOf g).id 0)
  g.stack.size == 1

/-- Ruling 853: Ajani Unrelenting's Cadet enters before his +1 resolves, so
the Cadet gets +1/+0 and haste. -/
def ajaniPlusOne : Game :=
  let g := enterPermanent afterDraw ajaniUnrelenting ⟨0⟩
  let ajani := namedPermanent g "Ajani Unrelenting"
  resolveStack (mustApply g ⟨0⟩ (.activate ajani.id 0)) 20

#guard (namedPermanent ajaniPlusOne "Ajani Unrelenting").status.loyaltyCounters == 6
#guard
  let cadet := namedPermanent ajaniPlusOne "Cadet"
  ajaniPlusOne.power cadet == 3 && ajaniPlusOne.hasHaste cadet
#guard (fraRuling 853).comment.contains "will get +1/+0 and gain haste"

/-!
## Draconic Visitor (rulings 780–782)
-/

def withVisitor : Game := addPermanent afterDraw draconicVisitor ⟨0⟩ ⟨0⟩

/-- Ruling 780: a Treasure is replaced by a 5/5 red Dragon with flying. It
has none of the Treasure's abilities, but “tapped” still applies. -/
def visitorTreasure : Game := withVisitor.createTreasureTokens ⟨0⟩ 1 (tapped := true)

#guard !visitorTreasure.battlefield.any (fun o => o.name == "Treasure")
#guard
  let d := namedPermanent visitorTreasure "Dragon"
  d.printed.isToken && d.status.tapped && visitorTreasure.power d == 5 &&
    visitorTreasure.hasFlying d && d.printed.colors == ColorSet.singleton .red &&
    !d.printed.tapSacrificeAddAnyColor && !d.printed.isArtifact
#guard (fraRuling 780).comment.contains "entirely replaced by 5/5 red Dragon"

/- Ruling 781: only tokens created under your control are replaced. -/
#guard
  let g := withVisitor.createTreasureTokens ⟨1⟩ 1
  g.battlefield.any (fun o => o.name == "Treasure" && o.controlledBy ⟨1⟩)
#guard (fraRuling 781).comment.contains "under whose control a token would be created"

/- Ruling 782: the token's own characteristics as created decide; a Cadet
isn't an artifact token, so it isn't replaced. -/
#guard
  let g := withVisitor.createKindTokens ⟨0⟩ .cadet 1
  g.battlefield.any (fun o => o.name == "Cadet")
#guard (fraRuling 782).comment.contains "Draconic Visitor's effect doesn't apply"

/-!
## Cast triggers (rulings 767 / 768 / 848 / 849 / 887)
-/

/-- Ruling 768: Plan for All Outcomes triggers on the first noncreature
spell and resolves before it. -/
def planShock : Game := castShockAtNissa (addPermanent afterDraw planForAllOutcomes ⟨0⟩ ⟨0⟩)

#guard planShock.stack.size == 2
#guard mentions (topOfStack planShock) "Plan for All Outcomes"
#guard
  let g := passBoth planShock
  (g.jacePlaneswalkerTokens ⟨0⟩).size == 1 && topOfStack g == "Shock"
#guard (fraRuling 768).comment.contains "resolves before the spell that caused it to trigger"

/-- Ruling 767: casting Plan itself is the first noncreature spell, so a
second one that turn doesn't trigger it. -/
def planCastThenShock : Game :=
  let g := withBlueMana (addToHand afterDraw planForAllOutcomes ⟨0⟩) ⟨0⟩ 4
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Plan for All Outcomes").id)
  let g := resolveStack (mustApply g ⟨0⟩ .pay) 20
  castShockAtNissa g

#guard planCastThenShock.battlefield.any (fun o => o.name == "Plan for All Outcomes")
#guard planCastThenShock.stack.size == 1
#guard (fraRuling 767).comment.contains "its second ability won't trigger"

/-- Ruling 887: Vraska, Soul of Stone's Sculpture is created before the spell
resolves. The Sculpture is a 1/1 artifact creature with a Treasure's mana
ability. -/
def vraskaShock : Game := castShockAtNissa (addPermanent afterDraw vraskaSoulOfStone ⟨0⟩ ⟨0⟩)

#guard vraskaShock.stack.size == 2
#guard
  let g := passBoth vraskaShock
  topOfStack g == "Shock" &&
    (let s := namedPermanent g "Sculpture"
     s.printed.isArtifact && s.isCreature && s.printed.tapSacrificeAddAnyColor &&
       g.hasSubtype s "Treasure")
#guard (fraRuling 887).comment.contains "resolves before the spell that caused it to trigger"

/-- Ruling 848: Danitha's counter arrives before the spell resolves. -/
def danithaShock : Game := castShockAtNissa (addPermanent afterDraw danithaSpearOfAgony ⟨0⟩ ⟨0⟩)

#guard danithaShock.stack.size == 2
#guard
  let g := passBoth danithaShock
  (namedPermanent g "Danitha, Spear of Agony").status.plusOnePlusOne == 1 && topOfStack g == "Shock"
#guard (fraRuling 848).comment.contains "resolves before the spell that caused it to trigger"

/- Ruling 849: one trigger per spell, however many targets. A spell that
targets Nissa and her creature triggers Danitha once. -/
#guard
  let g := addPermanent afterDraw danithaSpearOfAgony ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let (g, spell) := g.allocObject lightningBolt ⟨0⟩ .stack (some ⟨0⟩)
  let g := g.putStackEntry ⟨0⟩ spell.id
  let g := g.setStackEntryTargets spell.id
    #[.player ⟨1⟩, .permanent (namedPermanent g "Grizzly Bears").id]
  let g := g.putCastTriggersOnStack ⟨0⟩ (g.object! spell.id)
  (g.waitingTriggers.filter (fun w => w.source.name == "Danitha, Spear of Agony")).size == 1
#guard (fraRuling 849).comment.contains "triggers only once per spell"

/-!
## Lyra, Archangel of Dawn (rulings 831 / 832)
-/

/-- Ruling 832: two lifelink creatures dealing combat damage trigger Lyra
twice; each puts a +1/+1 counter on each Angel you control. -/
def lyraTwoLifelinkers : Game :=
  let g := addPermanent afterDraw lyraArchangelOfDawn ⟨0⟩ ⟨0⟩
  let g := addPermanent g blossomBlessedAngel ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := withLifelink (withLifelink g "Grizzly Bears") "Gray Ogre"
  resolveStack (attackWith g #["Grizzly Bears", "Gray Ogre"]) 20

#guard (namedPermanent lyraTwoLifelinkers "Lyra, Archangel of Dawn").status.plusOnePlusOne == 2
#guard (namedPermanent lyraTwoLifelinkers "Blossom-Blessed Angel").status.plusOnePlusOne == 2
#guard (namedPermanent lyraTwoLifelinkers "Grizzly Bears").status.plusOnePlusOne == 0
#guard (fraRuling 832).comment.contains "Lyra's last ability will trigger once for each"

/-- A 2/1 Angel without flying, so Grizzly Bears can block it. -/
def testAngel : CardDef := creature "Test Angel" ManaCost.empty #["Angel"] 2 1

/- Ruling 831: an Angel dealt lethal damage as you gain life dies before its
counter arrives. -/
#guard
  let g := addPermanent afterDraw lyraArchangelOfDawn ⟨0⟩ ⟨0⟩
  let g := addPermanent g testAngel ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := withLifelink g "Test Angel"
  let g := attackWith g #["Test Angel"] #[("Grizzly Bears", "Test Angel")]
  let g := resolveStack g 20
  !g.battlefield.any (fun o => o.name == "Test Angel") &&
    (namedPermanent g "Lyra, Archangel of Dawn").status.plusOnePlusOne == 1
#guard (fraRuling 831).comment.contains "it won't receive a counter from Lyra's ability in time"

/-!
## Tetsuko Umezawa, Fugitive (ruling 842)
-/

/-- Creatures you control with power or toughness 1 or less can't be
blocked. Ruling 842: once Grizzly Bears is blocked, lowering its power to 1
doesn't make it unblocked. -/
def tetsukoBoard : Game :=
  let g := addPermanent afterDraw tetsukoUmezawaFugitive ⟨0⟩ ⟨0⟩
  addPermanent (addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩) grayOgre ⟨1⟩ ⟨1⟩

#guard tetsukoBoard.hasCantBeBlocked (namedPermanent tetsukoBoard "Tetsuko Umezawa, Fugitive")
#guard !tetsukoBoard.hasCantBeBlocked (namedPermanent tetsukoBoard "Grizzly Bears")
#guard !tetsukoBoard.hasCantBeBlocked (namedPermanent tetsukoBoard "Gray Ogre")
#guard
  let g := passBoth (skipTo tetsukoBoard .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[((namedPermanent g "Gray Ogre").id,
    (namedPermanent g "Grizzly Bears").id)])
  let g := g.mapObjectStatus (namedPermanent g "Grizzly Bears") (fun s => s.addPump (-1) 0)
  (namedPermanent g "Grizzly Bears").status.blocked
#guard (fraRuling 842).comment.contains "won't cause it to become unblocked"

/-!
## Koth of the Homestead (ruling 830)
-/

/- A Plains entering triggers both of Koth's abilities, and Koth's controller
orders them. -/
#guard
  let g := addPermanent afterDraw kothOfTheHomestead ⟨0⟩ ⟨0⟩
  let g := playLandNamed g plains
  g.pending == .chooseTriggerToStack ⟨0⟩ || g.stack.size == 2
#guard
  let g := addPermanent afterDraw kothOfTheHomestead ⟨0⟩ ⟨0⟩
  let g := playLandNamed g plains
  let g := resolveStack g 30
  (g.player ⟨0⟩).life == 21 &&
    (namedPermanent g "Koth of the Homestead").status.plusOnePlusOne == 1
#guard (fraRuling 830).comment.contains "both of Koth's abilities will trigger"

/-!
## Hall of Echoes (rulings 810–817)
-/

/-- Activate Hall of Echoes targeting `target` and resolve it. -/
def hallCopies (g : Game) (target : String) : Game :=
  let g := addPermanent g hallOfEchoes ⟨0⟩ ⟨0⟩
  let g := withMana g ⟨0⟩ .green 5
  let g := mustApply g ⟨0⟩ (.activate (namedPermanent g "Hall of Echoes").id 0)
  let g := mustApply g ⟨0⟩ (.target (.permanent (namedPermanent g target).id))
  resolveStack (mustApply g ⟨0⟩ .pay) 20

/-- Lyra with two +1/+1 counters, tapped. -/
def lyraWithCounters : Game :=
  let g := addPermanent afterDraw lyraArchangelOfDawn ⟨0⟩ ⟨0⟩
  g.mapObjectStatus (namedPermanent g "Lyra, Archangel of Dawn") (fun s =>
    { s.addPlusOnePlusOne 2 with tapped := true })

def hallAsLyra : Game := hallCopies lyraWithCounters "Lyra, Archangel of Dawn"

/- Rulings 811 / 813: Hall of Echoes becomes a copy of a legendary creature,
and the legend rule doesn't apply this turn, so both stay. -/
#guard (hallAsLyra.battlefield.filter (fun o => o.name == "Lyra, Archangel of Dawn")).size == 2
#guard hallAsLyra.checkSBA.pending == .none
#guard (fraRuling 811).comment.contains "both permanents will remain on the battlefield"
#guard (fraRuling 813).comment.contains "none of them will be put into the graveyard"

/- Ruling 816: the copy doesn't copy counters or tapped status. -/
#guard
  let copy := (hallAsLyra.battlefield.filter (fun o =>
    o.name == "Lyra, Archangel of Dawn" && o.copyRestore.isSome))[0]!
  copy.status.plusOnePlusOne == 0 && !copy.status.tapped && copy.isCreature
#guard (fraRuling 816).comment.contains "It doesn't copy whether that creature is tapped"

/- Ruling 812: becoming a copy isn't entering, so Mindseeker Oculus's
enters ability doesn't trigger. -/
#guard
  let g := hallCopies (addPermanent afterDraw mindseekerOculus ⟨0⟩ ⟨0⟩) "Mindseeker Oculus"
  (g.battlefield.filter (fun o => o.name == "Mindseeker Oculus")).size == 2 &&
    (g.jacePlaneswalkerTokens ⟨0⟩).isEmpty
#guard (fraRuling 812).comment.contains "isn't entering the battlefield"

/- Ruling 815: copying a token copy of Lyra makes Hall of Echoes a Lyra. -/
#guard
  let (g, _) := afterDraw.createToken ⟨0⟩
    { lyraArchangelOfDawn with name := "Lyra, Archangel of Dawn" }
  let g := hallCopies g "Lyra, Archangel of Dawn"
  (g.battlefield.filter (fun o => o.name == "Lyra, Archangel of Dawn")).size == 2
#guard (fraRuling 815).comment.contains "becomes a copy of whatever that creature copied"

/-- Rulings 814 / 817: in cleanup the copy ends and the legend rule applies
again at the same time. A second real Lyra that entered this turn must then
go, and Hall of Echoes is a land again. -/
def hallTwoLyrasAfterCleanup : Game :=
  let g := addPermanent hallAsLyra lyraArchangelOfDawn ⟨0⟩ ⟨0⟩
  passBoth (skipTo g .end 80)

#guard hallTwoLyrasAfterCleanup.battlefield.any (fun o =>
  o.name == "Hall of Echoes" && o.printed.isLand && !o.isCreature)
#guard
  let g := skipTo hallTwoLyrasAfterCleanup .upkeep 80
  (g.battlefield.filter (fun o => o.name == "Lyra, Archangel of Dawn")).size == 1
#guard (fraRuling 814).comment.contains "begins applying again"
#guard (fraRuling 817).comment.contains "wear off at exactly the same time"

/- Ruling 810: the legend rule is a state-based action that uses no stack. -/
#guard
  let g := addPermanent (addPermanent afterDraw lyraArchangelOfDawn ⟨0⟩ ⟨0⟩)
    lyraArchangelOfDawn ⟨0⟩ ⟨0⟩
  let g := g.checkSBA
  g.stack.isEmpty && match g.pending with
    | .chooseLegend .. => true
    | _ => false
#guard (fraRuling 810).comment.contains "doesn't use the stack"

end Mtg.Engine.FraRulingTests
