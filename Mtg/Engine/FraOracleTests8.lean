import Mtg.Engine.FraCardTests3

/-!
# Engine behavior for Reality Fracture (FRA) judge rulings (part 8)

Rulings whose situation needs a card from another set. Each such card is
parsed here from its Oracle text, so the catalog stays limited to its sets:

- Meddling Mage (Alara Reborn) names a prepare spell (ruling 745).
- The Ozolith (Ikoria: Lair of Behemoths) collects Graft Surgeon's counters
  alongside its dies trigger (ruling 757).
- Ezuri, Stalker of Spheres (Phyrexia: All Will Be One) triggers when Tam,
  the Possibility proliferates choosing nothing (ruling 884).
-/

namespace Mtg.Engine.FraRulingTests8

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests
open Mtg.Engine.FraRulingTests
open Mtg.Engine.FraCardTests
open Mtg.Engine.FraCardTests2
open Mtg.Engine.FraCardTests3

def meddlingMage : CardDef :=
  fromOracleKeeping [
    "Meddling Mage",
    "{W}{U}",
    "Creature — Human Wizard",
    "2/2",
    "As Meddling Mage enters, choose a nonland card name.",
    "Spells with the chosen name can't be cast."
  ]

def theOzolith : CardDef :=
  fromOracleKeeping [
    "The Ozolith",
    "{1}",
    "Legendary Artifact",
    "Whenever a creature you control leaves the battlefield, if it had counters on it, put those counters on The Ozolith.",
    "At the beginning of combat on your turn, if The Ozolith has counters on it, you may move all counters from The Ozolith onto target creature."
  ]

def ezuriStalkerOfSpheres : CardDef :=
  fromOracleKeeping [
    "Ezuri, Stalker of Spheres",
    "{2}{G}{U}",
    "Legendary Creature — Phyrexian Elf Warrior",
    "3/3",
    "When Ezuri enters, you may pay {3}. If you do, proliferate twice.",
    "Whenever you proliferate, draw a card."
  ]

/- Each card is fully parsed. -/
#guard [meddlingMage, theOzolith, ezuriStalkerOfSpheres].all (!keepsPrintedText ·)

/-! ## Ruling 745: naming a prepare spell -/

#guard (fraRuling 745).comment.contains "alternative prepare spell's name"

/-- The opponent's Meddling Mage enters while Vigorbloom Vanguard (prepare
spell Seed Suture) and Hexhaven Dueling Arena are in the game. -/
def mageEntered : Game :=
  let g := enterPermanent afterDraw vigorbloomVanguard me
  let g := addToHand (addToHand g vigorbloomVanguard me) hexhavenDuelingArena me
  enterPermanent g meddlingMage opp

def mageNamed (name : String) : Game := mustApply mageEntered opp (.chooseName name)

def seedSutureCopy (g : Game) : GameObject :=
  (g.objects.find? (fun o => o.zone == .exile && o.name == "Seed Suture")).get!

/- The Mage's controller names a card as it enters. -/
#guard
  match mageEntered.pending with
  | .fraChoice q (.chooseCardName _) => q == opp
  | _ => false

/- The prepare spell's name may be chosen. It is judged by the prepare
spell's characteristics: Seed Suture is a sorcery, so it is a nonland name,
while the land Hexhaven Dueling Arena isn't one. -/
#guard (namedPermanent (mageNamed "Seed Suture") "Meddling Mage").status.chosenName == some "Seed Suture"
#guard (mageEntered.apply opp (.chooseName "Hexhaven Dueling Arena")).toOption.isNone
#guard (mageEntered.apply opp (.chooseName "Not A Card")).toOption.isNone

/- Naming Seed Suture stops the prepared copy from being cast, but not
Vigorbloom Vanguard itself. -/
#guard
  let g := everyColor (mageNamed "Seed Suture") me
  !g.canCast me (seedSutureCopy g) &&
    (g.apply me (.cast (seedSutureCopy g).id)).toOption.isNone &&
    g.canCast me (handObj g me "Vigorbloom Vanguard")

/- Naming the creature stops the creature spell, but the prepared copy is a
spell named Seed Suture and can still be cast. -/
#guard
  let g := everyColor (mageNamed "Vigorbloom Vanguard") me
  g.canCast me (seedSutureCopy g) && !g.canCast me (handObj g me "Vigorbloom Vanguard")

/-! ## Ruling 757: The Ozolith and Graft Surgeon -/

#guard (fraRuling 757).comment.contains "both The Ozolith and the target creature"

/-- Graft Surgeon (with the +1/+1 counter it entered with), Grizzly Bears,
and The Ozolith; Graft Surgeon then dies. -/
def surgeonDied : Game :=
  let g := enterPermanent afterDraw graftSurgeon me
  let g := addPermanent (addPermanent g grizzlyBears me me) theOzolith me me
  let surgeon := namedPermanent g "Graft Surgeon"
  settle (g.sacrificeToGraveyard surgeon "Chandra sacrifices Graft Surgeon")

#guard counters (enterPermanent afterDraw graftSurgeon me) "Graft Surgeon" == 1
#guard counters surgeonDied "The Ozolith" == 1 && counters surgeonDied "Grizzly Bears" == 1

/- A creature that leaves without counters doesn't trigger The Ozolith. -/
#guard
  let g := addPermanent (addPermanent afterDraw grizzlyBears me me) theOzolith me me
  let g := stackTriggers (g.sacrificeToGraveyard (namedPermanent g "Grizzly Bears") "sacrificed")
  g.stack.isEmpty && counters g "The Ozolith" == 0

/- At the beginning of combat on your turn, The Ozolith may move its counters
onto a target creature. -/
#guard
  let g := passBoth (skipTo surgeonDied .beginningOfCombat 80)
  let g := settle g
  counters g "The Ozolith" == 0 && counters g "Grizzly Bears" == 2

/-! ## Ruling 884: “whenever you proliferate” -/

#guard (fraRuling 884).comment.contains "even if you chose no permanents or players"

/- Tam proliferates once (one planeswalker type), choosing nothing; Ezuri
still draws a card. -/
#guard
  let g := addPermanent (addPermanent afterDraw tamThePossibility me me) ezuriStalkerOfSpheres me me
  let g := pw ajaniResolute 2 g
  let before := handSize g me
  let g := activateNamed g "Tam, the Possibility" "Proliferate"
  let g := resolveTop g
  let g := mustApply g me (.targets #[])
  let g := settle g
  handSize g me == before + 1

/- Ezuri's enters ability: pay {3} to proliferate twice, drawing twice. -/
#guard
  let g := withMana (addPermanent afterDraw grizzlyBears me me) me .green 3
  let g := plusOnes g "Grizzly Bears" 1
  let before := handSize g me
  let g := resolveTop (stackTriggers (enterPermanent g ezuriStalkerOfSpheres me))
  let g := mustApply g me .accept
  let bears := (namedPermanent g "Grizzly Bears").id
  let g := mustApply g me (.targets #[.permanent bears])
  let g := mustApply g me (.targets #[.permanent bears])
  let g := settle g
  handSize g me == before + 2 && counters g "Grizzly Bears" == 3

end Mtg.Engine.FraRulingTests8
