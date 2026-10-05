import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.RealityFracture
import Mtg.Engine.FraOracleTests
import Mtg.Engine.Game
import Mtg.Engine.OracleData
import Mtg.Engine.Tests.Abilities
import Mtg.Engine.Tests.Auras
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns

/-!
# Engine behavior for Reality Fracture (FRA) judge rulings (part 2)

Card-specific FRA rulings: flashback, `{X}` in mana value, life gain
triggers, Break Under Pressure, Multiply by Zero, Violent Echoes, Heartwood,
Tarmogoyf, the Commons and slow lands, Ghalta, Samut's split second, and
Karn, Argent Defender.
-/

namespace Mtg.Engine.FraRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

/-- The object named `name` in `p`'s graveyard. -/
def graveyardCard (g : Game) (p : PlayerId) (name : String) : GameObject :=
  match (g.player p).graveyard.find? (fun id => (g.object! id).name == name) with
  | some id => g.object! id
  | none => panic! s!"expected {name} in the graveyard"

/-- Pass priority until the stack is empty, resolving each object. -/
def resolveStack (g : Game) : Nat → Game
  | 0 => g
  | n + 1 => if g.stack.isEmpty && g.pending == .none then g else resolveStack (applyIdle g) n

/-!
## Flashback (rulings 32, 33, 37, 752–754)
-/

/-- Ruling 754: a flashback card put into the graveyard without being cast
(here milled) can still be cast with flashback. Ruling 33: in your main
phase you have priority, so you can cast it before anyone else acts. -/
def incursionInGraveyard : Game :=
  withGreenMana (addToGraveyard afterDraw bestialIncursion ⟨0⟩) ⟨0⟩ 6

#guard incursionInGraveyard.hasPriority ⟨0⟩
#guard incursionInGraveyard.canCast ⟨0⟩ (graveyardCard incursionInGraveyard ⟨0⟩ "Bestial Incursion")
#guard (fraRuling 754).comment.contains "without having been cast"
#guard (fraRuling 33).comment.contains "before any other player can take any actions"

/- Rulings 752 / 753: the flashback cost replaces the mana cost; the mana
value is still that of the mana cost. -/
#guard
  let card := graveyardCard incursionInGraveyard ⟨0⟩ "Bestial Incursion"
  incursionInGraveyard.playManaCost card card.printed == bestialIncursion.flashback.get! &&
    incursionInGraveyard.objectManaValue card == 4
#guard (fraRuling 753).comment.contains "mana value of the spell is determined only by its mana cost"

/-- Rulings 32 / 752: a spell cast with flashback is exiled as it leaves the
stack. Bestial Incursion creates a 4/4 green Beast with trample. -/
def incursionFlashedBack : Game :=
  let g := incursionInGraveyard
  let g := mustApply g ⟨0⟩ (.cast (graveyardCard g ⟨0⟩ "Bestial Incursion").id)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard incursionFlashedBack.objects.any (fun o => o.zone == .exile && o.name == "Bestial Incursion")
#guard !(incursionFlashedBack.player ⟨0⟩).graveyard.any (fun id =>
  (incursionFlashedBack.object! id).name == "Bestial Incursion")
#guard
  let beast := namedPermanent incursionFlashedBack "Beast"
  beast.printed.isToken && incursionFlashedBack.power beast == 4 &&
    incursionFlashedBack.hasTrample beast && beast.printed.colors == ColorSet.singleton .green
#guard (fraRuling 32).comment.contains "will always be exiled afterward"
#guard (fraRuling 752).comment.contains "exile this card instead of putting it anywhere else"

/- Ruling 37: flashback follows the card's timing; a sorcery can't be cast
at the beginning of combat. -/
#guard
  let g := skipTo incursionInGraveyard .beginningOfCombat 80
  !g.canCast ⟨0⟩ (graveyardCard g ⟨0⟩ "Bestial Incursion")
#guard (fraRuling 37).comment.contains "you can cast a sorcery using flashback only when"

/-!
## `{X}` in mana value (rulings 751, 763, 765, 777, 807)
-/

/- Off the stack, `{X}` is 0 (CR 107.3g): Guiding Hydra's mana value is 1 in
the graveyard and on the battlefield. -/
#guard
  let g := addToGraveyard afterDraw guidingHydra ⟨0⟩
  g.objectManaValue (graveyardCard g ⟨0⟩ "Guiding Hydra") == 1
#guard
  let g := addPermanent afterDraw guidingHydra ⟨0⟩ ⟨0⟩
  g.objectManaValue (namedPermanent g "Guiding Hydra") == 1
#guard [751, 763, 765, 777, 807].all (fun i => (fraRuling i).comment.contains "X")

/-!
## Life gain triggers (rulings 761 / 762 / 876 / 877)
-/

/-- Grant lifelink until end of turn so the creature's combat damage gains life. -/
def withLifelink (g : Game) (name : String) : Game :=
  let o := namedPermanent g name
  g.mapObjectStatus o (fun s => s.grantUntilEot Keyword.lifelink)

/-- Attack with every creature named in `names` and let combat damage happen,
optionally blocked by `blockers` (blocker name, attacker name). -/
def attackWith (g : Game) (names : Array String)
    (blockers : Array (String × String) := #[]) : Game :=
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers (names.map (fun n => (namedPermanent g n).id)))
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers (blockers.map (fun (b, a) =>
    ((namedPermanent g b).id, (namedPermanent g a).id))))
  passBoth g

/-- Ruling 761: two creatures with lifelink dealing combat damage at once are
two life-gain events, so Unflinching Hortimancer triggers twice. -/
def hortimancerTwoLifelinkers : Game :=
  let g := addPermanent afterDraw unflinchingHortimancer ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := withLifelink (withLifelink g "Grizzly Bears") "Gray Ogre"
  attackWith g #["Grizzly Bears", "Gray Ogre"]

#guard (hortimancerTwoLifelinkers.player ⟨0⟩).life == 24
#guard
  let g := resolveStack hortimancerTwoLifelinkers 20
  (namedPermanent g "Unflinching Hortimancer").status.plusOnePlusOne == 2
#guard (fraRuling 761).comment.contains "trigger once for each of those creatures"

/-- Ruling 762: if Hortimancer is dealt lethal damage as you gain life, it
dies before its counter arrives. -/
def hortimancerTradesWithBears : Game :=
  let g := addPermanent afterDraw unflinchingHortimancer ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := withLifelink g "Unflinching Hortimancer"
  attackWith g #["Unflinching Hortimancer"] #[("Grizzly Bears", "Unflinching Hortimancer")]

#guard (hortimancerTradesWithBears.player ⟨0⟩).life == 22
#guard !hortimancerTradesWithBears.battlefield.any (fun o => o.name == "Unflinching Hortimancer")
#guard (fraRuling 762).comment.contains "won't receive a counter from its ability in time"

/-- Rulings 876 / 877: Titanbones triggers once per lifelink creature and
puts two +1/+1 counters on itself each time. -/
def titanbonesTwoLifelinkers : Game :=
  let g := addPermanent afterDraw titanbonesToweringHeart ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := withLifelink (withLifelink g "Grizzly Bears") "Gray Ogre"
  resolveStack (attackWith g #["Grizzly Bears", "Gray Ogre"]) 20

#guard (namedPermanent titanbonesTwoLifelinkers "Titanbones, Towering Heart").status.plusOnePlusOne == 4
#guard (fraRuling 877).comment.contains "trigger once for each of those creatures"

def titanbonesTradesWithWurm : Game :=
  let g := addPermanent afterDraw titanbonesToweringHeart ⟨0⟩ ⟨0⟩
  let g := addPermanent g crawWurm ⟨1⟩ ⟨1⟩
  let g := withLifelink g "Titanbones, Towering Heart"
  attackWith g #["Titanbones, Towering Heart"] #[("Craw Wurm", "Titanbones, Towering Heart")]

#guard !titanbonesTradesWithWurm.battlefield.any (fun o => o.name == "Titanbones, Towering Heart")
#guard (fraRuling 876).comment.contains "won't receive a counter from his ability in time"

/-!
## Germinate Recruits (ruling 755)
-/

/-- Germinate Recruits counts life gained this turn, ignoring life lost: gain
3 and lose 3, and three Cadets are created. -/
def recruitsResolved : Game :=
  let g := (afterDraw.gainLife ⟨0⟩ 3).loseLife ⟨0⟩ 3
  let g := withWhiteMana (addToHand g germinateRecruits ⟨0⟩) ⟨0⟩ 3
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Germinate Recruits").id)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard (recruitsResolved.player ⟨0⟩).life == 20
#guard (recruitsResolved.battlefield.filter (fun o => o.name == "Cadet")).size == 3
#guard (fraRuling 755).comment.contains "without taking into account any life you lost"

/-!
## Break Under Pressure (rulings 771–773)
-/

/-- Cast Break Under Pressure on Nissa after setting up her board. -/
def breakUnderPressureOn (g : Game) : Game :=
  let g := withBlackMana (addToHand g breakUnderPressure ⟨0⟩) ⟨0⟩ 3
  let g := proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Break Under Pressure").id (.player ⟨1⟩)
  passBoth (mustApply g ⟨0⟩ .pay)

/-- Ruling 771: creatures and planeswalkers form one group. Nissa controls
Grizzly Bears (mana value 2) and Jace, Reality Sculptor (5); she sacrifices
Jace. You gain 2 life. -/
def breakJaceAndBears : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  breakUnderPressureOn (enterPermanent g jaceRealitySculptor ⟨1⟩)

#guard !breakJaceAndBears.battlefield.any (fun o => o.name == "Jace, Reality Sculptor")
#guard breakJaceAndBears.battlefield.any (fun o => o.name == "Grizzly Bears")
#guard (breakJaceAndBears.player ⟨0⟩).life == 22
#guard (fraRuling 771).comment.contains "as one group"

/-- Ruling 773: only the player is targeted, so a hexproof creature with the
greatest mana value is sacrificed. Ruling 772: the choice is made as the
spell resolves, after the hexproof Craw Wurm entered. -/
def breakHexproofWurm : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := withBlackMana (addToHand g breakUnderPressure ⟨0⟩) ⟨0⟩ 3
  let g := proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Break Under Pressure").id (.player ⟨1⟩)
  let g := mustApply g ⟨0⟩ .pay
  let g := addPermanent g crawWurm ⟨1⟩ ⟨1⟩
  let g := g.mapObjectStatus (namedPermanent g "Craw Wurm") (fun s =>
    s.grantUntilEot Keyword.hexproof)
  passBoth g

#guard !breakHexproofWurm.battlefield.any (fun o => o.name == "Craw Wurm")
#guard breakHexproofWurm.battlefield.any (fun o => o.name == "Grizzly Bears")
#guard (fraRuling 772).comment.contains "determined as Break Under Pressure resolves"
#guard (fraRuling 773).comment.contains "targets only the opponent"

/-!
## Tarmogoyf and Multiply by Zero (rulings 776, 797–801)
-/

/-- A 2/2 legendary artifact creature card, for card-type counting. -/
def testArtifactCreature : CardDef :=
  { legendaryCreature "Test Construct" ManaCost.empty #["Construct"] 2 2 with
    types := #[.artifact, .creature] }

def goyfOnBattlefield : Game := addPermanent afterDraw tarmogoyf ⟨0⟩ ⟨0⟩

/- Ruling 797: card types are counted, not cards. -/
#guard
  let g := goyfOnBattlefield
  let o := namedPermanent g "Tarmogoyf"
  g.power o == 0 && g.toughness o == 1
#guard
  let g := addToGraveyard goyfOnBattlefield testArtifactCreature ⟨1⟩
  let o := namedPermanent g "Tarmogoyf"
  g.power o == 2 && g.toughness o == 3
#guard
  let g := (List.range 10).foldl (fun g _ => addToGraveyard g testArtifactCreature ⟨1⟩)
    goyfOnBattlefield
  let o := namedPermanent g "Tarmogoyf"
  g.power o == 2 && g.toughness o == 3
#guard (fraRuling 797).comment.contains "counts card types, not cards"

/- Ruling 800: legendary and basic are supertypes; a basic land card adds
only the land type. Kindred and battle are card types. -/
#guard
  let g := addToGraveyard (addToGraveyard goyfOnBattlefield forest ⟨0⟩) testArtifactCreature ⟨0⟩
  g.graveyardCardTypeCount == 3
#guard (fraRuling 800).comment.contains "Legendary, basic, and snow are supertypes"
#guard (fraRuling 801).comment.contains "kindred"

/- Ruling 799: the ability works in every zone. In a graveyard alone,
Tarmogoyf counts itself and is 1/2. -/
#guard
  let g := addToGraveyard afterDraw tarmogoyf ⟨0⟩
  let o := graveyardCard g ⟨0⟩ "Tarmogoyf"
  g.power o == 1 && g.toughness o == 2
#guard (fraRuling 799).comment.contains "works in all zones"

/-- Ruling 798: Shock is put into the graveyard before state-based actions,
so the new instant type raises Tarmogoyf's toughness in time. With a
creature card in a graveyard, Tarmogoyf is 1/2; Shock's 2 damage doesn't
kill it because it is then 2/3. -/
def shockedGoyf : Game :=
  let g := addToGraveyard goyfOnBattlefield grizzlyBears ⟨1⟩
  let g := withRedMana (addToHand g shock ⟨0⟩) ⟨0⟩ 1
  let g := proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Shock").id
    (.permanent (namedPermanent g "Tarmogoyf").id)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard shockedGoyf.battlefield.any (fun o => o.name == "Tarmogoyf")
#guard shockedGoyf.toughness (namedPermanent shockedGoyf "Tarmogoyf") == 3
#guard (fraRuling 798).comment.contains "put into its owner's graveyard before state-based actions"

/-- Ruling 776: Multiply by Zero's 0/0 overrides Tarmogoyf's ability, but a
+1/+1 counter still applies, so it survives as a 1/1. -/
def zeroedGoyf : Game :=
  let g := addToGraveyard goyfOnBattlefield grizzlyBears ⟨1⟩
  let g := g.mapObjectStatus (namedPermanent g "Tarmogoyf") (fun s => s.addPlusOnePlusOne 1)
  let g := withBlackMana (addToHand g multiplyByZero ⟨0⟩) ⟨0⟩ 2
  let g := proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Multiply by Zero").id
    (.permanent (namedPermanent g "Tarmogoyf").id)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard
  let o := namedPermanent zeroedGoyf "Tarmogoyf"
  zeroedGoyf.power o == 1 && zeroedGoyf.toughness o == 1
#guard
  let g := passBoth (skipTo zeroedGoyf .end 80)
  let o := namedPermanent g "Tarmogoyf"
  g.toughness o == 4
#guard (fraRuling 776).comment.contains "overrides any other effect that sets a creature's base power"

/-!
## Violent Echoes (rulings 121 / 790)
-/

def violentEchoesAt (g : Game) (target : String) : Game :=
  let g := withRedMana (addToHand g violentEchoes ⟨0⟩) ⟨0⟩ 4
  let g := proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Violent Echoes").id
    (.permanent (namedPermanent g target).id)
  passBoth (mustApply g ⟨0⟩ .pay)

/- Ruling 121: damage beyond lethal damage is excess. Grizzly Bears with 1
damage marked needs 1 more, so 5 of the 6 is excess: Empower Jace 5. -/
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := g.dealDamageToPermanent (namedPermanent g "Grizzly Bears") 1
  let g := violentEchoesAt g "Grizzly Bears"
  (jaceTokenOf g).status.loyaltyCounters == 5
#guard (fraRuling 121).comment.contains "damage already marked on the creature is taken into account"

/- Ruling 790: for a planeswalker, excess is damage beyond its loyalty.
Jace, Reality Sculptor has 5, so 1 is excess. -/
#guard
  let g := violentEchoesAt (enterPermanent afterDraw jaceRealitySculptor ⟨1⟩)
    "Jace, Reality Sculptor"
  (jaceTokenOf g).status.loyaltyCounters == 1 &&
    !g.battlefield.any (fun o => o.name == "Jace, Reality Sculptor")
#guard (fraRuling 790).comment.contains "in excess of the planeswalker's loyalty"

/-!
## Heartwood tokens (ruling 793)
-/

/- A Heartwood is a red and green artifact with the Heartwood subtype and
“{T}: Add {R} or {G}.” Soul Tether creates one. -/
#guard
  let g := afterDraw.applyEffect ⟨0⟩ (Effect.createTokens .heartwood 1) #[]
  let o := namedPermanent g "Heartwood"
  o.printed.isToken && o.printed.isArtifact && g.hasSubtype o "Heartwood" &&
    o.printed.colors == (ColorSet.singleton .red).insert .green &&
    o.printed.tapAddOneOf == #[.colored .red, .colored .green]
#guard (heartwoodCrafter.prepareFace.bind (·.spellEffect)).map (·.resolution) ==
  some (.createTokens .heartwood 1)
#guard (fraRuling 793).comment.contains "artifact subtype Heartwood"

/- Ruling 823: the Ajani's Pridemate token has no mana cost. -/
#guard Game.pridemateToken.manaValue == 0
#guard (fraRuling 823).comment.contains "Its mana value is 0"

/- Ruling 888: Sculpture is a creature type and Treasure an artifact type. -/
#guard Game.sculptureToken.subtypes == #["Sculpture", "Treasure"]
#guard !isNoncreatureSubtype "Sculpture" && isNoncreatureSubtype "Treasure"
#guard (fraRuling 888).comment.contains "Sculpture is a creature type"

/-!
## Lands that enter tapped (rulings 808 / 809)
-/

def playLandNamed (g : Game) (card : CardDef) : Game :=
  let g := addToHand (g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 0 }))
    card ⟨0⟩
  mustApply g ⟨0⟩ (.playLand (handCardNamed g ⟨0⟩ card.name).id)

/- Dedicated Commons enters tapped unless you control a planeswalker. -/
#guard (namedPermanent (playLandNamed afterDraw dedicatedCommons) "Dedicated Commons").status.tapped
#guard !(namedPermanent (playLandNamed (afterDraw.empowerJace ⟨0⟩ 1) dedicatedCommons)
  "Dedicated Commons").status.tapped
#guard (fraRuling 808).comment.contains "that planeswalker isn't considered"

/- Deserted Beach enters tapped unless you control two or more other lands. -/
#guard
  let g := addPermanent afterDraw plains ⟨0⟩ ⟨0⟩
  (namedPermanent (playLandNamed g desertedBeach) "Deserted Beach").status.tapped
#guard
  let g := addPermanent (addPermanent afterDraw plains ⟨0⟩ ⟨0⟩) island ⟨0⟩ ⟨0⟩
  !(namedPermanent (playLandNamed g desertedBeach) "Deserted Beach").status.tapped
#guard (fraRuling 809).comment.contains "those other lands are not counted"

/-!
## Ghalta (rulings 824–829, 870–874)
-/

/-- A 0/12 wall used to push Ghalta's reduction past its generic mana. -/
def testWall : CardDef :=
  creature "Test Wall" ManaCost.empty #["Wall"] 0 12

/-- Cost of Ghalta from hand once it is on the stack (CR 601.2a / 601.2f). -/
def ghaltaCost (g : Game) (card : CardDef) : ManaCost :=
  let g := addToHand g card ⟨0⟩
  let ghalta := handCardNamed g ⟨0⟩ card.name
  let (g, _) := g.move ghalta.id .stack (some ⟨0⟩)
  g.playManaCost ghalta ghalta.printed

/- Ruling 827: Ghalta the Immovable costs {X} less for the greatest
toughness, but never less than {W}. Ruling 829: its mana value stays 9. -/
#guard
  let c := ghaltaCost (addPermanent afterDraw hillGiant ⟨0⟩ ⟨0⟩) ghaltaTheImmovable
  c.manaValue == 6 && c.coloredCount .white == 1
#guard
  let c := ghaltaCost (addPermanent afterDraw testWall ⟨0⟩ ⟨0⟩) ghaltaTheImmovable
  c.manaValue == 1 && c.coloredCount .white == 1
#guard ghaltaTheImmovable.manaValue == 9
#guard (fraRuling 827).comment.contains "can't reduce the total cost to cast the spell below {W}"
#guard (fraRuling 829).comment.contains "mana value doesn't change"

/- Rulings 870 / 872: Ghalta the Unstoppable uses the greatest power and
can't go below {G}. -/
#guard
  let c := ghaltaCost (addPermanent afterDraw crawWurm ⟨0⟩ ⟨0⟩) ghaltaTheUnstoppable
  c.manaValue == 3 && c.coloredCount .green == 1
#guard ghaltaTheUnstoppable.manaValue == 9
#guard (fraRuling 870).comment.contains "below {G}"
#guard (fraRuling 872).comment.contains "mana value doesn't change"

/-- A 0/5 creature whose power is the number of cards in your hand. -/
def testHandSizer : CardDef :=
  { creature "Test Hand Sizer" ManaCost.empty #["Elemental"] 0 5 with
    staticAbilities := #[.powerEqualCardsInHand] }

/-- Chandra holds Ghalta the Unstoppable and three other cards and controls
the hand-sized creature (power 4), then begins casting Ghalta. -/
def ghaltaProposed : Game :=
  let g := emptyHand (addPermanent afterDraw testHandSizer ⟨0⟩ ⟨0⟩) ⟨0⟩
  let g := addToHand (addToHand (addToHand g grizzlyBears ⟨0⟩) grizzlyBears ⟨0⟩) grizzlyBears ⟨0⟩
  let g := addToHand g ghaltaTheUnstoppable ⟨0⟩
  mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Ghalta the Unstoppable").id)

/- Ruling 874 (and 824 for Ghalta the Immovable): Ghalta moves to the stack
first, so the hand-sized creature has power 3 when the cost is determined. -/
#guard
  let c := (ghaltaProposed.proposedSpell.map (·.cost)).getD ManaCost.empty
  c.manaValue == 6 && c.coloredCount .green == 1
#guard (fraRuling 874).comment.contains "The first step of casting a spell is to move it to the stack"
#guard (fraRuling 824).comment.contains "The first step of casting a spell is to move it to the stack"

/- Rulings 873 / 826: no player may act until the spell is paid for. -/
#guard !ghaltaProposed.hasPriority ⟨1⟩
#guard !(ghaltaProposed.apply ⟨1⟩ .pass).isOk
#guard (fraRuling 873).comment.contains "no player may take actions until the spell has been paid for"
#guard (fraRuling 826).comment.contains "no player may take actions until the spell has been paid for"

/- Rulings 871 / 828: the determined cost stays locked even if the greatest
power changes while paying. -/
#guard
  let o := namedPermanent ghaltaProposed "Test Hand Sizer"
  let g := ghaltaProposed.mapObjectStatus o (fun s => s.addPump 10 0)
  let g := withGreenMana g ⟨0⟩ 6
  let g := mustApply g ⟨0⟩ .pay
  g.stack.size == 1 && (g.player ⟨0⟩).manaPool.total == 0
#guard (fraRuling 871).comment.contains "the cost to cast Ghalta remains what you previously determined"
#guard (fraRuling 828).comment.contains "the cost to cast Ghalta remains what you previously determined"

/-!
## Blazing Crescendo (rulings 388 / 567 / 568)
-/

def crescendoCast : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addToLibraryTop g mountain ⟨0⟩
  let g := withRedMana (addToHand g realityFractureBlazingCrescendo ⟨0⟩) ⟨0⟩ 2
  let g := proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Blazing Crescendo").id
    (.permanent (namedPermanent g "Grizzly Bears").id)
  mustApply g ⟨0⟩ .pay

/- Rulings 567 / 568: with its target gone, the spell doesn't resolve and no
card is exiled. -/
#guard
  let bears := namedPermanent crescendoCast "Grizzly Bears"
  let (g, _) := crescendoCast.move bears.id (.graveyard ⟨0⟩) none
  let g := passBoth g
  !g.objects.any (fun o => o.zone == .exile && o.name == "Mountain") &&
    (g.player ⟨0⟩).library.size == (crescendoCast.player ⟨0⟩).library.size
#guard (fraRuling 567).comment.contains "No card will be exiled"
#guard (fraRuling 568).comment.contains "No card will be exiled"

/-- Ruling 388: an exiled land is played with the normal timing rules — only
in a main phase with an empty stack. -/
def crescendoResolved : Game := passBoth crescendoCast

#guard crescendoResolved.power (namedPermanent crescendoResolved "Grizzly Bears") == 5
#guard
  let mtn := crescendoResolved.objects.find? (fun o => o.zone == .exile && o.name == "Mountain")
  match mtn with
  | some m =>
    let g := crescendoResolved
    (g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 0 })).apply ⟨0⟩
      (.playLand m.id) |>.isOk
  | none => false
#guard
  let g := skipTo crescendoResolved .beginningOfCombat 80
  match g.objects.find? (fun o => o.zone == .exile && o.name == "Mountain") with
  | some m => !(g.apply ⟨0⟩ (.playLand m.id)).isOk
  | none => false
#guard (fraRuling 388).comment.contains "you may play it only during your main phase"

/-!
## Split second (rulings 837–841)
-/

/-- Chandra controls Samut and casts Shock at Nissa. Nissa holds Lightning
Bolt and red mana. -/
def samutShock : Game :=
  let g := addPermanent afterDraw samutTyrantOfNaktamun ⟨0⟩ ⟨0⟩
  let g := addPermanent g mountain ⟨1⟩ ⟨1⟩
  let g := withRedMana (addToHand g lightningBolt ⟨1⟩) ⟨1⟩ 1
  let g := withRedMana (addToHand g shock ⟨0⟩) ⟨0⟩ 1
  let g := proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Shock").id (.player ⟨1⟩)
  mustApply (mustApply g ⟨0⟩ .pay) ⟨0⟩ .pass

#guard samutShock.splitSecondOnStack
#guard samutShock.hasPriority ⟨1⟩
/- Ruling 837: Nissa still gets priority but can't cast Lightning Bolt. She
may still activate a mana ability. -/
#guard rejects samutShock ⟨1⟩ (.cast (handCardNamed samutShock ⟨1⟩ "Lightning Bolt").id)
  "split second"
#guard (samutShock.apply ⟨1⟩ (.tapForMana (namedPermanent samutShock "Mountain").id
  (.colored .red))).isOk
#guard (fraRuling 837).comment.contains "limited to mana abilities"

/- Ruling 838: split second doesn't stop triggered abilities. Guttersnipe
still triggers when Shock is cast. -/
#guard
  let g := addPermanent afterDraw samutTyrantOfNaktamun ⟨0⟩ ⟨0⟩
  let g := addPermanent g guttersnipe ⟨0⟩ ⟨0⟩
  let g := withRedMana (addToHand g shock ⟨0⟩) ⟨0⟩ 1
  let g := proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Shock").id (.player ⟨1⟩)
  let g := mustApply g ⟨0⟩ .pay
  g.stack.size == 2 && g.splitSecondOnStack &&
    (resolveStack g 20 |>.player ⟨1⟩).life == 16
#guard (fraRuling 838).comment.contains "Split second doesn't stop triggered abilities"

/- Ruling 839: a spell can't be cast as part of a resolving ability while a
spell with split second is on the stack. -/
#guard
  let g := addToHand (emptyHand samutShock ⟨0⟩) lightningBolt ⟨0⟩
  let g := g.castInstantSorceryFromHandMvAtMost ⟨0⟩ 3
  (g.player ⟨0⟩).hand.any (fun id => (g.object! id).name == "Lightning Bolt") &&
    g.stack.size == 1
#guard
  let g := addToHand (emptyHand afterDraw ⟨0⟩) lightningBolt ⟨0⟩
  let g := g.castInstantSorceryFromHandMvAtMost ⟨0⟩ 3
  g.stack.size == 1 && !(g.player ⟨0⟩).hand.any (fun id => (g.object! id).name == "Lightning Bolt")
#guard (fraRuling 839).comment.contains "that spell can't be cast if a spell with split second is on the stack"

/-- Ruling 841: once Shock resolves, Nissa may cast spells again. -/
def samutShockResolved : Game := mustApply samutShock ⟨1⟩ .pass

#guard !samutShockResolved.splitSecondOnStack
#guard (samutShockResolved.player ⟨1⟩).life == 18
#guard
  let g := mustApply samutShockResolved ⟨0⟩ .pass
  (g.apply ⟨1⟩ (.cast (handCardNamed g ⟨1⟩ "Lightning Bolt").id)).isOk
#guard (fraRuling 841).comment.contains "players may again cast spells"

/-- Ruling 840: an ability already on the stack still resolves after a split
second spell is cast in response. -/
def samutOverJace : Game :=
  let g := addPermanent (afterDraw.empowerJace ⟨0⟩ 3) samutTyrantOfNaktamun ⟨0⟩ ⟨0⟩
  let g := withRedMana (addToHand g shock ⟨0⟩) ⟨0⟩ 1
  let g := mustApply g ⟨0⟩ (.activate (jaceTokenOf g).id 1)
  let g := proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Shock").id (.player ⟨1⟩)
  mustApply g ⟨0⟩ .pay

#guard samutOverJace.stack.size == 2
#guard
  let g := resolveStack samutOverJace 20
  (g.player ⟨1⟩).life == 18 &&
    (g.player ⟨0⟩).hand.size == (samutOverJace.player ⟨0⟩).hand.size + 1
#guard (fraRuling 840).comment.contains "won't affect spells and abilities that are already on the stack"

/-!
## Karn, Argent Defender (rulings 890–893)
-/

def withKarn : Game := addPermanent afterDraw karnArgentDefender ⟨0⟩ ⟨0⟩

/-- Ruling 892: a creature entering doesn't cause abilities to trigger, so
Mindseeker Oculus's empower trigger never happens. -/
def oculusUnderKarn : Game :=
  passBoth ((enterPermanent withKarn mindseekerOculus ⟨0⟩).receivePriority ⟨0⟩)

#guard (oculusUnderKarn.jacePlaneswalkerTokens ⟨0⟩).isEmpty
#guard (fraRuling 892).comment.contains "Look at the permanent as it exists on the battlefield"

/- Ruling 890: replacement effects still apply. The Angel enters prepared,
and a planeswalker enters with loyalty. -/
#guard
  let g := enterPermanent withKarn blossomBlessedAngel ⟨0⟩
  (namedPermanent g "Blossom-Blessed Angel").status.prepared
#guard
  let g := enterPermanent withKarn jaceRealitySculptor ⟨0⟩
  (namedPermanent g "Jace, Reality Sculptor").status.loyaltyCounters == 5
#guard (fraRuling 890).comment.contains "Replacement effects"

/- Ruling 891: Karn entering doesn't trigger Mentor of the Meek either. -/
#guard
  let g := addPermanent afterDraw mentorOfTheMeek ⟨0⟩ ⟨0⟩
  let g := enterPermanent g karnArgentDefender ⟨0⟩
  g.waitingTriggers.isEmpty
#guard
  let g := addPermanent afterDraw mentorOfTheMeek ⟨0⟩ ⟨0⟩
  let g := enterPermanent g grizzlyBears ⟨0⟩
  !g.waitingTriggers.isEmpty
#guard (fraRuling 891).comment.contains "neither one will cause triggered abilities to trigger"

/-- Ruling 893: a land that is neither an artifact nor a creature still
causes landfall, but an artifact land doesn't. -/
def testArtifactLand : CardDef :=
  { name := "Test Artifact Land", types := #[.artifact, .land] }

#guard
  let g := addPermanent withKarn avatarOfBurgeoningEchoes ⟨0⟩ ⟨0⟩
  let g := playLandNamed g forest
  g.waitingTriggers.size + g.stack.size == 1
#guard
  let g := addPermanent withKarn avatarOfBurgeoningEchoes ⟨0⟩ ⟨0⟩
  let g := playLandNamed g testArtifactLand
  g.waitingTriggers.isEmpty && g.stack.isEmpty
#guard (fraRuling 893).comment.contains "If an artifact land or creature land you control enters"

end Mtg.Engine.FraRulingTests
