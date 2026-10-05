import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.RealityFracture
import Mtg.Engine.FraOracleTests
import Mtg.Engine.FraOracleTests2
import Mtg.Engine.FraOracleTests4
import Mtg.Engine.Game
import Mtg.Engine.OracleData
import Mtg.Engine.Tests.Abilities
import Mtg.Engine.Tests.Auras
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns

/-!
# Engine behavior for Reality Fracture (FRA) judge rulings (part 5)

Ajani Resolute, Ghalta's and Loot's combat damage, Sphinx's Approach,
Proft, Verdant Kraken, Eardrum Rattler, Teyo, Vraska, the Cutting Glare,
Desperate Futurescribe, The Theorist, Omnipresence, and Face Yourself.
-/

namespace Mtg.Engine.FraRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

/-!
## Ajani Resolute (rulings 821 / 822)
-/

/-- Ruling 821: two lifelink creatures dealing combat damage are two life
gains, so Ajani's first ability and the Pridemate token each trigger twice. -/
def ajaniResoluteTwoLifelinkers : Game :=
  let g := enterPermanent afterDraw ajaniResolute ⟨0⟩
  let g := g.createKindTokens ⟨0⟩ .pridemate 1
  let g := g.mapObjectStatus (namedPermanent g "Ajani's Pridemate") (fun s =>
    { s with summoningSick := false })
  let g := addPermanent (addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩) grayOgre ⟨0⟩ ⟨0⟩
  let g := withLifelink (withLifelink g "Grizzly Bears") "Gray Ogre"
  resolveStack (attackWith g #["Grizzly Bears", "Gray Ogre"]) 30

#guard (namedPermanent ajaniResoluteTwoLifelinkers "Ajani Resolute").status.loyaltyCounters == 4
#guard (namedPermanent ajaniResoluteTwoLifelinkers "Ajani's Pridemate").status.plusOnePlusOne == 2
#guard (fraRuling 821).comment.contains "trigger that many times"

/- Ruling 822: a Pridemate dealt lethal damage as you gain life dies before
its counter arrives. -/
#guard
  let g := afterDraw.createKindTokens ⟨0⟩ .pridemate 1
  let g := g.mapObjectStatus (namedPermanent g "Ajani's Pridemate") (fun s =>
    { s with summoningSick := false })
  let g := addPermanent g crawWurm ⟨1⟩ ⟨1⟩
  let g := withLifelink g "Ajani's Pridemate"
  let g := attackWith g #["Ajani's Pridemate"] #[("Craw Wurm", "Ajani's Pridemate")]
  (g.player ⟨0⟩).life == 22 && !g.battlefield.any (fun o => o.name == "Ajani's Pridemate")
#guard (fraRuling 822).comment.contains "won't receive a counter from its ability in time"

/- Ajani's −4 creates the Pridemate token. -/
#guard
  let g := enterPermanent afterDraw ajaniResolute ⟨0⟩
  let g := g.mapObjectStatus (namedPermanent g "Ajani Resolute") (fun s =>
    { s with loyaltyCounters := 4 })
  let g := resolveStack (mustApply g ⟨0⟩ (.activate (namedPermanent g "Ajani Resolute").id 1)) 20
  g.battlefield.any (fun o => o.name == "Ajani's Pridemate" && o.printed.isToken)

/-!
## Ghalta, the Immovable and Loot, the Anomaly (rulings 825 / 850 / 851)
-/

/-- A 1/4 creature, so toughness exceeds power. -/
def testTallCreature : CardDef := creature "Test Tower" ManaCost.empty #["Wall"] 1 4

/- Ruling 825: with Ghalta, the 1/4 assigns 4 combat damage, but its power
is still 1. -/
#guard
  let g := addPermanent (addPermanent afterDraw ghaltaTheImmovable ⟨0⟩ ⟨0⟩) testTallCreature ⟨0⟩ ⟨0⟩
  let g := attackWith g #["Test Tower"]
  (g.player ⟨1⟩).life == 16 && g.power (namedPermanent g "Test Tower") == 1
#guard (fraRuling 825).comment.contains "doesn't actually change any creature's power"

/- Ruling 850: Loot (−2/4) assigns 2 combat damage, and his power stays −2. -/
#guard
  let g := attackWith (addPermanent afterDraw lootTheAnomaly ⟨0⟩ ⟨0⟩) #["Loot, the Anomaly"]
  (g.player ⟨1⟩).life == 18 && g.power (namedPermanent g "Loot, the Anomaly") == -2
#guard (fraRuling 850).comment.contains "Loot's first ability doesn't change his power"

/- Ruling 851: with Ghalta, Loot assigns damage equal to his toughness. -/
#guard
  let g := addPermanent (addPermanent afterDraw ghaltaTheImmovable ⟨0⟩ ⟨0⟩) lootTheAnomaly ⟨0⟩ ⟨0⟩
  let g := attackWith g #["Loot, the Anomaly"]
  (g.player ⟨1⟩).life == 16
#guard (fraRuling 851).comment.contains "use his toughness"

/-!
## Sphinx's Approach and Proft, Sinister Mastermind (rulings 769 / 852)
-/

/- Ruling 769: a constructed deck may hold any number of Sphinx's Approach,
but other cards are still limited to four. -/
#guard (validateDeck .constructed
  ((Array.replicate 5 sphinxsApproach) ++ Array.replicate 55 island)).isOk
#guard !(validateDeck .constructed
  ((Array.replicate 5 shock) ++ Array.replicate 55 island)).isOk
#guard (fraRuling 769).comment.contains "lets you ignore the \"four-of\" rule"

/-- Ruling 852: casting Proft from a graveyard needs seven other cards there.
A flashback cost stands in for the permission to cast it from the graveyard. -/
def proftFromGraveyard (others : Nat) : Game :=
  let proft := { proftSinisterMastermind with flashback := some (ManaCost.ofColor .black) }
  let g := (List.range others).foldl (fun g _ => addToGraveyard g grizzlyBears ⟨0⟩) afterDraw
  withBlackMana (addToGraveyard g proft ⟨0⟩) ⟨0⟩ 1

#guard rejects (proftFromGraveyard 6) ⟨0⟩
  (.cast (graveyardCard (proftFromGraveyard 6) ⟨0⟩ "Proft, Sinister Mastermind").id)
  "7 or more other cards"
#guard ((proftFromGraveyard 7).apply ⟨0⟩
  (.cast (graveyardCard (proftFromGraveyard 7) ⟨0⟩ "Proft, Sinister Mastermind").id)).isOk
#guard (fraRuling 852).comment.contains "seven other cards in your graveyard"

/-!
## Verdant Kraken (ruling 802)
-/

/-- At Nissa's upkeep, Chandra's Kraken creates a Forest Tentacle. It's a
Forest land creature, but not basic. -/
def krakenAtNissaUpkeep : Game :=
  let g := addPermanent afterDraw verdantKraken ⟨0⟩ ⟨0⟩
  resolveStack (skipTo (passBoth (skipTo g .end 80)) .draw 80) 20

#guard
  let g := krakenAtNissaUpkeep
  let t := namedPermanent g "Forest Tentacle"
  t.controlledBy ⟨0⟩ && t.printed.isLand && t.isCreature && g.hasSubtype t "Forest" &&
    !t.printed.hasSupertype .basic && g.power t == 3
#guard (fraRuling 802).comment.contains "isn't a basic land"

/-!
## Eardrum Rattler (ruling 783)
-/

def rattlerBoard : Game :=
  addPermanent (addPermanent afterDraw eardrumRattler ⟨0⟩ ⟨0⟩) grizzlyBears ⟨0⟩ ⟨0⟩

def rattlerActivated : Game :=
  let g := withRedMana rattlerBoard ⟨0⟩ 1
  let g := mustApply g ⟨0⟩ (.activate (namedPermanent g "Eardrum Rattler").id 0)
  let g := mustApply g ⟨0⟩ (.target (.permanent (namedPermanent g "Grizzly Bears").id))
  mustApply g ⟨0⟩ .pay

/- Once the ability resolves, raising the power doesn't matter. -/
#guard
  let g := passBoth rattlerActivated
  let g := g.mapObjectStatus (namedPermanent g "Grizzly Bears") (fun s => s.addPump 3 0)
  g.hasCantBeBlocked (namedPermanent g "Grizzly Bears")

/- If the target's power rises above 2 first, the ability does nothing. -/
#guard
  let g := rattlerActivated.mapObjectStatus (namedPermanent rattlerActivated "Grizzly Bears")
    (fun s => s.addPump 1 0)
  let g := passBoth g
  !g.hasCantBeBlocked (namedPermanent g "Grizzly Bears")
#guard (fraRuling 783).comment.contains "the ability does nothing because the target is no longer legal"

/-!
## Teyo (ruling 833)
-/

/-- A permanent that is both a creature and a planeswalker. -/
def testCreatureWalker : CardDef :=
  { creature "Test Walker" ManaCost.empty #["Jace"] 2 2 with
    types := #[.creature, .planeswalker], loyalty := some 3 }

/- A target that is both a creature and a planeswalker gets both counters. -/
#guard
  let g := enterPermanent afterDraw testCreatureWalker ⟨0⟩
  let g := (enterPermanent g teyoLightshieldExpert ⟨0⟩).receivePriority ⟨0⟩
  let g := mustApply g ⟨0⟩ (.target (.permanent (namedPermanent g "Test Walker").id))
  let g := resolveStack g 20
  let w := namedPermanent g "Test Walker"
  w.status.plusOnePlusOne == 1 && w.status.loyaltyCounters == 4 && g.hasHexproof w
#guard (fraRuling 833).comment.contains "it will get both kinds of counters"

/-!
## Vraska, the Cutting Glare (ruling 889)
-/

def withLands (g : Game) (n : Nat) : Game :=
  (List.range n).foldl (fun g _ => addPermanent g swamp ⟨0⟩ ⟨0⟩) g

def vraskaEnters (lands : Nat) : Game :=
  let g := addPermanent (withLands afterDraw lands) grizzlyBears ⟨1⟩ ⟨1⟩
  (enterPermanent g vraskaTheCuttingGlare ⟨0⟩).receivePriority ⟨0⟩

/- With five lands the ability doesn't trigger. -/
#guard (vraskaEnters 5).stack.isEmpty && (vraskaEnters 5).pending == .none
/- With six, it destroys the target and its controller creates a Treasure. -/
#guard
  let g := resolveStack (vraskaEnters 6) 20
  !g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    g.battlefield.any (fun o => o.name == "Treasure" && o.controlledBy ⟨1⟩)
/- If a land leaves before it resolves, it does nothing. -/
#guard
  let g := vraskaEnters 6
  let g := match g.pending with
    | .chooseTargets _ => mustApply g ⟨0⟩ (.target (.permanent (namedPermanent g "Grizzly Bears").id))
    | _ => g
  let (g, _) := g.move (namedPermanent g "Swamp").id (.graveyard ⟨0⟩) none
  let g := resolveStack g 20
  g.battlefield.any (fun o => o.name == "Grizzly Bears")
#guard (fraRuling 889).comment.contains "will check again as it tries to resolve"

/-!
## Desperate Futurescribe (ruling 804)
-/

def futurescribeCombat (scried surveilled : Bool) : Game :=
  let g := addPermanent (addPermanent afterDraw desperateFuturescribe ⟨0⟩ ⟨0⟩) grizzlyBears ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl =>
    { pl with scriedOrSurveilledThisTurn := scried || surveilled })
  resolveStack (skipTo g .beginningOfCombat 80) 20

/- Having scried and surveilled still gives only one counter. -/
#guard
  let o := namedPermanent (futurescribeCombat true true) "Grizzly Bears"
  o.status.plusOnePlusOne == 1 && o.status.pump == (0, 0)
#guard
  let o := namedPermanent (futurescribeCombat false false) "Grizzly Bears"
  o.status.plusOnePlusOne == 0 && o.status.pump == (1, 1)
#guard (fraRuling 804).comment.contains "only one +1/+1 counter"

/- Scrying or surveilling sets the flag; scry 0 doesn't. -/
#guard (afterDraw.beginSurveil ⟨0⟩ 1).player ⟨0⟩ |>.scriedOrSurveilledThisTurn
#guard (afterDraw.beginScry ⟨0⟩ 1).player ⟨0⟩ |>.scriedOrSurveilledThisTurn
#guard !((afterDraw.beginScry ⟨0⟩ 0).player ⟨0⟩).scriedOrSurveilledThisTurn

/-!
## The Theorist, Jace Beleren (ruling 770)
-/

/-- Nissa draws for her draw step before The Theorist's trigger lets Chandra
draw. -/
def theoristAtNissaDraw : Game :=
  let g := enterPermanent afterDraw theTheoristJaceBeleren ⟨0⟩
  skipTo (passBoth (skipTo g .end 80)) .draw 80

#guard
  let g := theoristAtNissaDraw
  let hand0 := (g.player ⟨0⟩).hand.size
  let g' := resolveStack g 20
  (g'.player ⟨0⟩).hand.size == hand0 + 1
#guard theoristAtNissaDraw.activePlayer == ⟨1⟩ && theoristAtNissaDraw.stack.size == 1
#guard (fraRuling 770).comment.contains "before you draw a card from Jace's first ability"

/-!
## Omnipresence (rulings 794–796)
-/

def omniBoard : Game :=
  let g := addPermanent afterDraw omnipresence ⟨0⟩ ⟨0⟩
  addPermanent (addPermanent g grayOgre ⟨0⟩ ⟨0⟩) grayOgre ⟨0⟩ ⟨0⟩

/- Mana value 2 or less: cast without paying its mana cost. -/
#guard
  let g := addToHand omniBoard grizzlyBears ⟨0⟩
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Grizzly Bears").id)
  g.stack.size == 1 && g.pending == .none
/- Mana value 3 is more than the two creatures: pay normally. -/
#guard
  let g := addToHand omniBoard hillGiant ⟨0⟩
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Hill Giant").id)
  g.pending == .activateManaAbilities ⟨0⟩
/- Ruling 794: normal timing applies; a creature can't be cast at combat. -/
#guard
  let g := skipTo (addToHand omniBoard grizzlyBears ⟨0⟩) .beginningOfCombat 80
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Grizzly Bears")
#guard (fraRuling 794).comment.contains "normal timing permissions"

/- Ruling 795: additional costs are still paid. Countersculpt costs nothing
but its {1} if Chandra doesn't behold a Jace. -/
#guard
  let g := withRedMana (addToHand (addToHand omniBoard shock ⟨0⟩) countersculpt ⟨0⟩) ⟨0⟩ 1
  let g := proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Shock").id (.player ⟨1⟩)
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Countersculpt").id)
  let g := mustApply g ⟨0⟩ (.chooseAdditionalCost true)
  match g.proposedSpell with
  | some prop => prop.cost.manaValue == 1
  | none => false
#guard (fraRuling 795).comment.contains "You can, however, pay additional costs"

/- Ruling 796: after Omnipresence resolves on your turn, you get priority. -/
#guard
  let g := withMana (addToHand afterDraw omnipresence ⟨0⟩) ⟨0⟩ .green 8
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Omnipresence").id)
  let g := passBoth (mustApply g ⟨0⟩ .pay)
  g.battlefield.any (fun o => o.name == "Omnipresence") && g.hasPriority ⟨0⟩
#guard (fraRuling 796).comment.contains "you'll have priority immediately after it resolves"

/-!
## Face Yourself (rulings 784–789)
-/

/-- Chandra casts Face Yourself targeting Nissa. -/
def faceYourselfAt (g : Game) : Game :=
  let g := withRedMana (addToHand g faceYourself ⟨0⟩) ⟨0⟩ 7
  let g := proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Face Yourself").id (.player ⟨1⟩)
  resolveStack (mustApply g ⟨0⟩ .pay) 30

/-- Tokens Chandra controls named `name`. -/
def chandraTokens (g : Game) (name : String) : Array GameObject :=
  g.battlefield.filter (fun o => o.name == name && o.printed.isToken && o.controlledBy ⟨0⟩)

/-- Ruling 784: an enters ability of the copied creature triggers. Ruling
787: counters and tapped status aren't copied. -/
def facedOculus : Game :=
  let g := addPermanent afterDraw mindseekerOculus ⟨1⟩ ⟨1⟩
  let g := g.mapObjectStatus (namedPermanent g "Mindseeker Oculus") (fun s =>
    { s.addPlusOnePlusOne 2 with tapped := true })
  faceYourselfAt g

#guard (chandraTokens facedOculus "Mindseeker Oculus").size == 1
#guard (jaceTokenOf facedOculus).status.loyaltyCounters == 4
#guard (chandraTokens facedOculus "Mindseeker Oculus").all (fun o =>
  o.status.plusOnePlusOne == 0 && !o.status.tapped && facedOculus.hasHaste o)
#guard (fraRuling 784).comment.contains "Any enters abilities of the copied creature will trigger"
#guard (fraRuling 787).comment.contains "It doesn't copy whether that creature is tapped"

/- Ruling 785: a copy of Guiding Hydra has X = 0, so it enters with no
counters and dies as a 1/0. -/
#guard
  let g := addPermanent afterDraw guidingHydra ⟨1⟩ ⟨1⟩
  let g := g.mapObjectStatus (namedPermanent g "Guiding Hydra") (fun s => s.addPlusOnePlusOne 3)
  let g := faceYourselfAt g
  (chandraTokens g "Guiding Hydra").isEmpty && g.battlefield.any (fun o => o.name == "Guiding Hydra")
#guard (fraRuling 785).comment.contains "X is considered to be 0"

/- Rulings 786 / 789: a token, or a creature copying something, is copied as
what it is: a Cadet copy is a 2/2 Cadet. -/
#guard
  let g := faceYourselfAt (afterDraw.createKindTokens ⟨1⟩ .cadet 1)
  (chandraTokens g "Cadet").size == 1 &&
    (chandraTokens g "Cadet").all (fun o => g.power o == 2 && g.hasSubtype o "Wizard")
#guard (fraRuling 786).comment.contains "copies the original characteristics of that token"
#guard (fraRuling 789).comment.contains "enters the battlefield as whatever that creature copied"

/- Ruling 788: the tokens see each other enter. The Mentor of the Meek copy
sees the Grizzly Bears copy enter. -/
#guard
  let g := addPermanent (addPermanent afterDraw mentorOfTheMeek ⟨1⟩ ⟨1⟩) grizzlyBears ⟨1⟩ ⟨1⟩
  let g := withRedMana (addToHand g faceYourself ⟨0⟩) ⟨0⟩ 7
  let g := proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Face Yourself").id (.player ⟨1⟩)
  let g := passBoth (mustApply g ⟨0⟩ .pay)
  g.stack.any (fun e =>
    e.controller == ⟨0⟩ && mentions (g.object! e.objectId).name "Mentor of the Meek")
#guard (fraRuling 788).comment.contains "The tokens see each other enter the battlefield"

/- At the end step, the copies are sacrificed unless Chandra controls a
planeswalker. -/
#guard
  let g := faceYourselfAt (addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩)
  let g := resolveStack (skipTo g .end 80) 20
  (chandraTokens g "Grizzly Bears").isEmpty
#guard
  let g := faceYourselfAt (addPermanent (afterDraw.empowerJace ⟨0⟩ 2) grizzlyBears ⟨1⟩ ⟨1⟩)
  let g := resolveStack (skipTo g .end 80) 20
  (chandraTokens g "Grizzly Bears").size == 1

end Mtg.Engine.FraRulingTests
