import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.RealityFracture
import Mtg.Engine.FraOracleTests
import Mtg.Engine.FraOracleTests2
import Mtg.Engine.FraOracleTests4
import Mtg.Engine.Game
import Mtg.Engine.OracleData
import Mtg.Engine.Tests.Abilities
import Mtg.Engine.Tests.Auras
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Mulligans
import Mtg.Engine.Tests.Turns

/-!
# Engine behavior for Reality Fracture (FRA) judge rulings (part 7)

Chandra, Torch of Defiance: casting the exiled card as her ability resolves,
her mana ability that uses the stack, and her emblem. Graft Surgeon,
Gardenize, Loot, the Nexus, Proft, Consulting Detective, Fblthp,
Roiling Canopy, Grim Repriser, Enlightened Confidant, Cryotheory Adept,
Campus Crier, and Compel Brutality.
-/

namespace Mtg.Engine.FraRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

/-- Chandra enters with four loyalty and `top` on top of her library. -/
def chandraBoard (g : Game) (top : CardDef) : Game :=
  let g := addToLibraryTop (emptyHand g ⟨0⟩) top ⟨0⟩
  enterPermanent g chandraTorchOfDefiance ⟨0⟩

/-- Apply idle actions until `done` holds. -/
def stepUntil (g : Game) (done : Game → Bool) : Nat → Game
  | 0 => g
  | n + 1 => if done g then g else stepUntil (applyIdle g) done n

/-- Activate Chandra's first +1 and let it resolve. -/
def chandraExileTop (g : Game) : Game :=
  let chandra := namedPermanent g "Chandra, Torch of Defiance"
  passBoth (mustApply g ⟨0⟩ (.activate chandra.id 0))

def exiledNamed (g : Game) (name : String) : GameObject :=
  match g.objects.find? (fun o => o.zone == .exile && o.name == name) with
  | some o => o
  | none => panic! s!"expected {name} in exile"

/- Ruling 855: a land can't be cast, so Chandra deals 2 damage to each
opponent. -/
#guard
  let g := chandraExileTop (chandraBoard afterDraw forest)
  (g.player ⟨1⟩).life == 18 && g.pending == .none &&
    g.objects.any (fun o => o.zone == .exile && o.name == "Forest")
#guard (fraRuling 855).comment.contains "doesn't allow you to play lands"

/- Declining to cast also deals the damage. -/
#guard
  let g := chandraExileTop (chandraBoard afterDraw grizzlyBears)
  let g := mustApply g ⟨0⟩ .decline
  (g.player ⟨1⟩).life == 18

/-- Rulings 857 / 859: the card is cast as the ability resolves, ignoring the
creature's sorcery timing, and Chandra pays its costs. -/
def chandraCastsGiant : Game :=
  let g := withRedMana (chandraExileTop (chandraBoard afterDraw hillGiant)) ⟨0⟩ 4
  mustApply g ⟨0⟩ (.cast (exiledNamed g "Hill Giant").id)

#guard topOfStack chandraCastsGiant == "Hill Giant"
#guard (chandraCastsGiant.player ⟨0⟩).manaPool.total == 0
#guard (chandraCastsGiant.player ⟨1⟩).life == 20
#guard (passBoth chandraCastsGiant).battlefield.any (fun o => o.name == "Hill Giant")
#guard
  let g := chandraExileTop (chandraBoard afterDraw hillGiant)
  rejects g ⟨0⟩ (.cast (exiledNamed g "Hill Giant").id) "cannot pay"
#guard (fraRuling 857).comment.contains "You pay the costs for the exiled card"
#guard (fraRuling 859).comment.contains "Timing permissions based on the card's type are ignored"

/- A cast spell with a target still announces it. -/
#guard
  let g := withRedMana (chandraExileTop (chandraBoard afterDraw shock)) ⟨0⟩ 1
  let g := mustApply g ⟨0⟩ (.cast (exiledNamed g "Shock").id)
  let g := mustApply g ⟨0⟩ (.target (.player ⟨1⟩))
  (passBoth g |>.player ⟨1⟩).life == 18

/- Ruling 856: Chandra's “+1: Add {R}{R}.” isn't a mana ability; it uses
the stack. -/
#guard
  let g := chandraBoard afterDraw forest
  let g := mustApply g ⟨0⟩ (.activate (namedPermanent g "Chandra, Torch of Defiance").id 1)
  g.stack.size == 1 && (passBoth g |>.player ⟨0⟩).manaPool.total == 2

/- Ruling 854: with two opponents, each is dealt 2 damage, 4 in total (as
the opposing team would be in Two-Headed Giant). -/
#guard
  let g := chandraBoard (skipTo threeStarted .precombatMain 80) forest
  let g := mustApply g ⟨0⟩ (.activate (namedPermanent g "Chandra, Torch of Defiance").id 0)
  let g := resolveStack g 20
  (g.player ⟨1⟩).life == 18 && (g.player ⟨2⟩).life == 18
#guard (fraRuling 854).comment.contains "4 damage total"

/-- Chandra with seven loyalty uses her −7 for the emblem. -/
def chandraEmblem : Game :=
  let g := chandraBoard afterDraw forest
  let chandra := namedPermanent g "Chandra, Torch of Defiance"
  let g := g.mapObjectStatus chandra (fun s => { s with loyaltyCounters := 7 })
  passBoth (mustApply g ⟨0⟩ (.activate chandra.id 3))

/- Ruling 858: the emblem is colorless. -/
#guard chandraEmblem.objects.any (fun o =>
  o.zone == .command && o.controlledBy ⟨0⟩ && o.printed.colors.isColorless)
#guard (fraRuling 858).comment.contains "The emblem created by Chandra's last ability is colorless"

/- Ruling 860: the emblem's trigger resolves before the spell. -/
#guard
  let g := castShockAtNissa chandraEmblem
  let g := stepUntil g (fun g => g.stack.size == 1) 20
  topOfStack g == "Shock" && (g.player ⟨1⟩).life == 15
#guard (fraRuling 860).comment.contains "resolves before the spell that caused it to trigger"

/-!
## Graft Surgeon (rulings 756 / 758)
-/

/-- Graft Surgeon enters with a +1/+1 counter; give it a shield counter too,
then it dies. Its trigger puts the same number of each kind of counter on
Grizzly Bears, not only its +1/+1 counters. -/
def graftSurgeonDied : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := enterPermanent g graftSurgeon ⟨0⟩
  let surgeon := namedPermanent g "Graft Surgeon"
  let g := g.mapObjectStatus surgeon (fun s => { s with shield := 1 })
  let g := g.moveToOwnerGraveyard (g.object! surgeon.id) "Graft Surgeon dies"
  resolveStack (g.receivePriority ⟨0⟩) 20

#guard (namedPermanent (enterPermanent afterDraw graftSurgeon ⟨0⟩) "Graft Surgeon").status.plusOnePlusOne == 1
#guard (namedPermanent graftSurgeonDied "Grizzly Bears").status.plusOnePlusOne == 1
#guard (namedPermanent graftSurgeonDied "Grizzly Bears").status.shield == 1
#guard (fraRuling 756).comment.contains "not just its +1/+1 counters"
#guard (fraRuling 758).comment.contains "you put the same number of each kind of counter"

/-!
## Gardenize (ruling 792)
-/

/-- A creature Chandra controls dies, so Gardenize gets a charge counter. At
her next first main phase, Gardenize is destroyed with its trigger on the
stack, and its last-known counter still adds {G}. -/
def gardenizeNextMain : Game :=
  let g := addPermanent (addPermanent afterDraw gardenize ⟨0⟩ ⟨0⟩) grizzlyBears ⟨0⟩ ⟨0⟩
  let g := g.moveToOwnerGraveyard (namedPermanent g "Grizzly Bears") "Grizzly Bears dies"
  let g := resolveStack (g.receivePriority ⟨0⟩) 20
  let g := passBoth (skipTo g .end 80)
  let g := passBoth (skipTo g .end 80)
  skipTo g .precombatMain 80

#guard (namedPermanent gardenizeNextMain "Gardenize").status.charge == 1
#guard
  let g := gardenizeNextMain
  let (g, _) := g.move (namedPermanent g "Gardenize").id (.graveyard ⟨0⟩) none
  let g := resolveStack g 20
  g.activePlayer == ⟨0⟩ && (g.player ⟨0⟩).manaPool.total == 1
#guard (fraRuling 792).comment.contains "use the number of counters it had on it the last time"

/-!
## Loot, the Nexus (ruling 875)
-/

/- A 1/1 and two creatures with power 2 are two different powers. -/
#guard
  let g := addPermanent afterDraw lootTheNexus ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g llanowarElves ⟨0⟩ ⟨0⟩
  let g := mustApply g ⟨0⟩ (.tapForMana (namedPermanent g "Loot, the Nexus").id (.colored .blue))
  (g.player ⟨0⟩).manaPool.total == 2
#guard (fraRuling 875).comment.contains "A creature has different power from another"

/-!
## Proft, Consulting Detective (ruling 836)
-/

/-- Proft's ability waits until the scry is finished, then Chandra may pay
{2} to put a +1/+1 counter on Proft and draw. -/
def proftScrying : Game :=
  let g := addPermanent afterDraw proftConsultingDetective ⟨0⟩ ⟨0⟩
  withMana (g.beginScry ⟨0⟩ 1) ⟨0⟩ .blue 2

#guard proftScrying.pending == .scry ⟨0⟩ 1 && proftScrying.stack.isEmpty
#guard rejects proftScrying ⟨0⟩
  (.surveil (proftScrying.scryLookedIds ⟨0⟩ 1) #[]) "use scry"
#guard
  let g := mustApply proftScrying ⟨0⟩ (.scry (proftScrying.scryLookedIds ⟨0⟩ 1) #[])
  let hand := (g.player ⟨0⟩).hand.size
  let g := passBoth g
  let g := mustApply g ⟨0⟩ .payGeneric
  (namedPermanent g "Proft, Consulting Detective").status.plusOnePlusOne == 1 &&
    (g.player ⟨0⟩).hand.size == hand + 1
#guard (fraRuling 836).comment.contains "Proft's ability goes on the stack after you finish scrying or surveilling"

/-!
## Fblthp, Impossibly Lost (ruling 835)
-/

/-- Fblthp's combat damage triggers its ability. With one card left, the
second draw is from an empty library, but Chandra wins as it resolves,
before that state-based action. -/
def fblthpWins : Game :=
  let g := afterDraw.modifyPlayer ⟨0⟩ (fun pl => { pl with library := #[] })
  let g := addToLibraryTop g forest ⟨0⟩
  let g := addPermanent g fblthpImpossiblyLost ⟨0⟩ ⟨0⟩
  resolveStack (attackWith g #["Fblthp, Impossibly Lost"]) 20

#guard fblthpWins.result == some (.won ⟨0⟩)
#guard (fraRuling 835).comment.contains "this happens before those state-based actions"

/- With cards left, Chandra draws two and Fblthp is shuffled into her
library. -/
#guard
  let g := addPermanent afterDraw fblthpImpossiblyLost ⟨0⟩ ⟨0⟩
  let lib := (g.player ⟨0⟩).library.size
  let g := resolveStack (attackWith g #["Fblthp, Impossibly Lost"]) 20
  g.result.isNone && !g.battlefield.any (fun o => o.name == "Fblthp, Impossibly Lost") &&
    (g.player ⟨0⟩).library.size == lib - 2 + 1

/-!
## Roiling Canopy (rulings 818–820)
-/

def withForests (g : Game) (n : Nat) : Game :=
  (List.range n).foldl (fun g _ => addPermanent g forest ⟨0⟩ ⟨0⟩) g

def canopyBoard (forests : Nat) : Game :=
  let g := addPermanent afterDraw roilingCanopy ⟨0⟩ ⟨0⟩
  withForests (addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩) forests

/- Ruling 818: with five other Forests, a Forest entering triggers it; with
four, it doesn't trigger. -/
#guard
  let g := resolveStack (playLandNamed (canopyBoard 5) forest) 20
  g.power (namedPermanent g "Grizzly Bears") == 5
#guard
  let g := playLandNamed (canopyBoard 4) forest
  g.stack.isEmpty && g.waitingTriggers.isEmpty
#guard (fraRuling 818).comment.contains "intervening 'if' clause"

/-- Ruling 819: if the Forest that caused it leaves, the count is the same;
if another Forest leaves, the count drops and the ability does nothing. -/
def canopyTriggered : Game :=
  let g := playLandNamed (canopyBoard 5) forest
  match g.pending with
  | .chooseTargets _ => mustApply g ⟨0⟩ (.target (.permanent (namedPermanent g "Grizzly Bears").id))
  | _ => g

#guard
  let newest := (canopyTriggered.battlefield.filter (fun o => o.name == "Forest")).back!
  let (g, _) := canopyTriggered.move newest.id (.graveyard ⟨0⟩) none
  let g := resolveStack g 20
  g.power (namedPermanent g "Grizzly Bears") == 5
#guard
  let oldest := (canopyTriggered.battlefield.filter (fun o => o.name == "Forest"))[0]!
  let (g, _) := canopyTriggered.move oldest.id (.graveyard ⟨0⟩) none
  let g := resolveStack g 20
  g.power (namedPermanent g "Grizzly Bears") == 2
#guard (fraRuling 819).comment.contains "Roiling Canopy's count isn't affected"

/- Ruling 820: two Forests entering together each trigger it, each counting
the other. -/
#guard
  let g := canopyBoard 4
  let g := addPermanent (addPermanent g forest ⟨0⟩ ⟨0⟩) forest ⟨0⟩ ⟨0⟩
  let forests := g.battlefield.filter (fun o => o.name == "Forest")
  let g := g.afterLandEnters forests[4]!
  let g := g.afterLandEnters (g.object! forests[5]!.id)
  let g := resolveStack (g.receivePriority ⟨0⟩) 30
  g.power (namedPermanent g "Grizzly Bears") == 8
#guard (fraRuling 820).comment.contains "takes into consideration the other Forests that entered at the same time"

/-!
## Grim Repriser (ruling 805)
-/

def repriserInGraveyard : Game :=
  withMana (withMana (addToGraveyard afterDraw grimRepriser ⟨0⟩) ⟨0⟩ .black 1) ⟨0⟩ .red 1

/- It can't be activated until an opponent is dealt noncombat damage this
turn; it didn't need to be in the graveyard then. It returns with a
finality counter. -/
#guard rejects repriserInGraveyard ⟨0⟩
  (.activate (graveyardCard repriserInGraveyard ⟨0⟩ "Grim Repriser").id 0) "noncombat damage"
#guard
  let g := repriserInGraveyard.dealDamageToPlayer ⟨1⟩ 1
  let g := mustApply g ⟨0⟩ (.activate (graveyardCard g ⟨0⟩ "Grim Repriser").id 0)
  let g := resolveStack (mustApply g ⟨0⟩ .pay) 20
  (namedPermanent g "Grim Repriser").status.finality == 1
#guard (fraRuling 805).comment.contains "doesn't need to have been in your graveyard"

/-!
## Cryotheory Adept and stun counters (ruling 764)
-/

/-- Nissa's Grizzly Bears is already tapped; it can still be targeted and
gets a stun counter. Cryotheory Adept is exiled from the graveyard to pay. -/
def adeptStunned : Game :=
  let g := withBlueMana (addToGraveyard afterDraw cryotheoryAdept ⟨0⟩) ⟨0⟩ 4
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := g.mapObjectStatus (namedPermanent g "Grizzly Bears") (fun s => { s with tapped := true })
  let g := mustApply g ⟨0⟩ (.activate (graveyardCard g ⟨0⟩ "Cryotheory Adept").id 0)
  let g := mustApply g ⟨0⟩ (.target (.permanent (namedPermanent g "Grizzly Bears").id))
  resolveStack (mustApply g ⟨0⟩ .pay) 20

#guard (namedPermanent adeptStunned "Grizzly Bears").status.stun == 1
#guard adeptStunned.objects.any (fun o => o.zone == .exile && o.name == "Cryotheory Adept")
#guard (fraRuling 764).comment.contains "doesn't need to be untapped"

/- In Nissa's untap step the stun counter is removed instead (CR 122.1d). -/
#guard
  let g := skipTo (passBoth (skipTo adeptStunned .end 80)) .upkeep 80
  let bears := namedPermanent g "Grizzly Bears"
  g.activePlayer == ⟨1⟩ && bears.status.tapped && bears.status.stun == 0

/- Campus Crier empowers Jace from the graveyard, exiling itself. -/
#guard
  let g := withMana (addToGraveyard afterDraw campusCrier ⟨0⟩) ⟨0⟩ .white 1
  let g := mustApply g ⟨0⟩ (.activate (graveyardCard g ⟨0⟩ "Campus Crier").id 0)
  let g := resolveStack (mustApply g ⟨0⟩ .pay) 20
  (jaceTokenOf g).status.loyaltyCounters == 2 &&
    g.objects.any (fun o => o.zone == .exile && o.name == "Campus Crier")

/-!
## Enlightened Confidant (ruling 750)
-/

/-- Chandra controls Enlightened Confidant with `top` on top of her library,
having gained `life`, and moves to her end step. -/
def confidantEndStep (life : Nat) (top : CardDef) : Game :=
  let g := addPermanent afterDraw enlightenedConfidant ⟨0⟩ ⟨0⟩
  let g := addToLibraryTop g top ⟨0⟩
  skipTo (g.gainLife ⟨0⟩ life) .end 80

/- Without life gained this turn, it doesn't trigger. -/
#guard (confidantEndStep 0 grizzlyBears).stack.isEmpty
/- Gaining 3 life: Grizzly Bears (mana value 2) surveiled into the graveyard
goes to Chandra's hand. -/
#guard
  let g := passBoth (confidantEndStep 3 grizzlyBears)
  let g := mustApply g ⟨0⟩ (.surveil #[] (g.scryLookedIds ⟨0⟩ 1))
  (g.player ⟨0⟩).hand.any (fun id => (g.object! id).name == "Grizzly Bears")
/- The life gained is checked as it resolves: gaining 1 more with the
ability on the stack lets Hill Giant (mana value 4) come back. -/
#guard
  let g := confidantEndStep 3 hillGiant
  let g := passBoth (g.gainLife ⟨0⟩ 1)
  let g := mustApply g ⟨0⟩ (.surveil #[] (g.scryLookedIds ⟨0⟩ 1))
  (g.player ⟨0⟩).hand.any (fun id => (g.object! id).name == "Hill Giant")
#guard
  let g := passBoth (confidantEndStep 3 hillGiant)
  let g := mustApply g ⟨0⟩ (.surveil #[] (g.scryLookedIds ⟨0⟩ 1))
  (g.player ⟨0⟩).graveyard.any (fun id => (g.object! id).name == "Hill Giant")
#guard (fraRuling 750).comment.contains "the last part of the ability will check how much life you've gained as the ability resolves"

/-!
## Compel Brutality (ruling 791)
-/

/-- Chandra's Grizzly Bears targets Nissa's Hill Giant with the first mode. -/
def compelCast (mode : Nat) (src dst : String) (g : Game) : Game :=
  let g := withGreenMana (addToHand (emptyHand g ⟨0⟩) compelBrutality ⟨0⟩) ⟨0⟩ 2
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Compel Brutality").id)
  let g := mustApply g ⟨0⟩ (.chooseMode mode)
  let g := mustApply g ⟨0⟩ (.target (.permanent (namedPermanent g src).id))
  let g := mustApply g ⟨0⟩ (.target (.permanent (namedPermanent g dst).id))
  mustApply g ⟨0⟩ .pay

def bearsVsGiant : Game :=
  addPermanent (addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩) hillGiant ⟨1⟩ ⟨1⟩

/- The power is checked as the spell resolves: pumped to 4, the Bears kill
the Giant. -/
#guard
  let g := compelCast 0 "Grizzly Bears" "Hill Giant" bearsVsGiant
  let g := g.mapObjectStatus (namedPermanent g "Grizzly Bears") (fun s => s.addPump 2 0)
  let g := passBoth g
  !g.battlefield.any (fun o => o.name == "Hill Giant")
/- If the Bears leave first, no damage is dealt. -/
#guard
  let g := compelCast 0 "Grizzly Bears" "Hill Giant" bearsVsGiant
  let (g, _) := g.move (namedPermanent g "Grizzly Bears").id (.graveyard ⟨0⟩) none
  let g := passBoth g
  (namedPermanent g "Hill Giant").status.damage == 0
/- The second mode uses a planeswalker's loyalty. -/
#guard
  let g := addPermanent (afterDraw.empowerJace ⟨0⟩ 3) hillGiant ⟨1⟩ ⟨1⟩
  let g := compelCast 1 "Jace" "Hill Giant" g
  let g := passBoth g
  !g.battlefield.any (fun o => o.name == "Hill Giant")
#guard (fraRuling 791).comment.contains "checked as the spell resolves"

end Mtg.Engine.FraRulingTests
