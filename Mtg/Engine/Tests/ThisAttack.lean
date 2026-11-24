import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Fixture
import Mtg.Engine.Game
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns

/-!
# Unified attack triggers

Ant-Man and Grim Reaper pay into a reflexive ability. Iron Man draws when
an artifact entered. Thor blinks a nontoken. Whiplash drains for Equipment.
Viv draws at power 4. Luke Cage gets +2/+0 and indestructible.
-/

namespace Mtg.Engine.ThisAttackTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def me : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def resolve (g : Game) (ab : TriggeredAbility) (sourceId : Option ObjectId := none)
    (targets : Array Target := #[]) (lastKnownPower : Option Int := none) : Game :=
  g.applyTriggeredAbility me ab sourceId targets #[] lastKnownPower

def named (g : Game) (name : String) : GameObject :=
  namedPermanent g name

def hand (g : Game) : Nat :=
  (g.player me).hand.size

/- The attack triggers carry unified `Instruction` bodies and keep their Oracle lines. -/
#guard (TriggeredAbility.onThisAttack Effect.thisAttackMayPayPlusOne).effect.body == Effect.thisAttackMayPayPlusOne.body
#guard (TriggeredAbility.onThisAttack Effect.thisAttackPayReturnAttacking).effect.body == Effect.thisAttackPayReturnAttacking.body
#guard (TriggeredAbility.onThisAttack Effect.thisAttackIfArtifactEnteredDraw).effect.body == Effect.thisAttackIfArtifactEnteredDraw.body
#guard (TriggeredAbility.onThisAttack Effect.thisAttackBlinkNontoken).effect.body == Effect.thisAttackBlinkNontoken.body
#guard (TriggeredAbility.onThisAttack Effect.thisAttackEquippedDrain).effect.body == Effect.thisAttackEquippedDrain.body
#guard (TriggeredAbility.onThisAttack Effect.thisAttackDrawIfPower4).effect.body == Effect.thisAttackDrawIfPower4.body
#guard (TriggeredAbility.onThisAttack Effect.thisAttackAttacksAlonePlus2Indestructible).effect.body ==
  Effect.thisAttackAttacksAlonePlus2Indestructible.body

/- Ant-Man may pay {1}. Declining queues nothing. Paying queues the
+1/+1 counter. -/
def antManOffer : Game :=
  let g := addPermanent afterDraw antManColonyCommander me me
  resolve g (TriggeredAbility.onThisAttack Effect.thisAttackMayPayPlusOne)
    (some (named g "Ant-Man, Colony Commander").id)

#guard
  match antManOffer.pending with
  | .resolutionChoice q (.mayPayManaForReflexive cost _ eff _) =>
    q == me && cost == #[.generic 1] && eff.body == Instruction.putPlusOne (.target 0) 1
  | _ => false

def antManDeclines : Game :=
  mustApply antManOffer me .decline

#guard antManDeclines.pending == .none && !antManDeclines.hasModeledReflexiveOnStack &&
  logContains antManDeclines "isn't paid"

def antManPays : Game :=
  let g := antManOffer.addMana me (.colored .green) 1
  let g := mustApply g me .accept
  passBoth (mustApply g me (.target (Target.permanent (named g "Ant-Man, Colony Commander").id)))

#guard antManPays.hasModeledReflexiveOnStack == false &&
  (named antManPays "Ant-Man, Colony Commander").status.plusOnePlusOne == 1

/- Grim Reaper may pay {3}{B}. The return is the reflexive ability. -/
def reaperOffer : Game :=
  let g := addPermanent afterDraw grimReaperLethalLegionnaire me me
  resolve g (TriggeredAbility.onThisAttack Effect.thisAttackPayReturnAttacking)
    (some (named g "Grim Reaper, Lethal Legionnaire").id)

#guard
  match reaperOffer.pending with
  | .resolutionChoice q (.mayPayManaForReflexive cost _ eff _) =>
    q == me && cost == #[.generic 3, .colored .black] &&
      eff.targets == .creatureCardInYourGraveyard
  | _ => false

/- Iron Man's draw is an intervening if: it does not trigger without an
artifact, and it draws when one entered. -/
def ironQuiet : Bool :=
  let g := addPermanent afterDraw ironManMasterOfMachines me me
  let iron := named g "Iron Man, Master of Machines"
  let ab := TriggeredAbility.onThisAttack Effect.thisAttackIfArtifactEnteredDraw
  let skipped := !g.triggerConditionHolds me ab none (some iron)
  let hand0 := hand g
  let g := resolve g ab (some iron.id)
  skipped && hand g == hand0 &&
    logContains g "No artifact entered"

def ironDraws : Bool :=
  let g := addPermanent afterDraw ironManMasterOfMachines me me
  let g := g.record (GameEvent.moved g.turnNumber
    { id := some ⟨40⟩, controller := some me, owner := me, types := #[.artifact] }
    (.hand me) .battlefield (cause := .oneShotEffect none none (some me)))
  let iron := named g "Iron Man, Master of Machines"
  let ab := TriggeredAbility.onThisAttack Effect.thisAttackIfArtifactEnteredDraw
  let hand0 := hand g
  let g := resolve g ab (some iron.id)
  g.triggerConditionHolds me ab none (some iron) && hand g == hand0 + 1

#guard ironQuiet
#guard ironDraws

/- Viv draws only when her power is 4 or greater, including last-known power. -/
def vivSmall : Bool :=
  let g := addPermanent afterDraw vivVisionTeenSynthezoid me me
  let viv := named g "Viv Vision, Teen Synthezoid"
  let hand0 := hand g
  let g := resolve g (TriggeredAbility.onThisAttack Effect.thisAttackDrawIfPower4) (some viv.id)
  hand g == hand0 && logContains g "not 4 or greater"

#guard vivSmall

def vivLeft : Bool :=
  let g := addPermanent afterDraw vivVisionTeenSynthezoid me me
  let viv := named g "Viv Vision, Teen Synthezoid"
  let g := g.addPlusOnePlusOneTo viv 2
  let pw := g.power (named g "Viv Vision, Teen Synthezoid")
  let hand0 := hand g
  let (g, _) := g.move (named g "Viv Vision, Teen Synthezoid").id (.graveyard me) none
  let g := resolve g (TriggeredAbility.onThisAttack Effect.thisAttackDrawIfPower4)
    (some viv.id) #[] (some pw)
  pw ≥ 4 && hand g == hand0 + 1

#guard vivLeft

/- Whiplash does nothing while unequipped. Equipped, each opponent loses
that many life and Whiplash's controller gains it. A source that left uses
the last-known count. -/
def whipBare : Bool :=
  let g := addPermanent afterDraw whiplashVengefulEngineer me me
  let life := (g.player opp).life
  let you := (g.player me).life
  let g := resolve g (TriggeredAbility.onThisAttack Effect.thisAttackEquippedDrain)
    (some (named g "Whiplash, Vengeful Engineer").id)
  (g.player opp).life == life && (g.player me).life == you &&
    logContains g "isn't equipped"

#guard whipBare

def whipEquipped : Bool :=
  let g := addPermanent (addPermanent afterDraw whiplashVengefulEngineer me me)
    captainAmericaSShield me me
  let whip := named g "Whiplash, Vengeful Engineer"
  let shield := named g "Captain America's Shield"
  let g := g.attachSourceTo shield whip
  let n := g.attachedEquipmentCount (named g "Whiplash, Vengeful Engineer")
  let life := (g.player opp).life
  let you := (g.player me).life
  let g := resolve g (TriggeredAbility.onThisAttack Effect.thisAttackEquippedDrain)
    (some whip.id)
  n == 1 && (g.player opp).life + n == life && (g.player me).life == you + n

#guard whipEquipped

def whipLeft : Bool :=
  let g := addPermanent (addPermanent (addPermanent afterDraw whiplashVengefulEngineer me me)
    captainAmericaSShield me me) falconSWingHarness me me
  let whip := named g "Whiplash, Vengeful Engineer"
  let eq1 := named g "Captain America's Shield"
  let eq2 := named g "Falcon's Wing Harness"
  let g := (g.attachSourceTo eq1 whip).attachSourceTo (g.object! eq2.id) (g.object! whip.id)
  let life := (g.player opp).life
  let you := (g.player me).life
  let (g, _) := g.move whip.id (.graveyard me) none
  let g := resolve g (TriggeredAbility.onThisAttack Effect.thisAttackEquippedDrain)
    (some whip.id)
  (g.player opp).life + 2 == life && (g.player me).life == you + 2

#guard whipLeft

/- Luke Cage gets +2/+0 and indestructible until end of turn. -/
def luke : Game :=
  let g := addPermanent afterDraw lukeCagePowerMan me me
  resolve g (TriggeredAbility.onThisAttack Effect.thisAttackAttacksAlonePlus2Indestructible)
    (some (named g "Luke Cage, Power Man").id)

#guard luke.pumpOf (named luke "Luke Cage, Power Man") == (2, 0) &&
  KeywordAbility.hasIndestructible (luke.currentKeywords (named luke "Luke Cage, Power Man"))

end Mtg.Engine.ThisAttackTests
