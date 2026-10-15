import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Fixture
import Mtg.Engine.Game
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns

/-!
# Attack triggers without `ThisAttackLeftover`

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

/- The shared attack effects resolve as constructors that do not carry
`ThisAttackLeftover`. The printed sentence stays the Oracle line. -/
#guard TriggeredAbility.resolution (TriggeredAbility.onThisAttack Effect.thisAttackMayPayPlusOne) ==
  .may (.pay #[.generic 1]) (.queueReflexive (.modeled 12)) .ifYouDo
#guard TriggeredAbility.resolution (TriggeredAbility.onThisAttack Effect.thisAttackPayReturnAttacking) ==
  .may (.pay #[.generic 3, .colored .black]) (.queueReflexive (.modeled 6)) .ifYouDo
#guard TriggeredAbility.resolution (TriggeredAbility.onThisAttack Effect.thisAttackIfArtifactEnteredDraw) ==
  .«if» .artifactEnteredThisTurn (.draw (.fixed 1))
#guard TriggeredAbility.resolution (TriggeredAbility.onThisAttack Effect.thisAttackBlinkNontoken) ==
  .exile .target .returnTapped
#guard TriggeredAbility.resolution (TriggeredAbility.onThisAttack Effect.thisAttackEquippedDrain) ==
  .«if» .attachedEquipment (.sequence [
    .loseLife 0 (who := .eachOpponent) (amount := .attachedEquipment),
    .gainLife 0 (amount := .attachedEquipment)])
#guard TriggeredAbility.resolution (TriggeredAbility.onThisAttack Effect.thisAttackDrawIfPower4) ==
  .«if» (.sourcePowerAtLeast 4) (.draw (.fixed 1))
#guard TriggeredAbility.resolution
    (TriggeredAbility.onThisAttack Effect.thisAttackAttacksAlonePlus2Indestructible) ==
  .sequence [.pump (.fixed 2) (.fixed 0) .source, .grant (.keywords Keyword.indestructible) .source]

#guard toString (TriggeredAbility.onThisAttack Effect.thisAttackMayPayPlusOne) ==
  TriggeredAbility.thisAttackSentence .mayPayPlusOne
#guard toString (TriggeredAbility.onThisAttack Effect.thisAttackPayReturnAttacking) ==
  TriggeredAbility.thisAttackSentence .payReturnAttacking
#guard toString (TriggeredAbility.onThisAttack Effect.thisAttackIfArtifactEnteredDraw) ==
  TriggeredAbility.thisAttackSentence .ifArtifactEnteredDraw
#guard toString (TriggeredAbility.onThisAttack Effect.thisAttackBlinkNontoken) ==
  TriggeredAbility.thisAttackSentence .blinkNontoken
#guard toString (TriggeredAbility.onThisAttack Effect.thisAttackEquippedDrain) ==
  TriggeredAbility.thisAttackSentence .equippedDrain
#guard toString (TriggeredAbility.onThisAttack Effect.thisAttackDrawIfPower4) ==
  TriggeredAbility.thisAttackSentence .drawIfPower4
#guard toString (TriggeredAbility.onThisAttack Effect.thisAttackAttacksAlonePlus2Indestructible) ==
  TriggeredAbility.thisAttackSentence .attacksAlonePlus2Indestructible

/- Ant-Man may pay {1}. Declining queues nothing. Paying queues the
+1/+1 counter. -/
def antManOffer : Game :=
  let g := addPermanent afterDraw antManColonyCommander me me
  resolve g (TriggeredAbility.onThisAttack Effect.thisAttackMayPayPlusOne)
    (some (named g "Ant-Man, Colony Commander").id)

#guard
  match antManOffer.pending with
  | .fraChoice q (.mayPayManaForReflexive cost _ 12 _) =>
    q == me && cost == #[.generic 1]
  | _ => false

def antManDeclines : Game :=
  mustApply antManOffer me .decline

#guard antManDeclines.pending == .none && !antManDeclines.hasModeledReflexiveOnStack &&
  logContains antManDeclines "isn't paid"

def antManPays : Game :=
  let g := antManOffer.modifyPlayer me (fun pl =>
    { pl with manaPool := pl.manaPool.add (.colored .green) 1 })
  let g := mustApply g me .accept
  g.applyModeledReflexive #[Target.permanent (named g "Ant-Man, Colony Commander").id]

#guard antManPays.hasModeledReflexiveOnStack == false &&
  (named antManPays "Ant-Man, Colony Commander").status.plusOnePlusOne == 1

/- Grim Reaper may pay {3}{B}. The return is the reflexive ability. -/
def reaperOffer : Game :=
  let g := addPermanent afterDraw grimReaperLethalLegionnaire me me
  resolve g (TriggeredAbility.onThisAttack Effect.thisAttackPayReturnAttacking)
    (some (named g "Grim Reaper, Lethal Legionnaire").id)

#guard
  match reaperOffer.pending with
  | .fraChoice q (.mayPayManaForReflexive cost _ 6 _) =>
    q == me && cost == #[.generic 3, .colored .black]
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
  let g := g.modifyPlayer me (fun pl => { pl with artifactEnteredThisTurn := true })
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
  let g := addPermanent afterDraw whiplashVengefulEngineer me me
  let whip := named g "Whiplash, Vengeful Engineer"
  let life := (g.player opp).life
  let you := (g.player me).life
  let (g, _) := g.move whip.id (.graveyard me) none
  let g := resolve g (TriggeredAbility.onThisAttack Effect.thisAttackEquippedDrain)
    (some whip.id) #[] (some 2)
  (g.player opp).life + 2 == life && (g.player me).life == you + 2

#guard whipLeft

/- Luke Cage gets +2/+0 and indestructible until end of turn. -/
def luke : Game :=
  let g := addPermanent afterDraw lukeCagePowerMan me me
  resolve g (TriggeredAbility.onThisAttack Effect.thisAttackAttacksAlonePlus2Indestructible)
    (some (named g "Luke Cage, Power Man").id)

#guard (named luke "Luke Cage, Power Man").status.pump == (2, 0) &&
  (named luke "Luke Cage, Power Man").status.untilEotKeywords.indestructible

end Mtg.Engine.ThisAttackTests
