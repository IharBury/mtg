import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# `TriggerResolution.gainLife`

How much life is a `NumberSelector`.
A fixed amount, life equal to the targeted card's power, one life for each
permanent an earlier step destroyed, one life for each other creature you
control, and life for each Equipment attached to the source.
Any other selector gains nothing.
-/

namespace Mtg.Engine.GainLifeTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests hiding afterDraw

def afterDraw : Game := Mtg.Engine.Tests.afterDraw.change (.pushContinuationFrame {})

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def life (g : Game) : Int :=
  (g.player caster).life

def step (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[])
    (cardPower : Option Nat := none) (ab : TriggeredAbility := .onEnterDraw 1) : Game :=
  g.applyTriggeredAbility caster ab sourceId targets
    (resolutionOverride := some r) (sequencedCardPower := cardPower)

def putInGraveyard (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.graveyard p)

def namedIn (g : Game) (ids : Array ObjectId) (name : String) : ObjectId :=
  match ids.find? (fun id => (g.findObject? id).any (·.name == name)) with
  | some id => id
  | none => panic! s!"missing {name}"

def inHand (g : Game) (name : String) : Bool :=
  (g.player caster).hand.any (fun id => (g.findObject? id).any (·.name == name))

def inGraveyard (g : Game) (name : String) : Bool :=
  (g.player caster).graveyard.any (fun id => (g.findObject? id).any (·.name == name))

def pid (g : Game) (name : String) : ObjectId :=
  match g.battlefield.find? (·.name == name) with
  | some o => o.id
  | none => panic! s!"missing {name}"

def counters (g : Game) (name : String) : Nat :=
  match g.battlefield.find? (·.name == name) with
  | some o => o.status.plusOnePlusOne
  | none => panic! s!"missing {name}"

def elf : CardDef := creature "Lorien Elf" ManaCost.empty #["Elf"] 4 4
def bear : CardDef := creature "Cave Bear" ManaCost.empty #["Bear"] 2 2

def equalPower : TriggeredAbility.TriggerResolution :=
  .gainLife .equalToTargetPower

def perDestroyed : TriggeredAbility.TriggerResolution :=
  .gainLife .forEachDestroyedThisWay

def perOther : TriggeredAbility.TriggerResolution :=
  .gainLife .perOtherCreature

/- The controller gains the printed amount. Gaining none changes nothing.
A selector this resolution does not read gains nothing. -/
#guard
  let g := step afterDraw (.gainLife (.fixed 4))
  life g == life afterDraw + 4 && logContains g "gains 4 life"

#guard
  let g := step afterDraw (.gainLife (.fixed 0))
  life g == life afterDraw && g.log == afterDraw.log

#guard
  let g := step afterDraw (.gainLife .greatestPower)
  life g == life afterDraw && g.log == afterDraw.log

/- Life equal to the targeted card's power. The amount noted when a sequence
starts is used even when that card's current power is different. A missing
target, and a card that has left the graveyard, gain nothing. -/
#guard
  let g0 := putInGraveyard afterDraw elf caster
  let id := namedIn g0 (g0.player caster).graveyard "Lorien Elf"
  let g := step g0 equalPower (targets := #[Target.card id])
    (ab := .onEnterOrAttackReturnElfGainLife)
  life g == life g0 + 4 && inGraveyard g "Lorien Elf"

#guard
  let g0 := putInGraveyard afterDraw elf caster
  let id := namedIn g0 (g0.player caster).graveyard "Lorien Elf"
  let g := step g0 equalPower (targets := #[Target.card id]) (cardPower := some 9)
    (ab := .onEnterOrAttackReturnElfGainLife)
  life g == life g0 + 9

#guard
  let g := step afterDraw equalPower (cardPower := some 5)
  life g == life afterDraw + 5

#guard
  let g := step afterDraw equalPower (ab := .onEnterOrAttackReturnElfGainLife)
  life g == life afterDraw && logContains g "The target is no longer legal"

#guard
  let g0 := putInGraveyard afterDraw elf caster
  let id := namedIn g0 (g0.player caster).graveyard "Lorien Elf"
  let (g1, _) := g0.move id .exile none
  let g := step g1 equalPower (targets := #[Target.card id])
    (ab := .onEnterOrAttackReturnElfGainLife)
  life g == life g1 && logContains g "no longer in the graveyard"

/- The return-then-gain sequence uses that power, then the card is in hand.
An illegal graveyard card skips both steps. -/
#guard
  let g0 := putInGraveyard afterDraw elf caster
  let id := namedIn g0 (g0.player caster).graveyard "Lorien Elf"
  let g := g0.applyTriggeredAbility caster .onEnterOrAttackReturnElfGainLife none
    #[Target.card id]
  life g == life g0 + 4 && inHand g "Lorien Elf" && !inGraveyard g "Lorien Elf"

#guard
  let g0 := putInGraveyard afterDraw bear caster
  let id := namedIn g0 (g0.player caster).graveyard "Cave Bear"
  let g := g0.applyTriggeredAbility caster .onEnterOrAttackReturnElfGainLife none
    #[Target.card id]
  life g == life g0 && inGraveyard g "Cave Bear" && !inHand g "Cave Bear" &&
    logContains g "no longer legal"

/- One life for each permanent an earlier step destroyed. None clears the
note and gains nothing. -/
#guard
  let g0 := afterDraw.change (.permanentsDestroyedThisWay 3)
  let g := step g0 perDestroyed
  life g == life g0 + 3 && g.permanentsDestroyedThisWay == 0

#guard
  let g := step afterDraw perDestroyed
  life g == life afterDraw && g.permanentsDestroyedThisWay == 0

/- One life for each other creature the controller controls. The source and
opposing creatures are not counted. None gains nothing. -/
#guard
  let g0 := addPermanent afterDraw (creature "Source" ManaCost.empty #[] 2 2) caster caster
  let g0 := addPermanent g0 (creature "Ally" ManaCost.empty #[] 1 1) caster caster
  let g0 := addPermanent g0 (creature "Foe" ManaCost.empty #[] 1 1) opp opp
  let g := step g0 perOther (some (pid g0 "Source"))
  life g == life g0 + 1

#guard
  let g0 := addPermanent afterDraw (creature "Source" ManaCost.empty #[] 2 2) caster caster
  let g0 := addPermanent g0 (creature "Ally" ManaCost.empty #[] 1 1) caster caster
  let g := step g0 perOther
  life g == life g0 + 2

#guard
  let g0 := addPermanent afterDraw (creature "Source" ManaCost.empty #[] 2 2) caster caster
  let g := step g0 perOther (some (pid g0 "Source"))
  life g == life g0

#guard
  let g0 := addPermanent afterDraw (creature "Source" ManaCost.empty #[] 2 2) caster caster
  let g0 := addPermanent g0 (creature "Ally" ManaCost.empty #[] 1 1) caster caster
  let g0 := addPermanent g0 (creature "Foe" ManaCost.empty #[] 1 1) opp opp
  let g := g0.applyTriggeredAbility caster .onEnterOrAttackPlusOneEachOtherGainLife
    (some (pid g0 "Source"))
  life g == life g0 + 1 && counters g "Ally" == 1 && counters g "Source" == 0 &&
    counters g "Foe" == 0

#guard TriggeredAbility.resolutionPhrase { resolution := .gainLife (.fixed 3) } ==
  "you gain 3 life"

#guard TriggeredAbility.resolutionPhrase { resolution := .gainLife .greatestPower } ==
  "you gain life"

#guard TriggeredAbility.resolutionPhrase { resolution := equalPower } ==
  "you gain life equal to that card's power"

#guard TriggeredAbility.resolutionPhrase { resolution := perDestroyed } ==
  "you gain 1 life for each permanent destroyed this way"

#guard TriggeredAbility.resolutionPhrase { resolution := perOther } ==
  "you gain 1 life for each other creature you control"

#guard (SharedTrigger.timing .returnElfGainLife).resolution ==
  .sequence [.returnToHand .graveyardCard, equalPower]

#guard (SharedTrigger.timing .destroyOppArtifactsEnchantmentsGainLife).resolution ==
  .sequence [.destroy .oppArtifactsEnchantments (note := .countDestroyed), perDestroyed]

#guard (SharedTrigger.timing .plusOneEachOtherGainLife).resolution ==
  .sequence [.putCounters (.ofKind .plusOnePlusOne) .eachOther, perOther]

end Mtg.Engine.GainLifeTests
