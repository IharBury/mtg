import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# `TriggerResolution.destroy`

Which permanents are destroyed is an `ObjectSelector`. Opponents' artifacts
and enchantments, the permanent an earlier step dealt damage to, and the
announced creature. Any other selector destroys nothing. What a later step
can read is still a note.
-/

namespace Mtg.Engine.DestroyTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def step (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[])
    (lastKnownPower : Option Int := none) : Game :=
  g.applyTriggeredAbility caster (.onEnterDraw 1) sourceId targets
    (lastKnownPower := lastKnownPower) (resolutionOverride := some r)

def onBoard (g : Game) (name : String) : Bool :=
  g.battlefield.any (·.name == name)

def buried (g : Game) (name : String) : Bool :=
  g.objects.any (fun o =>
    o.name == name &&
      match o.zone with
      | .graveyard _ => true
      | _ => false)

def exiled (g : Game) (name : String) : Bool :=
  g.objects.any (fun o => o.name == name && o.zone == .exile)

def pid (g : Game) (name : String) : ObjectId :=
  match g.battlefield.find? (·.name == name) with
  | some o => o.id
  | none => panic! s!"missing {name}"

def obj (g : Game) (name : String) : GameObject :=
  match g.battlefield.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing {name}"

def oppArts : TriggeredAbility.TriggerResolution :=
  .destroy .oppArtifactsEnchantments (note := .countDestroyed)

def markedDestroy : TriggeredAbility.TriggerResolution :=
  .destroy .permanentDealtDamage

def notedDestroy : TriggeredAbility.TriggerResolution :=
  .destroy .target (note := .forAmass)

def amassSeq : TriggeredAbility.TriggerResolution :=
  .sequence [
    notedDestroy,
    .amass .notedPower (who := .notedController),
    .«if» .youControlledDestroyed (.draw (.fixed 1))]

/- Opponents' artifacts and enchantments are destroyed and counted.
Yours stay. Indestructible permanents and shield counters stay and do
not count. A permanent exiled instead of dying still counts. -/
#guard
  let g0 := addPermanent afterDraw (artifact "Opp Sword" ManaCost.empty "") opp opp
  let g0 := addPermanent g0 (enchantment "Opp Aura" ManaCost.empty "") opp opp
  let g0 := addPermanent g0 (artifactCreature "Opp Construct" ManaCost.empty #[] 1 1) opp opp
  let g0 := addPermanent g0 (artifact "My Sword" ManaCost.empty "") caster caster
  let g0 := addPermanent g0
    (artifact "Hardy Relic" ManaCost.empty "" (keywords := Keyword.indestructible)) opp opp
  let g0 := addPermanent g0 (artifact "Shielded Relic" ManaCost.empty "") opp opp
  let shielded := obj g0 "Shielded Relic"
  let g0 := g0.setObject { shielded with status := { shielded.status with shield := 1 } }
  let g0 := addPermanent g0 (artifact "Fleeting Relic" ManaCost.empty "") opp opp
  let fleeting := obj g0 "Fleeting Relic"
  let g0 := g0.setObject { fleeting with status :=
    { fleeting.status with untilEotExileIfDies := true } }
  let g0 := addPermanent g0 (creature "Opp Bear" ManaCost.empty #[] 2 2) opp opp
  let g := step g0 oppArts
  !onBoard g "Opp Sword" && buried g "Opp Sword" &&
    !onBoard g "Opp Aura" && buried g "Opp Aura" &&
    !onBoard g "Opp Construct" && buried g "Opp Construct" &&
    !onBoard g "Fleeting Relic" && exiled g "Fleeting Relic" &&
    onBoard g "My Sword" && onBoard g "Hardy Relic" && onBoard g "Shielded Relic" &&
    onBoard g "Opp Bear" &&
    (obj g "Shielded Relic").status.shield == 0 &&
    g.permanentsDestroyedThisWay == 4 &&
    logContains g "is indestructible and isn't destroyed" &&
    logContains g "shield counter is removed"

/- The following life step spends that count, including when nothing left. -/
#guard
  let g0 := addPermanent afterDraw (artifact "Opp Sword" ManaCost.empty "") opp opp
  let g := step g0 (.sequence [oppArts, .gainLife .forEachDestroyedThisWay])
  (g.player caster).life == (afterDraw.player caster).life + 1 &&
    g.permanentsDestroyedThisWay == 0 && !onBoard g "Opp Sword"

#guard
  let g := step afterDraw (.sequence [oppArts, .gainLife .forEachDestroyedThisWay])
  (g.player caster).life == (afterDraw.player caster).life &&
    g.permanentsDestroyedThisWay == 0

/- Counting is the note. Without it, nothing is destroyed. -/
#guard
  let g0 := addPermanent afterDraw (artifact "Opp Sword" ManaCost.empty "") opp opp
  let g := step g0 (.destroy .oppArtifactsEnchantments)
  onBoard g "Opp Sword" && g.permanentsDestroyedThisWay == 0

/- The permanent an earlier damage step marked is destroyed, and the mark
is cleared. No mark, a missing object, indestructible, and a shield
counter each leave the permanent in play. -/
#guard
  let g0 := addPermanent afterDraw (creature "Wyrm" ManaCost.empty #["Dragon"] 4 4) opp opp
  let id := pid g0 "Wyrm"
  let g := step { g0 with permanentDealtDamageThisWay := some id } markedDestroy
  !onBoard g "Wyrm" && buried g "Wyrm" && g.permanentDealtDamageThisWay.isNone

#guard
  let g := step afterDraw markedDestroy
  g.permanentDealtDamageThisWay.isNone && g.log == afterDraw.log

#guard
  let g0 := addPermanent afterDraw (creature "Wyrm" ManaCost.empty #["Dragon"] 4 4) opp opp
  let id := pid g0 "Wyrm"
  let (g1, _) := g0.move id (.graveyard opp) none
  let g := step { g1 with permanentDealtDamageThisWay := some id } markedDestroy
  buried g "Wyrm" && g.permanentDealtDamageThisWay.isNone &&
    !(logContains g "is destroyed")

#guard
  let g0 := addPermanent afterDraw
    (creature "Adamant Wyrm" ManaCost.empty #["Dragon"] 4 4
      (keywords := Keyword.indestructible)) opp opp
  let id := pid g0 "Adamant Wyrm"
  let g := step { g0 with permanentDealtDamageThisWay := some id } markedDestroy
  onBoard g "Adamant Wyrm" && g.permanentDealtDamageThisWay.isNone &&
    logContains g "is indestructible and isn't destroyed"

#guard
  let g0 := addPermanent afterDraw (creature "Wyrm" ManaCost.empty #["Dragon"] 4 4) opp opp
  let wyrm := obj g0 "Wyrm"
  let g0 := g0.setObject { wyrm with status := { wyrm.status with shield := 1 } }
  let id := pid g0 "Wyrm"
  let g := step { g0 with permanentDealtDamageThisWay := some id } markedDestroy
  onBoard g "Wyrm" && (obj g "Wyrm").status.shield == 0 &&
    g.permanentDealtDamageThisWay.isNone &&
    logContains g "shield counter is removed"

/- A different note does not destroy the marked permanent. -/
#guard
  let g0 := addPermanent afterDraw (creature "Wyrm" ManaCost.empty #["Dragon"] 4 4) opp opp
  let id := pid g0 "Wyrm"
  let g := step { g0 with permanentDealtDamageThisWay := some id }
    (.destroy .permanentDealtDamage (note := .forAmass))
  onBoard g "Wyrm" && g.permanentDealtDamageThisWay == some id

/- Damage, then destroy only when that damage marked a Dragon.
The ability's target kind is what makes the permanent a legal target. -/
#guard
  let g0 := addPermanent afterDraw (creature "Wyrm" ManaCost.empty #["Dragon"] 4 4) opp opp
  let id := pid g0 "Wyrm"
  let g := g0.applyTriggeredAbility caster
    (.onEnterDealDamageDestroyIfSubtype 1 "Dragon") none #[Target.permanent id]
  !onBoard g "Wyrm" && buried g "Wyrm" && g.permanentDealtDamageThisWay.isNone

#guard
  let g0 := addPermanent afterDraw (creature "Hill" ManaCost.empty #["Giant"] 3 3) opp opp
  let id := pid g0 "Hill"
  let g := g0.applyTriggeredAbility caster
    (.onEnterDealDamageDestroyIfSubtype 1 "Dragon") none #[Target.permanent id]
  onBoard g "Hill" && (obj g "Hill").status.damage == 1 &&
    g.permanentDealtDamageThisWay.isNone && !(logContains g "is destroyed")

/- The announced creature is destroyed and its controller and power are
noted. Last-known power wins. No legal target clears the note. The
controller still amasses when the creature is indestructible. -/
#guard
  let g0 := addPermanent afterDraw (creature "Ogre" ManaCost.empty #[] 2 2) opp opp
  let id := pid g0 "Ogre"
  let g := step g0 notedDestroy (targets := #[Target.permanent id]) (lastKnownPower := some 5)
  !onBoard g "Ogre" && buried g "Ogre" &&
    g.destroyedForAmassThisWay && g.amassControllerThisWay == some opp &&
    g.amassAmountThisWay == 5 && !g.amassYouControlledThisWay

#guard
  let g0 := addPermanent afterDraw (creature "Mine" ManaCost.empty #[] 3 3) caster caster
  let id := pid g0 "Mine"
  let before := (g0.player caster).hand.size
  let g := step g0 amassSeq (targets := #[Target.permanent id])
  !onBoard g "Mine" &&
    onBoard g "Goblin Army" && (obj g "Goblin Army").controlledBy caster &&
    (obj g "Goblin Army").status.plusOnePlusOne == 3 &&
    (g.player caster).hand.size == before + 1 &&
    !g.destroyedForAmassThisWay && g.amassControllerThisWay.isNone &&
    g.amassAmountThisWay == 0 && !g.amassYouControlledThisWay

#guard
  let g0 := addPermanent afterDraw (creature "Ogre" ManaCost.empty #[] 2 2) opp opp
  let id := pid g0 "Ogre"
  let before := (g0.player caster).hand.size
  let g := step g0 amassSeq (targets := #[Target.permanent id]) (lastKnownPower := some 5)
  !onBoard g "Ogre" &&
    g.battlefield.any (fun o => o.name == "Goblin Army" && o.controlledBy opp) &&
    (g.battlefield.find? (·.name == "Goblin Army")).any
      (·.status.plusOnePlusOne == 5) &&
    (g.player caster).hand.size == before && !g.destroyedForAmassThisWay

#guard
  let g0 := addPermanent afterDraw (creature "Tiny" ManaCost.empty #[] 0 1) opp opp
  let id := pid g0 "Tiny"
  let g := step g0 notedDestroy (targets := #[Target.permanent id]) (lastKnownPower := some (-2))
  !onBoard g "Tiny" && g.destroyedForAmassThisWay && g.amassAmountThisWay == 0 &&
    g.amassControllerThisWay == some opp

#guard
  let before := afterDraw.log.size
  let g := step afterDraw notedDestroy
  !g.destroyedForAmassThisWay && g.amassControllerThisWay.isNone &&
    g.amassAmountThisWay == 0 &&
    logContains g "no player amasses" &&
    !(g.battlefield.any (fun o => g.hasSubtype o "Army")) &&
    (g.log.extract before g.log.size).any (fun s => mentions s "no player amasses")

#guard
  let g0 := addPermanent afterDraw (creature "Ogre" ManaCost.empty #[] 2 2) opp opp
  let id := pid g0 "Ogre"
  let (g1, _) := g0.move id (.graveyard opp) none
  let g := step g1 notedDestroy (targets := #[Target.permanent id])
  !g.destroyedForAmassThisWay && g.amassAmountThisWay == 0 &&
    logContains g "no longer legal" &&
    !(g.battlefield.any (fun o => g.hasSubtype o "Army"))

#guard
  let g := step afterDraw notedDestroy (targets := #[Target.player opp])
  !g.destroyedForAmassThisWay && logContains g "no player amasses"

#guard
  let g0 := addPermanent afterDraw
    (creature "Hardy" ManaCost.empty #[] 2 2 (keywords := Keyword.indestructible)) caster caster
  let id := pid g0 "Hardy"
  let before := (g0.player caster).hand.size
  let g := step g0 amassSeq (targets := #[Target.permanent id])
  onBoard g "Hardy" && onBoard g "Goblin Army" &&
    (obj g "Goblin Army").status.plusOnePlusOne == 2 &&
    (g.player caster).hand.size == before + 1 &&
    logContains g "is indestructible and isn't destroyed"

/- Any other selector destroys nothing. -/
#guard
  let g0 := addPermanent afterDraw (creature "Ogre" ManaCost.empty #[] 2 2) opp opp
  let g := step g0 (.destroy .humans)
  onBoard g "Ogre" && g.permanentsDestroyedThisWay == 0 && g.log == g0.log

/- Noting the controller is the note. Without it, the creature stays. -/
#guard
  let g0 := addPermanent afterDraw (creature "Ogre" ManaCost.empty #[] 2 2) opp opp
  let id := pid g0 "Ogre"
  let g := step g0 (.destroy .target) (targets := #[Target.permanent id])
  onBoard g "Ogre" && !g.destroyedForAmassThisWay && g.amassAmountThisWay == 0

#guard (SharedTrigger.timing .destroyOppArtifactsEnchantmentsGainLife).resolution ==
  .sequence [oppArts, .gainLife .forEachDestroyedThisWay]

#guard (SharedTrigger.timing (.dealDamageDestroyIfSubtype 1 "Dragon")).resolution ==
  .sequence [.dealDamage (.fixed 1) .target .markedPermanent,
    .«if» (.dealtDamageToSubtype "Dragon") markedDestroy]

#guard (SharedTrigger.timing .destroyOtherAmassControllerPower).resolution ==
  amassSeq

#guard TriggeredAbility.toNotation .onEnterDestroyOppArtifactsEnchantmentsGainLife ==
  "When this permanent enters, destroy all artifacts and enchantments your opponents control. You gain 1 life for each permanent destroyed this way."

#guard TriggeredAbility.toNotation (.onEnterDealDamageDestroyIfSubtype 1 "Dragon") ==
  "When this permanent enters, it deals 1 damage to any target. If a Dragon is dealt damage this way, destroy it."

#guard TriggeredAbility.toNotation .onEnterDestroyOtherAmassControllerPower ==
  "When Azog enters, destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card."

#guard TriggeredAbility.resolutionPhrase
    (SharedTrigger.timing .destroyOtherAmassControllerPower) ==
  "destroy another target creature. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card"

#guard TriggeredAbility.resolutionPhrase { resolution := .destroy .target } ==
  "destroy it"
#guard TriggeredAbility.resolutionPhrase { resolution := .destroy .humans } ==
  "destroy it"

/- A selector amass does not use amasses nothing. -/
#guard
  let g := step afterDraw (.amass .perOtherCreature)
  g.log.size == afterDraw.log.size

end Mtg.Engine.DestroyTests
