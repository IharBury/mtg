import Mtg.Engine.Tests.Builders
import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# Unified destroy instructions (`Instruction.destroy`)

Opponents' artifacts and enchantments, a permanent dealt damage by an earlier
step, and an announced creature whose power feeds amass. Indestructible,
shield counters, and replacement exile are all respected via `Instruction.bind`.
-/

namespace Mtg.Engine.DestroyTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests hiding afterDraw

def afterDraw : Game := Mtg.Engine.Tests.afterDraw.change (.pushContinuationFrame {})

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def step (g : Game) (ab : TriggeredAbility)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[])
    (lastKnownPower : Option Int := none) : Game :=
  g.applyTriggeredAbility caster ab sourceId targets (lastKnownPower := lastKnownPower)

def stepBody (g : Game) (body : Instruction)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[])
    (spec : TargetSpec := .none) (lastKnownPower : Option Int := none) : Game :=
  g.applyTriggeredAbility caster
    (TriggeredAbility.mkTrigger .thisEnters { targets := spec, body })
    sourceId targets (lastKnownPower := lastKnownPower)

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

/- Opponents' artifacts and enchantments are destroyed and counted for life gain.
Yours stay. Indestructible permanents and shield counters stay and do not count.
A permanent exiled instead of dying still counts. -/
#guard
  let g0 := addPermanent afterDraw (artifact "Opp Sword" ManaCost.empty "") opp opp
  let g0 := addPermanent g0 (enchantment "Opp Aura" ManaCost.empty "") opp opp
  let g0 := addPermanent g0 (artifactCreature "Opp Construct" ManaCost.empty #[] 1 1) opp opp
  let g0 := addPermanent g0 (artifact "My Sword" ManaCost.empty "") caster caster
  let g0 := addPermanent g0
    (artifact "Hardy Relic" ManaCost.empty "" (keywords := #[Keyword.indestructible])) opp opp
  let g0 := addPermanent g0 (artifact "Shielded Relic" ManaCost.empty "") opp opp
  let shielded := obj g0 "Shielded Relic"
  let g0 := g0.recordPutCounters shielded.id .shield 1
  let g0 := addPermanent g0 (artifact "Fleeting Relic" ManaCost.empty "") opp opp
  let fleeting := obj g0 "Fleeting Relic"
  let g0 := g0.createEffect (.exileIfDiesUntilEot fleeting.id)
  let g0 := addPermanent g0 (creature "Opp Bear" ManaCost.empty #[] 2 2) opp opp
  let life0 := (g0.player caster).life
  let g := step g0 .onEnterDestroyOppArtifactsEnchantmentsGainLife
  !onBoard g "Opp Sword" && buried g "Opp Sword" &&
    !onBoard g "Opp Aura" && buried g "Opp Aura" &&
    !onBoard g "Opp Construct" && buried g "Opp Construct" &&
    !onBoard g "Fleeting Relic" && exiled g "Fleeting Relic" &&
    onBoard g "My Sword" && onBoard g "Hardy Relic" && onBoard g "Shielded Relic" &&
    onBoard g "Opp Bear" &&
    (obj g "Shielded Relic").status.shield == 0 &&
    (g.player caster).life == life0 + 4 &&
    logContains g "is indestructible and isn't destroyed" &&
    logContains g "shield counter is removed"

/- Nothing destroyed gains 0 life. -/
#guard
  let g := step afterDraw .onEnterDestroyOppArtifactsEnchantmentsGainLife
  (g.player caster).life == (afterDraw.player caster).life

/- Damage, then destroy only when that damage hit a Dragon. -/
#guard
  let g0 := addPermanent afterDraw (creature "Wyrm" ManaCost.empty #["Dragon"] 4 4) opp opp
  let id := pid g0 "Wyrm"
  let g := g0.applyTriggeredAbility caster
    (.onEnterDealDamageDestroyIfSubtype 1 "Dragon") none #[Target.permanent id]
  !onBoard g "Wyrm" && buried g "Wyrm"

#guard
  let g0 := addPermanent afterDraw (creature "Hill" ManaCost.empty #["Giant"] 3 3) opp opp
  let id := pid g0 "Hill"
  let g := g0.applyTriggeredAbility caster
    (.onEnterDealDamageDestroyIfSubtype 1 "Dragon") none #[Target.permanent id]
  onBoard g "Hill" && (obj g "Hill").status.damage == 1 && !(logContains g "is destroyed")

#guard
  let g0 := addPermanent afterDraw
    (creature "Adamant Wyrm" ManaCost.empty #["Dragon"] 4 4
      (keywords := #[Keyword.indestructible])) opp opp
  let id := pid g0 "Adamant Wyrm"
  let g := g0.applyTriggeredAbility caster
    (.onEnterDealDamageDestroyIfSubtype 1 "Dragon") none #[Target.permanent id]
  onBoard g "Adamant Wyrm" && logContains g "is indestructible and isn't destroyed"

#guard
  let g0 := addPermanent afterDraw (creature "Wyrm" ManaCost.empty #["Dragon"] 4 4) opp opp
  let g0 := g0.recordPutCounters (pid g0 "Wyrm") .shield 1
  let id := pid g0 "Wyrm"
  let g := g0.applyTriggeredAbility caster
    (.onEnterDealDamageDestroyIfSubtype 1 "Dragon") none #[Target.permanent id]
  onBoard g "Wyrm" && (obj g "Wyrm").status.shield == 0 &&
    logContains g "shield counter is removed"

/- Azog: destroy another target creature, its controller amasses Goblins X
equal to its power, and if you controlled that creature, draw a card.
Indestructible still causes its controller to amass. -/
#guard
  let g0 := addPermanent afterDraw (creature "Mine" ManaCost.empty #[] 3 3) caster caster
  let id := pid g0 "Mine"
  let before := (g0.player caster).hand.size
  let g := step g0 .onEnterDestroyOtherAmassControllerPower none #[Target.permanent id]
  !onBoard g "Mine" &&
    onBoard g "Goblin Army" && g.controlledBy (obj g "Goblin Army") caster &&
    (obj g "Goblin Army").status.plusOnePlusOne == 3 &&
    (g.player caster).hand.size == before + 1

#guard
  let g0 := addPermanent afterDraw (creature "Ogre" ManaCost.empty #[] 5 5) opp opp
  let id := pid g0 "Ogre"
  let before := (g0.player caster).hand.size
  let g := step g0 .onEnterDestroyOtherAmassControllerPower none #[Target.permanent id]
  !onBoard g "Ogre" &&
    g.battlefield.any (fun o => o.name == "Goblin Army" && g.controlledBy o opp) &&
    (g.battlefield.find? (·.name == "Goblin Army")).any (·.status.plusOnePlusOne == 5) &&
    (g.player caster).hand.size == before

#guard
  let g0 := addPermanent afterDraw
    (creature "Hardy" ManaCost.empty #[] 2 2 (keywords := #[Keyword.indestructible])) caster caster
  let id := pid g0 "Hardy"
  let before := (g0.player caster).hand.size
  let g := step g0 .onEnterDestroyOtherAmassControllerPower none #[Target.permanent id]
  onBoard g "Hardy" && onBoard g "Goblin Army" &&
    (obj g "Goblin Army").status.plusOnePlusOne == 2 &&
    (g.player caster).hand.size == before + 1 &&
    logContains g "is indestructible and isn't destroyed"

#guard
  let g := step afterDraw .onEnterDestroyOtherAmassControllerPower
  !(g.battlefield.any (fun o => g.hasSubtype o .army))

/- A selector that names no permanent on this board destroys nothing. -/
#guard
  let g0 := addPermanent afterDraw (creature "Ogre" ManaCost.empty #[] 2 2) opp opp
  let g := stepBody g0 (Instruction.destroy (.inZones .battlefield (.all #[.hasSubtype (.literal .human), .controlledBy .you])))
  onBoard g "Ogre" && g.log == g0.log

/- Printed notations stay intact. -/
#guard TriggeredAbility.toNotation .onEnterDestroyOppArtifactsEnchantmentsGainLife ==
  "When this permanent enters, destroy all artifacts and enchantments your opponents control. You gain 1 life for each permanent destroyed this way."

#guard TriggeredAbility.toNotation (.onEnterDealDamageDestroyIfSubtype 1 "Dragon") ==
  "When this permanent enters, it deals 1 damage to any target. If a Dragon is dealt damage this way, destroy it."

#guard TriggeredAbility.toNotation .onEnterDestroyOtherAmassControllerPower ==
  "When this permanent enters, if there is target, destroy up to one other target creature; its controller amasses Goblins target's power; if target's controller is you, draw a card."

/- Amass reads dynamic counts; zero other creatures still amasses Goblins 0. -/
#guard
  let otherCreatures := ValueExpr.count (.inZones .battlefield (.all #[.otherThan .this, .hasType .creature, .controlledBy .you]))
  let g := stepBody afterDraw (.player (.amass .you .goblin otherCreatures))
  onBoard g "Goblin Army" &&
    (g.battlefield.find? (·.name == "Goblin Army")).any
      (fun o => o.status.plusOnePlusOne == 0 && g.controlledBy o caster) &&
    logContains g "amasses Goblins 0"

end Mtg.Engine.DestroyTests
