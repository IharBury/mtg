import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# Unified life gain instructions (`Instruction.gainLife`)

How much life is a `ValueExpr`: a fixed amount, life equal to the returned
card's power, one life for each permanent destroyed this way, and one life
for each other creature you control. Plus CR 702.15b aggregated lifelink gain
on divided damage.
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

def step (g : Game) (body : Instruction)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[])
    (spec : TargetSpec := .none) : Game :=
  g.applyTriggeredAbility caster
    (TriggeredAbility.mkTrigger .thisEnters { targets := spec, body })
    sourceId targets

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

def perOther : Instruction :=
  Instruction.gainLife (ValueExpr.count (.inZones .battlefield (.all #[
    .otherThan .this, .hasType .creature, .controlledBy .you])))

/- The controller gains the printed amount. Gaining 0 changes nothing. -/
#guard
  let g := step afterDraw (Instruction.gainLifeFixed 4)
  life g == life afterDraw + 4 && logContains g "gains 4 life"

#guard
  let g := step afterDraw (Instruction.gainLifeFixed 0)
  life g == life afterDraw && g.log == afterDraw.log

/- The return-then-gain sequence uses the returned Elf card's power, then
the card is in hand. An illegal graveyard card skips both steps. -/
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

#guard
  let g0 := putInGraveyard afterDraw elf caster
  let id := namedIn g0 (g0.player caster).graveyard "Lorien Elf"
  let (g1, _) := g0.move id .exile none
  let g := g1.applyTriggeredAbility caster .onEnterOrAttackReturnElfGainLife none
    #[Target.card id]
  life g == life g1

/- One life for each permanent destroyed by the bound destroy step. -/
#guard
  let g0 := addPermanent (addPermanent afterDraw (artifact "A" ManaCost.empty "") opp opp)
    (enchantment "E" ManaCost.empty "") opp opp
  let g := g0.applyTriggeredAbility caster .onEnterDestroyOppArtifactsEnchantmentsGainLife none
  life g == life g0 + 2

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

#guard TriggeredAbility.resolutionPhrase (Effect.triggerGainLife 3) ==
  "you gain 3 life"

#guard TriggeredAbility.resolutionPhrase Effect.triggerDestroyOppArtifactsEnchantmentsGainLife ==
  "destroy all artifacts and enchantments your opponents control. You gain 1 life for each permanent destroyed this way"

#guard TriggeredAbility.resolutionPhrase Effect.triggerPlusOneEachOtherGainLife ==
  "put a +1/+1 counter on each other creature you control. You gain 1 life for each other creature you control"

/- CR 702.15b: divided trigger damage from a lifelink source aggregates life gain
into a single `LifeEvent.gained` event across multiple recipients. -/
#guard
  let llSrc : CardDef :=
    creature "Divided Lifelinker" ManaCost.empty #[] 3 3 (keywords := #[Keyword.lifelink])
  let g0 := addPermanent (addPermanent afterDraw llSrc caster caster) bear opp opp
  let src := g0.battlefield.find? (·.name == "Divided Lifelinker") |>.get!
  let oppBear := g0.battlefield.find? (·.name == "Cave Bear") |>.get!
  let ab : TriggeredAbility := TriggeredAbility.mkTrigger .thisEnters (Effect.triggerDividedDamage 3 2)
  let startIdx := g0.events.size
  let g1 := g0.applyTriggeredAbility caster ab (some src.id)
    #[Target.player opp, Target.permanent oppBear.id] (dividedDamage := #[2, 1])
  let gains := (g1.events.extract startIdx g1.events.size).filter fun e =>
    match e.change with
    | .rules (.life (.gained _ _)) => true
    | _ => false
  gains.size == 1 && life g1 == life g0 + 3

end Mtg.Engine.GainLifeTests
