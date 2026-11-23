import Mtg.Engine.Fixture
import Mtg.Engine.Game

/-!
# Unified counter placement instructions (`Instruction.putCounters`)

What counter is put (`CounterOp.put`) and who receives it (`ObjectExpr`)
execute through `Interpreter.execPermanent`.
-/

namespace Mtg.Engine.PutCountersTests

open Mtg.Engine
open Mtg.Engine.Tests hiding afterDraw

def afterDraw : Game := Mtg.Engine.Tests.afterDraw.change (.pushContinuationFrame {})

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def bear : CardDef := {
  name := "Counter Bear"
  types := #[.creature]
  power := some 2
  toughness := some 2
}

def other : CardDef := {
  name := "Counter Other"
  types := #[.creature]
  subtypes := #["Goblin"]
  power := some 1
  toughness := some 1
}

def elf : CardDef := {
  name := "Counter Elf"
  types := #[.creature]
  subtypes := #["Elf"]
  power := some 1
  toughness := some 1
}

def foe : CardDef := {
  name := "Counter Foe"
  types := #[.creature]
  power := some 2
  toughness := some 2
}

def rock : CardDef := {
  name := "Counter Rock"
  types := #[.artifact]
}

def aura : CardDef := {
  name := "Counter Aura"
  types := #[.enchantment]
}

def step (g : Game) (body : Instruction)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[])
    (spec : TargetSpec := .none)
    (lastKnownPower : Option Int := none) : Game :=
  g.applyTriggeredAbility caster
    (TriggeredAbility.mkTrigger .thisEnters { targeting := .of spec, body })
    sourceId targets (lastKnownPower := lastKnownPower)

def obj (g : Game) (name : String) : GameObject :=
  match g.objects.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing {name}"

def pid (g : Game) (name : String) : ObjectId :=
  (obj g name).id

def plus (g : Game) (name : String) : Nat :=
  (obj g name).status.plusOnePlusOne

def board : Game :=
  let g := addPermanent afterDraw bear caster caster
  let g := addPermanent g other caster caster
  let g := addPermanent g elf caster caster
  let g := addPermanent g rock caster caster
  let g := addPermanent g foe opp opp
  addPermanent g aura caster caster

def attach (g : Game) (auraName hostName : String) : Game :=
  let a := obj g auraName
  g.record (GameEvent.attached g.turnNumber (g.snapshot a) (pid g hostName) (cause := .gameRule .staticAbility))

def leave (g : Game) (name : String) : Game :=
  let o := obj g name
  (g.move o.id (.graveyard o.owner) none).1

/- Each creature you control gets one +1/+1 counter. A subtype limits that
to permanents of the subtype. The city's blessing puts two instead.
An opponent's creature and an artifact are left alone. -/
#guard
  let g := step board (Instruction.putPlusOne (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])) 1)
  plus g "Counter Bear" == 1 && plus g "Counter Other" == 1 &&
    plus g "Counter Elf" == 1 && plus g "Counter Rock" == 0 &&
    plus g "Counter Foe" == 0

#guard
  let g := step board (Instruction.putPlusOne (.inZones .battlefield (.all #[.hasSubtype (.literal .goblin), .controlledBy .you])) 1)
  plus g "Counter Other" == 1 && plus g "Counter Bear" == 0 &&
    plus g "Counter Elf" == 0 && plus g "Counter Rock" == 0

#guard
  let plain := board.applyTriggeredAbility caster .onEquippedAttacksPlusOneEachIfCityBlessing none
  let blessed :=
    (board.record (GameEvent.gainedDesignation board.turnNumber caster .citysBlessing
      (cause := some (.gameRule .staticAbility)))).applyTriggeredAbility caster
      .onEquippedAttacksPlusOneEachIfCityBlessing none
  plus plain "Counter Bear" == 1 && plus plain "Counter Rock" == 0 &&
    plus blessed "Counter Bear" == 2 && plus blessed "Counter Elf" == 2 &&
    plus blessed "Counter Rock" == 0

/- Each other creature you control gets a counter. The source does not,
and neither does an opponent's creature. -/
#guard
  let g0 := board
  let g := step g0
    (Instruction.putPlusOne (.inZones .battlefield (.all #[.otherThan .this, .hasType .creature, .controlledBy .you])) 1)
    (some (pid g0 "Counter Bear"))
  plus g "Counter Bear" == 0 && plus g "Counter Other" == 1 &&
    plus g "Counter Elf" == 1 && plus g "Counter Foe" == 0

/- The announced permanent gets the printed count. -/
#guard
  let g0 := board
  let tgt := #[Target.permanent (pid g0 "Counter Bear")]
  let two := step g0 (Instruction.putPlusOne (.target 0) 2) none tgt .creature
  let one := step g0 (Instruction.putPlusOne (.target 0) 1) none tgt .creature
  plus two "Counter Bear" == 2 && plus one "Counter Bear" == 1

/- Source, enchanted host, and while-source-remains targets receive counters cleanly. -/
#guard
  let g0 := board
  let sid := pid g0 "Counter Bear"
  let g := step g0 (Instruction.putCounters .this .loyalty (.const 1)) (some sid)
  (obj g "Counter Bear").status.loyaltyCounters == 1

#guard
  let g0 := board
  let sid := pid g0 "Counter Bear"
  let gone := step (leave g0 "Counter Bear") (Instruction.putPlusOne .this 1) (some sid)
  let absent := step g0 (Instruction.putPlusOne .this 1)
  plus gone "Counter Bear" == 0 && plus absent "Counter Bear" == 0

#guard
  let g0 := board
  let silent := step g0 (Instruction.putPlusOne .attachedHost 1) (some (pid g0 "Counter Aura"))
  let g := step (attach g0 "Counter Aura" "Counter Bear")
    (Instruction.putPlusOne .attachedHost 1) (some (pid g0 "Counter Aura"))
  plus silent "Counter Bear" == 0 && plus g "Counter Bear" == 1 &&
    plus g "Counter Aura" == 0

#guard
  let g0 := board
  let tgt := #[Target.permanent (pid g0 "Counter Bear")]
  let sid := pid g0 "Counter Aura"
  let instr := Instruction.ifThen (.exists .this) (Instruction.putPlusOne (.target 0) 1)
  let g := step g0 instr (some sid) tgt .creature
  let gone := step (leave g0 "Counter Aura") instr (some sid) tgt .creature
  plus g "Counter Bear" == 1 && plus gone "Counter Bear" == 0

/- Shield counter on source; hand selector puts no counters on permanents. -/
#guard
  let g0 := board
  let g := step g0 (Instruction.putCounters .this .shield (.const 1)) (some (pid g0 "Counter Bear"))
  (obj g "Counter Bear").status.shield == 1 && (obj g "Counter Other").status.shield == 0

#guard
  let g0 := board
  let g := step g0 (Instruction.putPlusOne (.inZones (.handOf .you) .anyObject) 1)
  plus g "Counter Bear" == 0 && plus g "Counter Other" == 0

/- Printed phrases stay intact. -/
#guard TriggeredAbility.resolutionPhrase
    { body := Instruction.putPlusOne (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])) 1 } ==
  "put a +1/+1 counter on each creature you control"

/- Phase 11: Putting loyalty counters on an artifact that gained `.planeswalker`
in Layer 4 snapshots `.planeswalker` on `PermanentEvent.counters` and triggers
`TriggerPattern.youPutLoyaltyCounters`. -/
#guard
  let loyaltyWatcher : CardDef := {
    name := "Loyalty Watcher"
    types := #[.enchantment]
    triggeredAbilities := #[TriggeredAbility.ofPattern .youPutLoyaltyCounters "" (Instruction.drawFixed 1)]
  }
  let g0 := addPermanent board loyaltyWatcher caster caster
  let rockId := pid g0 "Counter Rock"
  let g1 := g0.createEffect
    (.layered (.objects #[rockId]) (.types .add #[.planeswalker] #[.jace] #[]) .untilEndOfTurn)
  let g2 := g1.withBatch none fun g =>
    g.recordPutCounters rockId .loyalty 1 (byPlayer := some caster)
  let snapHasPw := g2.events.any fun e =>
    match e.change with
    | .rules (.permanent (.counters (.object eo) .loyalty (.put 1) (some p))) =>
      eo.id == some rockId && p == caster && eo.types.contains .planeswalker
    | _ => false
  snapHasPw &&
    g2.waitingTriggers.any (·.pattern == .youPutLoyaltyCounters)

/- Phase 25: Removing the last shield counter via `destroyPermanent` routes through
`recordRemoveCounters` and immediately expires `.whileSourceHasCounter` effects (CR 122.1c / 611.2a). -/
#guard
  let rockId := pid board "Counter Rock"
  let g1 := board.recordPutCounters rockId .shield 1 (byPlayer := some caster)
  let g2 := g1.createEffect
    (.layered (.objects #[rockId]) (.types .add #[.creature] #[] #[]) (.whileSourceHasCounter rockId .shield))
  let g3 := g2.destroyPermanent (g2.object! rockId)
  g2.isCreature (g2.object! rockId) &&
    (g3.object! rockId).isOnBattlefield &&
    (g3.object! rockId).status.shield == 0 &&
    !g3.isCreature (g3.object! rockId)

end Mtg.Engine.PutCountersTests
