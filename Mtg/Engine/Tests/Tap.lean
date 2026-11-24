import Mtg.Engine.Tests.Builders
import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# Unified tap instructions (`Instruction.tap` / `PermanentOp.setTapped`)

Any number of untapped Humans (with follow-up draw via `stepEnv`), the
enchanted creature (with counter removal), and the announced permanent while
it is on the battlefield (with lose-all-abilities while source remains) all
execute through `Game/Interpreter.lean`.
-/

namespace Mtg.Engine.TapTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def stepEffect (g : Game) (e : Effect)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[]) : Game :=
  let g :=
    if g.continuations.isEmpty then
      g.change (.pushContinuationFrame { resolvingContext := some (sourceId, caster) })
    else g
  g.applyTriggeredAbility caster (TriggeredAbility.mkTrigger .thisEnters e) sourceId targets

def obj (g : Game) (name : String) : GameObject :=
  match g.battlefield.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing {name}"

def anyObj (g : Game) (name : String) : GameObject :=
  match g.objects.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing {name}"

def pid (g : Game) (name : String) : ObjectId :=
  (obj g name).id

def handSize (g : Game) : Nat :=
  (g.player caster).hand.size

def attach (g : Game) (aura host : String) : Game :=
  let a := obj g aura
  g.record (GameEvent.attached g.turnNumber (g.snapshot a) (pid g host) (cause := .gameRule .staticAbility))

def folk : CardDef := creature "Townsfolk" ManaCost.empty #["Human"] 1 1
def scout : CardDef := creature "Scout" ManaCost.empty #["Human"] 1 1
def bear : CardDef := creature "Bear" ManaCost.empty #[] 2 2
def foe : CardDef := creature "Foe" ManaCost.empty #["Human"] 2 2
def grasp : CardDef := enchantment "Grasp" ManaCost.empty ""
def hawk : CardDef :=
  creature "Hawk" ManaCost.empty #[] 1 1 (keywords := #[Keyword.flying])
def wasp : CardDef := creature "Wasp" ManaCost.empty #[] 1 1

def tapHumansOnly : Effect :=
  { body := .permanent (.setTapped
      (.inZones .battlefield (.all #[.hasSubtype (.literal .human), .controlledBy .you, .tapped false]))
      true (choice? := some { chooser := .controller, count := .anyNumber })) }

def tapEnchantedOnly : Effect :=
  { body := Instruction.tap .attachedHost }

def tapTargetOnly : Effect :=
  { targets := TargetSpec.creature.asUpTo 1, body := Instruction.tap (.target 0) }

def village : Game :=
  let g := addPermanent afterDraw folk caster caster
  let g := addPermanent g scout caster caster
  addPermanent g bear caster caster

def offered : Game :=
  stepEffect village Effect.triggerTapHumansDraw

def rejects (g : Game) (ids : Array ObjectId) (needle : String) : Bool :=
  match g.choosePermanents caster ids with
  | .error e => mentions e needle
  | .ok _ => false

/- Choosing Humans records the later draw. None, and declining, draw nothing.
A choice that is not an untapped Human you control is refused. -/
#guard
  offered.pending == .tapHumans caster &&
    offered.currentInterpWait?.isSome &&
    handSize offered == handSize village &&
    logContains offered "may tap any number of untapped Humans"

#guard
  let g := stepEffect village tapHumansOnly
  g.pending == .tapHumans caster

#guard
  let g := mustApply offered caster (.choosePermanents #[
    pid offered "Townsfolk", pid offered "Scout"])
  (obj g "Townsfolk").status.tapped && (obj g "Scout").status.tapped &&
    !(obj g "Bear").status.tapped &&
    handSize g == handSize village + 2 &&
    g.pending == .none && g.currentInterpWait?.isNone

#guard
  let g := mustApply offered caster (.choosePermanents #[])
  !(obj g "Townsfolk").status.tapped && !(obj g "Scout").status.tapped &&
    handSize g == handSize village && g.pending == .none &&
    !(logContains g "taps no Humans")

#guard
  let g := mustApply offered caster .decline
  !(obj g "Townsfolk").status.tapped && handSize g == handSize village &&
    g.pending == .none && logContains g "taps no Humans"

#guard
  let asked := stepEffect village tapHumansOnly
  let g := mustApply asked caster (.choosePermanents #[pid asked "Townsfolk"])
  (obj g "Townsfolk").status.tapped && !(obj g "Scout").status.tapped &&
    g.pending == .none && handSize g == handSize village

#guard rejects offered #[pid offered "Bear"] "not an untapped Human"
#guard
  let g := addPermanent offered foe opp opp
  rejects g #[pid g "Foe"] "not an untapped Human"
#guard
  let towns := obj offered "Townsfolk"
  let g := setTapped offered towns.id true
  rejects g #[pid g "Townsfolk"] "not an untapped Human"
#guard rejects offered #[pid offered "Townsfolk", pid offered "Townsfolk"] "Duplicate card"
#guard
  match offered.choosePermanents opp #[pid offered "Townsfolk"] with
  | .error e => mentions e "Only"
  | .ok _ => false
#guard
  let townsId := pid offered "Townsfolk"
  let (g, newId) := offered.move townsId (.graveyard caster) none
  rejects g #[newId] "not an untapped Human"

/- The enchanted creature is tapped, including an opponent's. Nothing
enchanted, a missing host, and a missing source tap nothing. An already
tapped host stays tapped. -/
#guard
  let g0 := attach
    (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
    "Grasp" "Bear"
  let bear0 := obj g0 "Bear"
  let g0 := g0.recordPutCounters bear0.id .hope 2
  let g := stepEffect g0 Effect.triggerTapEnchantedRemoveCounters (some (pid g0 "Grasp"))
  (obj g "Bear").status.tapped && (obj g "Bear").status.hope == 0 &&
    !(obj g "Grasp").status.tapped &&
    logContains g "becomes tapped"

#guard
  let g0 := attach
    (addPermanent (addPermanent afterDraw foe opp opp) grasp caster caster)
    "Grasp" "Foe"
  let g := stepEffect g0 tapEnchantedOnly (some (pid g0 "Grasp"))
  (obj g "Foe").status.tapped && !(obj g "Grasp").status.tapped

#guard
  let g0 := attach
    (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
    "Grasp" "Bear"
  let bear0 := obj g0 "Bear"
  let g0 := setTapped g0 bear0.id true
  let g := stepEffect g0 tapEnchantedOnly (some (pid g0 "Grasp"))
  (obj g "Bear").status.tapped && logContains g "already tapped"

#guard
  let g0 := addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster
  let bear0 := obj g0 "Bear"
  let g0 := g0.recordPutCounters bear0.id .hope 2
  let g := stepEffect g0 Effect.triggerTapEnchantedRemoveCounters (some (pid g0 "Grasp"))
  !(obj g "Bear").status.tapped && (obj g "Bear").status.hope == 2

#guard
  let g0 := addPermanent afterDraw bear caster caster
  let g := stepEffect g0 tapEnchantedOnly
  !(obj g "Bear").status.tapped && g.log == g0.log

/- The announced permanent is tapped only while it is on the battlefield.
A missing target taps nothing. The following loss of abilities needs the
source to still be there. -/
#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let g := stepEffect g0 Effect.enterTapLoseAbilitiesWhileSource (some (pid g0 "Wasp"))
    #[Target.permanent (pid g0 "Hawk")]
  (obj g "Hawk").status.tapped && !(obj g "Wasp").status.tapped &&
    !g.hasFlying (obj g "Hawk") &&
    g.losesAbilitiesGrantedBy (obj g "Hawk") == #[pid g0 "Wasp"]

#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let hawk0 := obj g0 "Hawk"
  let g0 := setTapped g0 hawk0.id true
  let g := stepEffect g0 tapTargetOnly (some (pid g0 "Wasp")) #[Target.permanent (pid g0 "Hawk")]
  (obj g "Hawk").status.tapped && logContains g "already tapped"

#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let waspId := pid g0 "Wasp"
  let (g1, _) := g0.move waspId (.graveyard caster) none
  let g := stepEffect g1 Effect.enterTapLoseAbilitiesWhileSource (some waspId)
    #[Target.permanent (pid g1 "Hawk")]
  (obj g "Hawk").status.tapped && g.hasFlying (obj g "Hawk") &&
    (g.losesAbilitiesGrantedBy (obj g "Hawk")).isEmpty

#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let g := stepEffect g0 Effect.enterTapLoseAbilitiesWhileSource (some (pid g0 "Wasp"))
  !(obj g "Hawk").status.tapped && g.hasFlying (obj g "Hawk") &&
    !(logContains g "becomes tapped")

#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let hawkId := pid g0 "Hawk"
  let (g1, newHawk) := g0.move hawkId (.graveyard caster) none
  let g := stepEffect g1 Effect.enterTapLoseAbilitiesWhileSource (some (pid g1 "Wasp"))
    #[Target.permanent newHawk]
  !(anyObj g "Hawk").status.tapped &&
    (g.losesAbilitiesGrantedBy (anyObj g "Hawk")).isEmpty &&
    !(logContains g "becomes tapped")

#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let g := stepEffect g0 tapTargetOnly (some (pid g0 "Wasp")) #[Target.player opp]
  !(obj g "Hawk").status.tapped

/- Printed phrases and notations stay intact. -/
#guard TriggeredAbility.onAttackTapHumansDraw.effect.body == Effect.triggerTapHumansDraw.body
#guard TriggeredAbility.onEnterTapEnchantedRemoveCounters.effect.body ==
  Effect.triggerTapEnchantedRemoveCounters.body
#guard TriggeredAbility.resolutionPhrase tapEnchantedOnly == "tap enchanted creature"
#guard TriggeredAbility.resolutionPhrase Effect.triggerTapHumansDraw ==
  "you may tap any number of untapped Humans you control. Draw a card for each Human tapped this way"
#guard TriggeredAbility.resolutionPhrase Effect.enterTapLoseAbilitiesWhileSource ==
  "tap up to one target creature. It loses all abilities for as long as this remains on the battlefield"
#guard TriggeredAbility.toNotation .onAttackTapHumansDraw ==
  "Whenever this creature attacks, you may tap any number of untapped Humans you control. Draw a card for each Human tapped this way."
#guard TriggeredAbility.toNotation .onEnterTapEnchantedRemoveCounters ==
  "When this Aura enters, tap enchanted creature. Remove any number of counter(s) from enchanted creature."

end Mtg.Engine.TapTests
