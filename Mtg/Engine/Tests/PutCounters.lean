import Mtg.Engine.Fixture
import Mtg.Engine.Game

/-!
# `TriggerResolution.putCounters`

What is put is a `CounterSelector`. Who receives it is an `ObjectSelector`.
A kind and a permanent the selector names receive those counters. A hand
does not.
-/

namespace Mtg.Engine.PutCountersTests

open Mtg.Engine
open Mtg.Engine.Tests

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

def step (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[])
    (ab : TriggeredAbility := .onEnterDraw 1)
    (lastKnownPower : Option Int := none) : Game :=
  g.applyTriggeredAbility caster ab sourceId targets
    (lastKnownPower := lastKnownPower) (resolutionOverride := some r)

def obj (g : Game) (name : String) : GameObject :=
  match g.objects.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing {name}"

def pid (g : Game) (name : String) : ObjectId :=
  (obj g name).id

def plus (g : Game) (name : String) : Nat :=
  (obj g name).status.plusOnePlusOne

def phrase (r : TriggeredAbility.TriggerResolution) : String :=
  TriggeredAbility.resolutionPhrase { resolution := r }

def board : Game :=
  let g := addPermanent afterDraw bear caster caster
  let g := addPermanent g other caster caster
  let g := addPermanent g elf caster caster
  let g := addPermanent g rock caster caster
  let g := addPermanent g foe opp opp
  addPermanent g aura caster caster

def attach (g : Game) (auraName hostName : String) : Game :=
  let a := obj g auraName
  g.changeObject a.id (.attachedTo (some (pid g hostName)))

def leave (g : Game) (name : String) : Game :=
  let o := obj g name
  g.changeObject o.id (.zone (.graveyard o.owner))

/- Each creature you control gets one +1/+1 counter. A subtype limits that
to permanents of the subtype. The city's blessing puts two instead.
An opponent's creature and an artifact are left alone. -/
#guard
  let g := step board (.putCounters (.ofKind .plusOnePlusOne) .youControl)
  plus g "Counter Bear" == 1 && plus g "Counter Other" == 1 &&
    plus g "Counter Elf" == 1 && plus g "Counter Rock" == 0 &&
    plus g "Counter Foe" == 0

#guard
  let g := step board (.putCounters (.ofKind .plusOnePlusOne) (.youControl (.subtype .goblin)))
  plus g "Counter Other" == 1 && plus g "Counter Bear" == 0 &&
    plus g "Counter Elf" == 0 && plus g "Counter Rock" == 0

#guard
  let plain := step board (.putCounters (.ofKind .plusOnePlusOne) (.youControl .citysBlessing))
  let blessed := step
    (board.changePlayer caster (.citysBlessing true))
    (.putCounters (.ofKind .plusOnePlusOne) (.youControl .citysBlessing))
  plus plain "Counter Bear" == 1 && plus plain "Counter Rock" == 0 &&
    plus blessed "Counter Bear" == 2 && plus blessed "Counter Elf" == 2 &&
    plus blessed "Counter Rock" == 0

/- Each other creature you control gets a counter. The source does not,
and neither does an opponent's creature. -/
#guard
  let g0 := board
  let g := step g0 (.putCounters (.ofKind .plusOnePlusOne) .eachOther)
    (some (pid g0 "Counter Bear"))
  plus g "Counter Bear" == 0 && plus g "Counter Other" == 1 &&
    plus g "Counter Elf" == 1 && plus g "Counter Foe" == 0

/- The announced permanent gets the printed count. `byYou` puts one counter
and names the controller. A missing target is reported, and that report
says you won't put counters when `byYou` is set. -/
#guard
  let g0 := board
  let tgt := #[Target.permanent (pid g0 "Counter Bear")]
  let ab := TriggeredAbility.onEnterPlusOneOnCreature
  let two := step g0 (.putCounters (.ofKind .plusOnePlusOne 2) .permanent) none tgt ab
  let yours := step g0 (.putCounters (.ofKind .plusOnePlusOne 2) (.permanent true)) none tgt ab
  plus two "Counter Bear" == 2 && plus yours "Counter Bear" == 1

#guard
  let missing := step board (.putCounters (.ofKind .plusOnePlusOne) .permanent)
  let yours := step board (.putCounters (.ofKind .plusOnePlusOne) (.permanent true))
  logContains missing "The target is no longer legal" &&
    !(logContains missing "You won't put counters on anything.") &&
    logContains yours "You won't put counters on anything."

/- The source gets the counter. A source that has left is reported and
later steps still run, so the game does not skip the rest of a sequence.
Nothing enchanted is silent. The enchanted creature gets the counter.
The announced permanent gets one while the source remains, and nothing
once the source has left. -/
#guard
  let g0 := board
  let sid := pid g0 "Counter Bear"
  let g := step g0 (.putCounters (.ofKind .loyalty) .source) (some sid)
  (obj g "Counter Bear").status.loyaltyCounters == 1 &&
    logContains g "A loyalty counter is put on Counter Bear"

#guard
  let g0 := board
  let sid := pid g0 "Counter Bear"
  let gone := step (leave g0 "Counter Bear")
    (.putCounters (.ofKind .plusOnePlusOne) .sourceIfPresent) (some sid)
  let absent := step g0 (.putCounters (.ofKind .plusOnePlusOne) .sourceIfPresent)
  plus gone "Counter Bear" == 0 &&
    logContains gone "Counter Bear is no longer on the battlefield. No counter is put." &&
    !gone.skipTriggerSequenceRest &&
    logContains absent "The source is no longer on the battlefield. No counter is put."

#guard
  let g0 := board
  let silent := step g0 (.putCounters (.ofKind .plusOnePlusOne) .enchanted)
    (some (pid g0 "Counter Aura"))
  let g := step (attach g0 "Counter Aura" "Counter Bear")
    (.putCounters (.ofKind .plusOnePlusOne) .enchanted)
    (some (pid g0 "Counter Aura"))
  plus silent "Counter Bear" == 0 && plus g "Counter Bear" == 1 &&
    plus g "Counter Aura" == 0

#guard
  let g0 := board
  let tgt := #[Target.permanent (pid g0 "Counter Bear")]
  let ab := TriggeredAbility.onEnterPlusOneOnCreature
  let sid := pid g0 "Counter Aura"
  let g := step g0 (.putCounters (.ofKind .plusOnePlusOne) (.target .whileSource))
    (some sid) tgt ab
  let gone := step (leave g0 "Counter Aura")
    (.putCounters (.ofKind .plusOnePlusOne) (.target .whileSource)) (some sid) tgt ab
  plus g "Counter Bear" == 1 && plus gone "Counter Bear" == 0

/- The created token gets the noted count, and that note is consumed.
Each announced creature you control, up to the last-known count, gets one
counter. A noncreature is reported. Zero puts nothing. -/
#guard
  let g0 := board
  let id := pid g0 "Counter Other"
  let g := step (g0.changes #[.createdTokenThisWay (some id), .notedCountThisWay 3])
    (.putCounters .plusOneNoted .createdToken)
  plus g "Counter Other" == 3 && g.createdTokenThisWay.isNone &&
    g.notedCountThisWay == 3

#guard
  let g0 := board
  let targets := #[
    Target.permanent (pid g0 "Counter Bear"),
    Target.permanent (pid g0 "Counter Rock"),
    Target.permanent (pid g0 "Counter Elf")]
  let g := step g0 (.putCounters (.ofKind .plusOnePlusOne) .eachUpToLastKnown)
    none targets (lastKnownPower := some 2)
  let none := step g0 (.putCounters (.ofKind .plusOnePlusOne) .eachUpToLastKnown)
    none targets (lastKnownPower := some 0)
  plus g "Counter Bear" == 1 && plus g "Counter Elf" == 0 &&
    plus g "Counter Rock" == 0 &&
    logContains g "The target is no longer legal" &&
    plus none "Counter Bear" == 0 && plus none "Counter Elf" == 0

/- The announced permanent gets the counters. A shield counter is put.
A hand is not a permanent, so it receives nothing. -/
#guard
  let g0 := board
  let tgt := #[Target.permanent (pid g0 "Counter Bear")]
  let g := step g0 (.putCounters (.ofKind .plusOnePlusOne) .target) none tgt
    TriggeredAbility.onEnterPlusOneOnCreature
  plus g "Counter Bear" == 1 && plus g "Counter Other" == 0 &&
    plus g "Counter Elf" == 0

#guard
  let g0 := board
  let g := step g0 (.putCounters (.ofKind .shield) .source) (some (pid g0 "Counter Bear"))
  (obj g "Counter Bear").status.shield == 1 &&
    (obj g "Counter Other").status.shield == 0

#guard
  let g0 := board
  let g := step g0 (.putCounters (.ofKind .plusOnePlusOne) .hand)
  plus g "Counter Bear" == 0 && plus g "Counter Other" == 0

#guard phrase (.putCounters (.ofKind .plusOnePlusOne) .youControl) ==
  "put a +1/+1 counter on each creature you control"
#guard phrase (.putCounters (.ofKind .plusOnePlusOne) .eachOther) ==
  "put a +1/+1 counter on each other creature you control"
#guard phrase (.putCounters (.ofKind .plusOnePlusOne) .eachUpToLastKnown) ==
  "put a +1/+1 counter on each of up to that many target creatures you control"
#guard phrase (.putCounters (.ofKind .plusOnePlusOne) .hand) == "put counters"

end Mtg.Engine.PutCountersTests
