import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# `TriggerResolution.tap`

Who is tapped is an `ObjectSelector`. Any number of untapped Humans, the
enchanted creature, and the announced permanent while it is still on the
battlefield. Any other selector taps nothing.
-/

namespace Mtg.Engine.TapTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def step (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[]) : Game :=
  let g :=
    if g.continuations.isEmpty then
      g.change (.pushContinuationFrame { resolvingContext := some (sourceId, caster) })
    else g
  g.applyTriggeredAbility caster (.onEnterDraw 1) sourceId targets
    (resolutionOverride := some r)

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
  g.record (GameEvent.attached g.turnNumber a.id (pid g host) (cause := .gameRule .staticAbility))

def folk : CardDef := creature "Townsfolk" ManaCost.empty #["Human"] 1 1
def scout : CardDef := creature "Scout" ManaCost.empty #["Human"] 1 1
def bear : CardDef := creature "Bear" ManaCost.empty #[] 2 2
def foe : CardDef := creature "Foe" ManaCost.empty #["Human"] 2 2
def grasp : CardDef := enchantment "Grasp" ManaCost.empty ""
def hawk : CardDef :=
  creature "Hawk" ManaCost.empty #[] 1 1 (keywords := Keyword.flying)
def wasp : CardDef := creature "Wasp" ManaCost.empty #[] 1 1

def humansDraw : TriggeredAbility.TriggerResolution :=
  .sequence [.may (.tap .humans) (.sequence []), .draw .forEachTappedHuman]

def enchantedRemove : TriggeredAbility.TriggerResolution :=
  .sequence [.tap .enchanted, .removeCounters .all .enchanted]

def targetLose : TriggeredAbility.TriggerResolution :=
  .sequence [.tap (.target .ifPresent), .lose .allAbilities (.target .ifPresent)]

def village : Game :=
  let g := addPermanent afterDraw folk caster caster
  let g := addPermanent g scout caster caster
  addPermanent g bear caster caster

def offered : Game :=
  step ((village.change (.pushContinuationFrame {})).change (.humansTappedThisWay 4)) humansDraw

def rejects (g : Game) (ids : Array ObjectId) (needle : String) : Bool :=
  match g.choosePermanents caster ids with
  | .error e => mentions e needle
  | .ok _ => false

/- Choosing Humans records the later draw. None, and declining, draw nothing.
A choice that is not an untapped Human you control is refused. -/
#guard
  offered.pending == .tapHumans caster && offered.humansTappedThisWay == 0 &&
    offered.triggerSequenceRest.isSome &&
    handSize offered == handSize village &&
    logContains offered "may tap any number of untapped Humans"

#guard
  let g := step village (.tap .humans)
  g.pending == .tapHumans caster && g.humansTappedThisWay == 0

#guard
  let g := step village (.may (.tap .humans) (.sequence []))
  g.pending == .tapHumans caster && g.triggerSequenceRest.isNone

#guard
  let g := mustApply offered caster (.choosePermanents #[
    pid offered "Townsfolk", pid offered "Scout"])
  (obj g "Townsfolk").status.tapped && (obj g "Scout").status.tapped &&
    !(obj g "Bear").status.tapped &&
    handSize g == handSize village + 2 &&
    g.pending == .none && g.triggerSequenceRest.isNone &&
    g.humansTappedThisWay == 0

#guard
  let g := mustApply offered caster (.choosePermanents #[])
  !(obj g "Townsfolk").status.tapped && !(obj g "Scout").status.tapped &&
    handSize g == handSize village && g.pending == .none &&
    g.humansTappedThisWay == 0 && !(logContains g "taps no Humans")

#guard
  let g := mustApply offered caster .decline
  !(obj g "Townsfolk").status.tapped && handSize g == handSize village &&
    g.pending == .none && g.humansTappedThisWay == 0 &&
    logContains g "taps no Humans"

#guard
  let askedSeq := step village (.sequence [.tap .humans, .may (.gainLife (.fixed 1)) (.sequence [])])
  let gMid := mustApply askedSeq caster (.choosePermanents #[pid askedSeq "Townsfolk"])
  let asked := step village (.tap .humans)
  let g := mustApply asked caster (.choosePermanents #[pid asked "Townsfolk"])
  (obj g "Townsfolk").status.tapped && !(obj g "Scout").status.tapped &&
    gMid.humansTappedThisWay == 1 && g.continuations.isEmpty && g.pending == .none &&
    handSize g == handSize village

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
enchanted, a missing host, and a missing source tap nothing. A host that
has left is still tapped. An already tapped host stays tapped. -/
#guard
  let g0 := attach
    (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
    "Grasp" "Bear"
  let bear0 := obj g0 "Bear"
  let g0 := g0.recordPutCounters bear0.id .hope 2
  let g := step g0 enchantedRemove (some (pid g0 "Grasp"))
  (obj g "Bear").status.tapped && (obj g "Bear").status.hope == 0 &&
    !(obj g "Grasp").status.tapped &&
    logContains g "becomes tapped"

#guard
  let g0 := attach
    (addPermanent (addPermanent afterDraw foe opp opp) grasp caster caster)
    "Grasp" "Foe"
  let g := step g0 (.tap .enchanted) (some (pid g0 "Grasp"))
  (obj g "Foe").status.tapped && !(obj g "Grasp").status.tapped

#guard
  let g0 := attach
    (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
    "Grasp" "Bear"
  let g := step g0 (.may (.tap .enchanted) (.sequence [])) (some (pid g0 "Grasp"))
  (obj g "Bear").status.tapped && g.pending == g0.pending

#guard
  let g0 := attach
    (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
    "Grasp" "Bear"
  let bear0 := obj g0 "Bear"
  let g0 := setTapped g0 bear0.id true
  let g := step g0 (.tap .enchanted) (some (pid g0 "Grasp"))
  (obj g "Bear").status.tapped && logContains g "already tapped"

#guard
  let g0 := addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster
  let bear0 := obj g0 "Bear"
  let g0 := g0.recordPutCounters bear0.id .hope 2
  let g := step g0 enchantedRemove (some (pid g0 "Grasp"))
  !(obj g "Bear").status.tapped && (obj g "Bear").status.hope == 2 &&
    logContains g "Nothing is enchanted"

#guard
  let g0 := attach
    (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
    "Grasp" "Bear"
  let aura := obj g0 "Grasp"
  let g0 := g0.record (GameEvent.attached g0.turnNumber aura.id ⟨99999⟩ (cause := .gameRule .staticAbility))
  let g := step g0 (.tap .enchanted) (some (pid g0 "Grasp"))
  !(obj g "Bear").status.tapped && logContains g "Nothing is enchanted"

#guard
  let g0 := addPermanent afterDraw bear caster caster
  let g := step g0 (.tap .enchanted)
  !(obj g "Bear").status.tapped && g.log == g0.log

#guard
  let g0 := attach
    (addPermanent (addPermanent afterDraw bear caster caster) grasp caster caster)
    "Grasp" "Bear"
  let (g1, bearId) := g0.move (pid g0 "Bear") (.graveyard caster) none
  let aura := anyObj g1 "Grasp"
  let g1 := g1.record (GameEvent.attached g1.turnNumber aura.id bearId (cause := .gameRule .staticAbility))
  let g := step g1 (.tap .enchanted) (some aura.id)
  (anyObj g "Bear").status.tapped && logContains g "becomes tapped"

/- The announced permanent is tapped only while it is on the battlefield.
A missing target taps nothing. The following loss of abilities needs the
source to still be there. -/
#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let g := step g0 targetLose (some (pid g0 "Wasp")) #[Target.permanent (pid g0 "Hawk")]
  (obj g "Hawk").status.tapped && !(obj g "Wasp").status.tapped &&
    !g.hasFlying (obj g "Hawk") &&
    g.losesAbilitiesGrantedBy (obj g "Hawk") == #[pid g0 "Wasp"]

#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let g := step g0 (.may (.tap (.target .ifPresent)) (.sequence [])) (some (pid g0 "Wasp"))
    #[Target.permanent (pid g0 "Hawk")]
  (obj g "Hawk").status.tapped && g.hasFlying (obj g "Hawk") &&
    g.pending == g0.pending

#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let hawk0 := obj g0 "Hawk"
  let g0 := setTapped g0 hawk0.id true
  let g := step g0 (.tap (.target .ifPresent)) (some (pid g0 "Wasp"))
    #[Target.permanent (pid g0 "Hawk")]
  (obj g "Hawk").status.tapped && logContains g "already tapped"

#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let waspId := pid g0 "Wasp"
  let (g1, _) := g0.move waspId (.graveyard caster) none
  let g := step g1 targetLose (some waspId) #[Target.permanent (pid g1 "Hawk")]
  (obj g "Hawk").status.tapped && g.hasFlying (obj g "Hawk") &&
    (g.losesAbilitiesGrantedBy (obj g "Hawk")).isEmpty &&
    logContains g "keeps its abilities"

#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let g := step g0 targetLose (some (pid g0 "Wasp"))
  !(obj g "Hawk").status.tapped && g.hasFlying (obj g "Hawk") &&
    !(logContains g "becomes tapped") && !(logContains g "keeps its abilities")

#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let hawkId := pid g0 "Hawk"
  let (g1, newHawk) := g0.move hawkId (.graveyard caster) none
  let g := step g1 targetLose (some (pid g1 "Wasp")) #[Target.permanent newHawk]
  !(anyObj g "Hawk").status.tapped &&
    (g.losesAbilitiesGrantedBy (anyObj g "Hawk")).isEmpty &&
    !(logContains g "becomes tapped")

#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let g := step g0 (.tap (.target .ifPresent)) (some (pid g0 "Wasp"))
    #[Target.permanent ⟨99999⟩]
  !(obj g "Hawk").status.tapped && g.log == g0.log

#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let g := step g0 (.tap (.target .ifPresent)) (some (pid g0 "Wasp")) #[Target.player opp]
  !(obj g "Hawk").status.tapped && g.log == g0.log

#guard
  let g0 := addPermanent (addPermanent afterDraw hawk caster caster) wasp caster caster
  let g := step g0 (.tap (.target .ifPresent)) (some (pid g0 "Wasp"))
    #[Target.card (pid g0 "Hawk")]
  !(obj g "Hawk").status.tapped && g.log == g0.log

/- Any other selector taps nothing. -/
#guard
  let g0 := addPermanent afterDraw bear caster caster
  let g := step g0 (.tap .attackingCreatures) (some (pid g0 "Bear"))
  !(obj g "Bear").status.tapped && g.log == g0.log

/- Printed phrases stay with the combination that produces them. -/
#guard TriggeredAbility.resolution .onAttackTapHumansDraw == humansDraw
#guard TriggeredAbility.resolution .onEnterTapEnchantedRemoveCounters == enchantedRemove
#guard (SharedTrigger.timing (.enter .tapLoseAbilitiesWhileSource)).resolution == targetLose
#guard (SharedTrigger.timing .tapHumansDraw).resolution == humansDraw
#guard (SharedTrigger.timing .tapEnchantedRemoveCounters).resolution == enchantedRemove

#guard TriggeredAbility.resolutionPhrase { resolution := .tap .humans } ==
  "tap any number of untapped Humans you control"
#guard TriggeredAbility.resolutionPhrase { resolution := .may (.tap .humans) (.sequence []) } ==
  "you may tap any number of untapped Humans you control"
#guard TriggeredAbility.resolutionPhrase { resolution := .tap .enchanted } ==
  "tap enchanted creature"
#guard TriggeredAbility.resolutionPhrase { resolution := .tap (.target .ifPresent) } ==
  "tap up to one target creature"
#guard TriggeredAbility.resolutionPhrase { resolution := .tap .attackingCreatures } ==
  "tap it"
#guard TriggeredAbility.resolutionPhrase { resolution := .may (.tap .enchanted) (.sequence []) } ==
  "you may do it"
#guard TriggeredAbility.resolutionPhrase { resolution := humansDraw } ==
  "you may tap any number of untapped Humans you control. Draw a card for each Human tapped this way"
#guard TriggeredAbility.resolutionPhrase { resolution := enchantedRemove } ==
  "tap enchanted creature and remove all counters from it"
#guard TriggeredAbility.resolutionPhrase { resolution := targetLose } ==
  "tap up to one target creature. It loses all abilities for as long as this remains on the battlefield"
#guard TriggeredAbility.toNotation .onAttackTapHumansDraw ==
  "Whenever this creature attacks, you may tap any number of untapped Humans you control. Draw a card for each Human tapped this way."
#guard TriggeredAbility.toNotation .onEnterTapEnchantedRemoveCounters ==
  "When this Aura enters, tap enchanted creature and remove all counters from it."

end Mtg.Engine.TapTests
