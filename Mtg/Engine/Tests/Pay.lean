import Mtg.Engine.Tests.Builders
import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# Unified optional cost payments (`Instruction.optional` + `CostSpec`)

Paying mana, sacrificing permanents, discarding cards, and disjunctive costs
execute through `Instruction.optional` + `CostSpec`. Declining skips the
follow-up; paying executes it (and binds sacrificed/discarded objects when
`CostSpec.bindVar?` is set).
-/

namespace Mtg.Engine.PayTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests hiding afterDraw

def afterDraw : Game := Mtg.Engine.Tests.afterDraw.change (.pushContinuationFrame {})

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def step (g : Game) (e : Effect) (sourceId : Option ObjectId := none) : Game :=
  g.applyTriggeredAbility caster (TriggeredAbility.mkTrigger .thisEnters e) sourceId #[]

def stepBody (g : Game) (body : Instruction) (sourceId : Option ObjectId := none) : Game :=
  step g { body } sourceId

def bear : CardDef := creature "Bear" ManaCost.empty #[] 2 2
def ox : CardDef := creature "Ox" ManaCost.empty #[] 3 3
def relic : CardDef := artifact "Relic" ManaCost.empty ""
def relicTwo : CardDef := artifact "Relic Two" ManaCost.empty ""
def oppRelic : CardDef := artifact "Opp Relic" ManaCost.empty ""
def wolf : CardDef := creature "Wolf" ManaCost.empty #[] 1 1
def field : CardDef := land "Field" ""
def plains : CardDef := land "Plains" "" (subtypes := #["Plains"])

def pid (g : Game) (name : String) : ObjectId :=
  match g.battlefield.find? (·.name == name) with
  | some o => o.id
  | none => panic! s!"missing {name}"

def counters (g : Game) (name : String) : Nat :=
  match g.battlefield.find? (·.name == name) with
  | some o => o.status.plusOnePlusOne
  | none => panic! s!"missing {name}"

def handSize (g : Game) (p : PlayerId) : Nat :=
  (g.player p).hand.size

def onBoard (g : Game) (name : String) : Bool :=
  g.battlefield.any (·.name == name)

def buried (g : Game) (name : String) : Bool :=
  g.objects.any (fun o =>
    o.name == name &&
      match o.zone with
      | .graveyard _ => true
      | _ => false)

def inHand (g : Game) (p : PlayerId) (name : String) : Bool :=
  (g.player p).hand.any (fun id => (g.findObject? id).any (·.name == name))

def putInGraveyard (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.graveyard p)

def putInHand (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.hand p)

def namedIn (g : Game) (ids : Array ObjectId) (name : String) : ObjectId :=
  match ids.find? (fun id => (g.findObject? id).any (·.name == name)) with
  | some id => id
  | none => panic! s!"missing {name}"

def withMana (g : Game) : Game :=
  ((g.addMana caster (.colored .green) 2).addMana caster (.colored .blue) 1).addMana caster .colorless 1

def emptyHand (g : Game) : Game :=
  Mtg.Engine.Tests.emptyHand g caster

def payDraw : Effect := Effect.triggerMayPayGenericDraw 1
def payPlusOne : Effect := Effect.triggerMayPayGenericDraw 2 (plusOneOnSource := true)
def payReturn : Effect := Effect.triggerPayReturnFromGy
def sacPower : Effect := Effect.triggerAttackSacPlusOneEqualPower
def sacTreasure : Effect := Effect.triggerMaySacDrawTreasure
def sacOrDiscard : Effect := Effect.triggerMaySacArtifactOrDiscardDraw
def sacDestroy : Effect := Effect.enterMaySacAnotherThenDestroyOppNonland
def sacDamage : Effect := Effect.enterMaySacOrDiscardNonlandThenDamage

def sacTwoArtifacts : Instruction :=
  Instruction.may .you (some (CostSpec.ofItem (.sacrifice (.exact 2) (.filter (.hasType .artifact)))))
    (Instruction.drawFixed 1)

def discardTwo : Instruction :=
  Instruction.may .you (some (CostSpec.ofItem (.discard (.exact 2) .hand)))
    (Instruction.drawFixed 1)

/- Printed phrases stay the sentences those payments used. -/
#guard TriggeredAbility.resolutionPhrase payDraw == "you may pay {1}. If you do, draw a card"
#guard TriggeredAbility.resolutionPhrase payPlusOne ==
  "you may pay {2}. If you do, put a +1/+1 counter on this creature and draw a card"
#guard TriggeredAbility.resolutionPhrase sacPower ==
  "you may sacrifice another creature. If you do, put a number of +1/+1 counters on this creature equal to the sacrificed creature's power"
#guard TriggeredAbility.resolutionPhrase sacTreasure ==
  "you may sacrifice another creature or artifact. If you do, draw a card and create a Treasure token"
#guard TriggeredAbility.resolutionPhrase sacDestroy ==
  "you may sacrifice another creature. When you do, destroy target nonland permanent an opponent controls"
#guard TriggeredAbility.resolutionPhrase sacDamage ==
  "you may sacrifice an artifact or discard a nonland card. When you do, this deals 2 damage to any target"

/- `{1}` offers a generic payment. Declining skips the draw. Paying draws. -/
#guard
  let g0 := step (withMana afterDraw) payDraw
  let before := handSize g0 caster
  let declined := mustApply g0 caster .decline
  let paid := mustApply g0 caster .payGeneric
  g0.pending != .none &&
    handSize declined caster == before && declined.pending == .none &&
    handSize paid caster == before + 1 && paid.pending == .none

/- `{2}` puts a +1/+1 counter on the source and draws. -/
#guard
  let g0 := addPermanent (withMana afterDraw) bear caster caster
  let offered := step g0 payPlusOne (some (pid g0 "Bear"))
  let before := handSize offered caster
  let paid := mustApply offered caster .payGeneric
  offered.pending != .none &&
    counters paid "Bear" == 1 && handSize paid caster == before + 1

/- `{1}{G}{U}` returns the source from its owner's graveyard. -/
#guard
  let g0 := putInGraveyard (withMana afterDraw) bear caster
  let id := namedIn g0 (g0.player caster).graveyard "Bear"
  let offered := step g0 payReturn (some id)
  let paid := mustApply offered caster .accept
  offered.pending != .none && inHand paid caster "Bear" && !buried paid "Bear"

/- Sacrificing another creature binds its power into +1/+1 counters on the source.
No other creature skips; declining sacrifices nothing. -/
#guard
  let g0 := addPermanent afterDraw bear caster caster
  let g := step g0 sacPower (some (pid g0 "Bear"))
  g.pending == .none && counters g "Bear" == 0

#guard
  let g0 := addPermanent (addPermanent afterDraw bear caster caster) ox caster caster
  let offered := step g0 sacPower (some (pid g0 "Bear"))
  let declined := mustApply offered caster .decline
  let paid := mustApply offered caster (.choosePermanents #[pid g0 "Ox"])
  counters declined "Bear" == 0 && onBoard declined "Ox" &&
    counters paid "Bear" == 3 && buried paid "Ox" && !onBoard paid "Ox"

/- Sacrificing another creature or artifact draws and creates a Treasure. -/
#guard
  let g0 := addPermanent afterDraw bear caster caster
  let g := step g0 sacTreasure (some (pid g0 "Bear"))
  g.pending == .none && !onBoard g "Treasure"

#guard
  let g0 := addPermanent (addPermanent afterDraw bear caster caster) relic caster caster
  let before := handSize g0 caster
  let g := mustApply (step g0 sacTreasure (some (pid g0 "Bear"))) caster
    (.choosePermanents #[pid g0 "Relic"])
  handSize g caster == before + 1 && buried g "Relic" && onBoard g "Treasure"

/- Sacrificing an artifact or discarding a card draws; declining draws nothing. -/
#guard
  let g0 := step afterDraw sacOrDiscard
  let before := handSize g0 caster
  let declined := mustApply g0 caster .decline
  let id := (g0.player caster).hand.back!
  let gy := (g0.player caster).graveyard.size
  let discarded := mustApply g0 caster (.discard id)
  handSize declined caster == before && declined.pending == .none &&
    handSize discarded caster == before && (discarded.player caster).graveyard.size == gy + 1

#guard
  let g0 := addPermanent afterDraw relic caster caster
  let before := handSize g0 caster
  let g := mustApply (step g0 sacOrDiscard (some (pid g0 "Relic"))) caster
    (.sacrifice (pid g0 "Relic"))
  handSize g caster == before + 1 && buried g "Relic"

/- Sacrificing another creature queues the destroy reflexive. -/
#guard
  let g0 := addPermanent afterDraw bear caster caster
  let g := step g0 sacDestroy (some (pid g0 "Bear"))
  g.pending == .none && g.stack.isEmpty

#guard
  let g0 := addPermanent (addPermanent (addPermanent afterDraw bear caster caster) ox caster caster) oppRelic opp opp
  let offered := step g0 sacDestroy (some (pid g0 "Bear"))
  let declined := mustApply offered caster .decline
  let paid := mustApply offered caster (.choosePermanents #[pid g0 "Ox"])
  declined.stack.isEmpty && onBoard declined "Ox" && onBoard declined "Opp Relic" &&
    buried paid "Ox" && logContains paid "reflexive"

/- Sacrificing an artifact or discarding a nonland queues the damage reflexive. -/
#guard
  let g0 := emptyHand (addPermanent afterDraw bear caster caster)
  let g := step g0 sacDamage (some (pid g0 "Bear"))
  g.pending == .none && g.stack.isEmpty

#guard
  let g0 := addPermanent (addPermanent afterDraw bear caster caster) relic caster caster
  let g := mustApply (step g0 sacDamage (some (pid g0 "Bear"))) caster
    (.choosePermanents #[pid g0 "Relic"])
  buried g "Relic" && logContains g "reflexive"

/- Sacrificing two artifacts: one artifact cannot pay; two artifacts can pay and draw. -/
#guard
  let g0 := addPermanent afterDraw relic caster caster
  let g := stepBody g0 sacTwoArtifacts (some (pid g0 "Relic"))
  g.pending == .none && onBoard g "Relic"

#guard
  let g0 := addPermanent (addPermanent afterDraw relic caster caster) relicTwo caster caster
  let before := handSize g0 caster
  let offered := stepBody g0 sacTwoArtifacts (some (pid g0 "Relic"))
  let declined := mustApply offered caster .decline
  let paid := mustApply offered caster (.choosePermanents #[pid g0 "Relic", pid g0 "Relic Two"])
  handSize declined caster == before && onBoard declined "Relic" && onBoard declined "Relic Two" &&
    handSize paid caster == before + 1 && buried paid "Relic" && buried paid "Relic Two"

/- Discarding two cards: one card cannot pay; two cards can pay and draw. -/
#guard
  let g0 := putInHand (emptyHand afterDraw) bear caster
  let before := handSize g0 caster
  let g := stepBody g0 discardTwo
  g.pending == .none && handSize g caster == before

#guard
  let g0 := putInHand (putInHand (emptyHand afterDraw) bear caster) ox caster
  let bearId := namedIn g0 (g0.player caster).hand "Bear"
  let oxId := namedIn g0 (g0.player caster).hand "Ox"
  let offered := stepBody g0 discardTwo
  let declined := mustApply offered caster .decline
  let paid := mustApply offered caster (.choosePermanents #[bearId, oxId])
  inHand declined caster "Bear" && inHand declined caster "Ox" && handSize declined caster == 2 &&
    buried paid "Bear" && buried paid "Ox" && handSize paid caster == 1

end Mtg.Engine.PayTests
