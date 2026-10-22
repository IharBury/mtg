import Mtg.Engine.Catalog
import Mtg.Engine.Fixture

/-!
# `TriggerResolution.pay`

Paying mana, and paying by sacrificing or discarding, are `pay`. What is
paid is an argument. How many cards a discard discards is a `NumberSelector`.
Which cards are an `ObjectSelector`. Declining inside `.may _ _ .ifYouDo`
skips the follow-up.
-/

namespace Mtg.Engine.PayTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def step (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none) : Game :=
  g.applyTriggeredAbility caster (.onEnterDraw 1) sourceId #[]
    (resolutionOverride := some r)

def phrase (r : TriggeredAbility.TriggerResolution) : String :=
  TriggeredAbility.resolutionPhrase { resolution := r }

def bear : CardDef := creature "Bear" ManaCost.empty #[] 2 2
def ox : CardDef := creature "Ox" ManaCost.empty #[] 3 3
def relic : CardDef := artifact "Relic" ManaCost.empty ""
def oppRelic : CardDef := artifact "Opp Relic" ManaCost.empty ""

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
  insertObject g card p (.graveyard p) none {} (fun id _ =>
    #[.pushGraveyard id])

def putInHand (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.hand p) none {} (fun id _ =>
    #[.pushHand id])

def namedIn (g : Game) (ids : Array ObjectId) (name : String) : ObjectId :=
  match ids.find? (fun id => (g.findObject? id).any (·.name == name)) with
  | some id => id
  | none => panic! s!"missing {name}"

def withMana (g : Game) : Game :=
  g.changePlayers caster
    #[.addMana (.colored .green) 2, .addMana (.colored .blue) 1, .addMana .colorless 1]

def emptyHand (g : Game) : Game :=
  g.changePlayer caster (.hand #[])

def payDraw : TriggeredAbility.TriggerResolution :=
  .may (.pay (.mana #[.generic 1])) (.draw (.fixed 1)) .ifYouDo

def payPlusOne : TriggeredAbility.TriggerResolution :=
  .may (.pay (.mana #[.generic 2]))
    (.sequence [.putCounters (.ofKind .plusOnePlusOne 1) .source, .draw (.fixed 1)])
    .ifYouDo

def payReturn : TriggeredAbility.TriggerResolution :=
  .may (.pay (.mana #[.generic 1, .colored .green, .colored .blue]))
    (.returnToHand .source) .ifYouDo

def sacPower : TriggeredAbility.TriggerResolution :=
  .may (.pay (.sacrifice (.fixed 1) .another)) (.putCounters .plusOneSacrificedPower .source) .ifYouDo

def sacTreasure : TriggeredAbility.TriggerResolution :=
  .may (.pay (.sacrifice (.fixed 1) .anotherCreatureOrArtifact))
    (.sequence [.draw (.fixed 1), .createTokens .treasure (.fixed 1) false]) .ifYouDo

def sacOrDiscard : TriggeredAbility.TriggerResolution :=
  .may (.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .card]))
    (.draw (.fixed 1)) .ifYouDo

def sacDestroy : TriggeredAbility.TriggerResolution :=
  .may (.pay (.sacrifice (.fixed 1) .another)) (.queueReflexive (.destroy .target)) .ifYouDo

def sacDamage : TriggeredAbility.TriggerResolution :=
  .may (.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .nonland]))
    (.queueReflexive (.dealDamage (.fixed 2) .target)) .ifYouDo

def sacOrDiscardReversed : TriggeredAbility.TriggerResolution :=
  .may (.pay (.or [.discard (.fixed 1) .card, .sacrifice (.fixed 1) .artifact]))
    (.draw (.fixed 1)) .ifYouDo

def payArtifact : TriggeredAbility.TriggerResolution :=
  .may (.pay (.sacrifice (.fixed 1) .artifact)) (.draw (.fixed 1)) .ifYouDo

def payNonland : TriggeredAbility.TriggerResolution :=
  .may (.pay (.discard (.fixed 1) .nonland)) (.draw (.fixed 1)) .ifYouDo

def sacOrMana : TriggeredAbility.TriggerResolution :=
  .may (.pay (.or [.sacrifice (.fixed 1) .artifact, .mana #[.generic 1]])) (.draw (.fixed 1)) .ifYouDo

def relicTwo : CardDef := artifact "Relic Two" ManaCost.empty ""
def wolf : CardDef := creature "Wolf" ManaCost.empty #[] 1 1

def sacTwoArtifacts : TriggeredAbility.TriggerResolution :=
  .may (.pay (.sacrifice (.fixed 2) .artifact)) (.draw (.fixed 1)) .ifYouDo

def sacPerOther : TriggeredAbility.TriggerResolution :=
  .may (.pay (.sacrifice .perOtherCreature .artifact)) (.draw (.fixed 1)) .ifYouDo

def sacHand : TriggeredAbility.TriggerResolution :=
  .may (.pay (.sacrifice (.fixed 1) .hand)) (.draw (.fixed 1)) .ifYouDo

def sacZero : TriggeredAbility.TriggerResolution :=
  .may (.pay (.sacrifice (.fixed 0) .artifact)) (.draw (.fixed 1)) .ifYouDo

def field : CardDef := land "Field" ""

/- Printed phrases stay the sentences those payments used. -/
#guard phrase payDraw == "you may pay {1}. If you do, draw a card"
#guard phrase payPlusOne ==
  "you may pay {2}. If you do, put a +1/+1 counter on this creature and draw a card"
#guard phrase payReturn ==
  "you may pay {1}{G}{U}. If you do, return this card from your graveyard to your hand"
#guard phrase sacPower ==
  "you may sacrifice another creature. If you do, put a number of +1/+1 counters on this creature equal to the sacrificed creature's power"
#guard phrase sacTreasure ==
  "you may sacrifice another creature or artifact. If you do, draw a card and create a Treasure token"
#guard phrase sacOrDiscard ==
  "you may sacrifice an artifact or discard a card. If you do, draw a card"
#guard phrase sacDestroy ==
  "you may sacrifice another creature. When you do, destroy target nonland permanent an opponent controls"
#guard phrase sacDamage ==
  "you may sacrifice an artifact or discard a nonland card. When you do, this deals 2 damage to any target"
#guard phrase (.pay (.mana #[.generic 1])) == "pay {1}"
#guard phrase (.pay (.sacrifice (.fixed 1) .another)) == "pay that cost"

/- `{1}` offers a generic payment. Declining skips the draw. Paying draws. -/
#guard
  let g := step (withMana afterDraw) payDraw
  match g.pending with
  | .mayPayGeneric p 1 => p == caster && logContains g "may pay {1}"
  | _ => false

#guard
  let g0 := step (withMana afterDraw) payDraw
  let before := handSize g0 caster
  let g := mustApply g0 caster .decline
  handSize g caster == before && g.pending == .none && logContains g "declines to pay"

#guard
  let g0 := step (withMana afterDraw) payDraw
  let before := handSize g0 caster
  let g := mustApply g0 caster .payGeneric
  handSize g caster == before + 1 && g.pending == .none

/- `{2}` puts a +1/+1 counter on the source and draws. -/
#guard
  let g0 := addPermanent (withMana afterDraw) bear caster caster
  let g := step g0 payPlusOne (some (pid g0 "Bear"))
  match g.pending with
  | .mayPayGeneric p 2 => p == caster && logContains g "put a +1/+1 counter"
  | _ => false

#guard
  let g0 := addPermanent (withMana afterDraw) bear caster caster
  let before := handSize g0 caster
  let g := mustApply (step g0 payPlusOne (some (pid g0 "Bear"))) caster .payGeneric
  counters g "Bear" == 1 && handSize g caster == before + 1

/- `{1}{G}{U}` returns the source from its owner's graveyard. A source still
on the battlefield is reported. -/
#guard
  let g0 := putInGraveyard (withMana afterDraw) bear caster
  let id := namedIn g0 (g0.player caster).graveyard "Bear"
  let g := step g0 payReturn (some id)
  match g.pending with
  | .fraChoice p (.mayPaySymbolsThen _ _ sid) => p == caster && sid == id
  | _ => false

#guard
  let g0 := putInGraveyard (withMana afterDraw) bear caster
  let id := namedIn g0 (g0.player caster).graveyard "Bear"
  let g := mustApply (step g0 payReturn (some id)) caster .accept
  inHand g caster "Bear" && !buried g "Bear"

#guard
  let g0 := addPermanent (withMana afterDraw) bear caster caster
  let g := step g0 payReturn (some (pid g0 "Bear"))
  g.pending == .none && onBoard g "Bear" &&
    logContains g "Bear is no longer in the graveyard"

/- Sacrificing another creature notes its power as +1/+1 counters.
No other creature skips the counters. Declining sacrifices nothing. -/
#guard
  let g0 := addPermanent afterDraw bear caster caster
  let g := step g0 sacPower (some (pid g0 "Bear"))
  g.pending == .none && counters g "Bear" == 0 &&
    logContains g "No other creature to sacrifice"

#guard
  let g0 := addPermanent (addPermanent afterDraw bear caster caster) ox caster caster
  let g := step g0 sacPower (some (pid g0 "Bear"))
  match g.pending with
  | .fraChoice p (.maySacrificeAnotherCreatureForPower sid) =>
    p == caster && sid == pid g0 "Bear"
  | _ => false

#guard
  let g0 := addPermanent (addPermanent afterDraw bear caster caster) ox caster caster
  let g := mustApply (step g0 sacPower (some (pid g0 "Bear"))) caster .decline
  counters g "Bear" == 0 && onBoard g "Ox"

#guard
  let g0 := addPermanent (addPermanent afterDraw bear caster caster) ox caster caster
  let g := mustApply (step g0 sacPower (some (pid g0 "Bear"))) caster
    (.choosePermanents #[pid g0 "Ox"])
  counters g "Bear" == 3 && buried g "Ox" && !onBoard g "Ox"

/- Sacrificing another creature or artifact draws and creates a Treasure.
Nothing else to sacrifice skips both. -/
#guard
  let g0 := addPermanent afterDraw bear caster caster
  let g := step g0 sacTreasure (some (pid g0 "Bear"))
  g.pending == .none && logContains g "Nothing to sacrifice" &&
    !onBoard g "Treasure"

#guard
  let g0 := addPermanent (addPermanent afterDraw bear caster caster) relic caster caster
  let g := step g0 sacTreasure (some (pid g0 "Bear"))
  match g.pending with
  | .fraChoice p (.maySacrificeAnotherForDrawTreasure sid) =>
    p == caster && sid == pid g0 "Bear"
  | _ => false

#guard
  let g0 := addPermanent (addPermanent afterDraw bear caster caster) relic caster caster
  let before := handSize g0 caster
  let g := mustApply (step g0 sacTreasure (some (pid g0 "Bear"))) caster
    (.choosePermanents #[pid g0 "Relic"])
  handSize g caster == before + 1 && buried g "Relic" && onBoard g "Treasure"

/- Sacrificing an artifact, or discarding a card, draws. Declining draws
nothing. -/
#guard
  let g := step afterDraw sacOrDiscard
  match g.pending with
  | .maySacArtifactOrDiscard p 1 => p == caster
  | _ => false

#guard
  let g0 := step afterDraw sacOrDiscard
  let before := handSize g0 caster
  let g := mustApply g0 caster .decline
  handSize g caster == before && g.pending == .none &&
    logContains g "declines to sacrifice an artifact or discard a card"

#guard
  let g0 := addPermanent afterDraw relic caster caster
  let before := handSize g0 caster
  let g := mustApply (step g0 sacOrDiscard (some (pid g0 "Relic"))) caster
    (.sacrifice (pid g0 "Relic"))
  handSize g caster == before + 1 && buried g "Relic"

#guard
  let g0 := step afterDraw sacOrDiscard
  let id := (g0.player caster).hand.back!
  let before := handSize g0 caster
  let gy := (g0.player caster).graveyard.size
  let g := mustApply g0 caster (.discard id)
  handSize g caster == before && (g.player caster).graveyard.size == gy + 1

/- Sacrificing another creature queues the destroy reflexive. No other
creature queues nothing. -/
#guard
  let g0 := addPermanent afterDraw bear caster caster
  let g := step g0 sacDestroy (some (pid g0 "Bear"))
  g.pending == .none && g.stack.isEmpty &&
    logContains g "no other creature to sacrifice"

#guard
  let g0 := addPermanent (addPermanent afterDraw bear caster caster) ox caster caster
  let g0 := addPermanent g0 oppRelic opp opp
  let g := step g0 sacDestroy (some (pid g0 "Bear"))
  match g.pending with
  | .fraChoice p (.mayPayPickThen (.sacrificeAnotherSubtype "Creature") _ sid) =>
    p == caster && sid == pid g0 "Bear"
  | _ => false

#guard
  let g0 := addPermanent (addPermanent afterDraw bear caster caster) ox caster caster
  let g0 := addPermanent g0 oppRelic opp opp
  let g := mustApply (step g0 sacDestroy (some (pid g0 "Bear"))) caster .decline
  g.stack.isEmpty && onBoard g "Ox" && onBoard g "Opp Relic"

#guard
  let g0 := addPermanent (addPermanent afterDraw bear caster caster) ox caster caster
  let g0 := addPermanent g0 oppRelic opp opp
  let g := mustApply (step g0 sacDestroy (some (pid g0 "Bear"))) caster
    (.choosePermanents #[pid g0 "Ox"])
  buried g "Ox" && logContains g "reflexive ability is put on the stack"

/- Sacrificing an artifact or discarding a nonland queues the damage
reflexive. Nothing to pay queues nothing. -/
#guard
  let g0 := emptyHand (addPermanent afterDraw bear caster caster)
  let g := step g0 sacDamage (some (pid g0 "Bear"))
  g.pending == .none && g.stack.isEmpty

#guard
  let g0 := addPermanent (addPermanent afterDraw bear caster caster) relic caster caster
  let g := step g0 sacDamage (some (pid g0 "Bear"))
  match g.pending with
  | .fraChoice p (.mayPayPickThen .sacrificeArtifactOrDiscardNonland _ sid) =>
    p == caster && sid == pid g0 "Bear"
  | _ => false

#guard
  let g0 := addPermanent (addPermanent afterDraw bear caster caster) relic caster caster
  let g := mustApply (step g0 sacDamage (some (pid g0 "Bear"))) caster
    (.choosePermanents #[pid g0 "Relic"])
  buried g "Relic" && logContains g "reflexive ability is put on the stack"

/- Either order of artifact and discard is the same combined payment. -/
#guard
  let g := step afterDraw sacOrDiscardReversed
  match g.pending with
  | .maySacArtifactOrDiscard p 1 => p == caster
  | _ => false

/- Sacrificing an artifact on its own draws. Nothing to sacrifice skips the draw. -/
#guard
  let g := step afterDraw payArtifact
  g.pending == .none

#guard
  let g0 := addPermanent afterDraw relic caster caster
  let g := step g0 payArtifact (some (pid g0 "Relic"))
  match g.pending with
  | .fraChoice p (.mayPayPickThen .sacrificeArtifact _ _) => p == caster
  | _ => false

#guard
  let g0 := addPermanent afterDraw relic caster caster
  let before := handSize g0 caster
  let g := mustApply (step g0 payArtifact (some (pid g0 "Relic"))) caster
    (.choosePermanents #[pid g0 "Relic"])
  handSize g caster == before + 1 && buried g "Relic"

/- Discarding a nonland draws. A hand of only lands skips the draw. -/
#guard
  let g := step (putInHand (emptyHand afterDraw) field caster) payNonland
  g.pending == .none

#guard
  let g0 := putInHand (emptyHand afterDraw) bear caster
  let g := step g0 payNonland
  match g.pending with
  | .fraChoice p (.mayPayPickThen .discardNonland _ _) => p == caster
  | _ => false

#guard
  let g0 := putInHand (emptyHand afterDraw) bear caster
  let id := namedIn g0 (g0.player caster).hand "Bear"
  let g := mustApply (step g0 payNonland) caster (.choosePermanents #[id])
  buried g "Bear" && handSize g caster == 1

/- An `or` of other costs offers each one that can be paid. -/
#guard
  let g := step afterDraw sacOrMana
  g.pending == .none

#guard
  let g := step (withMana afterDraw) sacOrMana
  match g.pending with
  | .mayPayGeneric p 1 => p == caster
  | _ => false

#guard
  let g0 := addPermanent (withMana afterDraw) relic caster caster
  let g := step g0 sacOrMana (some (pid g0 "Relic"))
  match g.pending with
  | .chooseTriggerOr p => p == caster
  | _ => false

#guard
  let g0 := addPermanent (withMana afterDraw) relic caster caster
  let g := mustApply (step g0 sacOrMana (some (pid g0 "Relic"))) caster (.chooseMode 0)
  match g.pending with
  | .fraChoice p (.mayPayPickThen .sacrificeArtifact _ _) => p == caster
  | _ => false

#guard
  let g0 := addPermanent (withMana afterDraw) relic caster caster
  let before := handSize g0 caster
  let g := mustApply
    (mustApply (step g0 sacOrMana (some (pid g0 "Relic"))) caster (.chooseMode 1))
    caster .payGeneric
  handSize g caster == before + 1 && onBoard g "Relic"

/- Any other count sacrifices that many permanents the selector names.
One artifact cannot pay for two. Declining sacrifices nothing. -/
#guard phrase sacTwoArtifacts == "you may sacrifice that. If you do, do that"

#guard
  let g0 := addPermanent afterDraw relic caster caster
  let g := step g0 sacTwoArtifacts (some (pid g0 "Relic"))
  g.pending == .none && onBoard g "Relic" && logContains g "Nothing to sacrifice"

#guard
  let g0 := addPermanent (addPermanent afterDraw relic caster caster) relicTwo caster caster
  let g := step g0 sacTwoArtifacts (some (pid g0 "Relic"))
  match g.pending with
  | .fraChoice p (.maySacrificeThese n ids) =>
    p == caster && n == 2 && ids.size == 2 &&
      ids.any (· == pid g0 "Relic") && ids.any (· == pid g0 "Relic Two") &&
      logContains g "may sacrifice 2 permanents"
  | _ => false

#guard
  let g0 := addPermanent (addPermanent afterDraw relic caster caster) relicTwo caster caster
  let before := handSize g0 caster
  let g := mustApply (step g0 sacTwoArtifacts (some (pid g0 "Relic"))) caster .decline
  handSize g caster == before && onBoard g "Relic" && onBoard g "Relic Two"

#guard
  let g0 := addPermanent (addPermanent afterDraw relic caster caster) relicTwo caster caster
  let before := handSize g0 caster
  let g := mustApply (step g0 sacTwoArtifacts (some (pid g0 "Relic"))) caster
    (.choosePermanents #[pid g0 "Relic", pid g0 "Relic Two"])
  handSize g caster == before + 1 && buried g "Relic" && buried g "Relic Two"

/- `.perOtherCreature` is how many artifacts are sacrificed. A hand is not
a permanent, and zero pays nothing. -/
#guard
  let g0 := addPermanent (addPermanent afterDraw bear caster caster) ox caster caster
  let g0 := addPermanent g0 relic caster caster
  let g := step g0 sacPerOther (some (pid g0 "Bear"))
  match g.pending with
  | .fraChoice p (.maySacrificeThese n ids) =>
    p == caster && n == 1 && ids.size == 1 && ids[0]? == some (pid g0 "Relic") &&
      logContains g "may sacrifice a permanent"
  | _ => false

#guard
  let g0 := addPermanent (addPermanent afterDraw bear caster caster) ox caster caster
  let g0 := addPermanent g0 relic caster caster
  let before := handSize g0 caster
  let g := mustApply (step g0 sacPerOther (some (pid g0 "Bear"))) caster
    (.choosePermanents #[pid g0 "Relic"])
  handSize g caster == before + 1 && buried g "Relic" && onBoard g "Bear" && onBoard g "Ox"

#guard
  let g0 := addPermanent
    (addPermanent (addPermanent afterDraw bear caster caster) ox caster caster) wolf caster caster
  let g0 := addPermanent g0 relic caster caster
  let before := handSize g0 caster
  let g := step g0 sacPerOther (some (pid g0 "Bear"))
  g.pending == .none && handSize g caster == before && onBoard g "Relic" &&
    logContains g "Nothing to sacrifice"

#guard
  let g0 := addPermanent afterDraw relic caster caster
  let before := handSize g0 caster
  let g := step g0 sacHand (some (pid g0 "Relic"))
  g.pending == .none && handSize g caster == before && onBoard g "Relic" &&
    logContains g "Nothing to sacrifice"

#guard
  let g0 := addPermanent afterDraw relic caster caster
  let before := handSize g0 caster
  let g := step g0 sacZero (some (pid g0 "Relic"))
  g.pending == .none && handSize g caster == before && onBoard g "Relic" &&
    logContains g "Nothing to sacrifice"

def payDiscard : TriggeredAbility.TriggerResolution :=
  .may (.pay (.discard (.fixed 1) .card)) (.draw (.fixed 1)) .ifYouDo

def discardTwo : TriggeredAbility.TriggerResolution :=
  .may (.pay (.discard (.fixed 2) .card)) (.draw (.fixed 1)) .ifYouDo

def discardPerPlains : TriggeredAbility.TriggerResolution :=
  .may (.pay (.discard .perPlains .nonland)) (.draw (.fixed 1)) .ifYouDo

def discardArtifact : TriggeredAbility.TriggerResolution :=
  .may (.pay (.discard (.fixed 1) .artifact)) (.draw (.fixed 1)) .ifYouDo

def discardZero : TriggeredAbility.TriggerResolution :=
  .may (.pay (.discard (.fixed 0) .card)) (.draw (.fixed 1)) .ifYouDo

def plains : CardDef := land "Plains" "" (subtypes := #["Plains"])

/- Discarding a card draws. An empty hand skips the draw. -/
#guard phrase payDiscard == "you may discard that. If you do, do that"

#guard
  let g := step (emptyHand afterDraw) payDiscard
  g.pending == .none

#guard
  let g0 := putInHand (emptyHand afterDraw) bear caster
  let g := step g0 payDiscard
  match g.pending with
  | .fraChoice p (.mayPayPickThen .discardACard _ _) => p == caster
  | _ => false

#guard
  let g0 := putInHand (emptyHand afterDraw) bear caster
  let id := namedIn g0 (g0.player caster).hand "Bear"
  let g := mustApply (step g0 payDiscard) caster (.choosePermanents #[id])
  buried g "Bear" && handSize g caster == 1

/- Any other count discards that many cards the selector names.
One card cannot pay for two. Declining discards nothing. -/
#guard phrase discardTwo == "you may discard that. If you do, do that"

#guard
  let g0 := putInHand (emptyHand afterDraw) bear caster
  let before := handSize g0 caster
  let g := step g0 discardTwo
  g.pending == .none && handSize g caster == before &&
    logContains g "Nothing to discard"

#guard
  let g0 := putInHand (putInHand (emptyHand afterDraw) bear caster) ox caster
  let g := step g0 discardTwo
  let bearId := namedIn g0 (g0.player caster).hand "Bear"
  let oxId := namedIn g0 (g0.player caster).hand "Ox"
  match g.pending with
  | .fraChoice p (.mayDiscardThese n ids) =>
    p == caster && n == 2 && ids.size == 2 &&
      ids.any (· == bearId) && ids.any (· == oxId) &&
      logContains g "may discard 2 cards"
  | _ => false

#guard
  let g0 := putInHand (putInHand (emptyHand afterDraw) bear caster) ox caster
  let g := mustApply (step g0 discardTwo) caster .decline
  inHand g caster "Bear" && inHand g caster "Ox" && handSize g caster == 2

#guard
  let g0 := putInHand (putInHand (emptyHand afterDraw) bear caster) ox caster
  let bearId := namedIn g0 (g0.player caster).hand "Bear"
  let oxId := namedIn g0 (g0.player caster).hand "Ox"
  let g := mustApply (step g0 discardTwo) caster (.choosePermanents #[bearId, oxId])
  buried g "Bear" && buried g "Ox" && handSize g caster == 1

/- `.perPlains` is how many nonland cards are discarded. A land is not
a nonland, an artifact is not a card in hand, and zero pays nothing. -/
#guard
  let g0 := addPermanent (putInHand (emptyHand afterDraw) bear caster) plains caster caster
  let g := step g0 discardPerPlains
  let bearId := namedIn g0 (g0.player caster).hand "Bear"
  match g.pending with
  | .fraChoice p (.mayDiscardThese n ids) =>
    p == caster && n == 1 && ids.size == 1 && ids[0]? == some bearId &&
      logContains g "may discard a card"
  | _ => false

#guard
  let g0 := addPermanent (putInHand (emptyHand afterDraw) bear caster) plains caster caster
  let bearId := namedIn g0 (g0.player caster).hand "Bear"
  let g := mustApply (step g0 discardPerPlains) caster (.choosePermanents #[bearId])
  buried g "Bear" && handSize g caster == 1 && onBoard g "Plains"

#guard
  let g0 := addPermanent
    (addPermanent (putInHand (emptyHand afterDraw) bear caster) plains caster caster)
    plains caster caster
  let before := handSize g0 caster
  let g := step g0 discardPerPlains
  g.pending == .none && handSize g caster == before &&
    logContains g "Nothing to discard"

#guard
  let g0 := addPermanent (putInHand (emptyHand afterDraw) bear caster) relic caster caster
  let before := handSize g0 caster
  let g := step g0 discardArtifact (some (pid g0 "Relic"))
  g.pending == .none && handSize g caster == before && onBoard g "Relic" &&
    logContains g "Nothing to discard"

#guard
  let g0 := putInHand (emptyHand afterDraw) bear caster
  let before := handSize g0 caster
  let g := step g0 discardZero
  g.pending == .none && handSize g caster == before && inHand g caster "Bear" &&
    logContains g "Nothing to discard"

end Mtg.Engine.PayTests
