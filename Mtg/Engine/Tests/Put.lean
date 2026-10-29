import Mtg.Engine.Fixture

/-!
# `TriggerResolution.put`

Which cards is an `ObjectSelector`.
Cards the source exiled, a graveyard nonland, the source returned as an
artifact, noted lands, a discarded land, a land from hand, and an artifact
from hand.
Any other selector puts nothing.
-/

namespace Mtg.Engine.PutTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def owner : PlayerId := ⟨1⟩

def isle : CardDef := land "Test Isle" "({T}: Add {C}.)" (tapAddMana := #[.colorless])

def bear : CardDef :=
  creature "Test Bear" (ManaCost.ofGeneric 2) #["Bear"] 2 2

def beast : CardDef :=
  creature "Costly Beast" (ManaCost.ofGeneric 4) #["Beast"] 4 4

def hunter : CardDef :=
  creature "Test Hunter" (ManaCost.ofGeneric 1) #["Human"] 1 1

def bauble : CardDef := artifact "Test Bauble" (ManaCost.ofGeneric 1) ""

def sword : CardDef :=
  equipment "Test Sword" (ManaCost.ofGeneric 1) "" (ManaCost.ofGeneric 2)

def putInHand (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.hand p) none {} (fun id _ =>
    #[.pushHand id])

def putInGraveyard (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.graveyard p) none {} (fun id _ =>
    #[.pushGraveyard id])

def putInExile (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p .exile

def idNamed (g : Game) (ids : Array ObjectId) (name : String) : Option ObjectId :=
  ids.find? (fun id => (g.findObject? id).any (·.name == name))

def exileId (g : Game) (name : String) : Option ObjectId :=
  (g.objects.find? (fun o => o.name == name && o.zone == .exile)).map GameObject.id

def onBoard (g : Game) (name : String) : Option GameObject :=
  g.battlefield.find? (·.name == name)

def inExile (g : Game) (name : String) : Bool :=
  g.objects.any (fun o => o.name == name && o.zone == .exile)

def putStep (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[]) : Game :=
  g.applyTriggeredAbility caster (.onEnterDraw 1) sourceId targets
    (resolutionOverride := some r)

/- Cards exiled by the source return under their owners. A missing source
returns nothing. -/
#guard
  let g := addPermanent afterDraw hunter caster caster
  let g := putInExile (putInExile g bear owner) beast caster
  let bearId := exileId g "Test Bear"
  let beastId := exileId g "Costly Beast"
  let src := onBoard g "Test Hunter"
  match bearId, beastId, src with
  | some bearId, some beastId, some src =>
    let g := g.changeObjects src.id
      #[.leaveTriggerExile #[bearId], .linkedExile #[beastId]]
    let g := g.applyTriggeredAbility caster .onLeaveReturnExiled (some src.id)
    match onBoard g "Test Bear", onBoard g "Costly Beast", onBoard g "Test Hunter" with
    | some bear, some beast, some _ =>
      bear.controller == some owner && !bear.status.tapped &&
        beast.controller == some caster && !beast.status.tapped &&
        logContains g "returns to the battlefield"
    | _, _, _ => false
  | _, _, _ => false

#guard
  let g := putInExile afterDraw bear owner
  let g := putStep g (.put .linkedExile)
  inExile g "Test Bear" && (onBoard g "Test Bear").isNone

/- A graveyard nonland of mana value 3 or less enters under its owner.
No target, a land, and a mana value 4 creature do not enter. -/
#guard
  let g := putInGraveyard afterDraw bear owner
  match idNamed g (g.player owner).graveyard "Test Bear" with
  | none => false
  | some id =>
    let g := g.applyTriggeredAbility caster (.onCombatDamagePutNonlandMvAtMost 3)
      none #[Target.card id]
    match onBoard g "Test Bear" with
    | some o =>
      o.controller == some owner && !o.status.tapped &&
        !(g.player owner).graveyard.contains id &&
        logContains g "under its owner's control"
    | none => false

#guard
  let g := putInGraveyard afterDraw bear owner
  let g := g.applyTriggeredAbility caster (.onCombatDamagePutNonlandMvAtMost 3) none
  (onBoard g "Test Bear").isNone && logContains g "No card was chosen"

#guard
  let g := putInGraveyard (putInGraveyard afterDraw isle caster) beast caster
  let land := idNamed g (g.player caster).graveyard "Test Isle"
  let costly := idNamed g (g.player caster).graveyard "Costly Beast"
  match land, costly with
  | some land, some costly =>
    let g := g.applyTriggeredAbility caster (.onCombatDamagePutNonlandMvAtMost 3)
      none #[Target.card land]
    let g := g.applyTriggeredAbility caster (.onCombatDamagePutNonlandMvAtMost 3)
      none #[Target.card costly]
    (onBoard g "Test Isle").isNone && (onBoard g "Costly Beast").isNone &&
      logContains g "no longer legal"
  | _, _ => false

/- The source returns from its owner's graveyard as an artifact. Still on
the battlefield, it stays a creature. -/
#guard
  let g := addPermanent afterDraw bear caster caster
  match onBoard g "Test Bear" with
  | none => false
  | some src =>
    let (g, gid) := g.move src.id (.graveyard caster) none
    let g := g.applyTriggeredAbility caster .onDiesReturnAsArtifact (some gid)
    match onBoard g "Test Bear" with
    | some o =>
      !g.isCreature o && (g.types o).contains .artifact && g.returnedAsArtifact o &&
        logContains g "returns as an artifact"
    | none => false

#guard
  let g := addPermanent afterDraw bear caster caster
  match onBoard g "Test Bear" with
  | none => false
  | some src =>
    let g := g.applyTriggeredAbility caster .onDiesReturnAsArtifact (some src.id)
    match onBoard g "Test Bear" with
    | some o => g.isCreature o && !g.returnedAsArtifact o
    | none => false

/- Lands noted by the previous exile return tapped. An empty note returns
nothing. -/
#guard
  let g := addPermanent afterDraw isle caster caster
  match onBoard g "Test Isle" with
  | none => false
  | some land =>
    let (g, eid) := g.move land.id .exile none
    let g := putStep (g.change (.exiledIdsThisWay #[eid]))
      (.put .notedLands (how := .tapped))
    match onBoard g "Test Isle" with
    | some o =>
      o.status.tapped && o.controller == some caster && g.exiledIdsThisWay.isEmpty &&
        logContains g "returned tapped"
    | none => false

#guard
  let g := putStep afterDraw (.put .notedLands (how := .tapped))
  g.exiledIdsThisWay.isEmpty && (onBoard g "Test Isle").isNone

/- A land discarded this way enters tapped. A nonland, and a missing note,
do not. -/
#guard
  let g := putInGraveyard afterDraw isle caster
  match idNamed g (g.player caster).graveyard "Test Isle" with
  | none => false
  | some id =>
    let g := putStep (g.change (.discardedCardThisWay (some (caster, id))))
      (.put .discardedLand (how := .tapped))
    match onBoard g "Test Isle" with
    | some o =>
      o.status.tapped && g.discardedCardThisWay.isNone &&
        logContains g "enters the battlefield tapped"
    | none => false

#guard
  let g := putInGraveyard afterDraw bear caster
  match idNamed g (g.player caster).graveyard "Test Bear" with
  | none => false
  | some id =>
    let g := putStep (g.change (.discardedCardThisWay (some (caster, id))))
      (.put .discardedLand (how := .tapped))
    (onBoard g "Test Bear").isNone && g.discardedCardThisWay.isNone &&
      (g.player caster).graveyard.contains id

#guard
  let g := putStep afterDraw (.put .discardedLand (how := .tapped))
  g.discardedCardThisWay.isNone && (onBoard g "Test Isle").isNone

/- You may put a land from hand tapped. Declining leaves it in hand. -/
#guard
  let g := putInHand afterDraw isle caster
  match idNamed g (g.player caster).hand "Test Isle" with
  | none => false
  | some id =>
    let g := putStep g (.may (.put .landFromHand (how := .tapped)) (.sequence []))
    let offered :=
      match g.pending with
      | .mayPutLandFromHand p => p == caster
      | _ => false
    let g := mustApply g caster .decline
    offered && g.pending == .none &&
      (g.player caster).hand.contains id && (onBoard g "Test Isle").isNone

#guard
  let g := putInHand afterDraw isle caster
  match idNamed g (g.player caster).hand "Test Isle" with
  | none => false
  | some id =>
    let g := putStep g (.put .landFromHand (how := .tapped))
    let g := mustApply g caster (.cast id)
    match onBoard g "Test Isle" with
    | some o => o.status.tapped && !(g.player caster).hand.contains id
    | none => false

/- You may put an artifact from hand. Equipment is remembered for the
attach; another artifact is not. An empty hand skips the choice. -/
#guard
  let g := addPermanent afterDraw hunter caster caster
  match onBoard g "Test Hunter" with
  | none => false
  | some host =>
    let g := putInHand g sword caster
    match idNamed g (g.player caster).hand "Test Sword" with
    | none => false
    | some id =>
      let g := putStep g (.may (.put .artifactFromHand (note := .forAttach)) (.sequence []))
        (some host.id)
      let offered :=
        match g.pending with
        | .mayPutArtifactFromHand p hid => p == caster && hid == host.id
        | _ => false
      let g := mustApply g caster (.cast id)
      match g.putArtifactThisWay, onBoard g "Test Sword" with
      | some (putId, hid), some sword =>
        let (g, holds) := g.triggerIfHolds caster (.onEnterDraw 1) (some host.id)
          #[] none (.atLeast (.count .putEquipment) (.fixed 1))
        offered && putId == sword.id && hid == host.id && holds &&
          g.putArtifactThisWay.isSome
      | _, _ => false

#guard
  let g := addPermanent afterDraw hunter caster caster
  match onBoard g "Test Hunter" with
  | none => false
  | some host =>
    let g := putInHand g bauble caster
    match idNamed g (g.player caster).hand "Test Bauble" with
    | none => false
    | some id =>
      let g := putStep g (.put .artifactFromHand (note := .forAttach)) (some host.id)
      let g := mustApply g caster (.cast id)
      let (g, holds) := g.triggerIfHolds caster (.onEnterDraw 1) (some host.id)
        #[] none (.atLeast (.count .putEquipment) (.fixed 1))
      !holds && g.putArtifactThisWay.isNone && (onBoard g "Test Bauble").isSome

#guard
  let g := addPermanent (putInHand afterDraw isle caster) hunter caster caster
  match onBoard g "Test Hunter" with
  | none => false
  | some host =>
    let g := putStep g (.put .artifactFromHand (note := .forAttach)) (some host.id)
    g.pending == .none && logContains g "no artifact" && g.putArtifactThisWay.isNone

#guard
  let g := addPermanent afterDraw hunter caster caster
  match onBoard g "Test Hunter" with
  | none => false
  | some host =>
    let g := putInHand g bauble caster
    match idNamed g (g.player caster).hand "Test Bauble" with
    | none => false
    | some id =>
      let g := putStep g (.put .artifactFromHand (note := .forAttach)) (some host.id)
      let g := mustApply g caster .decline
      g.pending == .none && g.putArtifactThisWay.isNone &&
        (g.player caster).hand.contains id

/- A hand, a player, an untargeted graveyard card, a battlefield source,
a missing cause, an empty linked exile, and lands that were not exiled
put nothing. The top card of the library enters. -/
#guard
  let g0 := putInGraveyard (addPermanent afterDraw bear caster caster) beast caster
  let sid := (onBoard g0 "Test Bear").map (·.id)
  let quiet := [
    putStep g0 (.put .target) sid,
    putStep g0 (.put .hand) sid,
    putStep g0 (.put (.player .you)) sid,
    putStep g0 (.put .graveyardCard) sid,
    putStep g0 (.put .source) sid,
    putStep g0 (.put .cause) sid,
    putStep g0 (.put .linkedExile (how := .tapped)) sid,
    putStep g0 (.put .notedLands) sid]
  quiet.all fun g =>
    (onBoard g "Test Bear").isSome && (onBoard g "Costly Beast").isNone &&
      g.pending == .none && g.log == g0.log && g.exiledIdsThisWay == g0.exiledIdsThisWay

#guard
  let g0 := putInGraveyard (addPermanent afterDraw bear caster caster) beast caster
  let before := (g0.player caster).library.size
  let g := putStep g0 (.put .top) ((onBoard g0 "Test Bear").map (·.id))
  (g.player caster).library.size == before - 1 &&
    (onBoard g "Test Bear").isSome && (onBoard g "Costly Beast").isNone &&
    logContains g "is put onto the battlefield"

/- Printed phrases stay with the combination that produces them. -/
#guard TriggeredAbility.resolutionPhrase { resolution := .put .linkedExile } ==
  "return the exiled card to the battlefield under its owner's control"
#guard TriggeredAbility.resolutionPhrase { resolution := .put (.nonlandMvAtMost 3) } ==
  "put up to one target nonland permanent card with mana value 3 or less from a graveyard onto the battlefield under its owner's control"
#guard TriggeredAbility.resolutionPhrase { resolution := .put .source (how := .asArtifact) } ==
  "if they were a creature, return them to the battlefield. They're an artifact"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .put .source .underOwner (.entering [.loseAllAbilities]) } ==
  "return this from its owner's graveyard to the battlefield under its owner's control"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .put (.cause (some .villain)) .underOwner } ==
  "return it to the battlefield under its owner's control"
#guard TriggeredAbility.resolutionPhrase { resolution := .put .landFromHand (how := .tapped) } ==
  "put a land card from your hand onto the battlefield tapped"
#guard TriggeredAbility.resolutionPhrase { resolution := .put .target } ==
  "put it onto the battlefield"

end Mtg.Engine.PutTests
