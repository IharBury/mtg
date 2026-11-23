import Mtg.Engine.Fixture

/-!
# Unified put-onto-battlefield instructions (`Instruction.moveZone ... (.battlefield ...)`)

Cards exiled by the source, a graveyard nonland, the source returning as an
artifact, lands exiled and returned tapped, a discarded land entering tapped,
a land from hand, an artifact from hand with Equipment attach, and top of
library all execute through unified `Instruction`.
-/

namespace Mtg.Engine.PutTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests hiding afterDraw

def afterDraw : Game := Mtg.Engine.Tests.afterDraw.change (.pushContinuationFrame {})

def caster : PlayerId := ⟨0⟩
def owner : PlayerId := ⟨1⟩

def isle : CardDef :=
  land "Test Isle" "({T}: Add {C}.)"
    (activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 1)])])

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
  insertObject g card p (.hand p)

def putInGraveyard (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.graveyard p)

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

def stepBody (g : Game) (body : Instruction)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[]) : Game :=
  g.applyTriggeredAbility caster (TriggeredAbility.mkTrigger .thisEnters { body }) sourceId targets

/- Cards exiled by the source return under their owners. A missing source returns nothing. -/
#guard
  let g := addPermanent afterDraw hunter caster caster
  let g := putInExile (putInExile g bear owner) beast caster
  let bearId := exileId g "Test Bear"
  let beastId := exileId g "Costly Beast"
  let src := onBoard g "Test Hunter"
  match bearId, beastId, src with
  | some bearId, some beastId, some src =>
    let g := (g.changeObject src.id (.pushLeaveTriggerExile bearId)).changeObject src.id
      (.linkedExile #[beastId])
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
  let g := g.applyTriggeredAbility caster .onLeaveReturnExiled none
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
  (onBoard g "Test Bear").isNone

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
    (onBoard g "Test Isle").isNone && (onBoard g "Costly Beast").isNone
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
      !g.isCreature o && (g.types o).contains .artifact && g.returnedAsArtifact o
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

/- Lands exiled and returned tapped via unified `onEnterExileLandsThenReturnTapped`. -/
#guard
  let g := addPermanent afterDraw isle caster caster
  match onBoard g "Test Isle" with
  | none => false
  | some land =>
    let g := g.applyTriggeredAbility caster .onEnterExileLandsThenReturnTapped none
      #[Target.permanent land.id]
    match onBoard g "Test Isle" with
    | some o => o.status.tapped && o.controller == some caster
    | none => false

/- Loot-then-put-discarded-land-tapped (`onEnterLootLandEntersTapped`): a discarded land
enters tapped while a discarded creature stays in the graveyard. -/
#guard
  let g := putInHand (emptyHand afterDraw caster) isle caster
  let g := g.applyTriggeredAbility caster .onEnterLootLandEntersTapped none
  match idNamed g (g.player caster).hand "Test Isle" with
  | none => false
  | some id =>
    let g := mustApply g caster (.discard id)
    match onBoard g "Test Isle" with
    | some o => o.status.tapped
    | none => false

#guard
  let g := putInHand (emptyHand afterDraw caster) bear caster
  let g := g.applyTriggeredAbility caster .onEnterLootLandEntersTapped none
  match idNamed g (g.player caster).hand "Test Bear" with
  | none => false
  | some id =>
    let g := mustApply g caster (.discard id)
    (onBoard g "Test Bear").isNone &&
      (g.player caster).graveyard.any (fun gid => (g.findObject? gid).any (·.name == "Test Bear"))

/- You may put a land from hand tapped. Declining leaves it in hand; choosing puts it tapped. -/
#guard
  let g := putInHand afterDraw isle caster
  match idNamed g (g.player caster).hand "Test Isle" with
  | none => false
  | some id =>
    let putLandEff : Effect := {
      body := Instruction.may .you none
        (.moveZone (.inZones (.handOf .you) (.hasType .land)) (.battlefield .controller) .put {
          tapped := true
          choice? := some { chooser := .controller, count := .exact (.const 1) }
        })
    }
    let offered := g.applyTriggeredAbility caster (.onEnter putLandEff) none
    let declined := mustApply offered caster .decline
    let put := mustApply offered caster (.cast id)
    offered.pending != .none && declined.pending == .none &&
      (declined.player caster).hand.contains id && (onBoard declined "Test Isle").isNone &&
      (onBoard put "Test Isle").any (·.status.tapped)

/- You may put an artifact from hand; if it's an Equipment, attach it to the source. -/
#guard
  let g := addPermanent afterDraw hunter caster caster
  match onBoard g "Test Hunter" with
  | none => false
  | some host =>
    let g := putInHand g sword caster
    match idNamed g (g.player caster).hand "Test Sword" with
    | none => false
    | some id =>
      let offered := g.applyTriggeredAbility caster .onCombatMayPutArtifactAttachEquipment (some host.id)
      let done := mustApply offered caster (.cast id)
      match onBoard done "Test Sword" with
      | some sw => sw.attachedTo == some host.id
      | none => false

#guard
  let g := addPermanent afterDraw hunter caster caster
  match onBoard g "Test Hunter" with
  | none => false
  | some host =>
    let g := putInHand g bauble caster
    match idNamed g (g.player caster).hand "Test Bauble" with
    | none => false
    | some id =>
      let offered := g.applyTriggeredAbility caster .onCombatMayPutArtifactAttachEquipment (some host.id)
      let declined := mustApply offered caster .decline
      let put := mustApply offered caster (.cast id)
      declined.pending == .none && (declined.player caster).hand.contains id &&
        (onBoard put "Test Bauble").any (·.attachedTo.isNone)

/- The top card of the library enters via unified `moveZone (.topOfLibrary .you (.const 1))`. -/
#guard
  let g0 := addPermanent afterDraw bear caster caster
  let before := (g0.player caster).library.size
  let g := stepBody g0 (.moveZone (.topOfLibrary .you (.const 1)) (.battlefield .controller) .put)
  (g.player caster).library.size == before - 1

/- Printed phrases stay intact. -/
#guard TriggeredAbility.resolutionPhrase Effect.triggerReturnLinkedExile ==
  "return the exiled card to the battlefield under its owner's control"
#guard TriggeredAbility.resolutionPhrase (Effect.triggerPutNonlandMvAtMostFromGy 3) ==
  "put up to one target nonland permanent card with mana value 3 or less from a graveyard onto the battlefield under its owner's control"
#guard TriggeredAbility.toNotation .onDiesReturnAsArtifact ==
  "When Tom, Bert, and William die, if they were a creature, return them to the battlefield. They're an artifact."

end Mtg.Engine.PutTests
