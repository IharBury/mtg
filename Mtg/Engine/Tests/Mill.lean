import Mtg.Engine.Fixture

/-!
# Unified mill instructions (`Instruction.mill` / `PlayerInstr.inspectLibrary`)

The controller, the announced player, the player who lost life, and each
opponent mill cards. Mill-then-put-subtype-into-hand and mill-then-copy-reflexive
execute via unified `Instruction.bind` and `PlayerInstr.inspectLibrary`.
-/

namespace Mtg.Engine.MillTests

open Mtg.Engine
open Mtg.Engine.Tests hiding afterDraw

def afterDraw : Game := Mtg.Engine.Tests.afterDraw.change (.pushContinuationFrame {})

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def elf : CardDef := {
  name := "Mill Elf"
  types := #[.creature]
  subtypes := #["Elf"]
  power := some 1
  toughness := some 1
}

def relic : CardDef := {
  name := "Mill Relic"
  types := #[.artifact]
}

def bolt : CardDef := {
  name := "Mill Bolt"
  types := #[.instant]
}

def plot : CardDef := {
  name := "Mill Plot"
  types := #[.land]
}

def putInGraveyard (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.graveyard p)

def putOnLibrary (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.library p)

/-- Replace `p`'s library. The last card is on top. -/
def onlyLibrary (g : Game) (p : PlayerId) (cards : List CardDef) : Game :=
  cards.foldl (fun g c => putOnLibrary g c p)
    (emptyLibrary g p)

def libSize (g : Game) (p : PlayerId) : Nat :=
  (g.player p).library.size

def inHand (g : Game) (p : PlayerId) (name : String) : Bool :=
  (g.player p).hand.any (fun id => (g.findObject? id).any (·.name == name))

def inGraveyard (g : Game) (p : PlayerId) (name : String) : Bool :=
  (g.player p).graveyard.any (fun id => (g.findObject? id).any (·.name == name))

def permanentId (g : Game) (name : String) : ObjectId :=
  match g.battlefield.find? (·.name == name) with
  | some o => o.id
  | none => panic! s!"missing {name}"

def step (g : Game) (ab : TriggeredAbility)
    (targets : Array Target := #[])
    (lastKnownPower : Option Int := none)
    (causeController : Option PlayerId := none) : Game :=
  let g :=
    match causeController with
    | none => g
    | some pid =>
      let abId : ObjectId := ⟨g.nextObjectId⟩
      let srcSnap : EventObject := {
        owner := caster, controller := some caster, name := "Mill Source", zone := .battlefield }
      let g := g.record (GameEvent.triggerPutOnStack g.turnNumber abId srcSnap caster
        (spec := { triggeredAbility := some ab, fraCauseController := some pid }))
      let g := if g.continuations.isEmpty then g.change (.pushContinuationFrame {}) else g
      g.changes #[.popStack, .resolvingAbility (some abId)]
  g.applyTriggeredAbility caster ab none targets (lastKnownPower := lastKnownPower)

def stepBody (g : Game) (body : Instruction) (targets : Array Target := #[])
    (spec : TargetSpec := .none) : Game :=
  g.applyTriggeredAbility caster
    (TriggeredAbility.mkTrigger .thisEnters { targeting := .of spec, body })
    none targets

def playerMill : TriggeredAbility := .onDrawSecondMillPlayer 1

/- The controller mills the top cards. -/
#guard
  let g0 := putOnLibrary (putOnLibrary afterDraw elf caster) bolt caster
  let g := stepBody g0 (Instruction.mill (.const 2) .you)
  inGraveyard g caster "Mill Bolt" && inGraveyard g caster "Mill Elf" &&
    libSize g caster == libSize g0 caster - 2 &&
    libSize g opp == libSize g0 opp &&
    logContains g "Chandra mills Mill Bolt" &&
    logContains g "Chandra mills Mill Elf"

/- Milling zero cards changes nothing. A short library mills what it has. -/
#guard
  let g0 := putOnLibrary afterDraw elf caster
  let g := stepBody g0 (Instruction.mill (.const 0) .you)
  libSize g caster == libSize g0 caster && g.log.size == g0.log.size

#guard
  let g0 := onlyLibrary afterDraw caster [elf]
  let g := stepBody g0 (Instruction.mill (.const 3) .you)
  inGraveyard g caster "Mill Elf" && libSize g caster == 0 &&
    logContains g "Chandra mills Mill Elf" &&
    logContains g "Chandra mills nothing (empty library)"

#guard
  let g0 := onlyLibrary afterDraw caster []
  let g := stepBody g0 (Instruction.mill (.const 2) .you)
  libSize g caster == 0 &&
    logContains g "Chandra mills nothing (empty library)"

/- The announced player mills, including the controller. Illegal targets are skipped. -/
#guard
  let g0 := putOnLibrary afterDraw bolt opp
  let g := step g0 playerMill #[Target.player opp]
  inGraveyard g opp "Mill Bolt" && libSize g caster == libSize g0 caster &&
    logContains g "Nissa mills Mill Bolt"

#guard
  let g0 := putOnLibrary afterDraw elf caster
  let g := step g0 playerMill #[Target.player caster]
  inGraveyard g caster "Mill Elf" && logContains g "Chandra mills Mill Elf"

#guard
  let g0 := putOnLibrary afterDraw bolt opp
  let g := step g0 playerMill
  !inGraveyard g opp "Mill Bolt" && libSize g opp == libSize g0 opp

#guard
  let g0 := addPermanent (putOnLibrary afterDraw bolt opp) relic caster caster
  let g := step g0 playerMill #[Target.permanent (permanentId g0 "Mill Relic")]
  !inGraveyard g opp "Mill Bolt"

#guard
  let g0 := putOnLibrary afterDraw bolt opp
  let g0 := g0.record (GameEvent.playerLost g0.turnNumber opp .conceded)
  let g := step g0 playerMill #[Target.player opp]
  !inGraveyard g opp "Mill Bolt"

#guard
  let g0 := putOnLibrary afterDraw bolt opp
  let g0 := g0.createEffect (.protectionFromEverything opp)
  let g := step g0 playerMill #[Target.player opp]
  !inGraveyard g opp "Mill Bolt"

/- The player who lost life mills that many. -/
#guard
  let g0 := putOnLibrary (putOnLibrary afterDraw elf opp) bolt opp
  let g := step g0 .onPlayerLosesLifeMillThatMany
    (lastKnownPower := some 2) (causeController := some opp)
  inGraveyard g opp "Mill Bolt" && inGraveyard g opp "Mill Elf" &&
    libSize g opp == libSize g0 opp - 2 &&
    libSize g caster == libSize g0 caster &&
    logContains g "Nissa mills Mill Bolt"

#guard
  let g0 := putOnLibrary afterDraw elf caster
  let g := step g0 .onPlayerLosesLifeMillThatMany
    (lastKnownPower := some 1) (causeController := some caster)
  inGraveyard g caster "Mill Elf" && logContains g "Chandra mills Mill Elf"

#guard
  let g0 := putOnLibrary afterDraw elf opp
  let missingPower := step g0 .onPlayerLosesLifeMillThatMany (causeController := some opp)
  let zero := step g0 .onPlayerLosesLifeMillThatMany (lastKnownPower := some 0) (causeController := some opp)
  let negative := step g0 .onPlayerLosesLifeMillThatMany (lastKnownPower := some (-1)) (causeController := some opp)
  !inGraveyard missingPower opp "Mill Elf" &&
    !inGraveyard zero opp "Mill Elf" &&
    !inGraveyard negative opp "Mill Elf"

/- Mill then put matching subtype cards into hand: already-in-graveyard cards stay there. -/
#guard
  let g0 := putInGraveyard (onlyLibrary afterDraw caster [relic, elf]) elf caster
  let g := step g0 (.onEnterMillThenSubtypeToHand 2 "Elf")
  inHand g caster "Mill Elf" &&
    inGraveyard g caster "Mill Relic" &&
    inGraveyard g caster "Mill Elf"

#guard
  let g0 := onlyLibrary afterDraw caster [relic]
  let g := step g0 (.onEnterMillThenSubtypeToHand 1 "Elf")
  !inHand g caster "Mill Relic" && inGraveyard g caster "Mill Relic"

/- Each opponent mills; reflexive trigger fires only if at least one card was milled. -/
#guard
  let g0 := onlyLibrary afterDraw opp [plot]
  let g := step g0 .onCastSecondSpellMillThenCopy
  inGraveyard g opp "Mill Plot"

#guard
  let g0 := onlyLibrary afterDraw opp []
  let g := step g0 .onCastSecondSpellMillThenCopy
  g.stack.isEmpty

/- Printed notations stay intact. -/
#guard TriggeredAbility.toNotation (.onDrawSecondMillPlayer 3) ==
  "Whenever you draw your second card each turn, target player mills 3 cards."
#guard TriggeredAbility.toNotation .onPlayerLosesLifeMillThatMany ==
  "Whenever a player loses life, that player mills that many cards."
#guard TriggeredAbility.toNotation (.onEnterMillThenSubtypeToHand 4 "Elf") ==
  "When this permanent enters, mill 4 cards, then put all Elf cards from among them into your hand."
#guard TriggeredAbility.toNotation .onCastSecondSpellMillThenCopy ==
  "Whenever you cast your second spell each turn, each opponent mills two cards. When one or more cards are milled this way, exile target enchantment, instant, or sorcery card with equal or lesser mana value than that spell from an opponent's graveyard. Copy the exiled card. You may cast the copy without paying its mana cost."

end Mtg.Engine.MillTests
