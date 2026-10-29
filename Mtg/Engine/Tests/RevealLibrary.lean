import Mtg.Engine.Fixture

/-!
# `TriggerResolution.revealLibrary`

The top cards of your library and a random creature from among them, cards
until a creature, and cards until a Saga are reveals. Cards from the damaged
player's library until an instant or sorcery are exiled for an impulse cast.
Cards from the announced player's library until a nonland may put a +1/+1
counter on the source, or let you cast that nonland until end of turn.
How far the ability looks is `TriggerLibraryHow`. Whose library it uses
is a `PlayerSelector`. What happens to the cards is a `TriggerResolution`.
Any other combination reveals those cards, then resolves the follow-up.
A player the selector does not name reveals nothing.
-/

namespace Mtg.Engine.RevealLibraryTests

open Mtg.Engine
open Mtg.Engine.Tests

def caster : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def bear : CardDef := {
  name := "Reveal Bear"
  types := #[.creature]
  power := some 2
  toughness := some 2
}

def elf : CardDef := {
  name := "Reveal Elf"
  types := #[.creature]
  power := some 1
  toughness := some 1
}

def costly : CardDef := {
  name := "Costly Bear"
  manaCost := ManaCost.ofGeneric 2
  types := #[.creature]
  power := some 2
  toughness := some 2
}

def plot : CardDef := {
  name := "Reveal Plot"
  types := #[.land]
}

def relic : CardDef := {
  name := "Reveal Relic"
  types := #[.artifact]
}

def bolt : CardDef := {
  name := "Reveal Bolt"
  types := #[.instant]
}

def tale : CardDef := {
  name := "Reveal Tale"
  types := #[.enchantment]
  subtypes := #["Saga"]
  saga := some { sacrificeAfter := "I", chapters := #[] }
}

def putOnLibrary (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.library p) none {} (fun id _ =>
    #[.pushLibrary id])

/-- Replace `p`'s library. The last card is on top. -/
def onlyLibrary (g : Game) (p : PlayerId) (cards : List CardDef) : Game :=
  cards.foldl (fun g c => putOnLibrary g c p)
    (g.changePlayer p (.library #[]))

def withLands (g : Game) (n : Nat) : Game :=
  (List.range n).foldl (fun g _ => addPermanent g plot caster caster) g

def stepRaw (g : Game) (r : TriggeredAbility.TriggerResolution) : Game :=
  g.applyTriggeredAbility caster (.onEnterDraw 1) none (resolutionOverride := some r)

def step (g : Game) (r : TriggeredAbility.TriggerResolution) : Game :=
  (stepRaw g r).resolveRandom

def libNames (g : Game) (p : PlayerId) : List String :=
  (g.player p).library.toList.map fun id =>
    (g.findObject? id).map (·.name) |>.getD ""

def inLib (g : Game) (p : PlayerId) (name : String) : Bool :=
  libNames g p |>.contains name

def inHand (g : Game) (p : PlayerId) (name : String) : Bool :=
  (g.player p).hand.any (fun id => (g.findObject? id).any (·.name == name))

def inExile (g : Game) (name : String) : Bool :=
  g.objects.any (fun o => o.name == name && o.zone == .exile)

def onBattlefield (g : Game) (name : String) : Bool :=
  g.battlefield.any (·.name == name)

def libId (g : Game) (p : PlayerId) (name : String) : ObjectId :=
  match (g.player p).library.find? (fun id => (g.findObject? id).any (·.name == name)) with
  | some id => id
  | none => panic! s!"missing {name}"

def ordered (g : Game) (ids : Array ObjectId := #[]) : Game :=
  match g.supplyOrder ids with
  | .ok g => g
  | .error e => panic! e

def randomCreature (n : Nat) : TriggeredAbility.TriggerResolution :=
  .revealLibrary (.top n) (.put .randomCreature)

def untilCreature : TriggeredAbility.TriggerResolution :=
  .revealLibrary .untilCreature
    (.ifElse .revealedManaValueAtMostLands (.put .revealed) (.returnToHand .revealed))

def untilSaga : TriggeredAbility.TriggerResolution :=
  .revealLibrary .untilSaga (.put .revealed)

def exileImpulse : TriggeredAbility.TriggerResolution :=
  .revealLibrary .untilInstantOrSorcery (.exile .top .forLater .impulse) .damagedPlayer

def untilNonland : TriggeredAbility.TriggerResolution :=
  .revealLibrary .untilNonland
    (.may (.putCounters (.ofKind .plusOnePlusOne) .source)
      (.exile .top .forLater .anyManaThisTurn) .ifYouDont)
    .announced

def spy : CardDef := {
  name := "Widow Source"
  types := #[.creature]
  power := some 1
  toughness := some 2
}

def stepAt (g : Game) (r : TriggeredAbility.TriggerResolution)
    (sourceId : Option ObjectId := none) (targets : Array Target := #[]) : Game :=
  (g.applyTriggeredAbility caster (.onEnterDraw 1) sourceId targets
    (resolutionOverride := some r)).resolveRandom

def spyId (g : Game) : ObjectId :=
  match g.battlefield.find? (·.name == "Widow Source") with
  | some o => o.id
  | none => panic! "missing Widow Source"

def noteHit (g : Game) (p : PlayerId) : Game :=
  let g :=
    if onBattlefield g "Widow Source" then g
    else addPermanent g spy caster caster
  g.noteCombatDamageTo p (g.object! (spyId g)).asEvent

/- The only revealed creature enters. Cards under the window stay above the
card that goes on the bottom. The opponent's library stays put. -/
#guard
  let g0 := onlyLibrary (onlyLibrary afterDraw caster [relic, plot, bear]) opp [bolt]
  let g := step g0 (randomCreature 2)
  onBattlefield g "Reveal Bear" && !inLib g caster "Reveal Bear" &&
    libNames g caster == ["Reveal Plot", "Reveal Relic"] &&
    libNames g opp == ["Reveal Bolt"] &&
    logContains g "Chandra reveals Reveal Bear" &&
    logContains g "Chandra reveals Reveal Plot" &&
    !logContains g "Reveal Relic" &&
    logContains g "Reveal Bear enters the battlefield" &&
    logContains g "puts the rest on the bottom"

/- No creature puts the revealed card on the bottom and leaves the rest of
the library above it. Looking at zero cards finds nothing. A short library
reveals only the cards it has. -/
#guard
  let g0 := onlyLibrary afterDraw caster [relic, plot]
  let g := step g0 (randomCreature 1)
  !onBattlefield g "Reveal Plot" &&
    libNames g caster == ["Reveal Plot", "Reveal Relic"] &&
    logContains g "No creature card was revealed" &&
    logContains g "Chandra reveals Reveal Plot" &&
    !logContains g "Reveal Relic"

#guard
  let g0 := onlyLibrary afterDraw caster [bear]
  let before := (g0.player caster).library
  let g := step g0 (randomCreature 0)
  (g.player caster).library == before && !onBattlefield g "Reveal Bear" &&
    g.log.back? == some "No creature card was revealed"

#guard
  let g0 := onlyLibrary afterDraw caster [plot, bear]
  let g := step g0 (randomCreature 5)
  onBattlefield g "Reveal Bear" && libNames g caster == ["Reveal Plot"] &&
    logContains g "Chandra reveals Reveal Bear" &&
    logContains g "Chandra reveals Reveal Plot"

/- With one creature, that creature enters. With two, the
choice waits, and the chosen creature then enters. -/
#guard
  let g0 := onlyLibrary afterDraw caster [plot, bear]
  let g := stepRaw g0 (randomCreature 2)
  onBattlefield g "Reveal Bear" && g.pending == .none &&
    libNames g caster == ["Reveal Plot"]

#guard
  let g0 := onlyLibrary afterDraw caster [plot, bear, elf]
  let g := stepRaw g0 (randomCreature 3)
  let bearId := libId g caster "Reveal Bear"
  let elfId := libId g caster "Reveal Elf"
  let waiting :=
    match g.pending with
    | .resolveRandom (.chooseObject ids) =>
      ids == #[bearId, elfId] && !onBattlefield g "Reveal Bear" &&
        !onBattlefield g "Reveal Elf"
    | _ => false
  let g := ordered g #[elfId]
  waiting && onBattlefield g "Reveal Elf" && !onBattlefield g "Reveal Bear" &&
    logContains g "puts a random creature from among them" &&
    (match g.pending with
      | .resolveRandom (.orderInto ids (.library p) _) =>
        p == caster && ids.size == 2
      | _ => false)

/- Without `norandom`, one of the revealed creatures enters and the other
revealed cards stay in the library. -/
#guard
  let g0 := onlyLibrary afterDraw caster [plot, bear, elf]
  let g := step g0 (randomCreature 3)
  let bears := onBattlefield g "Reveal Bear"
  let elves := onBattlefield g "Reveal Elf"
  bears != elves && inLib g caster "Reveal Plot" &&
    (if bears then inLib g caster "Reveal Elf" else inLib g caster "Reveal Bear") &&
    !inExile g "Reveal Bear" && !inExile g "Reveal Elf" && !inHand g caster "Reveal Bear"

/- A creature at most the lands you control enters. A more expensive
creature goes to hand. Revealing stops at the first creature. An empty
library changes nothing. -/
#guard
  let g0 := onlyLibrary afterDraw caster [elf, plot, bear]
  let g := step g0 untilCreature
  onBattlefield g "Reveal Bear" && !inHand g caster "Reveal Bear" &&
    libNames g caster == ["Reveal Elf", "Reveal Plot"] &&
    !logContains g "Reveal Elf" &&
    logContains g "Reveal Bear enters the battlefield"

#guard
  let g0 := onlyLibrary afterDraw caster [plot, costly]
  let g := step g0 untilCreature
  inHand g caster "Costly Bear" && !onBattlefield g "Costly Bear" &&
    libNames g caster == ["Reveal Plot"] &&
    logContains g "Costly Bear is put into Chandra's hand"

#guard
  let g0 := withLands (onlyLibrary afterDraw caster [plot, costly]) 2
  let g := step g0 untilCreature
  onBattlefield g "Costly Bear" && !inHand g caster "Costly Bear" &&
    logContains g "Costly Bear enters the battlefield"

#guard
  let g0 := withLands (onlyLibrary afterDraw caster [costly]) 1
  let g := step g0 untilCreature
  inHand g caster "Costly Bear" && !onBattlefield g "Costly Bear"

#guard
  let g0 := onlyLibrary afterDraw caster [bear]
  let g := step g0 untilCreature
  onBattlefield g "Reveal Bear" && (g.player caster).library.isEmpty

#guard
  let g0 := onlyLibrary afterDraw caster [tale, plot, bear]
  let g := step g0 untilCreature
  onBattlefield g "Reveal Bear" && inLib g caster "Reveal Tale" &&
    !onBattlefield g "Reveal Tale" && !logContains g "Reveal Tale"

#guard
  let g0 := onlyLibrary afterDraw caster []
  let g := step g0 untilCreature
  (g.player caster).library.isEmpty && g.log.size == g0.log.size

#guard
  let g0 := onlyLibrary afterDraw caster [bolt, plot]
  let g := stepRaw g0 untilCreature
  (g.player caster).library.isEmpty && inExile g "Reveal Bolt" && inExile g "Reveal Plot" &&
    (match g.pending with
      | .resolveRandom (.orderInto ids (.library p) _) => p == caster && ids.size == 2
      | _ => false)

/- A Saga enters. Other cards go on the bottom. No Saga puts every revealed
card on the bottom. An empty library changes nothing. -/
#guard
  let g0 := onlyLibrary afterDraw caster [relic, plot, tale]
  let g := step g0 untilSaga
  onBattlefield g "Reveal Tale" &&
    libNames g caster == ["Reveal Relic", "Reveal Plot"] &&
    !logContains g "Reveal Relic" &&
    logContains g "Reveal Tale enters the battlefield"

#guard
  let g0 := onlyLibrary afterDraw caster [tale]
  let g := step g0 untilSaga
  onBattlefield g "Reveal Tale" && (g.player caster).library.isEmpty &&
    !logContains g "puts the rest on the bottom"

#guard
  let g0 := onlyLibrary afterDraw caster [bolt, plot]
  let g := step g0 untilSaga
  !onBattlefield g "Reveal Bolt" && !onBattlefield g "Reveal Plot" &&
    inLib g caster "Reveal Bolt" && inLib g caster "Reveal Plot" &&
    !inExile g "Reveal Bolt" && logContains g "puts the rest on the bottom"

#guard
  let g0 := onlyLibrary afterDraw caster []
  let g := step g0 untilSaga
  (g.player caster).library.isEmpty && g.log.size == g0.log.size

/- The damaged player's library is exiled until an instant or sorcery, and
the spell is remembered for the impulse cast. A missing seat is the
opponent. The controller's library is used when that player was damaged.
An empty library is remembered with nothing exiled. -/
#guard
  let g0 := onlyLibrary (onlyLibrary afterDraw opp [relic, bolt]) caster [bear]
  let g0 := noteHit g0 opp
  let g := step g0 exileImpulse
  g.grimaImpulseReady && g.grimaImpulseVictim == some opp &&
    (g.grimaImpulseFound.bind g.findObject?).any (·.name == "Reveal Bolt") &&
    g.grimaImpulseOthers.size == 0 &&
    inExile g "Reveal Bolt" && inLib g opp "Reveal Relic" &&
    libNames g caster == ["Reveal Bear"] &&
    logContains g "Nissa exiles Reveal Bolt face up" &&
    !logContains g "Reveal Relic"

#guard
  let g0 := onlyLibrary afterDraw opp [bolt, plot]
  let g0 := noteHit g0 opp
  let g := step g0 exileImpulse
  g.grimaImpulseReady &&
    (g.grimaImpulseFound.bind g.findObject?).any (·.name == "Reveal Bolt") &&
    g.grimaImpulseOthers.any (fun id => (g.findObject? id).any (·.name == "Reveal Plot")) &&
    (g.player opp).library.isEmpty && inExile g "Reveal Plot" && inExile g "Reveal Bolt" &&
    logContains g "Nissa exiles Reveal Plot face up" &&
    logContains g "Nissa exiles Reveal Bolt face up"

#guard
  let g0 := onlyLibrary afterDraw opp [plot, relic]
  let g0 := noteHit g0 opp
  let g := step g0 exileImpulse
  g.grimaImpulseReady && g.grimaImpulseFound.isNone &&
    g.grimaImpulseOthers.size == 2 && (g.player opp).library.isEmpty &&
    inExile g "Reveal Plot" && inExile g "Reveal Relic"

#guard
  let g0 := onlyLibrary afterDraw opp []
  let g0 := noteHit g0 opp
  let before := g0.log.size
  let g := step g0 exileImpulse
  g.grimaImpulseReady && g.grimaImpulseVictim == some opp &&
    g.grimaImpulseFound.isNone && g.grimaImpulseOthers.isEmpty &&
    (g.player opp).library.isEmpty && g.log.size == before

#guard
  let g0 := onlyLibrary (onlyLibrary afterDraw caster [bolt]) opp [plot]
  let g := step g0 exileImpulse
  g.grimaImpulseVictim == some opp &&
    (g.grimaImpulseFound.bind g.findObject?).isNone &&
    inExile g "Reveal Plot" && libNames g caster == ["Reveal Bolt"]

#guard
  let g0 := onlyLibrary (onlyLibrary afterDraw caster [bolt]) opp [plot]
  let g0 := noteHit g0 caster
  let g := step g0 exileImpulse
  g.grimaImpulseVictim == some caster &&
    (g.grimaImpulseFound.bind g.findObject?).any (·.name == "Reveal Bolt") &&
    libNames g opp == ["Reveal Plot"] &&
    logContains g "Chandra exiles Reveal Bolt face up"

/- The following impulse cast reads the stored spell. -/
#guard
  let g0 := onlyLibrary afterDraw opp [plot, bolt]
  let g0 := noteHit g0 opp
  let g := step g0 (.sequence [exileImpulse, .mayCast .impulse .unlimited .withoutPaying])
  match g.pending with
  | .fraChoice p (.mayCastGrima _ _ v) =>
    p == caster && v == opp && !g.grimaImpulseReady
  | _ => false

/- The announced player exiles until a nonland. The source still in play
asks for the counter. A missing source grants the cast. No player is
reported, and an empty library exiles nothing. -/
#guard
  let g0 := onlyLibrary (addPermanent afterDraw spy caster caster) opp [plot, bolt]
  let src := spyId g0
  let g := stepAt g0 untilNonland (some src) #[Target.player opp]
  match g.pending with
  | .fraChoice _ (.widowMayCounter sid exiled) =>
    sid == some src &&
      (exiled.bind g.findObject?).any (·.name == "Reveal Bolt") &&
      inExile g "Reveal Bolt" && libNames g opp == ["Reveal Plot"] &&
      logContains g "exiles Reveal Bolt" &&
      logContains g "You may put a +1/+1 counter"
  | _ => false

#guard
  let g0 := onlyLibrary afterDraw opp [plot, bolt]
  let g := stepAt g0 untilNonland none #[Target.player opp]
  g.pending == .none && inExile g "Reveal Bolt" && libNames g opp == ["Reveal Plot"] &&
    (g.objects.any (fun o =>
      o.name == "Reveal Bolt" && o.zone == .exile && (g.playPermission o).isSome)) &&
    logContains g "may cast Reveal Bolt until end of turn"

#guard
  let g0 := onlyLibrary afterDraw opp [bolt]
  let g := step g0 untilNonland
  libNames g opp == ["Reveal Bolt"] && g.pending == .none &&
    logContains g "didn't deal combat damage"

#guard
  let g0 := onlyLibrary (addPermanent afterDraw spy caster caster) opp []
  let g := stepAt g0 untilNonland (some (spyId g0)) #[Target.player opp]
  match g.pending with
  | .fraChoice _ (.widowMayCounter _ exiled) =>
    exiled.isNone && libNames g opp == []
  | _ => false

/- A combination that is not printed reveals as `how` and `who` say,
then resolves the follow-up. No announced player reveals nothing. -/
#guard
  let g0 := onlyLibrary (onlyLibrary afterDraw caster [plot, bear, tale]) opp [bolt, plot]
  let g0 := noteHit (g0.change (.grimaImpulseReady false)) opp
  let g := step g0 (.revealLibrary (.top 3) (.put .revealed))
  onBattlefield g "Reveal Plot" && onBattlefield g "Reveal Bear" &&
    onBattlefield g "Reveal Tale" && libNames g caster == []

#guard
  let g0 := onlyLibrary (onlyLibrary afterDraw caster [plot, bear, tale]) opp [bolt, plot]
  let g := step g0 (.revealLibrary (.top 3) (.returnToHand .revealed))
  inHand g caster "Reveal Plot" && inHand g caster "Reveal Bear" &&
    inHand g caster "Reveal Tale" && libNames g caster == []

#guard
  let g0 := onlyLibrary (onlyLibrary afterDraw caster [plot, bear, tale]) opp [bolt, plot]
  let g0 := g0.change (.grimaImpulseReady false)
  let g := step g0 (.revealLibrary (.top 3) (.exile .top .forLater .impulse))
  g.grimaImpulseReady && inExile g "Reveal Plot" && inExile g "Reveal Bear" &&
    inExile g "Reveal Tale" && libNames g caster == []

#guard
  let g0 := onlyLibrary (onlyLibrary afterDraw caster [plot, bear, tale]) opp [bolt, plot]
  let g0 := noteHit g0 opp
  let g := step g0 (.revealLibrary (.top 3) (.put .randomCreature) .damagedPlayer)
  !onBattlefield g "Reveal Bolt" && !onBattlefield g "Reveal Plot" &&
    inLib g opp "Reveal Bolt" && inLib g opp "Reveal Plot" &&
    logContains g "No creature card was revealed"

#guard
  let g0 := onlyLibrary (onlyLibrary afterDraw caster [plot, bear, tale]) opp [bolt, plot]
  let g := step g0 (.revealLibrary .untilCreature (.put .randomCreature))
  onBattlefield g "Reveal Bear" && inLib g caster "Reveal Plot" &&
    inLib g caster "Reveal Tale" && !inLib g caster "Reveal Bear"

#guard
  let g0 := onlyLibrary (onlyLibrary afterDraw caster [plot, bear, tale]) opp [bolt, plot]
  let g := step g0 (.revealLibrary .untilCreature (.put .revealed))
  onBattlefield g "Reveal Bear" && inLib g caster "Reveal Plot" &&
    inLib g caster "Reveal Tale"

#guard
  let g0 := onlyLibrary (onlyLibrary afterDraw caster [plot, bear, tale]) opp [bolt, plot]
  let g := step g0 (.revealLibrary .untilSaga (.returnToHand .revealed))
  inHand g caster "Reveal Tale" && inLib g caster "Reveal Plot" &&
    inLib g caster "Reveal Bear" && !inLib g caster "Reveal Tale"

#guard
  let g0 := onlyLibrary (onlyLibrary afterDraw caster [plot, bear, tale]) opp [bolt, plot]
  let g0 := noteHit g0 opp
  let g := step g0 (.revealLibrary .untilSaga (.put .revealed) .damagedPlayer)
  !onBattlefield g "Reveal Bolt" && !onBattlefield g "Reveal Plot" &&
    inLib g opp "Reveal Bolt" && inLib g opp "Reveal Plot" &&
    logContains g "reveals Reveal Plot"

#guard
  let g0 := onlyLibrary (onlyLibrary afterDraw caster [plot, bear, tale]) opp [bolt, plot]
  let g := step g0 (.revealLibrary .untilInstantOrSorcery (.exile .top .forLater .impulse))
  !g.grimaImpulseReady && inLib g caster "Reveal Plot" &&
    inLib g caster "Reveal Bear" && inLib g caster "Reveal Tale" &&
    logContains g "reveals Reveal Tale"

#guard
  let g0 := onlyLibrary (onlyLibrary afterDraw caster [plot, bear, tale]) opp [bolt, plot]
  let g0 := noteHit g0 opp
  let g := step g0
    (.revealLibrary .untilInstantOrSorcery (.put .revealed) .damagedPlayer)
  onBattlefield g "Reveal Bolt" && inLib g opp "Reveal Plot" &&
    !inLib g opp "Reveal Bolt"

#guard
  let g0 := onlyLibrary (onlyLibrary afterDraw caster [plot, bear, tale]) opp [bolt, plot]
  let quiet := [
    .revealLibrary .untilNonland (.put .revealed) .announced,
    .revealLibrary .untilNonland (.exile .top .forLater .anyManaThisTurn) .announced]
  quiet.all fun r =>
    let g := step g0 r
    libNames g caster == libNames g0 caster && libNames g opp == libNames g0 opp &&
      g.log.size == g0.log.size

#guard
  let g0 := onlyLibrary (onlyLibrary afterDraw caster [plot, bear, tale]) opp [bolt, plot]
  let offered := step g0 (.revealLibrary .untilNonland
    (.may (.putCounters (.ofKind .plusOnePlusOne) .source)
      (.exile .top .forLater .anyManaThisTurn) .ifYouDont) .you)
  let g := mustApply offered caster .decline
  (match offered.pending with
    | .mayResolve p => p == caster
    | _ => false) &&
    inExile g "Reveal Tale" &&
    (g.objects.any fun o =>
      o.name == "Reveal Tale" && ((g.playPermission o).bind (fun p => some p.anyMana)) == some true) &&
    inLib g caster "Reveal Bear" && inLib g caster "Reveal Plot"

#guard
  let g0 := onlyLibrary (onlyLibrary afterDraw caster [plot, bear, tale]) opp [bolt, plot]
  let g := step g0 (.revealLibrary (.top 1)
    (.may (.putCounters (.ofKind .plusOnePlusOne) .source)
      (.exile .top .forLater .anyManaThisTurn) .ifYouDont) .announced)
  libNames g caster == libNames g0 caster && libNames g opp == libNames g0 opp &&
    g.log.size > g0.log.size

#guard
  let g0 := onlyLibrary (onlyLibrary afterDraw caster [plot, bear, tale]) opp [bolt, plot]
  let g := step g0 (.revealLibrary (.top 3) (.put .randomCreature) .eachOpponent)
  !onBattlefield g "Reveal Bolt" && inLib g opp "Reveal Bolt" &&
    inLib g opp "Reveal Plot" && logContains g "No creature card was revealed"

/- The follow-up resolutions do nothing on their own. `revealLibrary` is
what gives them the revealed cards. -/
#guard
  let g0 := onlyLibrary afterDraw caster [plot, bear, tale]
  let alone := [
    .put .randomCreature,
    .put .revealed,
    .returnToHand .revealed,
    .exile .top .forLater .impulse,
    .exile .top .forLater .anyManaThisTurn,
    .ifElse .revealedManaValueAtMostLands (.put .revealed) (.returnToHand .revealed)]
  alone.all fun r =>
    let g := step g0 r
    libNames g caster == libNames g0 caster && !onBattlefield g "Reveal Bear" &&
      !onBattlefield g "Reveal Tale" && !g.grimaImpulseReady &&
      g.log.size == g0.log.size

/- Printed phrases and resolutions stay with the combination that produces them. -/
#guard TriggeredAbility.resolution (.onDiesRevealTopPutRandomCreature 4) ==
  .revealLibrary (.top 4) (.put .randomCreature)
#guard TriggeredAbility.resolution .onNontokenYouControlDiesRevealCreature ==
  untilCreature
#guard TriggeredAbility.resolution .onFinalSagaChapterRevealSaga ==
  untilSaga
#guard TriggeredAbility.resolution .onCombatDamageImpulseInstantSorcery ==
  .sequence [exileImpulse, .mayCast .impulse .unlimited .withoutPaying]
#guard TriggeredAbility.resolutionPhrase
    { resolution := .revealLibrary (.top 4) (.put .randomCreature) } ==
  s!"reveal the top 4 cards of your library. Put a random creature card from among them onto the battlefield. {restOnBottomRandomPhrase}"
#guard TriggeredAbility.resolutionPhrase { resolution := untilCreature } ==
  s!"reveal cards from the top of your library until you reveal a creature card. If its mana value is less than or equal to the number of lands you control, put it onto the battlefield. Otherwise, put it into your hand. {restOnBottomRandomPhrase}"
#guard TriggeredAbility.resolutionPhrase { resolution := untilSaga } ==
  "reveal cards from the top of your library until you reveal a Saga card. Put that card onto the battlefield and the rest on the bottom of your library in a random order"
#guard TriggeredAbility.resolutionPhrase { resolution := exileImpulse } ==
  "that player exiles cards from the top of their library until they exile an instant or sorcery card"
#guard TriggeredAbility.resolutionPhrase { resolution := untilNonland } ==
  "that player exiles cards until a nonland card"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .revealLibrary (.top 2) (.put .revealed) } ==
  "reveal cards from a library"
#guard TriggeredAbility.resolutionPhrase
    { resolution := .revealLibrary (.top 3) (.put .randomCreature) .eachOpponent } ==
  "reveal cards from a library"
#guard TriggeredAbility.toNotation (.onDiesRevealTopPutRandomCreature 4) ==
  s!"When this artifact is put into a graveyard from the battlefield, reveal the top 4 cards of your library. Put a random creature card from among them onto the battlefield. {restOnBottomRandomPhrase}."
#guard TriggeredAbility.toNotation .onNontokenYouControlDiesRevealCreature ==
  s!"Whenever a nontoken creature you control dies, reveal cards from the top of your library until you reveal a creature card. If its mana value is less than or equal to the number of lands you control, put it onto the battlefield. Otherwise, put it into your hand. {restOnBottomRandomPhrase}. This ability triggers only once each turn."
#guard TriggeredAbility.toNotation .onFinalSagaChapterRevealSaga ==
  "Whenever the final chapter ability of a Saga you control resolves, reveal cards from the top of your library until you reveal a Saga card. Put that card onto the battlefield and the rest on the bottom of your library in a random order. This ability triggers only once each turn."
#guard TriggeredAbility.toNotation .onCombatDamageImpulseInstantSorcery ==
  "Whenever Gríma deals combat damage to a player, that player exiles cards from the top of their library until they exile an instant or sorcery card. You may cast that card without paying its mana cost. Then that player puts the exiled cards that weren't cast this way on the bottom of their library in a random order."

end Mtg.Engine.RevealLibraryTests
