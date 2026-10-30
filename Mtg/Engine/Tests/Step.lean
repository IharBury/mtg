import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Fixture
import Mtg.Engine.Game
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns

/-!
# Step triggers without `StepLeftover`

The enchanted creature's controller draws. Drawing fills a hand to ten.
The source becomes a copy until the controller's next turn. A +1/+1 counter
or removing a counter draws. A harnessed source exiles a nonland and
returns it.
-/

namespace Mtg.Engine.StepTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests hiding afterDraw

def afterDraw : Game := Mtg.Engine.Tests.afterDraw.change (.pushContinuationFrame {})

def me : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def handSize (g : Game) (p : PlayerId) : Nat :=
  (g.player p).hand.size

def resolve (g : Game) (ab : TriggeredAbility) (sourceId : Option ObjectId := none)
    (targets : Array Target := #[]) : Game :=
  g.applyTriggeredAbility me ab sourceId targets

def named (g : Game) (name : String) : GameObject :=
  namedPermanent g name

def onBoard (g : Game) (name : String) : Bool :=
  g.battlefield.any (·.name == name)

/- The shared step effects resolve as constructors that do not carry
`StepLeftover`. The printed sentence stays the Oracle line. -/
#guard TriggeredAbility.resolution (TriggeredAbility.onStep Effect.stepEnchantedControllerDraws) ==
  .draw (.fixed 1) (who := .controller .enchanted)
#guard TriggeredAbility.resolution (TriggeredAbility.onStep Effect.stepDrawToTen) ==
  .draw (.upToHandSize 10)
#guard TriggeredAbility.resolution (TriggeredAbility.onStep Effect.stepCopyAbsorbingMan) ==
  .becomeCopy .artifactEnchantmentOrLand
#guard TriggeredAbility.resolution (TriggeredAbility.onStep Effect.stepCopyTaskmaster) ==
  .becomeCopy .creatureOrGraveyardCard
#guard TriggeredAbility.resolution (TriggeredAbility.onStep Effect.stepHydeChoose) ==
  .chooseModes TriggeredAbility.TriggerResolution.hydeModes .plusOneOrRemoveCounter
#guard TriggeredAbility.resolution
    (TriggeredAbility.onEnter (Effect.ofTrigger .exileOtherCopyEnchanted)) ==
  .sequence [.exile .target .untilSourceLeaves .copyAndHost, .becomeCopy .noted]
#guard TriggeredAbility.resolution (TriggeredAbility.onStep Effect.stepHarnessedFlicker) ==
  .«if» (.atLeast (.count .harnessedSource) (.fixed 1)) (.exile .target .returnImmediately)

#guard toString (TriggeredAbility.onStep Effect.stepEnchantedControllerDraws) ==
  TriggeredAbility.stepSentence .enchantedControllerDraws
#guard toString (TriggeredAbility.onStep Effect.stepDrawToTen) ==
  TriggeredAbility.stepSentence .drawToTen
#guard toString (TriggeredAbility.onStep Effect.stepCopyAbsorbingMan) ==
  TriggeredAbility.stepSentence .copyAbsorbingMan
#guard toString (TriggeredAbility.onStep Effect.stepCopyTaskmaster) ==
  TriggeredAbility.stepSentence .copyTaskmaster
#guard toString (TriggeredAbility.onStep Effect.stepHydeChoose) ==
  TriggeredAbility.stepSentence .hydeChoose
#guard toString (TriggeredAbility.onStep Effect.stepHarnessedFlicker) ==
  TriggeredAbility.stepSentence .harnessedFlicker

/- The enchanted creature's controller draws. The Aura's controller does not.
Nothing enchanted draws nothing. -/
def enchantedDraws : Game :=
  let g := addPermanent afterDraw grizzlyBears opp opp
  let g := addPermanent g superIntelligence me me
  let host := named g "Grizzly Bears"
  let aura := named g "Super Intelligence"
  let g := g.attachSourceTo aura host
  resolve g (TriggeredAbility.onStep Effect.stepEnchantedControllerDraws) (some aura.id)

#guard handSize enchantedDraws opp == handSize afterDraw opp + 1
#guard handSize enchantedDraws me == handSize afterDraw me

def enchantedMissing : Game :=
  let g := addPermanent afterDraw superIntelligence me me
  resolve g (TriggeredAbility.onStep Effect.stepEnchantedControllerDraws)
    (some (named g "Super Intelligence").id)

#guard handSize enchantedMissing me == handSize afterDraw me &&
  handSize enchantedMissing opp == handSize afterDraw opp &&
  logContains enchantedMissing "No card is drawn"

/- Drawing fills the hand to ten, and a second resolution draws nothing. -/
def filledToTen : Game :=
  let g := addPermanent afterDraw theTenRings me me
  resolve g (TriggeredAbility.onStep Effect.stepDrawToTen) (some (named g "The Ten Rings").id)

#guard handSize filledToTen me == 10

def alreadyTen : Game :=
  resolve filledToTen (TriggeredAbility.onStep Effect.stepDrawToTen)
    (some (named filledToTen "The Ten Rings").id)

#guard handSize alreadyTen me == 10 &&
  logContains alreadyTen "already have ten or more cards in hand"

/- Absorbing Man copies a land and keeps his name, power, and vigilance.
A creature is not copied. Choosing none copies nothing. -/
def copiedLand : Game :=
  let g := addPermanent (addPermanent afterDraw absorbingMan me me) forest me me
  resolve g (TriggeredAbility.onStep Effect.stepCopyAbsorbingMan)
    (some (named g "Absorbing Man").id)
    #[Target.permanent (named g "Forest").id]

#guard
  let copied := named copiedLand "Absorbing Man"
  copiedLand.isLand copied && !copied.printed.isLand &&
    copiedLand.name copied == "Absorbing Man" &&
    copiedLand.power copied == 4 && copiedLand.hasVigilance copied

def rejectedCreature : Game :=
  let g := addPermanent (addPermanent afterDraw absorbingMan me me) grizzlyBears me me
  resolve g (TriggeredAbility.onStep Effect.stepCopyAbsorbingMan)
    (some (named g "Absorbing Man").id)
    #[Target.permanent (named g "Grizzly Bears").id]

#guard !rejectedCreature.isLand (named rejectedCreature "Absorbing Man") &&
  logContains rejectedCreature "isn't an artifact, non-Aura enchantment, or land"

def copyNothing : Game :=
  let g := addPermanent afterDraw absorbingMan me me
  resolve g (TriggeredAbility.onStep Effect.stepCopyAbsorbingMan)
    (some (named g "Absorbing Man").id)

#guard !copyNothing.isLand (named copyNothing "Absorbing Man") &&
  logContains copyNothing "doesn't become a copy"

/- The enchanted creature becomes a copy of the creature an earlier step
noted. Nothing noted leaves the creature unchanged. -/
def notedCopy : Game :=
  let g := addPermanent (addPermanent afterDraw grizzlyBears me me) hillGiant opp opp
  let host := named g "Grizzly Bears"
  let giant := named g "Hill Giant"
  let g := g.changes #[.notedCopyObject (some giant), .notedHostId (some host.id)]
  g.applyTriggeredAbility me (TriggeredAbility.onEnterDraw 1) none
    (resolutionOverride := some (.becomeCopy .noted))

#guard
  match notedCopy.battlefield.find? (fun o => (notedCopy.copyRestore o).isSome) with
  | some o =>
    notedCopy.name o == "Hill Giant" &&
      o.printed.name == "Grizzly Bears" &&
      ((notedCopy.copyRestore o).getD o.printed).name == "Grizzly Bears" &&
      notedCopy.notedCopyObject.isNone
  | none => false

def notedMissing : Game :=
  let g := addPermanent afterDraw grizzlyBears me me
  g.applyTriggeredAbility me (TriggeredAbility.onEnterDraw 1) none
    (resolutionOverride := some (.becomeCopy .noted))

#guard (named notedMissing "Grizzly Bears").name == "Grizzly Bears" &&
  (notedMissing.copyRestore (named notedMissing "Grizzly Bears")).isNone

/- Any other selector copies nothing. -/
#guard
  let g0 := addPermanent afterDraw grizzlyBears me me
  let g := g0.applyTriggeredAbility me (TriggeredAbility.onEnterDraw 1) none
    (resolutionOverride := some (.becomeCopy .source))
  (g.copyRestore (named g "Grizzly Bears")).isNone && g.log.size == g0.log.size
#guard TriggeredAbility.resolutionPhrase { resolution := .becomeCopy .source } ==
  "become a copy"
#guard TriggeredAbility.resolutionPhrase { resolution := .becomeCopy (.cause (some .villain)) } ==
  "become a copy"

/- Taskmaster copies a creature card in a graveyard and replaces his type line. -/
def copiedGraveyard : Game :=
  let g := addPermanent afterDraw taskmasterMercenaryMimic me me
  let g := addToGraveyard g hillGiant opp
  let giant :=
    match (g.player opp).graveyard.find? (fun id => (g.object! id).name == "Hill Giant") with
    | some id => id
    | none => ⟨0⟩
  resolve g (TriggeredAbility.onStep Effect.stepCopyTaskmaster)
    (some (named g "Taskmaster, Mercenary Mimic").id) #[Target.card giant]

#guard
  let tm := named copiedGraveyard "Taskmaster, Mercenary Mimic"
  tm.name == "Taskmaster, Mercenary Mimic" &&
    tm.printed.power == hillGiant.power &&
    tm.subtypes == #[.human, .mercenary, .villain]

/- Mister Hyde's upkeep asks for a mode. The first mode puts a +1/+1 counter. -/
def hydeAsks : Game :=
  let g := addPermanent afterDraw misterHydeMonsterWithin me me
  resolve g (TriggeredAbility.onStep Effect.stepHydeChoose)
    (some (named g "Mister Hyde, Monster Within").id)

#guard
  match hydeAsks.pending with
  | .fraChoice _ (.hydeMode _) => true
  | _ => false

def hydePlusOne : Game :=
  mustApply hydeAsks me (.chooseMode 0)

#guard (named hydePlusOne "Mister Hyde, Monster Within").status.plusOnePlusOne == 1

/- A harnessed Mind Stone blinks another nonland. An unharnessed source
does not. A land is not a legal object to blink. -/
def harness (g : Game) : Game :=
  let stone := named g "The Mind Stone"
  g.record (GameEvent.designation g.turnNumber stone.asEvent .harnessed true
    (cause := .gameRule .staticAbility))

def blinked : Game :=
  let g := harness (addPermanent afterDraw theMindStone me me)
  let g := addPermanent (addPermanent g forest me me) grizzlyBears me me
  resolve g (TriggeredAbility.onStep Effect.stepHarnessedFlicker)
    (some (named g "The Mind Stone").id)
    #[Target.permanent (named g "Grizzly Bears").id]

#guard onBoard blinked "Grizzly Bears" && onBoard blinked "Forest" &&
  (named blinked "The Mind Stone").linkedExile.isEmpty &&
  logContains blinked "is exiled, then returned"

def notHarnessed : Game :=
  let g := addPermanent (addPermanent afterDraw theMindStone me me) grizzlyBears me me
  resolve g (TriggeredAbility.onStep Effect.stepHarnessedFlicker)
    (some (named g "The Mind Stone").id)
    #[Target.permanent (named g "Grizzly Bears").id]

#guard onBoard notHarnessed "Grizzly Bears" &&
  logContains notHarnessed "is not harnessed" &&
  !logContains notHarnessed "is exiled, then returned"

def blinkLand : Game :=
  let g := harness (addPermanent (addPermanent afterDraw theMindStone me me) forest me me)
  resolve g (TriggeredAbility.onStep Effect.stepHarnessedFlicker)
    (some (named g "The Mind Stone").id)
    #[Target.permanent (named g "Forest").id]

#guard onBoard blinkLand "Forest" &&
  logContains blinkLand "no longer legal" &&
  !logContains blinkLand "is exiled, then returned"

end Mtg.Engine.StepTests
