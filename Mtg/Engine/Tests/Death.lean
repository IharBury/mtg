import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Fixture
import Mtg.Engine.Game
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns

/-!
# Dies triggers without `DeathLeftover`

Hellcat returns under her owner's control. A Villain returns as a Hero.
An attacking creature returns to its owner's hand. Each opponent sacrifices
a nontoken creature.
-/

namespace Mtg.Engine.DeathTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def me : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def resolve (g : Game) (ab : TriggeredAbility) (sourceId : Option ObjectId := none)
    (targets : Array Target := #[]) : Game :=
  g.applyTriggeredAbility me ab sourceId targets

def named (g : Game) (name : String) : GameObject :=
  namedPermanent g name

def onBoard (g : Game) (name : String) : Bool :=
  g.battlefield.any (·.name == name)

def inZone (g : Game) (z : Zone) (name : String) : Bool :=
  g.objects.any (fun o => o.zone == z && o.name == name)

/- The shared dies effects resolve as constructors that do not carry
`DeathLeftover`. The printed sentence stays the Oracle line. -/
#guard TriggeredAbility.resolution (TriggeredAbility.onDeath Effect.deathHellcatReturn) ==
  .put .source .underOwner (.entering [
    .loseAllAbilities, .keywords Keyword.haste,
    .counter .plusOnePlusOne (asEnters := true)])
#guard TriggeredAbility.resolution (TriggeredAbility.onDeath Effect.deathVillainReturnAsHero) ==
  .put (.cause (some "Villain")) .underOwner (.entering [
    .additionalSubtype "Hero", .counter .finality])
#guard TriggeredAbility.resolution (TriggeredAbility.onDeath Effect.deathAttackingReturnHand) ==
  .returnToHand .cause
#guard TriggeredAbility.resolution (TriggeredAbility.onDeath Effect.deathDeathtouchOppSac) ==
  .sacrifice .chosenNontokenCreature

#guard toString (TriggeredAbility.onDeath Effect.deathHellcatReturn) ==
  TriggeredAbility.deathSentence .hellcatReturn
#guard toString (TriggeredAbility.onDeath Effect.deathVillainReturnAsHero) ==
  TriggeredAbility.deathSentence .villainReturnAsHero
#guard toString (TriggeredAbility.onDeath Effect.deathAttackingReturnHand) ==
  TriggeredAbility.deathSentence .attackingReturnHand
#guard toString (TriggeredAbility.onDeath Effect.deathDeathtouchOppSac) ==
  TriggeredAbility.deathSentence .deathtouchOppSac

/- Hellcat returns with a +1/+1 counter, haste, and no abilities.
A Hellcat still on the battlefield is reported and stays there. -/
def hellcatReturns : Game :=
  let g := addPermanent afterDraw hellcatUndyingVigilante me me
  let old := (named g "Hellcat, Undying Vigilante").id
  let g := g.destroyPermanent (named g "Hellcat, Undying Vigilante")
  resolve g (TriggeredAbility.onDeath Effect.deathHellcatReturn) (some old)

#guard
  let cat := named hellcatReturns "Hellcat, Undying Vigilante"
  onBoard hellcatReturns "Hellcat, Undying Vigilante" &&
    cat.status.plusOnePlusOne == 1 && hellcatReturns.hasHaste cat &&
    cat.printed.keywords.haste && cat.printed.triggeredAbilities.isEmpty &&
    cat.printed.activatedAbilities.isEmpty && cat.printed.staticAbilities.isEmpty &&
    logContains hellcatReturns "enters with" &&
    logContains hellcatReturns "loses all abilities"

def hellcatStillInPlay : Game :=
  let g := addPermanent afterDraw hellcatUndyingVigilante me me
  resolve g (TriggeredAbility.onDeath Effect.deathHellcatReturn)
    (some (named g "Hellcat, Undying Vigilante").id)

#guard onBoard hellcatStillInPlay "Hellcat, Undying Vigilante" &&
  (named hellcatStillInPlay "Hellcat, Undying Vigilante").status.plusOnePlusOne == 0 &&
  logContains hellcatStillInPlay "Hellcat is no longer in the graveyard"

/- A Villain in the graveyard returns as a Hero with a finality counter.
A creature that is not a Villain stays in the graveyard. -/
def villainReturns : Game :=
  let g := addPermanent afterDraw thunderboltsConspiracy me me
  let g := addPermanent g agentsOfHYDRA me me
  let villain := named g "Agents of HYDRA"
  let (g, gyId) := g.move villain.id (.graveyard me) none
  resolve g (TriggeredAbility.onDeath Effect.deathVillainReturnAsHero)
    (some (named g "Thunderbolts Conspiracy").id) #[Target.card gyId]

#guard
  let o := named villainReturns "Agents of HYDRA"
  onBoard villainReturns "Agents of HYDRA" &&
    villainReturns.hasSubtype o "Hero" && o.status.finality == 1 &&
    logContains villainReturns "finality counter"

def bearStays : Game :=
  let g := addPermanent afterDraw thunderboltsConspiracy me me
  let g := addPermanent g grizzlyBears me me
  let bear := named g "Grizzly Bears"
  let (g, gyId) := g.move bear.id (.graveyard me) none
  resolve g (TriggeredAbility.onDeath Effect.deathVillainReturnAsHero)
    (some (named g "Thunderbolts Conspiracy").id) #[Target.card gyId]

#guard inZone bearStays (.graveyard me) "Grizzly Bears" &&
  !onBoard bearStays "Grizzly Bears"

/- An attacking creature that died returns to its owner's hand.
A creature that was not attacking is reported and stays in the graveyard. -/
def attackerReturns : Game :=
  let g := addPermanent afterDraw aresGodOfWar me me
  let ares := named g "Ares, God of War"
  let g := g.setObject { ares with status := { ares.status with
    attacking := true, attackingWhom := some opp } }
  let (g, _) := g.move (named g "Ares, God of War").id (.graveyard me) none
  resolve g (TriggeredAbility.onDeath Effect.deathAttackingReturnHand)

#guard inZone attackerReturns (.hand me) "Ares, God of War" &&
  !onBoard attackerReturns "Ares, God of War"

def notAttacking : Game :=
  let g := addPermanent afterDraw aresGodOfWar me me
  let (g, _) := g.move (named g "Ares, God of War").id (.graveyard me) none
  resolve g (TriggeredAbility.onDeath Effect.deathAttackingReturnHand)

#guard inZone notAttacking (.graveyard me) "Ares, God of War" &&
  logContains notAttacking "no longer in the graveyard"

/- Each opponent is asked to sacrifice a nontoken creature. -/
def oppSacrifices : Game :=
  let g := addPermanent (addPermanent afterDraw grizzlyBears opp opp) hillGiant opp opp
  resolve g (TriggeredAbility.onDeath Effect.deathDeathtouchOppSac)

#guard
  match oppSacrifices.pending with
  | .fraChoice q (.sacrificeNontokenEach ..) => q == opp
  | _ => false

end Mtg.Engine.DeathTests
