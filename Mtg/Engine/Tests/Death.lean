import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Fixture
import Mtg.Engine.Game
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns

/-!
# Unified dies triggers

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

/- The dies triggers carry unified `Instruction` bodies and keep their Oracle lines. -/
#guard (TriggeredAbility.onDeath Effect.deathHellcatReturn).effect.body == Effect.deathHellcatReturn.body
#guard (TriggeredAbility.onDeath Effect.deathVillainReturnAsHero).effect.body == Effect.deathVillainReturnAsHero.body
#guard (TriggeredAbility.onDeath Effect.deathAttackingReturnHand).effect.body == Effect.deathAttackingReturnHand.body
#guard (TriggeredAbility.onDeath Effect.deathDeathtouchOppSac).effect.body == Effect.deathDeathtouchOppSac.body
#guard toString (TriggeredAbility.onDeath Effect.deathHellcatReturn) ==
  "When this creature dies, return card in a graveyard that is this permanent onto the battlefield under its owner's control with a +1/+1 counter on it with haste with no abilities."
#guard toString (TriggeredAbility.onDeath Effect.deathVillainReturnAsHero) ==
  "Whenever a Villain creature you control dies, return that permanent matching Villain onto the battlefield under its owner's control with a finality counter on it as Hero in addition to its other types."
#guard toString (TriggeredAbility.onDeath Effect.deathAttackingReturnHand) ==
  "Whenever an attacking creature you control dies, return that permanent to its owner's hand."
#guard toString (TriggeredAbility.onDeath Effect.deathDeathtouchOppSac) ==
  "Whenever another creature you control with deathtouch dies, for each an opponent, that player sacrifices a nontoken creature that player controls."

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
    KeywordAbility.hasHaste (hellcatReturns.currentKeywords cat) &&
    (hellcatReturns.triggeredAbilities cat).isEmpty &&
    (hellcatReturns.activatedAbilitiesOf cat).isEmpty &&
    (hellcatReturns.staticAbilities cat).isEmpty &&
    !cat.printed.triggeredAbilities.isEmpty &&
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
    villainReturns.hasSubtype o .hero && o.status.finality == 1 &&
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
  let g := g.markAttacking ares.id (some (.player opp))
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
