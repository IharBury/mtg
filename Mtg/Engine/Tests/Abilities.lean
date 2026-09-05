import Mtg.Engine.Agent
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Game
import Mtg.Engine.Oracle
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns
import Mtg.Engine.Tests.Auras

/-!
# Additional costs, graveyard activations, mass effects, and MSH smokes.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/- Black Hobbit Welcome Deck: structured abilities for each remaining card. -/

/-- Empty `p`'s hand so injected spells are the only playable cards. -/
def emptyHand (g : Game) (p : PlayerId) : Game :=
  g.modifyPlayer p (fun pl => { pl with hand := #[] })

def readyMain (g : Game) : Game :=
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })

/-- Front Porch Sentries: dies, target opposing creature gets -1 / -1. -/
def sentriesDied : Game :=
  let g := addPermanent afterDraw frontPorchSentriesCard ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let (g, _) := g.move (namedPermanent g "Front Porch Sentries").id (.graveyard ⟨0⟩) none
  g.receivePriority ⟨0⟩

#guard sentriesDied.pending == .chooseTargets ⟨0⟩
#guard (sentriesDied.object! sentriesDied.stack.back!.objectId).triggeredAbility ==
  some (.onDiesOppCreatureGets (-1) (-1))
#guard sentriesDied.log.any (fun s => mentions s "dies trigger is put on the stack")
#guard
  match Agent.choose sentriesDied ⟨0⟩ with
  | some (.target (Target.permanent id)) =>
    (sentriesDied.object! id).name == "Grizzly Bears"
  | _ => false

def sentriesPumpResolved : Game :=
  let g := mustApply sentriesDied ⟨0⟩
    (.target (Target.permanent (namedPermanent sentriesDied "Grizzly Bears").id))
  passBoth g

#guard sentriesPumpResolved.power (namedPermanent sentriesPumpResolved "Grizzly Bears") == 1
#guard sentriesPumpResolved.toughness (namedPermanent sentriesPumpResolved "Grizzly Bears") == 1
#guard sentriesPumpResolved.log.any (fun s =>
  mentions s "Grizzly Bears gets -1/-1 until end of turn")

#guard
  let g := addPermanent afterDraw frontPorchSentriesCard ⟨0⟩ ⟨0⟩
  let (g, _) := g.move (namedPermanent g "Front Porch Sentries").id (.graveyard ⟨0⟩) none
  let g := g.receivePriority ⟨0⟩
  g.stack.isEmpty && g.log.any (fun s => mentions s "no legal target")

/-- Great Fierce Bee: another creature dying scries 1. -/
def beeOtherDied : Game :=
  let g := addPermanent afterDraw greatFierceBeeCard ⟨0⟩ ⟨0⟩
  let g := addPermanent g ragingGoblin ⟨0⟩ ⟨0⟩
  let (g, _) := g.move (namedPermanent g "Raging Goblin").id (.graveyard ⟨0⟩) none
  g.receivePriority ⟨0⟩

#guard beeOtherDied.stack.size == 1
#guard (beeOtherDied.object! beeOtherDied.stack.back!.objectId).triggeredAbility ==
  some (.onOneOrMoreOtherCreaturesDieScry 1)
#guard beeOtherDied.creatureDiedThisTurn

def beeScrying : Game := passBoth beeOtherDied

#guard
  match beeScrying.pending with
  | .scry ⟨0⟩ 1 => true
  | _ => false
#guard beeScrying.log.any (fun s => mentions s "scries 1")

#guard
  let g := addPermanent afterDraw greatFierceBeeCard ⟨0⟩ ⟨0⟩
  let (g, _) := g.move (namedPermanent g "Great Fierce Bee").id (.graveyard ⟨0⟩) none
  let g := g.receivePriority ⟨0⟩
  g.stack.isEmpty && g.creatureDiedThisTurn

#guard
  let g := addPermanent afterDraw greatFierceBeeCard ⟨0⟩ ⟨0⟩
  let g := addPermanent g ragingGoblin ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let (g, _) := g.move (namedPermanent g "Raging Goblin").id (.graveyard ⟨0⟩) none
  let (g, _) := g.move (namedPermanent g "Gray Ogre").id (.graveyard ⟨1⟩) none
  let g := g.receivePriority ⟨0⟩
  g.stack.size == 1

/-- Stir Up Trouble: additional cost is sacrifice or pay {4}, then destroy.
Additional costs are announced at CR 601.2b, before targets at 601.2c. -/
def stirReady : Game :=
  let g := addPermanent afterDraw ragingGoblin ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := readyMain (emptyHand g ⟨0⟩)
  withBlackMana (addToHand g stirUpTroubleCard ⟨0⟩) ⟨0⟩ 1

#guard stirReady.canCast ⟨0⟩ (handCardNamed stirReady ⟨0⟩ "Stir Up Trouble")
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := readyMain (emptyHand g ⟨0⟩)
  let g := withBlackMana (addToHand g stirUpTroubleCard ⟨0⟩) ⟨0⟩ 5
  g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Stir Up Trouble")

def proposedStir : Game :=
  mustApply stirReady ⟨0⟩ (.cast (handCardNamed stirReady ⟨0⟩ "Stir Up Trouble").id)

#guard
  match proposedStir.pending with
  | .chooseAdditionalCost ⟨0⟩ => true
  | _ => false
#guard proposedStir.log.any (fun s =>
  mentions s "must choose an additional cost (CR 601.2b)")
#guard
  match proposedStir.apply ⟨0⟩
      (.target (Target.permanent (namedPermanent proposedStir "Grizzly Bears").id)) with
  | .error msg => mentions msg "Not time to choose targets (CR 601.2c)"
  | .ok _ => false
#guard
  match Agent.choose proposedStir ⟨0⟩ with
  | some (.chooseAdditionalCost false) => true
  | _ => false

/-- Alias used by the demo: the 601.2b additional-cost window. -/
def stirChooseAdditional : Game := proposedStir

def stirSacChosen : Game :=
  mustApply stirChooseAdditional ⟨0⟩ (.chooseAdditionalCost false)

#guard
  match stirSacChosen.pending with
  | .chooseTargets ⟨0⟩ => true
  | _ => false
#guard
  match stirSacChosen.proposedSpell with
  | some prop => prop.needsSacrificeOther && prop.cost == ManaCost.ofColor .black
  | none => false
#guard stirSacChosen.log.any (fun s =>
  mentions s "chooses to sacrifice an artifact or creature (CR 601.2b)")

def stirSacTargeted : Game :=
  mustApply stirSacChosen ⟨0⟩
    (.target (Target.permanent (namedPermanent stirSacChosen "Grizzly Bears").id))

#guard stirSacTargeted.pending == .activateManaAbilities ⟨0⟩

def stirPaidSac : Game := mustApply stirSacTargeted ⟨0⟩ .pay

#guard
  match stirPaidSac.pending with
  | .sacrificePermanent ⟨0⟩ _ => true
  | _ => false

def stirCastViaSac : Game :=
  mustApply stirPaidSac ⟨0⟩ (.sacrifice (namedPermanent stirPaidSac "Raging Goblin").id)

#guard stirCastViaSac.log.any (fun s => mentions s "casts Stir Up Trouble")
#guard !(stirCastViaSac.battlefield.any (fun o => o.name == "Raging Goblin"))

def stirResolvedViaSac : Game := passBoth stirCastViaSac

#guard !(stirResolvedViaSac.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard stirResolvedViaSac.log.any (fun s => mentions s "Grizzly Bears is destroyed")

def stirPayGenericReady : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := readyMain (emptyHand g ⟨0⟩)
  withBlackMana (addToHand g stirUpTroubleCard ⟨0⟩) ⟨0⟩ 5

def stirPayGenericChosen : Game :=
  let g := mustApply stirPayGenericReady ⟨0⟩
    (.cast (handCardNamed stirPayGenericReady ⟨0⟩ "Stir Up Trouble").id)
  let g := mustApply g ⟨0⟩ (.chooseAdditionalCost true)
  mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Grizzly Bears").id))

#guard
  match stirPayGenericChosen.proposedSpell with
  | some prop =>
    !prop.needsSacrificeOther && prop.cost.manaValue == 5
  | none => false
#guard stirPayGenericChosen.pending == .activateManaAbilities ⟨0⟩
#guard stirPayGenericChosen.log.any (fun s =>
  mentions s "chooses to pay {4} as an additional cost (CR 601.2b)")

def stirResolvedViaPay : Game :=
  passBoth (mustApply stirPayGenericChosen ⟨0⟩ .pay)

#guard !(stirResolvedViaPay.battlefield.any (fun o => o.name == "Grizzly Bears"))

/-- Haunt of the Dead Marshes: GY activate only with a legendary creature. -/
def hauntAbility : ActivatedAbility :=
  hauntOfTheDeadMarshes.activatedAbilities[0]!

def hauntInGy : Game :=
  let g := readyMain (addToGraveyard afterDraw hauntOfTheDeadMarshes ⟨0⟩)
  withBlackMana g ⟨0⟩ 3

#guard !(hauntInGy.canActivate ⟨0⟩
  (namedGraveyardCard hauntInGy ⟨0⟩ "Haunt of the Dead Marshes") hauntAbility)

def hauntInGyWithLegend : Game :=
  addPermanent hauntInGy gollumSilentSlinkerCard ⟨0⟩ ⟨0⟩

#guard hauntInGyWithLegend.canActivate ⟨0⟩
  (namedGraveyardCard hauntInGyWithLegend ⟨0⟩ "Haunt of the Dead Marshes") hauntAbility
#guard
  let g := addPermanent hauntInGy hauntOfTheDeadMarshes ⟨0⟩ ⟨0⟩
  let g := addPermanent g gollumSilentSlinkerCard ⟨0⟩ ⟨0⟩
  !(g.canActivate ⟨0⟩ (namedPermanent g "Haunt of the Dead Marshes") hauntAbility)

def hauntReturned : Game :=
  let g := hauntInGyWithLegend
  let src := namedGraveyardCard g ⟨0⟩ "Haunt of the Dead Marshes"
  let g := mustApply g ⟨0⟩ (.activate src.id 0)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard hauntReturned.battlefield.any (fun o =>
  o.name == "Haunt of the Dead Marshes" && o.status.tapped)
#guard hauntReturned.log.any (fun s =>
  mentions s "returns to the battlefield tapped")
#guard hauntReturned.stack.size == 1
#guard (hauntReturned.object! hauntReturned.stack.back!.objectId).triggeredAbility ==
  some (.onEnterScry 1)

/-- Gollum, Silent Slinker: menace requires two blockers. -/
def gollumMenaceField : Game :=
  let g := addPermanent afterDraw gollumSilentSlinkerCard ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  addPermanent g llanowarElves ⟨1⟩ ⟨1⟩

#guard (namedPermanent gollumMenaceField "Gollum, Silent Slinker").printed.keywords.menace
#guard gollumMenaceField.minBlockersRequired
  (namedPermanent gollumMenaceField "Gollum, Silent Slinker") == 2

def gollumAttacking : Game :=
  let g := passBoth (skipTo gollumMenaceField .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gollum, Silent Slinker").id])

def gollumDeclareBlockers : Game := passBoth gollumAttacking

#guard gollumDeclareBlockers.pending == .declareBlockers
#guard
  match gollumDeclareBlockers.apply ⟨1⟩ (.declareBlockers #[(
    (namedPermanent gollumDeclareBlockers "Grizzly Bears").id,
    (namedPermanent gollumDeclareBlockers "Gollum, Silent Slinker").id)]) with
  | .error msg => mentions msg "two or more creatures"
  | .ok _ => false

def gollumBlockedByTwo : Game :=
  mustApply gollumDeclareBlockers ⟨1⟩ (.declareBlockers #[
    ((namedPermanent gollumDeclareBlockers "Grizzly Bears").id,
      (namedPermanent gollumDeclareBlockers "Gollum, Silent Slinker").id),
    ((namedPermanent gollumDeclareBlockers "Llanowar Elves").id,
      (namedPermanent gollumDeclareBlockers "Gollum, Silent Slinker").id)])

#guard (namedPermanent gollumBlockedByTwo "Gollum, Silent Slinker").status.blocked
#guard gollumBlockedByTwo.log.any (fun s => mentions s "Grizzly Bears blocks")
#guard gollumBlockedByTwo.log.any (fun s => mentions s "Llanowar Elves blocks")

/-- Bilbo's Deadly Slice destroys a creature. -/
def sliceSetup : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := readyMain (emptyHand g ⟨0⟩)
  withBlackMana (addToHand g bilbosDeadlySliceCard ⟨0⟩) ⟨0⟩ 3

#guard sliceSetup.canCast ⟨0⟩ (handCardNamed sliceSetup ⟨0⟩ "Bilbo's Deadly Slice")
#guard
  match Agent.choose sliceSetup ⟨0⟩ with
  | some (.cast id) => (sliceSetup.object! id).name == "Bilbo's Deadly Slice"
  | _ => false

def sliceResolved : Game :=
  let g := mustApply sliceSetup ⟨0⟩
    (.cast (handCardNamed sliceSetup ⟨0⟩ "Bilbo's Deadly Slice").id)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Grizzly Bears").id))
  passBoth (mustApply g ⟨0⟩ .pay)

#guard !(sliceResolved.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard sliceResolved.log.any (fun s => mentions s "Grizzly Bears is destroyed")

/-- Dreaded Bat-Cloud costs {3} less if a creature died this turn. -/
def batCloudFull : Game :=
  let g := readyMain (emptyHand afterDraw ⟨0⟩)
  withBlackMana (addToHand g dreadedBatCloudCard ⟨0⟩) ⟨0⟩ 5

def batCloudReduced : Game :=
  { batCloudFull with creatureDiedThisTurn := true }

#guard batCloudFull.canCast ⟨0⟩ (handCardNamed batCloudFull ⟨0⟩ "Dreaded Bat-Cloud")
#guard
  match batCloudFull.apply ⟨0⟩
      (.cast (handCardNamed batCloudFull ⟨0⟩ "Dreaded Bat-Cloud").id) with
  | .ok g' =>
    match g'.proposedSpell with
    | some prop => prop.cost.manaValue == 5
    | none => false
  | .error _ => false
#guard
  match batCloudReduced.apply ⟨0⟩
      (.cast (handCardNamed batCloudReduced ⟨0⟩ "Dreaded Bat-Cloud").id) with
  | .ok g' =>
    match g'.proposedSpell with
    | some prop => prop.cost.manaValue == 2
    | none => false
  | .error _ => false
#guard
  let g := addPermanent afterDraw hillGiant ⟨0⟩ ⟨0⟩
  let (g, _) := g.move (namedPermanent g "Hill Giant").id (.graveyard ⟨0⟩) none
  g.creatureDiedThisTurn
#guard
  let g := addPermanent afterDraw hillGiant ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Hill Giant"
  let g := g.setObject { o with status := { o.status with untilEotExileIfDies := true } }
  let (g, _) := g.move (namedPermanent g "Hill Giant").id (.graveyard ⟨0⟩) none
  !g.creatureDiedThisTurn


/-- Languish: all creatures get -4 / -4. -/
def languishReady : Game :=
  let g := addPermanent afterDraw ragingGoblin ⟨0⟩ ⟨0⟩
  let g := addPermanent g rumblingBaloth ⟨1⟩ ⟨1⟩
  let g := readyMain (emptyHand g ⟨0⟩)
  withBlackMana (addToHand g languish ⟨0⟩) ⟨0⟩ 4

#guard languishReady.canCast ⟨0⟩ (handCardNamed languishReady ⟨0⟩ "Languish")
#guard !languish.requiresTarget
#guard
  match Agent.choose languishReady ⟨0⟩ with
  | some (.cast id) => (languishReady.object! id).name == "Languish"
  | _ => false

def languishResolved : Game :=
  let g := mustApply languishReady ⟨0⟩
    (.cast (handCardNamed languishReady ⟨0⟩ "Languish").id)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard !(languishResolved.battlefield.any (fun o => o.name == "Raging Goblin"))
#guard !(languishResolved.battlefield.any (fun o => o.name == "Rumbling Baloth"))
#guard languishResolved.log.any (fun s =>
  mentions s "gets -4/-4 until end of turn")

/-- Shadow of the Enemy: exile GY creatures and grant any-mana casts. -/
def shadowReady : Game :=
  let g := addToGraveyard afterDraw grayOgre ⟨1⟩
  let g := addToGraveyard g lightningBolt ⟨1⟩
  let g := readyMain (emptyHand g ⟨0⟩)
  withBlackMana (addToHand g shadowOfTheEnemy ⟨0⟩) ⟨0⟩ 6

def shadowResolved : Game :=
  let g := mustApply shadowReady ⟨0⟩
    (.cast (handCardNamed shadowReady ⟨0⟩ "Shadow of the Enemy").id)
  let g := mustApply g ⟨0⟩ (.target (Target.player ⟨1⟩))
  passBoth (mustApply g ⟨0⟩ .pay)

#guard shadowResolved.objects.any (fun o =>
  o.name == "Gray Ogre" && o.zone == .exile)
#guard shadowResolved.objects.any (fun o =>
  o.name == "Lightning Bolt" && o.zone == .graveyard ⟨1⟩)
#guard
  match (shadowResolved.objects.find? (fun o =>
      o.name == "Gray Ogre" && o.zone == .exile)) with
  | some ogre =>
    match ogre.playPermission with
    | some perm => perm.whileExiled && perm.anyMana && perm.player == ⟨0⟩
    | none => false
  | none => false

#guard
  match (shadowResolved.objects.find? (fun o =>
      o.name == "Gray Ogre" && o.zone == .exile)) with
  | none => false
  | some ogre =>
    match shadowResolved.apply ⟨0⟩ (.cast ogre.id) with
    | .ok g' =>
      match g'.proposedSpell with
      | some prop => prop.cost == ManaCost.ofGeneric 3
      | none => false
    | .error _ => false

def shadowCastOgre : Game :=
  let g := readyMain (emptyHand shadowResolved ⟨0⟩)
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with manaPool := {} })
  let g := withGreenMana g ⟨0⟩ 3
  match g.objects.find? (fun o => o.name == "Gray Ogre" && o.zone == .exile) with
  | none => panic! "expected Gray Ogre in exile"
  | some ogre =>
    let g := mustApply g ⟨0⟩ (.cast ogre.id)
    passBoth (mustApply g ⟨0⟩ .pay)

#guard shadowCastOgre.battlefield.any (fun o => o.name == "Gray Ogre")

/-- Gollum the Abandoned: can't block; ETB exile GY + opps lose 2; GY to hand. -/
def abandonedAbility : ActivatedAbility :=
  gollumTheAbandonedCard.activatedAbilities[0]!

#guard
  let g := addPermanent afterDraw gollumTheAbandonedCard ⟨1⟩ ⟨1⟩
  !g.mayDeclareAsBlocker (namedPermanent g "Gollum the Abandoned")

#guard
  let g := addPermanent afterDraw gollumTheAbandonedCard ⟨1⟩ ⟨1⟩
  let g := addPermanent g ragingGoblin ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Raging Goblin").id])
  let g := passBoth g
  match g.apply ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Gollum the Abandoned").id,
    (namedPermanent g "Raging Goblin").id)]) with
  | .error msg => mentions msg "cannot block"
  | .ok _ => false

def abandonedEtbReady : Game :=
  let g := addToGraveyard afterDraw llanowarElves ⟨1⟩
  let g := readyMain (emptyHand g ⟨0⟩)
  withBlackMana (addToHand g gollumTheAbandonedCard ⟨0⟩) ⟨0⟩ 2

def abandonedEntered : Game :=
  let g := mustApply abandonedEtbReady ⟨0⟩
    (.cast (handCardNamed abandonedEtbReady ⟨0⟩ "Gollum the Abandoned").id)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard abandonedEntered.pending == .chooseTargets ⟨0⟩
#guard (abandonedEntered.object! abandonedEntered.stack.back!.objectId).triggeredAbility ==
  some (.onEnterExileOppGyCardOppsLoseLife 2)

def abandonedDeclined : Game :=
  let g := mustApply abandonedEntered ⟨0⟩ .decline
  passBoth g

#guard (abandonedDeclined.player ⟨1⟩).life == 18
#guard abandonedDeclined.objects.any (fun o =>
  o.name == "Llanowar Elves" && o.zone == .graveyard ⟨1⟩)
#guard abandonedDeclined.log.any (fun s => mentions s "Nissa loses 2 life")

def abandonedExiled : Game :=
  let g := mustApply abandonedEntered ⟨0⟩
    (.target (Target.card (namedGraveyardCard abandonedEntered ⟨1⟩ "Llanowar Elves").id))
  passBoth g

#guard abandonedExiled.objects.any (fun o =>
  o.name == "Llanowar Elves" && o.zone == .exile)
#guard (abandonedExiled.player ⟨1⟩).life == 18

def abandonedInGy : Game :=
  let g := addToGraveyard afterDraw gollumTheAbandonedCard ⟨0⟩
  let g := addPermanent g ragingGoblin ⟨0⟩ ⟨0⟩
  let g := readyMain g
  withBlackMana g ⟨0⟩ 2

#guard abandonedInGy.canActivate ⟨0⟩
  (namedGraveyardCard abandonedInGy ⟨0⟩ "Gollum the Abandoned") abandonedAbility

def abandonedReturnedToHand : Game :=
  let g := abandonedInGy
  let src := namedGraveyardCard g ⟨0⟩ "Gollum the Abandoned"
  let g := mustApply g ⟨0⟩ (.activate src.id 0)
  let g := mustApply g ⟨0⟩ .pay
  let g := mustApply g ⟨0⟩ (.sacrifice (namedPermanent g "Raging Goblin").id)
  passBoth g

#guard (abandonedReturnedToHand.handObjects ⟨0⟩).any (fun o =>
  o.name == "Gollum the Abandoned")
#guard !(abandonedReturnedToHand.battlefield.any (fun o => o.name == "Raging Goblin"))
#guard abandonedReturnedToHand.log.any (fun s =>
  mentions s "returned to Chandra's hand")

/-- Gnashing of Teeth: -5 / -5 exile-if-dies, or creatures of a player -1 / -1. -/
def gnashingReady : Game :=
  let g := addPermanent afterDraw rumblingBaloth ⟨1⟩ ⟨1⟩
  let g := readyMain (emptyHand g ⟨0⟩)
  withBlackMana (addToHand g gnashingOfTeethCard ⟨0⟩) ⟨0⟩ 3

#guard gnashingOfTeethCard.isModal
#guard
  match Agent.choose gnashingReady ⟨0⟩ with
  | some (.cast id) => (gnashingReady.object! id).name == "Gnashing of Teeth"
  | _ => false

def gnashingMinusFive : Game :=
  let g := mustApply gnashingReady ⟨0⟩
    (.cast (handCardNamed gnashingReady ⟨0⟩ "Gnashing of Teeth").id)
  let g := mustApply g ⟨0⟩ (.chooseMode 0)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Rumbling Baloth").id))
  passBoth (mustApply g ⟨0⟩ .pay)

#guard !(gnashingMinusFive.battlefield.any (fun o => o.name == "Rumbling Baloth"))
#guard gnashingMinusFive.objects.any (fun o =>
  o.name == "Rumbling Baloth" && o.zone == .exile)
#guard gnashingMinusFive.log.any (fun s =>
  mentions s "If Rumbling Baloth would die this turn, exile it instead")
#guard gnashingMinusFive.log.any (fun s => mentions s "exiled instead of dying")

def gnashingPlayerPump : Game :=
  let g := addPermanent gnashingReady grizzlyBears ⟨0⟩ ⟨0⟩
  let g := mustApply g ⟨0⟩
    (.cast (handCardNamed g ⟨0⟩ "Gnashing of Teeth").id)
  let g := mustApply g ⟨0⟩ (.chooseMode 1)
  let g := mustApply g ⟨0⟩ (.target (Target.player ⟨0⟩))
  passBoth (mustApply g ⟨0⟩ .pay)

#guard gnashingPlayerPump.power (namedPermanent gnashingPlayerPump "Grizzly Bears") == 1
#guard gnashingPlayerPump.toughness (namedPermanent gnashingPlayerPump "Grizzly Bears") == 1

/-- Troll of Khazad-dûm: can't be blocked except by three or more. -/
def trollField : Game :=
  let g := addPermanent afterDraw trollOfKhazadDum ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g llanowarElves ⟨1⟩ ⟨1⟩
  addPermanent g giantSpider ⟨1⟩ ⟨1⟩

#guard trollField.minBlockersRequired (namedPermanent trollField "Troll of Khazad-dûm") == 3

def trollDeclareBlockers : Game :=
  let g := passBoth (skipTo trollField .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Troll of Khazad-dûm").id])
  passBoth g

#guard
  match trollDeclareBlockers.apply ⟨1⟩ (.declareBlockers #[
    ((namedPermanent trollDeclareBlockers "Grizzly Bears").id,
      (namedPermanent trollDeclareBlockers "Troll of Khazad-dûm").id),
    ((namedPermanent trollDeclareBlockers "Llanowar Elves").id,
      (namedPermanent trollDeclareBlockers "Troll of Khazad-dûm").id)]) with
  | .error msg => mentions msg "3 or more creatures"
  | .ok _ => false

def trollBlockedByThree : Game :=
  mustApply trollDeclareBlockers ⟨1⟩ (.declareBlockers #[
    ((namedPermanent trollDeclareBlockers "Grizzly Bears").id,
      (namedPermanent trollDeclareBlockers "Troll of Khazad-dûm").id),
    ((namedPermanent trollDeclareBlockers "Llanowar Elves").id,
      (namedPermanent trollDeclareBlockers "Troll of Khazad-dûm").id),
    ((namedPermanent trollDeclareBlockers "Giant Spider").id,
      (namedPermanent trollDeclareBlockers "Troll of Khazad-dûm").id)])

#guard (namedPermanent trollBlockedByThree "Troll of Khazad-dûm").status.blocked

/-- Merciless Executioner: each player sacrifices a creature. -/
def executionerReady : Game :=
  let g := addPermanent afterDraw ragingGoblin ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := readyMain (emptyHand g ⟨0⟩)
  withBlackMana (addToHand g mercilessExecutioner ⟨0⟩) ⟨0⟩ 3

def executionerEntered : Game :=
  let g := mustApply executionerReady ⟨0⟩
    (.cast (handCardNamed executionerReady ⟨0⟩ "Merciless Executioner").id)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard executionerEntered.stack.size == 1
#guard (executionerEntered.object! executionerEntered.stack.back!.objectId).triggeredAbility ==
  some .onEnterEachPlayerSacrificesCreature

def executionerSacrificing : Game := passBoth executionerEntered

#guard
  match executionerSacrificing.pending with
  | .chooseSacrificeCreature ⟨0⟩ _ _ => true
  | _ => false

def executionerBothSac : Game :=
  let g := mustApply executionerSacrificing ⟨0⟩
    (.sacrifice (namedPermanent executionerSacrificing "Raging Goblin").id)
  mustApply g ⟨1⟩ (.sacrifice (namedPermanent g "Grizzly Bears").id)

#guard !(executionerBothSac.battlefield.any (fun o => o.name == "Raging Goblin"))
#guard !(executionerBothSac.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard executionerBothSac.battlefield.any (fun o => o.name == "Merciless Executioner")
#guard executionerBothSac.pending == .none

/-- Bitter Downfall: destroy and controller loses 2; {3} less if damaged. -/
def downfallSetup (damaged : Bool) : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g :=
    if damaged then
      let o := namedPermanent g "Grizzly Bears"
      g.setObject { o with status := { o.status with damage := 1 } }
    else g
  let g := readyMain (emptyHand g ⟨0⟩)
  withBlackMana (addToHand g bitterDownfall ⟨0⟩) ⟨0⟩ 4

def downfallFull : Game := downfallSetup false
def downfallCheap : Game := downfallSetup true

#guard
  match downfallFull.apply ⟨0⟩
      (.cast (handCardNamed downfallFull ⟨0⟩ "Bitter Downfall").id) with
  | .ok g' =>
    match g'.proposedSpell with
    | some prop => prop.cost.manaValue == 4
    | none => false
  | .error _ => false

def downfallCheapLocked : Game :=
  let g := mustApply downfallCheap ⟨0⟩
    (.cast (handCardNamed downfallCheap ⟨0⟩ "Bitter Downfall").id)
  mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Grizzly Bears").id))

#guard
  match downfallCheapLocked.proposedSpell with
  | some prop => prop.cost.manaValue == 1
  | none => false

def downfallResolved : Game :=
  passBoth (mustApply downfallCheapLocked ⟨0⟩ .pay)

#guard !(downfallResolved.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard (downfallResolved.player ⟨1⟩).life == 18
#guard downfallResolved.log.any (fun s => mentions s "Nissa loses 2 life")

/-- Reverent Howl: draw 2 lose 2, or +2/+2 and lifelink. -/
def howlReady : Game :=
  let g := addPermanent afterDraw ragingGoblin ⟨0⟩ ⟨0⟩
  let g := readyMain (emptyHand g ⟨0⟩)
  withBlackMana (addToHand g reverentHowlCard ⟨0⟩) ⟨0⟩ 3

def howlDraw : Game :=
  let g := mustApply howlReady ⟨0⟩
    (.cast (handCardNamed howlReady ⟨0⟩ "Reverent Howl").id)
  let g := mustApply g ⟨0⟩ (.chooseMode 0)
  let g := mustApply g ⟨0⟩ (.target (Target.player ⟨0⟩))
  passBoth (mustApply g ⟨0⟩ .pay)

#guard (howlDraw.player ⟨0⟩).life == 18
#guard (howlDraw.player ⟨0⟩).hand.size == 2
#guard howlDraw.log.any (fun s => mentions s "Chandra loses 2 life")

def howlLifelink : Game :=
  let g := mustApply howlReady ⟨0⟩
    (.cast (handCardNamed howlReady ⟨0⟩ "Reverent Howl").id)
  let g := mustApply g ⟨0⟩ (.chooseMode 1)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Raging Goblin").id))
  passBoth (mustApply g ⟨0⟩ .pay)

#guard howlLifelink.power (namedPermanent howlLifelink "Raging Goblin") == 3
#guard howlLifelink.toughness (namedPermanent howlLifelink "Raging Goblin") == 3
#guard howlLifelink.hasLifelink (namedPermanent howlLifelink "Raging Goblin")
#guard howlLifelink.log.any (fun s => mentions s "gains lifelink until end of turn")

def howlCombat : Game :=
  let g := passBoth (skipTo howlLifelink .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Raging Goblin").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[])
  passBoth g

#guard (howlCombat.player ⟨1⟩).life == 17
#guard (howlCombat.player ⟨0⟩).life == 23
#guard howlCombat.log.any (fun s => mentions s "gains 3 life")

/-- Night's Whisper: draw 2, lose 2 (no target). -/
def whisperReady : Game :=
  let g := readyMain (emptyHand afterDraw ⟨0⟩)
  withBlackMana (addToHand g nightsWhisper ⟨0⟩) ⟨0⟩ 2

#guard whisperReady.canCast ⟨0⟩ (handCardNamed whisperReady ⟨0⟩ "Night's Whisper")
#guard !nightsWhisper.requiresTarget
#guard
  match Agent.choose whisperReady ⟨0⟩ with
  | some (.cast id) => (whisperReady.object! id).name == "Night's Whisper"
  | _ => false

def whisperResolved : Game :=
  let g := mustApply whisperReady ⟨0⟩
    (.cast (handCardNamed whisperReady ⟨0⟩ "Night's Whisper").id)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard (whisperResolved.player ⟨0⟩).life == 18
#guard (whisperResolved.player ⟨0⟩).hand.size == 2
#guard whisperResolved.log.any (fun s => mentions s "Chandra loses 2 life")

/-- Stony-Voiced Goblins: each opponent discards a card. -/
def stonyReady : Game :=
  let g := readyMain (emptyHand afterDraw ⟨0⟩)
  withBlackMana (addToHand g stonyVoicedGoblinsCard ⟨0⟩) ⟨0⟩ 2

def stonyEntered : Game :=
  let g := mustApply stonyReady ⟨0⟩
    (.cast (handCardNamed stonyReady ⟨0⟩ "Stony-Voiced Goblins").id)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard stonyEntered.stack.size == 1
#guard (stonyEntered.object! stonyEntered.stack.back!.objectId).triggeredAbility ==
  some .onEnterEachOpponentDiscards

def stonyDiscarding : Game := passBoth stonyEntered

#guard
  match stonyDiscarding.pending with
  | .chooseDiscardCard ⟨1⟩ _ => true
  | _ => false
#guard (stonyDiscarding.player ⟨1⟩).hand.size == 7
#guard
  match Agent.choose stonyDiscarding ⟨1⟩ with
  | some (.discard _) => true
  | _ => false

def stonyAfterDiscard : Game := applyIdle stonyDiscarding

#guard (stonyAfterDiscard.player ⟨1⟩).hand.size == 6
#guard stonyAfterDiscard.pending == .none
#guard stonyAfterDiscard.log.any (fun s => mentions s "Nissa discards")

/-- “Discard two cards” starts one pending discard and keeps a remaining
count; calling `beginDiscardCards` twice only replaced the choice. -/
def discardTwoPending : Game :=
  afterDraw.drawThenBeginDiscard ⟨0⟩ 0 (discardRounds := 2)

#guard
  match discardTwoPending.pending with
  | .chooseDiscardCard ⟨0⟩ _ => true
  | _ => false
#guard discardTwoPending.pendingDiscardsLeft == 2
#guard (discardTwoPending.player ⟨0⟩).hand.size == 7
#guard
  (discardTwoPending.log.filter (fun s => mentions s "must discard a card")).size == 1

def discardTwoAfterFirst : Game :=
  mustApply discardTwoPending ⟨0⟩
    (.discard (discardTwoPending.player ⟨0⟩).hand.back!)

#guard
  match discardTwoAfterFirst.pending with
  | .chooseDiscardCard ⟨0⟩ _ => true
  | _ => false
#guard discardTwoAfterFirst.pendingDiscardsLeft == 1
#guard (discardTwoAfterFirst.player ⟨0⟩).hand.size == 6
#guard (discardTwoAfterFirst.player ⟨0⟩).graveyard.size == 1

def discardTwoAfterSecond : Game :=
  mustApply discardTwoAfterFirst ⟨0⟩
    (.discard (discardTwoAfterFirst.player ⟨0⟩).hand.back!)

#guard discardTwoAfterSecond.pending == .none
#guard discardTwoAfterSecond.pendingDiscardsLeft == 0
#guard (discardTwoAfterSecond.player ⟨0⟩).hand.size == 5
#guard (discardTwoAfterSecond.player ⟨0⟩).graveyard.size == 2

/-- An artifact does not finish a required two-card discard (unlike Thirst). -/
def discardTwoArtifactStillNeedsSecond : Bool :=
  let g := addToHand afterDraw theMindStone ⟨0⟩
  let g := g.drawThenBeginDiscard ⟨0⟩ 0 (discardRounds := 2)
  let g := mustApply g ⟨0⟩ (.discard (handCardNamed g ⟨0⟩ "The Mind Stone").id)
  (match g.pending with
   | .chooseDiscardCard ⟨0⟩ _ => true
   | _ => false) &&
    g.pendingDiscardsLeft == 1 &&
    (g.player ⟨0⟩).graveyard.any (fun id => (g.object! id).name == "The Mind Stone")

#guard discardTwoArtifactStillNeedsSecond

/-- HYDRA Infiltration: target opponent discards two cards. -/
def hydraInfiltrationDiscarding : Game :=
  afterDraw.applyTriggeredAbility ⟨0⟩ (.onEnterTargetOpponentDiscards 2) none
    #[Target.player ⟨1⟩]

#guard
  match hydraInfiltrationDiscarding.pending with
  | .chooseDiscardCard ⟨1⟩ _ => true
  | _ => false
#guard hydraInfiltrationDiscarding.pendingDiscardsLeft == 2
#guard (hydraInfiltrationDiscarding.player ⟨1⟩).hand.size == 7
#guard
  (hydraInfiltrationDiscarding.log.filter (fun s =>
    mentions s "must discard a card")).size == 1

def hydraInfiltrationAfterFirst : Game :=
  mustApply hydraInfiltrationDiscarding ⟨1⟩
    (.discard (hydraInfiltrationDiscarding.player ⟨1⟩).hand.back!)

#guard
  match hydraInfiltrationAfterFirst.pending with
  | .chooseDiscardCard ⟨1⟩ _ => true
  | _ => false
#guard (hydraInfiltrationAfterFirst.player ⟨1⟩).hand.size == 6

def hydraInfiltrationAfterSecond : Game :=
  mustApply hydraInfiltrationAfterFirst ⟨1⟩
    (.discard (hydraInfiltrationAfterFirst.player ⟨1⟩).hand.back!)

#guard hydraInfiltrationAfterSecond.pending == .none
#guard (hydraInfiltrationAfterSecond.player ⟨1⟩).hand.size == 5
#guard hydraInfiltrationAfterSecond.log.any (fun s => mentions s "Nissa discards")

/-- Super Speed: enchanted creature gains first strike until EOT. -/
def superSpeedFirstStrikeOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g superSpeed ⟨0⟩ ⟨0⟩
  let host := namedPermanent g "Grizzly Bears"
  let aura := namedPermanent g "Super Speed"
  let g := g.attachSourceTo aura host
  let g := g.applyTriggeredAbility ⟨0⟩
    (.onEnterEnchanted (.grantKeywords Keyword.firstStrike)) (some aura.id)
  (g.object! host.id).status.untilEotKeywords.firstStrike

#guard superSpeedFirstStrikeOk

/-- Frozen in Ice: tap enchanted creature. -/
def frozenInIceTapOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g frozenInIce ⟨0⟩ ⟨0⟩
  let host := namedPermanent g "Grizzly Bears"
  let aura := namedPermanent g "Frozen in Ice"
  let g := g.attachSourceTo aura host
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnterEnchanted .tap) (some aura.id)
  (g.object! host.id).status.tapped

#guard frozenInIceTapOk

/-- Super Suit: attach then untap the host. -/
def superSuitUntapOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let host := namedPermanent g "Grizzly Bears"
  let g := g.mapObjectStatus host (fun s => { s with tapped := true })
  let g := addPermanent g superSuit ⟨0⟩ ⟨0⟩
  let eq := namedPermanent g "Super Suit"
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnterAttachThen .untap)
    (some eq.id) #[Target.permanent host.id]
  !(g.object! host.id).status.tapped &&
    (g.object! eq.id).attachedTo == some host.id

#guard superSuitUntapOk

/-- Stolen Stark Tech: attach then grant indestructible. -/
def stolenStarkIndestructibleOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g stolenStarkTech ⟨0⟩ ⟨0⟩
  let host := namedPermanent g "Grizzly Bears"
  let eq := namedPermanent g "Stolen Stark Tech"
  let g := g.applyTriggeredAbility ⟨0⟩
    (.onEnterAttachThen (.grantKeywords Keyword.indestructible))
    (some eq.id) #[Target.permanent host.id]
  (g.object! host.id).status.untilEotKeywords.indestructible &&
    (g.object! eq.id).attachedTo == some host.id

#guard stolenStarkIndestructibleOk

/-- Doctor Doom: create two Doombots. -/
def doctorDoomDoombotsOk : Bool :=
  let g := addPermanent afterDraw doctorDoom ⟨0⟩ ⟨0⟩
  let doom := namedPermanent g "Doctor Doom"
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnterCreateTokens .doombot 2) (some doom.id)
  (g.battlefield.filter (fun o => o.name == "Doombot")).size == 2

#guard doctorDoomDoombotsOk

/-- Thor: exile an instant from the graveyard; it is playable until next turn. -/
def thorExilePlayOk : Bool :=
  let g := addPermanent afterDraw thorGodOfThunder ⟨0⟩ ⟨0⟩
  let g := addToGraveyard g lightningBolt ⟨0⟩
  let thor := namedPermanent g "Thor, God of Thunder"
  let bolt := namedGraveyardCard g ⟨0⟩ "Lightning Bolt"
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterExileGyPlayUntilNextTurn)
    (some thor.id) #[Target.card bolt.id]
  match g.objects.find? (fun o => o.zone == .exile && o.name == "Lightning Bolt") with
  | some bolt =>
    match bolt.playPermission with
    | some perm => perm.player == ⟨0⟩ && perm.turnEndsRemaining == 2
    | none => false
  | none => false

#guard thorExilePlayOk

/-- Wolverine fights another creature. Use a 4/4 so both sides survive
sequential damage (a 3/3 would die before dealing damage back). -/
def wolverineFightOk : Bool :=
  let g := addPermanent afterDraw wolverineFierceFighter ⟨0⟩ ⟨0⟩
  let g := addPermanent g rumblingBaloth ⟨1⟩ ⟨1⟩
  let w := namedPermanent g "Wolverine, Fierce Fighter"
  let baloth := namedPermanent g "Rumbling Baloth"
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterFightUpToOne)
    (some w.id) #[Target.permanent baloth.id]
  (namedPermanent g "Wolverine, Fierce Fighter").status.damage > 0 &&
    (namedPermanent g "Rumbling Baloth").status.damage > 0

#guard wolverineFightOk

/-- Justice returns a nonland nontoken. -/
def justiceBounceOk : Bool :=
  let g := addPermanent afterDraw justiceVanceAstrovik ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let j := namedPermanent g "Justice, Vance Astrovik"
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnter Effect.enterReturnNonlandNontoken)
    (some j.id) #[Target.permanent bears.id]
  !g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    (g.handObjects ⟨1⟩).any (fun o => o.name == "Grizzly Bears")

#guard justiceBounceOk

/-- S.H.I.E.L.D. Flying Car: exile until the next end step. -/
def flyingCarFlickerOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g sHIELDFlyingCar ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let car := namedPermanent g "S.H.I.E.L.D. Flying Car"
  let g := g.applyTriggeredAbility ⟨0⟩ .onEnterExileCreatureReturnEndStep
    (some car.id) #[Target.permanent bears.id]
  !g.battlefield.any (fun o => o.name == "Grizzly Bears") &&
    g.delayedEndStepReturns.size == 1

#guard flyingCarFlickerOk

/-- Giant-Sized Flying Ant: choose tap. -/
def flyingAntTapOk : Bool :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g giantSizedFlyingAnt ⟨0⟩ ⟨0⟩
  let bears := namedPermanent g "Grizzly Bears"
  let ant := namedPermanent g "Giant-Sized Flying Ant"
  let g := g.applyTriggeredAbility ⟨0⟩ .onEnterTapOrUntapNonland
    (some ant.id) #[Target.permanent bears.id]
  let g := mustApply g ⟨0⟩ (.chooseMode 0)
  (g.object! bears.id).status.tapped

#guard flyingAntTapOk

/-- Ant-Man's Army: choose Treasure. -/
def antManArmyTreasureOk : Bool :=
  let g := addPermanent afterDraw antManSArmy ⟨0⟩ ⟨0⟩
  let army := namedPermanent g "Ant-Man's Army"
  let g := g.applyTriggeredAbility ⟨0⟩ .onEnterCreateFoodOrTreasure (some army.id)
  let g := mustApply g ⟨0⟩ (.chooseMode 1)
  g.battlefield.any (fun o => o.hasSubtype "Treasure") &&
    !g.battlefield.any (fun o => o.hasSubtype "Food" && o.printed.isToken)

#guard antManArmyTreasureOk

/-- Hero in Training: draw, and gain 2 if another Hero is present. -/
def heroInTrainingLifeOk : Bool :=
  let g := addPermanent afterDraw captainAmericaSuperSoldier ⟨0⟩ ⟨0⟩
  let g := addPermanent g heroInTraining ⟨0⟩ ⟨0⟩
  let hero := namedPermanent g "Hero in Training"
  let life0 := (g.player ⟨0⟩).life
  let hand0 := (g.player ⟨0⟩).hand.size
  let g := g.applyTriggeredAbility ⟨0⟩ .onEnterDrawGainLifeIfAnotherHero (some hero.id)
  (g.player ⟨0⟩).hand.size == hand0 + 1 && (g.player ⟨0⟩).life == life0 + 2

#guard heroInTrainingLifeOk

/-- Wakandan Royal Guard: two +1/+1s on another Hero. -/
def wakandanRoyalGuardHeroOk : Bool :=
  let g := addPermanent afterDraw captainAmericaSuperSoldier ⟨0⟩ ⟨0⟩
  let g := addPermanent g wakandanRoyalGuard ⟨0⟩ ⟨0⟩
  let cap := namedPermanent g "Captain America, Super-Soldier"
  let guard := namedPermanent g "Wakandan Royal Guard"
  let before := (g.object! cap.id).status.plusOnePlusOne
  let g := g.applyTriggeredAbility ⟨0⟩ .onEnterPlusOneOrTwoIfAnotherHero
    (some guard.id) #[Target.permanent cap.id]
  (g.object! cap.id).status.plusOnePlusOne == before + 2

#guard wakandanRoyalGuardHeroOk

/-- K'un-Lun Warrior: discard, then draw. -/
def kunLunDiscardDrawOk : Bool :=
  let g := addPermanent afterDraw kUnLunWarrior ⟨0⟩ ⟨0⟩
  let w := namedPermanent g "K'un-Lun Warrior"
  let g := g.applyTriggeredAbility ⟨0⟩ .onEnterMaySacArtifactOrDiscardDraw (some w.id)
  let hand0 := (g.player ⟨0⟩).hand.size
  let disc := (g.player ⟨0⟩).hand.back!
  let g := mustApply g ⟨0⟩ (.discard disc)
  (g.player ⟨0⟩).hand.size == hand0

#guard kunLunDiscardDrawOk

/-- A single-card discard still finishes after one card. -/
def discardOneStillOne : Bool :=
  let g := afterDraw.drawThenBeginDiscard ⟨0⟩ 0
  let g := mustApply g ⟨0⟩ (.discard (g.player ⟨0⟩).hand.back!)
  g.pending == .none && (g.player ⟨0⟩).hand.size == 6

#guard discardOneStillOne

end Mtg.Engine.Tests
