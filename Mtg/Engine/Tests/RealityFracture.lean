import Mtg.Engine.Catalog.RealityFracture
import Mtg.Engine.Game
import Mtg.Engine.Tests.Auras
import Mtg.Engine.Tests.Helpers

/-!
# Reality Fracture

Empower Jace creates one planeswalker token and stacks loyalty on it.
A prepare creature enters prepared and unprepares when its spell is cast.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

def empoweredJace : Game :=
  started.empowerJace ⟨0⟩ 2

#guard empoweredJace.battlefield.any (fun o =>
  o.name == "Jace" && o.printed.isToken && o.printed.isPlaneswalker &&
    o.status.loyaltyCounters == 2)

def empoweredJaceAgain : Game :=
  empoweredJace.empowerJace ⟨0⟩ 3

#guard (empoweredJaceAgain.battlefield.filter (fun o => o.name == "Jace")).size == 1
#guard (namedPermanent empoweredJaceAgain "Jace").status.loyaltyCounters == 5

/-- Put the angel on the battlefield and run enters-the-battlefield actions. -/
def preparedAngel : Game :=
  let g := skipTo (addPermanent started grayOgre ⟨0⟩ ⟨0⟩) .precombatMain 40
  let (g, obj) := g.allocObject blossomBlessedAngel ⟨0⟩ .battlefield (some ⟨0⟩)
    (status := { summoningSick := false })
  g.afterPermanentEnters obj

#guard (namedPermanent preparedAngel "Blossom-Blessed Angel").status.prepared
#guard preparedAngel.objects.any (fun o =>
  o.zone == .exile && o.name == "Seed Suture" &&
    o.playPermission.any (·.prepareSource.isSome))

def seedSutureCopy (g : Game) : GameObject :=
  match g.objects.find? (fun o => o.zone == .exile && o.name == "Seed Suture") with
  | some o => o
  | none => panic! "expected an exiled Seed Suture"

def proposedSeedSuture : Game :=
  let g := withWhiteMana preparedAngel ⟨0⟩ 2
  mustApply g ⟨0⟩ (.cast (seedSutureCopy g).id)

#guard !(namedPermanent proposedSeedSuture "Blossom-Blessed Angel").status.prepared
#guard proposedSeedSuture.pending == .chooseTargets ⟨0⟩

def targetedSeedSuture : Game :=
  let angel := namedPermanent proposedSeedSuture "Blossom-Blessed Angel"
  mustApply proposedSeedSuture ⟨0⟩ (.target (.permanent angel.id))

#guard targetedSeedSuture.pending == .activateManaAbilities ⟨0⟩

def paidSeedSuture : Game :=
  mustApply targetedSeedSuture ⟨0⟩ .pay

#guard paidSeedSuture.stack.size == 1
#guard paidSeedSuture.log.any (fun s => mentions s "Seed Suture")

/-- Seed Suture puts a +1/+1 counter on the Angel and gains 1 life. The
copy of the prepare spell then ceases to exist instead of going to a
graveyard. -/
def resolvedSeedSuture : Game := passBoth paidSeedSuture

#guard (namedPermanent resolvedSeedSuture "Blossom-Blessed Angel").status.plusOnePlusOne == 1
#guard (resolvedSeedSuture.player ⟨0⟩).life == (paidSeedSuture.player ⟨0⟩).life + 1
#guard !resolvedSeedSuture.objects.any (fun o => o.name == "Seed Suture")
#guard karnGildedGuardian.manaCost.manaValue == 10

end Mtg.Engine.Tests
