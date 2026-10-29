import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Fixture
import Mtg.Engine.Game
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns

/-!
# Resource triggers without `ResourceLeftover`

Each leftover draw, discard, life, and +1/+1-counter effect resolves as the
constructors that effect uses. `ResourceLeftover` stays the printed sentence.
-/

namespace Mtg.Engine.ResourceTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

def me : PlayerId := ⟨0⟩
def opp : PlayerId := ⟨1⟩

def resolve (g : Game) (ab : TriggeredAbility) (sourceId : Option ObjectId := none)
    (targets : Array Target := #[]) (lastKnownPower : Option Int := none) : Game :=
  g.applyTriggeredAbility me ab sourceId targets (lastKnownPower := lastKnownPower)

def named (g : Game) (name : String) : GameObject :=
  namedPermanent g name

def tokensNamed (g : Game) (name : String) : Nat :=
  (g.battlefield.filter fun o => o.printed.isToken && o.name == name).size

def resource (e : Effect) : TriggeredAbility :=
  TriggeredAbility.onResource e

/- The shared resource effects resolve as constructors that do not carry
`ResourceLeftover`. The printed sentence stays the Oracle line. -/
#guard TriggeredAbility.resolution (resource Effect.resourceDiscardExilePlay) ==
  .may (.exile .discarded .playUntilNextTurn) (.sequence []) .ifYouDo
#guard TriggeredAbility.resolution (resource Effect.resourceDrawIfAnotherHeroDamage) ==
  .«if» (.atLeast (.count (.othersOfSubtype .hero)) (.fixed 1)) (.dealDamage (.fixed 1) (.player (.target .opponent)))
#guard TriggeredAbility.resolution (resource Effect.resourceSecondDrawBecome66) ==
  .sequence [.setBasePT (.fixed 6) (.fixed 6) .source, .grant (.keywords Keyword.trample) .source]
#guard TriggeredAbility.resolution (resource Effect.resourceSecondDrawPlusOneTarget) ==
  .putCounters (.ofKind .plusOnePlusOne) .permanent
#guard TriggeredAbility.resolution (resource Effect.resourceSecondDrawDrain) ==
  .sequence [.loseLife (.fixed 1) .eachOpponent, .gainLife (.fixed 1)]
#guard TriggeredAbility.resolution (resource Effect.resourceGainLifePlusOnes) ==
  .putCounters (.ofKind .plusOnePlusOne) .eachUpToLastKnown
#guard TriggeredAbility.resolution (resource Effect.resourcePlusOneCreateInsectOnce) ==
  .createTokens .insect11green (.fixed 1) false
#guard TriggeredAbility.resolution (resource Effect.resourcePlusOneOnThisOnce) ==
  .putCounters (.ofKind .plusOnePlusOne) .source
#guard TriggeredAbility.resolution (resource Effect.resourcePlusOneOnHeroesCreateWall) ==
  .may (.createTokens .wall04defender (.fixed 1) false) (.sequence []) .ifYouDo

#guard (SharedTrigger.timing (.resource .plusOneCreateInsectOnce)).onceEachTurn
#guard (SharedTrigger.timing (.resource .plusOneOnThisOnce)).onceEachTurn
#guard (SharedTrigger.timing (.resource .gainLifePlusOnes)).allowsZeroTargets
#guard (SharedTrigger.timing (.resource .drawIfAnotherHeroDamage)).targeting.kind ==
  .opponent
#guard (SharedTrigger.timing (.resource .secondDrawPlusOneTarget)).targeting.kind ==
  .creature
#guard (SharedTrigger.timing (.resource .gainLifePlusOnes)).targeting.kind ==
  .creatureYouControl

#guard toString (resource Effect.resourceDiscardExilePlay) ==
  TriggeredAbility.resourceSentence .discardExilePlay
#guard toString (resource Effect.resourceDrawIfAnotherHeroDamage) ==
  TriggeredAbility.resourceSentence .drawIfAnotherHeroDamage
#guard toString (resource Effect.resourceSecondDrawBecome66) ==
  TriggeredAbility.resourceSentence .secondDrawBecome66
#guard toString (resource Effect.resourceSecondDrawPlusOneTarget) ==
  TriggeredAbility.resourceSentence .secondDrawPlusOneTarget
#guard toString (resource Effect.resourceSecondDrawDrain) ==
  TriggeredAbility.resourceSentence .secondDrawDrain
#guard toString (resource Effect.resourceGainLifePlusOnes) ==
  TriggeredAbility.resourceSentence .gainLifePlusOnes
#guard toString (resource Effect.resourcePlusOneCreateInsectOnce) ==
  TriggeredAbility.resourceSentence .plusOneCreateInsectOnce
#guard toString (resource Effect.resourcePlusOneOnThisOnce) ==
  TriggeredAbility.resourceSentence .plusOneOnThisOnce
#guard toString (resource Effect.resourcePlusOneOnHeroesCreateWall) ==
  TriggeredAbility.resourceSentence .plusOneOnHeroesCreateWall

/- Moonstone may exile the discarded card. Declining leaves it in the graveyard. -/
def moonstoneBoard : Game :=
  let g := addPermanent afterDraw moonstoneHarshMistress me me
  addToGraveyard g lightningBolt me

def moonstoneOffer : Game :=
  let bolt := namedGraveyardCard moonstoneBoard me "Lightning Bolt"
  resolve moonstoneBoard (resource Effect.resourceDiscardExilePlay)
    none #[] (some (Int.ofNat bolt.id.raw))

def moonstoneKept : Game :=
  mustApply moonstoneOffer me .decline

def moonstoneExiled : Game :=
  mustApply moonstoneOffer me .accept

def moonstoneMissing : Game :=
  resolve moonstoneBoard (resource Effect.resourceDiscardExilePlay)

def moonstoneLeft : Game :=
  let g := addPermanent afterDraw grizzlyBears me me
  let bears := named g "Grizzly Bears"
  resolve g (resource Effect.resourceDiscardExilePlay) none #[]
    (some (Int.ofNat bears.id.raw))

#guard
  match moonstoneOffer.pending with
  | .fraChoice _ (.moonstoneMayExile _) =>
    logContains moonstoneOffer "You may exile Lightning Bolt"
  | _ => false
#guard moonstoneKept.objects.any (fun o =>
  o.name == "Lightning Bolt" && o.zone == .graveyard me)
#guard moonstoneExiled.objects.any (fun o =>
  o.name == "Lightning Bolt" && o.zone == .exile &&
    moonstoneExiled.playPermissionDuration o == some (.untilEndOfNextTurnOf me))
#guard logContains moonstoneMissing "No discarded card is in the graveyard"
#guard logContains moonstoneLeft "no longer in your graveyard"

/- Human Torch deals 1 damage only while another Hero is in play. -/
def torchBoard : Game :=
  addPermanent afterDraw humanTorchJohnnyStorm me me

def torchAlone : Game :=
  let torch := named torchBoard "Human Torch, Johnny Storm"
  resolve torchBoard (resource Effect.resourceDrawIfAnotherHeroDamage)
    (some torch.id) #[Target.player opp]

def torchHeroBoard : Game :=
  addPermanent torchBoard colleenWingStreetSamurai me me

def torchHero : Game :=
  let torch := named torchHeroBoard "Human Torch, Johnny Storm"
  resolve torchHeroBoard (resource Effect.resourceDrawIfAnotherHeroDamage)
    (some torch.id) #[Target.player opp]

#guard (torchAlone.player opp).life == (torchBoard.player opp).life
#guard logContains torchAlone "Human Torch's ability has no effect"
#guard (torchHero.player opp).life == (torchHeroBoard.player opp).life - 1

/- Moon Girl becomes 6/6 with trample. A prior set-P/T is overwritten;
pumps and counters still apply. A missing source changes nothing. -/
def moonBoard : Game :=
  addPermanent afterDraw moonGirlAndDevilDinosaur me me

def moonGirl : Game :=
  let src := named moonBoard "Moon Girl and Devil Dinosaur"
  resolve moonBoard (resource Effect.resourceSecondDrawBecome66) (some src.id)

def moonOverwrite : Game :=
  let src := named moonBoard "Moon Girl and Devil Dinosaur"
  let g := (moonBoard.createEffect (.setBasePTUntilEot src.id (1, 1))).createEffect (.pump src.id 1 1)
  let g := g.addPlusOnePlusOneTo (named g "Moon Girl and Devil Dinosaur") 1
  resolve g (resource Effect.resourceSecondDrawBecome66)
    (some (named g "Moon Girl and Devil Dinosaur").id)

def moonMissing : Game :=
  resolve afterDraw (resource Effect.resourceSecondDrawBecome66)

#guard
  let mg := named moonGirl "Moon Girl and Devil Dinosaur"
  moonGirl.power mg == 6 && moonGirl.toughness mg == 6 && moonGirl.hasTrample mg
#guard
  let mg := named moonOverwrite "Moon Girl and Devil Dinosaur"
  moonOverwrite.power mg == 8 && moonOverwrite.toughness mg == 8 &&
    moonOverwrite.hasTrample mg
#guard logContains moonMissing "no longer in play"

/- A +1/+1 counter on the announced creature. A land is not a creature. -/
def roxxonBoard : Game :=
  let g := addPermanent afterDraw roxxonBrutes me me
  let g := addPermanent g grizzlyBears me me
  addPermanent g mountain opp opp

def roxxonCounter : Game :=
  let bears := named roxxonBoard "Grizzly Bears"
  resolve roxxonBoard (resource Effect.resourceSecondDrawPlusOneTarget)
    (some (named roxxonBoard "Roxxon Brutes").id) #[Target.permanent bears.id]

def roxxonLand : Game :=
  let land := named roxxonBoard "Mountain"
  resolve roxxonBoard (resource Effect.resourceSecondDrawPlusOneTarget)
    (some (named roxxonBoard "Roxxon Brutes").id) #[Target.permanent land.id]

#guard (named roxxonCounter "Grizzly Bears").status.plusOnePlusOne == 1
#guard (named roxxonLand "Mountain").status.plusOnePlusOne == 0
#guard logContains roxxonLand "no longer legal"

/- Each opponent loses 1 life and you gain 1 life. -/
def kangDrain : Game :=
  resolve afterDraw (resource Effect.resourceSecondDrawDrain)

#guard (kangDrain.player me).life == (afterDraw.player me).life + 1
#guard (kangDrain.player opp).life == (afterDraw.player opp).life - 1

/- Heroic Feast puts a counter on up to as many creatures you control as
the life gained. An opponent's creature, and targets past that count, are
skipped. Zero life and no targets put nothing. -/
def feastBoard : Game :=
  let g := addPermanent afterDraw heroicFeast me me
  let g := addPermanent g grizzlyBears me me
  let g := addPermanent g hillGiant me me
  addPermanent g grizzlyBears opp opp

def feastOne : Game :=
  let bears := named feastBoard "Grizzly Bears"
  let giant := named feastBoard "Hill Giant"
  resolve feastBoard (resource Effect.resourceGainLifePlusOnes)
    (some (named feastBoard "Heroic Feast").id)
    #[Target.permanent bears.id, Target.permanent giant.id] (some 1)

def feastBoth : Game :=
  let bears := named feastBoard "Grizzly Bears"
  let giant := named feastBoard "Hill Giant"
  resolve feastBoard (resource Effect.resourceGainLifePlusOnes)
    (some (named feastBoard "Heroic Feast").id)
    #[Target.permanent bears.id, Target.permanent giant.id] (some 2)

def feastOpp : Game :=
  let theirs :=
    (feastBoard.battlefield.filter fun o =>
      o.name == "Grizzly Bears" && o.controller == some opp)[0]!
  let mine := named feastBoard "Hill Giant"
  resolve feastBoard (resource Effect.resourceGainLifePlusOnes)
    (some (named feastBoard "Heroic Feast").id)
    #[Target.permanent theirs.id, Target.permanent mine.id] (some 1)

def feastZero : Game :=
  let bears := named feastBoard "Grizzly Bears"
  resolve feastBoard (resource Effect.resourceGainLifePlusOnes)
    (some (named feastBoard "Heroic Feast").id)
    #[Target.permanent bears.id] (some 0)

def feastNone : Game :=
  resolve feastBoard (resource Effect.resourceGainLifePlusOnes)
    (some (named feastBoard "Heroic Feast").id) #[] (some 3)

#guard (named feastOne "Grizzly Bears").status.plusOnePlusOne == 1
#guard (named feastOne "Hill Giant").status.plusOnePlusOne == 0
#guard (named feastBoth "Grizzly Bears").status.plusOnePlusOne == 1
#guard (named feastBoth "Hill Giant").status.plusOnePlusOne == 1
#guard
  let theirs :=
    (feastOpp.battlefield.filter fun o =>
      o.name == "Grizzly Bears" && o.controller == some opp)[0]!
  theirs.status.plusOnePlusOne == 0 &&
    (named feastOpp "Hill Giant").status.plusOnePlusOne == 0 &&
    logContains feastOpp "no longer legal"
#guard (named feastZero "Grizzly Bears").status.plusOnePlusOne == 0
#guard (named feastNone "Grizzly Bears").status.plusOnePlusOne == 0
#guard (named feastNone "Hill Giant").status.plusOnePlusOne == 0

/- Putting a +1/+1 counter creates one Insect. -/
def antManBoard : Game :=
  addPermanent afterDraw antManColonyCommander me me

def antManInsect : Game :=
  let src := named antManBoard "Ant-Man, Colony Commander"
  resolve antManBoard (resource Effect.resourcePlusOneCreateInsectOnce) (some src.id)

#guard
  let tok := named antManInsect "Insect"
  tokensNamed antManInsect "Insect" == 1 &&
    antManInsect.power tok == 1 && antManInsect.toughness tok == 1

/- A counter on another creature puts one on the source. A missing source
puts nothing. -/
def knightBoard : Game :=
  addPermanent afterDraw knightOfWundagore me me

def knightCounter : Game :=
  let src := named knightBoard "Knight of Wundagore"
  resolve knightBoard (resource Effect.resourcePlusOneOnThisOnce) (some src.id)

def knightMissing : Game :=
  resolve afterDraw (resource Effect.resourcePlusOneOnThisOnce)

#guard (named knightCounter "Knight of Wundagore").status.plusOnePlusOne == 1
#guard logContains knightMissing "no longer in play"

/- Invisible Woman may create a 0/4 Wall with defender. Declining creates none. -/
def sueBoard : Game :=
  addPermanent afterDraw invisibleWomanSueStorm me me

def sueOffer : Game :=
  let src := named sueBoard "Invisible Woman, Sue Storm"
  resolve sueBoard (resource Effect.resourcePlusOneOnHeroesCreateWall) (some src.id)

def sueDeclined : Game :=
  mustApply sueOffer me .decline

def sueWall : Game :=
  mustApply sueOffer me .accept

#guard
  match sueOffer.pending with
  | .fraChoice _ (.mayCreateTokens .wall04defender 1) =>
    logContains sueOffer "may create a 0/4 Wall"
  | _ => false
#guard tokensNamed sueDeclined "Wall" == 0
#guard
  let tok := named sueWall "Wall"
  tokensNamed sueWall "Wall" == 1 &&
    sueWall.power tok == 0 && sueWall.toughness tok == 4 &&
    sueWall.hasKeyword tok (·.defender)

end Mtg.Engine.ResourceTests
