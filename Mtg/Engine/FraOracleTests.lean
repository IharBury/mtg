import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.RealityFracture
import Mtg.Engine.Game
import Mtg.Engine.OracleData
import Mtg.Engine.Tests.Auras
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.RealityFracture
import Mtg.Engine.Tests.Turns

/-!
# Engine behavior for Reality Fracture (FRA) judge rulings

These tests check Gatherer / Scryfall `wotc` comments on FRA cards —
rulings issued by judges — not the rules text printed on the cards. Each
check is tagged with the ruling id from `uniqueOracleRulings`.

This module covers planeswalker loyalty, Empower Jace, and prepare.
`Mtg.Engine.FraOracleTests2` covers card-specific rulings, and
`Mtg.Engine.FraOracleTests3` inventories every FRA ruling.
-/

namespace Mtg.Engine.FraRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

/-- Look up a unique judge ruling by 1-based id in `uniqueOracleRulings`. -/
def fraRuling (id : Nat) : OracleRuling :=
  uniqueOracleRulings[id - 1]!

#guard uniqueFraOracleRulingCount == 178
#guard uniqueFraOracleRulings.all (fun r => (fraRuling r.id).id == r.id)

/-- Put `card` onto the battlefield under `p`'s control as if it entered,
so it gets loyalty counters and enters prepared. -/
def enterPermanent (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  let (g, obj) := g.allocObject card p .battlefield (some p)
    (status := { summoningSick := false })
  g.afterPermanentEnters obj

/-- The first Jace planeswalker token `p` controls. -/
def jaceTokenOf (g : Game) (p : PlayerId := ⟨0⟩) : GameObject :=
  match (g.jacePlaneswalkerTokens p)[0]? with
  | some o => o
  | none => panic! "expected a Jace planeswalker token"

/-- True when applying `a` is rejected and the error mentions `needle`. -/
def rejects (g : Game) (p : PlayerId) (a : Action) (needle : String) : Bool :=
  match g.apply p a with
  | .error e => mentions e needle
  | .ok _ => false

/-- True when `name` has a copy in exile that may be cast. -/
def exiledCopies (g : Game) (name : String) : Array GameObject :=
  g.objects.filter (fun o => o.zone == .exile && o.name == name)

/-!
## Planeswalker loyalty (CR 306.5b / 606 / 704.5i / 120.3c)
-/

/-- A planeswalker enters with its printed loyalty, and damage dealt to it
removes loyalty counters. -/
def sculptorEntered : Game := enterPermanent afterDraw jaceRealitySculptor ⟨0⟩

#guard (namedPermanent sculptorEntered "Jace, Reality Sculptor").status.loyaltyCounters == 5
#guard
  let g := sculptorEntered.dealDamageToPermanent
    (namedPermanent sculptorEntered "Jace, Reality Sculptor") 3
  (namedPermanent g "Jace, Reality Sculptor").status.loyaltyCounters == 2

/-- A planeswalker with no loyalty counters is put into its owner's
graveyard as a state-based action. -/
def jaceAtZero : Game := afterDraw.empowerJace ⟨0⟩ 0

#guard (jaceAtZero.jacePlaneswalkerTokens ⟨0⟩).size == 1
#guard (jaceAtZero.checkSBA.jacePlaneswalkerTokens ⟨0⟩).isEmpty

/-- Ruling 778: with Sanctum Lurker, a planeswalker with 0 loyalty stays. It
still can't pay a loyalty cost that removes counters. -/
def jaceAtZeroWithLurker : Game :=
  (addPermanent jaceAtZero sanctumLurker ⟨0⟩ ⟨0⟩).checkSBA

#guard (jaceAtZeroWithLurker.jacePlaneswalkerTokens ⟨0⟩).size == 1
#guard rejects jaceAtZeroWithLurker ⟨0⟩ (.activate (jaceTokenOf jaceAtZeroWithLurker).id 0)
  "loyalty counters to remove"
#guard (fraRuling 778).comment.contains "it will not be put into its owner's graveyard"

/-- Ruling 732: the Jace token has 0 printed loyalty, “[−1]: Surveil 1,” and
“[−3]: Draw a card.” Empower Jace 5 then puts five counters on it. -/
def jaceFive : Game := afterDraw.empowerJace ⟨0⟩ 5

#guard Game.jacePlaneswalkerToken.loyalty == some 0
#guard Game.jacePlaneswalkerToken.isToken && Game.jacePlaneswalkerToken.isPlaneswalker
#guard Game.jacePlaneswalkerToken.colors == ColorSet.singleton .blue
#guard Game.jacePlaneswalkerToken.activatedAbilities.map (·.cost.loyalty) ==
  #[some (.minus 1), some (.minus 3)]
#guard Game.jacePlaneswalkerToken.activatedAbilities.map (·.effect.resolution) ==
  #[.surveil 1, .draw 1]
#guard (jaceTokenOf jaceFive).status.loyaltyCounters == 5
#guard (fraRuling 732).comment.contains "create a blue Jace planeswalker token with 0 loyalty"

/-- Activating [−1] removes a loyalty counter as its cost (CR 606.4). The
library's top card is known so the surveil is visible. -/
def jaceMinusOne : Game :=
  let g := addToLibraryTop jaceFive grizzlyBears ⟨0⟩
  mustApply g ⟨0⟩ (.activate (jaceTokenOf g).id 0)

#guard (jaceTokenOf jaceMinusOne).status.loyaltyCounters == 4
#guard (jaceTokenOf jaceMinusOne).status.loyaltyActivatedThisTurn
#guard jaceMinusOne.stack.size == 1

/-- Surveil 1 looks at the top card; a card not kept on top goes to the
graveyard (CR 701.25). -/
def jaceSurveilling : Game := passBoth jaceMinusOne

#guard jaceSurveilling.pending == .scry ⟨0⟩ 1 && jaceSurveilling.surveilling

def jaceSurveilledToGraveyard : Game :=
  let top := jaceSurveilling.scryLookedIds ⟨0⟩ 1
  mustApply jaceSurveilling ⟨0⟩ (.scry #[] top)

#guard (jaceSurveilledToGraveyard.player ⟨0⟩).graveyard.any (fun id =>
  (jaceSurveilledToGraveyard.object! id).name == "Grizzly Bears")
#guard !jaceSurveilledToGraveyard.surveilling

/- Ruling 779: only one loyalty ability of each planeswalker per turn
(CR 606.3). -/
#guard rejects jaceSurveilledToGraveyard ⟨0⟩
  (.activate (jaceTokenOf jaceSurveilledToGraveyard).id 0) "already been activated"
#guard (fraRuling 779).comment.contains "Only one loyalty ability of each planeswalker"

/- The once-per-turn limit resets as the next turn begins. -/
#guard
  let g := skipTo (passBoth (skipTo jaceSurveilledToGraveyard .end 80)) .upkeep 80
  !(jaceTokenOf g).status.loyaltyActivatedThisTurn

/-- Loyalty abilities are activated only as a sorcery (CR 606.3). -/
def jaceAtCombat : Game := skipTo jaceFive .beginningOfCombat 80

#guard rejects jaceAtCombat ⟨0⟩ (.activate (jaceTokenOf jaceAtCombat).id 0) "only as a sorcery"

/-- Ruling 766: Jace's Machinations lets you activate loyalty abilities of
your Jace planeswalkers at instant speed this turn, but each is still limited
to one per turn. Empower Jace 8 creates the token. -/
def machinationsResolved : Game :=
  let g := withBlueMana (addToHand afterDraw jacesMachinations ⟨0⟩) ⟨0⟩ 3
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Jace's Machinations").id)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard (machinationsResolved.player ⟨0⟩).jaceLoyaltyAtInstantSpeed
#guard (jaceTokenOf machinationsResolved).status.loyaltyCounters == 8

def machinationsAtCombat : Game := skipTo machinationsResolved .beginningOfCombat 80

def machinationsActivated : Game :=
  mustApply machinationsAtCombat ⟨0⟩ (.activate (jaceTokenOf machinationsAtCombat).id 1)

#guard (jaceTokenOf machinationsActivated).status.loyaltyCounters == 5
#guard rejects machinationsActivated ⟨0⟩
  (.activate (jaceTokenOf machinationsActivated).id 0) "already been activated"
#guard (fraRuling 766).comment.contains "only one loyalty ability of each permanent"

/- The instant-speed permission ends with the turn. -/
#guard
  let g := passBoth (skipTo machinationsActivated .end 80)
  !(g.player ⟨0⟩).jaceLoyaltyAtInstantSpeed

/- Rulings 856 / 862: a loyalty ability that adds mana is still not a mana
ability (CR 605.1a), so it uses the stack and follows loyalty timing. -/
#guard
  let ab : ActivatedAbility :=
    { cost := { loyalty := some (.plus 1) }
      effect := { resolution := .addMana #[.colored .red], phrase := "Add {R}" } }
  !Game.isManaActivation ab
#guard (fraRuling 856).comment.contains "Loyalty abilities can't be mana abilities"
#guard (fraRuling 862).comment.contains "Loyalty abilities can't be mana abilities"

/-!
## Empower Jace (rulings 731–734)
-/

/-- Ruling 731: while you control a Jace planeswalker token, empower Jace
puts counters on it instead of creating another. -/
def empoweredTwice : Game := (afterDraw.empowerJace ⟨0⟩ 2).empowerJace ⟨0⟩ 3

#guard (empoweredTwice.jacePlaneswalkerTokens ⟨0⟩).size == 1
#guard (jaceTokenOf empoweredTwice).status.loyaltyCounters == 5

/-- Ruling 731: with several Jace tokens, you choose which one gets the
counters. -/
def twoJaceTokens : Game :=
  let (g, _) := afterDraw.createToken ⟨0⟩ Game.jacePlaneswalkerToken
  let (g, _) := g.createToken ⟨0⟩ Game.jacePlaneswalkerToken
  g

def empowerChosenJace : Game :=
  let first := (twoJaceTokens.jacePlaneswalkerTokens ⟨0⟩)[0]!
  twoJaceTokens.empowerJace ⟨0⟩ 2 (chosen := some first.id)

#guard (empowerChosenJace.jacePlaneswalkerTokens ⟨0⟩).size == 2
#guard (empowerChosenJace.jacePlaneswalkerTokens ⟨0⟩).map (·.status.loyaltyCounters) == #[2, 0]
#guard (fraRuling 731).comment.contains "you'll choose one of those tokens"

/-- Ruling 733: a nontoken Jace planeswalker doesn't receive the counters;
Empower Jace creates a token instead. -/
def empowerWithSculptor : Game := sculptorEntered.empowerJace ⟨0⟩ 2

#guard (namedPermanent empowerWithSculptor "Jace, Reality Sculptor").status.loyaltyCounters == 5
#guard (jaceTokenOf empowerWithSculptor).name == "Jace"
#guard (jaceTokenOf empowerWithSculptor).status.loyaltyCounters == 2

/-- Ruling 733: a token copy of a Jace planeswalker is a Jace planeswalker
token, so it gets the counters and no new token is created. -/
def empowerTokenCopy : Game :=
  let (g, _) := afterDraw.createToken ⟨0⟩ jaceRealitySculptor
  g.empowerJace ⟨0⟩ 3

#guard (empowerTokenCopy.jacePlaneswalkerTokens ⟨0⟩).size == 1
#guard (jaceTokenOf empowerTokenCopy).name == "Jace, Reality Sculptor"
#guard (jaceTokenOf empowerTokenCopy).status.loyaltyCounters == 3
#guard (fraRuling 733).comment.contains "nontoken Jace planeswalkers"

/-- Ruling 734: Academic Ascent targets a creature. If that target is
illegal as it resolves, the spell doesn't resolve and Jace isn't empowered. -/
def ascentCast : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := withWhiteMana (addToHand g academicAscent ⟨0⟩) ⟨0⟩ 2
  let g := proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Academic Ascent").id
    (.permanent (namedPermanent g "Grizzly Bears").id)
  mustApply g ⟨0⟩ .pay

def ascentResolved : Game := passBoth ascentCast

#guard (jaceTokenOf ascentResolved).status.loyaltyCounters == 2
#guard ascentResolved.power (namedPermanent ascentResolved "Grizzly Bears") == 4
#guard ascentResolved.hasFlying (namedPermanent ascentResolved "Grizzly Bears")

def ascentFizzled : Game :=
  let bears := namedPermanent ascentCast "Grizzly Bears"
  let (g, _) := ascentCast.move bears.id (.graveyard ⟨0⟩) none
  passBoth g

#guard (ascentFizzled.jacePlaneswalkerTokens ⟨0⟩).isEmpty
#guard ascentFizzled.log.any (fun s => mentions s "doesn't resolve")
#guard (fraRuling 734).comment.contains "You won't empower Jace"

/- Empower Jace also appears as an enters trigger (Mindseeker Oculus) and
an activated ability (Theorist's Sanctum). -/
#guard mindseekerOculus.triggeredAbilities.map toString ==
  #["When this permanent enters, empower Jace 4."]
#guard theoristsSanctum.activatedAbilities.map (·.effect.resolution) == #[.empowerJace 2]

def oculusEntered : Game := (enterPermanent afterDraw mindseekerOculus ⟨0⟩).receivePriority ⟨0⟩

#guard
  let g := passBoth oculusEntered
  (jaceTokenOf g).status.loyaltyCounters == 4

/-!
## Prepare (rulings 735–749)
-/

/-- Ruling 735: a preparation card is cast only as its creature; it has no
Adventure to cast from hand. -/
def angelInHand : Game :=
  withWhiteMana (addToHand afterDraw blossomBlessedAngel ⟨0⟩) ⟨0⟩ 4

#guard blossomBlessedAngel.adventure.isNone && blossomBlessedAngel.prepareFace.isSome
#guard rejects angelInHand ⟨0⟩
  (.castAdventure (handCardNamed angelInHand ⟨0⟩ "Blossom-Blessed Angel").id) "no Adventure"
#guard
  let g := mustApply angelInHand ⟨0⟩ (.cast (handCardNamed angelInHand ⟨0⟩ "Blossom-Blessed Angel").id)
  (g.object! g.stack.back!.objectId).printed.isCreature
#guard (fraRuling 735).comment.contains "only with their base characteristics"

/- Ruling 736: the copy of a prepare spell in exile doesn't cease to exist
when state-based actions are checked. -/
#guard (exiledCopies preparedAngel.checkSBA "Seed Suture").size == 1
#guard (fraRuling 736).comment.contains "this does not apply to copies of prepare spells"

/-- Ruling 737: unpreparing removes the copy; unpreparing an unprepared
creature does nothing. -/
def angelUnprepared : Game :=
  preparedAngel.unprepare (namedPermanent preparedAngel "Blossom-Blessed Angel")

#guard !(namedPermanent angelUnprepared "Blossom-Blessed Angel").status.prepared
#guard (exiledCopies angelUnprepared "Seed Suture").isEmpty
#guard
  let g := angelUnprepared.unprepare (namedPermanent angelUnprepared "Blossom-Blessed Angel")
  g.objects.size == angelUnprepared.objects.size && g.log.size == angelUnprepared.log.size
#guard (fraRuling 737).comment.contains "associated copy of its prepare spell in exile ceases to exist"

/-- Ruling 738: a preparation card is a creature card in every zone. In a
graveyard, Diviner of Victory is a blue creature card with mana value 1. -/
def divinerInGraveyard : GameObject :=
  let g := addToGraveyard afterDraw divinerOfVictory ⟨0⟩
  match g.objects.find? (fun o => o.name == "Diviner of Victory") with
  | some o => o
  | none => panic! "expected Diviner of Victory"

#guard divinerInGraveyard.printed.isCreature
#guard !divinerInGraveyard.printed.isInstantOrSorcery
#guard afterDraw.objectManaValue divinerInGraveyard == 1
#guard divinerInGraveyard.printed.colors == ColorSet.singleton .blue
#guard (fraRuling 738).comment.contains "creature card in every zone"

/-- Ruling 739: being prepared isn't copied. A token copy of the prepared
Angel isn't prepared but has the prepare spell, so it can become prepared. -/
def angelTokenCopy : Game × GameObject :=
  preparedAngel.createToken ⟨0⟩ (namedPermanent preparedAngel "Blossom-Blessed Angel").printed

#guard !angelTokenCopy.2.status.prepared
#guard angelTokenCopy.2.printed.prepareFace.isSome
#guard
  let (g, tok) := angelTokenCopy
  let g := g.becomePrepared tok
  (g.object! tok.id).status.prepared && (exiledCopies g "Seed Suture").size == 2
#guard (fraRuling 739).comment.contains "Being prepared isn't a copiable value"

/-- Ruling 740: a prepared creature that stops being a creature stays
prepared, and its controller may still cast the copy. -/
def angelNoLongerCreature : Game :=
  let o := namedPermanent preparedAngel "Blossom-Blessed Angel"
  preparedAngel.setObject { o with status := { o.status with returnedAsArtifact := true } }

#guard !(namedPermanent angelNoLongerCreature "Blossom-Blessed Angel").isCreature
#guard (namedPermanent angelNoLongerCreature "Blossom-Blessed Angel").status.prepared
#guard angelNoLongerCreature.mayPlayFromExile ⟨0⟩ (seedSutureCopy angelNoLongerCreature)
#guard (fraRuling 740).comment.contains "it will still be prepared"

/-- Ruling 741: the exiled copy is made from the printed prepare spell, so
copy exceptions on the creature don't change it. A 1/1 green Frog copy of
the Angel still exiles a sorcery Seed Suture with no power or toughness. -/
def frogAngel : Game :=
  let frog := { blossomBlessedAngel with
    subtypes := #["Frog"], power := some 1, toughness := some 1,
    colorIndicator := some (ColorSet.singleton .green) }
  let (g, tok) := afterDraw.createToken ⟨0⟩ frog
  g.becomePrepared tok

#guard (exiledCopies frogAngel "Seed Suture").size == 1
#guard (exiledCopies frogAngel "Seed Suture").all (fun c =>
  c.printed.isSorcery && !c.printed.isCreature && c.printed.power.isNone &&
    !c.printed.hasSubtype "Frog")
#guard (fraRuling 741).comment.contains "ignores copy exceptions"

/- Ruling 742: the copy stays only while its permanent is on the
battlefield and prepared. -/
#guard
  let o := namedPermanent preparedAngel "Blossom-Blessed Angel"
  let (g, _) := preparedAngel.move o.id (.graveyard ⟨0⟩) none
  (exiledCopies g "Seed Suture").isEmpty
#guard (fraRuling 742).comment.contains "That copy remains in exile"

/- Ruling 743: a prepared creature can't become prepared again. -/
#guard
  let g := preparedAngel.becomePrepared (namedPermanent preparedAngel "Blossom-Blessed Angel")
  (exiledCopies g "Seed Suture").size == 1 && g.log.any (fun s => mentions s "already prepared")

/-- Ruling 743: Bloodline Recollector's end-step trigger doesn't prepare it
twice; with fewer than three deaths it does nothing. -/
def recollectorTrigger : TriggeredAbility := bloodlineRecollector.triggeredAbilities[0]!

def recollectorWithDeaths (prepared : Bool) (deaths : Nat) : Game :=
  let g := enterPermanent afterDraw bloodlineRecollector ⟨0⟩
  let o := namedPermanent g "Bloodline Recollector"
  let g := if prepared then g.becomePrepared o else g
  let g := { g with battlefieldCreaturesToGyThisTurn := (List.replicate deaths o.id).toArray }
  g.applyTriggeredAbility ⟨0⟩ recollectorTrigger (some o.id)

#guard (exiledCopies (recollectorWithDeaths true 3) "Ancestral Craving").size == 1
#guard (namedPermanent (recollectorWithDeaths false 3) "Bloodline Recollector").status.prepared
#guard !(namedPermanent (recollectorWithDeaths false 2) "Bloodline Recollector").status.prepared
#guard (fraRuling 743).comment.contains "won't cause it to become prepared a second time"

/- Upkeep triggers prepare a creature only if it isn't already prepared. -/
#guard
  let g := enterPermanent afterDraw paradoxShaper ⟨0⟩
  let o := namedPermanent g "Paradox Shaper"
  let g := g.applyTriggeredAbility ⟨0⟩ paradoxShaper.triggeredAbilities[0]! (some o.id)
  (namedPermanent g "Paradox Shaper").status.prepared &&
    (exiledCopies g "Omit Variables").size == 1

/-- Ruling 744: only the current controller of the prepared creature may cast
the copy. -/
def angelStolen : Game :=
  let o := namedPermanent preparedAngel "Blossom-Blessed Angel"
  preparedAngel.setObject { o with controller := some ⟨1⟩ }

#guard !angelStolen.mayPlayFromExile ⟨0⟩ (seedSutureCopy angelStolen)
#guard angelStolen.mayPlayFromExile ⟨1⟩ (seedSutureCopy angelStolen)
#guard (fraRuling 744).comment.contains "Only the current controller"

/- Ruling 746: losing all abilities doesn't unprepare the creature. -/
#guard
  let o := namedPermanent preparedAngel "Blossom-Blessed Angel"
  let g := preparedAngel.setObject { o with status :=
    { o.status with losesAbilitiesGrantedBy := #[o.id] } }
  (namedPermanent g "Blossom-Blessed Angel").status.prepared &&
    (exiledCopies g "Seed Suture").size == 1
#guard (fraRuling 746).comment.contains "it won't stop being prepared"

/-- Ruling 747: a creature without a prepare spell can't become prepared,
including through Hexhaven Dueling Arena or Codie. -/
def bearsTriedToPrepare : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  g.becomePrepared (namedPermanent g "Grizzly Bears")

#guard !(namedPermanent bearsTriedToPrepare "Grizzly Bears").status.prepared
#guard !bearsTriedToPrepare.objects.any (fun o =>
  o.zone == .exile && (o.playPermission.bind (·.prepareSource)).isSome)
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := enterPermanent g paradoxShaper ⟨0⟩
  let g := g.applyAbilityEffect ⟨0⟩ Effect.eachCreatureYouControlBecomesPrepared #[]
  !(namedPermanent g "Grizzly Bears").status.prepared &&
    (namedPermanent g "Paradox Shaper").status.prepared
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := g.applyAbilityEffect ⟨0⟩ Effect.targetCreatureBecomesPrepared
    #[.permanent (namedPermanent g "Grizzly Bears").id]
  !(namedPermanent g "Grizzly Bears").status.prepared
#guard (fraRuling 747).comment.contains "A creature without a prepare spell can't become prepared"

/- Ruling 748: the copy is cast for its own mana cost, not an alternative
cost. -/
#guard preparedAngel.playManaCost (seedSutureCopy preparedAngel)
    (seedSutureCopy preparedAngel).printed ==
  (blossomBlessedAngel.prepareFace.map (·.manaCost)).getD ManaCost.empty
#guard (fraRuling 748).comment.contains "isn't casting it for an alternative cost"

/-- Ruling 749: if Seed Suture's target is illegal as it resolves, none of
its effects happen (no life gain), and the Angel stays unprepared. The copy
ceases to exist. -/
def sutureAtBears : Game :=
  let g := addPermanent preparedAngel grizzlyBears ⟨0⟩ ⟨0⟩
  let g := withWhiteMana g ⟨0⟩ 2
  let g := mustApply g ⟨0⟩ (.cast (seedSutureCopy g).id)
  let g := mustApply g ⟨0⟩ (.target (.permanent (namedPermanent g "Grizzly Bears").id))
  mustApply g ⟨0⟩ .pay

def sutureFizzled : Game :=
  let bears := namedPermanent sutureAtBears "Grizzly Bears"
  let (g, _) := sutureAtBears.move bears.id (.graveyard ⟨0⟩) none
  passBoth g

#guard (sutureFizzled.player ⟨0⟩).life == (sutureAtBears.player ⟨0⟩).life
#guard !(namedPermanent sutureFizzled "Blossom-Blessed Angel").status.prepared
#guard !sutureFizzled.objects.any (fun o => o.name == "Seed Suture")
#guard (fraRuling 749).comment.contains "the associated permanent will still not be prepared"

end Mtg.Engine.FraRulingTests
