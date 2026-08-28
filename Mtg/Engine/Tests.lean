import Mtg.Engine.Agent
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Game

/-!
# Compile-time smoke tests for the engine.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/-- 60-card constructed red fixture used only by engine tests. -/
def testRedDeck : Array CardDef :=
  copies 32 mountain ++
  copies 4 lightningBolt ++
  copies 4 shock ++
  copies 4 ragingGoblin ++
  copies 4 grayOgre ++
  copies 4 hillGiant ++
  copies 4 canyonMinotaur ++
  copies 4 mountain

/-- 60-card constructed green fixture used only by engine tests. -/
def testGreenDeck : Array CardDef :=
  copies 32 forest ++
  copies 4 llanowarElves ++
  copies 4 giantGrowth ++
  copies 4 grizzlyBears ++
  copies 4 giantSpider ++
  copies 4 crawWurm ++
  copies 4 centaurCourser ++
  copies 4 rumblingBaloth

def testConfig (seed : UInt64 := 20260807) : StartConfig := {
  seats := #[
    { name := "Chandra", deck := testRedDeck },
    { name := "Nissa", deck := testGreenDeck }
  ]
  format := .constructed
  seed := seed
  startingPlayer := some 0
}

def drawnHands : Game :=
  match Start.start (testConfig 1) with
  | .ok g => g
  | .error e => panic! e

/-- Keep every remaining opening hand (CR 103.5) so tests can begin on turn 1. -/
def keepOpeningHands : Game → Nat → Game
  | _, 0 => panic! "keepOpeningHands fuel exhausted"
  | g, n + 1 =>
    match g.pending with
    | .declareMulligan p =>
      match g.apply p .keep with
      | .ok g' => keepOpeningHands g' n
      | .error e => panic! e
    | .putOnBottom _ _ => panic! "keepOpeningHands: unexpected putOnBottom"
    | _ => g

def started : Game := keepOpeningHands drawnHands 8

#guard testRedDeck.size == 60
#guard testGreenDeck.size == 60
#guard isLegalDeck .constructed testRedDeck
#guard isLegalDeck .constructed testGreenDeck
#guard !isLegalDeck .constructed (copies 5 lightningBolt)

#guard drawnHands.pending == .declareMulligan ⟨0⟩
#guard drawnHands.actor == some ⟨0⟩
#guard drawnHands.openingHandsPending
#guard !drawnHands.hasPriority ⟨0⟩
#guard (drawnHands.player ⟨0⟩).hand.size == 7
#guard (drawnHands.player ⟨1⟩).hand.size == 7
#guard !(drawnHands.player ⟨0⟩).keptOpeningHand

#guard started.players.size == 2
#guard (started.player ⟨0⟩).life == 20
#guard (started.player ⟨1⟩).life == 20
#guard (started.player ⟨0⟩).hand.size == 7
#guard (started.player ⟨1⟩).hand.size == 7
#guard (started.player ⟨0⟩).library.size == 53
#guard started.startingPlayer == ⟨0⟩
#guard started.isFirstTurn
#guard started.step == .upkeep

/-- CR 103.1: the starting player is chosen before opening hands; that player
declares keep-or-mulligan first (CR 103.5). -/
def nissaStarts : Game :=
  match Start.start { testConfig 1 with startingPlayer := some 1 } with
  | .ok g => g
  | .error e => panic! e

#guard nissaStarts.startingPlayer == ⟨1⟩
#guard nissaStarts.activePlayer == ⟨1⟩
#guard nissaStarts.pending == .declareMulligan ⟨1⟩
#guard nissaStarts.actor == some ⟨1⟩
#guard nissaStarts.log.any (· == "Starting player: Nissa")

def nissaStarted : Game := keepOpeningHands nissaStarts 8

#guard nissaStarted.startingPlayer == ⟨1⟩
#guard nissaStarted.activePlayer == ⟨1⟩
#guard nissaStarted.skipsFirstDraw
#guard nissaStarted.log.any (· == "Nissa takes the first turn")

def nissaAfterDraw : Game :=
  match Game.pass nissaStarted ⟨1⟩ with
  | .error e => panic! e
  | .ok g1 =>
    match Game.pass g1 ⟨0⟩ with
    | .error e => panic! e
    | .ok g2 => g2

#guard nissaAfterDraw.step == .precombatMain
#guard (nissaAfterDraw.player ⟨1⟩).hand.size == 7
#guard nissaAfterDraw.hasPriority ⟨1⟩
#guard nissaAfterDraw.log.any (· == "Nissa skips their first draw step (CR 103.8a)")

/-- First player skipped the draw step (CR 103.8a / 500.11), so after upkeep
the game proceeds to precombat main: no card is drawn and nobody received
priority during the skipped step. -/
def afterDraw : Game :=
  match Game.pass started ⟨0⟩ with
  | .error e => panic! e
  | .ok g1 =>
    match Game.pass g1 ⟨1⟩ with
    | .error e => panic! e
    | .ok g2 => g2

#guard started.skipsFirstDraw
#guard afterDraw.step == .precombatMain
#guard (afterDraw.player ⟨0⟩).hand.size == 7
#guard (afterDraw.player ⟨0⟩).library.size == 53
#guard afterDraw.hasPriority ⟨0⟩
#guard afterDraw.asSorcery? ⟨0⟩
#guard afterDraw.canPlayLand ⟨0⟩
#guard !afterDraw.hasPriority ⟨1⟩
#guard afterDraw.actor == some ⟨0⟩
#guard afterDraw.log.any (· == "Chandra skips their first draw step (CR 103.8a)")
#guard (started.beginStep .draw).step == .precombatMain
#guard ((started.beginStep .draw).player ⟨0⟩).hand.size == 7

def played : Game :=
  Agent.play started 80

#guard played.log.size > 10
#guard played.turnNumber ≥ 1
#guard started.stack.isEmpty

/-- `true` iff `needle` occurs in `haystack`. -/
def mentions (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- `true` iff some log line contains `needle`. -/
def logContains (g : Game) (needle : String) : Bool :=
  g.log.any (fun s => mentions s needle)

/-- First card of `p`'s hand; tests assume opening hands are non-empty. -/
def firstHandCard (g : Game) (p : PlayerId) : GameObject :=
  match (g.handObjects p)[0]? with
  | some o => o
  | none => panic! "expected a card in hand"

def drawnOnce : Game := Game.draw started ⟨0⟩

#guard (drawnOnce.player ⟨0⟩).hand.size == 8
#guard (drawnOnce.player ⟨0⟩).library.size == 52
#guard (drawnOnce.player ⟨1⟩).hand.size == 7

/-- Put `card` into the game as a new object and optionally update its owner. -/
def insertObject (g : Game) (card : CardDef) (owner : PlayerId) (zone : Zone)
    (controller : Option PlayerId := none) (status : Status := {})
    (updateOwner : ObjectId → Player → Player := fun _ pl => pl) : Game :=
  let (g, obj) := g.allocObject card owner zone controller status
  g.modifyPlayer owner (updateOwner obj.id)

/-- Put `card` onto the battlefield with explicit owner and controller. -/
def addPermanent (g : Game) (card : CardDef) (owner controller : PlayerId) : Game :=
  insertObject g card owner .battlefield (some controller) { summoningSick := false }

/-- Drop a basic land onto the battlefield without using the play-land action. -/
def addUntappedLand (g : Game) (card : CardDef) : Game :=
  addPermanent g card g.activePlayer g.activePlayer

def withMountain : Game := addUntappedLand started mountain

def tappedMountain : Game :=
  match (withMountain.permanentsOf ⟨0⟩).find? (·.printed.isLand) with
  | none => panic! "expected a land on the battlefield"
  | some o =>
    match o.printed.manaAbilities[0]? with
    | none => panic! s!"{o.name} has no mana ability"
    | some m =>
      match withMountain.tapForMana ⟨0⟩ o.id m with
      | .ok g => g
      | .error e => panic! e

-- Occupants are unchanged, but the land is now tapped (CR 110.5 / 605.3a).
#guard withMountain.battlefield.map (·.id) == tappedMountain.battlefield.map (·.id)
#guard tappedMountain.battlefield.any (·.status.tapped)
#guard !(withMountain.battlefield.any (·.status.tapped))
#guard (tappedMountain.player ⟨0⟩).manaPool != (withMountain.player ⟨0⟩).manaPool

/-- Last permanent on the battlefield; tests assume one is present. -/
def lastPermanent (g : Game) : GameObject :=
  match g.battlefield.back? with
  | some o => o
  | none => panic! "expected a permanent on the battlefield"

/-- Untap is a turn-based action (CR 502.2): occupants stay put, but the land
is no longer tapped. -/
def afterUntapStep : Game := tappedMountain.beginStep .untap

#guard tappedMountain.battlefield.map (·.id) == afterUntapStep.battlefield.map (·.id)
#guard afterUntapStep.step == .untap
#guard !(afterUntapStep.battlefield.any (·.status.tapped))
#guard afterUntapStep.log.any (fun s => mentions s "untaps Mountain")

/-- A permanent Chandra owns and Nissa controls is among Nissa's permanents. -/
def stolenMountain : Game := addPermanent started mountain ⟨0⟩ ⟨1⟩

#guard (stolenMountain.permanentsOf ⟨1⟩).any (·.id == (lastPermanent stolenMountain).id)
#guard !(stolenMountain.permanentsOf ⟨0⟩).any (·.id == (lastPermanent stolenMountain).id)
#guard (lastPermanent stolenMountain).owner == ⟨0⟩
#guard (lastPermanent stolenMountain).controller == some ⟨1⟩

/-- Changing control does not move the permanent off the battlefield. -/
def afterControlChange : Game :=
  let o := lastPermanent withMountain
  withMountain.setObject { o with controller := some ⟨1⟩ }

#guard withMountain.battlefield.map (·.id) == afterControlChange.battlefield.map (·.id)
#guard (lastPermanent afterControlChange).controller == some ⟨1⟩
#guard (lastPermanent afterControlChange).owner == ⟨0⟩

/-- Nissa's permanent entered first; Chandra still has a later Forest. -/
def mixedControllers : Game := addPermanent stolenMountain forest ⟨0⟩ ⟨0⟩

#guard (mixedControllers.permanentsOf ⟨0⟩)[0]!.name == "Forest"
#guard (mixedControllers.permanentsOf ⟨1⟩)[0]!.name == "Mountain"

def uncontrolledPermanent : Game :=
  let o := lastPermanent withMountain
  withMountain.setObject { o with controller := none }

#guard (lastPermanent uncontrolledPermanent).controller.isNone
#guard (lastPermanent uncontrolledPermanent).owner == ⟨0⟩

/- Hands, battlefield, and other zones print keywords and abilities. -/
#guard mentions ragingGoblin.summary "haste"
#guard mentions giantSpider.summary "reach"
#guard mentions llanowarElves.summary "{T}: Add {G}"
#guard mentions lightningBolt.summary "deals 3 damage"
#guard mentions lightningBolt.summary "{R}"
#guard mentions mountain.summary "{T}: Add {R}"
#guard !mentions mountain.summary "{0}"
#guard !mentions forest.summary "{0}"
#guard !mentions roguesPassage.summary "{0}"
#guard mentions wayfarersBauble.summary "Search your library"
#guard mentions attercop.summary "reach"
#guard mentions attercop.summary "deathtouch"
#guard mentions attercop.summary "Landfall"
#guard attercop.keywords.reach
#guard attercop.keywords.deathtouch
#guard attercop.triggeredAbilities.size == 1
#guard attercop.triggeredAbilities == #[.onLandYouControlEntersGets1]
#guard mentions landrovalHorizonWitness.summary "flying"
#guard mentions landrovalHorizonWitness.summary "Whenever two or more creatures"
#guard mentions soldierOfTheGreyHost.summary "Flash"
#guard mentions soldierOfTheGreyHost.summary "flying"
#guard mentions roguesPassage.summary "{T}: Add {C}"
#guard mentions roguesPassage.summary "can't be blocked"
#guard roguesPassage.activatedAbilities.size == 1
#guard roguesPassage.activatedAbilities[0]!.effect == .targetCantBeBlockedThisTurn
#guard roguesPassage.activatedAbilities[0]!.cost.tap
#guard roguesPassage.activatedAbilities[0]!.cost.mana == ManaCost.ofGeneric 4
#guard mentions orcishSiegemaster.summary "trample"
#guard mentions orcishSiegemaster.summary "Other Orcs and Goblins"
#guard mentions orcishSiegemaster.summary "greatest power"
#guard orcishSiegemaster.staticAbilities.size == 1
#guard orcishSiegemaster.triggeredAbilities.size == 1
#guard mentions battleScarredGoblin.summary "becomes blocked"
#guard battleScarredGoblin.triggeredAbilities.size == 1
#guard mentions giftOfStrands.summary "flash"
#guard mentions giftOfStrands.summary "Enchanted creature"
#guard giftOfStrands.staticAbilities.size == 1
#guard giftOfStrands.triggeredAbilities.size == 1
#guard mentions raggedShortSpear.summary "Equipped creature"
#guard mentions raggedShortSpear.summary "Equip"
#guard raggedShortSpear.isEquipment
#guard raggedShortSpear.staticAbilities.size == 1
#guard raggedShortSpear.triggeredAbilities.size == 1
#guard raggedShortSpear.activatedAbilities.size == 1
#guard mentions crudeBentBlade.summary "Equipped creature"
#guard mentions crudeBentBlade.summary "Equip"
#guard mentions crudeBentBlade.summary "target opponent"
#guard crudeBentBlade.isEquipment
#guard crudeBentBlade.staticAbilities.size == 1
#guard crudeBentBlade.triggeredAbilities.size == 1
#guard crudeBentBlade.activatedAbilities.size == 1
#guard crudeBentBlade.triggeredAbilities == #[.onEnterTargetOpponentSacrificesCreature]
#guard mentions galadhrimGuide.summary "scry 2"
#guard galadhrimGuide.triggeredAbilities.size == 1
#guard galadhrimGuide.triggeredAbilities == #[.onEnterScry 2]
#guard mentions elvishVisionary.summary "draw a card"
#guard elvishVisionary.triggeredAbilities.size == 1
#guard elvishVisionary.triggeredAbilities == #[.onEnterDraw 1]
#guard mentions quarrel.summary "deals damage equal to its power"
#guard quarrel.isInstant
#guard quarrel.requiresTarget
#guard quarrel.spellEffect == some .creatureYouControlDealsPowerToOppCreature
#guard mentions smiteTheDeathless.summary "loses indestructible"
#guard mentions smiteTheDeathless.summary "exile it instead"
#guard smiteTheDeathless.isInstant
#guard smiteTheDeathless.requiresTarget
#guard smiteTheDeathless.spellEffect == some (.dealDamageLoseIndestructibleExile 3)
#guard mentions woodElves.summary "Forest card"
#guard woodElves.triggeredAbilities.size == 1
#guard woodElves.triggeredAbilities == #[.onEnterSearchForest]
#guard mentions elvishArchdruid.summary "Other Elf creatures"
#guard mentions elvishArchdruid.summary "for each Elf"
#guard elvishArchdruid.staticAbilities.size == 1
#guard elvishArchdruid.staticAbilities == #[.otherCreaturesGet #["Elf"] 1 1]
#guard elvishArchdruid.tapAddManaForEach == #[{ mana := .colored .green, subtype := "Elf" }]
#guard mentions mirkwoodElk.summary "trample"
#guard mentions mirkwoodElk.summary "Elf card"
#guard mirkwoodElk.keywords.trample
#guard mirkwoodElk.triggeredAbilities.size == 1
#guard mirkwoodElk.triggeredAbilities == #[.onEnterOrAttackReturnElfGainLife]
#guard mentions celebornTheWise.summary "one or more Elves"
#guard mentions celebornTheWise.summary "looked at"
#guard celebornTheWise.triggeredAbilities.size == 2
#guard celebornTheWise.triggeredAbilities ==
  #[.onAttackWithElvesScry 1, .onScryPumpSelfForEachLookedAt]
#guard mentions galionElvenkingsButler.summary "base power and toughness"
#guard galionElvenkingsButler.triggeredAbilities.size == 1
#guard galionElvenkingsButler.triggeredAbilities == #[.onAttackSetOtherBasePT]
#guard mentions lothlorienLookout.summary "scry 1"
#guard lothlorienLookout.triggeredAbilities.size == 1
#guard lothlorienLookout.triggeredAbilities == #[.onAttackScry 1]
#guard mentions woodlandWeavemaster.summary "vigilance"
#guard mentions woodlandWeavemaster.summary "another Elf"
#guard mentions woodlandWeavemaster.summary "any one color"
#guard woodlandWeavemaster.keywords.vigilance
#guard woodlandWeavemaster.triggeredAbilities.size == 1
#guard woodlandWeavemaster.triggeredAbilities == #[.onAnotherElfYouControlEntersGets1]
#guard woodlandWeavemaster.tapAddAnyColorEqualToPower
#guard mentions oliphaunt.summary "trample"
#guard mentions oliphaunt.summary "+2/+0"
#guard mentions oliphaunt.summary "Mountaincycling"
#guard oliphaunt.keywords.trample
#guard oliphaunt.triggeredAbilities.size == 1
#guard oliphaunt.triggeredAbilities == #[.onAttackOtherGets2AndTrample]
#guard oliphaunt.activatedAbilities.size == 1
#guard oliphaunt.activatedAbilities[0]!.effect == .searchLandTypeToHand "Mountain"
#guard mentions wargTactics.summary "Choose one"
#guard mentions wargTactics.summary "hexproof"
#guard wargTactics.isModal
#guard wargTactics.modes.size == 2
#guard mentions goblinCratermaker.summary "Choose one"
#guard mentions goblinCratermaker.summary "colorless nonland"
#guard goblinCratermaker.activatedAbilities.size == 1
#guard mentions beornsHospitality.summary "Landfall"
#guard mentions beornsHospitality.summary "Bear creature"
#guard beornsHospitality.triggeredAbilities.size == 1
#guard beornsHospitality.activatedAbilities.size == 1
#guard mentions mirkwoodPathmaker.summary "lands you control"
#guard mentions mirkwoodPathmaker.summary "*/*"
#guard mirkwoodPathmaker.staticAbilities.size == 1
#guard mirkwoodPathmaker.power.isNone
#guard mirkwoodPathmaker.toughness.isNone
#guard mentions ologHaiCrusher.summary "trample"
#guard mentions ologHaiCrusher.summary "can't block unless"
#guard ologHaiCrusher.keywords.trample
#guard ologHaiCrusher.staticAbilities.size == 1
#guard ologHaiCrusher.staticAbilities == #[.cantBlockUnlessYouControl #["Goblin", "Orc"]]
#guard mentions gandalfSparkStarter.summary "reach"
#guard mentions gandalfSparkStarter.summary "divided as you choose"
#guard gandalfSparkStarter.keywords.reach
#guard gandalfSparkStarter.triggeredAbilities.size == 1
#guard gandalfSparkStarter.triggeredAbilities == #[.onEnterDealDividedDamage 3 3]
#guard mentions goblinFireleaper.summary "+1/+0"
#guard mentions goblinFireleaper.summary "dies"
#guard goblinFireleaper.activatedAbilities.size == 1
#guard goblinFireleaper.triggeredAbilities.size == 1
#guard goblinFireleaper.triggeredAbilities == #[.onDiesDealDamageEqualToPowerToOppCreature]
#guard mentions desolationProwler.summary "Pay 2 life"
#guard mentions desolationProwler.summary "+2/+2"
#guard desolationProwler.activatedAbilities.size == 1
#guard desolationProwler.activatedAbilities[0]!.effect == .sourceGets 2 2
#guard desolationProwler.activatedAbilities[0]!.cost.payLife == 2
#guard desolationProwler.activatedAbilities[0]!.onceEachTurn
#guard mentions raveningWarg.summary "deathtouch"
#guard mentions raveningWarg.summary "Ferocious"
#guard mentions raveningWarg.summary "power 4 or greater"
#guard raveningWarg.keywords.deathtouch
#guard raveningWarg.triggeredAbilities.size == 1
#guard raveningWarg.triggeredAbilities == #[.onAttackFerociousGainLife 2]
#guard mentions gollumSilentSlinker.summary "menace"
#guard !mentions gollumSilentSlinker.summary "can't be blocked except"
#guard gollumSilentSlinker.keywords.menace
#guard gollumSilentSlinker.power == some 4
#guard gollumSilentSlinker.toughness == some 3
#guard mentions bilbosDeadlySlice.summary "Destroy target creature"
#guard bilbosDeadlySlice.isInstant
#guard bilbosDeadlySlice.spellEffect == some .destroyCreature
#guard bilbosDeadlySlice.requiresTarget
#guard bilbosDeadlySlice.hasCastKind .destroyCreature
#guard mentions infernoTitan.summary "+1/+0"
#guard mentions infernoTitan.summary "divided as you choose"
#guard infernoTitan.activatedAbilities.size == 1
#guard infernoTitan.triggeredAbilities.size == 1
#guard infernoTitan.triggeredAbilities == #[.onEnterOrAttackDealDividedDamage 3 3]
#guard mentions guttersnipe.summary "instant or sorcery"
#guard mentions guttersnipe.summary "each opponent"
#guard guttersnipe.triggeredAbilities.size == 1
#guard guttersnipe.triggeredAbilities == #[.onCastInstantOrSorceryDealDamageToEachOpponent 2]
#guard mentions guardianOfTheHalls.summary "trample"
#guard mentions guardianOfTheHalls.summary "+1/+1"
#guard guardianOfTheHalls.keywords.trample
#guard guardianOfTheHalls.activatedAbilities.size == 1
#guard guardianOfTheHalls.activatedAbilities[0]!.effect == .putPlusOnePlusOneOnSource 3
#guard guardianOfTheHalls.activatedAbilities[0]!.cost.mana ==
  ManaCost.ofGenericAndColors 5 [.green, .green]
#guard mentions improvisedClub.summary "additional cost"
#guard mentions improvisedClub.summary "4 damage"
#guard improvisedClub.isInstant
#guard improvisedClub.spellEffect == some (.dealDamage 4)
#guard improvisedClub.additionalCostSacrificeArtifactOrCreature
#guard improvisedClub.requiresTarget
#guard mentions fireOfOrthanc.summary "artifact or land"
#guard mentions fireOfOrthanc.summary "can't block this turn"
#guard fireOfOrthanc.isSorcery
#guard fireOfOrthanc.spellEffect == some .destroyArtifactOrLandNonflyersCantBlock
#guard fireOfOrthanc.requiresTarget
#guard mentions smaugTheGreatCalamity.summary "flying"
#guard mentions smaugTheGreatCalamity.summary "Spew Flame"
#guard smaugTheGreatCalamity.keywords.flying
#guard smaugTheGreatCalamity.hasAdventure
#guard mentions beornReluctantHost.summary "trample"
#guard mentions beornReluctantHost.summary "Till and Tend"
#guard mentions beornReluctantHost.summary "additional land"
#guard beornReluctantHost.keywords.trample
#guard beornReluctantHost.hasAdventure

/- Structured abilities still print when Oracle text is absent. -/
#guard
  let c := creature "Silent Elves" ManaCost.empty #[] 1 1
    (tapAddMana := #[.colored .green])
  mentions c.abilitiesText "{T}: Add {G}" &&
    mentions c.summary "{T}: Add {G}" &&
    !mentions c.summary "{0}"

#guard
  let c := creature "Silent Ornithopter" { symbols := #[.generic 0] } #[] 0 2
  mentions c.summary "{0}"

#guard
  let c := creature "Silent Siege" ManaCost.empty #[] 0 5
    (keywords := Keyword.trample)
    (staticAbilities := #[.otherCreaturesHaveTrample #["Orc", "Goblin"]])
    (triggeredAbilities := #[.onAttackPumpByGreatestPower])
  mentions c.abilitiesText "Other Orcs and Goblins" &&
    mentions c.abilitiesText "greatest power" &&
    mentions c.summary "trample"

#guard
  let c := creature "Silent Scar" ManaCost.empty #[] 2 2
    (triggeredAbilities := #[.onBecomesBlockedDeal1ToBlockers])
  mentions c.abilitiesText "becomes blocked" &&
    mentions c.abilitiesText "each creature blocking it"

#guard
  let c := aura "Silent Strands" ManaCost.empty ""
    (keywords := Keyword.flash)
    (staticAbilities := #[.enchantedCreatureGets 3 3])
    (triggeredAbilities := #[.onEnterScry 2])
  mentions c.abilitiesText "Enchanted creature gets +3/+3" &&
    mentions c.abilitiesText "scry 2" &&
    mentions c.summary "flash"

#guard
  let c := creature "Silent Visionary" ManaCost.empty #[] 1 1
    (triggeredAbilities := #[.onEnterDraw 1])
  mentions c.abilitiesText "draw a card"

#guard
  let c := creature "Silent Wood Elves" ManaCost.empty #[] 1 1
    (triggeredAbilities := #[.onEnterSearchForest])
  mentions c.abilitiesText "Forest card" &&
    mentions c.abilitiesText "onto the battlefield"

#guard
  let c := creature "Silent Archdruid" ManaCost.empty #["Elf", "Druid"] 2 2
    (staticAbilities := #[.otherCreaturesGet #["Elf"] 1 1])
    (tapAddManaForEach := #[{ mana := .colored .green, subtype := "Elf" }])
  mentions c.abilitiesText "Other Elf creatures you control get +1/+1" &&
    mentions c.abilitiesText "{T}: Add {G} for each Elf you control" &&
    !mentions c.abilitiesText "{T}: Add {G};" &&
    c.manaAbilities == #[.colored .green]

#guard
  let c := creature "Silent Weavemaster" ManaCost.empty #["Elf", "Druid"] 1 2
    (keywords := Keyword.vigilance)
    (triggeredAbilities := #[.onAnotherElfYouControlEntersGets1])
    (tapAddAnyColorEqualToPower := true)
  mentions c.summary "vigilance" &&
    mentions c.abilitiesText "another Elf you control enters" &&
    mentions c.abilitiesText "any one color" &&
    mentions c.abilitiesText "Elf spells" &&
    c.tapAddAnyColorEqualToPower &&
    c.manaAbilities.size == 5

#guard
  let c := artifact "Silent Spear" ManaCost.empty ""
    (subtypes := #["Equipment"])
    (staticAbilities := #[.equippedCreatureGets 2 0])
    (triggeredAbilities := #[.onEnterMayDiscardDraw 2])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 3)])
  mentions c.abilitiesText "Equipped creature gets +2/+0" &&
    mentions c.abilitiesText "you may discard a card" &&
    mentions c.abilitiesText "Attach this Equipment" &&
    mentions c.abilitiesText "activate only as a sorcery"

#guard
  let c := artifact "Silent Blade" ManaCost.empty ""
    (subtypes := #["Equipment"])
    (staticAbilities := #[.equippedCreatureGets 2 1])
    (triggeredAbilities := #[.onEnterTargetOpponentSacrificesCreature])
    (activatedAbilities := #[equipAbility (ManaCost.ofGeneric 2)])
  mentions c.abilitiesText "Equipped creature gets +2/+1" &&
    mentions c.abilitiesText "target opponent sacrifices a creature" &&
    mentions c.abilitiesText "Attach this Equipment" &&
    mentions c.abilitiesText "activate only as a sorcery"

#guard
  let c := enchantment "Silent Hospitality" ManaCost.empty ""
    (triggeredAbilities := #[.onLandYouControlEntersPlusOnePlusOne])
    (activatedAbilities := #[
      activated .becomeBearCreatureWithLandsPT
        (ManaCost.ofGenericAndColors 5 [.green, .green])])
  mentions c.abilitiesText "land you control enters" &&
    mentions c.abilitiesText "Bear creature" &&
    mentions c.abilitiesText "{5}{G}{G}"

#guard
  let c := creature "Silent Attercop" ManaCost.empty #["Spider"] 2 1
    (keywords := Keyword.reach.merge Keyword.deathtouch)
    (triggeredAbilities := #[.onLandYouControlEntersGets1])
  mentions c.summary "reach" &&
    mentions c.summary "deathtouch" &&
    mentions c.abilitiesText "land you control enters" &&
    mentions c.abilitiesText "+1/+1 until end of turn"

#guard
  let c := card "Silent Pathmaker" #[.creature]
    (staticAbilities := #[.powerToughnessEqualLandsYouControl])
  mentions c.abilitiesText "lands you control" &&
    mentions c.summary "*/*"

#guard
  let c := card "Silent Crusher" #[.creature]
    (keywords := Keyword.trample)
    (staticAbilities := #[.cantBlockUnlessYouControl #["Goblin", "Orc"]])
  mentions c.abilitiesText "can't block unless you control a Goblin or Orc" &&
    mentions c.summary "trample"

#guard
  let c := card "Silent Spark" #[.creature]
    (keywords := Keyword.reach)
    (triggeredAbilities := #[.onEnterDealDividedDamage 3 3])
  mentions c.abilitiesText "divided as you choose" &&
    mentions c.abilitiesText "one, two, or three" &&
    mentions c.summary "reach"

#guard
  let c := card "Silent Fireleaper" #[.creature]
    (activatedAbilities := #[
      activated (.sourceGets 1 0) (ManaCost.ofGenericAndColor 1 .red)])
    (triggeredAbilities := #[.onDiesDealDamageEqualToPowerToOppCreature])
  mentions c.abilitiesText "+1/+0" &&
    mentions c.abilitiesText "dies" &&
    mentions c.abilitiesText "{1}{R}"

#guard
  let c := land "Silent Passage" ""
    (tapAddMana := #[.colorless])
    (activatedAbilities := #[
      activated .targetCantBeBlockedThisTurn (ManaCost.ofGeneric 4) (tap := true)])
  mentions c.abilitiesText "{T}: Add {C}" &&
    mentions c.abilitiesText "can't be blocked this turn" &&
    mentions c.abilitiesText "{4}" &&
    mentions c.abilitiesText "{T}"

#guard
  let c := card "Silent Titan" #[.creature]
    (activatedAbilities := #[activated (.sourceGets 1 0) (ManaCost.ofColor .red)])
    (triggeredAbilities := #[.onEnterOrAttackDealDividedDamage 3 3])
  mentions c.abilitiesText "+1/+0" &&
    mentions c.abilitiesText "enters or attacks" &&
    mentions c.abilitiesText "divided as you choose" &&
    mentions c.abilitiesText "{R}"

#guard
  let c := creature "Silent Elk" ManaCost.empty #[] 6 6
    (keywords := Keyword.trample)
    (triggeredAbilities := #[.onEnterOrAttackReturnElfGainLife])
  mentions c.abilitiesText "Elf card" &&
    mentions c.abilitiesText "graveyard" &&
    mentions c.abilitiesText "gain life" &&
    mentions c.summary "trample"

#guard
  let c := creature "Silent Celeborn" ManaCost.empty #[] 3 3
    (triggeredAbilities := #[.onAttackWithElvesScry 1, .onScryPumpSelfForEachLookedAt])
  mentions c.abilitiesText "one or more Elves" &&
    mentions c.abilitiesText "scry 1" &&
    mentions c.abilitiesText "looked at"

#guard
  let c := creature "Silent Snipe" ManaCost.empty #[] 2 2
    (triggeredAbilities := #[.onCastInstantOrSorceryDealDamageToEachOpponent 2])
  mentions c.abilitiesText "instant or sorcery" &&
    mentions c.abilitiesText "each opponent"

#guard
  let c := creature "Silent Guardian" ManaCost.empty #[] 2 2
    (keywords := Keyword.trample)
    (activatedAbilities := #[
      activated (.putPlusOnePlusOneOnSource 3)
        (ManaCost.ofGenericAndColors 5 [.green, .green])])
  mentions c.abilitiesText "Put 3 +1/+1 counters" &&
    mentions c.abilitiesText "{5}{G}{G}" &&
    mentions c.summary "trample"

#guard
  let c := creature "Silent Butler" ManaCost.empty #[] 4 4
    (triggeredAbilities := #[.onAttackSetOtherBasePT])
  mentions c.abilitiesText "up to one other target" &&
    mentions c.abilitiesText "base power and toughness"

#guard
  let c := creature "Silent Lookout" ManaCost.empty #[] 1 3
    (triggeredAbilities := #[.onAttackScry 1])
  mentions c.abilitiesText "Whenever this creature attacks" &&
    mentions c.abilitiesText "scry 1"

#guard
  let c := creature "Silent Warg" ManaCost.empty #["Wolf"] 2 2
    (keywords := Keyword.deathtouch)
    (triggeredAbilities := #[.onAttackFerociousGainLife 2])
  mentions c.summary "deathtouch" &&
    mentions c.abilitiesText "power 4 or greater" &&
    mentions c.abilitiesText "you gain 2 life"

#guard
  let c := creature "Silent Slinker" ManaCost.empty #[] 4 3
    (oracleText := "Menace (This creature can't be blocked except by two or more creatures.)")
    (keywords := Keyword.menace)
  mentions c.summary "menace" &&
    !mentions c.summary "can't be blocked except" &&
    CardDef.isKeywordRestatement c.keywords c.oracleText

#guard
  let c := creature "Silent Oliphaunt" ManaCost.empty #[] 6 4
    (keywords := Keyword.trample)
    (triggeredAbilities := #[.onAttackOtherGets2AndTrample])
  mentions c.abilitiesText "+2/+0" &&
    mentions c.abilitiesText "gains trample" &&
    mentions c.summary "trample"

def withGoblin : Game := addPermanent started ragingGoblin ⟨0⟩ ⟨0⟩
def withElves : Game := addPermanent started llanowarElves ⟨0⟩ ⟨0⟩
def withSpider : Game := addPermanent started giantSpider ⟨0⟩ ⟨0⟩
def withAttercop : Game := addPermanent started attercop ⟨0⟩ ⟨0⟩
def withWarg : Game := addPermanent started raveningWarg ⟨0⟩ ⟨0⟩
def withGollum : Game := addPermanent started gollumSilentSlinker ⟨0⟩ ⟨0⟩
def withCrusher : Game := addPermanent started ologHaiCrusher ⟨0⟩ ⟨0⟩

def mustApply (g : Game) (p : PlayerId) (a : Action) : Game :=
  match g.apply p a with
  | .ok g' => g'
  | .error e => panic! e

/-- Apply the idle action for whoever must act: empty combat declarations or pass. -/
def applyIdle (g : Game) : Game :=
  match g.pending, g.actor with
  | .declareAttackers, some p =>
    mustApply g p (.declareAttackers #[])
  | .declareBlockers, some p =>
    mustApply g p (.declareBlockers #[])
  | .declareMulligan _, some p =>
    mustApply g p .keep
  | .putOnBottom _ n, some p =>
    mustApply g p (.putOnBottom ((g.player p).hand.extract 0 n))
  | .scry _ n, some p =>
    mustApply g p (.scry (g.scryLookedIds p n) #[])
  | .mayDiscardDraw _ _, some p =>
    mustApply g p .decline
  | .chooseAdditionalCost _, some p =>
    match g.proposedSpell with
    | none => panic! "expected a proposed spell while choosing an additional cost"
    | some prop =>
      let payGeneric := (g.sacrificeCreatureOrArtifactChoices p prop.spellId).isEmpty
      mustApply g p (.chooseAdditionalCost payGeneric)
  | .chooseSacrificeCreature p _ _, some _ =>
    match (g.creaturesControlledBy p)[0]? with
    | none => panic! "no creature to sacrifice"
    | some o => mustApply g p (.sacrifice o.id)
  | .chooseDiscardCard p _, some _ =>
    match (g.player p).hand.back? with
    | none => panic! "no card to discard"
    | some id => mustApply g p (.discard id)
  | .sacrificeCreature _, some p =>
    match (g.sacrificeCreatureChoices p)[0]? with
    | some sac => mustApply g p (.sacrifice sac.id)
    | none => panic! "expected a creature to sacrifice"
  | .chooseMode _, some p =>
    match g.proposedSpell with
    | none => panic! "expected a proposed spell or ability while choosing a mode"
    | some prop =>
      match prop.kind with
      | .activatedAbility =>
        match g.defaultAbilityMode p prop.abilityModes with
        | none => panic! "no legal mode (CR 601.2b)"
        | some idx => mustApply g p (.chooseMode idx)
      | .spell =>
        match g.findObject? prop.spellId with
        | none => panic! "expected a proposed spell while choosing a mode"
        | some spell =>
          match g.defaultMode p spell with
          | none => panic! "no legal mode (CR 601.2b)"
          | some i => mustApply g p (.chooseMode i)
  | .assignCombatDamage _ _, some p =>
    mustApply g p (.assignCombatDamage #[])
  | .chooseLegend _ _ ids, some p =>
    mustApply g p (.keepLegend (g.defaultLegendToKeep ids))
  | .chooseTriggerToStack p, some _ =>
    mustApply g p (.stackTriggers (g.defaultTriggerSourceIds p))
  | .chooseTargets _, some p =>
    match g.objectAwaitingTargets with
    | none => panic! "expected a proposed spell or trigger while choosing targets"
    | some spell =>
      match g.defaultTarget p spell with
      | some t => mustApply g p (.target t)
      | none =>
        match spell.triggeredAbility with
        | some ab =>
          if ab.allowsZeroTargets then mustApply g p .decline
          else panic! "no legal target (CR 601.2c)"
        | none => panic! "no legal target (CR 601.2c)"
  | _, some p =>
    mustApply g p .pass
  | _, none => panic! s!"no actor at {g.step}"

/-- Advance by idle actions until `g` is in `st` with no pending choice. -/
def skipTo (g : Game) (st : Step) : Nat → Game
  | 0 => panic! s!"skipTo fuel exhausted at {g.step}"
  | n + 1 =>
    if g.over then panic! "game over while skipping"
    else if g.step == st && g.pending == .none then g
    else skipTo (applyIdle g) st n

def passBoth (g : Game) : Game :=
  applyIdle (applyIdle g)

def atEndStep : Game := skipTo started .end 80

/-- A 0/0 creature kept alive only by an until-end-of-turn pump. -/
def zeroZero : CardDef :=
  creature "Zero/Zero" ManaCost.empty #[] 0 0

def addPumpedCreature (g : Game) (card : CardDef) (pumpP pumpT : Int) : Game :=
  insertObject g card g.activePlayer .battlefield (some g.activePlayer)
    { pump := (pumpP, pumpT), summoningSick := false }

/-- CR 514.3: after both players pass in the end step, cleanup does not grant
priority, so the next player's upkeep begins immediately. -/
def afterSilentCleanup : Game := passBoth atEndStep

#guard atEndStep.step == .end
#guard atEndStep.turnNumber == 1
#guard atEndStep.activePlayer == ⟨0⟩
#guard afterSilentCleanup.turnNumber == 2
#guard afterSilentCleanup.step == .upkeep
#guard afterSilentCleanup.activePlayer == ⟨1⟩
#guard !afterSilentCleanup.cleanupGivesPriority
#guard !afterSilentCleanup.log.any (· == "Players receive priority during cleanup (CR 514.3a)")

/-- Opponent's untap (CR 502.2) does not untap Chandra's land. -/
def nissaTurn2 : Game := passBoth (skipTo tappedMountain .end 80)

#guard nissaTurn2.turnNumber == 2
#guard nissaTurn2.activePlayer == ⟨1⟩
#guard nissaTurn2.step == .upkeep
#guard nissaTurn2.battlefield.any (·.status.tapped)
#guard !nissaTurn2.skipsFirstDraw

/-- The second player does draw on their first turn and receives priority
during the draw step (CR 103.8a applies only to the starting player). -/
def nissaDraw : Game := passBoth nissaTurn2

#guard nissaDraw.step == .draw
#guard nissaDraw.playersReceivePriority
#guard nissaDraw.hasPriority ⟨1⟩
#guard nissaDraw.actor == some ⟨1⟩
#guard (nissaDraw.player ⟨1⟩).hand.size == 8
#guard (nissaDraw.player ⟨0⟩).hand.size == 7
#guard !nissaDraw.asSorcery? ⟨1⟩
#guard nissaDraw.log.any (fun s => mentions s "Nissa draws")

/-- The pass that ends Nissa's turn also runs Chandra's untap. Occupants are
unchanged, but the land is now untapped (CR 502.2). -/
def nissaEnd : Game := skipTo nissaTurn2 .end 80
def chandraTurn3 : Game := passBoth nissaEnd

#guard nissaEnd.turnNumber == 2
#guard nissaEnd.step == .end
#guard nissaEnd.battlefield.any (·.status.tapped)
#guard chandraTurn3.turnNumber == 3
#guard chandraTurn3.activePlayer == ⟨0⟩
#guard chandraTurn3.step == .upkeep
#guard !(chandraTurn3.battlefield.any (·.status.tapped))
#guard nissaEnd.battlefield.map (·.id) == chandraTurn3.battlefield.map (·.id)
#guard chandraTurn3.log.any (fun s => mentions s "untaps Mountain")

/-- CR 514.3a: ending a pump that was keeping a 0/0 alive causes a state-based
action, so the active player receives priority still in cleanup. -/
def cleanupWithSBA : Game :=
  passBoth (addPumpedCreature atEndStep zeroZero 1 1)

#guard cleanupWithSBA.step == .cleanup
#guard cleanupWithSBA.cleanupGivesPriority
#guard cleanupWithSBA.playersReceivePriority
#guard cleanupWithSBA.actor == some ⟨0⟩
#guard cleanupWithSBA.hasPriority ⟨0⟩
#guard (cleanupWithSBA.battlefield.filter (fun o => o.name == "Zero/Zero")).isEmpty
#guard cleanupWithSBA.log.any (· == "Players receive priority during cleanup (CR 514.3a)")

/-- After the 514.3a priority window, another cleanup begins; with no further
state-based actions it ends the turn (CR 514.3a last sentence). -/
def afterExceptionCleanup : Game := passBoth cleanupWithSBA

#guard afterExceptionCleanup.turnNumber == 2
#guard afterExceptionCleanup.step == .upkeep
#guard afterExceptionCleanup.activePlayer == ⟨1⟩
#guard !afterExceptionCleanup.cleanupGivesPriority

/-- Lightning Bolt to a player (CR 120.3a) changes that player's life total. -/
def afterBolt : Game :=
  started.applyEffect ⟨0⟩ (.dealDamage 3) #[Target.player ⟨1⟩]

#guard (started.player ⟨1⟩).life == 20
#guard (afterBolt.player ⟨1⟩).life == 17
#guard (afterBolt.player ⟨0⟩).life == 20
#guard afterBolt.log.any (fun s => mentions s "17 life")

/-- Unblocked combat damage (CR 510.1a / 120.3a) also changes life. -/
def attackingGoblin : Game :=
  let g := addPermanent started ragingGoblin ⟨0⟩ ⟨0⟩
  let o := lastPermanent g
  g.setObject { o with status := { o.status with attacking := true } }

def afterCombatDamage : Game := attackingGoblin.combatDamage

#guard ragingGoblin.power == some 1
#guard (attackingGoblin.player ⟨1⟩).life == 20
#guard (afterCombatDamage.player ⟨1⟩).life == 19
#guard afterCombatDamage.log.any (fun s => mentions s "19 life")

/-- Put `card` into `p`'s hand without drawing. -/
def addToHand (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.hand p) none {} (fun id pl => { pl with hand := pl.hand.push id })

/-- Put `card` into `p`'s graveyard. -/
def addToGraveyard (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.graveyard p) none {} (fun id pl =>
    { pl with graveyard := pl.graveyard.push id })

/-- Put `card` on top of `p`'s library (the back of the library array). -/
def addToLibraryTop (g : Game) (card : CardDef) (p : PlayerId) : Game :=
  insertObject g card p (.library p) none {} (fun id pl =>
    { pl with library := pl.library.push id })

/-- Propose a spell (CR 601.2a) and announce its target (CR 601.2c). -/
def proposeTargeted (g : Game) (p : PlayerId) (id : ObjectId) (t : Target) : Game :=
  mustApply (mustApply g p (.cast id)) p (.target t)

def handCardNamed (g : Game) (p : PlayerId) (name : String) : GameObject :=
  match (g.handObjects p).find? (fun o => o.name == name) with
  | some o => o
  | none => panic! s!"expected {name} in hand"

/-- CR 601.2: a player may begin casting without mana in their pool, then
announce a target (601.2c), activate mana abilities (601.2g), then pay. -/
def boltSetup : Game :=
  addToHand (addUntappedLand started mountain) lightningBolt ⟨0⟩

def boltInHand : GameObject :=
  handCardNamed boltSetup ⟨0⟩ "Lightning Bolt"

def boltMountain : GameObject :=
  lastPermanent boltSetup

#guard (boltSetup.player ⟨0⟩).manaPool.isEmpty
#guard !(boltSetup.player ⟨0⟩).manaPool.canPay lightningBolt.manaCost
#guard (boltSetup.availableMana ⟨0⟩).canPay lightningBolt.manaCost
#guard boltSetup.canCast ⟨0⟩ boltInHand
#guard boltSetup.hasPriority ⟨0⟩

/-- The agent proposes a spell instead of tapping first. -/
def agentBeginsCast : Bool :=
  match Agent.choose boltSetup ⟨0⟩ with
  | some (.cast _) => true
  | _ => false

#guard agentBeginsCast

def proposedBolt : Game :=
  mustApply boltSetup ⟨0⟩ (.cast boltInHand.id)

#guard
  match proposedBolt.pending with
  | .chooseTargets ⟨0⟩ => true
  | _ => false
#guard proposedBolt.proposedSpell.isSome
#guard !proposedBolt.stack.isEmpty
#guard proposedBolt.stack.back!.targets.isEmpty
#guard !(proposedBolt.player ⟨0⟩).hand.contains boltInHand.id
#guard (proposedBolt.player ⟨0⟩).manaPool.isEmpty
#guard !proposedBolt.hasPriority ⟨0⟩
#guard !proposedBolt.canActivateManaAbility ⟨0⟩
#guard proposedBolt.actor == some ⟨0⟩
#guard proposedBolt.log.any (fun s => mentions s "begins casting Lightning Bolt")
#guard proposedBolt.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- CR 601.2c comes before mana abilities and payment.
#guard
  match proposedBolt.apply ⟨0⟩ .pay with
  | .error msg => mentions msg "Choose a target first"
  | .ok _ => false
#guard
  match proposedBolt.apply ⟨0⟩ (.target (Target.permanent ⟨99999⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match proposedBolt.apply ⟨1⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "may choose targets"
  | .ok _ => false

def agentChoosesTarget : Bool :=
  match Agent.choose proposedBolt ⟨0⟩ with
  | some (.target (Target.player q)) => q == ⟨1⟩
  | _ => false

#guard agentChoosesTarget

def targetedBolt : Game :=
  mustApply proposedBolt ⟨0⟩ (.target (Target.player ⟨1⟩))

#guard targetedBolt.pending == .activateManaAbilities ⟨0⟩
#guard targetedBolt.stack.back!.targets == #[Target.player ⟨1⟩]
#guard targetedBolt.canActivateManaAbility ⟨0⟩
#guard !targetedBolt.canActivateManaAbility ⟨1⟩
#guard targetedBolt.log.any (fun s => mentions s "chooses Nissa as a target (CR 601.2c)")
#guard targetedBolt.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")

/-- Opponent cannot activate mana abilities during the caster's 601.2g window. -/
def nissaTapDenied : Bool :=
  match targetedBolt.tapForMana ⟨1⟩ boltMountain.id (.colored .red) with
  | .error _ => true
  | .ok _ => false

#guard nissaTapDenied

def agentTapsInWindow : Bool :=
  match Agent.choose targetedBolt ⟨0⟩ with
  | some (.tapForMana id _) => id == boltMountain.id
  | _ => false

#guard agentTapsInWindow

def tappedForBolt : Game :=
  mustApply targetedBolt ⟨0⟩ (.tapForMana boltMountain.id (.colored .red))

#guard (tappedForBolt.player ⟨0⟩).manaPool.canPay lightningBolt.manaCost
#guard tappedForBolt.pending == .activateManaAbilities ⟨0⟩
#guard tappedForBolt.battlefield.any (·.status.tapped)

def agentPaysInWindow : Bool :=
  match Agent.choose tappedForBolt ⟨0⟩ with
  | some .pay => true
  | _ => false

#guard agentPaysInWindow

/-- Passing priority is not how the 601.2h payment is made. -/
def passDuringWindowDenied : Bool :=
  match targetedBolt.apply ⟨0⟩ .pass with
  | .error _ => true
  | .ok _ => false

#guard passDuringWindowDenied

def paidBolt : Game :=
  mustApply tappedForBolt ⟨0⟩ .pay

#guard paidBolt.pending == .none
#guard paidBolt.proposedSpell.isNone
#guard paidBolt.hasPriority ⟨0⟩
#guard (paidBolt.player ⟨0⟩).manaPool.isEmpty
#guard !paidBolt.stack.isEmpty
#guard paidBolt.log.any (fun s => mentions s "casts Lightning Bolt")

/-- Paying without enough mana reverses the cast (CR 601.2 / 733.1). -/
def reversedBolt : Game :=
  mustApply targetedBolt ⟨0⟩ .pay

#guard reversedBolt.pending == .none
#guard reversedBolt.proposedSpell.isNone
#guard reversedBolt.stack.isEmpty
#guard reversedBolt.hasPriority ⟨0⟩
#guard (reversedBolt.handObjects ⟨0⟩).any (fun o => o.name == "Lightning Bolt")
#guard !(reversedBolt.battlefield.any (·.status.tapped))
#guard (reversedBolt.player ⟨0⟩).manaPool.isEmpty
#guard reversedBolt.log.any (fun s => mentions s "the casting is reversed")

/-- Mana abilities activated at 601.2g are reversed with the illegal cast. -/
def ogreSetup : Game :=
  addToHand (addUntappedLand (skipTo started .precombatMain 80) mountain) grayOgre ⟨0⟩

def proposedOgre : Game :=
  mustApply ogreSetup ⟨0⟩ (.cast (handCardNamed ogreSetup ⟨0⟩ "Gray Ogre").id)

def tappedForOgre : Game :=
  mustApply proposedOgre ⟨0⟩ (.tapForMana (lastPermanent ogreSetup).id (.colored .red))

#guard tappedForOgre.pending == .activateManaAbilities ⟨0⟩
#guard (tappedForOgre.player ⟨0⟩).manaPool.canPay (ManaCost.ofColor .red)
#guard !(tappedForOgre.player ⟨0⟩).manaPool.canPay grayOgre.manaCost
#guard tappedForOgre.battlefield.any (·.status.tapped)

def reversedOgre : Game :=
  mustApply tappedForOgre ⟨0⟩ .pay

#guard reversedOgre.stack.isEmpty
#guard reversedOgre.hasPriority ⟨0⟩
#guard !(reversedOgre.battlefield.any (·.status.tapped))
#guard (reversedOgre.player ⟨0⟩).manaPool.isEmpty
#guard (reversedOgre.handObjects ⟨0⟩).any (fun o => o.name == "Gray Ogre")
#guard reversedOgre.log.any (fun s => mentions s "the casting is reversed")

/-- A resolved Lightning Bolt still changes life after the 601.2g window. -/
def resolvedBolt : Game :=
  mustApply (mustApply paidBolt ⟨0⟩ .pass) ⟨1⟩ .pass

#guard resolvedBolt.stack.isEmpty
#guard (resolvedBolt.player ⟨1⟩).life == 17
#guard resolvedBolt.log.any (fun s => mentions s "casts Lightning Bolt")

-- The heuristic still plays, and it announces targets then activates mana abilities.
#guard played.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")
#guard played.log.any (fun s => mentions s "must choose a target (CR 601.2c)")
#guard played.log.any (fun s => mentions s "begins casting")

/-- Two ready creatures: declaring a subset of attackers leaves the rest
untapped and not attacking. -/
def twoReadyAttackers : Game :=
  addPermanent (addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩) grayOgre ⟨0⟩ ⟨0⟩

def readyToDeclareAttackers : Game :=
  passBoth (skipTo twoReadyAttackers .beginningOfCombat 80)

def namedPermanent (g : Game) (name : String) : GameObject :=
  match g.battlefield.find? (fun o => o.name == name) with
  | some o => o
  | none => panic! s!"expected {name} on the battlefield"

def namedGraveyardCard (g : Game) (p : PlayerId) (name : String) : GameObject :=
  match g.objects.find? (fun o => o.name == name && o.zone == .graveyard p) with
  | some o => o
  | none => panic! s!"expected {name} in the graveyard"

#guard readyToDeclareAttackers.step == .declareAttackers
#guard readyToDeclareAttackers.pending == .declareAttackers
#guard (readyToDeclareAttackers.battlefield.filter (readyToDeclareAttackers.canAttack)).size == 2

def onlyBearsAttack : Game :=
  match readyToDeclareAttackers.apply ⟨0⟩
      (.declareAttackers #[(namedPermanent readyToDeclareAttackers "Grizzly Bears").id]) with
  | .ok g => g
  | .error e => panic! e

#guard (namedPermanent onlyBearsAttack "Grizzly Bears").status.attacking
#guard (namedPermanent onlyBearsAttack "Grizzly Bears").status.tapped
#guard !(namedPermanent onlyBearsAttack "Gray Ogre").status.attacking
#guard !(namedPermanent onlyBearsAttack "Gray Ogre").status.tapped
#guard onlyBearsAttack.log.any (fun s => mentions s "attacks with Grizzly Bears")
#guard !onlyBearsAttack.log.any (fun s => mentions s "attacks with Gray Ogre")

/-- Declaring both creatures still works; the demo's bare `attack` uses this. -/
def bothAttack : Game :=
  let ids := readyToDeclareAttackers.battlefield.filter (readyToDeclareAttackers.canAttack) |>.map (·.id)
  match readyToDeclareAttackers.apply ⟨0⟩ (.declareAttackers ids) with
  | .ok g => g
  | .error e => panic! e

#guard (namedPermanent bothAttack "Grizzly Bears").status.attacking
#guard (namedPermanent bothAttack "Gray Ogre").status.attacking

/-- Chandra's Gray Ogre attacks; Nissa has Grizzly Bears to block. -/
def ogreVsBears : Game :=
  addPermanent (addPermanent started grayOgre ⟨0⟩ ⟨0⟩) grizzlyBears ⟨1⟩ ⟨1⟩

def ogreDeclaredAttacker : Game :=
  let g := passBoth (skipTo ogreVsBears .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])

def readyToDeclareBlockers : Game :=
  passBoth ogreDeclaredAttacker

#guard readyToDeclareBlockers.step == .declareBlockers
#guard readyToDeclareBlockers.pending == .declareBlockers
#guard readyToDeclareBlockers.actor == some ⟨1⟩
#guard (namedPermanent readyToDeclareBlockers "Gray Ogre").status.attacking
#guard (namedPermanent readyToDeclareBlockers "Grizzly Bears").status.blocking.isEmpty

def bearsBlockOgre : Game :=
  let g := readyToDeclareBlockers
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Gray Ogre").id)])

#guard (namedPermanent bearsBlockOgre "Grizzly Bears").status.blocking ==
  #[(namedPermanent bearsBlockOgre "Gray Ogre").id]
#guard (namedPermanent bearsBlockOgre "Gray Ogre").status.blocked
#guard bearsBlockOgre.log.any (fun s => mentions s "Grizzly Bears blocks Gray Ogre")
#guard bearsBlockOgre.pending == .none

/-- Blocking sends combat damage to the creature, not the defending player. -/
def afterBlockedDamage : Game := passBoth bearsBlockOgre

#guard (afterBlockedDamage.player ⟨1⟩).life == 20
#guard afterBlockedDamage.log.any (fun s =>
  mentions s "Gray Ogre deals 2 combat damage to Grizzly Bears")
#guard afterBlockedDamage.log.any (fun s =>
  mentions s "Grizzly Bears deals 2 combat damage to Gray Ogre")
#guard !afterBlockedDamage.log.any (fun s =>
  mentions s "deals 2 combat damage to Nissa")

def afterUnblockedDamage : Game :=
  passBoth (mustApply readyToDeclareBlockers ⟨1⟩ (.declareBlockers #[]))

#guard (afterUnblockedDamage.player ⟨1⟩).life == 18
#guard afterUnblockedDamage.log.any (fun s =>
  mentions s "Gray Ogre deals 2 combat damage to Nissa")

/-- Unused mana is emptied as a turn-based action (CR 500.4). -/
def emptiedPool : Game := tappedMountain.emptyManaPools

#guard (emptiedPool.player ⟨0⟩).manaPool.isEmpty
#guard emptiedPool.log.any (fun s => mentions s "empties mana pool")

/-- CR 103.5: the starting player declares first; the mulligan is taken only
after every remaining player has declared. -/
def afterChandraDeclaresMulligan : Game :=
  mustApply drawnHands ⟨0⟩ .takeMulligan

#guard afterChandraDeclaresMulligan.pending == .declareMulligan ⟨1⟩
#guard afterChandraDeclaresMulligan.actor == some ⟨1⟩
#guard (afterChandraDeclaresMulligan.player ⟨0⟩).hand == (drawnHands.player ⟨0⟩).hand
#guard (afterChandraDeclaresMulligan.player ⟨0⟩).mulligansTaken == 0
#guard afterChandraDeclaresMulligan.willMulligan == #[⟨0⟩]
#guard afterChandraDeclaresMulligan.log.any (fun s => mentions s "will take a mulligan")
#guard !afterChandraDeclaresMulligan.log.any (fun s => mentions s "takes a mulligan (")

/-- Nissa keeps; then Chandra's declared mulligan is taken (CR 103.5). -/
def afterChandraMulligan : Game :=
  mustApply afterChandraDeclaresMulligan ⟨1⟩ .keep

#guard afterChandraMulligan.pending == .putOnBottom ⟨0⟩ 1
#guard afterChandraMulligan.actor == some ⟨0⟩
#guard (afterChandraMulligan.player ⟨0⟩).hand.size == 7
#guard (afterChandraMulligan.player ⟨0⟩).mulligansTaken == 1
#guard (afterChandraMulligan.player ⟨0⟩).library.size == 53
#guard (afterChandraMulligan.player ⟨1⟩).keptOpeningHand
#guard (afterChandraMulligan.player ⟨1⟩).hand == (drawnHands.player ⟨1⟩).hand
#guard afterChandraMulligan.log.any (fun s => mentions s "takes a mulligan")
#guard afterChandraMulligan.log.any (fun s => mentions s "at the same time")

def chandraBottomCard : GameObject :=
  match (afterChandraMulligan.handObjects ⟨0⟩)[0]? with
  | some o => o
  | none => panic! "expected a card to put on the bottom"

def afterChandraBottoms : Game :=
  mustApply afterChandraMulligan ⟨0⟩ (.putOnBottom #[chandraBottomCard.id])

#guard (afterChandraBottoms.player ⟨0⟩).hand.size == 6
#guard (afterChandraBottoms.player ⟨0⟩).library.size == 54
#guard afterChandraBottoms.pending == .declareMulligan ⟨0⟩
#guard (afterChandraBottoms.player ⟨1⟩).keptOpeningHand
#guard !(afterChandraBottoms.player ⟨0⟩).keptOpeningHand
#guard (afterChandraBottoms.object! (afterChandraBottoms.player ⟨0⟩).library[0]!).name ==
  chandraBottomCard.name
#guard afterChandraBottoms.log.any (fun s => mentions s "on the bottom of their library")

def afterChandraKeepsSix : Game :=
  mustApply afterChandraBottoms ⟨0⟩ .keep

#guard afterChandraKeepsSix.pending == .none
#guard afterChandraKeepsSix.step == .upkeep
#guard afterChandraKeepsSix.isFirstTurn
#guard (afterChandraKeepsSix.player ⟨0⟩).hand.size == 6
#guard (afterChandraKeepsSix.player ⟨1⟩).hand.size == 7
#guard (afterChandraKeepsSix.player ⟨0⟩).keptOpeningHand
#guard afterChandraKeepsSix.log.any (fun s => mentions s "takes the first turn")

/-- Both players declare a mulligan before either hand is shuffled (CR 103.5). -/
def afterBothDeclareMulligan : Game :=
  mustApply afterChandraDeclaresMulligan ⟨1⟩ .takeMulligan

#guard afterBothDeclareMulligan.pending == .putOnBottom ⟨0⟩ 1
#guard afterBothDeclareMulligan.actor == some ⟨0⟩
#guard (afterBothDeclareMulligan.player ⟨0⟩).mulligansTaken == 1
#guard (afterBothDeclareMulligan.player ⟨1⟩).mulligansTaken == 1
#guard (afterBothDeclareMulligan.player ⟨0⟩).hand.size == 7
#guard (afterBothDeclareMulligan.player ⟨1⟩).hand.size == 7
#guard (afterBothDeclareMulligan.player ⟨1⟩).hand != (drawnHands.player ⟨1⟩).hand
#guard afterBothDeclareMulligan.mulliganToBottom == #[⟨0⟩, ⟨1⟩]
#guard afterBothDeclareMulligan.log.any (fun s => mentions s "will take a mulligan")

def afterChandraBottomsBothMulligan : Game :=
  let id := (afterBothDeclareMulligan.player ⟨0⟩).hand[0]!
  mustApply afterBothDeclareMulligan ⟨0⟩ (.putOnBottom #[id])

#guard afterChandraBottomsBothMulligan.pending == .putOnBottom ⟨1⟩ 1
#guard afterChandraBottomsBothMulligan.actor == some ⟨1⟩
#guard (afterChandraBottomsBothMulligan.player ⟨0⟩).hand.size == 6
#guard (afterChandraBottomsBothMulligan.player ⟨1⟩).hand.size == 7

#guard started.pending == .none
#guard (started.player ⟨0⟩).keptOpeningHand
#guard (started.player ⟨1⟩).keptOpeningHand

-- Lands cannot be played before opening hands are kept.
#guard
  match drawnHands.apply ⟨0⟩ (.playLand (drawnHands.player ⟨0⟩).hand[0]!) with
  | .error _ => true
  | .ok _ => false

-- Nissa cannot declare before Chandra in the first round.
#guard
  match drawnHands.apply ⟨1⟩ .takeMulligan with
  | .error msg => mentions msg "not your turn"
  | .ok _ => false

#guard
  match started.apply ⟨0⟩ .takeMulligan with
  | .error msg => mentions msg "Not time to take a mulligan"
  | .ok _ => false

#guard
  match afterChandraMulligan.apply ⟨0⟩ (.putOnBottom #[]) with
  | .error msg => mentions msg "exactly 1"
  | .ok _ => false

#guard
  match afterChandraMulligan.apply ⟨0⟩ (.putOnBottom #[⟨99999⟩]) with
  | .error msg => msg == "no such object"
  | .ok _ => false

/-- The seventh mulligan leaves a zero-card hand; further mulligans are illegal. -/
def seventhMulligan : Game :=
  let g := drawnHands.modifyPlayer ⟨0⟩ (fun pl => { pl with mulligansTaken := 6 })
  let g := mustApply g ⟨0⟩ .takeMulligan
  mustApply g ⟨1⟩ .keep

#guard seventhMulligan.pending == .putOnBottom ⟨0⟩ 7

def afterZeroHand : Game :=
  mustApply seventhMulligan ⟨0⟩ (.putOnBottom (seventhMulligan.player ⟨0⟩).hand)

#guard (afterZeroHand.player ⟨0⟩).hand.size == 0
#guard (afterZeroHand.player ⟨0⟩).keptOpeningHand
#guard afterZeroHand.pending == .none
#guard afterZeroHand.step == .upkeep

#guard
  let g := drawnHands.modifyPlayer ⟨0⟩ (fun pl => { pl with mulligansTaken := 7 })
  match g.apply ⟨0⟩ .takeMulligan with
  | .error msg => mentions msg "zero cards"
  | .ok _ => false

-- The heuristic keeps opening hands rather than mulliganing.
#guard
  match Agent.choose drawnHands ⟨0⟩ with
  | some .keep => true
  | _ => false

def agentKeepsHands : Game := Agent.play drawnHands 10

#guard (agentKeepsHands.player ⟨0⟩).keptOpeningHand
#guard (agentKeepsHands.player ⟨1⟩).keptOpeningHand
#guard !agentKeepsHands.openingHandsPending
#guard agentKeepsHands.log.any (fun s => mentions s "takes the first turn")

/-- Two untapped Mountains and a Wayfarer's Bauble; a land has already been
played this turn so the agent will activate rather than play another land. -/
def baubleReady : Game :=
  let g := skipTo started .precombatMain 80
  let g := addUntappedLand g mountain
  let g := addUntappedLand g mountain
  let g := addPermanent g wayfarersBauble ⟨0⟩ ⟨0⟩
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })

def baubleSource (g : Game) : GameObject :=
  namedPermanent g "Wayfarer's Bauble"

#guard wayfarersBauble.activatedAbilities.size == 1
#guard wayfarersBauble.manaAbilities.isEmpty
#guard baubleReady.hasPriority ⟨0⟩
#guard baubleReady.canActivate ⟨0⟩ (baubleSource baubleReady)
  (wayfarersBauble.activatedAbilities[0]!)
#guard !(baubleReady.canActivate ⟨1⟩ (baubleSource baubleReady)
  (wayfarersBauble.activatedAbilities[0]!))

-- The heuristic activates the bauble when {2} is available.
#guard
  match Agent.choose baubleReady ⟨0⟩ with
  | some (.activate id 0) => id == (baubleSource baubleReady).id
  | _ => false

def proposedBauble : Game :=
  mustApply baubleReady ⟨0⟩ (.activate (baubleSource baubleReady).id 0)

#guard proposedBauble.pending == .activateManaAbilities ⟨0⟩
#guard proposedBauble.proposedSpell.isSome
#guard
  match proposedBauble.proposedSpell with
  | some prop => prop.kind == .activatedAbility
  | none => false
#guard proposedBauble.stack.size == 1
#guard (proposedBauble.object! proposedBauble.stack.back!.objectId).sourceId ==
  some (baubleSource proposedBauble).id
#guard (namedPermanent proposedBauble "Wayfarer's Bauble").isOnBattlefield
#guard proposedBauble.log.any (fun s => mentions s "begins activating Wayfarer's Bauble")
#guard proposedBauble.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")

-- Opponent cannot activate Chandra's bauble.
#guard
  match baubleReady.activateAbility ⟨1⟩ (baubleSource baubleReady).id 0 with
  | .error _ => true
  | .ok _ => false

-- A land has no non-mana activated ability.
#guard
  match (baubleReady.permanentsOf ⟨0⟩).find? (·.printed.isLand) with
  | none => false
  | some land =>
    match baubleReady.activateAbility ⟨0⟩ land.id 0 with
    | .error msg => mentions msg "has no activated ability"
    | .ok _ => false

def tapNextMana (g : Game) (p : PlayerId) : Game :=
  match (g.manaSources p)[0]? with
  | none => panic! "expected a mana source"
  | some (src, types) =>
    match types[0]? with
    | none => panic! "expected a mana type"
    | some t => mustApply g p (.tapForMana src.id t)

/-- Paying without enough mana reverses the activation (CR 602.2 / 733.1). -/
def reversedBauble : Game :=
  mustApply proposedBauble ⟨0⟩ .pay

#guard reversedBauble.pending == .none
#guard reversedBauble.proposedSpell.isNone
#guard reversedBauble.stack.isEmpty
#guard reversedBauble.hasPriority ⟨0⟩
#guard (namedPermanent reversedBauble "Wayfarer's Bauble").isOnBattlefield
#guard reversedBauble.log.any (fun s => mentions s "the activation is reversed")

def tappedOnceForBauble : Game := tapNextMana proposedBauble ⟨0⟩
def tappedTwiceForBauble : Game := tapNextMana tappedOnceForBauble ⟨0⟩

#guard (tappedTwiceForBauble.player ⟨0⟩).manaPool.canPay (ManaCost.ofGeneric 2)
#guard tappedTwiceForBauble.pending == .activateManaAbilities ⟨0⟩

def paidBauble : Game :=
  mustApply tappedTwiceForBauble ⟨0⟩ .pay

#guard paidBauble.pending == .none
#guard paidBauble.proposedSpell.isNone
#guard paidBauble.hasPriority ⟨0⟩
#guard paidBauble.stack.size == 1
#guard (paidBauble.player ⟨0⟩).manaPool.isEmpty
#guard (paidBauble.player ⟨0⟩).graveyard.any (fun id =>
  (paidBauble.object! id).name == "Wayfarer's Bauble")
#guard !(paidBauble.battlefield.any (fun o => o.name == "Wayfarer's Bauble"))
#guard paidBauble.log.any (fun s => mentions s "sacrifices Wayfarer's Bauble")
#guard paidBauble.log.any (fun s => mentions s "activates Wayfarer's Bauble")

-- The agent pays once the pool covers {2}.
#guard
  match Agent.choose tappedTwiceForBauble ⟨0⟩ with
  | some .pay => true
  | _ => false

def resolvedBauble : Game := passBoth paidBauble

#guard resolvedBauble.stack.isEmpty
#guard (resolvedBauble.battlefield.filter (fun o => o.name == "Mountain")).size == 3
#guard (resolvedBauble.battlefield.filter (fun o =>
  o.name == "Mountain" && o.status.tapped)).size == 3
#guard resolvedBauble.log.any (fun s =>
  mentions s "puts Mountain onto the battlefield tapped")
#guard resolvedBauble.log.any (fun s => mentions s "shuffles their library")

-- Lands put onto the battlefield this way are not a land drop (CR 305.3).
#guard (resolvedBauble.player ⟨0⟩).landsPlayedThisTurn == 1

/-- Snowslope Hunter plus fodder and a known library top, in the precombat main. -/
def hunterReady : Game :=
  let g := skipTo started .precombatMain 80
  let g := addPermanent g snowslopeHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g ragingGoblin ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addUntappedLand g mountain
  let g := addToLibraryTop g lightningBolt ⟨0⟩
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })

def hunterSource (g : Game) : GameObject :=
  namedPermanent g "Snowslope Hunter"

def hunterFodder (g : Game) : GameObject :=
  namedPermanent g "Raging Goblin"

def hunterAbility : ActivatedAbility :=
  snowslopeHunter.activatedAbilities[0]!

#guard snowslopeHunter.activatedAbilities.size == 1
#guard hunterAbility.cost.sacrificeAnotherCreatureOrArtifact
#guard hunterAbility.effect == .exileTopPlayUntilEndOfNextTurn
#guard hunterAbility.onlyDuringYourTurn
#guard hunterAbility.onceEachTurn
#guard !hunterAbility.onlyAsSorcery
#guard hunterReady.canActivate ⟨0⟩ (hunterSource hunterReady) hunterAbility
#guard !(hunterReady.canActivate ⟨1⟩ (hunterSource hunterReady) hunterAbility)
#guard (hunterReady.sacrificeCreatureOrArtifactChoices ⟨0⟩
  (hunterSource hunterReady).id).any (fun o => o.name == "Raging Goblin")

-- The heuristic begins activating the hunter when another creature is available.
#guard
  match Agent.choose hunterReady ⟨0⟩ with
  | some (.activate id 0) => id == (hunterSource hunterReady).id
  | _ => false

def proposedHunter : Game :=
  mustApply hunterReady ⟨0⟩ (.activate (hunterSource hunterReady).id 0)

#guard proposedHunter.pending == .activateManaAbilities ⟨0⟩
#guard proposedHunter.proposedSpell.isSome
#guard proposedHunter.stack.size == 1
#guard (namedPermanent proposedHunter "Raging Goblin").isOnBattlefield
#guard proposedHunter.log.any (fun s => mentions s "begins activating Snowslope Hunter")
#guard proposedHunter.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")

-- Sacrifice is not chosen at `activate`; it comes after `pay`.
#guard
  match proposedHunter.apply ⟨0⟩ (.sacrifice (hunterFodder proposedHunter).id) with
  | .error msg => mentions msg "Not time to sacrifice"
  | .ok _ => false

-- The heuristic pays the empty mana cost next.
#guard
  match Agent.choose proposedHunter ⟨0⟩ with
  | some .pay => true
  | _ => false

def paidHunter : Game :=
  mustApply proposedHunter ⟨0⟩ .pay

#guard
  match paidHunter.pending with
  | .sacrificePermanent p sid =>
    p == ⟨0⟩ && sid == (hunterSource paidHunter).id
  | _ => false
#guard paidHunter.proposedSpell.isSome
#guard (namedPermanent paidHunter "Raging Goblin").isOnBattlefield
#guard paidHunter.log.any (fun s =>
  mentions s "must sacrifice another creature or artifact")

-- Cannot sacrifice the hunter itself, a land, or skip the choice.
#guard
  match paidHunter.apply ⟨0⟩ (.sacrifice (hunterSource paidHunter).id) with
  | .error msg => mentions msg "Can't sacrifice"
  | .ok _ => false

#guard
  match (paidHunter.permanentsOf ⟨0⟩).find? (·.printed.isLand) with
  | none => false
  | some land =>
    match paidHunter.apply ⟨0⟩ (.sacrifice land.id) with
    | .error msg => mentions msg "Can't sacrifice"
    | .ok _ => false

#guard
  match Agent.choose paidHunter ⟨0⟩ with
  | some (.sacrifice id) => id == (hunterFodder paidHunter).id
  | _ => false

def activatedHunter : Game :=
  mustApply paidHunter ⟨0⟩ (.sacrifice (hunterFodder paidHunter).id)

#guard activatedHunter.pending == .none
#guard activatedHunter.proposedSpell.isNone
#guard activatedHunter.hasPriority ⟨0⟩
#guard activatedHunter.stack.size == 1
#guard (activatedHunter.object! activatedHunter.stack.back!.objectId).sourceId ==
  some (hunterSource activatedHunter).id
#guard (namedPermanent activatedHunter "Snowslope Hunter").isOnBattlefield
#guard !(activatedHunter.battlefield.any (fun o => o.name == "Raging Goblin"))
#guard (activatedHunter.player ⟨0⟩).graveyard.any (fun id =>
  (activatedHunter.object! id).name == "Raging Goblin")
#guard (namedPermanent activatedHunter "Snowslope Hunter").status.activationsThisTurn == 1
#guard activatedHunter.log.any (fun s => mentions s "sacrifices Raging Goblin")
#guard activatedHunter.log.any (fun s => mentions s "activates Snowslope Hunter")

/-- Finish activating Snowslope Hunter by paying, then sacrificing `sacName`. -/
def completeHunterActivation (g : Game) (sacName : String) : Game :=
  let g := mustApply g ⟨0⟩ (.activate (hunterSource g).id 0)
  let g := mustApply g ⟨0⟩ .pay
  mustApply g ⟨0⟩ (.sacrifice (namedPermanent g sacName).id)

-- Only once each turn: a second fodder still cannot be spent this turn.
def hunterActivatedOnce : Game :=
  completeHunterActivation hunterReady "Raging Goblin"

#guard
  match hunterActivatedOnce.activateAbility ⟨0⟩ (hunterSource hunterActivatedOnce).id 0 with
  | .error msg => mentions msg "only once each turn"
  | .ok _ => false
#guard !(hunterActivatedOnce.canActivate ⟨0⟩ (hunterSource hunterActivatedOnce) hunterAbility)

def resolvedHunter : Game := passBoth activatedHunter

#guard resolvedHunter.stack.isEmpty
#guard resolvedHunter.objects.any (fun o => o.zone == .exile && o.name == "Lightning Bolt")
#guard resolvedHunter.log.any (fun s =>
  mentions s "exiles Lightning Bolt and may play it until the end of their next turn")

def exiledBolt (g : Game) : GameObject :=
  match g.objects.find? (fun o => o.zone == .exile && o.name == "Lightning Bolt") with
  | some o => o
  | none => panic! "expected Lightning Bolt in exile"

#guard resolvedHunter.mayPlayFromExile ⟨0⟩ (exiledBolt resolvedHunter)
#guard !(resolvedHunter.mayPlayFromExile ⟨1⟩ (exiledBolt resolvedHunter))
#guard resolvedHunter.canCast ⟨0⟩ (exiledBolt resolvedHunter)
#guard !(resolvedHunter.canCast ⟨1⟩ (exiledBolt resolvedHunter))

-- Opponent cannot play the exiled card.
#guard
  match resolvedHunter.castSpell ⟨1⟩ (exiledBolt resolvedHunter).id with
  | .error _ => true
  | .ok _ => false

-- Cast the exiled Lightning Bolt the same turn (CR 701.14).
def proposedExiledBolt : Game :=
  proposeTargeted resolvedHunter ⟨0⟩
    (exiledBolt resolvedHunter).id (Target.player ⟨1⟩)

#guard proposedExiledBolt.pending == .activateManaAbilities ⟨0⟩
#guard !(proposedExiledBolt.objects.any (fun o => o.zone == .exile && o.name == "Lightning Bolt"))
#guard proposedExiledBolt.log.any (fun s => mentions s "begins casting Lightning Bolt")

def paidExiledBolt : Game :=
  mustApply (tapNextMana proposedExiledBolt ⟨0⟩) ⟨0⟩ .pay

def resolvedExiledBolt : Game := passBoth paidExiledBolt

#guard resolvedExiledBolt.stack.isEmpty
#guard (resolvedExiledBolt.player ⟨1⟩).life == 17
#guard resolvedExiledBolt.log.any (fun s => mentions s "is dealt 3 damage")
#guard !(resolvedExiledBolt.objects.any (fun o => o.zone == .exile && o.name == "Lightning Bolt"))

-- Playing an exiled land uses the land drop.
def hunterLandReady : Game :=
  let g := skipTo started .precombatMain 80
  let g := addPermanent g snowslopeHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g ragingGoblin ⟨0⟩ ⟨0⟩
  addToLibraryTop g mountain ⟨0⟩

def resolvedHunterLand : Game :=
  passBoth (completeHunterActivation hunterLandReady "Raging Goblin")

def exiledMountain (g : Game) : GameObject :=
  match g.objects.find? (fun o => o.zone == .exile && o.name == "Mountain") with
  | some o => o
  | none => panic! "expected Mountain in exile"

#guard resolvedHunterLand.mayPlayFromExile ⟨0⟩ (exiledMountain resolvedHunterLand)
#guard resolvedHunterLand.canPlayLand ⟨0⟩

def playedExiledLand : Game :=
  mustApply resolvedHunterLand ⟨0⟩ (.playLand (exiledMountain resolvedHunterLand).id)

#guard (playedExiledLand.player ⟨0⟩).landsPlayedThisTurn == 1
#guard playedExiledLand.battlefield.any (fun o => o.name == "Mountain")
#guard playedExiledLand.log.any (fun s => mentions s "plays Mountain")
#guard !(playedExiledLand.objects.any (fun o => o.zone == .exile && o.name == "Mountain"))

-- Activate only during your turn: Chandra has priority on Nissa's turn.
def hunterOnNissaTurn : Game :=
  let g := skipTo hunterReady .end 80
  let g := passBoth g
  let g := skipTo g .precombatMain 80
  mustApply g ⟨1⟩ .pass

#guard hunterOnNissaTurn.activePlayer == ⟨1⟩
#guard hunterOnNissaTurn.hasPriority ⟨0⟩
#guard
  match hunterOnNissaTurn.activateAbility ⟨0⟩ (hunterSource hunterOnNissaTurn).id 0 with
  | .error msg => mentions msg "only during your turn"
  | .ok _ => false

-- Instant-speed: the hunter can activate during the end step of your turn.
def hunterAtEndStep : Game := skipTo hunterReady .end 80

#guard hunterAtEndStep.step == .end
#guard hunterAtEndStep.canActivate ⟨0⟩ (hunterSource hunterAtEndStep) hunterAbility

-- Permission lasts through the next turn, then expires.
def hunterPermissionActive : Game :=
  let g := skipTo resolvedHunter .end 80
  let g := passBoth g
  skipTo g .precombatMain 80

#guard hunterPermissionActive.activePlayer == ⟨1⟩
#guard hunterPermissionActive.mayPlayFromExile ⟨0⟩ (exiledBolt hunterPermissionActive)

def hunterOnNextTurn : Game :=
  let g := skipTo hunterPermissionActive .end 80
  let g := passBoth g
  skipTo g .precombatMain 80

#guard hunterOnNextTurn.activePlayer == ⟨0⟩
#guard hunterOnNextTurn.mayPlayFromExile ⟨0⟩ (exiledBolt hunterOnNextTurn)
#guard hunterOnNextTurn.canActivate ⟨0⟩ (hunterSource hunterOnNextTurn) hunterAbility

def hunterActivatedNextTurn : Game :=
  completeHunterActivation hunterOnNextTurn "Gray Ogre"

#guard hunterActivatedNextTurn.log.any (fun s => mentions s "activates Snowslope Hunter")
#guard hunterActivatedNextTurn.log.any (fun s => mentions s "sacrifices Gray Ogre")

def hunterPermissionExpired : Game :=
  let g := skipTo hunterOnNextTurn .end 80
  let g := passBoth g
  let g := skipTo g .precombatMain 80
  mustApply g ⟨1⟩ .pass

#guard hunterPermissionExpired.activePlayer == ⟨1⟩
#guard hunterPermissionExpired.hasPriority ⟨0⟩
#guard hunterPermissionExpired.log.any (fun s =>
  mentions s "can no longer be played from exile")
#guard
  match hunterPermissionExpired.objects.find? (fun o =>
    o.zone == .exile && o.name == "Lightning Bolt") with
  | none => false
  | some o => !hunterPermissionExpired.mayPlayFromExile ⟨0⟩ o
#guard
  match hunterPermissionExpired.objects.find? (fun o =>
    o.zone == .exile && o.name == "Lightning Bolt") with
  | none => false
  | some o =>
    match hunterPermissionExpired.castSpell ⟨0⟩ o.id with
    | .error msg => mentions msg "may not play that card from exile"
    | .ok _ => false

-- Empty library: the ability still resolves.
def hunterEmptyLibrary : Game :=
  let g := skipTo started .precombatMain 80
  let g := addPermanent g snowslopeHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g ragingGoblin ⟨0⟩ ⟨0⟩
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with library := #[] })

def resolvedHunterEmpty : Game :=
  passBoth (completeHunterActivation hunterEmptyLibrary "Raging Goblin")

#guard resolvedHunterEmpty.stack.isEmpty
#guard resolvedHunterEmpty.log.any (fun s => mentions s "no cards in their library to exile")
#guard !(resolvedHunterEmpty.objects.any (fun o => o.zone == .exile))

/-- Orcish Siegemaster grants trample to other Orcs and Goblins you control. -/
def siegeAndGoblin : Game :=
  addPermanent (addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩) ragingGoblin ⟨0⟩ ⟨0⟩

def siegeAndOgre : Game :=
  addPermanent (addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩) grayOgre ⟨0⟩ ⟨0⟩

def siegeAndOppGoblin : Game :=
  addPermanent (addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩) ragingGoblin ⟨1⟩ ⟨1⟩

#guard siegeAndGoblin.hasTrample (namedPermanent siegeAndGoblin "Orcish Siegemaster")
#guard siegeAndGoblin.hasTrample (namedPermanent siegeAndGoblin "Raging Goblin")
#guard (siegeAndGoblin.effectiveKeywords (namedPermanent siegeAndGoblin "Raging Goblin")).trample
#guard (siegeAndGoblin.effectiveKeywords (namedPermanent siegeAndGoblin "Raging Goblin")).haste
#guard !withGoblin.hasTrample (lastPermanent withGoblin)
#guard !siegeAndOgre.hasTrample (namedPermanent siegeAndOgre "Gray Ogre")
#guard !siegeAndOppGoblin.hasTrample (namedPermanent siegeAndOppGoblin "Raging Goblin")

/-- Snowslope Hunter (a Goblin) trampling over Llanowar Elves. -/
def siegeHunterVsElves : Game :=
  let g := addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩
  let g := addPermanent g snowslopeHunter ⟨0⟩ ⟨0⟩
  addPermanent g llanowarElves ⟨1⟩ ⟨1⟩

def hunterGrantedTrampleAttack : Game :=
  let g := passBoth (skipTo siegeHunterVsElves .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Snowslope Hunter").id])

def hunterGrantedTrampleBlocked : Game :=
  let g := passBoth hunterGrantedTrampleAttack
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Snowslope Hunter").id)])

def afterGrantedTrample : Game := passBoth hunterGrantedTrampleBlocked

#guard afterGrantedTrample.log.any (fun s =>
  mentions s "Snowslope Hunter deals 1 combat damage to Llanowar Elves")
#guard afterGrantedTrample.log.any (fun s =>
  mentions s "Snowslope Hunter tramples for 1 to Nissa")
#guard (afterGrantedTrample.player ⟨1⟩).life == 19

/-- Without the Siegemaster, the same Goblin assigns all damage to the blocker. -/
def hunterOnlyVsElves : Game :=
  addPermanent (addPermanent started snowslopeHunter ⟨0⟩ ⟨0⟩) llanowarElves ⟨1⟩ ⟨1⟩

def afterHunterNoTrample : Game :=
  let g := passBoth (skipTo hunterOnlyVsElves .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Snowslope Hunter").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Snowslope Hunter").id)])
  passBoth g

#guard afterHunterNoTrample.log.any (fun s =>
  mentions s "Snowslope Hunter deals 2 combat damage to Llanowar Elves")
#guard !afterHunterNoTrample.log.any (fun s => mentions s "tramples")
#guard (afterHunterNoTrample.player ⟨1⟩).life == 20

/-- A non-Orc, non-Goblin does not receive the grant. -/
def siegeOgreVsElves : Game :=
  let g := addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  addPermanent g llanowarElves ⟨1⟩ ⟨1⟩

def afterOgreNoTrample : Game :=
  let g := passBoth (skipTo siegeOgreVsElves .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Gray Ogre").id)])
  passBoth g

#guard afterOgreNoTrample.log.any (fun s =>
  mentions s "Gray Ogre deals 2 combat damage to Llanowar Elves")
#guard !afterOgreNoTrample.log.any (fun s => mentions s "tramples")

/-- Attack trigger: +X/+0 where X is the greatest power among creatures you control. -/
def siegeGiantVsBears : Game :=
  let g := addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
  addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩

def siegeAttackDeclared : Game :=
  let g := passBoth (skipTo siegeGiantVsBears .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Orcish Siegemaster").id])

#guard siegeAttackDeclared.stack.size == 1
#guard (siegeAttackDeclared.object! siegeAttackDeclared.stack.back!.objectId).name ==
  "Orcish Siegemaster's ability"
#guard (siegeAttackDeclared.object! siegeAttackDeclared.stack.back!.objectId).sourceId ==
  some (namedPermanent siegeAttackDeclared "Orcish Siegemaster").id
#guard siegeAttackDeclared.log.any (fun s => mentions s "attack trigger is put on the stack")
#guard (namedPermanent siegeAttackDeclared "Orcish Siegemaster").power == 0
#guard siegeAttackDeclared.step == .declareAttackers
#guard siegeAttackDeclared.hasPriority ⟨0⟩

def siegePumpResolved : Game := passBoth siegeAttackDeclared

#guard siegePumpResolved.stack.isEmpty
#guard (namedPermanent siegePumpResolved "Orcish Siegemaster").power == 3
#guard siegePumpResolved.log.any (fun s => mentions s "gets +3/+0 until end of turn")
#guard siegePumpResolved.step == .declareAttackers

def siegeReadyToBlock : Game := passBoth siegePumpResolved

#guard siegeReadyToBlock.pending == .declareBlockers

def siegeBlocked : Game :=
  let g := siegeReadyToBlock
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Orcish Siegemaster").id)])

def afterSiegeCombat : Game := passBoth siegeBlocked

#guard afterSiegeCombat.log.any (fun s =>
  mentions s "Orcish Siegemaster deals 2 combat damage to Grizzly Bears")
#guard afterSiegeCombat.log.any (fun s =>
  mentions s "Orcish Siegemaster tramples for 1 to Nissa")
#guard (afterSiegeCombat.player ⟨1⟩).life == 19

/-- Alone, X is the Siegemaster's own power (0). -/
def siegeAloneResolved : Game :=
  let g := addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Orcish Siegemaster").id])
  passBoth g

#guard (namedPermanent siegeAloneResolved "Orcish Siegemaster").power == 0
#guard siegeAloneResolved.log.any (fun s => mentions s "gets +0/+0 until end of turn")

/-- Opponent creatures do not count toward X. -/
def siegeVsWurmResolved : Game :=
  let g := addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩
  let g := addPermanent g crawWurm ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Orcish Siegemaster").id])
  passBoth g

#guard (namedPermanent siegeVsWurmResolved "Orcish Siegemaster").power == 0

/-- X uses current power, including until-end-of-turn pumps. -/
def siegePumpedGiantResolved : Game :=
  let g := addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨0⟩ ⟨0⟩
  let g := g.applyEffect ⟨0⟩ (.pump 2 0)
    #[Target.permanent (namedPermanent g "Hill Giant").id]
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Orcish Siegemaster").id])
  passBoth g

#guard (namedPermanent siegePumpedGiantResolved "Hill Giant").power == 5
#guard (namedPermanent siegePumpedGiantResolved "Orcish Siegemaster").power == 5
#guard siegePumpedGiantResolved.log.any (fun s => mentions s "gets +5/+0 until end of turn")

/-- If the source leaves before the trigger resolves, the pump does not happen. -/
def siegeSourceGone : Game :=
  let g := siegeAttackDeclared
  let id := (namedPermanent g "Orcish Siegemaster").id
  let (g, _) := g.move id (.graveyard (g.object! id).owner) none
  passBoth g

#guard siegeSourceGone.stack.isEmpty
#guard !(siegeSourceGone.battlefield.any (fun o => o.name == "Orcish Siegemaster"))
#guard siegeSourceGone.log.any (fun s => mentions s "source is no longer in play")
#guard (namedPermanent siegeSourceGone "Hill Giant").status.pumpPower == 0

/-- The +X/+0 wears off in cleanup. -/
def afterSiegeCleanup : Game := passBoth (skipTo siegePumpResolved .end 80)

#guard (namedPermanent afterSiegeCleanup "Orcish Siegemaster").power == 0
#guard (namedPermanent afterSiegeCleanup "Orcish Siegemaster").status.pumpPower == 0

/-- Printed trample still assigns leftover damage (Beorn 5/5 vs Grizzly Bears 2/2). -/
def afterBeornTrample : Game :=
  let g := addPermanent (addPermanent started beornReluctantHost ⟨0⟩ ⟨0⟩)
    grizzlyBears ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Beorn, Reluctant Host").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Beorn, Reluctant Host").id)])
  passBoth g

#guard afterBeornTrample.log.any (fun s =>
  mentions s "Beorn, Reluctant Host deals 2 combat damage to Grizzly Bears")
#guard afterBeornTrample.log.any (fun s =>
  mentions s "Beorn, Reluctant Host tramples for 3 to Nissa")
#guard (afterBeornTrample.player ⟨1⟩).life == 17

/-- Battle-Scarred Goblin vs Grizzly Bears: becomes-blocked trigger, then combat. -/
def goblinVsBears : Game :=
  addPermanent (addPermanent started battleScarredGoblin ⟨0⟩ ⟨0⟩) grizzlyBears ⟨1⟩ ⟨1⟩

def goblinDeclaredAttacker : Game :=
  let g := passBoth (skipTo goblinVsBears .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Battle-Scarred Goblin").id])

def goblinReadyToBlock : Game := passBoth goblinDeclaredAttacker

def goblinBlockedByBears : Game :=
  let g := goblinReadyToBlock
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Battle-Scarred Goblin").id)])

#guard goblinBlockedByBears.stack.size == 1
#guard (goblinBlockedByBears.object! goblinBlockedByBears.stack.back!.objectId).name ==
  "Battle-Scarred Goblin's ability"
#guard (goblinBlockedByBears.object! goblinBlockedByBears.stack.back!.objectId).sourceId ==
  some (namedPermanent goblinBlockedByBears "Battle-Scarred Goblin").id
#guard goblinBlockedByBears.log.any (fun s => mentions s "becomes-blocked trigger is put on the stack")
#guard (namedPermanent goblinBlockedByBears "Battle-Scarred Goblin").status.blocked
#guard goblinBlockedByBears.step == .declareBlockers
#guard goblinBlockedByBears.hasPriority ⟨0⟩
#guard (namedPermanent goblinBlockedByBears "Grizzly Bears").status.damage == 0

def goblinTriggerResolved : Game := passBoth goblinBlockedByBears

#guard goblinTriggerResolved.stack.isEmpty
#guard (namedPermanent goblinTriggerResolved "Grizzly Bears").status.damage == 1
#guard goblinTriggerResolved.log.any (fun s =>
  mentions s "Battle-Scarred Goblin deals 1 damage to Grizzly Bears")
#guard goblinTriggerResolved.step == .declareBlockers
#guard goblinTriggerResolved.battlefield.any (fun o => o.name == "Grizzly Bears")
#guard (goblinTriggerResolved.player ⟨1⟩).life == 20

def afterGoblinBearsCombat : Game := passBoth goblinTriggerResolved

#guard afterGoblinBearsCombat.log.any (fun s =>
  mentions s "Battle-Scarred Goblin deals 2 combat damage to Grizzly Bears")
#guard afterGoblinBearsCombat.log.any (fun s =>
  mentions s "Grizzly Bears deals 2 combat damage to Battle-Scarred Goblin")
#guard (afterGoblinBearsCombat.player ⟨1⟩).life == 20
#guard !(afterGoblinBearsCombat.battlefield.any (fun o => o.name == "Battle-Scarred Goblin"))
#guard !(afterGoblinBearsCombat.battlefield.any (fun o => o.name == "Grizzly Bears"))

/-- A 1/1 blocker dies to the trigger; the Goblin stays blocked and assigns no
combat damage (CR 509.1h / 510.1c). -/
def goblinVsElves : Game :=
  addPermanent (addPermanent started battleScarredGoblin ⟨0⟩ ⟨0⟩) llanowarElves ⟨1⟩ ⟨1⟩

def goblinBlockedByElves : Game :=
  let g := passBoth (skipTo goblinVsElves .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Battle-Scarred Goblin").id])
  let g := passBoth g
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Battle-Scarred Goblin").id)])

def goblinElvesAfterTrigger : Game := passBoth goblinBlockedByElves

#guard goblinElvesAfterTrigger.stack.isEmpty
#guard goblinElvesAfterTrigger.log.any (fun s =>
  mentions s "Battle-Scarred Goblin deals 1 damage to Llanowar Elves")
#guard goblinElvesAfterTrigger.log.any (fun s => mentions s "Llanowar Elves dies from lethal damage")
#guard !(goblinElvesAfterTrigger.battlefield.any (fun o => o.name == "Llanowar Elves"))
#guard goblinElvesAfterTrigger.objects.any (fun o =>
  o.name == "Llanowar Elves" && o.zone == .graveyard ⟨1⟩)
#guard (namedPermanent goblinElvesAfterTrigger "Battle-Scarred Goblin").status.blocked
#guard goblinElvesAfterTrigger.step == .declareBlockers
#guard (goblinElvesAfterTrigger.player ⟨1⟩).life == 20

def afterGoblinElvesCombat : Game := passBoth goblinElvesAfterTrigger

#guard afterGoblinElvesCombat.log.any (fun s =>
  mentions s "blocked with no remaining blockers and assigns no combat damage")
#guard !afterGoblinElvesCombat.log.any (fun s => mentions s "combat damage to Nissa")
#guard (afterGoblinElvesCombat.player ⟨1⟩).life == 20
#guard afterGoblinElvesCombat.battlefield.any (fun o => o.name == "Battle-Scarred Goblin")
#guard (namedPermanent afterGoblinElvesCombat "Battle-Scarred Goblin").status.damage == 0

/-- Unblocked: the trigger does not fire, and combat damage hits the player. -/
def afterGoblinUnblocked : Game :=
  passBoth (mustApply goblinReadyToBlock ⟨1⟩ (.declareBlockers #[]))

#guard afterGoblinUnblocked.stack.isEmpty
#guard !afterGoblinUnblocked.log.any (fun s => mentions s "becomes-blocked trigger")
#guard (afterGoblinUnblocked.player ⟨1⟩).life == 18
#guard afterGoblinUnblocked.log.any (fun s =>
  mentions s "Battle-Scarred Goblin deals 2 combat damage to Nissa")

/-- CR 509.5c: two blockers still produce one trigger; each takes 1 damage. -/
def goblinVsTwoElves : Game :=
  let g := addPermanent started battleScarredGoblin ⟨0⟩ ⟨0⟩
  let g := addPermanent g llanowarElves ⟨1⟩ ⟨1⟩
  addPermanent g llanowarElves ⟨1⟩ ⟨1⟩

def goblinBlockedByTwoElves : Game :=
  let g := passBoth (skipTo goblinVsTwoElves .beginningOfCombat 80)
  let goblin := namedPermanent g "Battle-Scarred Goblin"
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  let g := mustApply g ⟨0⟩ (.declareAttackers #[goblin.id])
  let g := passBoth g
  mustApply g ⟨1⟩ (.declareBlockers #[(elves[0]!.id, goblin.id), (elves[1]!.id, goblin.id)])

#guard goblinBlockedByTwoElves.stack.size == 1
#guard (goblinBlockedByTwoElves.battlefield.filter (fun o =>
  !o.status.blocking.isEmpty)).size == 2

def goblinTwoElvesAfterTrigger : Game := passBoth goblinBlockedByTwoElves

#guard (goblinTwoElvesAfterTrigger.log.filter (fun s =>
  mentions s "Battle-Scarred Goblin deals 1 damage to Llanowar Elves")).size == 2
#guard (goblinTwoElvesAfterTrigger.battlefield.filter (fun o =>
  o.name == "Llanowar Elves")).isEmpty
#guard (goblinTwoElvesAfterTrigger.objects.filter (fun o =>
  o.name == "Llanowar Elves" && o.zone == .graveyard ⟨1⟩)).size == 2

/-- Two Goblins, one blocked: only the blocked one triggers. -/
def twoGoblinsOneBlocked : Game :=
  let g := addPermanent started battleScarredGoblin ⟨0⟩ ⟨0⟩
  let g := addPermanent g battleScarredGoblin ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let goblins := g.battlefield.filter (fun o => o.name == "Battle-Scarred Goblin")
  let g := mustApply g ⟨0⟩ (.declareAttackers (goblins.map (·.id)))
  let g := passBoth g
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    goblins[0]!.id)])

#guard twoGoblinsOneBlocked.stack.size == 1
#guard (twoGoblinsOneBlocked.battlefield.filter (fun o =>
  o.name == "Battle-Scarred Goblin" && o.status.blocked)).size == 1
#guard (twoGoblinsOneBlocked.battlefield.filter (fun o =>
  o.name == "Battle-Scarred Goblin" && o.status.attacking && !o.status.blocked)).size == 1

/-- If the source leaves before the trigger resolves, blockers are unharmed. -/
def goblinSourceGone : Game :=
  let g := goblinBlockedByBears
  let id := (namedPermanent g "Battle-Scarred Goblin").id
  let (g, _) := g.move id (.graveyard (g.object! id).owner) none
  passBoth g

#guard goblinSourceGone.stack.isEmpty
#guard goblinSourceGone.log.any (fun s => mentions s "source is no longer in play")
#guard (namedPermanent goblinSourceGone "Grizzly Bears").status.damage == 0

/-- Granted trample plus a killed 1/1 blocker: leftover damage goes to the player
(CR 702.19d). -/
def siegeGoblinVsElves : Game :=
  let g := addPermanent started orcishSiegemaster ⟨0⟩ ⟨0⟩
  let g := addPermanent g battleScarredGoblin ⟨0⟩ ⟨0⟩
  addPermanent g llanowarElves ⟨1⟩ ⟨1⟩

def afterSiegeGoblinElves : Game :=
  let g := passBoth (skipTo siegeGoblinVsElves .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Battle-Scarred Goblin").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Battle-Scarred Goblin").id)])
  let g := passBoth g
  passBoth g

#guard afterSiegeGoblinElves.log.any (fun s =>
  mentions s "Battle-Scarred Goblin deals 1 damage to Llanowar Elves")
#guard afterSiegeGoblinElves.log.any (fun s => mentions s "Llanowar Elves dies from lethal damage")
#guard afterSiegeGoblinElves.log.any (fun s =>
  mentions s "Battle-Scarred Goblin tramples for 2 to Nissa")
#guard (afterSiegeGoblinElves.player ⟨1⟩).life == 18
#guard afterSiegeGoblinElves.battlefield.any (fun o => o.name == "Battle-Scarred Goblin")

/-- Fill `p`'s mana pool with `n` mana of color `c`. -/
def withMana (g : Game) (p : PlayerId) (c : Color) (n : Nat := 4) : Game :=
  g.modifyPlayer p (fun pl => { pl with manaPool := pl.manaPool.add (.colored c) n })

/-- Fill `p`'s mana pool with `n` green mana. -/
def withGreenMana (g : Game) (p : PlayerId) (n : Nat := 4) : Game :=
  withMana g p .green n

/-- Fill `p`'s mana pool with `n` red mana. -/
def withRedMana (g : Game) (p : PlayerId) (n : Nat := 4) : Game :=
  withMana g p .red n

/-- Fill `p`'s mana pool with `n` black mana. -/
def withBlackMana (g : Game) (p : PlayerId) (n : Nat := 4) : Game :=
  withMana g p .black n

/-- Empty `p`'s hand and mark a land already played this turn. -/
def clearHandPlayedLand (g : Game) (p : PlayerId) : Game :=
  g.modifyPlayer p (fun pl => { pl with hand := #[], landsPlayedThisTurn := 1 })

/-- Pay the proposed spell or ability, then both players pass (resolve). -/
def payAndResolve (g : Game) (p : PlayerId) : Game :=
  passBoth (mustApply g p .pay)

/-- Keep the first listed legendary permanent in a CR 704.5j choice. -/
def keepFirstLegend (g : Game) : Game :=
  match g.pending with
  | .chooseLegend p _ ids => mustApply g p (.keepLegend ids[0]!)
  | _ => panic! "expected a legend-rule choice"

/-- Put `aura` onto the battlefield already attached to `host`. -/
def addAttachedAura (g : Game) (aura : CardDef) (host : GameObject)
    (owner controller : PlayerId) : Game :=
  let (g, _) := g.allocObject aura owner .battlefield (some controller)
    (attachedTo := some host.id)
  g

/-- Keep the looked-at cards on top in their current order (CR 701.20). -/
def keepScry (g : Game) : Game :=
  match g.pending with
  | .scry p n => mustApply g p (.scry (g.scryLookedIds p n) #[])
  | _ => panic! "expected a pending scry"

/-- Gift of Strands in hand, Grizzly Bears on the battlefield, enough mana. -/
def giftSetup : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  withGreenMana (addToHand g giftOfStrands ⟨0⟩) ⟨0⟩

#guard giftSetup.canCast ⟨0⟩ (handCardNamed giftSetup ⟨0⟩ "Gift of Strands")
#guard giftSetup.asSorcery? ⟨0⟩
#guard giftOfStrands.keywords.flash
#guard !giftOfStrands.hasSorcerySpeed

-- An Aura cannot be cast with no creature on the battlefield.
#guard
  let g := withGreenMana (addToHand afterDraw giftOfStrands ⟨0⟩) ⟨0⟩
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Gift of Strands")
#guard
  let g := withGreenMana (addToHand afterDraw giftOfStrands ⟨0⟩) ⟨0⟩
  match g.apply ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Gift of Strands").id) with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

-- Cast proposes the Aura; the target is announced as a later action (CR 601.2c).
#guard
  match giftSetup.apply ⟨0⟩ (.cast (handCardNamed giftSetup ⟨0⟩ "Gift of Strands").id) with
  | .ok g' =>
    match g'.pending with
    | .chooseTargets ⟨0⟩ => g'.stack.back!.targets.isEmpty
    | _ => false
  | .error _ => false

def proposedGift : Game :=
  proposeTargeted giftSetup ⟨0⟩
    (handCardNamed giftSetup ⟨0⟩ "Gift of Strands").id
    (Target.permanent (namedPermanent giftSetup "Grizzly Bears").id)

#guard proposedGift.pending == .activateManaAbilities ⟨0⟩
#guard proposedGift.stack.back!.targets ==
  #[Target.permanent (namedPermanent giftSetup "Grizzly Bears").id]
#guard proposedGift.log.any (fun s => mentions s "chooses Grizzly Bears as a target (CR 601.2c)")

def paidGift : Game := mustApply proposedGift ⟨0⟩ .pay

#guard paidGift.stack.size == 1
#guard paidGift.hasPriority ⟨0⟩

/-- The Aura enters attached and the creature is immediately +3/+3; scry waits on the stack. -/
def giftEntered : Game := passBoth paidGift

#guard (namedPermanent giftEntered "Gift of Strands").attachedTo ==
  some (namedPermanent giftEntered "Grizzly Bears").id
#guard giftEntered.power (namedPermanent giftEntered "Grizzly Bears") == 5
#guard giftEntered.toughness (namedPermanent giftEntered "Grizzly Bears") == 5
#guard (namedPermanent giftEntered "Grizzly Bears").power == 2
#guard giftEntered.stack.size == 1
#guard giftEntered.log.any (fun s => mentions s "attached to Grizzly Bears")
#guard giftEntered.log.any (fun s => mentions s "enters trigger is put on the stack")

def giftScrying : Game := passBoth giftEntered

#guard
  match giftScrying.pending with
  | .scry ⟨0⟩ 2 => true
  | _ => false
#guard giftScrying.actor == some ⟨0⟩
#guard !giftScrying.hasPriority ⟨0⟩
#guard giftScrying.log.any (fun s => mentions s "scries 2")
#guard giftScrying.stack.isEmpty

def giftScried : Game := keepScry giftScrying

#guard giftScried.pending == .none
#guard giftScried.hasPriority ⟨0⟩
#guard giftScried.power (namedPermanent giftScried "Grizzly Bears") == 5

-- The agent keeps scried cards on top.
#guard
  match Agent.choose giftScrying ⟨0⟩ with
  | some (.scry top bottom) =>
    bottom.isEmpty && top == giftScrying.scryLookedIds ⟨0⟩ 2
  | _ => false

/-- Put the current top card on the bottom; the next stays on top. -/
def giftKnownLib : Game :=
  addToLibraryTop (addToLibraryTop giftEntered forest ⟨0⟩) llanowarElves ⟨0⟩

def giftKnownScrying : Game := passBoth giftKnownLib

def giftBottomedElves : Game :=
  let looked := giftKnownScrying.scryLookedIds ⟨0⟩ 2
  -- looked is [Forest, Llanowar Elves] with Elves on top.
  mustApply giftKnownScrying ⟨0⟩ (.scry looked.pop #[looked.back!])

#guard (giftBottomedElves.object! (giftBottomedElves.player ⟨0⟩).library.back!).name == "Forest"
#guard (giftBottomedElves.object! (giftBottomedElves.player ⟨0⟩).library[0]!).name ==
  "Llanowar Elves"
#guard giftBottomedElves.log.any (fun s =>
  mentions s "puts Llanowar Elves on the bottom of their library")

/-- The rest may be put on top in any order (CR 701.20). -/
def giftReorderedTop : Game :=
  let looked := giftKnownScrying.scryLookedIds ⟨0⟩ 2
  -- Reverse the two looked-at cards: Forest becomes the new top.
  mustApply giftKnownScrying ⟨0⟩ (.scry looked.reverse #[])

#guard (giftReorderedTop.object! (giftReorderedTop.player ⟨0⟩).library.back!).name == "Forest"
#guard
  let lib := (giftReorderedTop.player ⟨0⟩).library
  (giftReorderedTop.object! lib[lib.size - 2]!).name == "Llanowar Elves"
#guard giftReorderedTop.log.any (fun s => mentions s "puts Forest on top of their library")
#guard giftReorderedTop.log.any (fun s =>
  mentions s "puts Llanowar Elves on top of their library")
#guard !(giftReorderedTop.log.any (fun s => mentions s "on the bottom of their library"))

/-- The +3/+3 is a continuous effect, so it does not wear off in cleanup. -/
def afterGiftCleanup : Game := passBoth (skipTo giftScried .end 80)

#guard afterGiftCleanup.power (namedPermanent afterGiftCleanup "Grizzly Bears") == 5
#guard (namedPermanent afterGiftCleanup "Grizzly Bears").status.pumpPower == 0

/-- If the target leaves before the Aura resolves, the Aura goes to the graveyard (CR 608.3a). -/
def giftTargetGone : Game :=
  let id := (namedPermanent paidGift "Grizzly Bears").id
  let (g, _) := paidGift.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard !(giftTargetGone.battlefield.any (fun o => o.name == "Gift of Strands"))
#guard giftTargetGone.log.any (fun s => mentions s "illegal Aura target")
#guard (giftTargetGone.player ⟨0⟩).graveyard.any (fun id =>
  (giftTargetGone.object! id).name == "Gift of Strands")

/-- If the enchanted creature leaves, the Aura becomes unattached and SBA 704.5n puts it
in the graveyard. -/
def afterHostLeaves : Game :=
  let id := (namedPermanent giftScried "Grizzly Bears").id
  let (g, _) := giftScried.move id (.graveyard ⟨0⟩) none
  g.checkSBA

#guard afterHostLeaves.log.any (fun s => mentions s "becomes unattached")
#guard afterHostLeaves.log.any (fun s => mentions s "704.5n")
#guard !(afterHostLeaves.battlefield.any (fun o => o.name == "Gift of Strands"))
#guard !(afterHostLeaves.battlefield.any (fun o => o.name == "Grizzly Bears"))

/- Legend rule (CR 704.5j). -/

def twoBofurs : Game :=
  addPermanent (addPermanent started bofurReliableGuardian ⟨0⟩ ⟨0⟩)
    bofurReliableGuardian ⟨0⟩ ⟨0⟩

def twoBofursSBA : Game := twoBofurs.checkSBA

#guard (namedPermanent twoBofurs "Bofur, Reliable Guardian").isLegendary
#guard (twoBofurs.battlefield.filter (·.name == "Bofur, Reliable Guardian")).size == 2
#guard twoBofurs.pending == .none
#guard twoBofurs.firstLegendRuleChoice?.isSome
#guard
  match twoBofursSBA.pending with
  | .chooseLegend p name ids =>
    p == ⟨0⟩ && name == "Bofur, Reliable Guardian" && ids.size == 2
  | _ => false
#guard twoBofursSBA.actor == some ⟨0⟩
#guard twoBofursSBA.legendChoicePending?
#guard twoBofursSBA.log.any (fun s => mentions s "704.5j")
#guard (twoBofursSBA.battlefield.filter (·.name == "Bofur, Reliable Guardian")).size == 2

def keptOlderBofur : Game :=
  keepFirstLegend twoBofursSBA

#guard (keptOlderBofur.battlefield.filter (·.name == "Bofur, Reliable Guardian")).size == 1
#guard keptOlderBofur.pending == .none
#guard !keptOlderBofur.legendChoicePending?
#guard keptOlderBofur.log.any (fun s => mentions s "keeps Bofur, Reliable Guardian")
#guard keptOlderBofur.log.any (fun s =>
  mentions s "is put into its owner's graveyard (legend rule, CR 704.5j)")
#guard (keptOlderBofur.player ⟨0⟩).graveyard.any (fun id =>
  (keptOlderBofur.object! id).name == "Bofur, Reliable Guardian")
#guard keptOlderBofur.hasPriority ⟨0⟩

/-- Each player may control a copy of the same legend. -/
def eachControlsBofur : Game :=
  addPermanent (addPermanent started bofurReliableGuardian ⟨0⟩ ⟨0⟩)
    bofurReliableGuardian ⟨1⟩ ⟨1⟩

#guard (eachControlsBofur.checkSBA).pending == .none
#guard (eachControlsBofur.checkSBA.battlefield.filter
  (·.name == "Bofur, Reliable Guardian")).size == 2

/-- Different legendary names do not conflict. -/
def twoDifferentLegends : Game :=
  addPermanent (addPermanent started bofurReliableGuardian ⟨0⟩ ⟨0⟩)
    landrovalHorizonWitness ⟨0⟩ ⟨0⟩

#guard (twoDifferentLegends.checkSBA).pending == .none
#guard (twoDifferentLegends.checkSBA.battlefield.filter (·.isLegendary)).size == 2

/-- Three copies: keep one, two go to the graveyard. -/
def threeBofursSBA : Game :=
  (addPermanent twoBofurs bofurReliableGuardian ⟨0⟩ ⟨0⟩).checkSBA

def keptOneOfThree : Game :=
  match threeBofursSBA.pending with
  | .chooseLegend p _ ids => mustApply threeBofursSBA p (.keepLegend ids[1]!)
  | _ => panic! "expected a legend-rule choice"

#guard (keptOneOfThree.battlefield.filter (·.name == "Bofur, Reliable Guardian")).size == 1
#guard ((keptOneOfThree.player ⟨0⟩).graveyard.filter (fun id =>
  (keptOneOfThree.object! id).name == "Bofur, Reliable Guardian")).size == 2

/-- Indestructible does not save a legend from CR 704.5j. -/
def legendaryIndestructible : CardDef :=
  legendaryCreature "Unyielding Legend" ManaCost.empty #[] 2 2
    (keywords := Keyword.indestructible)

def twoIndestructibleLegends : Game :=
  let g :=
    addPermanent (addPermanent started legendaryIndestructible ⟨0⟩ ⟨0⟩)
      legendaryIndestructible ⟨0⟩ ⟨0⟩
  keepFirstLegend (g.checkSBA)

#guard (twoIndestructibleLegends.battlefield.filter
  (·.name == "Unyielding Legend")).size == 1
#guard (namedPermanent twoIndestructibleLegends "Unyielding Legend").printed.keywords.indestructible
#guard ((twoIndestructibleLegends.player ⟨0⟩).graveyard.filter (fun id =>
  (twoIndestructibleLegends.object! id).name == "Unyielding Legend")).size == 1

/-- The rest go to their owners' graveyards, not the controller's. -/
def nissaControlsTwoBofurs : Game :=
  addPermanent (addPermanent started bofurReliableGuardian ⟨0⟩ ⟨1⟩)
    bofurReliableGuardian ⟨1⟩ ⟨1⟩

def nissaKeepsOwnBofur : Game :=
  let g := nissaControlsTwoBofurs.checkSBA
  match g.pending with
  | .chooseLegend p _ ids => mustApply g p (.keepLegend ids[1]!)
  | _ => panic! "expected a legend-rule choice"

#guard nissaControlsTwoBofurs.checkSBA.actor == some ⟨1⟩
#guard (nissaKeepsOwnBofur.player ⟨0⟩).graveyard.any (fun id =>
  (nissaKeepsOwnBofur.object! id).name == "Bofur, Reliable Guardian")
#guard (nissaKeepsOwnBofur.battlefield.filter (·.name == "Bofur, Reliable Guardian")).size == 1
#guard (namedPermanent nissaKeepsOwnBofur "Bofur, Reliable Guardian").owner == ⟨1⟩

/-- Two legend pairs: after the first choice, the second pair is prompted. -/
def twoLegendPairs : Game :=
  addPermanent (addPermanent twoBofurs landrovalHorizonWitness ⟨0⟩ ⟨0⟩)
    landrovalHorizonWitness ⟨0⟩ ⟨0⟩

def afterFirstLegendPair : Game :=
  let g := twoLegendPairs.checkSBA
  match g.pending with
  | .chooseLegend p name ids =>
    if name == "Bofur, Reliable Guardian" then
      mustApply g p (.keepLegend ids[0]!)
    else panic! s!"expected Bofur first, got {name}"
  | _ => panic! "expected a legend-rule choice"

#guard
  match afterFirstLegendPair.pending with
  | .chooseLegend _ name ids =>
    name == "Landroval, Horizon Witness" && ids.size == 2
  | _ => false

-- The opponent cannot make the legend-rule choice.
#guard
  match twoBofursSBA.pending with
  | .chooseLegend _ _ ids =>
    match twoBofursSBA.apply ⟨1⟩ (.keepLegend ids[0]!) with
    | .error msg => mentions msg "Only Chandra"
    | .ok _ => false
  | _ => false

/-- The heuristic keeps the newest copy. -/
def agentKeptLegend : Game :=
  match Agent.step twoBofursSBA with
  | .ok g => g
  | .error e => panic! e

#guard (agentKeptLegend.battlefield.filter (·.name == "Bofur, Reliable Guardian")).size == 1
#guard agentKeptLegend.pending == .none
#guard
  match twoBofursSBA.pending with
  | .chooseLegend _ _ ids =>
    (namedPermanent agentKeptLegend "Bofur, Reliable Guardian").id ==
      twoBofursSBA.defaultLegendToKeep ids
  | _ => false

/-- An Aura on the discarded legend is put into the graveyard (CR 704.5m). -/
def twoBofursWithAura : Game :=
  let host := (twoBofurs.battlefield.filter
    (·.name == "Bofur, Reliable Guardian"))[0]!
  addAttachedAura twoBofurs giftOfStrands host ⟨0⟩ ⟨0⟩

def afterLegendKillsEnchanted : Game :=
  let g := twoBofursWithAura.checkSBA
  match g.pending with
  | .chooseLegend p _ ids => mustApply g p (.keepLegend ids[1]!)
  | _ => panic! "expected a legend-rule choice"

#guard !(afterLegendKillsEnchanted.battlefield.any (fun o => o.name == "Gift of Strands"))
#guard afterLegendKillsEnchanted.log.any (fun s => mentions s "704.5n")
#guard (afterLegendKillsEnchanted.player ⟨0⟩).graveyard.any (fun id =>
  (afterLegendKillsEnchanted.object! id).name == "Gift of Strands")

-- CR 704.3: a 0-toughness creature dies in the same check, then the legend
-- rule still pauses; no player has priority until the choice is made.
def zeroAndTwoBofursSBA : Game :=
  (addPermanent twoBofurs zeroZero ⟨0⟩ ⟨0⟩).checkSBA

#guard !(zeroAndTwoBofursSBA.battlefield.any (·.name == "Zero/Zero"))
#guard
  match zeroAndTwoBofursSBA.pending with
  | .chooseLegend _ name ids =>
    name == "Bofur, Reliable Guardian" && ids.size == 2
  | _ => false
#guard !zeroAndTwoBofursSBA.hasPriority ⟨0⟩
#guard zeroAndTwoBofursSBA.actor == some ⟨0⟩

/-- Legendary creature with a dies trigger, for the CR 704.3 wait. -/
def legendaryFireleaper : CardDef :=
  legendaryCreature "Legendary Fireleaper" ManaCost.empty #["Goblin"] 2 1
    (triggeredAbilities := #[.onDiesDealDamageEqualToPowerToOppCreature])

def twoFireleapersSBA : Game :=
  let g := addPermanent started legendaryFireleaper ⟨0⟩ ⟨0⟩
  let g := addPermanent g legendaryFireleaper ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  g.checkSBA

-- CR 704.3: the dies trigger waits until the legend-rule SBA is finished.
#guard twoFireleapersSBA.waitingTriggers.isEmpty
#guard twoFireleapersSBA.stack.isEmpty
#guard twoFireleapersSBA.legendChoicePending?
#guard !twoFireleapersSBA.hasPriority ⟨0⟩
#guard (twoFireleapersSBA.receivePriority ⟨0⟩).legendChoicePending?
#guard (twoFireleapersSBA.receivePriority ⟨0⟩).stack.isEmpty

def afterKeepFireleaper : Game :=
  keepFirstLegend twoFireleapersSBA

#guard afterKeepFireleaper.waitingTriggers.isEmpty
#guard afterKeepFireleaper.pending == .chooseTargets ⟨0⟩
#guard afterKeepFireleaper.stack.any (fun e =>
  (afterKeepFireleaper.object! e.objectId).triggeredAbility ==
    some .onDiesDealDamageEqualToPowerToOppCreature)
#guard !afterKeepFireleaper.hasPriority ⟨0⟩
#guard afterKeepFireleaper.actor == some ⟨0⟩

/-- A 0/0 creature survives while Gift of Strands is attached. -/
def zeroEnchanted : Game :=
  let g := addPermanent started zeroZero ⟨0⟩ ⟨0⟩
  addAttachedAura g giftOfStrands (namedPermanent g "Zero/Zero") ⟨0⟩ ⟨0⟩

#guard zeroEnchanted.power (namedPermanent zeroEnchanted "Zero/Zero") == 3
#guard zeroEnchanted.toughness (namedPermanent zeroEnchanted "Zero/Zero") == 3
#guard (zeroEnchanted.checkSBA).battlefield.any (fun o => o.name == "Zero/Zero")

/-- Combat uses the enchanted power. -/
def afterEnchantedCombat : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addAttachedAura g giftOfStrands (namedPermanent g "Grizzly Bears") ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[])
  passBoth g

#guard afterEnchantedCombat.log.any (fun s =>
  mentions s "Grizzly Bears deals 5 combat damage to Nissa")
#guard (afterEnchantedCombat.player ⟨1⟩).life == 15

/-- Flash lets Gift of Strands be cast when it is not a main phase. -/
def flashWindow : Game :=
  let g := applyIdle (passBoth (skipTo afterDraw .end 80))
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  withGreenMana (addToHand g giftOfStrands ⟨0⟩) ⟨0⟩

#guard flashWindow.hasPriority ⟨0⟩
#guard !flashWindow.asSorcery? ⟨0⟩
#guard flashWindow.canCast ⟨0⟩ (handCardNamed flashWindow ⟨0⟩ "Gift of Strands")
#guard
  let g := addToHand flashWindow grayOgre ⟨0⟩
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Gray Ogre")

def paidFlashGift : Game :=
  let g := proposeTargeted flashWindow ⟨0⟩
    (handCardNamed flashWindow ⟨0⟩ "Gift of Strands").id
    (Target.permanent (namedPermanent flashWindow "Grizzly Bears").id)
  mustApply g ⟨0⟩ .pay

def flashGiftEntered : Game := passBoth paidFlashGift

#guard flashGiftEntered.step == .upkeep
#guard flashGiftEntered.activePlayer == ⟨1⟩
#guard flashGiftEntered.power (namedPermanent flashGiftEntered "Grizzly Bears") == 5

/-- You may enchant an opponent's creature. -/
def giftOnNissa : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := withGreenMana (addToHand g giftOfStrands ⟨0⟩) ⟨0⟩
  let g := proposeTargeted g ⟨0⟩
    (handCardNamed g ⟨0⟩ "Gift of Strands").id
    (Target.permanent (namedPermanent g "Grizzly Bears").id)
  let g := mustApply g ⟨0⟩ .pay
  keepScry (passBoth (passBoth g))

#guard giftOnNissa.power (namedPermanent giftOnNissa "Grizzly Bears") == 5
#guard (namedPermanent giftOnNissa "Grizzly Bears").controller == some ⟨1⟩
#guard (namedPermanent giftOnNissa "Gift of Strands").controller == some ⟨0⟩

/-- The agent casts Gift of Strands on its own creature when that is the
playable spell. -/
def agentGiftOnly : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withGreenMana (addToHand g giftOfStrands ⟨0⟩) ⟨0⟩

#guard
  match Agent.choose agentGiftOnly ⟨0⟩ with
  | some (.cast id) => (agentGiftOnly.object! id).name == "Gift of Strands"
  | _ => false

#guard
  let g := mustApply agentGiftOnly ⟨0⟩
    (.cast (handCardNamed agentGiftOnly ⟨0⟩ "Gift of Strands").id)
  match Agent.choose g ⟨0⟩ with
  | some (.target (Target.permanent tid)) => (g.object! tid).name == "Grizzly Bears"
  | _ => false

/-- Scrying 2 with one card looks at that card; an empty library still scries. -/
def scryOneCard : Game :=
  let g := { giftEntered with pending := .none, stack := #[] }
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with library := pl.library.extract (pl.library.size - 1) pl.library.size })
  g.beginScry ⟨0⟩ 2

#guard
  match scryOneCard.pending with
  | .scry ⟨0⟩ 1 => true
  | _ => false

def scryEmpty : Game :=
  let g := { giftEntered with pending := .none, stack := #[] }
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with library := #[] })
  g.beginScry ⟨0⟩ 2

#guard scryEmpty.pending == .none
#guard scryEmpty.log.any (fun s => mentions s "no cards to look at")

/-- Galadhrim Guide in hand with enough mana to cast it (CR 601.2). -/
def guideSetup : Game :=
  withGreenMana (addToHand afterDraw galadhrimGuide ⟨0⟩) ⟨0⟩

#guard guideSetup.canCast ⟨0⟩ (handCardNamed guideSetup ⟨0⟩ "Galadhrim Guide")
#guard guideSetup.asSorcery? ⟨0⟩
#guard !galadhrimGuide.keywords.flash
#guard galadhrimGuide.hasSorcerySpeed

-- A creature without flash cannot be cast when it is not a main phase.
#guard
  let g := applyIdle (passBoth (skipTo afterDraw .end 80))
  let g := withGreenMana (addToHand g galadhrimGuide ⟨0⟩) ⟨0⟩
  !g.asSorcery? ⟨0⟩ && !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Galadhrim Guide")

def proposedGuide : Game :=
  mustApply guideSetup ⟨0⟩ (.cast (handCardNamed guideSetup ⟨0⟩ "Galadhrim Guide").id)

#guard proposedGuide.pending == .activateManaAbilities ⟨0⟩
#guard proposedGuide.log.any (fun s => mentions s "begins casting Galadhrim Guide")

def paidGuide : Game := mustApply proposedGuide ⟨0⟩ .pay

#guard paidGuide.stack.size == 1
#guard paidGuide.hasPriority ⟨0⟩
#guard paidGuide.log.any (fun s => mentions s "casts Galadhrim Guide")

/-- The creature enters; scry waits on the stack (CR 603.6a). -/
def guideEntered : Game := passBoth paidGuide

#guard (namedPermanent guideEntered "Galadhrim Guide").printed.power == some 3
#guard guideEntered.power (namedPermanent guideEntered "Galadhrim Guide") == 3
#guard guideEntered.toughness (namedPermanent guideEntered "Galadhrim Guide") == 4
#guard guideEntered.stack.size == 1
#guard (guideEntered.object! guideEntered.stack.back!.objectId).triggeredAbility ==
  some (.onEnterScry 2)
#guard (guideEntered.object! guideEntered.stack.back!.objectId).sourceId ==
  some (namedPermanent guideEntered "Galadhrim Guide").id
#guard guideEntered.log.any (fun s => mentions s "enters the battlefield")
#guard guideEntered.log.any (fun s => mentions s "enters trigger is put on the stack")

def guideScrying : Game := passBoth guideEntered

#guard
  match guideScrying.pending with
  | .scry ⟨0⟩ 2 => true
  | _ => false
#guard guideScrying.actor == some ⟨0⟩
#guard !guideScrying.hasPriority ⟨0⟩
#guard guideScrying.log.any (fun s => mentions s "scries 2")
#guard guideScrying.stack.isEmpty
#guard guideScrying.battlefield.any (fun o => o.name == "Galadhrim Guide")

def guideScried : Game := keepScry guideScrying

#guard guideScried.pending == .none
#guard guideScried.hasPriority ⟨0⟩
#guard guideScried.battlefield.any (fun o => o.name == "Galadhrim Guide")

-- The agent keeps scried cards on top.
#guard
  match Agent.choose guideScrying ⟨0⟩ with
  | some (.scry top bottom) =>
    bottom.isEmpty && top == guideScrying.scryLookedIds ⟨0⟩ 2
  | _ => false

/-- Known library: Forest then Elves on top; scry 2 looks at both. -/
def guideKnownLib : Game :=
  addToLibraryTop (addToLibraryTop guideEntered forest ⟨0⟩) llanowarElves ⟨0⟩

def guideKnownScrying : Game := passBoth guideKnownLib

#guard
  let looked := guideKnownScrying.scryLookedIds ⟨0⟩ 2
  looked.size == 2 &&
    (guideKnownScrying.object! looked[0]!).name == "Forest" &&
    (guideKnownScrying.object! looked.back!).name == "Llanowar Elves"

/-- The trigger still scries if Galadhrim Guide has left the battlefield (CR 113.7a). -/
def guideLeftBeforeTrigger : Game :=
  let id := (namedPermanent guideEntered "Galadhrim Guide").id
  let (g, _) := guideEntered.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard
  match guideLeftBeforeTrigger.pending with
  | .scry ⟨0⟩ 2 => true
  | _ => false
#guard !(guideLeftBeforeTrigger.battlefield.any (fun o => o.name == "Galadhrim Guide"))
#guard (guideLeftBeforeTrigger.player ⟨0⟩).graveyard.any (fun id =>
  (guideLeftBeforeTrigger.object! id).name == "Galadhrim Guide")

/-- The agent casts Galadhrim Guide when that is the playable spell. -/
def agentGuideOnly : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  withGreenMana (addToHand g galadhrimGuide ⟨0⟩) ⟨0⟩

#guard
  match Agent.choose agentGuideOnly ⟨0⟩ with
  | some (.cast id) => (agentGuideOnly.object! id).name == "Galadhrim Guide"
  | _ => false

/-- Elvish Visionary in hand with enough mana to cast it (CR 601.2). -/
def visionarySetup : Game :=
  withGreenMana (addToHand afterDraw elvishVisionary ⟨0⟩) ⟨0⟩

#guard visionarySetup.canCast ⟨0⟩ (handCardNamed visionarySetup ⟨0⟩ "Elvish Visionary")
#guard visionarySetup.asSorcery? ⟨0⟩
#guard !elvishVisionary.keywords.flash
#guard elvishVisionary.hasSorcerySpeed

def proposedVisionary : Game :=
  mustApply visionarySetup ⟨0⟩ (.cast (handCardNamed visionarySetup ⟨0⟩ "Elvish Visionary").id)

#guard proposedVisionary.pending == .activateManaAbilities ⟨0⟩
#guard proposedVisionary.log.any (fun s => mentions s "begins casting Elvish Visionary")

def paidVisionary : Game := mustApply proposedVisionary ⟨0⟩ .pay

#guard paidVisionary.stack.size == 1
#guard paidVisionary.hasPriority ⟨0⟩
#guard paidVisionary.log.any (fun s => mentions s "casts Elvish Visionary")

/-- The creature enters; draw waits on the stack (CR 603.6a). -/
def visionaryEntered : Game := passBoth paidVisionary

#guard (namedPermanent visionaryEntered "Elvish Visionary").printed.power == some 1
#guard visionaryEntered.power (namedPermanent visionaryEntered "Elvish Visionary") == 1
#guard visionaryEntered.toughness (namedPermanent visionaryEntered "Elvish Visionary") == 1
#guard visionaryEntered.stack.size == 1
#guard (visionaryEntered.object! visionaryEntered.stack.back!.objectId).triggeredAbility ==
  some (.onEnterDraw 1)
#guard (visionaryEntered.object! visionaryEntered.stack.back!.objectId).sourceId ==
  some (namedPermanent visionaryEntered "Elvish Visionary").id
#guard visionaryEntered.log.any (fun s => mentions s "enters the battlefield")
#guard visionaryEntered.log.any (fun s => mentions s "enters trigger is put on the stack")

/-- Known library: Forest on top is drawn when the trigger resolves (CR 121). -/
def visionaryKnownLib : Game :=
  addToLibraryTop visionaryEntered forest ⟨0⟩

def visionaryDrew : Game := passBoth visionaryKnownLib

#guard visionaryDrew.pending == .none
#guard visionaryDrew.hasPriority ⟨0⟩
#guard visionaryDrew.stack.isEmpty
#guard visionaryDrew.battlefield.any (fun o => o.name == "Elvish Visionary")
#guard (visionaryDrew.player ⟨0⟩).hand.size == (visionaryKnownLib.player ⟨0⟩).hand.size + 1
#guard (visionaryDrew.handObjects ⟨0⟩).any (fun o => o.name == "Forest")
#guard visionaryDrew.log.any (fun s => mentions s "draws Forest")

-- Direct resolution of an enters-draw trigger draws that many cards (CR 121).
#guard
  let g := addToLibraryTop (addToLibraryTop afterDraw forest ⟨0⟩) llanowarElves ⟨0⟩
  let beforeHand := (g.player ⟨0⟩).hand.size
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnterDraw 2) none
  (g.player ⟨0⟩).hand.size == beforeHand + 2 &&
    g.log.any (fun s => mentions s "draws Llanowar Elves") &&
    g.log.any (fun s => mentions s "draws Forest")

/-- The trigger still draws if Elvish Visionary has left the battlefield (CR 113.7a). -/
def visionaryLeftBeforeTrigger : Game :=
  let id := (namedPermanent visionaryKnownLib "Elvish Visionary").id
  let (g, _) := visionaryKnownLib.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard !(visionaryLeftBeforeTrigger.battlefield.any (fun o => o.name == "Elvish Visionary"))
#guard (visionaryLeftBeforeTrigger.player ⟨0⟩).graveyard.any (fun id =>
  (visionaryLeftBeforeTrigger.object! id).name == "Elvish Visionary")
#guard (visionaryLeftBeforeTrigger.handObjects ⟨0⟩).any (fun o => o.name == "Forest")
#guard visionaryLeftBeforeTrigger.log.any (fun s => mentions s "draws Forest")

/-- Drawing from an empty library is a state-based loss (CR 704.5b / 121.4). -/
def visionaryEmptyLib : Game :=
  let g := visionaryEntered.modifyPlayer ⟨0⟩ (fun pl => { pl with library := #[] })
  passBoth g

#guard visionaryEmptyLib.over
#guard visionaryEmptyLib.result == some (.won ⟨1⟩)
#guard (visionaryEmptyLib.player ⟨0⟩).lost
#guard visionaryEmptyLib.log.any (fun s => mentions s "tries to draw from an empty library")
#guard visionaryEmptyLib.log.any (fun s => mentions s "loses the game (drew from empty library)")
#guard visionaryEmptyLib.log.any (fun s => mentions s "Nissa wins the game")

/-- The agent casts Elvish Visionary when that is the playable spell. -/
def agentVisionaryOnly : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  withGreenMana (addToHand g elvishVisionary ⟨0⟩) ⟨0⟩

#guard
  match Agent.choose agentVisionaryOnly ⟨0⟩ with
  | some (.cast id) => (agentVisionaryOnly.object! id).name == "Elvish Visionary"
  | _ => false

/- Wood Elves: search for a Forest card, put it onto the battlefield, shuffle. -/

#guard isForestCard forest
#guard isBasicLandCard forest
#guard !isForestCard mountain
#guard isBasicLandCard mountain
#guard isLandTypeCard mountain "Mountain"
#guard isLandTypeCard swamp "Swamp"
#guard !isLandTypeCard mountain "Swamp"
#guard !isLandTypeCard swamp "Mountain"

/-- Nonbasic land with the Forest type; Wood Elves can find it (CR 305.7). -/
def tropicalIsland : CardDef :=
  land "Tropical Island" "" (subtypes := #["Forest", "Island"])

#guard isForestCard tropicalIsland
#guard !isBasicLandCard tropicalIsland
#guard !isForestCard roguesPassage

/-- Wood Elves in hand with enough mana to cast it (CR 601.2). -/
def woodElvesSetup : Game :=
  withGreenMana (addToHand afterDraw woodElves ⟨0⟩) ⟨0⟩

#guard woodElvesSetup.canCast ⟨0⟩ (handCardNamed woodElvesSetup ⟨0⟩ "Wood Elves")
#guard woodElvesSetup.asSorcery? ⟨0⟩
#guard !woodElves.keywords.flash
#guard woodElves.hasSorcerySpeed
#guard woodElves.power == some 1
#guard woodElves.toughness == some 1

def proposedWoodElves : Game :=
  mustApply woodElvesSetup ⟨0⟩ (.cast (handCardNamed woodElvesSetup ⟨0⟩ "Wood Elves").id)

#guard proposedWoodElves.pending == .activateManaAbilities ⟨0⟩
#guard proposedWoodElves.log.any (fun s => mentions s "begins casting Wood Elves")

def paidWoodElves : Game := mustApply proposedWoodElves ⟨0⟩ .pay

#guard paidWoodElves.stack.size == 1
#guard paidWoodElves.hasPriority ⟨0⟩
#guard paidWoodElves.log.any (fun s => mentions s "casts Wood Elves")

/-- The creature enters; the search waits on the stack (CR 603.6a). -/
def woodElvesEntered : Game := passBoth paidWoodElves

#guard (namedPermanent woodElvesEntered "Wood Elves").printed.power == some 1
#guard woodElvesEntered.power (namedPermanent woodElvesEntered "Wood Elves") == 1
#guard woodElvesEntered.toughness (namedPermanent woodElvesEntered "Wood Elves") == 1
#guard woodElvesEntered.stack.size == 1
#guard (woodElvesEntered.object! woodElvesEntered.stack.back!.objectId).triggeredAbility ==
  some .onEnterSearchForest
#guard (woodElvesEntered.object! woodElvesEntered.stack.back!.objectId).sourceId ==
  some (namedPermanent woodElvesEntered "Wood Elves").id
#guard woodElvesEntered.log.any (fun s => mentions s "enters the battlefield")
#guard woodElvesEntered.log.any (fun s => mentions s "enters trigger is put on the stack")

/-- Mountain on top, Forest below: search finds the Forest (CR 701.19). -/
def woodElvesKnownLib : Game :=
  addToLibraryTop (addToLibraryTop woodElvesEntered forest ⟨0⟩) mountain ⟨0⟩

def woodElvesResolved : Game := passBoth woodElvesKnownLib

#guard woodElvesResolved.pending == .none
#guard woodElvesResolved.hasPriority ⟨0⟩
#guard woodElvesResolved.stack.isEmpty
#guard woodElvesResolved.battlefield.any (fun o => o.name == "Wood Elves")
#guard woodElvesResolved.battlefield.any (fun o => o.name == "Forest")
#guard !(namedPermanent woodElvesResolved "Forest").status.tapped
#guard !(namedPermanent woodElvesResolved "Forest").status.summoningSick
#guard (woodElvesResolved.player ⟨0⟩).landsPlayedThisTurn ==
  (woodElvesKnownLib.player ⟨0⟩).landsPlayedThisTurn
#guard woodElvesResolved.log.any (fun s =>
  mentions s "puts Forest onto the battlefield" && !mentions s "tapped")
#guard woodElvesResolved.log.any (fun s => mentions s "shuffles their library")

-- A Mountain on top is not chosen; the Forest type is required (CR 305.7).
#guard !(woodElvesResolved.battlefield.any (fun o =>
  o.name == "Mountain" &&
    !(woodElvesKnownLib.battlefield.any (fun p => p.id == o.id))))

-- The fetched Forest can tap for {G} immediately.
#guard
  match woodElvesResolved.tapForMana ⟨0⟩
      (namedPermanent woodElvesResolved "Forest").id (.colored .green) with
  | .ok g =>
    (g.player ⟨0⟩).manaPool.green ==
      (woodElvesResolved.player ⟨0⟩).manaPool.green + 1 &&
      (namedPermanent g "Forest").status.tapped
  | .error _ => false

-- Direct resolution of an enters-search trigger puts a Forest onto the battlefield.
#guard
  let g := addToLibraryTop afterDraw forest ⟨0⟩
  let beforeLands := (g.player ⟨0⟩).landsPlayedThisTurn
  let g := g.applyTriggeredAbility ⟨0⟩ .onEnterSearchForest none
  g.battlefield.any (fun o => o.name == "Forest" && !o.status.tapped) &&
    (g.player ⟨0⟩).landsPlayedThisTurn == beforeLands &&
    g.log.any (fun s => mentions s "puts Forest onto the battlefield") &&
    g.log.any (fun s => mentions s "shuffles their library")

/-- The trigger still searches if Wood Elves has left the battlefield (CR 113.7a). -/
def woodElvesLeftBeforeTrigger : Game :=
  let id := (namedPermanent woodElvesKnownLib "Wood Elves").id
  let (g, _) := woodElvesKnownLib.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard !(woodElvesLeftBeforeTrigger.battlefield.any (fun o => o.name == "Wood Elves"))
#guard (woodElvesLeftBeforeTrigger.player ⟨0⟩).graveyard.any (fun id =>
  (woodElvesLeftBeforeTrigger.object! id).name == "Wood Elves")
#guard woodElvesLeftBeforeTrigger.battlefield.any (fun o => o.name == "Forest")
#guard woodElvesLeftBeforeTrigger.log.any (fun s => mentions s "puts Forest onto the battlefield")

/-- No Forest in the library: the search fails and the library is still shuffled. -/
def woodElvesNoForest : Game := passBoth woodElvesEntered

#guard woodElvesNoForest.stack.isEmpty
#guard !(woodElvesNoForest.battlefield.any (fun o => o.name == "Forest"))
#guard woodElvesNoForest.log.any (fun s => mentions s "finds no Forest card")
#guard woodElvesNoForest.log.any (fun s => mentions s "shuffles their library")

/-- A nonbasic Forest card is a legal find (CR 305.7). -/
def woodElvesNonbasic : Game :=
  let g := addToLibraryTop woodElvesEntered tropicalIsland ⟨0⟩
  passBoth g

#guard woodElvesNonbasic.battlefield.any (fun o => o.name == "Tropical Island")
#guard !(namedPermanent woodElvesNonbasic "Tropical Island").status.tapped
#guard woodElvesNonbasic.log.any (fun s =>
  mentions s "puts Tropical Island onto the battlefield")

/-- Landfall triggers when the fetched Forest enters (CR 603.6a). -/
def woodElvesLandfallPending : Game :=
  let g := addPermanent woodElvesKnownLib beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  passBoth g

#guard woodElvesLandfallPending.pending == .chooseTargets ⟨0⟩
#guard woodElvesLandfallPending.battlefield.any (fun o => o.name == "Forest")
#guard (woodElvesLandfallPending.object! woodElvesLandfallPending.stack.back!.objectId).triggeredAbility ==
  some .onLandYouControlEntersPlusOnePlusOne
#guard woodElvesLandfallPending.log.any (fun s => mentions s "landfall trigger is put on the stack")

/-- The agent casts Wood Elves when that is the playable spell. -/
def agentWoodElvesOnly : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  withGreenMana (addToHand g woodElves ⟨0⟩) ⟨0⟩

#guard
  match Agent.choose agentWoodElvesOnly ⟨0⟩ with
  | some (.cast id) => (agentWoodElvesOnly.object! id).name == "Wood Elves"
  | _ => false

/-- Goblin Cratermaker plus an opposing 2/2 and a Mountain; a land drop is already
used so the agent will activate rather than play another land. -/
def cratermakerReady : Game :=
  let g := skipTo started .precombatMain 80
  let g := addUntappedLand g mountain
  let g := addPermanent g goblinCratermaker ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })

def cratermakerSource (g : Game) : GameObject :=
  namedPermanent g "Goblin Cratermaker"

def cratermakerAbility : ActivatedAbility :=
  goblinCratermaker.activatedAbilities[0]!

#guard cratermakerAbility.isModal
#guard cratermakerAbility.cost.sacrificeSource
#guard cratermakerAbility.effect == .dealDamageToTargetCreature 2
#guard cratermakerAbility.otherModes == #[.destroyTargetColorlessNonland]
#guard cratermakerReady.canActivate ⟨0⟩ (cratermakerSource cratermakerReady) cratermakerAbility
#guard !(cratermakerReady.canActivate ⟨1⟩ (cratermakerSource cratermakerReady)
  cratermakerAbility)
#guard (namedPermanent cratermakerReady "Grizzly Bears").isColorlessNonland == false
#guard (cratermakerSource cratermakerReady).printed.colors.contains .red

-- The heuristic begins activating Cratermaker when {1} is available.
#guard
  match Agent.choose cratermakerReady ⟨0⟩ with
  | some (.activate id 0) => id == (cratermakerSource cratermakerReady).id
  | _ => false

def proposedCratermaker : Game :=
  mustApply cratermakerReady ⟨0⟩ (.activate (cratermakerSource cratermakerReady).id 0)

#guard
  match proposedCratermaker.pending with
  | .chooseMode ⟨0⟩ => true
  | _ => false
#guard proposedCratermaker.proposedSpell.isSome
#guard proposedCratermaker.stack.size == 1
#guard (proposedCratermaker.object! proposedCratermaker.stack.back!.objectId).abilityEffect.isNone
#guard (namedPermanent proposedCratermaker "Goblin Cratermaker").isOnBattlefield
#guard proposedCratermaker.log.any (fun s => mentions s "begins activating Goblin Cratermaker")
#guard proposedCratermaker.log.any (fun s => mentions s "must choose a mode (CR 601.2b)")

-- Opponent cannot choose Chandra's mode.
#guard
  match proposedCratermaker.apply ⟨1⟩ (.chooseMode 0) with
  | .error msg => mentions msg "Only Chandra"
  | .ok _ => false

-- Mode index out of range.
#guard
  match proposedCratermaker.apply ⟨0⟩ (.chooseMode 2) with
  | .error msg => mentions msg "No such mode"
  | .ok _ => false

-- Targeting is not chosen at `activate`; it comes after the mode.
#guard
  match proposedCratermaker.apply ⟨0⟩
      (.target (Target.permanent (namedPermanent proposedCratermaker "Grizzly Bears").id)) with
  | .error msg => mentions msg "Not time to choose targets"
  | .ok _ => false

-- The heuristic picks the damage mode when the opponent has a creature.
#guard
  match Agent.choose proposedCratermaker ⟨0⟩ with
  | some (.chooseMode 0) => true
  | _ => false

def cratermakerModeChosen : Game :=
  mustApply proposedCratermaker ⟨0⟩ (.chooseMode 0)

#guard cratermakerModeChosen.pending == .chooseTargets ⟨0⟩
#guard (cratermakerModeChosen.object! cratermakerModeChosen.stack.back!.objectId).abilityEffect ==
  some (.dealDamageToTargetCreature 2)
#guard cratermakerModeChosen.log.any (fun s =>
  mentions s "chooses a mode: This creature deals 2 damage")
#guard cratermakerModeChosen.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- A player is not a legal target for the damage mode.
#guard
  match cratermakerModeChosen.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The heuristic targets Nissa's creature.
#guard
  match Agent.choose cratermakerModeChosen ⟨0⟩ with
  | some (.target (Target.permanent id)) =>
    (cratermakerModeChosen.object! id).name == "Grizzly Bears"
  | _ => false

def cratermakerTargeted : Game :=
  mustApply cratermakerModeChosen ⟨0⟩
    (.target (Target.permanent (namedPermanent cratermakerModeChosen "Grizzly Bears").id))

#guard cratermakerTargeted.pending == .activateManaAbilities ⟨0⟩
#guard cratermakerTargeted.stack.back!.targets ==
  #[Target.permanent (namedPermanent cratermakerTargeted "Grizzly Bears").id]
#guard cratermakerTargeted.log.any (fun s =>
  mentions s "chooses Grizzly Bears as a target (CR 601.2c)")
#guard cratermakerTargeted.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")

-- Paying without mana reverses the activation (CR 602.2 / 733.1).
def reversedCratermaker : Game :=
  mustApply cratermakerTargeted ⟨0⟩ .pay

#guard reversedCratermaker.pending == .none
#guard reversedCratermaker.stack.isEmpty
#guard (namedPermanent reversedCratermaker "Goblin Cratermaker").isOnBattlefield
#guard reversedCratermaker.log.any (fun s => mentions s "the activation is reversed")

def paidCratermaker : Game :=
  mustApply (tapNextMana cratermakerTargeted ⟨0⟩) ⟨0⟩ .pay

#guard paidCratermaker.pending == .none
#guard paidCratermaker.proposedSpell.isNone
#guard paidCratermaker.hasPriority ⟨0⟩
#guard paidCratermaker.stack.size == 1
#guard (paidCratermaker.player ⟨0⟩).graveyard.any (fun id =>
  (paidCratermaker.object! id).name == "Goblin Cratermaker")
#guard !(paidCratermaker.battlefield.any (fun o => o.name == "Goblin Cratermaker"))
#guard paidCratermaker.log.any (fun s => mentions s "sacrifices Goblin Cratermaker")
#guard paidCratermaker.log.any (fun s => mentions s "activates Goblin Cratermaker")

def resolvedCratermaker : Game := passBoth paidCratermaker

#guard resolvedCratermaker.stack.isEmpty
#guard resolvedCratermaker.log.any (fun s => mentions s "Grizzly Bears is dealt 2 damage")
#guard resolvedCratermaker.log.any (fun s => mentions s "Grizzly Bears dies from lethal damage")
#guard !(resolvedCratermaker.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard resolvedCratermaker.objects.any (fun o =>
  o.name == "Grizzly Bears" && o.zone == .graveyard ⟨1⟩)

/-- 2 damage is not lethal to a 3-toughness creature. -/
def cratermakerVsGiant : Game :=
  let g := skipTo started .precombatMain 80
  let g := addUntappedLand g mountain
  let g := addPermanent g goblinCratermaker ⟨0⟩ ⟨0⟩
  addPermanent g hillGiant ⟨1⟩ ⟨1⟩

def resolvedCratermakerVsGiant : Game :=
  let g := mustApply cratermakerVsGiant ⟨0⟩
    (.activate (cratermakerSource cratermakerVsGiant).id 0)
  let g := mustApply g ⟨0⟩ (.chooseMode 0)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Hill Giant").id))
  let g := mustApply (tapNextMana g ⟨0⟩) ⟨0⟩ .pay
  passBoth g

#guard (namedPermanent resolvedCratermakerVsGiant "Hill Giant").status.damage == 2
#guard resolvedCratermakerVsGiant.battlefield.any (fun o => o.name == "Hill Giant")
#guard resolvedCratermakerVsGiant.log.any (fun s => mentions s "Hill Giant is dealt 2 damage")
#guard !resolvedCratermakerVsGiant.log.any (fun s => mentions s "Hill Giant dies")

/-- Targeting the Cratermaker itself: it is sacrificed as a cost, so the ability
does nothing on resolution. -/
def cratermakerSelfTarget : Game :=
  let g := skipTo started .precombatMain 80
  let g := addUntappedLand g mountain
  addPermanent g goblinCratermaker ⟨0⟩ ⟨0⟩

def resolvedCratermakerSelf : Game :=
  let g := mustApply cratermakerSelfTarget ⟨0⟩
    (.activate (cratermakerSource cratermakerSelfTarget).id 0)
  let g := mustApply g ⟨0⟩ (.chooseMode 0)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (cratermakerSource g).id))
  let g := mustApply (tapNextMana g ⟨0⟩) ⟨0⟩ .pay
  passBoth g

#guard resolvedCratermakerSelf.stack.isEmpty
#guard !(resolvedCratermakerSelf.battlefield.any (fun o => o.name == "Goblin Cratermaker"))
#guard resolvedCratermakerSelf.log.any (fun s => mentions s "The target is no longer in play")

/-- Destroy mode: Wayfarer's Bauble is a colorless nonland permanent. -/
def cratermakerDestroyReady : Game :=
  let g := skipTo started .precombatMain 80
  let g := addUntappedLand g mountain
  let g := addPermanent g goblinCratermaker ⟨0⟩ ⟨0⟩
  let g := addPermanent g wayfarersBauble ⟨1⟩ ⟨1⟩
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })

#guard (namedPermanent cratermakerDestroyReady "Wayfarer's Bauble").isColorlessNonland
#guard !(namedPermanent cratermakerDestroyReady "Goblin Cratermaker").isColorlessNonland

-- No opposing creature: the heuristic prefers the destroy mode.
#guard
  let g := mustApply cratermakerDestroyReady ⟨0⟩
    (.activate (cratermakerSource cratermakerDestroyReady).id 0)
  match Agent.choose g ⟨0⟩ with
  | some (.chooseMode 1) => true
  | _ => false

-- A Mountain is a land, so it is not a legal destroy target.
#guard
  let g := mustApply cratermakerDestroyReady ⟨0⟩
    (.activate (cratermakerSource cratermakerDestroyReady).id 0)
  let g := mustApply g ⟨0⟩ (.chooseMode 1)
  match (g.permanentsOf ⟨0⟩).find? (·.printed.isLand) with
  | none => false
  | some land =>
    match g.apply ⟨0⟩ (.target (Target.permanent land.id)) with
    | .error msg => mentions msg "Illegal target"
    | .ok _ => false

-- A colored creature is not a legal destroy target.
#guard
  let g := addPermanent cratermakerDestroyReady grizzlyBears ⟨1⟩ ⟨1⟩
  let g := mustApply g ⟨0⟩ (.activate (cratermakerSource g).id 0)
  let g := mustApply g ⟨0⟩ (.chooseMode 1)
  match g.apply ⟨0⟩ (.target (Target.permanent (namedPermanent g "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

def resolvedCratermakerDestroy : Game :=
  let g := mustApply cratermakerDestroyReady ⟨0⟩
    (.activate (cratermakerSource cratermakerDestroyReady).id 0)
  let g := mustApply g ⟨0⟩ (.chooseMode 1)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Wayfarer's Bauble").id))
  let g := mustApply (tapNextMana g ⟨0⟩) ⟨0⟩ .pay
  passBoth g

#guard resolvedCratermakerDestroy.stack.isEmpty
#guard resolvedCratermakerDestroy.log.any (fun s => mentions s "Wayfarer's Bauble is destroyed")
#guard !(resolvedCratermakerDestroy.battlefield.any (fun o => o.name == "Wayfarer's Bauble"))
#guard resolvedCratermakerDestroy.objects.any (fun o =>
  o.name == "Wayfarer's Bauble" && o.zone == .graveyard ⟨1⟩)
#guard !(resolvedCratermakerDestroy.battlefield.any (fun o => o.name == "Goblin Cratermaker"))

-- Destroy mode cannot be chosen when there is no colorless nonland.
#guard
  match proposedCratermaker.apply ⟨0⟩ (.chooseMode 1) with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

-- Instant-speed: Cratermaker can activate during the end step.
def cratermakerAtEndStep : Game := skipTo cratermakerReady .end 80

#guard cratermakerAtEndStep.step == .end
#guard cratermakerAtEndStep.canActivate ⟨0⟩ (cratermakerSource cratermakerAtEndStep)
  cratermakerAbility

/-- Hill Giant (3/3) blocked by two Llanowar Elves (1/1): CR 510.1c lets the
attacker assign all 3 damage to one blocker. -/
def giantVsTwoElves : Game :=
  let g := addPermanent started hillGiant ⟨0⟩ ⟨0⟩
  let g := addPermanent g llanowarElves ⟨1⟩ ⟨1⟩
  addPermanent g llanowarElves ⟨1⟩ ⟨1⟩

def giantBlockedByTwoElves : Game :=
  let g := passBoth (skipTo giantVsTwoElves .beginningOfCombat 80)
  let giant := namedPermanent g "Hill Giant"
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  let g := mustApply g ⟨0⟩ (.declareAttackers #[giant.id])
  let g := passBoth g
  mustApply g ⟨1⟩ (.declareBlockers #[(elves[0]!.id, giant.id), (elves[1]!.id, giant.id)])

def giantReadyToAssign : Game := passBoth giantBlockedByTwoElves

#guard giantReadyToAssign.step == .combatDamage
#guard giantReadyToAssign.pending == .assignCombatDamage ⟨0⟩ true
#guard giantReadyToAssign.actor == some ⟨0⟩
#guard giantReadyToAssign.needsCombatDamageChoice true
#guard !giantReadyToAssign.needsCombatDamageChoice false
#guard
  let g := giantReadyToAssign
  let giant := namedPermanent g "Hill Giant"
  g.combatDamageToAssign giant true == 3 &&
    (g.legalCombatDamageRecipients giant true).size == 2 &&
    !g.canAssignCombatDamageToDefendingPlayer giant true
#guard
  let g := giantReadyToAssign
  let giant := namedPermanent g "Hill Giant"
  let g := g.setObject { giant with status := giant.status.grantUntilEot Keyword.trample }
  let giant := namedPermanent g "Hill Giant"
  g.hasTrample giant && g.canAssignCombatDamageToDefendingPlayer giant true &&
    g.combatDamageToAssign giant true == 3

def giantAllDamageOnFirst : Game :=
  let g := giantReadyToAssign
  let giant := namedPermanent g "Hill Giant"
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  mustApply g ⟨0⟩ (.assignCombatDamage #[{
    source := giant.id
    toCreatures := #[(elves[0]!.id, 3), (elves[1]!.id, 0)]
  }])

#guard giantAllDamageOnFirst.log.any (fun s =>
  mentions s "Hill Giant deals 3 combat damage to Llanowar Elves")
#guard (giantAllDamageOnFirst.log.filter (fun s =>
  mentions s "Hill Giant deals" && mentions s "combat damage to Llanowar Elves")).size == 1
#guard (giantAllDamageOnFirst.player ⟨1⟩).life == 20
#guard (giantAllDamageOnFirst.battlefield.filter (fun o =>
  o.name == "Llanowar Elves")).size == 1
#guard giantAllDamageOnFirst.battlefield.any (fun o => o.name == "Hill Giant")
#guard (namedPermanent giantAllDamageOnFirst "Hill Giant").status.damage == 2

/-- The same total can be split 1 and 2; both Elves then take lethal damage. -/
def giantSplitDamage : Game :=
  let g := giantReadyToAssign
  let giant := namedPermanent g "Hill Giant"
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  mustApply g ⟨0⟩ (.assignCombatDamage #[{
    source := giant.id
    toCreatures := #[(elves[0]!.id, 1), (elves[1]!.id, 2)]
  }])

#guard giantSplitDamage.log.any (fun s =>
  mentions s "Hill Giant deals 1 combat damage to Llanowar Elves")
#guard giantSplitDamage.log.any (fun s =>
  mentions s "Hill Giant deals 2 combat damage to Llanowar Elves")
#guard (giantSplitDamage.battlefield.filter (fun o =>
  o.name == "Llanowar Elves")).isEmpty
#guard giantSplitDamage.battlefield.any (fun o => o.name == "Hill Giant")

/-- Assigning less than power, or to a creature that is not blocking, is illegal. -/
def giantTooLittleDamage : Bool :=
  let g := giantReadyToAssign
  let giant := namedPermanent g "Hill Giant"
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  match g.apply ⟨0⟩ (.assignCombatDamage #[{
    source := giant.id
    toCreatures := #[(elves[0]!.id, 2)]
  }]) with
  | .error msg => mentions msg "equal to its power"
  | .ok _ => false

#guard giantTooLittleDamage

def giantAssignsToItself : Bool :=
  let g := giantReadyToAssign
  let giant := namedPermanent g "Hill Giant"
  match g.apply ⟨0⟩ (.assignCombatDamage #[{
    source := giant.id
    toCreatures := #[(giant.id, 3)]
  }]) with
  | .error msg => mentions msg "creatures blocking it"
  | .ok _ => false

#guard giantAssignsToItself

/-- An empty assignment uses the default (all damage to the first blocker). -/
def giantDefaultAssign : Game :=
  mustApply giantReadyToAssign ⟨0⟩ (.assignCombatDamage #[])

#guard giantDefaultAssign.log.any (fun s =>
  mentions s "Hill Giant deals 3 combat damage to Llanowar Elves")
#guard (giantDefaultAssign.battlefield.filter (fun o =>
  o.name == "Llanowar Elves")).size == 1

/-- CR 510.1d: a blocker whose attacker has left combat assigns no damage. -/
def twoOgresOneBears : Game :=
  let g := addPermanent started grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩

def blockerWhoseAttackerLeft : Game :=
  let g := passBoth (skipTo twoOgresOneBears .beginningOfCombat 80)
  let ogres := g.battlefield.filter (fun o => o.name == "Gray Ogre")
  let bears := namedPermanent g "Grizzly Bears"
  let g := mustApply g ⟨0⟩ (.declareAttackers (ogres.map (·.id)))
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(bears.id, ogres[0]!.id)])
  let (g, _) := g.move ogres[0]!.id (.graveyard ⟨0⟩) none
  passBoth g

#guard blockerWhoseAttackerLeft.log.any (fun s =>
  mentions s "not blocking any creatures and assigns no combat damage")
#guard blockerWhoseAttackerLeft.log.any (fun s =>
  mentions s "Gray Ogre deals 2 combat damage to Nissa")
#guard (namedPermanent blockerWhoseAttackerLeft "Grizzly Bears").status.damage == 0
#guard (blockerWhoseAttackerLeft.player ⟨1⟩).life == 18

/-- CR 510.1d: a creature blocking two attackers divides its damage as chosen. -/
def bearsBlockingTwoOgresReady : Game :=
  let g := passBoth (skipTo twoOgresOneBears .beginningOfCombat 80)
  let ogres := g.battlefield.filter (fun o => o.name == "Gray Ogre")
  let g := mustApply g ⟨0⟩ (.declareAttackers (ogres.map (·.id)))
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[])
  let bears := namedPermanent g "Grizzly Bears"
  let g := g.setObject { bears with
    status := { bears.status with blocking := ogres.map (·.id) } }
  let g := Id.run do
    let mut g := g
    for o in ogres do
      let a := g.object! o.id
      g := g.setObject { a with status := { a.status with blocked := true } }
    return g
  passBoth g

#guard bearsBlockingTwoOgresReady.step == .combatDamage
#guard bearsBlockingTwoOgresReady.pending == .assignCombatDamage ⟨1⟩ false
#guard bearsBlockingTwoOgresReady.actor == some ⟨1⟩
#guard bearsBlockingTwoOgresReady.needsCombatDamageChoice false
#guard bearsBlockingTwoOgresReady.needsCombatDamageChoice true == false
#guard
  let g := bearsBlockingTwoOgresReady
  let bears := namedPermanent g "Grizzly Bears"
  g.combatDamageToAssign bears false == 2 &&
    (g.legalCombatDamageRecipients bears false).size == 2 &&
    !g.canAssignCombatDamageToDefendingPlayer bears false

def bearsAssignAllToFirstOgre : Game :=
  let g := bearsBlockingTwoOgresReady
  let bears := namedPermanent g "Grizzly Bears"
  let ogres := g.battlefield.filter (fun o => o.name == "Gray Ogre")
  mustApply g ⟨1⟩ (.assignCombatDamage #[{
    source := bears.id
    toCreatures := #[(ogres[0]!.id, 2), (ogres[1]!.id, 0)]
  }])

#guard bearsAssignAllToFirstOgre.log.any (fun s =>
  mentions s "Grizzly Bears deals 2 combat damage to Gray Ogre")
#guard (bearsAssignAllToFirstOgre.log.filter (fun s =>
  mentions s "Grizzly Bears deals" && mentions s "combat damage to Gray Ogre")).size == 1
#guard (bearsAssignAllToFirstOgre.battlefield.filter (fun o =>
  o.name == "Gray Ogre")).size == 1
#guard !(bearsAssignAllToFirstOgre.battlefield.any (fun o => o.name == "Grizzly Bears"))

def bearsAssignsToItself : Bool :=
  let g := bearsBlockingTwoOgresReady
  let bears := namedPermanent g "Grizzly Bears"
  match g.apply ⟨1⟩ (.assignCombatDamage #[{
    source := bears.id
    toCreatures := #[(bears.id, 2)]
  }]) with
  | .error msg => mentions msg "creatures it's blocking"
  | .ok _ => false

#guard bearsAssignsToItself

/-- Propose a modal spell, choose a 0-based mode, then announce its target. -/
def proposeModal (g : Game) (p : PlayerId) (id : ObjectId) (mode : Nat) (t : Target) : Game :=
  mustApply (mustApply (mustApply g p (.cast id)) p (.chooseMode mode)) p (.target t)

def hexproofFlyer : CardDef :=
  creature "Hexproof Flyer" ManaCost.empty #[] 1 1
    (keywords := Keyword.flying.merge Keyword.hexproof)

/-- Warg Tactics in hand, Grizzly Bears you control, an opposing flyer, enough mana. -/
def wargSetup : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g velvetwingButterflies ⟨1⟩ ⟨1⟩
  withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2

#guard wargSetup.canCast ⟨0⟩ (handCardNamed wargSetup ⟨0⟩ "Warg Tactics")
#guard wargTactics.isModal
#guard wargTactics.requiresTarget
#guard (wargSetup.legalModes ⟨0⟩ (handCardNamed wargSetup ⟨0⟩ "Warg Tactics")).size == 2

-- Cannot cast with no legal mode (no flyer and no creature you control).
#guard
  let g := withGreenMana (addToHand afterDraw wargTactics ⟨0⟩) ⟨0⟩ 2
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics")
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics")
#guard
  let g := withGreenMana (addToHand afterDraw wargTactics ⟨0⟩) ⟨0⟩ 2
  match g.apply ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Warg Tactics").id) with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

-- Own creature alone enables only the +1/+1 mode; an opposing flyer alone enables destroy.
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2
  g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics") &&
    g.legalModes ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics") == #[1]
#guard
  let g := addPermanent afterDraw velvetwingButterflies ⟨1⟩ ⟨1⟩
  let g := withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2
  g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics") &&
    g.legalModes ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics") == #[0]

-- An opposing hexproof flyer cannot be chosen for destroy (CR 702.11b).
#guard
  let g := addPermanent afterDraw hexproofFlyer ⟨1⟩ ⟨1⟩
  let g := withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics")
#guard
  let g := addPermanent afterDraw hexproofFlyer ⟨1⟩ ⟨1⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2
  g.legalModes ⟨0⟩ (handCardNamed g ⟨0⟩ "Warg Tactics") == #[1]

-- Casting a modal spell asks for a mode before a target (CR 601.2b).
def proposedWarg : Game :=
  mustApply wargSetup ⟨0⟩ (.cast (handCardNamed wargSetup ⟨0⟩ "Warg Tactics").id)

#guard
  match proposedWarg.pending with
  | .chooseMode ⟨0⟩ => true
  | _ => false
#guard proposedWarg.proposedSpell.isSome
#guard !proposedWarg.stack.isEmpty
#guard proposedWarg.stack.back!.chosenMode.isNone
#guard proposedWarg.stack.back!.targets.isEmpty
#guard proposedWarg.actor == some ⟨0⟩
#guard proposedWarg.log.any (fun s => mentions s "begins casting Warg Tactics")
#guard proposedWarg.log.any (fun s => mentions s "must choose a mode (CR 601.2b")

#guard
  match proposedWarg.apply ⟨0⟩ .pay with
  | .error msg => mentions msg "Choose a mode first"
  | .ok _ => false
#guard
  match proposedWarg.apply ⟨0⟩ (.target (Target.permanent
    (namedPermanent proposedWarg "Velvetwing Butterflies").id)) with
  | .error msg => mentions msg "Not time to choose targets"
  | .ok _ => false
#guard
  match proposedWarg.apply ⟨0⟩ (.chooseMode 2) with
  | .error msg => mentions msg "No such mode"
  | .ok _ => false
#guard
  match proposedWarg.apply ⟨1⟩ (.chooseMode 0) with
  | .error msg => mentions msg "may choose a mode"
  | .ok _ => false

-- The agent prefers destroying an opponent's flyer when that mode is legal.
#guard
  match Agent.choose proposedWarg ⟨0⟩ with
  | some (.chooseMode 0) => true
  | _ => false
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Warg Tactics").id)
  match Agent.choose g ⟨0⟩ with
  | some (.chooseMode 1) => true
  | _ => false

def wargModeDestroy : Game :=
  mustApply proposedWarg ⟨0⟩ (.chooseMode 0)

#guard wargModeDestroy.pending == .chooseTargets ⟨0⟩
#guard wargModeDestroy.stack.back!.chosenMode == some 0
#guard wargModeDestroy.log.any (fun s => mentions s "chooses mode 1")
#guard wargModeDestroy.log.any (fun s => mentions s "destroy target creature with flying")
#guard wargModeDestroy.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- Mode 1 cannot target a creature without flying or a player.
#guard
  match wargModeDestroy.apply ⟨0⟩ (.target (Target.permanent
    (namedPermanent wargModeDestroy "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match wargModeDestroy.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

#guard
  match Agent.choose wargModeDestroy ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (wargModeDestroy.object! tid).name == "Velvetwing Butterflies"
  | _ => false

def targetedWargDestroy : Game :=
  mustApply wargModeDestroy ⟨0⟩
    (.target (Target.permanent (namedPermanent wargModeDestroy "Velvetwing Butterflies").id))

#guard targetedWargDestroy.pending == .activateManaAbilities ⟨0⟩
#guard targetedWargDestroy.stack.back!.targets ==
  #[Target.permanent (namedPermanent targetedWargDestroy "Velvetwing Butterflies").id]

def paidWargDestroy : Game :=
  mustApply targetedWargDestroy ⟨0⟩ .pay

#guard paidWargDestroy.hasPriority ⟨0⟩
#guard paidWargDestroy.stack.size == 1
#guard paidWargDestroy.log.any (fun s => mentions s "casts Warg Tactics")

def resolvedWargDestroy : Game := passBoth paidWargDestroy

#guard resolvedWargDestroy.stack.isEmpty
#guard !(resolvedWargDestroy.battlefield.any (fun o => o.name == "Velvetwing Butterflies"))
#guard resolvedWargDestroy.objects.any (fun o =>
  o.name == "Velvetwing Butterflies" && o.zone == .graveyard ⟨1⟩)
#guard resolvedWargDestroy.log.any (fun s => mentions s "Velvetwing Butterflies is destroyed")
#guard (resolvedWargDestroy.player ⟨0⟩).graveyard.any (fun id =>
  (resolvedWargDestroy.object! id).name == "Warg Tactics")

-- If the flyer leaves before resolution, the spell does nothing (CR 608.2b).
def wargDestroyTargetGone : Game :=
  let id := (namedPermanent paidWargDestroy "Velvetwing Butterflies").id
  let (g, _) := paidWargDestroy.move id (.graveyard ⟨1⟩) none
  passBoth g

#guard wargDestroyTargetGone.log.any (fun s => mentions s "no longer in play")
#guard !(wargDestroyTargetGone.battlefield.any (fun o => o.name == "Velvetwing Butterflies"))

def wargModePump : Game :=
  mustApply proposedWarg ⟨0⟩ (.chooseMode 1)

#guard wargModePump.pending == .chooseTargets ⟨0⟩
#guard wargModePump.stack.back!.chosenMode == some 1
#guard wargModePump.log.any (fun s => mentions s "chooses mode 2")

-- Mode 2 cannot target an opponent's creature.
#guard
  match wargModePump.apply ⟨0⟩ (.target (Target.permanent
    (namedPermanent wargModePump "Velvetwing Butterflies").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

def paidWargPump : Game :=
  let g := mustApply wargModePump ⟨0⟩
    (.target (Target.permanent (namedPermanent wargModePump "Grizzly Bears").id))
  mustApply g ⟨0⟩ .pay

def resolvedWargPump : Game := passBoth paidWargPump

#guard resolvedWargPump.stack.isEmpty
#guard (namedPermanent resolvedWargPump "Grizzly Bears").status.plusOnePlusOne == 1
#guard resolvedWargPump.power (namedPermanent resolvedWargPump "Grizzly Bears") == 3
#guard resolvedWargPump.toughness (namedPermanent resolvedWargPump "Grizzly Bears") == 3
#guard resolvedWargPump.hasTrample (namedPermanent resolvedWargPump "Grizzly Bears")
#guard resolvedWargPump.hasHexproof (namedPermanent resolvedWargPump "Grizzly Bears")
#guard (resolvedWargPump.effectiveKeywords
  (namedPermanent resolvedWargPump "Grizzly Bears")).hexproof
#guard resolvedWargPump.log.any (fun s =>
  mentions s "gets a +1/+1 counter and gains trample and hexproof")

/-- A 0/0 survives after receiving a +1/+1 counter. -/
def zeroWithCounter : Game :=
  let g := addPermanent started zeroZero ⟨0⟩ ⟨0⟩
  let id := (namedPermanent g "Zero/Zero").id
  g.applyEffect ⟨0⟩ .plusOnePlusOneTrampleHexproof #[Target.permanent id]

#guard zeroWithCounter.power (namedPermanent zeroWithCounter "Zero/Zero") == 1
#guard zeroWithCounter.toughness (namedPermanent zeroWithCounter "Zero/Zero") == 1
#guard (zeroWithCounter.checkSBA).battlefield.any (fun o => o.name == "Zero/Zero")

/-- Hexproof wears off in cleanup; the counter does not. -/
def afterWargPumpCleanup : Game := passBoth (skipTo resolvedWargPump .end 80)

#guard (namedPermanent afterWargPumpCleanup "Grizzly Bears").status.plusOnePlusOne == 1
#guard afterWargPumpCleanup.power (namedPermanent afterWargPumpCleanup "Grizzly Bears") == 3
#guard !afterWargPumpCleanup.hasHexproof (namedPermanent afterWargPumpCleanup "Grizzly Bears")
#guard !afterWargPumpCleanup.hasTrample (namedPermanent afterWargPumpCleanup "Grizzly Bears")
#guard afterWargPumpCleanup.turnNumber == 2

/-- Granted trample assigns leftover combat damage. -/
def afterWargTrampleCombat : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g llanowarElves ⟨1⟩ ⟨1⟩
  let g := g.applyEffect ⟨0⟩ .plusOnePlusOneTrampleHexproof
    #[Target.permanent (namedPermanent g "Grizzly Bears").id]
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Grizzly Bears").id)])
  passBoth g

#guard afterWargTrampleCombat.log.any (fun s =>
  mentions s "Grizzly Bears deals 1 combat damage to Llanowar Elves")
#guard afterWargTrampleCombat.log.any (fun s =>
  mentions s "Grizzly Bears tramples for 2 to Nissa")
#guard (afterWargTrampleCombat.player ⟨1⟩).life == 18

/-- Nissa has Lightning Bolt while Chandra's pumped Grizzly Bears has hexproof. -/
def nissaBoltVsHexproof : Game :=
  let g := addPermanent resolvedWargPump mountain ⟨1⟩ ⟨1⟩
  let g := addToHand g lightningBolt ⟨1⟩
  mustApply g ⟨0⟩ .pass

#guard nissaBoltVsHexproof.hasPriority ⟨1⟩
#guard nissaBoltVsHexproof.canCast ⟨1⟩ (handCardNamed nissaBoltVsHexproof ⟨1⟩ "Lightning Bolt")

def proposedNissaBolt : Game :=
  mustApply nissaBoltVsHexproof ⟨1⟩
    (.cast (handCardNamed nissaBoltVsHexproof ⟨1⟩ "Lightning Bolt").id)

#guard
  match proposedNissaBolt.apply ⟨1⟩ (.target (Target.permanent
    (namedPermanent proposedNissaBolt "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

def paidNissaBoltPlayer : Game :=
  let g := mustApply proposedNissaBolt ⟨1⟩ (.target (Target.player ⟨0⟩))
  let g := tapNextMana g ⟨1⟩
  mustApply g ⟨1⟩ .pay

def resolvedNissaBoltPlayer : Game := passBoth paidNissaBoltPlayer

#guard (resolvedNissaBoltPlayer.player ⟨0⟩).life == 17
#guard resolvedNissaBoltPlayer.battlefield.any (fun o => o.name == "Grizzly Bears")

-- After hexproof wears off, the same creature is a legal Lightning Bolt target.
#guard
  (afterWargPumpCleanup.legalTargets ⟨1⟩ (.dealDamage 3)).contains
    (Target.permanent (namedPermanent afterWargPumpCleanup "Grizzly Bears").id)

/-- The agent casts Warg Tactics to destroy a flyer when that is the playable spell. -/
def agentWargDestroyOnly : Game :=
  let g := addPermanent afterDraw velvetwingButterflies ⟨1⟩ ⟨1⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2

#guard
  match Agent.choose agentWargDestroyOnly ⟨0⟩ with
  | some (.cast id) => (agentWargDestroyOnly.object! id).name == "Warg Tactics"
  | _ => false

/-- The agent casts Warg Tactics as a pump when no flyer is available. -/
def agentWargPumpOnly : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withGreenMana (addToHand g wargTactics ⟨0⟩) ⟨0⟩ 2

#guard
  match Agent.choose agentWargPumpOnly ⟨0⟩ with
  | some (.cast id) => (agentWargPumpOnly.object! id).name == "Warg Tactics"
  | _ => false

/-- Ragged Short Spear in hand, Grizzly Bears on the battlefield, enough mana. -/
def spearSetup : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  withRedMana (addToHand g raggedShortSpear ⟨0⟩) ⟨0⟩ 2

#guard spearSetup.canCast ⟨0⟩ (handCardNamed spearSetup ⟨0⟩ "Ragged Short Spear")
#guard spearSetup.asSorcery? ⟨0⟩
#guard !raggedShortSpear.requiresTarget
#guard raggedShortSpear.isEquipment

/-- Equipment is cast without announcing a creature (CR 301.5b). -/
def proposedSpear : Game :=
  mustApply spearSetup ⟨0⟩ (.cast (handCardNamed spearSetup ⟨0⟩ "Ragged Short Spear").id)

#guard proposedSpear.pending == .activateManaAbilities ⟨0⟩
#guard proposedSpear.stack.back!.targets.isEmpty
#guard proposedSpear.log.any (fun s => mentions s "begins casting Ragged Short Spear")

def paidSpear : Game := mustApply proposedSpear ⟨0⟩ .pay

#guard paidSpear.stack.size == 1
#guard paidSpear.hasPriority ⟨0⟩

/-- The Equipment enters unattached; the discard trigger waits on the stack. -/
def spearEntered : Game := passBoth paidSpear

#guard (namedPermanent spearEntered "Ragged Short Spear").attachedTo.isNone
#guard spearEntered.power (namedPermanent spearEntered "Grizzly Bears") == 2
#guard spearEntered.stack.size == 1
#guard spearEntered.log.any (fun s => mentions s "enters the battlefield")
#guard spearEntered.log.any (fun s => mentions s "enters trigger is put on the stack")

def spearMayDiscard : Game := passBoth spearEntered

#guard
  match spearMayDiscard.pending with
  | .mayDiscardDraw ⟨0⟩ 2 => true
  | _ => false
#guard spearMayDiscard.actor == some ⟨0⟩
#guard !spearMayDiscard.hasPriority ⟨0⟩
#guard spearMayDiscard.log.any (fun s => mentions s "may discard a card")
#guard spearMayDiscard.stack.isEmpty

/-- Declining the optional discard draws nothing. -/
def spearDeclined : Game := mustApply spearMayDiscard ⟨0⟩ .decline

#guard spearDeclined.pending == .none
#guard spearDeclined.hasPriority ⟨0⟩
#guard spearDeclined.log.any (fun s => mentions s "declines to discard")
#guard (spearDeclined.player ⟨0⟩).hand.size == (spearMayDiscard.player ⟨0⟩).hand.size
#guard (spearDeclined.player ⟨0⟩).library.size == (spearMayDiscard.player ⟨0⟩).library.size

-- The opponent cannot discard or decline for Chandra.
#guard
  match spearMayDiscard.apply ⟨1⟩ .decline with
  | .error msg => mentions msg "Only Chandra"
  | .ok _ => false
#guard
  match spearMayDiscard.apply ⟨1⟩
      (.discard (spearMayDiscard.player ⟨0⟩).hand.back!) with
  | .error msg => mentions msg "Only Chandra"
  | .ok _ => false

-- Discarding a card that is not in hand is illegal.
#guard
  match spearMayDiscard.apply ⟨0⟩
      (.discard (namedPermanent spearMayDiscard "Grizzly Bears").id) with
  | .error msg => mentions msg "not in your hand"
  | .ok _ => false

/-- Discard a known extra card, then draw the two known library tops. -/
def spearKnownLib : Game :=
  let g := addToHand spearEntered forest ⟨0⟩
  addToLibraryTop (addToLibraryTop g forest ⟨0⟩) llanowarElves ⟨0⟩

def spearKnownMayDiscard : Game := passBoth spearKnownLib

def spearDiscardedForest : Game :=
  mustApply spearKnownMayDiscard ⟨0⟩
    (.discard (handCardNamed spearKnownMayDiscard ⟨0⟩ "Forest").id)

#guard spearDiscardedForest.pending == .none
#guard spearDiscardedForest.hasPriority ⟨0⟩
#guard spearDiscardedForest.log.any (fun s => mentions s "discards Forest")
#guard spearDiscardedForest.log.any (fun s => mentions s "draws Llanowar Elves")
#guard spearDiscardedForest.log.any (fun s => mentions s "draws Forest")
#guard (spearDiscardedForest.handObjects ⟨0⟩).any (fun o => o.name == "Llanowar Elves")
#guard (spearDiscardedForest.handObjects ⟨0⟩).any (fun o => o.name == "Forest")
#guard (spearDiscardedForest.player ⟨0⟩).graveyard.any (fun id =>
  (spearDiscardedForest.object! id).name == "Forest")
#guard (spearDiscardedForest.player ⟨0⟩).hand.size ==
  (spearKnownMayDiscard.player ⟨0⟩).hand.size + 1

-- The heuristic discards the last card in hand.
#guard
  match Agent.choose spearKnownMayDiscard ⟨0⟩ with
  | some (.discard id) => id == (spearKnownMayDiscard.player ⟨0⟩).hand.back!
  | _ => false

/-- An empty hand skips the optional discard; no draw. -/
def spearEmptyHand : Game :=
  let g := { spearEntered with pending := .none, stack := #[] }
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with hand := #[] })
  g.beginMayDiscardDraw ⟨0⟩ 2

#guard spearEmptyHand.pending == .none
#guard spearEmptyHand.log.any (fun s => mentions s "has no card to discard")

/-- Equip {3} with a creature you control and enough mana. -/
def spearReadyToEquip : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g raggedShortSpear ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })
  withRedMana g ⟨0⟩ 3

def spearEquipAbility : ActivatedAbility :=
  raggedShortSpear.activatedAbilities[0]!

#guard spearReadyToEquip.canActivate ⟨0⟩
  (namedPermanent spearReadyToEquip "Ragged Short Spear") spearEquipAbility
#guard !(spearReadyToEquip.canActivate ⟨1⟩
  (namedPermanent spearReadyToEquip "Ragged Short Spear") spearEquipAbility)
#guard spearEquipAbility.onlyAsSorcery
#guard spearEquipAbility.effect.requiresTarget

-- Cannot Equip with no creature you control.
#guard
  let g := addPermanent afterDraw raggedShortSpear ⟨0⟩ ⟨0⟩
  let g := withRedMana g ⟨0⟩ 3
  !g.canActivate ⟨0⟩ (namedPermanent g "Ragged Short Spear") spearEquipAbility

-- Cannot Equip an opponent's creature: Equip needs a creature you control.
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g raggedShortSpear ⟨0⟩ ⟨0⟩
  let g := withRedMana g ⟨0⟩ 3
  !g.canActivate ⟨0⟩ (namedPermanent g "Ragged Short Spear") spearEquipAbility
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let g := addPermanent g raggedShortSpear ⟨0⟩ ⟨0⟩
  let g := withRedMana g ⟨0⟩ 3
  let g := mustApply g ⟨0⟩ (.activate (namedPermanent g "Ragged Short Spear").id 0)
  match g.apply ⟨0⟩ (.target (Target.permanent (namedPermanent g "Gray Ogre").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- Equip is sorcery-speed only (CR 702.6a).
#guard
  let g := applyIdle (passBoth (skipTo afterDraw .end 80))
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g raggedShortSpear ⟨0⟩ ⟨0⟩
  let g := withRedMana g ⟨0⟩ 3
  !g.asSorcery? ⟨0⟩ &&
    !g.canActivate ⟨0⟩ (namedPermanent g "Ragged Short Spear") spearEquipAbility

-- The heuristic Equips when {3} is available and a creature is controlled.
#guard
  match Agent.choose spearReadyToEquip ⟨0⟩ with
  | some (.activate id 0) =>
    (spearReadyToEquip.object! id).name == "Ragged Short Spear"
  | _ => false

def proposedEquip : Game :=
  mustApply spearReadyToEquip ⟨0⟩
    (.activate (namedPermanent spearReadyToEquip "Ragged Short Spear").id 0)

#guard
  match proposedEquip.pending with
  | .chooseTargets ⟨0⟩ => true
  | _ => false
#guard proposedEquip.log.any (fun s => mentions s "begins activating Ragged Short Spear")
#guard proposedEquip.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- The heuristic targets Chandra's creature.
#guard
  match Agent.choose proposedEquip ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (proposedEquip.object! tid).name == "Grizzly Bears"
  | _ => false

def targetedEquip : Game :=
  mustApply proposedEquip ⟨0⟩
    (.target (Target.permanent (namedPermanent proposedEquip "Grizzly Bears").id))

#guard targetedEquip.pending == .activateManaAbilities ⟨0⟩
#guard targetedEquip.stack.back!.targets ==
  #[Target.permanent (namedPermanent targetedEquip "Grizzly Bears").id]

def paidEquip : Game := mustApply targetedEquip ⟨0⟩ .pay

#guard paidEquip.pending == .none
#guard paidEquip.hasPriority ⟨0⟩
#guard (namedPermanent paidEquip "Ragged Short Spear").attachedTo.isNone
#guard paidEquip.log.any (fun s => mentions s "activates Ragged Short Spear")

def spearEquipped : Game := passBoth paidEquip

#guard (namedPermanent spearEquipped "Ragged Short Spear").attachedTo ==
  some (namedPermanent spearEquipped "Grizzly Bears").id
#guard spearEquipped.power (namedPermanent spearEquipped "Grizzly Bears") == 4
#guard spearEquipped.toughness (namedPermanent spearEquipped "Grizzly Bears") == 2
#guard (namedPermanent spearEquipped "Grizzly Bears").power == 2
#guard spearEquipped.log.any (fun s => mentions s "attaches to Grizzly Bears")

-- The heuristic does not re-equip a creature that is already equipped.
#guard
  let g := withRedMana spearEquipped ⟨0⟩ 3
  match Agent.choose g ⟨0⟩ with
  | some (.activate id 0) => (g.object! id).name != "Ragged Short Spear"
  | some .pass => true
  | some (.cast _) => true
  | _ => true

/-- The +2/+0 is a continuous effect, so it does not wear off in cleanup. -/
def afterSpearCleanup : Game := passBoth (skipTo spearEquipped .end 80)

#guard afterSpearCleanup.power (namedPermanent afterSpearCleanup "Grizzly Bears") == 4
#guard (namedPermanent afterSpearCleanup "Grizzly Bears").status.pumpPower == 0

/-- If the target leaves before Equip resolves, the ability does nothing. -/
def equipTargetGone : Game :=
  let id := (namedPermanent paidEquip "Grizzly Bears").id
  let (g, _) := paidEquip.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard (namedPermanent equipTargetGone "Ragged Short Spear").attachedTo.isNone
#guard equipTargetGone.log.any (fun s => mentions s "no longer in play")

/-- If the equipped creature leaves, the Equipment becomes unattached and stays
on the battlefield (CR 301.5c / 704.5n). -/
def afterEquippedHostLeaves : Game :=
  let id := (namedPermanent spearEquipped "Grizzly Bears").id
  let (g, _) := spearEquipped.move id (.graveyard ⟨0⟩) none
  g.checkSBA

#guard afterEquippedHostLeaves.log.any (fun s => mentions s "becomes unattached")
#guard afterEquippedHostLeaves.battlefield.any (fun o => o.name == "Ragged Short Spear")
#guard (namedPermanent afterEquippedHostLeaves "Ragged Short Spear").attachedTo.isNone
#guard !(afterEquippedHostLeaves.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard !(afterEquippedHostLeaves.log.any (fun s =>
  mentions s "Ragged Short Spear is put into its owner's graveyard"))

/-- Combat uses the equipped power. -/
def afterEquippedCombat : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addAttachedAura g raggedShortSpear (namedPermanent g "Grizzly Bears") ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[])
  passBoth g

#guard afterEquippedCombat.log.any (fun s =>
  mentions s "Grizzly Bears deals 4 combat damage to Nissa")
#guard (afterEquippedCombat.player ⟨1⟩).life == 16

/-- Move Equip from one creature to another. -/
def spearTwoCreatures : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g raggedShortSpear ⟨0⟩ ⟨0⟩
  withRedMana g ⟨0⟩ 3

def spearMovedToOgre : Game :=
  let g := mustApply spearTwoCreatures ⟨0⟩
    (.activate (namedPermanent spearTwoCreatures "Ragged Short Spear").id 0)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Grizzly Bears").id))
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  let g := withRedMana g ⟨0⟩ 3
  let g := mustApply g ⟨0⟩
    (.activate (namedPermanent g "Ragged Short Spear").id 0)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Gray Ogre").id))
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard spearMovedToOgre.power (namedPermanent spearMovedToOgre "Grizzly Bears") == 2
#guard spearMovedToOgre.power (namedPermanent spearMovedToOgre "Gray Ogre") == 4
#guard (namedPermanent spearMovedToOgre "Ragged Short Spear").attachedTo ==
  some (namedPermanent spearMovedToOgre "Gray Ogre").id

/-- Illegally attached Equipment becomes unattached and stays (CR 704.5n). -/
def spearOnMountain : Game :=
  let g := addPermanent started mountain ⟨0⟩ ⟨0⟩
  addAttachedAura g raggedShortSpear (namedPermanent g "Mountain") ⟨0⟩ ⟨0⟩

def spearUnattachedFromLand : Game := spearOnMountain.checkSBA

#guard spearUnattachedFromLand.log.any (fun s => mentions s "704.5n")
#guard (namedPermanent spearUnattachedFromLand "Ragged Short Spear").attachedTo.isNone
#guard spearUnattachedFromLand.battlefield.any (fun o => o.name == "Ragged Short Spear")

/-- The agent casts Ragged Short Spear when that is the playable spell. -/
def agentSpearOnly : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withRedMana (addToHand g raggedShortSpear ⟨0⟩) ⟨0⟩ 2

#guard
  match Agent.choose agentSpearOnly ⟨0⟩ with
  | some (.cast id) => (agentSpearOnly.object! id).name == "Ragged Short Spear"
  | _ => false

/- Crude Bent Blade: target opponent sacrifices a creature; Equip +2/+1. -/

/-- Crude Bent Blade in hand, Nissa has a Grizzly Bears, enough mana. -/
def bladeSetup : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  withBlackMana (addToHand g crudeBentBlade ⟨0⟩) ⟨0⟩ 3

#guard bladeSetup.canCast ⟨0⟩ (handCardNamed bladeSetup ⟨0⟩ "Crude Bent Blade")
#guard bladeSetup.asSorcery? ⟨0⟩
#guard !crudeBentBlade.requiresTarget
#guard crudeBentBlade.isEquipment
#guard crudeBentBlade.triggeredAbilities == #[.onEnterTargetOpponentSacrificesCreature]
#guard crudeBentBlade.staticAbilities == #[.equippedCreatureGets 2 1]

/-- Equipment is cast without announcing a creature (CR 301.5b). -/
def proposedBlade : Game :=
  mustApply bladeSetup ⟨0⟩ (.cast (handCardNamed bladeSetup ⟨0⟩ "Crude Bent Blade").id)

#guard proposedBlade.pending == .activateManaAbilities ⟨0⟩
#guard proposedBlade.stack.back!.targets.isEmpty
#guard proposedBlade.log.any (fun s => mentions s "begins casting Crude Bent Blade")

def paidBlade : Game := mustApply proposedBlade ⟨0⟩ .pay

#guard paidBlade.stack.size == 1
#guard paidBlade.hasPriority ⟨0⟩

/-- The Equipment enters unattached; the edict trigger waits for a target. -/
def bladeEntered : Game := passBoth paidBlade

#guard (namedPermanent bladeEntered "Crude Bent Blade").attachedTo.isNone
#guard bladeEntered.power (namedPermanent bladeEntered "Grizzly Bears") == 2
#guard bladeEntered.stack.size == 1
#guard bladeEntered.log.any (fun s => mentions s "enters the battlefield")
#guard bladeEntered.log.any (fun s => mentions s "enters trigger is put on the stack")
#guard
  match bladeEntered.pending with
  | .chooseTargets ⟨0⟩ => true
  | _ => false
#guard (bladeEntered.legalTriggerTargets ⟨0⟩ .onEnterTargetOpponentSacrificesCreature).contains
  (Target.player ⟨1⟩)
#guard !(bladeEntered.legalTriggerTargets ⟨0⟩ .onEnterTargetOpponentSacrificesCreature).contains
  (Target.player ⟨0⟩)
#guard (bladeEntered.object! bladeEntered.stack.back!.objectId).triggeredAbility ==
  some .onEnterTargetOpponentSacrificesCreature

-- Cannot target yourself or a creature; the trigger targets an opponent.
#guard
  match bladeEntered.apply ⟨0⟩ (.target (Target.player ⟨0⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match bladeEntered.apply ⟨0⟩
      (.target (Target.permanent (namedPermanent bladeEntered "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match bladeEntered.apply ⟨0⟩ .decline with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

-- The heuristic targets the opposing player.
#guard
  match Agent.choose bladeEntered ⟨0⟩ with
  | some (.target (Target.player q)) => q == ⟨1⟩
  | _ => false

def bladeTargeted : Game :=
  mustApply bladeEntered ⟨0⟩ (.target (Target.player ⟨1⟩))

#guard bladeTargeted.pending == .none
#guard bladeTargeted.stack.back!.targets == #[Target.player ⟨1⟩]
#guard bladeTargeted.log.any (fun s => mentions s "chooses Nissa")

/-- Resolving the trigger makes Nissa choose a creature to sacrifice. -/
def bladeMustSac : Game := passBoth bladeTargeted

#guard
  match bladeMustSac.pending with
  | .sacrificeCreature ⟨1⟩ => true
  | _ => false
#guard bladeMustSac.actor == some ⟨1⟩
#guard !bladeMustSac.hasPriority ⟨0⟩
#guard !bladeMustSac.hasPriority ⟨1⟩
#guard bladeMustSac.log.any (fun s => mentions s "must sacrifice a creature")
#guard bladeMustSac.stack.isEmpty
#guard (bladeMustSac.sacrificeCreatureChoices ⟨1⟩).any (fun o => o.name == "Grizzly Bears")
#guard (bladeMustSac.sacrificeCreatureChoices ⟨0⟩).isEmpty

-- Chandra cannot sacrifice for Nissa, and Nissa cannot sacrifice a land or skip.
#guard
  match bladeMustSac.apply ⟨0⟩
      (.sacrifice (namedPermanent bladeMustSac "Grizzly Bears").id) with
  | .error msg => mentions msg "Only Nissa"
  | .ok _ => false
#guard
  match bladeMustSac.apply ⟨1⟩ .pass with
  | .error msg => mentions msg "required choice"
  | .ok _ => false
#guard
  match bladeMustSac.apply ⟨1⟩ .decline with
  | .error msg => mentions msg "Not time to decline"
  | .ok _ => false
#guard
  let g := addPermanent bladeMustSac mountain ⟨1⟩ ⟨1⟩
  match g.apply ⟨1⟩ (.sacrifice (namedPermanent g "Mountain").id) with
  | .error msg => mentions msg "Can't sacrifice"
  | .ok _ => false

-- The heuristic sacrifices Nissa's creature.
#guard
  match Agent.choose bladeMustSac ⟨1⟩ with
  | some (.sacrifice id) => (bladeMustSac.object! id).name == "Grizzly Bears"
  | _ => false

def bladeSacrificed : Game :=
  mustApply bladeMustSac ⟨1⟩
    (.sacrifice (namedPermanent bladeMustSac "Grizzly Bears").id)

#guard bladeSacrificed.pending == .none
#guard bladeSacrificed.hasPriority ⟨0⟩
#guard bladeSacrificed.log.any (fun s => mentions s "sacrifices Grizzly Bears")
#guard !(bladeSacrificed.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard (bladeSacrificed.player ⟨1⟩).graveyard.any (fun id =>
  (bladeSacrificed.object! id).name == "Grizzly Bears")
#guard bladeSacrificed.battlefield.any (fun o => o.name == "Crude Bent Blade")

/-- Idle actions sacrifice the required creature so skipTo can proceed. -/
def bladeIdleSacrificed : Game := applyIdle bladeMustSac

#guard bladeIdleSacrificed.pending == .none
#guard bladeIdleSacrificed.log.any (fun s => mentions s "sacrifices Grizzly Bears")

/-- With no opposing creature, the trigger still targets and then does nothing. -/
def bladeNoCreatureSetup : Game :=
  withBlackMana (addToHand afterDraw crudeBentBlade ⟨0⟩) ⟨0⟩ 3

def bladeNoCreatureEntered : Game :=
  let g := mustApply bladeNoCreatureSetup ⟨0⟩
    (.cast (handCardNamed bladeNoCreatureSetup ⟨0⟩ "Crude Bent Blade").id)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard
  match bladeNoCreatureEntered.pending with
  | .chooseTargets ⟨0⟩ => true
  | _ => false
#guard (bladeNoCreatureEntered.legalTriggerTargets ⟨0⟩
  .onEnterTargetOpponentSacrificesCreature).contains (Target.player ⟨1⟩)

def bladeNoCreatureResolved : Game :=
  let g := mustApply bladeNoCreatureEntered ⟨0⟩ (.target (Target.player ⟨1⟩))
  passBoth g

#guard bladeNoCreatureResolved.pending == .none
#guard bladeNoCreatureResolved.hasPriority ⟨0⟩
#guard bladeNoCreatureResolved.log.any (fun s => mentions s "has no creature to sacrifice")
#guard bladeNoCreatureResolved.battlefield.any (fun o => o.name == "Crude Bent Blade")

-- Direct resolution with no announced target logs that the target is gone.
#guard
  (bladeNoCreatureResolved.applyTriggeredAbility ⟨0⟩
    .onEnterTargetOpponentSacrificesCreature none).log.any
    (fun s => mentions s "The target is no longer legal")

/-- Sacrificing Goblin Fireleaper still queues its dies trigger. -/
def bladeFireleaperSetup : Game :=
  let g := addPermanent afterDraw goblinFireleaper ⟨1⟩ ⟨1⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  withBlackMana (addToHand g crudeBentBlade ⟨0⟩) ⟨0⟩ 3

def bladeSacrificesFireleaper : Game :=
  let g := mustApply bladeFireleaperSetup ⟨0⟩
    (.cast (handCardNamed bladeFireleaperSetup ⟨0⟩ "Crude Bent Blade").id)
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  let g := mustApply g ⟨0⟩ (.target (Target.player ⟨1⟩))
  let g := passBoth g
  mustApply g ⟨1⟩ (.sacrifice (namedPermanent g "Goblin Fireleaper").id)

#guard bladeSacrificesFireleaper.log.any (fun s => mentions s "sacrifices Goblin Fireleaper")
#guard
  match bladeSacrificesFireleaper.pending with
  | .chooseTargets ⟨1⟩ => true
  | _ => false
#guard (bladeSacrificesFireleaper.object!
  bladeSacrificesFireleaper.stack.back!.objectId).triggeredAbility ==
  some .onDiesDealDamageEqualToPowerToOppCreature

/-- Equip {2} with a creature you control and enough mana. -/
def bladeReadyToEquip : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addPermanent g crudeBentBlade ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })
  withBlackMana g ⟨0⟩ 2

def bladeEquipAbility : ActivatedAbility :=
  crudeBentBlade.activatedAbilities[0]!

#guard bladeReadyToEquip.canActivate ⟨0⟩
  (namedPermanent bladeReadyToEquip "Crude Bent Blade") bladeEquipAbility
#guard !(bladeReadyToEquip.canActivate ⟨1⟩
  (namedPermanent bladeReadyToEquip "Crude Bent Blade") bladeEquipAbility)
#guard bladeEquipAbility.onlyAsSorcery
#guard bladeEquipAbility.effect.requiresTarget
#guard bladeEquipAbility.cost.mana == ManaCost.ofGeneric 2

-- Cannot Equip with no creature you control.
#guard
  let g := addPermanent afterDraw crudeBentBlade ⟨0⟩ ⟨0⟩
  let g := withBlackMana g ⟨0⟩ 2
  !g.canActivate ⟨0⟩ (namedPermanent g "Crude Bent Blade") bladeEquipAbility

-- The heuristic Equips when {2} is available and a creature is controlled.
#guard
  match Agent.choose bladeReadyToEquip ⟨0⟩ with
  | some (.activate id 0) =>
    (bladeReadyToEquip.object! id).name == "Crude Bent Blade"
  | _ => false

def proposedBladeEquip : Game :=
  mustApply bladeReadyToEquip ⟨0⟩
    (.activate (namedPermanent bladeReadyToEquip "Crude Bent Blade").id 0)

#guard
  match proposedBladeEquip.pending with
  | .chooseTargets ⟨0⟩ => true
  | _ => false

def targetedBladeEquip : Game :=
  mustApply proposedBladeEquip ⟨0⟩
    (.target (Target.permanent (namedPermanent proposedBladeEquip "Grizzly Bears").id))

def paidBladeEquip : Game := mustApply targetedBladeEquip ⟨0⟩ .pay

def bladeEquipped : Game := passBoth paidBladeEquip

#guard (namedPermanent bladeEquipped "Crude Bent Blade").attachedTo ==
  some (namedPermanent bladeEquipped "Grizzly Bears").id
#guard bladeEquipped.power (namedPermanent bladeEquipped "Grizzly Bears") == 4
#guard bladeEquipped.toughness (namedPermanent bladeEquipped "Grizzly Bears") == 3
#guard (namedPermanent bladeEquipped "Grizzly Bears").power == 2
#guard (namedPermanent bladeEquipped "Grizzly Bears").toughness == 2
#guard bladeEquipped.log.any (fun s => mentions s "attaches to Grizzly Bears")

-- The heuristic does not re-equip a creature that is already equipped.
#guard
  let g := withBlackMana bladeEquipped ⟨0⟩ 2
  match Agent.choose g ⟨0⟩ with
  | some (.activate id 0) => (g.object! id).name != "Crude Bent Blade"
  | some .pass => true
  | some (.cast _) => true
  | _ => true

/-- The +2/+1 is a continuous effect, so it does not wear off in cleanup. -/
def afterBladeCleanup : Game := passBoth (skipTo bladeEquipped .end 80)

#guard afterBladeCleanup.power (namedPermanent afterBladeCleanup "Grizzly Bears") == 4
#guard afterBladeCleanup.toughness (namedPermanent afterBladeCleanup "Grizzly Bears") == 3
#guard (namedPermanent afterBladeCleanup "Grizzly Bears").status.pumpPower == 0

/-- Combat uses the equipped power and toughness. -/
def afterEquippedBladeCombat : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addAttachedAura g crudeBentBlade (namedPermanent g "Grizzly Bears") ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[])
  passBoth g

#guard afterEquippedBladeCombat.log.any (fun s =>
  mentions s "Grizzly Bears deals 4 combat damage to Nissa")
#guard (afterEquippedBladeCombat.player ⟨1⟩).life == 16

/-- The agent casts Crude Bent Blade when that is the playable spell. -/
def agentBladeOnly : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withBlackMana (addToHand g crudeBentBlade ⟨0⟩) ⟨0⟩ 3

#guard
  match Agent.choose agentBladeOnly ⟨0⟩ with
  | some (.cast id) => (agentBladeOnly.object! id).name == "Crude Bent Blade"
  | _ => false

/- Beorn's Hospitality: landfall +1/+1 and lasting Bear animation. -/

def addForests (g : Game) (p : PlayerId) : Nat → Game
  | 0 => g
  | n + 1 => addPermanent (addForests g p n) forest p p

/-- Hospitality and Grizzly Bears in play; a Forest in hand. -/
def hospitalityLandfallSetup : Game :=
  let g := addPermanent afterDraw beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  addToHand g forest ⟨0⟩

#guard hospitalityLandfallSetup.canPlayLand ⟨0⟩
#guard beornsHospitality.triggeredAbilities == #[.onLandYouControlEntersPlusOnePlusOne]
#guard beornsHospitality.activatedAbilities[0]!.effect == .becomeBearCreatureWithLandsPT

def hospitalityLandPlayed : Game :=
  mustApply hospitalityLandfallSetup ⟨0⟩
    (.playLand (handCardNamed hospitalityLandfallSetup ⟨0⟩ "Forest").id)

#guard hospitalityLandPlayed.pending == .chooseTargets ⟨0⟩
#guard hospitalityLandPlayed.stack.size == 1
#guard (hospitalityLandPlayed.object! hospitalityLandPlayed.stack.back!.objectId).triggeredAbility ==
  some .onLandYouControlEntersPlusOnePlusOne
#guard hospitalityLandPlayed.stack.back!.targets.isEmpty
#guard hospitalityLandPlayed.log.any (fun s => mentions s "landfall trigger is put on the stack")
#guard hospitalityLandPlayed.log.any (fun s => mentions s "must choose a target (CR 603.3d")
#guard !hospitalityLandPlayed.hasPriority ⟨0⟩
#guard hospitalityLandPlayed.actor == some ⟨0⟩

-- The landfall trigger cannot target an opponent's creature or a player.
#guard
  let g := addPermanent hospitalityLandPlayed velvetwingButterflies ⟨1⟩ ⟨1⟩
  match g.apply ⟨0⟩ (.target (Target.permanent (namedPermanent g "Velvetwing Butterflies").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match hospitalityLandPlayed.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The heuristic targets a creature you control.
#guard
  match Agent.choose hospitalityLandPlayed ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (hospitalityLandPlayed.object! tid).name == "Grizzly Bears"
  | _ => false

def hospitalityLandfallTargeted : Game :=
  mustApply hospitalityLandPlayed ⟨0⟩
    (.target (Target.permanent (namedPermanent hospitalityLandPlayed "Grizzly Bears").id))

#guard hospitalityLandfallTargeted.pending == .none
#guard hospitalityLandfallTargeted.hasPriority ⟨0⟩
#guard hospitalityLandfallTargeted.stack.back!.targets ==
  #[Target.permanent (namedPermanent hospitalityLandfallTargeted "Grizzly Bears").id]
#guard hospitalityLandfallTargeted.log.any (fun s =>
  mentions s "chooses Grizzly Bears as a target")

def hospitalityLandfallResolved : Game := passBoth hospitalityLandfallTargeted

#guard hospitalityLandfallResolved.stack.isEmpty
#guard (namedPermanent hospitalityLandfallResolved "Grizzly Bears").status.plusOnePlusOne == 1
#guard hospitalityLandfallResolved.power
  (namedPermanent hospitalityLandfallResolved "Grizzly Bears") == 3
#guard hospitalityLandfallResolved.log.any (fun s => mentions s "gets a +1/+1 counter")

/-- No creature you control: the landfall trigger is removed (CR 603.3d). -/
def hospitalityNoTarget : Game :=
  let g := addPermanent afterDraw beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addPermanent g velvetwingButterflies ⟨1⟩ ⟨1⟩
  let g := addToHand g forest ⟨0⟩
  mustApply g ⟨0⟩ (.playLand (handCardNamed g ⟨0⟩ "Forest").id)

#guard hospitalityNoTarget.stack.isEmpty
#guard hospitalityNoTarget.hasPriority ⟨0⟩
#guard hospitalityNoTarget.log.any (fun s => mentions s "no legal target")

/-- An opponent's land does not trigger your landfall. -/
def nissaLandVsHospitality : Game :=
  let g := addPermanent afterDraw beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .end 80)
  let g := skipTo g .precombatMain 80
  let g := addToHand g forest ⟨1⟩
  mustApply g ⟨1⟩ (.playLand (handCardNamed g ⟨1⟩ "Forest").id)

#guard nissaLandVsHospitality.stack.isEmpty
#guard !(nissaLandVsHospitality.log.any (fun s => mentions s "landfall"))
#guard (namedPermanent nissaLandVsHospitality "Grizzly Bears").status.plusOnePlusOne == 0

/-- If the targeted creature leaves before resolution, the trigger does nothing. -/
def hospitalityTargetGone : Game :=
  let id := (namedPermanent hospitalityLandfallTargeted "Grizzly Bears").id
  let (g, _) := hospitalityLandfallTargeted.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard hospitalityTargetGone.log.any (fun s => mentions s "no longer in play")
#guard !(hospitalityTargetGone.battlefield.any (fun o => o.name == "Grizzly Bears"))

/-- Animate Beorn's Hospitality with three lands in play. -/
def hospitalityAnimateSetup : Game :=
  let g := addPermanent afterDraw beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addForests g ⟨0⟩ 3
  g.modifyPlayer ⟨0⟩ (fun pl =>
    { pl with
      manaPool := pl.manaPool.add (.colored .green) 7
      landsPlayedThisTurn := 1 })

#guard hospitalityAnimateSetup.canActivate ⟨0⟩
  (namedPermanent hospitalityAnimateSetup "Beorn's Hospitality")
  (beornsHospitality.activatedAbilities[0]!)
#guard !(namedPermanent hospitalityAnimateSetup "Beorn's Hospitality").isCreature
#guard hospitalityAnimateSetup.landsYouControl ⟨0⟩ == 3

def proposedHospitalityAnimate : Game :=
  mustApply hospitalityAnimateSetup ⟨0⟩
    (.activate (namedPermanent hospitalityAnimateSetup "Beorn's Hospitality").id 0)

#guard proposedHospitalityAnimate.pending == .activateManaAbilities ⟨0⟩
#guard proposedHospitalityAnimate.log.any (fun s => mentions s "begins activating Beorn's Hospitality")

def paidHospitalityAnimate : Game :=
  mustApply proposedHospitalityAnimate ⟨0⟩ .pay

#guard paidHospitalityAnimate.hasPriority ⟨0⟩
#guard paidHospitalityAnimate.stack.size == 1
#guard paidHospitalityAnimate.log.any (fun s => mentions s "activates Beorn's Hospitality")

def animatedHospitality : Game := passBoth paidHospitalityAnimate

#guard animatedHospitality.stack.isEmpty
#guard (namedPermanent animatedHospitality "Beorn's Hospitality").isCreature
#guard (namedPermanent animatedHospitality "Beorn's Hospitality").hasSubtype "Bear"
#guard (namedPermanent animatedHospitality "Beorn's Hospitality").printed.isEnchantment
#guard (namedPermanent animatedHospitality "Beorn's Hospitality").types.any (· == .creature)
#guard (namedPermanent animatedHospitality "Beorn's Hospitality").types.any (· == .enchantment)
#guard (namedPermanent animatedHospitality "Beorn's Hospitality").status.additionalCreature
#guard animatedHospitality.power
  (namedPermanent animatedHospitality "Beorn's Hospitality") == 3
#guard animatedHospitality.toughness
  (namedPermanent animatedHospitality "Beorn's Hospitality") == 3
#guard animatedHospitality.log.any (fun s => mentions s "becomes a Bear creature")

/-- The animation does not wear off in cleanup. -/
def afterHospitalityCleanup : Game := passBoth (skipTo animatedHospitality .end 80)

#guard (namedPermanent afterHospitalityCleanup "Beorn's Hospitality").isCreature
#guard afterHospitalityCleanup.power
  (namedPermanent afterHospitalityCleanup "Beorn's Hospitality") == 3

/-- 0/0 animated Hospitality dies (CR 704.5f). -/
def hospitalityZeroLands : Game :=
  let g := addPermanent afterDraw beornsHospitality ⟨0⟩ ⟨0⟩
  let g := withGreenMana g ⟨0⟩ 7
  let g := mustApply g ⟨0⟩
    (.activate (namedPermanent g "Beorn's Hospitality").id 0)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard !(hospitalityZeroLands.battlefield.any (fun o => o.name == "Beorn's Hospitality"))
#guard hospitalityZeroLands.log.any (fun s => mentions s "dies (toughness 0)")

/-- Pathmaker's printed setting ability uses lands you control. -/
def pathmakerWithLands : Game :=
  let g := addForests afterDraw ⟨0⟩ 2
  addPermanent g mirkwoodPathmaker ⟨0⟩ ⟨0⟩

#guard pathmakerWithLands.power (namedPermanent pathmakerWithLands "Mirkwood Pathmaker") == 2
#guard pathmakerWithLands.toughness
  (namedPermanent pathmakerWithLands "Mirkwood Pathmaker") == 2

/-- Landfall can target the animated Hospitality; P/T is lands plus counters. -/
def hospitalitySelfLandfall : Game :=
  let g := addPermanent afterDraw beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addForests g ⟨0⟩ 3
  let o := namedPermanent g "Beorn's Hospitality"
  let g := g.setObject { o with
    status := { o.status with
      additionalCreature := true
      additionalSubtypes := #["Bear"]
      grantedStaticAbilities := #[.powerToughnessEqualLandsYouControl] } }
  let g := addToHand g forest ⟨0⟩
  let g := mustApply g ⟨0⟩ (.playLand (handCardNamed g ⟨0⟩ "Forest").id)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Beorn's Hospitality").id))
  passBoth g

#guard (namedPermanent hospitalitySelfLandfall "Beorn's Hospitality").status.plusOnePlusOne == 1
#guard hospitalitySelfLandfall.power
  (namedPermanent hospitalitySelfLandfall "Beorn's Hospitality") ==
    Int.ofNat (hospitalitySelfLandfall.landsYouControl ⟨0⟩) + 1

/-- Summoning sickness: a Hospitality that entered this turn cannot attack
after it becomes a creature (CR 302.6). -/
def hospitalityEnteredThisTurn : Game :=
  let g := withGreenMana (addToHand afterDraw beornsHospitality ⟨0⟩) ⟨0⟩ 2
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Beorn's Hospitality").id)
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  let g := addForests g ⟨0⟩ 2
  let g := withGreenMana g ⟨0⟩ 7
  let g := mustApply g ⟨0⟩
    (.activate (namedPermanent g "Beorn's Hospitality").id 0)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard (namedPermanent hospitalityEnteredThisTurn "Beorn's Hospitality").isCreature
#guard !(hospitalityEnteredThisTurn.canAttack
  (namedPermanent hospitalityEnteredThisTurn "Beorn's Hospitality"))
#guard (namedPermanent hospitalityEnteredThisTurn "Beorn's Hospitality").status.summoningSick

/- The agent begins activating Hospitality when {5}{G}{G} is available. -/
#guard
  match Agent.choose hospitalityAnimateSetup ⟨0⟩ with
  | some (.activate id 0) =>
    (hospitalityAnimateSetup.object! id).name == "Beorn's Hospitality"
  | _ => false

/- Gandalf, Spark Starter: reach and divided-damage enters trigger (CR 601.2d). -/

/-- A flying attacker can be blocked by Gandalf (reach) but not by a Gray Ogre. -/
def flyerVsGandalf : Game :=
  let g := addPermanent started smaugTheGreatCalamity ⟨0⟩ ⟨0⟩
  let g := addPermanent g gandalfSparkStarter ⟨1⟩ ⟨1⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let smaug := namedPermanent g "Smaug, the Great Calamity"
  g.setObject { smaug with status := { smaug.status with attacking := true } }

#guard flyerVsGandalf.canBlock
  (namedPermanent flyerVsGandalf "Gandalf, Spark Starter")
  (namedPermanent flyerVsGandalf "Smaug, the Great Calamity")
#guard !flyerVsGandalf.canBlock
  (namedPermanent flyerVsGandalf "Gray Ogre")
  (namedPermanent flyerVsGandalf "Smaug, the Great Calamity")

/-- Gandalf in hand with enough mana to cast him. -/
def gandalfSetup : Game :=
  withRedMana (addToHand afterDraw gandalfSparkStarter ⟨0⟩) ⟨0⟩ 6

#guard gandalfSetup.canCast ⟨0⟩ (handCardNamed gandalfSetup ⟨0⟩ "Gandalf, Spark Starter")
#guard gandalfSetup.asSorcery? ⟨0⟩
#guard gandalfSparkStarter.hasSorcerySpeed

def proposedGandalf : Game :=
  mustApply gandalfSetup ⟨0⟩ (.cast (handCardNamed gandalfSetup ⟨0⟩ "Gandalf, Spark Starter").id)

#guard proposedGandalf.pending == .activateManaAbilities ⟨0⟩
#guard proposedGandalf.log.any (fun s => mentions s "begins casting Gandalf, Spark Starter")

def paidGandalf : Game := mustApply proposedGandalf ⟨0⟩ .pay

#guard paidGandalf.stack.size == 1
#guard paidGandalf.hasPriority ⟨0⟩
#guard paidGandalf.log.any (fun s => mentions s "casts Gandalf, Spark Starter")

/-- The creature enters; the divided-damage trigger waits for a division (CR 601.2d). -/
def gandalfEntered : Game := passBoth paidGandalf

#guard (namedPermanent gandalfEntered "Gandalf, Spark Starter").printed.power == some 4
#guard gandalfEntered.power (namedPermanent gandalfEntered "Gandalf, Spark Starter") == 4
#guard gandalfEntered.toughness (namedPermanent gandalfEntered "Gandalf, Spark Starter") == 3
#guard (namedPermanent gandalfEntered "Gandalf, Spark Starter").printed.keywords.reach
#guard gandalfEntered.stack.size == 1
#guard (gandalfEntered.object! gandalfEntered.stack.back!.objectId).triggeredAbility ==
  some (.onEnterDealDividedDamage 3 3)
#guard (gandalfEntered.object! gandalfEntered.stack.back!.objectId).sourceId ==
  some (namedPermanent gandalfEntered "Gandalf, Spark Starter").id
#guard gandalfEntered.stack.back!.targets.isEmpty
#guard gandalfEntered.stack.back!.dividedDamage.isEmpty
#guard gandalfEntered.pending == .chooseTargets ⟨0⟩
#guard gandalfEntered.actor == some ⟨0⟩
#guard !gandalfEntered.hasPriority ⟨0⟩
#guard gandalfEntered.log.any (fun s => mentions s "enters the battlefield")
#guard gandalfEntered.log.any (fun s => mentions s "enters trigger is put on the stack")
#guard gandalfEntered.log.any (fun s => mentions s "must divide 3 damage")
#guard gandalfEntered.announcingDividedDamage

-- The heuristic puts all 3 damage on the opponent.
#guard
  match Agent.choose gandalfEntered ⟨0⟩ with
  | some (.target (Target.player q)) => q == ⟨1⟩
  | _ => false

-- A player is a legal target; hexproof does not apply to players.
#guard (gandalfEntered.legalProposedTargets ⟨0⟩
  (gandalfEntered.object! gandalfEntered.stack.back!.objectId)).contains
  (Target.player ⟨1⟩)

-- `target` without an amount assigns all remaining damage (CR 601.2d).
def gandalfTargetedOpponent : Game :=
  mustApply gandalfEntered ⟨0⟩ (.target (Target.player ⟨1⟩))

#guard gandalfTargetedOpponent.pending == .none
#guard gandalfTargetedOpponent.hasPriority ⟨0⟩
#guard gandalfTargetedOpponent.stack.back!.targets == #[Target.player ⟨1⟩]
#guard gandalfTargetedOpponent.stack.back!.dividedDamage == #[3]
#guard gandalfTargetedOpponent.log.any (fun s =>
  mentions s "chooses Nissa to be dealt 3 damage (CR 601.2d)")

def gandalfResolvedOpponent : Game := passBoth gandalfTargetedOpponent

#guard gandalfResolvedOpponent.stack.isEmpty
#guard (gandalfResolvedOpponent.player ⟨1⟩).life == 17
#guard (gandalfResolvedOpponent.player ⟨0⟩).life == 20
#guard gandalfResolvedOpponent.log.any (fun s => mentions s "Nissa is dealt 3 damage")
#guard gandalfResolvedOpponent.battlefield.any (fun o => o.name == "Gandalf, Spark Starter")

-- Zero damage to a target is illegal.
#guard
  match gandalfEntered.apply ⟨0⟩ (.divideDamage #[(Target.player ⟨1⟩, 0)]) with
  | .error msg => mentions msg "at least 1 damage"
  | .ok _ => false

-- More than the remaining damage is illegal.
#guard
  match gandalfEntered.apply ⟨0⟩ (.divideDamage #[(Target.player ⟨1⟩, 4)]) with
  | .error msg => mentions msg "remains to divide"
  | .ok _ => false

-- `divideDamage` is not used for ordinary targeted spells.
#guard
  match proposedBolt.apply ⟨0⟩ (.divideDamage #[(Target.player ⟨1⟩, 3)]) with
  | .error msg => mentions msg "does not divide damage"
  | .ok _ => false

/-- An opposing 2/2 is in play so damage can be split. -/
def gandalfSplitSetup : Game :=
  addPermanent gandalfEntered grizzlyBears ⟨1⟩ ⟨1⟩

-- Multiple targets of one instance of the word “target” are chosen together
-- (CR 601.2c); leftover damage after that announcement is illegal.
#guard
  match gandalfSplitSetup.apply ⟨0⟩
      (.divideDamage #[(Target.permanent (namedPermanent gandalfSplitSetup "Grizzly Bears").id, 2)]) with
  | .error msg => mentions msg "Must assign all remaining damage"
  | .ok _ => false

-- Duplicate targets of one instance are illegal (CR 115.3).
#guard
  match gandalfSplitSetup.apply ⟨0⟩
      (.divideDamage #[(Target.player ⟨1⟩, 2), (Target.player ⟨1⟩, 1)]) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- Leaving leftover damage when more targets could still be chosen is illegal;
-- every target of this instance must be announced together.
#guard
  match gandalfSplitSetup.apply ⟨0⟩
      (.divideDamage #[(Target.player ⟨0⟩, 1), (Target.player ⟨1⟩, 1)]) with
  | .error msg => mentions msg "Must assign all remaining damage"
  | .ok _ => false

def gandalfSplitAnnounced : Game :=
  mustApply gandalfSplitSetup ⟨0⟩
    (.divideDamage #[
      (Target.player ⟨1⟩, 2),
      (Target.permanent (namedPermanent gandalfSplitSetup "Grizzly Bears").id, 1)])

#guard gandalfSplitAnnounced.pending == .none
#guard gandalfSplitAnnounced.hasPriority ⟨0⟩
#guard gandalfSplitAnnounced.stack.back!.targets.size == 2
#guard gandalfSplitAnnounced.stack.back!.dividedDamage == #[2, 1]
#guard gandalfSplitAnnounced.log.any (fun s =>
  mentions s "chooses Nissa to be dealt 2 damage")
#guard gandalfSplitAnnounced.log.any (fun s =>
  mentions s "chooses Grizzly Bears to be dealt 1 damage")

def gandalfSplitResolved : Game := passBoth gandalfSplitAnnounced

#guard gandalfSplitResolved.stack.isEmpty
#guard (gandalfSplitResolved.player ⟨1⟩).life == 18
#guard (namedPermanent gandalfSplitResolved "Grizzly Bears").status.damage == 1
#guard gandalfSplitResolved.log.any (fun s => mentions s "Nissa is dealt 2 damage")
#guard gandalfSplitResolved.log.any (fun s => mentions s "Grizzly Bears is dealt 1 damage")

/-- Three targets, 1 damage each. -/
def gandalfThreeAnnounced : Game :=
  let g := addPermanent gandalfEntered grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  mustApply g ⟨0⟩
    (.divideDamage #[
      (Target.player ⟨1⟩, 1),
      (Target.permanent (namedPermanent g "Grizzly Bears").id, 1),
      (Target.permanent (namedPermanent g "Gray Ogre").id, 1)])

#guard gandalfThreeAnnounced.stack.back!.dividedDamage == #[1, 1, 1]
#guard gandalfThreeAnnounced.pending == .none

def gandalfThreeResolved : Game := passBoth gandalfThreeAnnounced

#guard (gandalfThreeResolved.player ⟨1⟩).life == 19
#guard (namedPermanent gandalfThreeResolved "Grizzly Bears").status.damage == 1
#guard (namedPermanent gandalfThreeResolved "Gray Ogre").status.damage == 1

-- A fourth target of the same instance is illegal (CR 601.2d).
#guard
  let g := addPermanent gandalfEntered grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g ragingGoblin ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  match g.apply ⟨0⟩
      (.divideDamage #[
        (Target.player ⟨1⟩, 1),
        (Target.permanent (namedPermanent g "Grizzly Bears").id, 1),
        (Target.permanent (namedPermanent g "Raging Goblin").id, 1),
        (Target.permanent (namedPermanent g "Gray Ogre").id, 1)]) with
  | .error msg => mentions msg "Cannot choose more than 3 targets"
  | .ok _ => false

-- After every target of that instance is announced, a further announcement
-- is not a targeting step.
#guard
  match gandalfThreeAnnounced.apply ⟨0⟩
      (.divideDamage #[(Target.permanent (namedPermanent gandalfThreeAnnounced "Gray Ogre").id, 1)]) with
  | .error msg => mentions msg "Not time to choose targets"
  | .ok _ => false

/-- If a targeted creature leaves before resolution, that portion is skipped. -/
def gandalfTargetGone : Game :=
  let id := (namedPermanent gandalfSplitAnnounced "Grizzly Bears").id
  let (g, _) := gandalfSplitAnnounced.move id (.graveyard ⟨1⟩) none
  passBoth g

#guard (gandalfTargetGone.player ⟨1⟩).life == 18
#guard gandalfTargetGone.log.any (fun s => mentions s "Nissa is dealt 2 damage")
#guard gandalfTargetGone.log.any (fun s => mentions s "no longer in play")
#guard !(gandalfTargetGone.battlefield.any (fun o => o.name == "Grizzly Bears"))

/-- The trigger still deals damage if Gandalf has left (CR 113.7a). -/
def gandalfLeftBeforeTrigger : Game :=
  let id := (namedPermanent gandalfTargetedOpponent "Gandalf, Spark Starter").id
  let (g, _) := gandalfTargetedOpponent.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard (gandalfLeftBeforeTrigger.player ⟨1⟩).life == 17
#guard !(gandalfLeftBeforeTrigger.battlefield.any (fun o =>
  o.name == "Gandalf, Spark Starter"))
#guard (gandalfLeftBeforeTrigger.player ⟨0⟩).graveyard.any (fun id =>
  (gandalfLeftBeforeTrigger.object! id).name == "Gandalf, Spark Starter")

-- Hexproof makes an opposing creature an illegal target (CR 702.11b).
#guard
  let g := addPermanent gandalfEntered velvetwingButterflies ⟨1⟩ ⟨1⟩
  let o := namedPermanent g "Velvetwing Butterflies"
  let g := g.setObject { o with
    status := { o.status with untilEotKeywords := Keyword.hexproof } }
  match g.apply ⟨0⟩
      (.divideDamage #[(Target.permanent (namedPermanent g "Velvetwing Butterflies").id, 3)]) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

/-- The agent casts Gandalf when that is the playable spell. -/
def agentGandalfOnly : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  withRedMana (addToHand g gandalfSparkStarter ⟨0⟩) ⟨0⟩ 6

#guard
  match Agent.choose agentGandalfOnly ⟨0⟩ with
  | some (.cast id) => (agentGandalfOnly.object! id).name == "Gandalf, Spark Starter"
  | _ => false

/- Goblin Fireleaper: {1}{R} pump and a dies trigger. -/

def fireleaperAbility : ActivatedAbility :=
  goblinFireleaper.activatedAbilities[0]!

#guard fireleaperAbility.effect == .sourceGets 1 0
#guard fireleaperAbility.cost.mana == ManaCost.ofGenericAndColor 1 .red
#guard !fireleaperAbility.effect.requiresTarget
#guard goblinFireleaper.triggeredAbilities == #[.onDiesDealDamageEqualToPowerToOppCreature]

/-- Fireleaper in play with {1}{R} in the pool; a land drop is already used. -/
def fireleaperReady : Game :=
  let g := addPermanent afterDraw goblinFireleaper ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  withRedMana (g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })) ⟨0⟩ 2

def fireleaperSource (g : Game) : GameObject :=
  namedPermanent g "Goblin Fireleaper"

#guard fireleaperReady.canActivate ⟨0⟩ (fireleaperSource fireleaperReady) fireleaperAbility
#guard !(fireleaperReady.canActivate ⟨1⟩ (fireleaperSource fireleaperReady) fireleaperAbility)
#guard (fireleaperReady.player ⟨0⟩).manaPool.canPay fireleaperAbility.cost.mana
#guard fireleaperReady.power (fireleaperSource fireleaperReady) == 1

-- The heuristic pumps Fireleaper when {1}{R} is available.
#guard
  match Agent.choose fireleaperReady ⟨0⟩ with
  | some (.activate id 0) => id == (fireleaperSource fireleaperReady).id
  | _ => false

def proposedFireleaper : Game :=
  mustApply fireleaperReady ⟨0⟩ (.activate (fireleaperSource fireleaperReady).id 0)

#guard proposedFireleaper.pending == .activateManaAbilities ⟨0⟩
#guard proposedFireleaper.proposedSpell.isSome
#guard proposedFireleaper.stack.size == 1
#guard (proposedFireleaper.object! proposedFireleaper.stack.back!.objectId).abilityEffect ==
  some (.sourceGets 1 0)
#guard (namedPermanent proposedFireleaper "Goblin Fireleaper").isOnBattlefield
#guard proposedFireleaper.log.any (fun s => mentions s "begins activating Goblin Fireleaper")

-- Opponent cannot pay Chandra's activation.
#guard
  match proposedFireleaper.apply ⟨1⟩ .pay with
  | .error msg => mentions msg "Only Chandra"
  | .ok _ => false

def paidFireleaper : Game :=
  mustApply proposedFireleaper ⟨0⟩ .pay

#guard paidFireleaper.hasPriority ⟨0⟩
#guard paidFireleaper.stack.size == 1
#guard paidFireleaper.log.any (fun s => mentions s "activates Goblin Fireleaper")
#guard (namedPermanent paidFireleaper "Goblin Fireleaper").status.pumpPower == 0

def pumpedFireleaper : Game := passBoth paidFireleaper

#guard pumpedFireleaper.stack.isEmpty
#guard (namedPermanent pumpedFireleaper "Goblin Fireleaper").status.pumpPower == 1
#guard pumpedFireleaper.power (namedPermanent pumpedFireleaper "Goblin Fireleaper") == 2
#guard pumpedFireleaper.log.any (fun s => mentions s "Goblin Fireleaper gets +1/+0 until end of turn")

/-- A second activation stacks. -/
def fireleaperPumpedTwice : Game :=
  let g := withRedMana pumpedFireleaper ⟨0⟩ 2
  let g := mustApply g ⟨0⟩ (.activate (fireleaperSource g).id 0)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard fireleaperPumpedTwice.power (namedPermanent fireleaperPumpedTwice "Goblin Fireleaper") == 3
#guard (namedPermanent fireleaperPumpedTwice "Goblin Fireleaper").status.pumpPower == 2

/-- The +1/+0 wears off in cleanup. -/
def afterFireleaperCleanup : Game :=
  passBoth (skipTo pumpedFireleaper .end 80)

#guard afterFireleaperCleanup.power
  (namedPermanent afterFireleaperCleanup "Goblin Fireleaper") == 1
#guard (namedPermanent afterFireleaperCleanup "Goblin Fireleaper").status.pumpPower == 0

/-- If the source leaves before the pump resolves, the pump does not happen;
the dies trigger waits until after that ability resolves (CR 603.3). -/
def fireleaperPumpSourceGone : Game :=
  let id := (namedPermanent paidFireleaper "Goblin Fireleaper").id
  let (g, _) := paidFireleaper.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard fireleaperPumpSourceGone.log.any (fun s => mentions s "source is no longer in play")
#guard fireleaperPumpSourceGone.pending == .chooseTargets ⟨0⟩
#guard fireleaperPumpSourceGone.stack.size == 1
#guard (fireleaperPumpSourceGone.object! fireleaperPumpSourceGone.stack.back!.objectId).triggeredAbility ==
  some .onDiesDealDamageEqualToPowerToOppCreature

-- Instant-speed: Fireleaper can activate during the end step.
def fireleaperAtEndStep : Game := skipTo fireleaperReady .end 80

#guard fireleaperAtEndStep.step == .end
#guard fireleaperAtEndStep.canActivate ⟨0⟩ (fireleaperSource fireleaperAtEndStep)
  fireleaperAbility

/- Desolation Prowler: Pay 2 life for +2/+2, only once each turn. -/

def prowlerAbility : ActivatedAbility :=
  desolationProwler.activatedAbilities[0]!

#guard prowlerAbility.effect == .sourceGets 2 2
#guard prowlerAbility.cost.payLife == 2
#guard prowlerAbility.cost.mana == ManaCost.empty
#guard !prowlerAbility.cost.tap
#guard prowlerAbility.onceEachTurn
#guard !prowlerAbility.effect.requiresTarget

/-- Prowler in play; a land drop is already used so the heuristic can activate. -/
def prowlerReady : Game :=
  let g := addPermanent afterDraw desolationProwler ⟨0⟩ ⟨0⟩
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })

def prowlerSource (g : Game) : GameObject :=
  namedPermanent g "Desolation Prowler"

#guard prowlerReady.canActivate ⟨0⟩ (prowlerSource prowlerReady) prowlerAbility
#guard !(prowlerReady.canActivate ⟨1⟩ (prowlerSource prowlerReady) prowlerAbility)
#guard prowlerReady.power (prowlerSource prowlerReady) == 2
#guard prowlerReady.toughness (prowlerSource prowlerReady) == 2
#guard (prowlerReady.player ⟨0⟩).life == 20

-- The heuristic pays 2 life to pump when it would not lose the game.
#guard
  match Agent.choose prowlerReady ⟨0⟩ with
  | some (.activate id 0) => id == (prowlerSource prowlerReady).id
  | _ => false

-- Life payment is part of activation, so the ability is on the stack immediately.
def activatedProwler : Game :=
  mustApply prowlerReady ⟨0⟩ (.activate (prowlerSource prowlerReady).id 0)

#guard activatedProwler.pending == .none
#guard activatedProwler.hasPriority ⟨0⟩
#guard activatedProwler.stack.size == 1
#guard (activatedProwler.object! activatedProwler.stack.back!.objectId).abilityEffect ==
  some (.sourceGets 2 2)
#guard (activatedProwler.player ⟨0⟩).life == 18
#guard activatedProwler.log.any (fun s => mentions s "begins activating Desolation Prowler")
#guard activatedProwler.log.any (fun s => mentions s "pays 2 life (18 life)")
#guard activatedProwler.log.any (fun s => mentions s "activates Desolation Prowler")
#guard (namedPermanent activatedProwler "Desolation Prowler").status.activationsThisTurn == 1
#guard (namedPermanent activatedProwler "Desolation Prowler").status.pumpPower == 0

-- Payment of life is not damage (CR 118.3b).
#guard !(activatedProwler.log.any (fun s => mentions s "is dealt"))

def pumpedProwler : Game := passBoth activatedProwler

#guard pumpedProwler.stack.isEmpty
#guard (namedPermanent pumpedProwler "Desolation Prowler").status.pumpPower == 2
#guard (namedPermanent pumpedProwler "Desolation Prowler").status.pumpToughness == 2
#guard pumpedProwler.power (namedPermanent pumpedProwler "Desolation Prowler") == 4
#guard pumpedProwler.toughness (namedPermanent pumpedProwler "Desolation Prowler") == 4
#guard (pumpedProwler.player ⟨0⟩).life == 18
#guard pumpedProwler.log.any (fun s =>
  mentions s "Desolation Prowler gets +2/+2 until end of turn")

-- Only once each turn (CR 602.2b).
#guard !(pumpedProwler.canActivate ⟨0⟩ (prowlerSource pumpedProwler) prowlerAbility)
#guard
  match pumpedProwler.activateAbility ⟨0⟩ (prowlerSource pumpedProwler).id 0 with
  | .error msg => mentions msg "only once each turn"
  | .ok _ => false

/-- The +2/+2 wears off in cleanup, and the once-each-turn count resets. -/
def afterProwlerCleanup : Game :=
  passBoth (skipTo pumpedProwler .end 80)

#guard afterProwlerCleanup.power
  (namedPermanent afterProwlerCleanup "Desolation Prowler") == 2
#guard (namedPermanent afterProwlerCleanup "Desolation Prowler").status.pumpPower == 0
#guard (namedPermanent afterProwlerCleanup "Desolation Prowler").status.activationsThisTurn == 0

-- Instant-speed: Prowler can activate during the end step.
def prowlerAtEndStep : Game := skipTo prowlerReady .end 80

#guard prowlerAtEndStep.step == .end
#guard prowlerAtEndStep.canActivate ⟨0⟩ (prowlerSource prowlerAtEndStep) prowlerAbility

-- A player with 1 life cannot pay 2 life (CR 119.4).
#guard
  let g := prowlerReady.modifyPlayer ⟨0⟩ (fun pl => { pl with life := 1 })
  !g.canActivate ⟨0⟩ (prowlerSource g) prowlerAbility
#guard
  let g := prowlerReady.modifyPlayer ⟨0⟩ (fun pl => { pl with life := 1 })
  match g.activateAbility ⟨0⟩ (prowlerSource g).id 0 with
  | .error msg => mentions msg "cannot pay 2 life"
  | .ok _ => false

-- Paying 2 life from 2 life is legal, then CR 704.5a ends the game.
def prowlerPaysLastLife : Game :=
  let g := prowlerReady.modifyPlayer ⟨0⟩ (fun pl => { pl with life := 2 })
  mustApply g ⟨0⟩ (.activate (prowlerSource g).id 0)

#guard (prowlerPaysLastLife.player ⟨0⟩).life == 0
#guard prowlerPaysLastLife.over
#guard prowlerPaysLastLife.result == some (.won ⟨1⟩)
#guard prowlerPaysLastLife.log.any (fun s => mentions s "pays 2 life (0 life)")
#guard prowlerPaysLastLife.log.any (fun s => mentions s "loses the game (life total 0)")
#guard prowlerPaysLastLife.power (namedPermanent prowlerPaysLastLife "Desolation Prowler") == 2

-- The heuristic will not pay the last 2 life.
#guard
  let g := prowlerReady.modifyPlayer ⟨0⟩ (fun pl => { pl with life := 2 })
  match Agent.choose g ⟨0⟩ with
  | some (.activate _ 0) => false
  | _ => true

/-- Lethal damage puts the dies trigger on the stack (CR 700.4 / 603.3d). -/
def fireleaperDied : Game :=
  let o := namedPermanent fireleaperReady "Goblin Fireleaper"
  let g := fireleaperReady.setObject { o with status := { o.status with damage := 1 } }
  g.receivePriority ⟨0⟩

#guard fireleaperDied.pending == .chooseTargets ⟨0⟩
#guard fireleaperDied.stack.size == 1
#guard (fireleaperDied.object! fireleaperDied.stack.back!.objectId).triggeredAbility ==
  some .onDiesDealDamageEqualToPowerToOppCreature
#guard (fireleaperDied.object! fireleaperDied.stack.back!.objectId).lastKnownPower == some 1
#guard fireleaperDied.stack.back!.targets.isEmpty
#guard fireleaperDied.log.any (fun s => mentions s "dies from lethal damage")
#guard fireleaperDied.log.any (fun s => mentions s "dies trigger is put on the stack")
#guard fireleaperDied.log.any (fun s => mentions s "must choose a target (CR 603.3d")
#guard !(fireleaperDied.battlefield.any (fun o => o.name == "Goblin Fireleaper"))
#guard !fireleaperDied.hasPriority ⟨0⟩
#guard fireleaperDied.actor == some ⟨0⟩

-- The dies trigger cannot target a player or a creature you control.
#guard
  match fireleaperDied.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  let g := addPermanent fireleaperDied ragingGoblin ⟨0⟩ ⟨0⟩
  match g.apply ⟨0⟩ (.target (Target.permanent (namedPermanent g "Raging Goblin").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- Hexproof on an opponent's creature is not a legal target (CR 702.11b).
#guard
  let bears := namedPermanent fireleaperDied "Grizzly Bears"
  let g := fireleaperDied.setObject { bears with
    status := { bears.status with untilEotKeywords := Keyword.hexproof } }
  match g.apply ⟨0⟩ (.target (Target.permanent bears.id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The heuristic targets an opposing creature.
#guard
  match Agent.choose fireleaperDied ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (fireleaperDied.object! tid).name == "Grizzly Bears"
  | _ => false

def fireleaperDeathTargeted : Game :=
  mustApply fireleaperDied ⟨0⟩
    (.target (Target.permanent (namedPermanent fireleaperDied "Grizzly Bears").id))

#guard fireleaperDeathTargeted.pending == .none
#guard fireleaperDeathTargeted.hasPriority ⟨0⟩
#guard fireleaperDeathTargeted.stack.back!.targets ==
  #[Target.permanent (namedPermanent fireleaperDeathTargeted "Grizzly Bears").id]
#guard fireleaperDeathTargeted.log.any (fun s => mentions s "chooses Grizzly Bears as a target")

def fireleaperDeathResolved : Game := passBoth fireleaperDeathTargeted

#guard fireleaperDeathResolved.stack.isEmpty
#guard fireleaperDeathResolved.log.any (fun s =>
  mentions s "Goblin Fireleaper deals 1 damage to Grizzly Bears")
#guard (namedPermanent fireleaperDeathResolved "Grizzly Bears").status.damage == 1
#guard fireleaperDeathResolved.battlefield.any (fun o => o.name == "Grizzly Bears")

/-- Pumped power is last known information when the Fireleaper dies (CR 113.7a). -/
def fireleaperPumpedThenDied : Game :=
  let o := namedPermanent pumpedFireleaper "Goblin Fireleaper"
  let g := pumpedFireleaper.setObject { o with status := { o.status with damage := 1 } }
  let g := g.receivePriority ⟨0⟩
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Grizzly Bears").id))
  passBoth g

#guard fireleaperPumpedThenDied.log.any (fun s =>
  mentions s "Goblin Fireleaper deals 2 damage to Grizzly Bears")
#guard !(fireleaperPumpedThenDied.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard fireleaperPumpedThenDied.log.any (fun s => mentions s "Grizzly Bears dies from lethal damage")

/-- No opposing creature: the dies trigger is removed (CR 603.3d). -/
def fireleaperDiedAlone : Game :=
  let g := addPermanent afterDraw goblinFireleaper ⟨0⟩ ⟨0⟩
  let o := namedPermanent g "Goblin Fireleaper"
  let g := g.setObject { o with status := { o.status with damage := 1 } }
  g.receivePriority ⟨0⟩

#guard fireleaperDiedAlone.stack.isEmpty
#guard fireleaperDiedAlone.hasPriority ⟨0⟩
#guard fireleaperDiedAlone.log.any (fun s => mentions s "no legal target")
#guard !(fireleaperDiedAlone.battlefield.any (fun o => o.name == "Goblin Fireleaper"))

/-- If the targeted creature leaves before resolution, the trigger does nothing. -/
def fireleaperDeathTargetGone : Game :=
  let id := (namedPermanent fireleaperDeathTargeted "Grizzly Bears").id
  let (g, _) := fireleaperDeathTargeted.move id (.graveyard ⟨1⟩) none
  passBoth g

#guard fireleaperDeathTargetGone.log.any (fun s => mentions s "no longer in play")
#guard !(fireleaperDeathTargetGone.battlefield.any (fun o => o.name == "Grizzly Bears"))

/-- Combat: 1/1 Fireleaper into 2/2 Bears. Fireleaper dies; the trigger then
kills the Bears. -/
def fireleaperVsBearsCombat : Game :=
  addPermanent (addPermanent started goblinFireleaper ⟨0⟩ ⟨0⟩) grizzlyBears ⟨1⟩ ⟨1⟩

def fireleaperBlockedByBears : Game :=
  let g := passBoth (skipTo fireleaperVsBearsCombat .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Goblin Fireleaper").id])
  let g := passBoth g
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Goblin Fireleaper").id)])

#guard fireleaperBlockedByBears.stack.isEmpty
#guard fireleaperBlockedByBears.step == .declareBlockers

def fireleaperAfterCombatDamage : Game := passBoth fireleaperBlockedByBears

#guard fireleaperAfterCombatDamage.step == .combatDamage
#guard fireleaperAfterCombatDamage.pending == .chooseTargets ⟨0⟩
#guard !(fireleaperAfterCombatDamage.battlefield.any (fun o => o.name == "Goblin Fireleaper"))
#guard fireleaperAfterCombatDamage.battlefield.any (fun o => o.name == "Grizzly Bears")
#guard (namedPermanent fireleaperAfterCombatDamage "Grizzly Bears").status.damage == 1
#guard fireleaperAfterCombatDamage.log.any (fun s => mentions s "dies trigger is put on the stack")

def afterFireleaperBearsCombat : Game :=
  let g := mustApply fireleaperAfterCombatDamage ⟨0⟩
    (.target (Target.permanent (namedPermanent fireleaperAfterCombatDamage "Grizzly Bears").id))
  passBoth g

#guard afterFireleaperBearsCombat.log.any (fun s =>
  mentions s "Goblin Fireleaper deals 1 damage to Grizzly Bears")
#guard afterFireleaperBearsCombat.log.any (fun s => mentions s "Grizzly Bears dies from lethal damage")
#guard !(afterFireleaperBearsCombat.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard !(afterFireleaperBearsCombat.battlefield.any (fun o => o.name == "Goblin Fireleaper"))

/-- Both 1/1s die in combat: no remaining opposing creature, trigger removed. -/
def fireleaperVsElvesCombat : Game :=
  addPermanent (addPermanent started goblinFireleaper ⟨0⟩ ⟨0⟩) llanowarElves ⟨1⟩ ⟨1⟩

def afterFireleaperElvesCombat : Game :=
  let g := passBoth (skipTo fireleaperVsElvesCombat .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Goblin Fireleaper").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Goblin Fireleaper").id)])
  passBoth g

#guard afterFireleaperElvesCombat.stack.isEmpty
#guard afterFireleaperElvesCombat.pending == .none
#guard afterFireleaperElvesCombat.log.any (fun s => mentions s "no legal target")
#guard !(afterFireleaperElvesCombat.battlefield.any (fun o => o.name == "Goblin Fireleaper"))
#guard !(afterFireleaperElvesCombat.battlefield.any (fun o => o.name == "Llanowar Elves"))

/-- Sacrificing Fireleaper to Snowslope Hunter puts the dies trigger above the
activated ability. -/
def hunterSacrificesFireleaper : Game :=
  let g := addPermanent afterDraw snowslopeHunter ⟨0⟩ ⟨0⟩
  let g := addPermanent g goblinFireleaper ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addUntappedLand g mountain
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })
  let g := mustApply g ⟨0⟩ (.activate (namedPermanent g "Snowslope Hunter").id 0)
  let g := mustApply g ⟨0⟩ .pay
  mustApply g ⟨0⟩ (.sacrifice (namedPermanent g "Goblin Fireleaper").id)

#guard hunterSacrificesFireleaper.pending == .chooseTargets ⟨0⟩
#guard hunterSacrificesFireleaper.stack.size == 2
#guard (hunterSacrificesFireleaper.object! hunterSacrificesFireleaper.stack.back!.objectId).triggeredAbility ==
  some .onDiesDealDamageEqualToPowerToOppCreature
#guard hunterSacrificesFireleaper.log.any (fun s => mentions s "sacrifices Goblin Fireleaper")
#guard hunterSacrificesFireleaper.log.any (fun s => mentions s "dies trigger is put on the stack")

/- Galion, Elvenking's Butler: attack trigger sets another creature's base P/T. -/

def galionAndElves : Game :=
  addPermanent (addPermanent started galionElvenkingsButler ⟨0⟩ ⟨0⟩) llanowarElves ⟨0⟩ ⟨0⟩

#guard galionElvenkingsButler.triggeredAbilities == #[.onAttackSetOtherBasePT]
#guard galionAndElves.power (namedPermanent galionAndElves "Galion, Elvenking's Butler") == 4
#guard galionAndElves.power (namedPermanent galionAndElves "Llanowar Elves") == 1

def galionAttackDeclared : Game :=
  let g := passBoth (skipTo galionAndElves .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Galion, Elvenking's Butler").id])

#guard galionAttackDeclared.pending == .chooseTargets ⟨0⟩
#guard galionAttackDeclared.stack.size == 1
#guard (galionAttackDeclared.object! galionAttackDeclared.stack.back!.objectId).triggeredAbility ==
  some .onAttackSetOtherBasePT
#guard galionAttackDeclared.stack.back!.targets.isEmpty
#guard !galionAttackDeclared.stack.back!.targetsAnnounced
#guard galionAttackDeclared.log.any (fun s => mentions s "attack trigger is put on the stack")
#guard galionAttackDeclared.log.any (fun s => mentions s "must choose a target (CR 603.3d")
#guard !galionAttackDeclared.hasPriority ⟨0⟩
#guard galionAttackDeclared.actor == some ⟨0⟩

-- Cannot target Galion himself, an opponent's creature, or a player.
#guard
  match galionAttackDeclared.apply ⟨0⟩
      (.target (Target.permanent (namedPermanent galionAttackDeclared
        "Galion, Elvenking's Butler").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  let g := addPermanent galionAttackDeclared grizzlyBears ⟨1⟩ ⟨1⟩
  match g.apply ⟨0⟩ (.target (Target.permanent (namedPermanent g "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match galionAttackDeclared.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The heuristic targets the other creature you control.
#guard
  match Agent.choose galionAttackDeclared ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (galionAttackDeclared.object! tid).name == "Llanowar Elves"
  | _ => false

def galionTargeted : Game :=
  mustApply galionAttackDeclared ⟨0⟩
    (.target (Target.permanent (namedPermanent galionAttackDeclared "Llanowar Elves").id))

#guard galionTargeted.pending == .none
#guard galionTargeted.hasPriority ⟨0⟩
#guard galionTargeted.stack.back!.targets ==
  #[Target.permanent (namedPermanent galionTargeted "Llanowar Elves").id]
#guard galionTargeted.stack.back!.targetsAnnounced
#guard galionTargeted.log.any (fun s => mentions s "chooses Llanowar Elves as a target")

def galionResolved : Game := passBoth galionTargeted

#guard galionResolved.stack.isEmpty
#guard galionResolved.basePower (namedPermanent galionResolved "Llanowar Elves") == 4
#guard galionResolved.baseToughness (namedPermanent galionResolved "Llanowar Elves") == 4
#guard galionResolved.power (namedPermanent galionResolved "Llanowar Elves") == 4
#guard galionResolved.toughness (namedPermanent galionResolved "Llanowar Elves") == 4
#guard galionResolved.log.any (fun s =>
  mentions s "base power and toughness become 4/4 until end of turn")

/-- Counters on the target apply after the new base (CR 613.3c–d). -/
def galionOnCounteredElves : Game :=
  let g := galionAndElves
  let elves := namedPermanent g "Llanowar Elves"
  let g := g.setObject { elves with
    status := { elves.status with plusOnePlusOne := 1 } }
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩
    (.declareAttackers #[(namedPermanent g "Galion, Elvenking's Butler").id])
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Llanowar Elves").id))
  passBoth g

#guard galionOnCounteredElves.basePower (namedPermanent galionOnCounteredElves "Llanowar Elves") == 4
#guard galionOnCounteredElves.power (namedPermanent galionOnCounteredElves "Llanowar Elves") == 5
#guard (namedPermanent galionOnCounteredElves "Llanowar Elves").status.plusOnePlusOne == 1

/-- Uses Galion's actual P/T at resolution, including pumps (CR 613.3b ruling). -/
def galionPumpedResolved : Game :=
  let g := galionAndElves
  let g := g.applyEffect ⟨0⟩ (.pump 2 2)
    #[Target.permanent (namedPermanent g "Galion, Elvenking's Butler").id]
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩
    (.declareAttackers #[(namedPermanent g "Galion, Elvenking's Butler").id])
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Llanowar Elves").id))
  passBoth g

#guard galionPumpedResolved.power
  (namedPermanent galionPumpedResolved "Galion, Elvenking's Butler") == 6
#guard galionPumpedResolved.power (namedPermanent galionPumpedResolved "Llanowar Elves") == 6
#guard galionPumpedResolved.log.any (fun s =>
  mentions s "base power and toughness become 6/6 until end of turn")

/-- Later changes to Galion do not update the other creature. -/
def galionPumpedAfterResolve : Game :=
  galionResolved.applyEffect ⟨0⟩ (.pump 3 0)
    #[Target.permanent (namedPermanent galionResolved "Galion, Elvenking's Butler").id]

#guard galionPumpedAfterResolve.power
  (namedPermanent galionPumpedAfterResolve "Galion, Elvenking's Butler") == 7
#guard galionPumpedAfterResolve.power
  (namedPermanent galionPumpedAfterResolve "Llanowar Elves") == 4

/-- Overwrites a “P/T equal to lands you control” CDA (layer 7b over 7a). -/
def galionOnPathmaker : Game :=
  let g := addForests afterDraw ⟨0⟩ 2
  let g := addPermanent g galionElvenkingsButler ⟨0⟩ ⟨0⟩
  let g := addPermanent g mirkwoodPathmaker ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩
    (.declareAttackers #[(namedPermanent g "Galion, Elvenking's Butler").id])
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Mirkwood Pathmaker").id))
  passBoth g

#guard galionOnPathmaker.power (namedPermanent galionOnPathmaker "Mirkwood Pathmaker") == 4
#guard galionOnPathmaker.basePower (namedPermanent galionOnPathmaker "Mirkwood Pathmaker") == 4

/-- The set effect wears off in cleanup; Pathmaker returns to land-count P/T. -/
def afterGalionCleanup : Game := passBoth (skipTo galionResolved .end 80)

#guard afterGalionCleanup.power (namedPermanent afterGalionCleanup "Llanowar Elves") == 1
#guard afterGalionCleanup.basePower (namedPermanent afterGalionCleanup "Llanowar Elves") == 1
#guard (namedPermanent afterGalionCleanup "Llanowar Elves").status.setBasePower.isNone

def afterGalionPathmakerCleanup : Game := passBoth (skipTo galionOnPathmaker .end 80)

#guard afterGalionPathmakerCleanup.power
  (namedPermanent afterGalionPathmakerCleanup "Mirkwood Pathmaker") == 2

/-- “Up to one”: declining leaves the other creature unchanged. -/
def galionDeclined : Game :=
  let g := mustApply galionAttackDeclared ⟨0⟩ .decline
  passBoth g

#guard galionDeclined.stack.isEmpty
#guard galionDeclined.power (namedPermanent galionDeclined "Llanowar Elves") == 1
#guard galionDeclined.log.any (fun s => mentions s "chooses no target")
#guard galionDeclined.log.any (fun s => mentions s "No target was chosen")

/-- No other creature you control: the trigger still goes on the stack (CR 603.3d). -/
def galionAloneDeclared : Game :=
  let g := addPermanent started galionElvenkingsButler ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Galion, Elvenking's Butler").id])

#guard galionAloneDeclared.pending == .chooseTargets ⟨0⟩
#guard galionAloneDeclared.stack.size == 1
#guard (galionAloneDeclared.legalProposedTargets ⟨0⟩
  (galionAloneDeclared.object! galionAloneDeclared.stack.back!.objectId)).isEmpty
#guard
  match Agent.choose galionAloneDeclared ⟨0⟩ with
  | some .decline => true
  | _ => false

def galionAloneResolved : Game :=
  let g := mustApply galionAloneDeclared ⟨0⟩ .decline
  passBoth g

#guard galionAloneResolved.stack.isEmpty
#guard galionAloneResolved.log.any (fun s => mentions s "chooses no target")

/-- Last known P/T if Galion leaves before resolution (CR 113.7a). -/
def galionSourceGone : Game :=
  let g := galionTargeted
  let id := (namedPermanent g "Galion, Elvenking's Butler").id
  let (g, _) := g.move id (.graveyard (g.object! id).owner) none
  passBoth g

#guard galionSourceGone.stack.isEmpty
#guard !(galionSourceGone.battlefield.any (fun o => o.name == "Galion, Elvenking's Butler"))
#guard galionSourceGone.power (namedPermanent galionSourceGone "Llanowar Elves") == 4
#guard galionSourceGone.log.any (fun s =>
  mentions s "base power and toughness become 4/4 until end of turn")

/-- If the targeted creature leaves before resolution, the trigger does nothing. -/
def galionTargetGone : Game :=
  let id := (namedPermanent galionTargeted "Llanowar Elves").id
  let (g, _) := galionTargeted.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard galionTargetGone.log.any (fun s => mentions s "no longer in play")
#guard !(galionTargetGone.battlefield.any (fun o => o.name == "Llanowar Elves"))

/- Oliphaunt: attack trigger pumps another creature you control and grants trample. -/

def oliphauntAndOgre : Game :=
  addPermanent (addPermanent started oliphaunt ⟨0⟩ ⟨0⟩) grayOgre ⟨0⟩ ⟨0⟩

#guard oliphaunt.triggeredAbilities == #[.onAttackOtherGets2AndTrample]
#guard oliphauntAndOgre.hasTrample (namedPermanent oliphauntAndOgre "Oliphaunt")
#guard !oliphauntAndOgre.hasTrample (namedPermanent oliphauntAndOgre "Gray Ogre")
#guard oliphauntAndOgre.power (namedPermanent oliphauntAndOgre "Gray Ogre") == 2

def oliphauntAttackDeclared : Game :=
  let g := passBoth (skipTo oliphauntAndOgre .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Oliphaunt").id])

#guard oliphauntAttackDeclared.pending == .chooseTargets ⟨0⟩
#guard oliphauntAttackDeclared.stack.size == 1
#guard (oliphauntAttackDeclared.object! oliphauntAttackDeclared.stack.back!.objectId).triggeredAbility ==
  some .onAttackOtherGets2AndTrample
#guard oliphauntAttackDeclared.stack.back!.targets.isEmpty
#guard !oliphauntAttackDeclared.stack.back!.targetsAnnounced
#guard oliphauntAttackDeclared.log.any (fun s => mentions s "attack trigger is put on the stack")
#guard oliphauntAttackDeclared.log.any (fun s => mentions s "must choose a target (CR 603.3d")
#guard !oliphauntAttackDeclared.hasPriority ⟨0⟩
#guard oliphauntAttackDeclared.actor == some ⟨0⟩

-- Cannot target Oliphaunt himself, an opponent's creature, or a player.
#guard
  match oliphauntAttackDeclared.apply ⟨0⟩
      (.target (Target.permanent (namedPermanent oliphauntAttackDeclared "Oliphaunt").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  let g := addPermanent oliphauntAttackDeclared grizzlyBears ⟨1⟩ ⟨1⟩
  match g.apply ⟨0⟩ (.target (Target.permanent (namedPermanent g "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match oliphauntAttackDeclared.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The trigger is not optional: decline is illegal when a target is required.
#guard
  match oliphauntAttackDeclared.apply ⟨0⟩ .decline with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

-- The heuristic targets the other creature you control.
#guard
  match Agent.choose oliphauntAttackDeclared ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (oliphauntAttackDeclared.object! tid).name == "Gray Ogre"
  | _ => false

def oliphauntTargeted : Game :=
  mustApply oliphauntAttackDeclared ⟨0⟩
    (.target (Target.permanent (namedPermanent oliphauntAttackDeclared "Gray Ogre").id))

#guard oliphauntTargeted.pending == .none
#guard oliphauntTargeted.hasPriority ⟨0⟩
#guard oliphauntTargeted.stack.back!.targets ==
  #[Target.permanent (namedPermanent oliphauntTargeted "Gray Ogre").id]
#guard oliphauntTargeted.stack.back!.targetsAnnounced
#guard oliphauntTargeted.log.any (fun s => mentions s "chooses Gray Ogre as a target")

def oliphauntResolved : Game := passBoth oliphauntTargeted

#guard oliphauntResolved.stack.isEmpty
#guard oliphauntResolved.power (namedPermanent oliphauntResolved "Gray Ogre") == 4
#guard oliphauntResolved.toughness (namedPermanent oliphauntResolved "Gray Ogre") == 2
#guard oliphauntResolved.hasTrample (namedPermanent oliphauntResolved "Gray Ogre")
#guard (oliphauntResolved.effectiveKeywords
  (namedPermanent oliphauntResolved "Gray Ogre")).trample
#guard oliphauntResolved.log.any (fun s =>
  mentions s "gets +2/+0 and gains trample until end of turn")

-- Pump stacks with printed power; Oliphaunt itself is unchanged.
#guard oliphauntResolved.power (namedPermanent oliphauntResolved "Oliphaunt") == 6
#guard oliphauntResolved.hasTrample (namedPermanent oliphauntResolved "Oliphaunt")

/-- The pump and granted trample wear off in cleanup. -/
def afterOliphauntCleanup : Game := passBoth (skipTo oliphauntResolved .end 80)

#guard afterOliphauntCleanup.power (namedPermanent afterOliphauntCleanup "Gray Ogre") == 2
#guard !afterOliphauntCleanup.hasTrample (namedPermanent afterOliphauntCleanup "Gray Ogre")
#guard afterOliphauntCleanup.hasTrample (namedPermanent afterOliphauntCleanup "Oliphaunt")

/-- Granted trample assigns leftover combat damage (4/2 Ogre vs 1/1 Elves). -/
def oliphauntBothAttackDeclared : Game :=
  let g := passBoth (skipTo oliphauntAndOgre .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[
    (namedPermanent g "Oliphaunt").id,
    (namedPermanent g "Gray Ogre").id])

def oliphauntBothResolved : Game :=
  let g := mustApply oliphauntBothAttackDeclared ⟨0⟩
    (.target (Target.permanent (namedPermanent oliphauntBothAttackDeclared "Gray Ogre").id))
  passBoth g

#guard oliphauntBothResolved.power (namedPermanent oliphauntBothResolved "Gray Ogre") == 4
#guard oliphauntBothResolved.hasTrample (namedPermanent oliphauntBothResolved "Gray Ogre")
#guard (namedPermanent oliphauntBothResolved "Gray Ogre").status.attacking
#guard (namedPermanent oliphauntBothResolved "Oliphaunt").status.attacking

def afterOliphauntTrampleCombat : Game :=
  let g := addPermanent oliphauntBothResolved llanowarElves ⟨1⟩ ⟨1⟩
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Gray Ogre").id)])
  passBoth g

#guard afterOliphauntTrampleCombat.log.any (fun s =>
  mentions s "Gray Ogre deals 1 combat damage to Llanowar Elves")
#guard afterOliphauntTrampleCombat.log.any (fun s =>
  mentions s "Gray Ogre tramples for 3 to Nissa")
#guard afterOliphauntTrampleCombat.log.any (fun s =>
  mentions s "Oliphaunt deals 6 combat damage to Nissa")
#guard (afterOliphauntTrampleCombat.player ⟨1⟩).life == 11

/-- Without the trigger, the same Ogre assigns all damage to the blocker. -/
def ogreOnlyVsElves : Game :=
  addPermanent (addPermanent started grayOgre ⟨0⟩ ⟨0⟩) llanowarElves ⟨1⟩ ⟨1⟩

def afterOgreNoGrantedTrample : Game :=
  let g := passBoth (skipTo ogreOnlyVsElves .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Llanowar Elves").id,
    (namedPermanent g "Gray Ogre").id)])
  passBoth g

#guard afterOgreNoGrantedTrample.log.any (fun s =>
  mentions s "Gray Ogre deals 2 combat damage to Llanowar Elves")
#guard !afterOgreNoGrantedTrample.log.any (fun s => mentions s "tramples")
#guard (afterOgreNoGrantedTrample.player ⟨1⟩).life == 20

/-- No other creature you control: the trigger is removed (CR 603.3d). -/
def oliphauntAloneDeclared : Game :=
  let g := addPermanent started oliphaunt ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Oliphaunt").id])

#guard oliphauntAloneDeclared.stack.isEmpty
#guard oliphauntAloneDeclared.pending == .none
#guard oliphauntAloneDeclared.hasPriority ⟨0⟩
#guard oliphauntAloneDeclared.log.any (fun s => mentions s "no legal target")

/-- The effect does not depend on Oliphaunt remaining in play. -/
def oliphauntSourceGone : Game :=
  let g := oliphauntTargeted
  let id := (namedPermanent g "Oliphaunt").id
  let (g, _) := g.move id (.graveyard (g.object! id).owner) none
  passBoth g

#guard oliphauntSourceGone.stack.isEmpty
#guard !(oliphauntSourceGone.battlefield.any (fun o => o.name == "Oliphaunt"))
#guard oliphauntSourceGone.power (namedPermanent oliphauntSourceGone "Gray Ogre") == 4
#guard oliphauntSourceGone.hasTrample (namedPermanent oliphauntSourceGone "Gray Ogre")
#guard oliphauntSourceGone.log.any (fun s =>
  mentions s "gets +2/+0 and gains trample until end of turn")

/-- If the targeted creature leaves before resolution, the trigger does nothing. -/
def oliphauntTargetGone : Game :=
  let id := (namedPermanent oliphauntTargeted "Gray Ogre").id
  let (g, _) := oliphauntTargeted.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard oliphauntTargetGone.log.any (fun s => mentions s "no longer in play")
#guard !(oliphauntTargetGone.battlefield.any (fun o => o.name == "Gray Ogre"))

/- Lothlórien Lookout: attack trigger scries 1 (CR 508.2 / 701.20). -/

#guard lothlorienLookout.triggeredAbilities == #[.onAttackScry 1]
#guard lothlorienLookout.power == some 1
#guard lothlorienLookout.toughness == some 3

def lookoutOnBattlefield : Game :=
  addPermanent started lothlorienLookout ⟨0⟩ ⟨0⟩

#guard lookoutOnBattlefield.power (namedPermanent lookoutOnBattlefield "Lothlórien Lookout") == 1
#guard lookoutOnBattlefield.toughness (namedPermanent lookoutOnBattlefield "Lothlórien Lookout") == 3

def lookoutAttackDeclared : Game :=
  let g := passBoth (skipTo lookoutOnBattlefield .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Lothlórien Lookout").id])

#guard lookoutAttackDeclared.stack.size == 1
#guard (lookoutAttackDeclared.object! lookoutAttackDeclared.stack.back!.objectId).name ==
  "Lothlórien Lookout's ability"
#guard (lookoutAttackDeclared.object! lookoutAttackDeclared.stack.back!.objectId).triggeredAbility ==
  some (.onAttackScry 1)
#guard (lookoutAttackDeclared.object! lookoutAttackDeclared.stack.back!.objectId).sourceId ==
  some (namedPermanent lookoutAttackDeclared "Lothlórien Lookout").id
#guard lookoutAttackDeclared.log.any (fun s => mentions s "attack trigger is put on the stack")
#guard lookoutAttackDeclared.step == .declareAttackers
#guard lookoutAttackDeclared.hasPriority ⟨0⟩
#guard (namedPermanent lookoutAttackDeclared "Lothlórien Lookout").status.attacking

def lookoutScrying : Game := passBoth lookoutAttackDeclared

#guard
  match lookoutScrying.pending with
  | .scry ⟨0⟩ 1 => true
  | _ => false
#guard lookoutScrying.actor == some ⟨0⟩
#guard !lookoutScrying.hasPriority ⟨0⟩
#guard lookoutScrying.log.any (fun s => mentions s "scries 1")
#guard lookoutScrying.stack.isEmpty
#guard lookoutScrying.battlefield.any (fun o => o.name == "Lothlórien Lookout")

def lookoutScried : Game := keepScry lookoutScrying

#guard lookoutScried.pending == .none
#guard lookoutScried.hasPriority ⟨0⟩
#guard lookoutScried.battlefield.any (fun o => o.name == "Lothlórien Lookout")

-- The agent keeps scried cards on top.
#guard
  match Agent.choose lookoutScrying ⟨0⟩ with
  | some (.scry top bottom) =>
    bottom.isEmpty && top == lookoutScrying.scryLookedIds ⟨0⟩ 1
  | _ => false

/-- Known library: Forest on top; scry 1 looks at that card. -/
def lookoutKnownLib : Game :=
  addToLibraryTop lookoutAttackDeclared forest ⟨0⟩

def lookoutKnownScrying : Game := passBoth lookoutKnownLib

#guard
  let looked := lookoutKnownScrying.scryLookedIds ⟨0⟩ 1
  looked.size == 1 &&
    (lookoutKnownScrying.object! looked[0]!).name == "Forest"

def lookoutForestToBottom : Game :=
  let looked := lookoutKnownScrying.scryLookedIds ⟨0⟩ 1
  mustApply lookoutKnownScrying ⟨0⟩ (.scry #[] looked)

#guard
  let lib := (lookoutForestToBottom.player ⟨0⟩).library
  lib.size == (lookoutKnownScrying.player ⟨0⟩).library.size &&
    (lookoutForestToBottom.object! lib[0]!).name == "Forest"
#guard lookoutForestToBottom.log.any (fun s =>
  mentions s "puts Forest on the bottom of their library")

/-- The trigger still scries if Lothlórien Lookout has left the battlefield (CR 113.7a). -/
def lookoutLeftBeforeTrigger : Game :=
  let id := (namedPermanent lookoutKnownLib "Lothlórien Lookout").id
  let (g, _) := lookoutKnownLib.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard
  match lookoutLeftBeforeTrigger.pending with
  | .scry ⟨0⟩ 1 => true
  | _ => false
#guard !(lookoutLeftBeforeTrigger.battlefield.any (fun o => o.name == "Lothlórien Lookout"))
#guard (lookoutLeftBeforeTrigger.player ⟨0⟩).graveyard.any (fun id =>
  (lookoutLeftBeforeTrigger.object! id).name == "Lothlórien Lookout")
#guard
  let looked := lookoutLeftBeforeTrigger.scryLookedIds ⟨0⟩ 1
  looked.size == 1 &&
    (lookoutLeftBeforeTrigger.object! looked[0]!).name == "Forest"

/-- Another creature attacking does not trigger Lothlórien Lookout. -/
def lookoutIdleWhileBearsAttack : Game :=
  let g := addPermanent lookoutOnBattlefield grizzlyBears ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])

#guard lookoutIdleWhileBearsAttack.stack.isEmpty
#guard !lookoutIdleWhileBearsAttack.log.any (fun s => mentions s "attack trigger")
#guard (namedPermanent lookoutIdleWhileBearsAttack "Grizzly Bears").status.attacking
#guard !(namedPermanent lookoutIdleWhileBearsAttack "Lothlórien Lookout").status.attacking

/-- Entering the battlefield does not scry. -/
def lookoutSetup : Game :=
  withGreenMana (addToHand afterDraw lothlorienLookout ⟨0⟩) ⟨0⟩ 2

#guard lookoutSetup.canCast ⟨0⟩ (handCardNamed lookoutSetup ⟨0⟩ "Lothlórien Lookout")
#guard lookoutSetup.asSorcery? ⟨0⟩

def lookoutEntered : Game :=
  let g := mustApply lookoutSetup ⟨0⟩
    (.cast (handCardNamed lookoutSetup ⟨0⟩ "Lothlórien Lookout").id)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard lookoutEntered.stack.isEmpty
#guard lookoutEntered.pending == .none
#guard lookoutEntered.battlefield.any (fun o => o.name == "Lothlórien Lookout")
#guard !lookoutEntered.log.any (fun s => mentions s "scries")
#guard !lookoutEntered.log.any (fun s => mentions s "enters trigger")

/- Smaug, the Great Calamity // Spew Flame (CR 715). -/

/-- Smaug in hand, an opposing creature, and enough mana for either face. -/
def smaugSetup : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  withRedMana (addToHand g smaugTheGreatCalamity ⟨0⟩) ⟨0⟩ 7

#guard smaugTheGreatCalamity.hasAdventure
#guard smaugTheGreatCalamity.keywords.flying
#guard smaugSetup.canCast ⟨0⟩ (handCardNamed smaugSetup ⟨0⟩ "Smaug, the Great Calamity")
#guard smaugSetup.canCastAdventure ⟨0⟩ (handCardNamed smaugSetup ⟨0⟩ "Smaug, the Great Calamity")
#guard smaugSetup.asSorcery? ⟨0⟩

/-- Spew Flame requires a creature. -/
def smaugNoTarget : Game :=
  withRedMana (addToHand afterDraw smaugTheGreatCalamity ⟨0⟩) ⟨0⟩ 5

#guard !smaugNoTarget.canCastAdventure ⟨0⟩
  (handCardNamed smaugNoTarget ⟨0⟩ "Smaug, the Great Calamity")
#guard
  match smaugNoTarget.apply ⟨0⟩
      (.castAdventure (handCardNamed smaugNoTarget ⟨0⟩ "Smaug, the Great Calamity").id) with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

-- A card without an Adventure cannot be cast as one.
#guard
  match boltSetup.apply ⟨0⟩ (.castAdventure boltInHand.id) with
  | .error msg => mentions msg "has no Adventure"
  | .ok _ => false

def proposedSpewFlame : Game :=
  mustApply smaugSetup ⟨0⟩
    (.castAdventure (handCardNamed smaugSetup ⟨0⟩ "Smaug, the Great Calamity").id)

#guard proposedSpewFlame.pending == .chooseTargets ⟨0⟩
#guard (proposedSpewFlame.object! proposedSpewFlame.stack.back!.objectId).name == "Spew Flame"
#guard (proposedSpewFlame.object! proposedSpewFlame.stack.back!.objectId).printed.isSorcery
#guard (proposedSpewFlame.object! proposedSpewFlame.stack.back!.objectId).isAdventureSpell
#guard proposedSpewFlame.log.any (fun s => mentions s "begins casting Spew Flame")
#guard proposedSpewFlame.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- Spew Flame cannot target a player.
#guard
  match proposedSpewFlame.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The heuristic targets an opposing creature.
#guard
  match Agent.choose proposedSpewFlame ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (proposedSpewFlame.object! tid).name == "Grizzly Bears"
  | _ => false

def targetedSpewFlame : Game :=
  mustApply proposedSpewFlame ⟨0⟩
    (.target (Target.permanent (namedPermanent proposedSpewFlame "Grizzly Bears").id))

#guard targetedSpewFlame.pending == .activateManaAbilities ⟨0⟩
#guard targetedSpewFlame.stack.back!.targets ==
  #[Target.permanent (namedPermanent targetedSpewFlame "Grizzly Bears").id]

def paidSpewFlame : Game := mustApply targetedSpewFlame ⟨0⟩ .pay

#guard paidSpewFlame.hasPriority ⟨0⟩
#guard paidSpewFlame.log.any (fun s => mentions s "casts Spew Flame")
#guard (paidSpewFlame.object! paidSpewFlame.stack.back!.objectId).name == "Spew Flame"

def resolvedSpewFlame : Game := passBoth paidSpewFlame

#guard resolvedSpewFlame.stack.isEmpty
#guard !(resolvedSpewFlame.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard resolvedSpewFlame.log.any (fun s => mentions s "Grizzly Bears is dealt 5 damage")
#guard resolvedSpewFlame.objects.any (fun o =>
  o.zone == .exile && o.name == "Smaug, the Great Calamity")
#guard !((resolvedSpewFlame.player ⟨0⟩).graveyard.any (fun id =>
  (resolvedSpewFlame.object! id).name == "Smaug, the Great Calamity"))
#guard resolvedSpewFlame.log.any (fun s => mentions s "is exiled")
#guard resolvedSpewFlame.log.any (fun s => mentions s "may cast it for as long as it remains exiled")

def exiledSmaug (g : Game) : GameObject :=
  match g.objects.find? (fun o => o.zone == .exile && o.name == "Smaug, the Great Calamity") with
  | some o => o
  | none => panic! "expected Smaug, the Great Calamity in exile"

#guard resolvedSpewFlame.mayPlayFromExile ⟨0⟩ (exiledSmaug resolvedSpewFlame)
#guard !resolvedSpewFlame.canCastAdventure ⟨0⟩ (exiledSmaug resolvedSpewFlame)
#guard resolvedSpewFlame.adventureExileForbidsRecast (exiledSmaug resolvedSpewFlame)

-- The CR 715.3d permission does not allow recasting as an Adventure.
#guard
  match resolvedSpewFlame.castSpell ⟨0⟩ (exiledSmaug resolvedSpewFlame).id true with
  | .error msg => mentions msg "may not cast that card as an Adventure"
  | .ok _ => false

/-- Permission lasts past the end of the caster's next turn (CR 715.3d). -/
def smaugPermissionLater : Game :=
  let g := skipTo resolvedSpewFlame .end 80
  let g := passBoth g
  let g := skipTo g .end 80
  let g := passBoth g
  skipTo g .precombatMain 80

#guard smaugPermissionLater.activePlayer == ⟨0⟩
#guard smaugPermissionLater.mayPlayFromExile ⟨0⟩ (exiledSmaug smaugPermissionLater)
#guard !smaugPermissionLater.log.any (fun s =>
  mentions s "can no longer be played from exile")

/-- Cast Smaug from exile as the creature (CR 715.3d). -/
def smaugFromExileSetup : Game :=
  withRedMana resolvedSpewFlame ⟨0⟩ 7

#guard smaugFromExileSetup.canCast ⟨0⟩ (exiledSmaug smaugFromExileSetup)

def proposedExiledSmaug : Game :=
  mustApply smaugFromExileSetup ⟨0⟩ (.cast (exiledSmaug smaugFromExileSetup).id)

#guard proposedExiledSmaug.pending == .activateManaAbilities ⟨0⟩
#guard proposedExiledSmaug.log.any (fun s => mentions s "begins casting Smaug, the Great Calamity")
#guard (proposedExiledSmaug.object! proposedExiledSmaug.stack.back!.objectId).name ==
  "Smaug, the Great Calamity"
#guard !(proposedExiledSmaug.object! proposedExiledSmaug.stack.back!.objectId).isAdventureSpell

def resolvedExiledSmaug : Game :=
  passBoth (mustApply proposedExiledSmaug ⟨0⟩ .pay)

#guard resolvedExiledSmaug.stack.isEmpty
#guard resolvedExiledSmaug.battlefield.any (fun o => o.name == "Smaug, the Great Calamity")
#guard (namedPermanent resolvedExiledSmaug "Smaug, the Great Calamity").printed.keywords.flying
#guard resolvedExiledSmaug.power
  (namedPermanent resolvedExiledSmaug "Smaug, the Great Calamity") == 5
#guard resolvedExiledSmaug.toughness
  (namedPermanent resolvedExiledSmaug "Smaug, the Great Calamity") == 5
#guard resolvedExiledSmaug.log.any (fun s =>
  mentions s "Smaug, the Great Calamity enters the battlefield")
#guard !(resolvedExiledSmaug.objects.any (fun o =>
  o.zone == .exile && o.name == "Smaug, the Great Calamity"))

/-- Casting the creature from hand still works. -/
def proposedSmaugCreature : Game :=
  mustApply smaugSetup ⟨0⟩ (.cast (handCardNamed smaugSetup ⟨0⟩ "Smaug, the Great Calamity").id)

#guard proposedSmaugCreature.pending == .activateManaAbilities ⟨0⟩
#guard proposedSmaugCreature.log.any (fun s => mentions s "begins casting Smaug, the Great Calamity")
#guard (proposedSmaugCreature.object! proposedSmaugCreature.stack.back!.objectId).name ==
  "Smaug, the Great Calamity"

def resolvedSmaugCreature : Game :=
  passBoth (mustApply proposedSmaugCreature ⟨0⟩ .pay)

#guard (namedPermanent resolvedSmaugCreature "Smaug, the Great Calamity").printed.keywords.flying
#guard resolvedSmaugCreature.battlefield.any (fun o => o.name == "Grizzly Bears")

/-- Spew Flame is sorcery speed. -/
def smaugAtEndStep : Game := skipTo smaugSetup .end 80

#guard smaugAtEndStep.step == .end
#guard
  match smaugAtEndStep.apply ⟨0⟩
      (.castAdventure (handCardNamed smaugAtEndStep ⟨0⟩ "Smaug, the Great Calamity").id) with
  | .error msg => mentions msg "has sorcery speed"
  | .ok _ => false

/-- Reversing an unpaid Adventure returns the creature card to hand. -/
def unpaidSpewFlame : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addToHand g smaugTheGreatCalamity ⟨0⟩
  let g := mustApply g ⟨0⟩
    (.castAdventure (handCardNamed g ⟨0⟩ "Smaug, the Great Calamity").id)
  mustApply g ⟨0⟩ (.target (Target.permanent (namedPermanent g "Grizzly Bears").id))

def reversedSpewFlame : Game := mustApply unpaidSpewFlame ⟨0⟩ .pay

#guard reversedSpewFlame.stack.isEmpty
#guard (reversedSpewFlame.handObjects ⟨0⟩).any (fun o => o.name == "Smaug, the Great Calamity")
#guard reversedSpewFlame.log.any (fun s => mentions s "the casting is reversed")

/-- The heuristic casts Spew Flame when that is the playable spell. -/
def agentSmaugOnly : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withRedMana (addToHand g smaugTheGreatCalamity ⟨0⟩) ⟨0⟩ 5

#guard
  match Agent.choose agentSmaugOnly ⟨0⟩ with
  | some (.castAdventure id) =>
    (agentSmaugOnly.object! id).name == "Smaug, the Great Calamity"
  | _ => false

/-- With no opposing creature, the heuristic casts Smaug as a creature. -/
def agentSmaugCreatureOnly : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  withRedMana (addToHand g smaugTheGreatCalamity ⟨0⟩) ⟨0⟩ 7

#guard
  match Agent.choose agentSmaugCreatureOnly ⟨0⟩ with
  | some (.cast id) =>
    (agentSmaugCreatureOnly.object! id).name == "Smaug, the Great Calamity"
  | _ => false

/- Beorn, Reluctant Host // Till and Tend (CR 715, 305.2b). -/

/-- Beorn in hand with enough mana for Till and Tend. -/
def beornSetup : Game :=
  withGreenMana (addToHand afterDraw beornReluctantHost ⟨0⟩) ⟨0⟩ 2

#guard beornReluctantHost.hasAdventure
#guard beornReluctantHost.keywords.trample
#guard beornSetup.canCast ⟨0⟩ (handCardNamed beornSetup ⟨0⟩ "Beorn, Reluctant Host")
#guard beornSetup.canCastAdventure ⟨0⟩ (handCardNamed beornSetup ⟨0⟩ "Beorn, Reluctant Host")
#guard beornSetup.asSorcery? ⟨0⟩
#guard
  match beornReluctantHost.adventure with
  | some adv => !adv.toCardDef.requiresTarget
  | none => false

-- Without extra land plays, a second land is illegal (CR 305.2).
#guard
  let g := addToHand (addToHand afterDraw forest ⟨0⟩) forest ⟨0⟩
  let g := mustApply g ⟨0⟩ (.playLand (handCardNamed g ⟨0⟩ "Forest").id)
  match g.apply ⟨0⟩ (.playLand (handCardNamed g ⟨0⟩ "Forest").id) with
  | .error msg => mentions msg "Can't play a land now"
  | .ok _ => false

-- Extra land grants stack (CR 305.2b).
#guard
  let g := afterDraw.applyEffect ⟨0⟩ .playAdditionalLandThisTurn #[]
  let g := g.applyEffect ⟨0⟩ .playAdditionalLandThisTurn #[]
  (g.player ⟨0⟩).additionalLandsThisTurn == 2 && g.landPlaysAllowed ⟨0⟩ == 3

def proposedTillAndTend : Game :=
  mustApply beornSetup ⟨0⟩
    (.castAdventure (handCardNamed beornSetup ⟨0⟩ "Beorn, Reluctant Host").id)

#guard proposedTillAndTend.pending == .activateManaAbilities ⟨0⟩
#guard (proposedTillAndTend.object! proposedTillAndTend.stack.back!.objectId).name == "Till and Tend"
#guard (proposedTillAndTend.object! proposedTillAndTend.stack.back!.objectId).printed.isSorcery
#guard (proposedTillAndTend.object! proposedTillAndTend.stack.back!.objectId).isAdventureSpell
#guard proposedTillAndTend.log.any (fun s => mentions s "begins casting Till and Tend")
#guard proposedTillAndTend.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")

def paidTillAndTend : Game := mustApply proposedTillAndTend ⟨0⟩ .pay

#guard paidTillAndTend.hasPriority ⟨0⟩
#guard paidTillAndTend.log.any (fun s => mentions s "casts Till and Tend")
#guard (paidTillAndTend.object! paidTillAndTend.stack.back!.objectId).name == "Till and Tend"

def resolvedTillAndTend : Game := passBoth paidTillAndTend

#guard resolvedTillAndTend.stack.isEmpty
#guard resolvedTillAndTend.objects.any (fun o =>
  o.zone == .exile && o.name == "Beorn, Reluctant Host")
#guard !((resolvedTillAndTend.player ⟨0⟩).graveyard.any (fun id =>
  (resolvedTillAndTend.object! id).name == "Beorn, Reluctant Host"))
#guard resolvedTillAndTend.log.any (fun s => mentions s "is exiled")
#guard resolvedTillAndTend.log.any (fun s => mentions s "may cast it for as long as it remains exiled")
#guard resolvedTillAndTend.log.any (fun s => mentions s "may play an additional land this turn")
#guard (resolvedTillAndTend.player ⟨0⟩).additionalLandsThisTurn == 1
#guard resolvedTillAndTend.landPlaysAllowed ⟨0⟩ == 2
#guard resolvedTillAndTend.canPlayLand ⟨0⟩

def exiledBeorn (g : Game) : GameObject :=
  match g.objects.find? (fun o => o.zone == .exile && o.name == "Beorn, Reluctant Host") with
  | some o => o
  | none => panic! "expected Beorn, Reluctant Host in exile"

#guard resolvedTillAndTend.mayPlayFromExile ⟨0⟩ (exiledBeorn resolvedTillAndTend)
#guard !resolvedTillAndTend.canCastAdventure ⟨0⟩ (exiledBeorn resolvedTillAndTend)
#guard resolvedTillAndTend.adventureExileForbidsRecast (exiledBeorn resolvedTillAndTend)

-- The CR 715.3d permission does not allow recasting as an Adventure.
#guard
  match resolvedTillAndTend.castSpell ⟨0⟩ (exiledBeorn resolvedTillAndTend).id true with
  | .error msg => mentions msg "may not cast that card as an Adventure"
  | .ok _ => false

/-- Play a land, resolve Till and Tend, then play a second land. -/
def beornTwoLandsSetup : Game :=
  let g := addToHand afterDraw beornReluctantHost ⟨0⟩
  let g := addToHand g forest ⟨0⟩
  let g := addToHand g forest ⟨0⟩
  let g := addToHand g forest ⟨0⟩
  withGreenMana g ⟨0⟩ 2

def afterFirstForestForBeorn : Game :=
  mustApply beornTwoLandsSetup ⟨0⟩
    (.playLand (handCardNamed beornTwoLandsSetup ⟨0⟩ "Forest").id)

#guard (afterFirstForestForBeorn.player ⟨0⟩).landsPlayedThisTurn == 1
#guard !afterFirstForestForBeorn.canPlayLand ⟨0⟩

def resolvedTillAfterLand : Game :=
  let g := mustApply afterFirstForestForBeorn ⟨0⟩
    (.castAdventure (handCardNamed afterFirstForestForBeorn ⟨0⟩ "Beorn, Reluctant Host").id)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard resolvedTillAfterLand.canPlayLand ⟨0⟩
#guard (resolvedTillAfterLand.player ⟨0⟩).additionalLandsThisTurn == 1
#guard resolvedTillAfterLand.landPlaysAllowed ⟨0⟩ == 2

def afterSecondForestForBeorn : Game :=
  mustApply resolvedTillAfterLand ⟨0⟩
    (.playLand (handCardNamed resolvedTillAfterLand ⟨0⟩ "Forest").id)

#guard (afterSecondForestForBeorn.player ⟨0⟩).landsPlayedThisTurn == 2
#guard !afterSecondForestForBeorn.canPlayLand ⟨0⟩
#guard (afterSecondForestForBeorn.battlefield.filter (fun o => o.name == "Forest")).size == 2
#guard
  match afterSecondForestForBeorn.apply ⟨0⟩
      (.playLand (handCardNamed afterSecondForestForBeorn ⟨0⟩ "Forest").id) with
  | .error msg => mentions msg "Can't play a land now"
  | .ok _ => false

/-- Permission lasts past the end of the caster's next turn (CR 715.3d);
the extra land play does not. -/
def beornPermissionLater : Game :=
  let g := skipTo resolvedTillAndTend .end 80
  let g := passBoth g
  let g := skipTo g .end 80
  let g := passBoth g
  skipTo g .precombatMain 80

#guard beornPermissionLater.activePlayer == ⟨0⟩
#guard beornPermissionLater.mayPlayFromExile ⟨0⟩ (exiledBeorn beornPermissionLater)
#guard (beornPermissionLater.player ⟨0⟩).additionalLandsThisTurn == 0
#guard (beornPermissionLater.player ⟨0⟩).landsPlayedThisTurn == 0
#guard beornPermissionLater.landPlaysAllowed ⟨0⟩ == 1

/-- Cast Beorn from exile as the creature (CR 715.3d). -/
def beornFromExileSetup : Game :=
  withGreenMana resolvedTillAndTend ⟨0⟩ 5

#guard beornFromExileSetup.canCast ⟨0⟩ (exiledBeorn beornFromExileSetup)

def proposedExiledBeorn : Game :=
  mustApply beornFromExileSetup ⟨0⟩ (.cast (exiledBeorn beornFromExileSetup).id)

#guard proposedExiledBeorn.pending == .activateManaAbilities ⟨0⟩
#guard proposedExiledBeorn.log.any (fun s => mentions s "begins casting Beorn, Reluctant Host")
#guard (proposedExiledBeorn.object! proposedExiledBeorn.stack.back!.objectId).name ==
  "Beorn, Reluctant Host"
#guard !(proposedExiledBeorn.object! proposedExiledBeorn.stack.back!.objectId).isAdventureSpell

def resolvedExiledBeorn : Game :=
  passBoth (mustApply proposedExiledBeorn ⟨0⟩ .pay)

#guard resolvedExiledBeorn.stack.isEmpty
#guard resolvedExiledBeorn.battlefield.any (fun o => o.name == "Beorn, Reluctant Host")
#guard (namedPermanent resolvedExiledBeorn "Beorn, Reluctant Host").printed.keywords.trample
#guard resolvedExiledBeorn.power
  (namedPermanent resolvedExiledBeorn "Beorn, Reluctant Host") == 5
#guard resolvedExiledBeorn.toughness
  (namedPermanent resolvedExiledBeorn "Beorn, Reluctant Host") == 5
#guard resolvedExiledBeorn.log.any (fun s =>
  mentions s "Beorn, Reluctant Host enters the battlefield")
#guard !(resolvedExiledBeorn.objects.any (fun o =>
  o.zone == .exile && o.name == "Beorn, Reluctant Host"))

/-- Casting the creature from hand still works. -/
def proposedBeornCreature : Game :=
  mustApply (withGreenMana beornSetup ⟨0⟩ 5) ⟨0⟩
    (.cast (handCardNamed beornSetup ⟨0⟩ "Beorn, Reluctant Host").id)

#guard proposedBeornCreature.pending == .activateManaAbilities ⟨0⟩
#guard proposedBeornCreature.log.any (fun s => mentions s "begins casting Beorn, Reluctant Host")
#guard (proposedBeornCreature.object! proposedBeornCreature.stack.back!.objectId).name ==
  "Beorn, Reluctant Host"

def resolvedBeornCreature : Game :=
  passBoth (mustApply proposedBeornCreature ⟨0⟩ .pay)

#guard (namedPermanent resolvedBeornCreature "Beorn, Reluctant Host").printed.keywords.trample
#guard resolvedBeornCreature.power
  (namedPermanent resolvedBeornCreature "Beorn, Reluctant Host") == 5

/-- Till and Tend is sorcery speed. -/
def beornAtEndStep : Game := skipTo beornSetup .end 80

#guard beornAtEndStep.step == .end
#guard
  match beornAtEndStep.apply ⟨0⟩
      (.castAdventure (handCardNamed beornAtEndStep ⟨0⟩ "Beorn, Reluctant Host").id) with
  | .error msg => mentions msg "has sorcery speed"
  | .ok _ => false

/-- Reversing an unpaid Adventure returns the creature card to hand. -/
def unpaidTillAndTend : Game :=
  let g := addToHand afterDraw beornReluctantHost ⟨0⟩
  mustApply g ⟨0⟩
    (.castAdventure (handCardNamed g ⟨0⟩ "Beorn, Reluctant Host").id)

def reversedTillAndTend : Game := mustApply unpaidTillAndTend ⟨0⟩ .pay

#guard reversedTillAndTend.stack.isEmpty
#guard (reversedTillAndTend.handObjects ⟨0⟩).any (fun o => o.name == "Beorn, Reluctant Host")
#guard reversedTillAndTend.log.any (fun s => mentions s "the casting is reversed")

/-- The heuristic casts Till and Tend when that is the playable spell. -/
def agentBeornOnly : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  withGreenMana (addToHand g beornReluctantHost ⟨0⟩) ⟨0⟩ 2

#guard
  match Agent.choose agentBeornOnly ⟨0⟩ with
  | some (.castAdventure id) =>
    (agentBeornOnly.object! id).name == "Beorn, Reluctant Host"
  | _ => false

/-- With enough mana, the heuristic casts Beorn as a creature. -/
def agentBeornCreatureOnly : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  withGreenMana (addToHand g beornReluctantHost ⟨0⟩) ⟨0⟩ 5

#guard
  match Agent.choose agentBeornCreatureOnly ⟨0⟩ with
  | some (.cast id) =>
    (agentBeornCreatureOnly.object! id).name == "Beorn, Reluctant Host"
  | _ => false

/-- A sorcery Adventure is an instant-or-sorcery spell (CR 715.3b / 601.2i). -/
def paidTillWithGuttersnipe : Game :=
  let g := addPermanent beornSetup guttersnipe ⟨0⟩ ⟨0⟩
  let g := mustApply g ⟨0⟩
    (.castAdventure (handCardNamed g ⟨0⟩ "Beorn, Reluctant Host").id)
  mustApply g ⟨0⟩ .pay

#guard paidTillWithGuttersnipe.stack.size == 2
#guard (paidTillWithGuttersnipe.object! paidTillWithGuttersnipe.stack.back!.objectId).triggeredAbility ==
  some (.onCastInstantOrSorceryDealDamageToEachOpponent 2)
#guard (paidTillWithGuttersnipe.object! paidTillWithGuttersnipe.stack[0]!.objectId).name ==
  "Till and Tend"
#guard paidTillWithGuttersnipe.log.any (fun s => mentions s "casts Till and Tend")
#guard paidTillWithGuttersnipe.log.any (fun s => mentions s "cast trigger is put on the stack")

def tillWithGuttersnipeResolved : Game :=
  passBoth (passBoth paidTillWithGuttersnipe)

#guard (tillWithGuttersnipeResolved.player ⟨1⟩).life == 18
#guard (tillWithGuttersnipeResolved.player ⟨0⟩).additionalLandsThisTurn == 1

/-- Chandra's Gray Ogre attacks; Nissa has Olog-hai Crusher with no Goblin or Orc. -/
def ogreVsCrusher : Game :=
  addPermanent (addPermanent started grayOgre ⟨0⟩ ⟨0⟩) ologHaiCrusher ⟨1⟩ ⟨1⟩

def ogreVsCrusherReadyToBlock : Game :=
  let g := passBoth (skipTo ogreVsCrusher .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])
  passBoth g

#guard ogreVsCrusherReadyToBlock.pending == .declareBlockers
#guard
  let g := ogreVsCrusherReadyToBlock
  !g.canBlock (namedPermanent g "Olog-hai Crusher") (namedPermanent g "Gray Ogre")
#guard
  match ogreVsCrusherReadyToBlock.apply ⟨1⟩ (.declareBlockers #[(
    (namedPermanent ogreVsCrusherReadyToBlock "Olog-hai Crusher").id,
    (namedPermanent ogreVsCrusherReadyToBlock "Gray Ogre").id)]) with
  | .error msg => mentions msg "cannot block"
  | .ok _ => false

/-- Nissa's Goblin lets Olog-hai Crusher block. The Goblin need not block. -/
def ogreVsCrusherAndGoblin : Game :=
  addPermanent ogreVsCrusher ragingGoblin ⟨1⟩ ⟨1⟩

def ogreVsCrusherAndGoblinReadyToBlock : Game :=
  let g := passBoth (skipTo ogreVsCrusherAndGoblin .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])
  passBoth g

#guard
  let g := ogreVsCrusherAndGoblinReadyToBlock
  g.canBlock (namedPermanent g "Olog-hai Crusher") (namedPermanent g "Gray Ogre")

def crusherBlocksOgre : Game :=
  let g := ogreVsCrusherAndGoblinReadyToBlock
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Olog-hai Crusher").id,
    (namedPermanent g "Gray Ogre").id)])

#guard (namedPermanent crusherBlocksOgre "Olog-hai Crusher").status.blocking ==
  #[(namedPermanent crusherBlocksOgre "Gray Ogre").id]
#guard (namedPermanent crusherBlocksOgre "Gray Ogre").status.blocked
#guard crusherBlocksOgre.log.any (fun s => mentions s "Olog-hai Crusher blocks Gray Ogre")

/-- A tapped Goblin still enables blocking (it does not have to block). -/
def ogreVsCrusherTappedGoblinReadyToBlock : Game :=
  let g := ogreVsCrusherAndGoblinReadyToBlock
  let goblin := namedPermanent g "Raging Goblin"
  g.setObject { goblin with status := { goblin.status with tapped := true } }

#guard
  let g := ogreVsCrusherTappedGoblinReadyToBlock
  g.canBlock (namedPermanent g "Olog-hai Crusher") (namedPermanent g "Gray Ogre")
#guard !(ogreVsCrusherTappedGoblinReadyToBlock.canBlock
  (namedPermanent ogreVsCrusherTappedGoblinReadyToBlock "Raging Goblin")
  (namedPermanent ogreVsCrusherTappedGoblinReadyToBlock "Gray Ogre"))

/-- An Orc also enables blocking. -/
def ogreVsCrusherAndOrc : Game :=
  addPermanent ogreVsCrusher orcishSiegemaster ⟨1⟩ ⟨1⟩

def ogreVsCrusherAndOrcReadyToBlock : Game :=
  let g := passBoth (skipTo ogreVsCrusherAndOrc .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])
  passBoth g

#guard
  let g := ogreVsCrusherAndOrcReadyToBlock
  g.canBlock (namedPermanent g "Olog-hai Crusher") (namedPermanent g "Gray Ogre")

/-- An opponent's Goblin does not enable blocking. -/
def ogreVsCrusherOppGoblin : Game :=
  addPermanent ogreVsCrusher ragingGoblin ⟨0⟩ ⟨0⟩

def ogreVsCrusherOppGoblinReadyToBlock : Game :=
  let g := passBoth (skipTo ogreVsCrusherOppGoblin .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])
  passBoth g

#guard
  let g := ogreVsCrusherOppGoblinReadyToBlock
  !g.canBlock (namedPermanent g "Olog-hai Crusher") (namedPermanent g "Gray Ogre")

/-- Whether you control a Goblin or Orc is checked only when declaring blockers. -/
def crusherStillBlockingAfterGoblinLeaves : Game :=
  let g := crusherBlocksOgre
  let goblin := namedPermanent g "Raging Goblin"
  (g.move goblin.id (.graveyard ⟨1⟩) none).1

#guard !(crusherStillBlockingAfterGoblinLeaves.battlefield.any
  (fun o => o.name == "Raging Goblin"))
#guard (namedPermanent crusherStillBlockingAfterGoblinLeaves "Olog-hai Crusher").status.blocking ==
  #[(namedPermanent crusherStillBlockingAfterGoblinLeaves "Gray Ogre").id]

/-- A Goblin still does not let Crusher block a flyer. -/
def flyerVsCrusherAndGoblinReadyToBlock : Game :=
  let g := addPermanent (addPermanent (addPermanent started greatFierceBee ⟨0⟩ ⟨0⟩)
    ologHaiCrusher ⟨1⟩ ⟨1⟩) ragingGoblin ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Great Fierce Bee").id])
  passBoth g

#guard
  let g := flyerVsCrusherAndGoblinReadyToBlock
  !g.canBlock (namedPermanent g "Olog-hai Crusher") (namedPermanent g "Great Fierce Bee")

/-- Crusher can attack without a Goblin or Orc; printed trample assigns leftover. -/
def crusherReadyToAttack : Game :=
  passBoth (skipTo (addPermanent started ologHaiCrusher ⟨0⟩ ⟨0⟩) .beginningOfCombat 80)

#guard crusherReadyToAttack.canAttack (namedPermanent crusherReadyToAttack "Olog-hai Crusher")
#guard crusherReadyToAttack.hasTrample (namedPermanent crusherReadyToAttack "Olog-hai Crusher")

def afterCrusherTrample : Game :=
  let g := addPermanent (addPermanent started ologHaiCrusher ⟨0⟩ ⟨0⟩)
    grizzlyBears ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Olog-hai Crusher").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Olog-hai Crusher").id)])
  passBoth g

#guard afterCrusherTrample.log.any (fun s =>
  mentions s "Olog-hai Crusher deals 2 combat damage to Grizzly Bears")
#guard afterCrusherTrample.log.any (fun s =>
  mentions s "Olog-hai Crusher tramples for 2 to Nissa")
#guard (afterCrusherTrample.player ⟨1⟩).life == 18

/- Inferno Titan: {R} pump and enters-or-attacks divided damage (CR 601.2d / 508.2). -/

def titanAbility : ActivatedAbility :=
  infernoTitan.activatedAbilities[0]!

#guard titanAbility.effect == .sourceGets 1 0
#guard titanAbility.cost.mana == ManaCost.ofColor .red
#guard !titanAbility.effect.requiresTarget
#guard infernoTitan.triggeredAbilities == #[.onEnterOrAttackDealDividedDamage 3 3]

/-- Inferno Titan in hand with enough mana to cast it. -/
def titanSetup : Game :=
  withRedMana (addToHand afterDraw infernoTitan ⟨0⟩) ⟨0⟩ 6

#guard titanSetup.canCast ⟨0⟩ (handCardNamed titanSetup ⟨0⟩ "Inferno Titan")
#guard titanSetup.asSorcery? ⟨0⟩
#guard infernoTitan.hasSorcerySpeed

def proposedTitan : Game :=
  mustApply titanSetup ⟨0⟩ (.cast (handCardNamed titanSetup ⟨0⟩ "Inferno Titan").id)

#guard proposedTitan.pending == .activateManaAbilities ⟨0⟩
#guard proposedTitan.log.any (fun s => mentions s "begins casting Inferno Titan")

def paidTitan : Game := mustApply proposedTitan ⟨0⟩ .pay

#guard paidTitan.stack.size == 1
#guard paidTitan.hasPriority ⟨0⟩
#guard paidTitan.log.any (fun s => mentions s "casts Inferno Titan")

/-- The creature enters; the divided-damage trigger waits for a division (CR 601.2d). -/
def titanEntered : Game := passBoth paidTitan

#guard (namedPermanent titanEntered "Inferno Titan").printed.power == some 6
#guard titanEntered.power (namedPermanent titanEntered "Inferno Titan") == 6
#guard titanEntered.toughness (namedPermanent titanEntered "Inferno Titan") == 6
#guard titanEntered.stack.size == 1
#guard (titanEntered.object! titanEntered.stack.back!.objectId).triggeredAbility ==
  some (.onEnterOrAttackDealDividedDamage 3 3)
#guard (titanEntered.object! titanEntered.stack.back!.objectId).sourceId ==
  some (namedPermanent titanEntered "Inferno Titan").id
#guard titanEntered.stack.back!.targets.isEmpty
#guard titanEntered.stack.back!.dividedDamage.isEmpty
#guard titanEntered.pending == .chooseTargets ⟨0⟩
#guard titanEntered.actor == some ⟨0⟩
#guard !titanEntered.hasPriority ⟨0⟩
#guard titanEntered.log.any (fun s => mentions s "enters the battlefield")
#guard titanEntered.log.any (fun s => mentions s "enters trigger is put on the stack")
#guard titanEntered.log.any (fun s => mentions s "must divide 3 damage")
#guard titanEntered.announcingDividedDamage

-- The heuristic puts all 3 damage on the opponent.
#guard
  match Agent.choose titanEntered ⟨0⟩ with
  | some (.target (Target.player q)) => q == ⟨1⟩
  | _ => false

def titanTargetedOpponent : Game :=
  mustApply titanEntered ⟨0⟩ (.target (Target.player ⟨1⟩))

#guard titanTargetedOpponent.pending == .none
#guard titanTargetedOpponent.hasPriority ⟨0⟩
#guard titanTargetedOpponent.stack.back!.targets == #[Target.player ⟨1⟩]
#guard titanTargetedOpponent.stack.back!.dividedDamage == #[3]
#guard titanTargetedOpponent.log.any (fun s =>
  mentions s "chooses Nissa to be dealt 3 damage (CR 601.2d)")

def titanResolvedOpponent : Game := passBoth titanTargetedOpponent

#guard titanResolvedOpponent.stack.isEmpty
#guard (titanResolvedOpponent.player ⟨1⟩).life == 17
#guard (titanResolvedOpponent.player ⟨0⟩).life == 20
#guard titanResolvedOpponent.log.any (fun s => mentions s "Nissa is dealt 3 damage")
#guard titanResolvedOpponent.battlefield.any (fun o => o.name == "Inferno Titan")

/-- Split 2 to the opponent and 1 to a creature. -/
def titanSplitAnnounced : Game :=
  let g := addPermanent titanEntered grizzlyBears ⟨1⟩ ⟨1⟩
  mustApply g ⟨0⟩
    (.divideDamage #[
      (Target.player ⟨1⟩, 2),
      (Target.permanent (namedPermanent g "Grizzly Bears").id, 1)])

#guard titanSplitAnnounced.stack.back!.dividedDamage == #[2, 1]

def titanSplitResolved : Game := passBoth titanSplitAnnounced

#guard (titanSplitResolved.player ⟨1⟩).life == 18
#guard (namedPermanent titanSplitResolved "Grizzly Bears").status.damage == 1

/-- Inferno Titan already in play so it can attack (no ETB from `addPermanent`). -/
def titanOnBattlefield : Game :=
  addPermanent started infernoTitan ⟨0⟩ ⟨0⟩

def titanAttackDeclared : Game :=
  let g := passBoth (skipTo titanOnBattlefield .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Inferno Titan").id])

#guard titanAttackDeclared.pending == .chooseTargets ⟨0⟩
#guard titanAttackDeclared.stack.size == 1
#guard (titanAttackDeclared.object! titanAttackDeclared.stack.back!.objectId).triggeredAbility ==
  some (.onEnterOrAttackDealDividedDamage 3 3)
#guard (titanAttackDeclared.object! titanAttackDeclared.stack.back!.objectId).sourceId ==
  some (namedPermanent titanAttackDeclared "Inferno Titan").id
#guard titanAttackDeclared.stack.back!.targets.isEmpty
#guard titanAttackDeclared.stack.back!.dividedDamage.isEmpty
#guard titanAttackDeclared.log.any (fun s => mentions s "attack trigger is put on the stack")
#guard titanAttackDeclared.log.any (fun s => mentions s "must divide 3 damage")
#guard titanAttackDeclared.announcingDividedDamage
#guard !titanAttackDeclared.hasPriority ⟨0⟩
#guard titanAttackDeclared.actor == some ⟨0⟩
#guard (namedPermanent titanAttackDeclared "Inferno Titan").status.attacking

-- The heuristic still dumps all 3 on the opponent on attack.
#guard
  match Agent.choose titanAttackDeclared ⟨0⟩ with
  | some (.target (Target.player q)) => q == ⟨1⟩
  | _ => false

def titanAttackResolved : Game :=
  let g := mustApply titanAttackDeclared ⟨0⟩ (.target (Target.player ⟨1⟩))
  passBoth g

#guard titanAttackResolved.stack.isEmpty
#guard (titanAttackResolved.player ⟨1⟩).life == 17
#guard titanAttackResolved.log.any (fun s => mentions s "Nissa is dealt 3 damage")
#guard (namedPermanent titanAttackResolved "Inferno Titan").status.attacking

/-- The trigger still deals damage if Inferno Titan has left (CR 113.7a). -/
def titanLeftBeforeAttackTrigger : Game :=
  let g := mustApply titanAttackDeclared ⟨0⟩ (.target (Target.player ⟨1⟩))
  let id := (namedPermanent g "Inferno Titan").id
  let (g, _) := g.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard (titanLeftBeforeAttackTrigger.player ⟨1⟩).life == 17
#guard !(titanLeftBeforeAttackTrigger.battlefield.any (fun o => o.name == "Inferno Titan"))

/-- Inferno Titan in play with {R} in the pool; a land drop is already used. -/
def titanPumpReady : Game :=
  let g := addPermanent afterDraw infernoTitan ⟨0⟩ ⟨0⟩
  withRedMana (g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })) ⟨0⟩ 1

def titanSource (g : Game) : GameObject :=
  namedPermanent g "Inferno Titan"

#guard titanPumpReady.canActivate ⟨0⟩ (titanSource titanPumpReady) titanAbility
#guard !(titanPumpReady.canActivate ⟨1⟩ (titanSource titanPumpReady) titanAbility)
#guard (titanPumpReady.player ⟨0⟩).manaPool.canPay titanAbility.cost.mana
#guard titanPumpReady.power (titanSource titanPumpReady) == 6

-- The heuristic pumps Inferno Titan when {R} is available.
#guard
  match Agent.choose titanPumpReady ⟨0⟩ with
  | some (.activate id 0) => id == (titanSource titanPumpReady).id
  | _ => false

def proposedTitanPump : Game :=
  mustApply titanPumpReady ⟨0⟩ (.activate (titanSource titanPumpReady).id 0)

#guard proposedTitanPump.pending == .activateManaAbilities ⟨0⟩
#guard proposedTitanPump.proposedSpell.isSome
#guard proposedTitanPump.stack.size == 1
#guard (proposedTitanPump.object! proposedTitanPump.stack.back!.objectId).abilityEffect ==
  some (.sourceGets 1 0)
#guard proposedTitanPump.log.any (fun s => mentions s "begins activating Inferno Titan")

def paidTitanPump : Game :=
  mustApply proposedTitanPump ⟨0⟩ .pay

#guard paidTitanPump.hasPriority ⟨0⟩
#guard paidTitanPump.stack.size == 1
#guard paidTitanPump.log.any (fun s => mentions s "activates Inferno Titan")
#guard (namedPermanent paidTitanPump "Inferno Titan").status.pumpPower == 0

def pumpedTitan : Game := passBoth paidTitanPump

#guard pumpedTitan.stack.isEmpty
#guard (namedPermanent pumpedTitan "Inferno Titan").status.pumpPower == 1
#guard pumpedTitan.power (namedPermanent pumpedTitan "Inferno Titan") == 7
#guard pumpedTitan.log.any (fun s => mentions s "Inferno Titan gets +1/+0 until end of turn")

/-- A second activation stacks. -/
def titanPumpedTwice : Game :=
  let g := withRedMana pumpedTitan ⟨0⟩ 1
  let g := mustApply g ⟨0⟩ (.activate (titanSource g).id 0)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard titanPumpedTwice.power (namedPermanent titanPumpedTwice "Inferno Titan") == 8
#guard (namedPermanent titanPumpedTwice "Inferno Titan").status.pumpPower == 2

/-- The +1/+0 wears off in cleanup. -/
def afterTitanCleanup : Game :=
  passBoth (skipTo pumpedTitan .end 80)

#guard afterTitanCleanup.power (namedPermanent afterTitanCleanup "Inferno Titan") == 6
#guard (namedPermanent afterTitanCleanup "Inferno Titan").status.pumpPower == 0

/-- If the source leaves before the pump resolves, the pump does not happen. -/
def titanPumpSourceGone : Game :=
  let id := (namedPermanent paidTitanPump "Inferno Titan").id
  let (g, _) := paidTitanPump.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard titanPumpSourceGone.log.any (fun s => mentions s "source is no longer in play")
#guard titanPumpSourceGone.stack.isEmpty
#guard !(titanPumpSourceGone.battlefield.any (fun o => o.name == "Inferno Titan"))

-- Instant-speed: Inferno Titan can activate during the end step.
def titanAtEndStep : Game := skipTo titanPumpReady .end 80

#guard titanAtEndStep.step == .end
#guard titanAtEndStep.canActivate ⟨0⟩ (titanSource titanAtEndStep) titanAbility

/-- The agent casts Inferno Titan when that is the playable spell. -/
def agentTitanOnly : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  withRedMana (addToHand g infernoTitan ⟨0⟩) ⟨0⟩ 6

#guard
  match Agent.choose agentTitanOnly ⟨0⟩ with
  | some (.cast id) => (agentTitanOnly.object! id).name == "Inferno Titan"
  | _ => false

/- Guttersnipe: whenever you cast an instant or sorcery, 2 damage to each opponent. -/

#guard guttersnipe.triggeredAbilities == #[.onCastInstantOrSorceryDealDamageToEachOpponent 2]
#guard lightningBolt.isInstantOrSorcery
#guard !grayOgre.isInstantOrSorcery

/-- Guttersnipe in play with Lightning Bolt in hand and {R} in the pool. -/
def guttersnipeBoltSetup : Game :=
  let g := addPermanent afterDraw guttersnipe ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })
  withRedMana (addToHand g lightningBolt ⟨0⟩) ⟨0⟩ 1

#guard guttersnipeBoltSetup.canCast ⟨0⟩
  (handCardNamed guttersnipeBoltSetup ⟨0⟩ "Lightning Bolt")
#guard (guttersnipeBoltSetup.player ⟨1⟩).life == 20

/-- Propose, announce Nissa, and pay. The trigger goes on the stack above the Bolt
(CR 601.2i / 603.3). -/
def paidGuttersnipeBolt : Game :=
  let g := mustApply guttersnipeBoltSetup ⟨0⟩
    (.cast (handCardNamed guttersnipeBoltSetup ⟨0⟩ "Lightning Bolt").id)
  let g := mustApply g ⟨0⟩ (.target (Target.player ⟨1⟩))
  mustApply g ⟨0⟩ .pay

#guard paidGuttersnipeBolt.hasPriority ⟨0⟩
#guard paidGuttersnipeBolt.pending == .none
#guard paidGuttersnipeBolt.stack.size == 2
#guard (paidGuttersnipeBolt.object! paidGuttersnipeBolt.stack.back!.objectId).triggeredAbility ==
  some (.onCastInstantOrSorceryDealDamageToEachOpponent 2)
#guard (paidGuttersnipeBolt.object! paidGuttersnipeBolt.stack[0]!.objectId).name == "Lightning Bolt"
#guard paidGuttersnipeBolt.log.any (fun s => mentions s "casts Lightning Bolt")
#guard paidGuttersnipeBolt.log.any (fun s => mentions s "cast trigger is put on the stack")
#guard (paidGuttersnipeBolt.player ⟨1⟩).life == 20

/-- The trigger resolves first, then the Bolt. -/
def guttersnipeTriggerResolved : Game := passBoth paidGuttersnipeBolt

#guard guttersnipeTriggerResolved.stack.size == 1
#guard (guttersnipeTriggerResolved.object! guttersnipeTriggerResolved.stack.back!.objectId).name ==
  "Lightning Bolt"
#guard (guttersnipeTriggerResolved.player ⟨1⟩).life == 18
#guard guttersnipeTriggerResolved.log.any (fun s => mentions s "Nissa is dealt 2 damage")

def guttersnipeBoltResolved : Game := passBoth guttersnipeTriggerResolved

#guard guttersnipeBoltResolved.stack.isEmpty
#guard (guttersnipeBoltResolved.player ⟨1⟩).life == 15
#guard guttersnipeBoltResolved.log.any (fun s => mentions s "Nissa is dealt 3 damage")

-- Casting a creature does not trigger Guttersnipe.
def paidOgreWithGuttersnipe : Game :=
  let g := addPermanent afterDraw guttersnipe ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })
  let g := withRedMana (addToHand g grayOgre ⟨0⟩) ⟨0⟩ 3
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Gray Ogre").id)
  mustApply g ⟨0⟩ .pay

#guard paidOgreWithGuttersnipe.stack.size == 1
#guard (paidOgreWithGuttersnipe.object! paidOgreWithGuttersnipe.stack.back!.objectId).name ==
  "Gray Ogre"
#guard !paidOgreWithGuttersnipe.log.any (fun s => mentions s "cast trigger")
#guard (paidOgreWithGuttersnipe.player ⟨1⟩).life == 20

-- An opponent's Guttersnipe does not trigger when you cast a spell.
def paidBoltOppGuttersnipe : Game :=
  let g := addPermanent afterDraw guttersnipe ⟨1⟩ ⟨1⟩
  let g := withRedMana (addToHand g lightningBolt ⟨0⟩) ⟨0⟩ 1
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Lightning Bolt").id)
  let g := mustApply g ⟨0⟩ (.target (Target.player ⟨1⟩))
  mustApply g ⟨0⟩ .pay

#guard paidBoltOppGuttersnipe.stack.size == 1
#guard (paidBoltOppGuttersnipe.object! paidBoltOppGuttersnipe.stack.back!.objectId).name ==
  "Lightning Bolt"
#guard !paidBoltOppGuttersnipe.log.any (fun s => mentions s "cast trigger")

-- Two Guttersnipes both trigger; the controller chooses stack order (CR 603.3b).
def paidBoltTwoGuttersnipesPending : Game :=
  let g := addPermanent afterDraw guttersnipe ⟨0⟩ ⟨0⟩
  let g := addPermanent g guttersnipe ⟨0⟩ ⟨0⟩
  let g := withRedMana (addToHand g lightningBolt ⟨0⟩) ⟨0⟩ 1
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Lightning Bolt").id)
  let g := mustApply g ⟨0⟩ (.target (Target.player ⟨1⟩))
  mustApply g ⟨0⟩ .pay

#guard paidBoltTwoGuttersnipesPending.pending == .chooseTriggerToStack ⟨0⟩
#guard paidBoltTwoGuttersnipesPending.stack.size == 1
#guard paidBoltTwoGuttersnipesPending.waitingTriggers.size == 2
#guard paidBoltTwoGuttersnipesPending.log.any (fun s => mentions s "CR 603.3b")

def paidBoltTwoGuttersnipes : Game := applyIdle paidBoltTwoGuttersnipesPending

#guard paidBoltTwoGuttersnipes.stack.size == 3
#guard (paidBoltTwoGuttersnipes.object! paidBoltTwoGuttersnipes.stack.back!.objectId).triggeredAbility ==
  some (.onCastInstantOrSorceryDealDamageToEachOpponent 2)
#guard (paidBoltTwoGuttersnipes.object!
  paidBoltTwoGuttersnipes.stack[1]!.objectId).triggeredAbility ==
  some (.onCastInstantOrSorceryDealDamageToEachOpponent 2)

def twoGuttersnipesResolved : Game :=
  passBoth (passBoth (passBoth paidBoltTwoGuttersnipes))

#guard twoGuttersnipesResolved.stack.isEmpty
#guard (twoGuttersnipesResolved.player ⟨1⟩).life == 13

/-- The trigger still deals damage if Guttersnipe leaves before it resolves
(CR 113.7 / 608.2g). -/
def guttersnipeGoneResolved : Game :=
  let id := (namedPermanent paidGuttersnipeBolt "Guttersnipe").id
  let (g, _) := paidGuttersnipeBolt.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard !(guttersnipeGoneResolved.battlefield.any (fun o => o.name == "Guttersnipe"))
#guard (guttersnipeGoneResolved.player ⟨1⟩).life == 18
#guard guttersnipeGoneResolved.log.any (fun s => mentions s "Nissa is dealt 2 damage")

/-- Lethal Guttersnipe damage ends the game before the spell resolves. -/
def guttersnipeLethal : Game :=
  let g := paidGuttersnipeBolt.modifyPlayer ⟨1⟩ (fun pl => { pl with life := 2 })
  passBoth g

#guard guttersnipeLethal.over
#guard guttersnipeLethal.result == some (.won ⟨0⟩)
#guard (guttersnipeLethal.player ⟨1⟩).life == 0
#guard guttersnipeLethal.log.any (fun s => mentions s "Nissa loses the game")
#guard guttersnipeLethal.log.any (fun s => mentions s "Chandra wins the game")
#guard guttersnipeLethal.stack.size == 1

-- A sorcery Adventure is an instant-or-sorcery spell (CR 715.3b / 601.2i).
def paidSpewWithGuttersnipe : Game :=
  let g := addPermanent smaugSetup guttersnipe ⟨0⟩ ⟨0⟩
  let g := mustApply g ⟨0⟩
    (.castAdventure (handCardNamed g ⟨0⟩ "Smaug, the Great Calamity").id)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Grizzly Bears").id))
  mustApply g ⟨0⟩ .pay

#guard paidSpewWithGuttersnipe.stack.size == 2
#guard (paidSpewWithGuttersnipe.object! paidSpewWithGuttersnipe.stack.back!.objectId).triggeredAbility ==
  some (.onCastInstantOrSorceryDealDamageToEachOpponent 2)
#guard (paidSpewWithGuttersnipe.object! paidSpewWithGuttersnipe.stack[0]!.objectId).name ==
  "Spew Flame"
#guard paidSpewWithGuttersnipe.log.any (fun s => mentions s "casts Spew Flame")
#guard paidSpewWithGuttersnipe.log.any (fun s => mentions s "cast trigger is put on the stack")

def spewWithGuttersnipeResolved : Game :=
  passBoth (passBoth paidSpewWithGuttersnipe)

#guard (spewWithGuttersnipeResolved.player ⟨1⟩).life == 18
#guard !(spewWithGuttersnipeResolved.battlefield.any (fun o => o.name == "Grizzly Bears"))

-- The heuristic casts Bolt when that is the playable spell with Guttersnipe in play.
def agentGuttersnipeBoltOnly : Game :=
  let g := addPermanent afterDraw guttersnipe ⟨0⟩ ⟨0⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withRedMana (addToHand g lightningBolt ⟨0⟩) ⟨0⟩ 1

#guard
  match Agent.choose agentGuttersnipeBoltOnly ⟨0⟩ with
  | some (.cast id) => (agentGuttersnipeBoltOnly.object! id).name == "Lightning Bolt"
  | _ => false

/- Improvised Club: additional cost sacrifice an artifact or creature, then 4 damage. -/

def clubReady : Game :=
  let g := addPermanent afterDraw ragingGoblin ⟨0⟩ ⟨0⟩
  let g := addUntappedLand g mountain
  let g := clearHandPlayedLand g ⟨0⟩
  withRedMana (addToHand g improvisedClub ⟨0⟩) ⟨0⟩ 2

def clubFodder (g : Game) : GameObject :=
  namedPermanent g "Raging Goblin"

def clubNoFodder : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  withRedMana (addToHand g improvisedClub ⟨0⟩) ⟨0⟩ 2

#guard clubReady.canCast ⟨0⟩ (handCardNamed clubReady ⟨0⟩ "Improvised Club")
#guard !(clubNoFodder.canCast ⟨0⟩ (handCardNamed clubNoFodder ⟨0⟩ "Improvised Club"))
#guard (clubReady.player ⟨0⟩).manaPool.canPay improvisedClub.manaCost
#guard clubReady.hasPriority ⟨0⟩

#guard
  match clubNoFodder.apply ⟨0⟩
      (.cast (handCardNamed clubNoFodder ⟨0⟩ "Improvised Club").id) with
  | .error msg => mentions msg "requires sacrificing an artifact or creature"
  | .ok _ => false

#guard
  match Agent.choose clubReady ⟨0⟩ with
  | some (.cast id) => (clubReady.object! id).name == "Improvised Club"
  | _ => false

#guard
  match Agent.choose clubNoFodder ⟨0⟩ with
  | some .pass => true
  | _ => false

def proposedClub : Game :=
  mustApply clubReady ⟨0⟩ (.cast (handCardNamed clubReady ⟨0⟩ "Improvised Club").id)

#guard
  match proposedClub.pending with
  | .chooseTargets ⟨0⟩ => true
  | _ => false
#guard proposedClub.proposedSpell.isSome
#guard proposedClub.stack.size == 1
#guard proposedClub.log.any (fun s => mentions s "begins casting Improvised Club")
#guard proposedClub.log.any (fun s => mentions s "must choose a target (CR 601.2c)")
#guard (namedPermanent proposedClub "Raging Goblin").isOnBattlefield

#guard
  match Agent.choose proposedClub ⟨0⟩ with
  | some (.target (Target.player q)) => q == ⟨1⟩
  | _ => false

def targetedClub : Game :=
  mustApply proposedClub ⟨0⟩ (.target (Target.player ⟨1⟩))

#guard targetedClub.pending == .activateManaAbilities ⟨0⟩
#guard targetedClub.stack.back!.targets == #[Target.player ⟨1⟩]
#guard targetedClub.log.any (fun s => mentions s "chooses Nissa as a target (CR 601.2c)")
#guard targetedClub.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")
#guard
  match targetedClub.proposedSpell with
  | some prop => prop.needsSacrificeOther && prop.kind == .spell
  | none => false

#guard
  match Agent.choose targetedClub ⟨0⟩ with
  | some .pay => true
  | _ => false

def paidClub : Game :=
  mustApply targetedClub ⟨0⟩ .pay

#guard
  match paidClub.pending with
  | .sacrificePermanent p sid =>
    p == ⟨0⟩ && sid == paidClub.stack[0]!.objectId
  | _ => false
#guard paidClub.proposedSpell.isSome
#guard (namedPermanent paidClub "Raging Goblin").isOnBattlefield
#guard paidClub.log.any (fun s => mentions s "must sacrifice an artifact or creature")
#guard !(paidClub.log.any (fun s => mentions s "casts Improvised Club"))
#guard paidClub.stack.size == 1

#guard
  match paidClub.apply ⟨0⟩ (.sacrifice (namedPermanent paidClub "Raging Goblin").id) with
  | .ok _ => true
  | .error _ => false

-- Cannot sacrifice a land, an opponent's creature, or skip the choice.
#guard
  match (paidClub.permanentsOf ⟨0⟩).find? (·.printed.isLand) with
  | none => false
  | some land =>
    match paidClub.apply ⟨0⟩ (.sacrifice land.id) with
    | .error msg => mentions msg "Can't sacrifice"
    | .ok _ => false

#guard
  let g := addPermanent paidClub grizzlyBears ⟨1⟩ ⟨1⟩
  match g.apply ⟨0⟩ (.sacrifice (namedPermanent g "Grizzly Bears").id) with
  | .error msg => mentions msg "Can't sacrifice"
  | .ok _ => false

#guard
  match Agent.choose paidClub ⟨0⟩ with
  | some (.sacrifice id) => id == (clubFodder paidClub).id
  | _ => false

def castClub : Game :=
  mustApply paidClub ⟨0⟩ (.sacrifice (clubFodder paidClub).id)

#guard castClub.pending == .none
#guard castClub.proposedSpell.isNone
#guard castClub.hasPriority ⟨0⟩
#guard castClub.stack.size == 1
#guard (castClub.object! castClub.stack.back!.objectId).name == "Improvised Club"
#guard !(castClub.battlefield.any (fun o => o.name == "Raging Goblin"))
#guard (castClub.player ⟨0⟩).graveyard.any (fun id =>
  (castClub.object! id).name == "Raging Goblin")
#guard castClub.log.any (fun s => mentions s "sacrifices Raging Goblin")
#guard castClub.log.any (fun s => mentions s "casts Improvised Club")
#guard (castClub.player ⟨1⟩).life == 20

def resolvedClub : Game := passBoth castClub

#guard resolvedClub.stack.isEmpty
#guard (resolvedClub.player ⟨1⟩).life == 16
#guard resolvedClub.log.any (fun s => mentions s "Nissa is dealt 4 damage")

-- An artifact is a legal additional-cost sacrifice.
def clubArtifactReady : Game :=
  let g := addPermanent afterDraw wayfarersBauble ⟨0⟩ ⟨0⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withRedMana (addToHand g improvisedClub ⟨0⟩) ⟨0⟩ 2

#guard clubArtifactReady.canCast ⟨0⟩
  (handCardNamed clubArtifactReady ⟨0⟩ "Improvised Club")

def resolvedClubArtifact : Game :=
  let g := mustApply clubArtifactReady ⟨0⟩
    (.cast (handCardNamed clubArtifactReady ⟨0⟩ "Improvised Club").id)
  let g := mustApply g ⟨0⟩ (.target (Target.player ⟨1⟩))
  let g := mustApply g ⟨0⟩ .pay
  let g := mustApply g ⟨0⟩ (.sacrifice (namedPermanent g "Wayfarer's Bauble").id)
  passBoth g

#guard (resolvedClubArtifact.player ⟨1⟩).life == 16
#guard !(resolvedClubArtifact.battlefield.any (fun o => o.name == "Wayfarer's Bauble"))
#guard resolvedClubArtifact.log.any (fun s => mentions s "sacrifices Wayfarer's Bauble")

-- Targeting the creature that is then sacrificed makes the target illegal.
def resolvedClubSacTarget : Game :=
  let g := mustApply clubReady ⟨0⟩
    (.cast (handCardNamed clubReady ⟨0⟩ "Improvised Club").id)
  let g := mustApply g ⟨0⟩ (.target (Target.permanent (clubFodder g).id))
  let g := mustApply g ⟨0⟩ .pay
  let g := mustApply g ⟨0⟩ (.sacrifice (clubFodder g).id)
  passBoth g

#guard resolvedClubSacTarget.log.any (fun s => mentions s "no longer in play")
#guard (resolvedClubSacTarget.player ⟨1⟩).life == 20
#guard !(resolvedClubSacTarget.battlefield.any (fun o => o.name == "Raging Goblin"))

-- Instant speed: legal in the end step.
def clubAtEnd : Game :=
  let g := addPermanent afterDraw ragingGoblin ⟨0⟩ ⟨0⟩
  let g := clearHandPlayedLand g ⟨0⟩
  let g := addToHand g improvisedClub ⟨0⟩
  skipTo g .end 80

#guard clubAtEnd.step == .end
#guard clubAtEnd.canCast ⟨0⟩ (handCardNamed clubAtEnd ⟨0⟩ "Improvised Club")

-- Paying without enough mana reverses the cast; the fodder stays in play.
def reversedClub : Game :=
  let g := addPermanent afterDraw ragingGoblin ⟨0⟩ ⟨0⟩
  let g := addToHand g improvisedClub ⟨0⟩
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Improvised Club").id)
  let g := mustApply g ⟨0⟩ (.target (Target.player ⟨1⟩))
  mustApply g ⟨0⟩ .pay

#guard reversedClub.stack.isEmpty
#guard reversedClub.hasPriority ⟨0⟩
#guard (reversedClub.handObjects ⟨0⟩).any (fun o => o.name == "Improvised Club")
#guard reversedClub.battlefield.any (fun o => o.name == "Raging Goblin")
#guard reversedClub.log.any (fun s => mentions s "the casting is reversed")

-- Guttersnipe waits until the Club is actually cast, after the additional cost.
def clubGuttersnipeReady : Game :=
  let g := addPermanent afterDraw guttersnipe ⟨0⟩ ⟨0⟩
  let g := addPermanent g ragingGoblin ⟨0⟩ ⟨0⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withRedMana (addToHand g improvisedClub ⟨0⟩) ⟨0⟩ 2

def paidClubGuttersnipe : Game :=
  let g := mustApply clubGuttersnipeReady ⟨0⟩
    (.cast (handCardNamed clubGuttersnipeReady ⟨0⟩ "Improvised Club").id)
  let g := mustApply g ⟨0⟩ (.target (Target.player ⟨1⟩))
  mustApply g ⟨0⟩ .pay

#guard paidClubGuttersnipe.stack.size == 1
#guard !(paidClubGuttersnipe.log.any (fun s => mentions s "cast trigger"))
#guard (namedPermanent paidClubGuttersnipe "Raging Goblin").isOnBattlefield

def castClubGuttersnipe : Game :=
  mustApply paidClubGuttersnipe ⟨0⟩
    (.sacrifice (namedPermanent paidClubGuttersnipe "Raging Goblin").id)

#guard castClubGuttersnipe.stack.size == 2
#guard (castClubGuttersnipe.object! castClubGuttersnipe.stack.back!.objectId).triggeredAbility ==
  some (.onCastInstantOrSorceryDealDamageToEachOpponent 2)
#guard (castClubGuttersnipe.object! castClubGuttersnipe.stack[0]!.objectId).name ==
  "Improvised Club"
#guard castClubGuttersnipe.log.any (fun s => mentions s "casts Improvised Club")
#guard castClubGuttersnipe.log.any (fun s => mentions s "cast trigger is put on the stack")

def resolvedClubGuttersnipe : Game :=
  passBoth (passBoth castClubGuttersnipe)

#guard resolvedClubGuttersnipe.stack.isEmpty
#guard (resolvedClubGuttersnipe.player ⟨1⟩).life == 14
#guard resolvedClubGuttersnipe.log.any (fun s => mentions s "Nissa is dealt 2 damage")
#guard resolvedClubGuttersnipe.log.any (fun s => mentions s "Nissa is dealt 4 damage")

-- Sacrificing Fireleaper to Club puts the dies trigger above the spell.
def clubSacrificesFireleaper : Game :=
  let g := addPermanent afterDraw goblinFireleaper ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := clearHandPlayedLand g ⟨0⟩
  let g := withRedMana (addToHand g improvisedClub ⟨0⟩) ⟨0⟩ 2
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Improvised Club").id)
  let g := mustApply g ⟨0⟩ (.target (Target.player ⟨1⟩))
  let g := mustApply g ⟨0⟩ .pay
  mustApply g ⟨0⟩ (.sacrifice (namedPermanent g "Goblin Fireleaper").id)

#guard clubSacrificesFireleaper.pending == .chooseTargets ⟨0⟩
#guard clubSacrificesFireleaper.stack.size == 2
#guard (clubSacrificesFireleaper.object! clubSacrificesFireleaper.stack.back!.objectId).triggeredAbility ==
  some .onDiesDealDamageEqualToPowerToOppCreature
#guard (clubSacrificesFireleaper.object! clubSacrificesFireleaper.stack[0]!.objectId).name ==
  "Improvised Club"
#guard clubSacrificesFireleaper.log.any (fun s => mentions s "sacrifices Goblin Fireleaper")
#guard clubSacrificesFireleaper.log.any (fun s => mentions s "dies trigger is put on the stack")
#guard clubSacrificesFireleaper.log.any (fun s => mentions s "casts Improvised Club")

/- Guardian of the Halls: trample and {5}{G}{G} for three +1/+1 counters. -/

def guardianAbility : ActivatedAbility :=
  guardianOfTheHalls.activatedAbilities[0]!

#guard guardianAbility.effect == .putPlusOnePlusOneOnSource 3
#guard guardianAbility.cost.mana == ManaCost.ofGenericAndColors 5 [.green, .green]
#guard !guardianAbility.effect.requiresTarget
#guard guardianOfTheHalls.keywords.trample

/-- Guardian in play with {5}{G}{G} in the pool; a land drop is already used. -/
def guardianReady : Game :=
  let g := addPermanent afterDraw guardianOfTheHalls ⟨0⟩ ⟨0⟩
  withGreenMana (g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })) ⟨0⟩ 7

def guardianSource (g : Game) : GameObject :=
  namedPermanent g "Guardian of the Halls"

#guard guardianReady.canActivate ⟨0⟩ (guardianSource guardianReady) guardianAbility
#guard !(guardianReady.canActivate ⟨1⟩ (guardianSource guardianReady) guardianAbility)
#guard (guardianReady.player ⟨0⟩).manaPool.canPay guardianAbility.cost.mana
#guard guardianReady.power (guardianSource guardianReady) == 2
#guard guardianReady.toughness (guardianSource guardianReady) == 2
#guard guardianReady.hasTrample (guardianSource guardianReady)
#guard (guardianSource guardianReady).status.plusOnePlusOne == 0

-- Six green cannot pay {5}{G}{G}.
#guard
  let g := addPermanent afterDraw guardianOfTheHalls ⟨0⟩ ⟨0⟩
  let g := withGreenMana
    (g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })) ⟨0⟩ 6
  !(g.player ⟨0⟩).manaPool.canPay guardianAbility.cost.mana

-- The heuristic activates Guardian when {5}{G}{G} is available.
#guard
  match Agent.choose guardianReady ⟨0⟩ with
  | some (.activate id 0) => id == (guardianSource guardianReady).id
  | _ => false

def proposedGuardian : Game :=
  mustApply guardianReady ⟨0⟩ (.activate (guardianSource guardianReady).id 0)

#guard proposedGuardian.pending == .activateManaAbilities ⟨0⟩
#guard proposedGuardian.proposedSpell.isSome
#guard proposedGuardian.stack.size == 1
#guard (proposedGuardian.object! proposedGuardian.stack.back!.objectId).abilityEffect ==
  some (.putPlusOnePlusOneOnSource 3)
#guard (namedPermanent proposedGuardian "Guardian of the Halls").isOnBattlefield
#guard proposedGuardian.log.any (fun s => mentions s "begins activating Guardian of the Halls")

-- Opponent cannot pay Chandra's activation.
#guard
  match proposedGuardian.apply ⟨1⟩ .pay with
  | .error msg => mentions msg "Only Chandra"
  | .ok _ => false

def paidGuardian : Game :=
  mustApply proposedGuardian ⟨0⟩ .pay

#guard paidGuardian.hasPriority ⟨0⟩
#guard paidGuardian.stack.size == 1
#guard paidGuardian.log.any (fun s => mentions s "activates Guardian of the Halls")
#guard (namedPermanent paidGuardian "Guardian of the Halls").status.plusOnePlusOne == 0

def guardianResolved : Game := passBoth paidGuardian

#guard guardianResolved.stack.isEmpty
#guard (namedPermanent guardianResolved "Guardian of the Halls").status.plusOnePlusOne == 3
#guard guardianResolved.power (namedPermanent guardianResolved "Guardian of the Halls") == 5
#guard guardianResolved.toughness (namedPermanent guardianResolved "Guardian of the Halls") == 5
#guard guardianResolved.hasTrample
  (namedPermanent guardianResolved "Guardian of the Halls")
#guard guardianResolved.log.any (fun s =>
  mentions s "Guardian of the Halls gets 3 +1/+1 counters")

/-- A second activation stacks. -/
def guardianResolvedTwice : Game :=
  let g := withGreenMana guardianResolved ⟨0⟩ 7
  let g := mustApply g ⟨0⟩ (.activate (guardianSource g).id 0)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard guardianResolvedTwice.power
  (namedPermanent guardianResolvedTwice "Guardian of the Halls") == 8
#guard guardianResolvedTwice.toughness
  (namedPermanent guardianResolvedTwice "Guardian of the Halls") == 8
#guard (namedPermanent guardianResolvedTwice "Guardian of the Halls").status.plusOnePlusOne == 6

/-- Counters do not wear off in cleanup (CR 122.1 / 514.3). -/
def afterGuardianCleanup : Game :=
  passBoth (skipTo guardianResolved .end 80)

#guard afterGuardianCleanup.power
  (namedPermanent afterGuardianCleanup "Guardian of the Halls") == 5
#guard afterGuardianCleanup.toughness
  (namedPermanent afterGuardianCleanup "Guardian of the Halls") == 5
#guard (namedPermanent afterGuardianCleanup "Guardian of the Halls").status.plusOnePlusOne == 3

/-- If the source leaves before the ability resolves, the counters are not placed. -/
def guardianSourceGone : Game :=
  let id := (namedPermanent paidGuardian "Guardian of the Halls").id
  let (g, _) := paidGuardian.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard guardianSourceGone.log.any (fun s => mentions s "source is no longer in play")
#guard !(guardianSourceGone.battlefield.any (fun o => o.name == "Guardian of the Halls"))

-- Instant-speed: Guardian can activate during the end step.
def guardianAtEndStep : Game := skipTo guardianReady .end 80

#guard guardianAtEndStep.step == .end
#guard guardianAtEndStep.canActivate ⟨0⟩ (guardianSource guardianAtEndStep)
  guardianAbility

/-- Two damage is lethal to the 2/2, but not after three +1/+1 counters. -/
def guardianDiesFromTwoDamage : Game :=
  let o := namedPermanent guardianReady "Guardian of the Halls"
  let g := guardianReady.setObject { o with status := { o.status with damage := 2 } }
  g.receivePriority ⟨0⟩

#guard !(guardianDiesFromTwoDamage.battlefield.any (fun o =>
  o.name == "Guardian of the Halls"))
#guard guardianDiesFromTwoDamage.log.any (fun s =>
  mentions s "Guardian of the Halls dies from lethal damage")

def guardianSurvivesTwoDamage : Game :=
  let o := namedPermanent guardianResolved "Guardian of the Halls"
  let g := guardianResolved.setObject { o with status := { o.status with
    plusOnePlusOne := o.status.plusOnePlusOne, damage := 2 } }
  g.receivePriority ⟨0⟩

#guard guardianSurvivesTwoDamage.battlefield.any (fun o =>
  o.name == "Guardian of the Halls")
#guard (namedPermanent guardianSurvivesTwoDamage "Guardian of the Halls").status.damage == 2
#guard guardianSurvivesTwoDamage.power
  (namedPermanent guardianSurvivesTwoDamage "Guardian of the Halls") == 5

/-- Printed trample assigns leftover combat damage (5/5 vs 2/2 Bears). -/
def afterGuardianTrampleCombat : Game :=
  let g := addPermanent guardianResolved grizzlyBears ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩
    (.declareAttackers #[(namedPermanent g "Guardian of the Halls").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Guardian of the Halls").id)])
  passBoth g

#guard afterGuardianTrampleCombat.log.any (fun s =>
  mentions s "Guardian of the Halls deals 2 combat damage to Grizzly Bears")
#guard afterGuardianTrampleCombat.log.any (fun s =>
  mentions s "Guardian of the Halls tramples for 3 to Nissa")
#guard afterGuardianTrampleCombat.log.any (fun s =>
  mentions s "Grizzly Bears dies from lethal damage")
#guard (afterGuardianTrampleCombat.player ⟨1⟩).life == 17
#guard !(afterGuardianTrampleCombat.battlefield.any (fun o => o.name == "Grizzly Bears"))

/- Elvish Archdruid: other Elves get +1/+1, and `{T}: Add {G}` per Elf. -/

def archAndElves : Game :=
  addPermanent (addPermanent started elvishArchdruid ⟨0⟩ ⟨0⟩) llanowarElves ⟨0⟩ ⟨0⟩

def archAndBears : Game :=
  addPermanent (addPermanent started elvishArchdruid ⟨0⟩ ⟨0⟩) grizzlyBears ⟨0⟩ ⟨0⟩

def archAndOppElves : Game :=
  addPermanent (addPermanent started elvishArchdruid ⟨0⟩ ⟨0⟩) llanowarElves ⟨1⟩ ⟨1⟩

def archAlone : Game := addPermanent started elvishArchdruid ⟨0⟩ ⟨0⟩

#guard archAndElves.power (namedPermanent archAndElves "Llanowar Elves") == 2
#guard archAndElves.toughness (namedPermanent archAndElves "Llanowar Elves") == 2
#guard archAndElves.snapshotPower (namedPermanent archAndElves "Llanowar Elves") == 2
#guard archAndElves.snapshotToughness (namedPermanent archAndElves "Llanowar Elves") == 2
#guard archAndElves.power (namedPermanent archAndElves "Elvish Archdruid") == 2
#guard archAndElves.toughness (namedPermanent archAndElves "Elvish Archdruid") == 2
#guard (namedPermanent archAndElves "Llanowar Elves").status.pumpPower == 0
#guard archAndBears.power (namedPermanent archAndBears "Grizzly Bears") == 2
#guard archAndOppElves.power (namedPermanent archAndOppElves "Llanowar Elves") == 1
#guard archAlone.power (namedPermanent archAlone "Elvish Archdruid") == 2
#guard archAndElves.countSubtype ⟨0⟩ "Elf" == 2
#guard (archAndElves.availableMana ⟨0⟩).green == 3
#guard (archAlone.availableMana ⟨0⟩).green == 1
#guard (archAndOppElves.availableMana ⟨0⟩).green == 1
#guard (archAndBears.availableMana ⟨0⟩).green == 1

/-- Two Archdruids pump each other (CR 604.2). -/
def twoArchdruids : Game :=
  addPermanent (addPermanent started elvishArchdruid ⟨0⟩ ⟨0⟩) elvishArchdruid ⟨0⟩ ⟨0⟩

#guard
  let elves := twoArchdruids.battlefield.filter (fun o => o.name == "Elvish Archdruid")
  elves.size == 2 &&
    elves.all (fun o => twoArchdruids.power o == 3 && twoArchdruids.toughness o == 3)
#guard (twoArchdruids.availableMana ⟨0⟩).green == 4

/-- The +1/+1 is a continuous effect, so it does not wear off in cleanup. -/
def afterArchCleanup : Game := passBoth (skipTo archAndElves .end 80)

#guard afterArchCleanup.power (namedPermanent afterArchCleanup "Llanowar Elves") == 2
#guard (namedPermanent afterArchCleanup "Llanowar Elves").status.pumpPower == 0

/-- A 0/0 Elf survives while Archdruid is in play, and dies when it leaves. -/
def zeroElf : CardDef :=
  creature "Zero Elf" ManaCost.empty #["Elf"] 0 0

def zeroElfWithArch : Game :=
  addPermanent (addPermanent started elvishArchdruid ⟨0⟩ ⟨0⟩) zeroElf ⟨0⟩ ⟨0⟩

#guard zeroElfWithArch.power (namedPermanent zeroElfWithArch "Zero Elf") == 1
#guard zeroElfWithArch.toughness (namedPermanent zeroElfWithArch "Zero Elf") == 1
#guard (zeroElfWithArch.checkSBA).battlefield.any (fun o => o.name == "Zero Elf")

def zeroElfArchLeaves : Game :=
  let id := (namedPermanent zeroElfWithArch "Elvish Archdruid").id
  let (g, _) := zeroElfWithArch.move id (.graveyard ⟨0⟩) none
  g.checkSBA

#guard !(zeroElfArchLeaves.battlefield.any (fun o => o.name == "Zero Elf"))
#guard zeroElfArchLeaves.log.any (fun s => mentions s "dies (toughness 0)")

/-- Combat uses the lord's pumped power. -/
def afterArchdruidCombat : Game :=
  let g := passBoth (skipTo archAndElves .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Llanowar Elves").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[])
  passBoth g

#guard afterArchdruidCombat.log.any (fun s =>
  mentions s "Llanowar Elves deals 2 combat damage to Nissa")
#guard (afterArchdruidCombat.player ⟨1⟩).life == 18

/-- Tapping Archdruid alone adds {G} for itself. -/
def tappedArchAlone : Game :=
  mustApply archAlone ⟨0⟩
    (.tapForMana (namedPermanent archAlone "Elvish Archdruid").id (.colored .green))

#guard (tappedArchAlone.player ⟨0⟩).manaPool.green == 1
#guard (namedPermanent tappedArchAlone "Elvish Archdruid").status.tapped
#guard tappedArchAlone.log.any (fun s => mentions s "taps Elvish Archdruid for green")
#guard !(tappedArchAlone.log.any (fun s => mentions s "green ×"))

/-- Tapping Archdruid with another Elf adds {G}{G}. -/
def tappedArchAndElves : Game :=
  mustApply archAndElves ⟨0⟩
    (.tapForMana (namedPermanent archAndElves "Elvish Archdruid").id (.colored .green))

#guard (tappedArchAndElves.player ⟨0⟩).manaPool.green == 2
#guard (namedPermanent tappedArchAndElves "Elvish Archdruid").status.tapped
#guard !(namedPermanent tappedArchAndElves "Llanowar Elves").status.tapped
#guard tappedArchAndElves.log.any (fun s => mentions s "taps Elvish Archdruid for green ×2")
#guard (tappedArchAndElves.manaSources ⟨0⟩).size == 1
#guard (tappedArchAndElves.availableMana ⟨0⟩).green == 3

/-- Opponent Elves do not count toward the mana ability. -/
def tappedArchAndOppElves : Game :=
  mustApply archAndOppElves ⟨0⟩
    (.tapForMana (namedPermanent archAndOppElves "Elvish Archdruid").id (.colored .green))

#guard (tappedArchAndOppElves.player ⟨0⟩).manaPool.green == 1

-- Summoning sickness still stops the mana ability (CR 302.6).
#guard
  let o := namedPermanent archAlone "Elvish Archdruid"
  let g := archAlone.setObject { o with status := { o.status with summoningSick := true } }
  match g.tapForMana ⟨0⟩ o.id (.colored .green) with
  | .error msg => mentions msg "summoning sickness"
  | .ok _ => false

/-- Available mana from Archdruid plus Elves pays {2}{G}; the agent casts it. -/
def agentArchdruidMana : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  let g := addPermanent g elvishArchdruid ⟨0⟩ ⟨0⟩
  let g := addPermanent g llanowarElves ⟨0⟩ ⟨0⟩
  addToHand g centaurCourser ⟨0⟩

#guard (agentArchdruidMana.availableMana ⟨0⟩).canPay centaurCourser.manaCost
#guard
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  let g := addPermanent g llanowarElves ⟨0⟩ ⟨0⟩
  let g := addPermanent g elvishMystic ⟨0⟩ ⟨0⟩
  let g := addToHand g centaurCourser ⟨0⟩
  !((g.availableMana ⟨0⟩).canPay centaurCourser.manaCost)
#guard
  match Agent.choose agentArchdruidMana ⟨0⟩ with
  | some (.cast id) => (agentArchdruidMana.object! id).name == "Centaur Courser"
  | _ => false

/- Mirkwood Elk: trample and enters-or-attacks return an Elf from the graveyard
(CR 603.6a / 508.2 / 118.2). -/

#guard mirkwoodElk.triggeredAbilities == #[.onEnterOrAttackReturnElfGainLife]
#guard mirkwoodElk.keywords.trample
#guard mirkwoodElk.power == some 6
#guard mirkwoodElk.toughness == some 6

/-- Mirkwood Elk in hand, an Elf in the graveyard, and enough mana to cast it. -/
def elkSetup : Game :=
  let g := addToGraveyard afterDraw llanowarElves ⟨0⟩
  withGreenMana (addToHand g mirkwoodElk ⟨0⟩) ⟨0⟩ 6

#guard elkSetup.canCast ⟨0⟩ (handCardNamed elkSetup ⟨0⟩ "Mirkwood Elk")
#guard elkSetup.asSorcery? ⟨0⟩
#guard mirkwoodElk.hasSorcerySpeed
#guard (namedGraveyardCard elkSetup ⟨0⟩ "Llanowar Elves").hasSubtype "Elf"
#guard (elkSetup.legalTriggerTargets ⟨0⟩ .onEnterOrAttackReturnElfGainLife).contains
  (Target.card (namedGraveyardCard elkSetup ⟨0⟩ "Llanowar Elves").id)

def proposedElk : Game :=
  mustApply elkSetup ⟨0⟩ (.cast (handCardNamed elkSetup ⟨0⟩ "Mirkwood Elk").id)

#guard proposedElk.pending == .activateManaAbilities ⟨0⟩
#guard proposedElk.log.any (fun s => mentions s "begins casting Mirkwood Elk")

def paidElk : Game := mustApply proposedElk ⟨0⟩ .pay

#guard paidElk.stack.size == 1
#guard paidElk.hasPriority ⟨0⟩
#guard paidElk.log.any (fun s => mentions s "casts Mirkwood Elk")

/-- The creature enters; the trigger waits for a graveyard Elf (CR 603.3d). -/
def elkEntered : Game := passBoth paidElk

#guard (namedPermanent elkEntered "Mirkwood Elk").printed.power == some 6
#guard elkEntered.power (namedPermanent elkEntered "Mirkwood Elk") == 6
#guard elkEntered.toughness (namedPermanent elkEntered "Mirkwood Elk") == 6
#guard (namedPermanent elkEntered "Mirkwood Elk").printed.keywords.trample
#guard elkEntered.stack.size == 1
#guard (elkEntered.object! elkEntered.stack.back!.objectId).triggeredAbility ==
  some .onEnterOrAttackReturnElfGainLife
#guard (elkEntered.object! elkEntered.stack.back!.objectId).sourceId ==
  some (namedPermanent elkEntered "Mirkwood Elk").id
#guard elkEntered.stack.back!.targets.isEmpty
#guard elkEntered.pending == .chooseTargets ⟨0⟩
#guard elkEntered.actor == some ⟨0⟩
#guard !elkEntered.hasPriority ⟨0⟩
#guard elkEntered.log.any (fun s => mentions s "enters the battlefield")
#guard elkEntered.log.any (fun s => mentions s "enters trigger is put on the stack")
#guard elkEntered.log.any (fun s => mentions s "must choose a target (CR 603.3d")

-- The trigger cannot target a player, a battlefield creature, or a permanent id
-- of the graveyard card.
#guard
  match elkEntered.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match elkEntered.apply ⟨0⟩
      (.target (Target.permanent (namedPermanent elkEntered "Mirkwood Elk").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match elkEntered.apply ⟨0⟩
      (.target (Target.permanent (namedGraveyardCard elkEntered ⟨0⟩ "Llanowar Elves").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The heuristic returns the Elf from the graveyard.
#guard
  match Agent.choose elkEntered ⟨0⟩ with
  | some (.target (Target.card tid)) =>
    (elkEntered.object! tid).name == "Llanowar Elves"
  | _ => false

def elkTargeted : Game :=
  mustApply elkEntered ⟨0⟩
    (.target (Target.card (namedGraveyardCard elkEntered ⟨0⟩ "Llanowar Elves").id))

#guard elkTargeted.pending == .none
#guard elkTargeted.hasPriority ⟨0⟩
#guard elkTargeted.stack.back!.targets ==
  #[Target.card (namedGraveyardCard elkTargeted ⟨0⟩ "Llanowar Elves").id]
#guard elkTargeted.log.any (fun s =>
  mentions s "chooses Llanowar Elves as a target (CR 601.2c)")

def elkResolved : Game := passBoth elkTargeted

#guard elkResolved.stack.isEmpty
#guard (elkResolved.player ⟨0⟩).life == 21
#guard (elkResolved.handObjects ⟨0⟩).any (fun o => o.name == "Llanowar Elves")
#guard !(elkResolved.objects.any (fun o =>
  o.name == "Llanowar Elves" && o.zone == .graveyard ⟨0⟩))
#guard elkResolved.log.any (fun s => mentions s "Llanowar Elves is returned to Chandra's hand")
#guard elkResolved.log.any (fun s => mentions s "Chandra gains 1 life (21 life)")
#guard elkResolved.battlefield.any (fun o => o.name == "Mirkwood Elk")

-- The trigger still returns the Elf if Mirkwood Elk has left (CR 113.7a).
def elkLeftBeforeTrigger : Game :=
  let id := (namedPermanent elkTargeted "Mirkwood Elk").id
  let (g, _) := elkTargeted.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard (elkLeftBeforeTrigger.player ⟨0⟩).life == 21
#guard (elkLeftBeforeTrigger.handObjects ⟨0⟩).any (fun o => o.name == "Llanowar Elves")
#guard !(elkLeftBeforeTrigger.battlefield.any (fun o => o.name == "Mirkwood Elk"))

-- If the targeted card leaves the graveyard, nothing happens (CR 608.2b).
def elkTargetLeft : Game :=
  let id := (namedGraveyardCard elkTargeted ⟨0⟩ "Llanowar Elves").id
  let (g, _) := elkTargeted.move id .exile none
  passBoth g

#guard (elkTargetLeft.player ⟨0⟩).life == 20
#guard !(elkTargetLeft.handObjects ⟨0⟩).any (fun o => o.name == "Llanowar Elves")
#guard elkTargetLeft.log.any (fun s => mentions s "no longer in the graveyard")
#guard elkTargetLeft.objects.any (fun o => o.name == "Llanowar Elves" && o.zone == .exile)

/-- No Elf in the graveyard: the trigger is removed (CR 603.3d). -/
def elkNoTargetEntered : Game :=
  let g := withGreenMana (addToHand afterDraw mirkwoodElk ⟨0⟩) ⟨0⟩ 6
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Mirkwood Elk").id)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard elkNoTargetEntered.stack.isEmpty
#guard elkNoTargetEntered.pending == .none
#guard elkNoTargetEntered.battlefield.any (fun o => o.name == "Mirkwood Elk")
#guard elkNoTargetEntered.log.any (fun s =>
  mentions s "enters trigger is removed from the stack (no legal target)")
#guard (elkNoTargetEntered.player ⟨0⟩).life == 20

-- A non-Elf in the graveyard is not a legal target.
#guard
  let g := addToGraveyard afterDraw grizzlyBears ⟨0⟩
  let g := withGreenMana (addToHand g mirkwoodElk ⟨0⟩) ⟨0⟩ 6
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Mirkwood Elk").id)
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  g.stack.isEmpty &&
    g.log.any (fun s => mentions s "no legal target") &&
    !(g.legalTriggerTargets ⟨0⟩ .onEnterOrAttackReturnElfGainLife).contains
      (Target.card (namedGraveyardCard (addToGraveyard afterDraw grizzlyBears ⟨0⟩)
        ⟨0⟩ "Grizzly Bears").id)

-- An Elf in an opponent's graveyard is not a legal target.
#guard
  let g := addToGraveyard afterDraw llanowarElves ⟨1⟩
  (g.legalTriggerTargets ⟨0⟩ .onEnterOrAttackReturnElfGainLife).isEmpty

/-- Two Elves: life equals the chosen card's power; the heuristic picks the last. -/
def elkTwoElvesEntered : Game :=
  let g := addToGraveyard afterDraw llanowarElves ⟨0⟩
  let g := addToGraveyard g galadhrimGuide ⟨0⟩
  let g := withGreenMana (addToHand g mirkwoodElk ⟨0⟩) ⟨0⟩ 6
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Mirkwood Elk").id)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard elkTwoElvesEntered.pending == .chooseTargets ⟨0⟩
#guard (elkTwoElvesEntered.legalTriggerTargets ⟨0⟩ .onEnterOrAttackReturnElfGainLife).size == 2
#guard
  match Agent.choose elkTwoElvesEntered ⟨0⟩ with
  | some (.target (Target.card tid)) =>
    (elkTwoElvesEntered.object! tid).name == "Galadhrim Guide"
  | _ => false

def elkGuideResolved : Game :=
  let g := mustApply elkTwoElvesEntered ⟨0⟩
    (.target (Target.card (namedGraveyardCard elkTwoElvesEntered ⟨0⟩ "Galadhrim Guide").id))
  passBoth g

#guard (elkGuideResolved.player ⟨0⟩).life == 23
#guard (elkGuideResolved.handObjects ⟨0⟩).any (fun o => o.name == "Galadhrim Guide")
#guard (elkGuideResolved.objects.any (fun o =>
  o.name == "Llanowar Elves" && o.zone == .graveyard ⟨0⟩))
#guard elkGuideResolved.log.any (fun s => mentions s "Chandra gains 3 life (23 life)")

def elkElvesResolved : Game :=
  let g := mustApply elkTwoElvesEntered ⟨0⟩
    (.target (Target.card (namedGraveyardCard elkTwoElvesEntered ⟨0⟩ "Llanowar Elves").id))
  passBoth g

#guard (elkElvesResolved.player ⟨0⟩).life == 21
#guard (elkElvesResolved.handObjects ⟨0⟩).any (fun o => o.name == "Llanowar Elves")
#guard (elkElvesResolved.objects.any (fun o =>
  o.name == "Galadhrim Guide" && o.zone == .graveyard ⟨0⟩))

/-- Mirkwood Elk already in play so it can attack (no ETB from `addPermanent`). -/
def elkOnBattlefield : Game :=
  addToGraveyard (addPermanent started mirkwoodElk ⟨0⟩ ⟨0⟩) llanowarElves ⟨0⟩

def elkAttackDeclared : Game :=
  let g := passBoth (skipTo elkOnBattlefield .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Mirkwood Elk").id])

#guard elkAttackDeclared.pending == .chooseTargets ⟨0⟩
#guard elkAttackDeclared.stack.size == 1
#guard (elkAttackDeclared.object! elkAttackDeclared.stack.back!.objectId).triggeredAbility ==
  some .onEnterOrAttackReturnElfGainLife
#guard (elkAttackDeclared.object! elkAttackDeclared.stack.back!.objectId).sourceId ==
  some (namedPermanent elkAttackDeclared "Mirkwood Elk").id
#guard elkAttackDeclared.stack.back!.targets.isEmpty
#guard elkAttackDeclared.log.any (fun s => mentions s "attack trigger is put on the stack")
#guard elkAttackDeclared.log.any (fun s => mentions s "must choose a target (CR 603.3d")
#guard !elkAttackDeclared.hasPriority ⟨0⟩
#guard elkAttackDeclared.actor == some ⟨0⟩
#guard (namedPermanent elkAttackDeclared "Mirkwood Elk").status.attacking

#guard
  match Agent.choose elkAttackDeclared ⟨0⟩ with
  | some (.target (Target.card tid)) =>
    (elkAttackDeclared.object! tid).name == "Llanowar Elves"
  | _ => false

def elkAttackResolved : Game :=
  let g := mustApply elkAttackDeclared ⟨0⟩
    (.target (Target.card (namedGraveyardCard elkAttackDeclared ⟨0⟩ "Llanowar Elves").id))
  passBoth g

#guard elkAttackResolved.stack.isEmpty
#guard (elkAttackResolved.player ⟨0⟩).life == 21
#guard (elkAttackResolved.handObjects ⟨0⟩).any (fun o => o.name == "Llanowar Elves")
#guard elkAttackResolved.log.any (fun s => mentions s "Chandra gains 1 life")
#guard (namedPermanent elkAttackResolved "Mirkwood Elk").status.attacking

/-- Attack with no Elf in the graveyard removes the trigger (CR 603.3d). -/
def elkAttackNoTarget : Game :=
  let g := addPermanent started mirkwoodElk ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Mirkwood Elk").id])

#guard elkAttackNoTarget.stack.isEmpty
#guard elkAttackNoTarget.pending == .none
#guard elkAttackNoTarget.hasPriority ⟨0⟩
#guard elkAttackNoTarget.log.any (fun s =>
  mentions s "attack trigger is removed from the stack (no legal target)")
#guard (namedPermanent elkAttackNoTarget "Mirkwood Elk").status.attacking

/-- Printed trample assigns leftover combat damage (6/6 vs 2/2 Bears). -/
def afterElkTrampleCombat : Game :=
  let g := addPermanent (addPermanent started mirkwoodElk ⟨0⟩ ⟨0⟩)
    grizzlyBears ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Mirkwood Elk").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Mirkwood Elk").id)])
  passBoth g

#guard afterElkTrampleCombat.log.any (fun s =>
  mentions s "Mirkwood Elk deals 2 combat damage to Grizzly Bears")
#guard afterElkTrampleCombat.log.any (fun s =>
  mentions s "Mirkwood Elk tramples for 4 to Nissa")
#guard (afterElkTrampleCombat.player ⟨1⟩).life == 16
#guard !(afterElkTrampleCombat.battlefield.any (fun o => o.name == "Grizzly Bears"))

-- The agent casts Mirkwood Elk when that is the playable spell.
def agentElkOnly : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  let g := addToGraveyard g llanowarElves ⟨0⟩
  withGreenMana (addToHand g mirkwoodElk ⟨0⟩) ⟨0⟩ 6

#guard
  match Agent.choose agentElkOnly ⟨0⟩ with
  | some (.cast id) => (agentElkOnly.object! id).name == "Mirkwood Elk"
  | _ => false

/- Celeborn the Wise: attack with Elves to scry 1; whenever you scry, +1/+1
per card looked at. -/

#guard celebornTheWise.triggeredAbilities ==
  #[.onAttackWithElvesScry 1, .onScryPumpSelfForEachLookedAt]
#guard celebornTheWise.subtypes.any (· == "Elf")

/-- Celeborn on the battlefield, ready to attack. -/
def celebornReady : Game :=
  addPermanent started celebornTheWise ⟨0⟩ ⟨0⟩

def celebornAttackDeclared : Game :=
  let g := passBoth (skipTo celebornReady .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Celeborn the Wise").id])

#guard celebornAttackDeclared.stack.size == 1
#guard (celebornAttackDeclared.object! celebornAttackDeclared.stack.back!.objectId).triggeredAbility ==
  some (.onAttackWithElvesScry 1)
#guard (celebornAttackDeclared.object! celebornAttackDeclared.stack.back!.objectId).sourceId ==
  some (namedPermanent celebornAttackDeclared "Celeborn the Wise").id
#guard celebornAttackDeclared.log.any (fun s => mentions s "attack trigger is put on the stack")
#guard celebornAttackDeclared.hasPriority ⟨0⟩
#guard celebornAttackDeclared.power (namedPermanent celebornAttackDeclared "Celeborn the Wise") == 3

/-- Resolving the attack trigger starts scry 1. -/
def celebornScrying : Game := passBoth celebornAttackDeclared

#guard
  match celebornScrying.pending with
  | .scry ⟨0⟩ 1 => true
  | _ => false
#guard celebornScrying.stack.isEmpty
#guard celebornScrying.log.any (fun s => mentions s "scries 1")
#guard !celebornScrying.hasPriority ⟨0⟩

/-- After the scry, the pump trigger uses the number of cards looked at. -/
def celebornScried : Game := keepScry celebornScrying

#guard celebornScried.pending == .none
#guard celebornScried.stack.size == 1
#guard (celebornScried.object! celebornScried.stack.back!.objectId).triggeredAbility ==
  some .onScryPumpSelfForEachLookedAt
#guard (celebornScried.object! celebornScried.stack.back!.objectId).lastKnownPower == some 1
#guard celebornScried.log.any (fun s => mentions s "scry trigger is put on the stack")
#guard celebornScried.hasPriority ⟨0⟩
#guard celebornScried.power (namedPermanent celebornScried "Celeborn the Wise") == 3

def celebornPumped : Game := passBoth celebornScried

#guard celebornPumped.stack.isEmpty
#guard celebornPumped.power (namedPermanent celebornPumped "Celeborn the Wise") == 4
#guard celebornPumped.toughness (namedPermanent celebornPumped "Celeborn the Wise") == 4
#guard (namedPermanent celebornPumped "Celeborn the Wise").status.pumpPower == 1
#guard (namedPermanent celebornPumped "Celeborn the Wise").status.pumpToughness == 1
#guard celebornPumped.log.any (fun s => mentions s "gets +1/+1 until end of turn")

/-- Two Elves attacking still put only one scry trigger on the stack. -/
def celebornTwoElvesDeclared : Game :=
  let g := addPermanent celebornReady llanowarElves ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[
    (namedPermanent g "Celeborn the Wise").id,
    (namedPermanent g "Llanowar Elves").id])

#guard celebornTwoElvesDeclared.stack.size == 1
#guard (celebornTwoElvesDeclared.object! celebornTwoElvesDeclared.stack.back!.objectId).triggeredAbility ==
  some (.onAttackWithElvesScry 1)

/-- An Elf attacking while Celeborn stays back still triggers. -/
def celebornElvesAttackAlone : Game :=
  let g := addPermanent celebornReady llanowarElves ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Llanowar Elves").id])

#guard celebornElvesAttackAlone.stack.size == 1
#guard (celebornElvesAttackAlone.object! celebornElvesAttackAlone.stack.back!.objectId).sourceId ==
  some (namedPermanent celebornElvesAttackAlone "Celeborn the Wise").id

/-- Attacking with only a non-Elf does not trigger. -/
def celebornBearsAttack : Game :=
  let g := addPermanent celebornReady grizzlyBears ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])

#guard celebornBearsAttack.stack.isEmpty
#guard !celebornBearsAttack.log.any (fun s => mentions s "Celeborn the Wise's attack trigger")

/-- Gift of Strands scries 2; Celeborn gets +2/+2. -/
def celebornGiftEntered : Game :=
  addPermanent giftEntered celebornTheWise ⟨0⟩ ⟨0⟩

def celebornGiftScrying : Game := passBoth celebornGiftEntered

#guard
  match celebornGiftScrying.pending with
  | .scry ⟨0⟩ 2 => true
  | _ => false

def celebornGiftScried : Game := keepScry celebornGiftScrying

#guard celebornGiftScried.stack.size == 1
#guard (celebornGiftScried.object! celebornGiftScried.stack.back!.objectId).triggeredAbility ==
  some .onScryPumpSelfForEachLookedAt
#guard (celebornGiftScried.object! celebornGiftScried.stack.back!.objectId).lastKnownPower == some 2

def celebornGiftPumped : Game := passBoth celebornGiftScried

#guard celebornGiftPumped.power (namedPermanent celebornGiftPumped "Celeborn the Wise") == 5
#guard celebornGiftPumped.toughness (namedPermanent celebornGiftPumped "Celeborn the Wise") == 5
#guard celebornGiftPumped.log.any (fun s => mentions s "gets +2/+2 until end of turn")

/-- Scry 2 with one card in the library looks at one card, so +1/+1. -/
def celebornScryOneOfTwo : Game :=
  let g := addPermanent giftEntered celebornTheWise ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl =>
    { pl with library := pl.library.extract (pl.library.size - 1) pl.library.size })
  keepScry (passBoth g)

#guard celebornScryOneOfTwo.stack.size == 1
#guard (celebornScryOneOfTwo.object! celebornScryOneOfTwo.stack.back!.objectId).lastKnownPower ==
  some 1

def celebornScryOneOfTwoPumped : Game := passBoth celebornScryOneOfTwo

#guard celebornScryOneOfTwoPumped.power
  (namedPermanent celebornScryOneOfTwoPumped "Celeborn the Wise") == 4

/-- An empty library still scries; Celeborn gets +0/+0. -/
def celebornEmptyScry : Game :=
  let g := addPermanent giftEntered celebornTheWise ⟨0⟩ ⟨0⟩
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with library := #[] })
  passBoth g

#guard celebornEmptyScry.pending == .none
#guard celebornEmptyScry.stack.size == 1
#guard (celebornEmptyScry.object! celebornEmptyScry.stack.back!.objectId).triggeredAbility ==
  some .onScryPumpSelfForEachLookedAt
#guard (celebornEmptyScry.object! celebornEmptyScry.stack.back!.objectId).lastKnownPower == some 0
#guard celebornEmptyScry.log.any (fun s => mentions s "no cards to look at")

def celebornEmptyPumped : Game := passBoth celebornEmptyScry

#guard celebornEmptyPumped.power (namedPermanent celebornEmptyPumped "Celeborn the Wise") == 3
#guard celebornEmptyPumped.log.any (fun s => mentions s "gets +0/+0 until end of turn")

/-- If Celeborn leaves before the pump resolves, he is not pumped. -/
def celebornPumpSourceGone : Game :=
  let id := (namedPermanent celebornScried "Celeborn the Wise").id
  let (g, _) := celebornScried.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard celebornPumpSourceGone.stack.isEmpty
#guard !(celebornPumpSourceGone.battlefield.any (fun o => o.name == "Celeborn the Wise"))
#guard celebornPumpSourceGone.log.any (fun s => mentions s "source is no longer in play")

/-- If Celeborn leaves before the attack trigger resolves, you still scry, but
he is not on the battlefield to trigger from that scry. -/
def celebornGoneBeforeScry : Game :=
  let id := (namedPermanent celebornAttackDeclared "Celeborn the Wise").id
  let (g, _) := celebornAttackDeclared.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard
  match celebornGoneBeforeScry.pending with
  | .scry ⟨0⟩ 1 => true
  | _ => false
#guard celebornGoneBeforeScry.waitingTriggers.isEmpty

def celebornGoneAfterScry : Game := keepScry celebornGoneBeforeScry

#guard celebornGoneAfterScry.stack.isEmpty
#guard celebornGoneAfterScry.pending == .none

/-- An opponent's scry does not pump your Celeborn. -/
def opponentScriesCeleborn : Game :=
  let g := addPermanent afterDraw celebornTheWise ⟨0⟩ ⟨0⟩
  keepScry (g.beginScry ⟨1⟩ 1)

#guard opponentScriesCeleborn.stack.isEmpty
#guard opponentScriesCeleborn.power (namedPermanent opponentScriesCeleborn "Celeborn the Wise") == 3
#guard (namedPermanent opponentScriesCeleborn "Celeborn the Wise").status.pumpPower == 0

/-- The +1/+1 wears off in cleanup. -/
def afterCelebornCleanup : Game := passBoth (skipTo celebornPumped .end 80)

#guard afterCelebornCleanup.power (namedPermanent afterCelebornCleanup "Celeborn the Wise") == 3
#guard (namedPermanent afterCelebornCleanup "Celeborn the Wise").status.pumpPower == 0
#guard (namedPermanent afterCelebornCleanup "Celeborn the Wise").status.pumpToughness == 0

/- Woodland Weavemaster: vigilance, another-Elf-enters +1/+1, and restricted
any-color mana equal to power. -/

#guard woodlandWeavemaster.keywords.vigilance
#guard woodlandWeavemaster.triggeredAbilities == #[.onAnotherElfYouControlEntersGets1]
#guard woodlandWeavemaster.tapAddAnyColorEqualToPower
#guard woodlandWeavemaster.manaAbilities.contains (.colored .green)
#guard woodlandWeavemaster.manaAbilities.contains (.colored .white)
#guard !woodlandWeavemaster.manaAbilities.contains .colorless

def weavemasterReady : Game :=
  addPermanent afterDraw woodlandWeavemaster ⟨0⟩ ⟨0⟩

#guard (weavemasterReady.effectiveKeywords
  (namedPermanent weavemasterReady "Woodland Weavemaster")).vigilance
#guard weavemasterReady.hasVigilance
  (namedPermanent weavemasterReady "Woodland Weavemaster")
#guard weavemasterReady.power (namedPermanent weavemasterReady "Woodland Weavemaster") == 1
#guard weavemasterReady.manaFromTap
  (namedPermanent weavemasterReady "Woodland Weavemaster") (.colored .green) == 1
#guard (weavemasterReady.availableMana ⟨0⟩).green == 1
#guard (weavemasterReady.availableMana ⟨0⟩).elfGreen == 1
#guard (weavemasterReady.availableMana ⟨0⟩).canPay (ManaCost.ofColor .green) true
#guard !(weavemasterReady.availableMana ⟨0⟩).canPay (ManaCost.ofColor .green)

/-- Casting another Elf you control pumps Weavemaster (CR 603.6a). -/
def weavemasterElfSetup : Game :=
  withGreenMana (addToHand weavemasterReady llanowarElves ⟨0⟩) ⟨0⟩

def proposedWeavemasterElf : Game :=
  mustApply weavemasterElfSetup ⟨0⟩
    (.cast (handCardNamed weavemasterElfSetup ⟨0⟩ "Llanowar Elves").id)

def paidWeavemasterElf : Game := mustApply proposedWeavemasterElf ⟨0⟩ .pay

def weavemasterElfEntered : Game := passBoth paidWeavemasterElf

#guard weavemasterElfEntered.stack.size == 1
#guard (weavemasterElfEntered.object! weavemasterElfEntered.stack.back!.objectId).triggeredAbility ==
  some .onAnotherElfYouControlEntersGets1
#guard (weavemasterElfEntered.object! weavemasterElfEntered.stack.back!.objectId).sourceId ==
  some (namedPermanent weavemasterElfEntered "Woodland Weavemaster").id
#guard weavemasterElfEntered.log.any (fun s => mentions s "Llanowar Elves enters the battlefield")
#guard weavemasterElfEntered.log.any (fun s => mentions s "Elf-enters trigger is put on the stack")
#guard weavemasterElfEntered.power
  (namedPermanent weavemasterElfEntered "Woodland Weavemaster") == 1

def weavemasterElfPumped : Game := passBoth weavemasterElfEntered

#guard weavemasterElfPumped.stack.isEmpty
#guard weavemasterElfPumped.power
  (namedPermanent weavemasterElfPumped "Woodland Weavemaster") == 2
#guard weavemasterElfPumped.toughness
  (namedPermanent weavemasterElfPumped "Woodland Weavemaster") == 3
#guard weavemasterElfPumped.log.any (fun s =>
  mentions s "Woodland Weavemaster gets +1/+1 until end of turn")
#guard weavemasterElfPumped.manaFromTap
  (namedPermanent weavemasterElfPumped "Woodland Weavemaster") (.colored .green) == 2

/-- Weavemaster entering alone does not pump itself. -/
def weavemasterEntersAlone : Game :=
  let g := withGreenMana (addToHand afterDraw woodlandWeavemaster ⟨0⟩) ⟨0⟩ 2
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Woodland Weavemaster").id)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard weavemasterEntersAlone.battlefield.any (fun o => o.name == "Woodland Weavemaster")
#guard weavemasterEntersAlone.stack.isEmpty
#guard weavemasterEntersAlone.power
  (namedPermanent weavemasterEntersAlone "Woodland Weavemaster") == 1
#guard !weavemasterEntersAlone.log.any (fun s => mentions s "Elf-enters trigger")

/-- A non-Elf you control does not trigger the pump. -/
def weavemasterBearsEntered : Game :=
  let g := withGreenMana (addToHand weavemasterReady grizzlyBears ⟨0⟩) ⟨0⟩
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Grizzly Bears").id)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard weavemasterBearsEntered.stack.isEmpty
#guard weavemasterBearsEntered.power
  (namedPermanent weavemasterBearsEntered "Woodland Weavemaster") == 1

/-- An opponent's Elf does not trigger the pump. -/
def weavemasterOppElf : Game :=
  let g := addPermanent weavemasterReady llanowarElves ⟨1⟩ ⟨1⟩
  g.putAnotherElfYouControlEntersTriggers (namedPermanent g "Llanowar Elves")

#guard weavemasterOppElf.stack.isEmpty

/-- Two Weavemasters: the first triggers when the second enters. -/
def twoWeavemastersEntered : Game :=
  let g := addPermanent afterDraw woodlandWeavemaster ⟨0⟩ ⟨0⟩
  let g := withGreenMana (addToHand g woodlandWeavemaster ⟨0⟩) ⟨0⟩ 2
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Woodland Weavemaster").id)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard twoWeavemastersEntered.stack.size == 1
#guard (twoWeavemastersEntered.object! twoWeavemastersEntered.stack.back!.objectId).triggeredAbility ==
  some .onAnotherElfYouControlEntersGets1

def twoWeavemastersPumped : Game := passBoth twoWeavemastersEntered

#guard
  let weavers := twoWeavemastersPumped.battlefield.filter
    (fun o => o.name == "Woodland Weavemaster")
  weavers.size == 2 &&
    (weavers.filter (fun o => twoWeavemastersPumped.power o == 2)).size == 1 &&
    (weavers.filter (fun o => twoWeavemastersPumped.power o == 1)).size == 1

/-- If Weavemaster leaves before the trigger resolves, it is not pumped. -/
def weavemasterPumpSourceGone : Game :=
  let id := (namedPermanent weavemasterElfEntered "Woodland Weavemaster").id
  let (g, _) := weavemasterElfEntered.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard weavemasterPumpSourceGone.stack.isEmpty
#guard !(weavemasterPumpSourceGone.battlefield.any (fun o => o.name == "Woodland Weavemaster"))
#guard weavemasterPumpSourceGone.log.any (fun s => mentions s "source is no longer in play")

/-- The +1/+1 wears off in cleanup. -/
def afterWeavemasterCleanup : Game := passBoth (skipTo weavemasterElfPumped .end 80)

#guard afterWeavemasterCleanup.power
  (namedPermanent afterWeavemasterCleanup "Woodland Weavemaster") == 1
#guard (namedPermanent afterWeavemasterCleanup "Woodland Weavemaster").status.pumpPower == 0

/-- Tapping adds power of the chosen color as Elf-restricted mana. -/
def tappedWeavemasterGreen : Game :=
  mustApply weavemasterReady ⟨0⟩
    (.tapForMana (namedPermanent weavemasterReady "Woodland Weavemaster").id
      (.colored .green))

#guard (namedPermanent tappedWeavemasterGreen "Woodland Weavemaster").status.tapped
#guard (tappedWeavemasterGreen.player ⟨0⟩).manaPool.green == 1
#guard (tappedWeavemasterGreen.player ⟨0⟩).manaPool.elfGreen == 1
#guard (tappedWeavemasterGreen.player ⟨0⟩).manaPool.canPay (ManaCost.ofColor .green) true
#guard !(tappedWeavemasterGreen.player ⟨0⟩).manaPool.canPay (ManaCost.ofColor .green)
#guard !(tappedWeavemasterGreen.player ⟨0⟩).manaPool.canPay (ManaCost.ofColor .red) true
#guard tappedWeavemasterGreen.log.any (fun s =>
  mentions s "taps Woodland Weavemaster for green (Elf spells and abilities)")

def tappedWeavemasterWhite : Game :=
  mustApply weavemasterReady ⟨0⟩
    (.tapForMana (namedPermanent weavemasterReady "Woodland Weavemaster").id
      (.colored .white))

#guard (tappedWeavemasterWhite.player ⟨0⟩).manaPool.white == 1
#guard (tappedWeavemasterWhite.player ⟨0⟩).manaPool.elfWhite == 1

#guard
  match weavemasterReady.tapForMana ⟨0⟩
      (namedPermanent weavemasterReady "Woodland Weavemaster").id .colorless with
  | .error msg => mentions msg "cannot produce"
  | .ok _ => false

/-- Pumped power produces that much mana. -/
def tappedWeavemasterPumped : Game :=
  let g := weavemasterElfPumped.emptyManaPools
  mustApply g ⟨0⟩
    (.tapForMana (namedPermanent g "Woodland Weavemaster").id
      (.colored .green))

#guard (tappedWeavemasterPumped.player ⟨0⟩).manaPool.green == 2
#guard (tappedWeavemasterPumped.player ⟨0⟩).manaPool.elfGreen == 2
#guard tappedWeavemasterPumped.log.any (fun s =>
  mentions s "taps Woodland Weavemaster for green ×2 (Elf spells and abilities)")

/-- Restricted mana can pay for an Elf spell. -/
def weavemasterPaysElf : Game :=
  let g := addToHand tappedWeavemasterGreen llanowarElves ⟨0⟩
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Llanowar Elves").id)
  mustApply g ⟨0⟩ .pay

#guard weavemasterPaysElf.log.any (fun s => mentions s "casts Llanowar Elves")
#guard (weavemasterPaysElf.player ⟨0⟩).manaPool.isEmpty
#guard weavemasterPaysElf.stack.size == 1

/-- Restricted mana cannot pay for a non-Elf spell (CR 106.10). -/
def weavemasterPaysGrowth : Game :=
  let g := addToHand tappedWeavemasterGreen giantGrowth ⟨0⟩
  let g := proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Giant Growth").id
    (Target.permanent (namedPermanent g "Woodland Weavemaster").id)
  mustApply g ⟨0⟩ .pay

#guard weavemasterPaysGrowth.log.any (fun s => mentions s "cannot pay")
#guard weavemasterPaysGrowth.log.any (fun s => mentions s "casting is reversed")
#guard weavemasterPaysGrowth.stack.isEmpty
#guard (weavemasterPaysGrowth.handObjects ⟨0⟩).any (fun o => o.name == "Giant Growth")
#guard (namedPermanent weavemasterPaysGrowth "Woodland Weavemaster").status.tapped
#guard (weavemasterPaysGrowth.player ⟨0⟩).manaPool.elfGreen == 1

/-- Summoning sickness still stops the mana ability (CR 302.6). -/
def weavemasterSick : Game :=
  let o := namedPermanent weavemasterReady "Woodland Weavemaster"
  weavemasterReady.setObject { o with status := { o.status with summoningSick := true } }

#guard
  match weavemasterSick.tapForMana ⟨0⟩
      (namedPermanent weavemasterSick "Woodland Weavemaster").id (.colored .green) with
  | .error msg => mentions msg "summoning sickness"
  | .ok _ => false

/-- Attacking with vigilance does not tap the creature (CR 702.20). -/
def weavemasterVsGoblin : Game :=
  addPermanent (addPermanent started woodlandWeavemaster ⟨0⟩ ⟨0⟩) ragingGoblin ⟨1⟩ ⟨1⟩

def weavemasterAttackDeclared : Game :=
  let g := passBoth (skipTo weavemasterVsGoblin .beginningOfCombat 80)
  mustApply g ⟨0⟩
    (.declareAttackers #[(namedPermanent g "Woodland Weavemaster").id])

#guard (namedPermanent weavemasterAttackDeclared "Woodland Weavemaster").status.attacking
#guard !(namedPermanent weavemasterAttackDeclared "Woodland Weavemaster").status.tapped
#guard weavemasterAttackDeclared.log.any (fun s =>
  mentions s "attacks with Woodland Weavemaster")

/-- After attacking, Weavemaster can still block on the opponent's turn. -/
def nissaAttacksAfterVigilance : Game :=
  let g := passBoth (skipTo weavemasterAttackDeclared .beginningOfCombat 80)
  mustApply g ⟨1⟩ (.declareAttackers #[(namedPermanent g "Raging Goblin").id])

#guard !(namedPermanent nissaAttacksAfterVigilance "Woodland Weavemaster").status.tapped
#guard nissaAttacksAfterVigilance.canBlock
  (namedPermanent nissaAttacksAfterVigilance "Woodland Weavemaster")
  (namedPermanent nissaAttacksAfterVigilance "Raging Goblin")

def weavemasterBlocksAfterAttack : Game :=
  let g := passBoth nissaAttacksAfterVigilance
  mustApply g ⟨0⟩ (.declareBlockers #[(
    (namedPermanent g "Woodland Weavemaster").id,
    (namedPermanent g "Raging Goblin").id)])

#guard (namedPermanent weavemasterBlocksAfterAttack "Woodland Weavemaster").status.blocking.size == 1
#guard weavemasterBlocksAfterAttack.log.any (fun s =>
  mentions s "Woodland Weavemaster blocks Raging Goblin")

/-- The agent casts an Elf using Weavemaster's restricted mana. -/
def agentWeavemasterElf : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  let g := addPermanent g woodlandWeavemaster ⟨0⟩ ⟨0⟩
  addToHand g llanowarElves ⟨0⟩

#guard
  match Agent.choose agentWeavemasterElf ⟨0⟩ with
  | some (.cast id) => (agentWeavemasterElf.object! id).name == "Llanowar Elves"
  | _ => false

def agentWeavemasterPaying : Game :=
  mustApply agentWeavemasterElf ⟨0⟩
    (.cast (handCardNamed agentWeavemasterElf ⟨0⟩ "Llanowar Elves").id)

#guard
  match Agent.choose agentWeavemasterPaying ⟨0⟩ with
  | some (.tapForMana id (.colored .green)) =>
    (agentWeavemasterPaying.object! id).name == "Woodland Weavemaster"
  | _ => false

/-- The agent will not try to cast a non-Elf with only restricted mana. -/
def agentWeavemasterGrowth : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  let g := addPermanent g woodlandWeavemaster ⟨0⟩ ⟨0⟩
  addToHand g giantGrowth ⟨0⟩

#guard
  match Agent.choose agentWeavemasterGrowth ⟨0⟩ with
  | some (.cast id) => (agentWeavemasterGrowth.object! id).name != "Giant Growth"
  | _ => true

/- Mirkwood Pathmaker: power and toughness equal lands you control in all
zones (CR 208.2a / 604.3). -/

#guard mirkwoodPathmaker.staticAbilities == #[.powerToughnessEqualLandsYouControl]
#guard mirkwoodPathmaker.power.isNone
#guard mirkwoodPathmaker.toughness.isNone
#guard mentions mirkwoodPathmaker.summary "*/*"

#guard pathmakerWithLands.power (namedPermanent pathmakerWithLands "Mirkwood Pathmaker") == 2
#guard pathmakerWithLands.toughness
  (namedPermanent pathmakerWithLands "Mirkwood Pathmaker") == 2
#guard pathmakerWithLands.basePower
  (namedPermanent pathmakerWithLands "Mirkwood Pathmaker") == 2
#guard pathmakerWithLands.snapshotPower
  (namedPermanent pathmakerWithLands "Mirkwood Pathmaker") == 2
#guard pathmakerWithLands.snapshotToughness
  (namedPermanent pathmakerWithLands "Mirkwood Pathmaker") == 2
#guard (namedPermanent pathmakerWithLands "Mirkwood Pathmaker").power == 0
#guard pathmakerWithLands.landsYouControl ⟨0⟩ == 2

/-- Opponent lands do not count. -/
def pathmakerOppLands : Game :=
  addPermanent (addForests pathmakerWithLands ⟨1⟩ 5) grayOgre ⟨1⟩ ⟨1⟩

#guard pathmakerOppLands.power (namedPermanent pathmakerOppLands "Mirkwood Pathmaker") == 2
#guard pathmakerOppLands.landsYouControl ⟨1⟩ == 5

/-- A stolen Pathmaker uses its controller's lands (CR 109.5). -/
def stolenPathmaker : Game :=
  let g := addForests afterDraw ⟨0⟩ 3
  let g := addForests g ⟨1⟩ 1
  addPermanent g mirkwoodPathmaker ⟨0⟩ ⟨1⟩

#guard stolenPathmaker.power (namedPermanent stolenPathmaker "Mirkwood Pathmaker") == 1
#guard (namedPermanent stolenPathmaker "Mirkwood Pathmaker").owner == ⟨0⟩
#guard (namedPermanent stolenPathmaker "Mirkwood Pathmaker").controller == some ⟨1⟩

/-- The CDA functions in hand, graveyard, and on the stack (CR 604.3). -/
def pathmakerInHand : Game :=
  addToHand (addForests afterDraw ⟨0⟩ 2) mirkwoodPathmaker ⟨0⟩

#guard pathmakerInHand.power (handCardNamed pathmakerInHand ⟨0⟩ "Mirkwood Pathmaker") == 2
#guard pathmakerInHand.toughness (handCardNamed pathmakerInHand ⟨0⟩ "Mirkwood Pathmaker") == 2
#guard (handCardNamed pathmakerInHand ⟨0⟩ "Mirkwood Pathmaker").controller.isNone
#guard (handCardNamed pathmakerInHand ⟨0⟩ "Mirkwood Pathmaker").you == ⟨0⟩

def pathmakerInGraveyard : Game :=
  addToGraveyard (addForests afterDraw ⟨0⟩ 3) mirkwoodPathmaker ⟨0⟩

#guard pathmakerInGraveyard.power
  (namedGraveyardCard pathmakerInGraveyard ⟨0⟩ "Mirkwood Pathmaker") == 3
#guard pathmakerInGraveyard.toughness
  (namedGraveyardCard pathmakerInGraveyard ⟨0⟩ "Mirkwood Pathmaker") == 3

/-- Mirkwood Pathmaker in hand with two Forests in play and enough mana. -/
def pathmakerSetup : Game :=
  withGreenMana (addToHand (addForests afterDraw ⟨0⟩ 2) mirkwoodPathmaker ⟨0⟩) ⟨0⟩ 3

#guard pathmakerSetup.canCast ⟨0⟩ (handCardNamed pathmakerSetup ⟨0⟩ "Mirkwood Pathmaker")
#guard pathmakerSetup.asSorcery? ⟨0⟩
#guard mirkwoodPathmaker.hasSorcerySpeed
#guard pathmakerSetup.power (handCardNamed pathmakerSetup ⟨0⟩ "Mirkwood Pathmaker") == 2

def proposedPathmaker : Game :=
  mustApply pathmakerSetup ⟨0⟩ (.cast (handCardNamed pathmakerSetup ⟨0⟩ "Mirkwood Pathmaker").id)

#guard proposedPathmaker.pending == .activateManaAbilities ⟨0⟩
#guard proposedPathmaker.log.any (fun s => mentions s "begins casting Mirkwood Pathmaker")

def paidPathmaker : Game := mustApply proposedPathmaker ⟨0⟩ .pay

#guard paidPathmaker.stack.size == 1
#guard paidPathmaker.hasPriority ⟨0⟩
#guard paidPathmaker.power (paidPathmaker.object! paidPathmaker.stack.back!.objectId) == 2
#guard (paidPathmaker.object! paidPathmaker.stack.back!.objectId).controller == some ⟨0⟩
#guard paidPathmaker.log.any (fun s => mentions s "casts Mirkwood Pathmaker")

def pathmakerEntered : Game := passBoth paidPathmaker

#guard pathmakerEntered.stack.isEmpty
#guard pathmakerEntered.power (namedPermanent pathmakerEntered "Mirkwood Pathmaker") == 2
#guard pathmakerEntered.toughness (namedPermanent pathmakerEntered "Mirkwood Pathmaker") == 2
#guard (namedPermanent pathmakerEntered "Mirkwood Pathmaker").status.summoningSick
#guard !(pathmakerEntered.canAttack (namedPermanent pathmakerEntered "Mirkwood Pathmaker"))
#guard pathmakerEntered.log.any (fun s => mentions s "enters the battlefield")

/-- 0/0 Pathmaker dies (CR 704.5f). -/
def pathmakerZeroLands : Game :=
  (addPermanent afterDraw mirkwoodPathmaker ⟨0⟩ ⟨0⟩).checkSBA

#guard !(pathmakerZeroLands.battlefield.any (fun o => o.name == "Mirkwood Pathmaker"))
#guard pathmakerZeroLands.log.any (fun s => mentions s "dies (toughness 0)")

/-- Casting with no lands also dies on resolution. -/
def pathmakerEntersZero : Game :=
  let g := withGreenMana (addToHand afterDraw mirkwoodPathmaker ⟨0⟩) ⟨0⟩ 3
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Mirkwood Pathmaker").id)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

#guard !(pathmakerEntersZero.battlefield.any (fun o => o.name == "Mirkwood Pathmaker"))
#guard pathmakerEntersZero.log.any (fun s => mentions s "dies (toughness 0)")

/-- Playing a land updates P/T immediately (continuous effect). -/
def pathmakerGrowsWithLand : Game :=
  let g := addToHand pathmakerWithLands forest ⟨0⟩
  mustApply g ⟨0⟩ (.playLand (handCardNamed g ⟨0⟩ "Forest").id)

#guard pathmakerGrowsWithLand.power
  (namedPermanent pathmakerGrowsWithLand "Mirkwood Pathmaker") == 3
#guard pathmakerGrowsWithLand.toughness
  (namedPermanent pathmakerGrowsWithLand "Mirkwood Pathmaker") == 3
#guard pathmakerGrowsWithLand.landsYouControl ⟨0⟩ == 3

/-- Pumps, counters, lords, and Auras apply on top of the land-count base. -/
def pathmakerPumped : Game :=
  pathmakerWithLands.applyEffect ⟨0⟩ (.pump 2 2)
    #[Target.permanent (namedPermanent pathmakerWithLands "Mirkwood Pathmaker").id]

#guard pathmakerPumped.power (namedPermanent pathmakerPumped "Mirkwood Pathmaker") == 4
#guard pathmakerPumped.basePower (namedPermanent pathmakerPumped "Mirkwood Pathmaker") == 2
#guard pathmakerPumped.toughness (namedPermanent pathmakerPumped "Mirkwood Pathmaker") == 4

def pathmakerWithCounter : Game :=
  let o := namedPermanent pathmakerWithLands "Mirkwood Pathmaker"
  pathmakerWithLands.setObject { o with
    status := { o.status with plusOnePlusOne := 1 } }

#guard pathmakerWithCounter.power
  (namedPermanent pathmakerWithCounter "Mirkwood Pathmaker") == 3
#guard pathmakerWithCounter.basePower
  (namedPermanent pathmakerWithCounter "Mirkwood Pathmaker") == 2

def pathmakerWithArchdruid : Game :=
  addPermanent pathmakerWithLands elvishArchdruid ⟨0⟩ ⟨0⟩

#guard pathmakerWithArchdruid.power
  (namedPermanent pathmakerWithArchdruid "Mirkwood Pathmaker") == 3
#guard pathmakerWithArchdruid.toughness
  (namedPermanent pathmakerWithArchdruid "Mirkwood Pathmaker") == 3
#guard pathmakerWithArchdruid.basePower
  (namedPermanent pathmakerWithArchdruid "Mirkwood Pathmaker") == 2

def pathmakerWithGift : Game :=
  let host := namedPermanent pathmakerWithLands "Mirkwood Pathmaker"
  addAttachedAura pathmakerWithLands giftOfStrands host ⟨0⟩ ⟨0⟩

#guard pathmakerWithGift.power (namedPermanent pathmakerWithGift "Mirkwood Pathmaker") == 5
#guard pathmakerWithGift.toughness
  (namedPermanent pathmakerWithGift "Mirkwood Pathmaker") == 5
#guard pathmakerWithGift.basePower (namedPermanent pathmakerWithGift "Mirkwood Pathmaker") == 2

/-- Combat uses the land-count power. -/
def afterPathmakerCombat : Game :=
  let g := passBoth (skipTo pathmakerWithLands .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩
    (.declareAttackers #[(namedPermanent g "Mirkwood Pathmaker").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[])
  passBoth g

#guard afterPathmakerCombat.log.any (fun s =>
  mentions s "Mirkwood Pathmaker deals 2 combat damage to Nissa")
#guard (afterPathmakerCombat.player ⟨1⟩).life == 18

/-- Returning Pathmaker from the graveyard gains life equal to its CDA power. -/
def elkReturnsPathmakerEntered : Game :=
  let g := addToGraveyard (addForests afterDraw ⟨0⟩ 2) mirkwoodPathmaker ⟨0⟩
  let g := withGreenMana (addToHand g mirkwoodElk ⟨0⟩) ⟨0⟩ 6
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Mirkwood Elk").id)
  let g := mustApply g ⟨0⟩ .pay
  passBoth g

def elkReturnsPathmaker : Game :=
  let g := mustApply elkReturnsPathmakerEntered ⟨0⟩
    (.target (Target.card (namedGraveyardCard elkReturnsPathmakerEntered ⟨0⟩
      "Mirkwood Pathmaker").id))
  passBoth g

#guard (elkReturnsPathmaker.player ⟨0⟩).life == 22
#guard (elkReturnsPathmaker.handObjects ⟨0⟩).any (fun o => o.name == "Mirkwood Pathmaker")
#guard elkReturnsPathmaker.power
  (handCardNamed elkReturnsPathmaker ⟨0⟩ "Mirkwood Pathmaker") == 2
#guard elkReturnsPathmaker.log.any (fun s => mentions s "Chandra gains 2 life (22 life)")

/-- The heuristic casts Pathmaker when it is the playable creature. -/
def agentPathmaker : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  let g := addForests g ⟨0⟩ 2
  withGreenMana (addToHand g mirkwoodPathmaker ⟨0⟩) ⟨0⟩ 3

#guard
  match Agent.choose agentPathmaker ⟨0⟩ with
  | some (.cast id) => (agentPathmaker.object! id).name == "Mirkwood Pathmaker"
  | _ => false

/- Fire of Orthanc (CR 701.8 / 509.1b / 611.2a). -/

/-- Fire of Orthanc in hand, an opposing Forest, enough mana. -/
def fireOfOrthancSetup : Game :=
  let g := addPermanent afterDraw forest ⟨1⟩ ⟨1⟩
  withRedMana (addToHand g fireOfOrthanc ⟨0⟩) ⟨0⟩ 4

#guard fireOfOrthanc.isSorcery
#guard fireOfOrthanc.requiresTarget
#guard fireOfOrthanc.spellEffect == some .destroyArtifactOrLandNonflyersCantBlock
#guard fireOfOrthancSetup.canCast ⟨0⟩ (handCardNamed fireOfOrthancSetup ⟨0⟩ "Fire of Orthanc")
#guard fireOfOrthancSetup.asSorcery? ⟨0⟩
#guard
  (fireOfOrthancSetup.legalTargets ⟨0⟩ .destroyArtifactOrLandNonflyersCantBlock).contains
    (Target.permanent (namedPermanent fireOfOrthancSetup "Forest").id)

-- Cannot cast with no artifact or land.
#guard
  let g := withRedMana (addToHand afterDraw fireOfOrthanc ⟨0⟩) ⟨0⟩ 4
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Fire of Orthanc")
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := withRedMana (addToHand g fireOfOrthanc ⟨0⟩) ⟨0⟩ 4
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Fire of Orthanc")
#guard
  let g := withRedMana (addToHand afterDraw fireOfOrthanc ⟨0⟩) ⟨0⟩ 4
  match g.apply ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Fire of Orthanc").id) with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

-- An opposing artifact is a legal target; a non-artifact creature is not.
#guard
  let g := addPermanent afterDraw wayfarersBauble ⟨1⟩ ⟨1⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := withRedMana (addToHand g fireOfOrthanc ⟨0⟩) ⟨0⟩ 4
  (g.legalTargets ⟨0⟩ .destroyArtifactOrLandNonflyersCantBlock).contains
    (Target.permanent (namedPermanent g "Wayfarer's Bauble").id) &&
    !(g.legalTargets ⟨0⟩ .destroyArtifactOrLandNonflyersCantBlock).contains
      (Target.permanent (namedPermanent g "Grizzly Bears").id)

-- Own lands are legal; hexproof on an opponent's land is not (CR 702.11b).
#guard
  let g := addPermanent afterDraw mountain ⟨0⟩ ⟨0⟩
  let g := withRedMana (addToHand g fireOfOrthanc ⟨0⟩) ⟨0⟩ 4
  g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Fire of Orthanc") &&
    (g.legalTargets ⟨0⟩ .destroyArtifactOrLandNonflyersCantBlock).contains
      (Target.permanent (namedPermanent g "Mountain").id)
#guard
  let g := addPermanent afterDraw forest ⟨1⟩ ⟨1⟩
  let forest := namedPermanent g "Forest"
  let g := g.setObject { forest with
    status := { forest.status with untilEotKeywords := Keyword.hexproof } }
  let g := withRedMana (addToHand g fireOfOrthanc ⟨0⟩) ⟨0⟩ 4
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Fire of Orthanc")

def proposedFireOfOrthanc : Game :=
  mustApply fireOfOrthancSetup ⟨0⟩
    (.cast (handCardNamed fireOfOrthancSetup ⟨0⟩ "Fire of Orthanc").id)

#guard proposedFireOfOrthanc.pending == .chooseTargets ⟨0⟩
#guard proposedFireOfOrthanc.log.any (fun s => mentions s "begins casting Fire of Orthanc")
#guard proposedFireOfOrthanc.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- Cannot target a player or a creature that is not an artifact.
#guard
  match proposedFireOfOrthanc.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

def targetedFireOfOrthanc : Game :=
  mustApply proposedFireOfOrthanc ⟨0⟩
    (.target (Target.permanent (namedPermanent proposedFireOfOrthanc "Forest").id))

#guard targetedFireOfOrthanc.pending == .activateManaAbilities ⟨0⟩
#guard targetedFireOfOrthanc.stack.back!.targets ==
  #[Target.permanent (namedPermanent targetedFireOfOrthanc "Forest").id]

#guard
  match Agent.choose proposedFireOfOrthanc ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (proposedFireOfOrthanc.object! tid).name == "Forest"
  | _ => false

-- Prefer an opposing land over your own (CR 601.2c heuristic).
#guard
  let g := addPermanent fireOfOrthancSetup mountain ⟨0⟩ ⟨0⟩
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Fire of Orthanc").id)
  match Agent.choose g ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (g.object! tid).name == "Forest"
  | _ => false

def paidFireOfOrthanc : Game := mustApply targetedFireOfOrthanc ⟨0⟩ .pay

#guard paidFireOfOrthanc.hasPriority ⟨0⟩
#guard paidFireOfOrthanc.stack.size == 1
#guard paidFireOfOrthanc.log.any (fun s => mentions s "casts Fire of Orthanc")

def resolvedFireOfOrthanc : Game := passBoth paidFireOfOrthanc

#guard resolvedFireOfOrthanc.stack.isEmpty
#guard !(resolvedFireOfOrthanc.battlefield.any (fun o => o.name == "Forest"))
#guard resolvedFireOfOrthanc.objects.any (fun o =>
  o.name == "Forest" && o.zone == .graveyard ⟨1⟩)
#guard resolvedFireOfOrthanc.log.any (fun s => mentions s "Forest is destroyed")
#guard resolvedFireOfOrthanc.log.any (fun s =>
  mentions s "Creatures without flying can't block this turn")
#guard resolvedFireOfOrthanc.creaturesWithoutFlyingCantBlock
#guard (resolvedFireOfOrthanc.player ⟨0⟩).graveyard.any (fun id =>
  (resolvedFireOfOrthanc.object! id).name == "Fire of Orthanc")

-- Destroying an artifact also sets the can't-block effect.
#guard
  let g := addPermanent afterDraw wayfarersBauble ⟨1⟩ ⟨1⟩
  let g := g.applyEffect ⟨0⟩ .destroyArtifactOrLandNonflyersCantBlock
    #[Target.permanent (namedPermanent g "Wayfarer's Bauble").id]
  !(g.battlefield.any (fun o => o.name == "Wayfarer's Bauble")) &&
    g.creaturesWithoutFlyingCantBlock &&
    g.log.any (fun s => mentions s "Wayfarer's Bauble is destroyed")

-- If the target leaves before resolution, neither effect happens (CR 608.2b).
def fireOfOrthancTargetGone : Game :=
  let id := (namedPermanent paidFireOfOrthanc "Forest").id
  let (g, _) := paidFireOfOrthanc.move id (.graveyard ⟨1⟩) none
  passBoth g

#guard fireOfOrthancTargetGone.log.any (fun s => mentions s "no longer in play")
#guard !fireOfOrthancTargetGone.creaturesWithoutFlyingCantBlock

/-- Chandra's Gray Ogre attacks after Fire of Orthanc; Nissa's Grizzly Bears
cannot block. -/
def fireOfOrthancReadyToBlock : Game :=
  let g := addPermanent started grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addPermanent g forest ⟨1⟩ ⟨1⟩
  let g := g.applyEffect ⟨0⟩ .destroyArtifactOrLandNonflyersCantBlock
    #[Target.permanent (namedPermanent g "Forest").id]
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])
  passBoth g

#guard fireOfOrthancReadyToBlock.pending == .declareBlockers
#guard fireOfOrthancReadyToBlock.creaturesWithoutFlyingCantBlock
#guard
  let g := fireOfOrthancReadyToBlock
  !g.canBlock (namedPermanent g "Grizzly Bears") (namedPermanent g "Gray Ogre")
#guard
  match fireOfOrthancReadyToBlock.apply ⟨1⟩ (.declareBlockers #[(
    (namedPermanent fireOfOrthancReadyToBlock "Grizzly Bears").id,
    (namedPermanent fireOfOrthancReadyToBlock "Gray Ogre").id)]) with
  | .error msg => mentions msg "cannot block"
  | .ok _ => false

/-- A flying creature can still block after Fire of Orthanc. -/
def fireOfOrthancFlyerReadyToBlock : Game :=
  let g := addPermanent started grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g velvetwingButterflies ⟨1⟩ ⟨1⟩
  let g := addPermanent g forest ⟨1⟩ ⟨1⟩
  let g := g.applyEffect ⟨0⟩ .destroyArtifactOrLandNonflyersCantBlock
    #[Target.permanent (namedPermanent g "Forest").id]
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])
  passBoth g

#guard
  let g := fireOfOrthancFlyerReadyToBlock
  g.canBlock (namedPermanent g "Velvetwing Butterflies") (namedPermanent g "Gray Ogre")

def fireOfOrthancFlyerBlocks : Game :=
  let g := fireOfOrthancFlyerReadyToBlock
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Velvetwing Butterflies").id,
    (namedPermanent g "Gray Ogre").id)])

#guard (namedPermanent fireOfOrthancFlyerBlocks "Velvetwing Butterflies").status.blocking ==
  #[(namedPermanent fireOfOrthancFlyerBlocks "Gray Ogre").id]
#guard (namedPermanent fireOfOrthancFlyerBlocks "Gray Ogre").status.blocked

/-- The can't-block effect wears off in cleanup (CR 514.2). -/
def afterFireOfOrthancCleanup : Game :=
  passBoth (skipTo resolvedFireOfOrthanc .end 80)

#guard afterFireOfOrthancCleanup.turnNumber == 2
#guard !afterFireOfOrthancCleanup.creaturesWithoutFlyingCantBlock

/-- The agent casts Fire of Orthanc when that is the playable spell. -/
def agentFireOfOrthancOnly : Game :=
  let g := addPermanent afterDraw forest ⟨1⟩ ⟨1⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withRedMana (addToHand g fireOfOrthanc ⟨0⟩) ⟨0⟩ 4

#guard
  match Agent.choose agentFireOfOrthancOnly ⟨0⟩ with
  | some (.cast id) => (agentFireOfOrthancOnly.object! id).name == "Fire of Orthanc"
  | _ => false

/- Quarrel: target creature you control deals damage equal to its power to
target creature an opponent controls (CR 601.2c / 608.2b / 120.3a). -/

/-- Propose a two-target spell (CR 601.2a / 601.2c). -/
def proposeTwoTargeted (g : Game) (p : PlayerId) (id : ObjectId) (t1 t2 : Target) : Game :=
  mustApply (proposeTargeted g p id t1) p (.target t2)

/-- Quarrel in hand, Llanowar Elves you control, Grizzly Bears opposing. -/
def quarrelSetup : Game :=
  let g := addPermanent afterDraw llanowarElves ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  withGreenMana (addToHand g quarrel ⟨0⟩) ⟨0⟩ 2

#guard quarrel.isInstant
#guard quarrel.requiresTarget
#guard SpellEffect.targetCount .creatureYouControlDealsPowerToOppCreature == 2
#guard quarrelSetup.canCast ⟨0⟩ (handCardNamed quarrelSetup ⟨0⟩ "Quarrel")
#guard quarrelSetup.asSorcery? ⟨0⟩
#guard (quarrelSetup.legalTargets ⟨0⟩ .creatureYouControlDealsPowerToOppCreature).size == 2

-- Cannot cast with no creature you control.
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := withGreenMana (addToHand g quarrel ⟨0⟩) ⟨0⟩ 2
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Quarrel")
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := withGreenMana (addToHand g quarrel ⟨0⟩) ⟨0⟩ 2
  match g.apply ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Quarrel").id) with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

-- Cannot cast with no opposing creature.
#guard
  let g := addPermanent afterDraw llanowarElves ⟨0⟩ ⟨0⟩
  let g := withGreenMana (addToHand g quarrel ⟨0⟩) ⟨0⟩ 2
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Quarrel")

-- Hexproof makes an opposing creature an illegal dest (CR 702.11b).
#guard
  let g := addPermanent afterDraw llanowarElves ⟨0⟩ ⟨0⟩
  let g := addPermanent g hexproofFlyer ⟨1⟩ ⟨1⟩
  let g := withGreenMana (addToHand g quarrel ⟨0⟩) ⟨0⟩ 2
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Quarrel")

def proposedQuarrel : Game :=
  mustApply quarrelSetup ⟨0⟩ (.cast (handCardNamed quarrelSetup ⟨0⟩ "Quarrel").id)

#guard proposedQuarrel.pending == .chooseTargets ⟨0⟩
#guard proposedQuarrel.stack.back!.targets.isEmpty
#guard proposedQuarrel.log.any (fun s => mentions s "begins casting Quarrel")
#guard proposedQuarrel.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- Distinct instances of the word “target” are announced sequentially (CR 601.2c).
#guard
  match proposedQuarrel.announceTargetChoices ⟨0⟩
      #[(Target.permanent (namedPermanent proposedQuarrel "Llanowar Elves").id, none),
        (Target.permanent (namedPermanent proposedQuarrel "Grizzly Bears").id, none)] with
  | .error msg => mentions msg "separately"
  | .ok _ => false

-- First target must be a creature you control, not a player or an opponent's creature.
#guard
  match proposedQuarrel.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match proposedQuarrel.apply ⟨0⟩
      (.target (Target.permanent (namedPermanent proposedQuarrel "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The heuristic's first target is the creature you control.
#guard
  match Agent.choose proposedQuarrel ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (proposedQuarrel.object! tid).name == "Llanowar Elves"
  | _ => false

def quarrelSourceChosen : Game :=
  mustApply proposedQuarrel ⟨0⟩
    (.target (Target.permanent (namedPermanent proposedQuarrel "Llanowar Elves").id))

#guard quarrelSourceChosen.pending == .chooseTargets ⟨0⟩
#guard quarrelSourceChosen.proposedSpell.isSome
#guard quarrelSourceChosen.stack.back!.targets ==
  #[Target.permanent (namedPermanent quarrelSourceChosen "Llanowar Elves").id]
#guard quarrelSourceChosen.log.any (fun s => mentions s "chooses Llanowar Elves as a target")

-- Second target must be an opposing creature.
#guard
  match quarrelSourceChosen.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  match quarrelSourceChosen.apply ⟨0⟩
      (.target (Target.permanent (namedPermanent quarrelSourceChosen "Llanowar Elves").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The heuristic's second target is the opposing creature.
#guard
  match Agent.choose quarrelSourceChosen ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (quarrelSourceChosen.object! tid).name == "Grizzly Bears"
  | _ => false

def targetedQuarrel : Game :=
  mustApply quarrelSourceChosen ⟨0⟩
    (.target (Target.permanent (namedPermanent quarrelSourceChosen "Grizzly Bears").id))

#guard targetedQuarrel.pending == .activateManaAbilities ⟨0⟩
#guard targetedQuarrel.stack.back!.targets ==
  #[Target.permanent (namedPermanent targetedQuarrel "Llanowar Elves").id,
    Target.permanent (namedPermanent targetedQuarrel "Grizzly Bears").id]

def paidQuarrel : Game := mustApply targetedQuarrel ⟨0⟩ .pay

#guard paidQuarrel.hasPriority ⟨0⟩
#guard paidQuarrel.log.any (fun s => mentions s "casts Quarrel")

def resolvedQuarrel : Game := passBoth paidQuarrel

#guard resolvedQuarrel.stack.isEmpty
#guard resolvedQuarrel.battlefield.any (fun o => o.name == "Grizzly Bears")
#guard (namedPermanent resolvedQuarrel "Grizzly Bears").status.damage == 1
#guard resolvedQuarrel.log.any (fun s => mentions s "Llanowar Elves deals 1 damage to Grizzly Bears")
#guard resolvedQuarrel.log.any (fun s => mentions s "goes to the graveyard")
#guard (resolvedQuarrel.player ⟨0⟩).graveyard.any (fun id =>
  (resolvedQuarrel.object! id).name == "Quarrel")

/-- A 3-power source deals lethal damage to a 2/2. -/
def quarrelLethalSetup : Game :=
  let g := addPermanent afterDraw hillGiant ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  withGreenMana (addToHand g quarrel ⟨0⟩) ⟨0⟩ 2

def resolvedQuarrelLethal : Game :=
  let g := proposeTwoTargeted quarrelLethalSetup ⟨0⟩
    (handCardNamed quarrelLethalSetup ⟨0⟩ "Quarrel").id
    (Target.permanent (namedPermanent quarrelLethalSetup "Hill Giant").id)
    (Target.permanent (namedPermanent quarrelLethalSetup "Grizzly Bears").id)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard resolvedQuarrelLethal.stack.isEmpty
#guard !(resolvedQuarrelLethal.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard resolvedQuarrelLethal.log.any (fun s => mentions s "Hill Giant deals 3 damage to Grizzly Bears")
#guard resolvedQuarrelLethal.log.any (fun s => mentions s "Grizzly Bears dies from lethal damage")

/-- Pumping the source after targeting uses the new power (CR 608.2g / 611.3a). -/
def quarrelPumpedSource : Game :=
  let g := addToHand paidQuarrel giantGrowth ⟨0⟩
  let g := withGreenMana g ⟨0⟩ 1
  let g := proposeTargeted g ⟨0⟩ (handCardNamed g ⟨0⟩ "Giant Growth").id
    (Target.permanent (namedPermanent g "Llanowar Elves").id)
  let g := mustApply g ⟨0⟩ .pay
  passBoth (passBoth g)

#guard quarrelPumpedSource.power (namedPermanent quarrelPumpedSource "Llanowar Elves") == 4
#guard !(quarrelPumpedSource.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard quarrelPumpedSource.log.any (fun s =>
  mentions s "Llanowar Elves deals 4 damage to Grizzly Bears")

/-- If the dest leaves before resolution, no damage is dealt (CR 608.2b). -/
def quarrelDestGone : Game :=
  let dest := namedPermanent paidQuarrel "Grizzly Bears"
  let (g, _) := paidQuarrel.move dest.id (.graveyard dest.owner) none
  passBoth g

#guard quarrelDestGone.log.any (fun s => mentions s "The target is no longer in play")
#guard !quarrelDestGone.log.any (fun s => mentions s "deals")
#guard !(quarrelDestGone.battlefield.any (fun o => o.name == "Grizzly Bears"))

/-- If the source leaves before resolution, no damage is dealt (CR 608.2b). -/
def quarrelSourceGone : Game :=
  let src := namedPermanent paidQuarrel "Llanowar Elves"
  let (g, _) := paidQuarrel.move src.id (.graveyard src.owner) none
  passBoth g

#guard quarrelSourceGone.log.any (fun s => mentions s "The target is no longer in play")
#guard !quarrelSourceGone.log.any (fun s => mentions s "deals")
#guard quarrelSourceGone.battlefield.any (fun o => o.name == "Grizzly Bears")
#guard (namedPermanent quarrelSourceGone "Grizzly Bears").status.damage == 0

/-- Hexproof gained after targeting makes the dest illegal (CR 608.2b / 702.11b). -/
def quarrelDestHexproof : Game :=
  let dest := namedPermanent paidQuarrel "Grizzly Bears"
  let g := paidQuarrel.setObject { dest with
    status := { dest.status with untilEotKeywords := Keyword.hexproof } }
  passBoth g

#guard quarrelDestHexproof.log.any (fun s => mentions s "The target is no longer legal")
#guard !quarrelDestHexproof.log.any (fun s => mentions s "deals")
#guard (namedPermanent quarrelDestHexproof "Grizzly Bears").status.damage == 0

/-- The heuristic casts Quarrel when it is the playable spell. -/
def agentQuarrel : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  let g := addPermanent g llanowarElves ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  withGreenMana (addToHand g quarrel ⟨0⟩) ⟨0⟩ 2

#guard
  match Agent.choose agentQuarrel ⟨0⟩ with
  | some (.cast id) => (agentQuarrel.object! id).name == "Quarrel"
  | _ => false

/- Attercop: reach, deathtouch, and landfall +1/+1 until end of turn. -/

#guard attercop.keywords.reach
#guard attercop.keywords.deathtouch
#guard attercop.triggeredAbilities == #[.onLandYouControlEntersGets1]
#guard attercop.power == some 2
#guard attercop.toughness == some 1

/-- A flying attacker can be blocked by Attercop (reach) but not by a Gray Ogre. -/
def flyerVsAttercop : Game :=
  let g := addPermanent started smaugTheGreatCalamity ⟨0⟩ ⟨0⟩
  let g := addPermanent g attercop ⟨1⟩ ⟨1⟩
  let g := addPermanent g grayOgre ⟨1⟩ ⟨1⟩
  let smaug := namedPermanent g "Smaug, the Great Calamity"
  g.setObject { smaug with status := { smaug.status with attacking := true } }

#guard flyerVsAttercop.canBlock
  (namedPermanent flyerVsAttercop "Attercop")
  (namedPermanent flyerVsAttercop "Smaug, the Great Calamity")
#guard !flyerVsAttercop.canBlock
  (namedPermanent flyerVsAttercop "Gray Ogre")
  (namedPermanent flyerVsAttercop "Smaug, the Great Calamity")

/-- Attercop in play; a Forest in hand. -/
def attercopLandfallSetup : Game :=
  let g := addPermanent afterDraw attercop ⟨0⟩ ⟨0⟩
  addToHand g forest ⟨0⟩

#guard attercopLandfallSetup.canPlayLand ⟨0⟩
#guard attercopLandfallSetup.power (namedPermanent attercopLandfallSetup "Attercop") == 2
#guard attercopLandfallSetup.toughness (namedPermanent attercopLandfallSetup "Attercop") == 1

def attercopLandPlayed : Game :=
  mustApply attercopLandfallSetup ⟨0⟩
    (.playLand (handCardNamed attercopLandfallSetup ⟨0⟩ "Forest").id)

#guard attercopLandPlayed.pending == .none
#guard attercopLandPlayed.hasPriority ⟨0⟩
#guard attercopLandPlayed.stack.size == 1
#guard (attercopLandPlayed.object! attercopLandPlayed.stack.back!.objectId).triggeredAbility ==
  some .onLandYouControlEntersGets1
#guard (attercopLandPlayed.object! attercopLandPlayed.stack.back!.objectId).sourceId ==
  some (namedPermanent attercopLandPlayed "Attercop").id
#guard attercopLandPlayed.stack.back!.targets.isEmpty
#guard attercopLandPlayed.log.any (fun s => mentions s "landfall trigger is put on the stack")
#guard attercopLandPlayed.power (namedPermanent attercopLandPlayed "Attercop") == 2

def attercopLandfallResolved : Game := passBoth attercopLandPlayed

#guard attercopLandfallResolved.stack.isEmpty
#guard attercopLandfallResolved.hasPriority ⟨0⟩
#guard (namedPermanent attercopLandfallResolved "Attercop").status.pumpPower == 1
#guard (namedPermanent attercopLandfallResolved "Attercop").status.pumpToughness == 1
#guard attercopLandfallResolved.power
  (namedPermanent attercopLandfallResolved "Attercop") == 3
#guard attercopLandfallResolved.toughness
  (namedPermanent attercopLandfallResolved "Attercop") == 2
#guard attercopLandfallResolved.log.any (fun s =>
  mentions s "Attercop gets +1/+1 until end of turn")

-- Direct resolution of a landfall pump stacks with an existing pump.
#guard
  let id := (namedPermanent attercopLandfallResolved "Attercop").id
  let g := attercopLandfallResolved.applyTriggeredAbility ⟨0⟩
    .onLandYouControlEntersGets1 (some id)
  g.power (namedPermanent g "Attercop") == 4 &&
    g.toughness (namedPermanent g "Attercop") == 3

/-- An opponent's land does not trigger your landfall. -/
def nissaLandVsAttercop : Game :=
  let g := addPermanent afterDraw attercop ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .end 80)
  let g := skipTo g .precombatMain 80
  let g := addToHand g forest ⟨1⟩
  mustApply g ⟨1⟩ (.playLand (handCardNamed g ⟨1⟩ "Forest").id)

#guard nissaLandVsAttercop.stack.isEmpty
#guard !(nissaLandVsAttercop.log.any (fun s => mentions s "landfall"))
#guard nissaLandVsAttercop.power (namedPermanent nissaLandVsAttercop "Attercop") == 2

/-- If Attercop leaves before the trigger resolves, it is not pumped. -/
def attercopSourceGone : Game :=
  let id := (namedPermanent attercopLandPlayed "Attercop").id
  let (g, _) := attercopLandPlayed.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard attercopSourceGone.log.any (fun s => mentions s "source is no longer in play")
#guard !(attercopSourceGone.battlefield.any (fun o => o.name == "Attercop"))

/-- The +1/+1 wears off in cleanup (CR 514.3). -/
def afterAttercopCleanup : Game := passBoth (skipTo attercopLandfallResolved .end 80)

#guard afterAttercopCleanup.power (namedPermanent afterAttercopCleanup "Attercop") == 2
#guard afterAttercopCleanup.toughness (namedPermanent afterAttercopCleanup "Attercop") == 1
#guard (namedPermanent afterAttercopCleanup "Attercop").status.pumpPower == 0
#guard (namedPermanent afterAttercopCleanup "Attercop").status.pumpToughness == 0

/-- Two Attercops both trigger from one land; the controller chooses order
(CR 603.3b). -/
def twoAttercopsLandPending : Game :=
  let g := addPermanent afterDraw attercop ⟨0⟩ ⟨0⟩
  let g := addPermanent g attercop ⟨0⟩ ⟨0⟩
  let g := addToHand g forest ⟨0⟩
  mustApply g ⟨0⟩ (.playLand (handCardNamed g ⟨0⟩ "Forest").id)

#guard twoAttercopsLandPending.pending == .chooseTriggerToStack ⟨0⟩
#guard twoAttercopsLandPending.waitingTriggers.size == 2
#guard twoAttercopsLandPending.stack.isEmpty
#guard twoAttercopsLandPending.actor == some ⟨0⟩
#guard twoAttercopsLandPending.log.any (fun s => mentions s "CR 603.3b")
#guard
  match Agent.choose twoAttercopsLandPending ⟨0⟩ with
  | some (.stackTriggers ids) =>
    ids == twoAttercopsLandPending.defaultTriggerSourceIds ⟨0⟩
  | _ => false

def twoAttercopsLandPlayed : Game := applyIdle twoAttercopsLandPending

#guard twoAttercopsLandPlayed.stack.size == 2
#guard (twoAttercopsLandPlayed.object! twoAttercopsLandPlayed.stack.back!.objectId).triggeredAbility ==
  some .onLandYouControlEntersGets1
#guard (twoAttercopsLandPlayed.object!
  twoAttercopsLandPlayed.stack[0]!.objectId).triggeredAbility ==
  some .onLandYouControlEntersGets1

def twoAttercopsPumped : Game := passBoth (passBoth twoAttercopsLandPlayed)

#guard twoAttercopsPumped.stack.isEmpty
#guard
  let spiders := twoAttercopsPumped.battlefield.filter (fun o => o.name == "Attercop")
  spiders.size == 2 && spiders.all (fun o => twoAttercopsPumped.power o == 3)

/- CR 603.3b: APNAP order and the controller's chosen order. -/

/-- The controller may put the newer Attercop's trigger first (bottom). -/
def twoAttercopsReversed : Game :=
  let ids := twoAttercopsLandPending.defaultTriggerSourceIds ⟨0⟩
  mustApply twoAttercopsLandPending ⟨0⟩ (.stackTriggers ids.reverse)

#guard twoAttercopsReversed.pending == .none
#guard twoAttercopsReversed.stack.size == 2
#guard twoAttercopsReversed.waitingTriggers.isEmpty
#guard twoAttercopsReversed.hasPriority ⟨0⟩
#guard
  let ids := twoAttercopsLandPending.defaultTriggerSourceIds ⟨0⟩
  (twoAttercopsReversed.object! twoAttercopsReversed.stack[0]!.objectId).sourceId ==
    some ids[1]! &&
    (twoAttercopsReversed.object! twoAttercopsReversed.stack.back!.objectId).sourceId ==
      some ids[0]!
#guard twoAttercopsReversed.log.any (fun s =>
  mentions s "chooses the order of triggered abilities")

-- An incomplete list is illegal.
#guard
  match twoAttercopsLandPending.apply ⟨0⟩
      (.stackTriggers (twoAttercopsLandPending.defaultTriggerSourceIds ⟨0⟩).pop) with
  | .error msg => mentions msg "CR 603.3b"
  | .ok _ => false

-- Only the controller of those triggers may choose the order.
#guard
  match twoAttercopsLandPending.apply ⟨1⟩
      (.stackTriggers (twoAttercopsLandPending.defaultTriggerSourceIds ⟨0⟩)) with
  | .error msg => mentions msg "CR 603.3b"
  | .ok _ => false

/-- Both Fireleapers in play with a creature each side can target. -/
def apnapDiesSetup : Game :=
  let g := addPermanent afterDraw goblinFireleaper ⟨0⟩ ⟨0⟩
  let g := addPermanent g goblinFireleaper ⟨1⟩ ⟨1⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩

def fireleaperControlledBy (g : Game) (p : PlayerId) : ObjectId :=
  match (g.permanentsOf p).find? (fun o => o.name == "Goblin Fireleaper") with
  | some o => o.id
  | none => panic! "expected Goblin Fireleaper"

/-- Chandra (AP) and Nissa each have a dies trigger; AP puts first and
announces targets before NAP's trigger is stacked (CR 603.3b / 603.3d). -/
def apnapDiesTriggers : Game :=
  let chandraId := fireleaperControlledBy apnapDiesSetup ⟨0⟩
  let nissaId := fireleaperControlledBy apnapDiesSetup ⟨1⟩
  let (g, _) := apnapDiesSetup.move chandraId (.graveyard ⟨0⟩) none
  let (g, _) := g.move nissaId (.graveyard ⟨1⟩) none
  g.receivePriority ⟨0⟩

#guard apnapDiesTriggers.stack.size == 1
#guard apnapDiesTriggers.waitingTriggers.size == 1
#guard apnapDiesTriggers.waitingTriggers[0]!.controller == ⟨1⟩
#guard apnapDiesTriggers.pending == .chooseTargets ⟨0⟩
#guard apnapDiesTriggers.stack[0]!.controller == ⟨0⟩
#guard (apnapDiesTriggers.object! apnapDiesTriggers.stack[0]!.objectId).sourceId ==
  some (fireleaperControlledBy apnapDiesSetup ⟨0⟩)

def apnapDiesAfterApTargets : Game :=
  match (apnapDiesTriggers.permanentsOf ⟨1⟩).find? (fun o => o.name == "Grizzly Bears") with
  | none => panic! "expected Nissa's Grizzly Bears"
  | some bears =>
    mustApply apnapDiesTriggers ⟨0⟩ (.target (Target.permanent bears.id))

#guard apnapDiesAfterApTargets.stack.size == 2
#guard apnapDiesAfterApTargets.waitingTriggers.isEmpty
#guard apnapDiesAfterApTargets.pending == .chooseTargets ⟨1⟩
#guard apnapDiesAfterApTargets.stack[0]!.controller == ⟨0⟩
#guard apnapDiesAfterApTargets.stack.back!.controller == ⟨1⟩
#guard (apnapDiesAfterApTargets.object! apnapDiesAfterApTargets.stack.back!.objectId).sourceId ==
  some (fireleaperControlledBy apnapDiesSetup ⟨1⟩)

/-- Wood Elves putting a Forest onto the battlefield also triggers landfall. -/
def attercopWoodElvesResolved : Game :=
  let g := addPermanent afterDraw attercop ⟨0⟩ ⟨0⟩
  let g := withGreenMana (addToHand g woodElves ⟨0⟩) ⟨0⟩
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Wood Elves").id)
  let g := mustApply g ⟨0⟩ .pay
  let g := passBoth g
  let g := addToLibraryTop (addToLibraryTop g forest ⟨0⟩) mountain ⟨0⟩
  passBoth g

#guard attercopWoodElvesResolved.battlefield.any (fun o => o.name == "Forest")
#guard attercopWoodElvesResolved.stack.size == 1
#guard (attercopWoodElvesResolved.object!
  attercopWoodElvesResolved.stack.back!.objectId).triggeredAbility ==
  some .onLandYouControlEntersGets1
#guard attercopWoodElvesResolved.log.any (fun s => mentions s "landfall trigger is put on the stack")

def attercopWoodElvesPumped : Game := passBoth attercopWoodElvesResolved

#guard attercopWoodElvesPumped.stack.isEmpty
#guard attercopWoodElvesPumped.power
  (namedPermanent attercopWoodElvesPumped "Attercop") == 3
#guard attercopWoodElvesPumped.log.any (fun s =>
  mentions s "Attercop gets +1/+1 until end of turn")

/-- The heuristic plays a land when Attercop is in play. -/
def agentAttercopLand : Game :=
  let g := afterDraw.modifyPlayer ⟨0⟩ (fun pl => { pl with hand := #[] })
  let g := addPermanent g attercop ⟨0⟩ ⟨0⟩
  addToHand g forest ⟨0⟩

#guard
  match Agent.choose agentAttercopLand ⟨0⟩ with
  | some (.playLand id) => (agentAttercopLand.object! id).name == "Forest"
  | _ => false

/- Rogue's Passage: {T}: Add {C} and {4}, {T}: target creature can't be blocked. -/

def passageAbility : ActivatedAbility :=
  roguesPassage.activatedAbilities[0]!

/-- Passage, Gray Ogre, and opposing Bears; {4} in the pool; land drop used. -/
def passageReady : Game :=
  let g := addPermanent afterDraw roguesPassage ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  withRedMana (g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })) ⟨0⟩ 4

def passageSource (g : Game) : GameObject :=
  namedPermanent g "Rogue's Passage"

#guard passageAbility.effect == .targetCantBeBlockedThisTurn
#guard passageAbility.cost.tap
#guard passageAbility.cost.mana == ManaCost.ofGeneric 4
#guard passageAbility.effect.requiresTarget
#guard !passageAbility.onlyAsSorcery
#guard passageReady.canActivate ⟨0⟩ (passageSource passageReady) passageAbility
#guard !(passageReady.canActivate ⟨1⟩ (passageSource passageReady) passageAbility)
#guard (passageReady.player ⟨0⟩).manaPool.canPay passageAbility.cost.mana
#guard roguesPassage.manaAbilities == #[.colorless]

-- Cannot activate with no creature in play.
#guard
  let g := addPermanent afterDraw roguesPassage ⟨0⟩ ⟨0⟩
  let g := withRedMana g ⟨0⟩ 4
  !g.canActivate ⟨0⟩ (namedPermanent g "Rogue's Passage") passageAbility

-- Cannot activate while the land is tapped.
#guard
  let o := passageSource passageReady
  let g := passageReady.setObject { o with status := { o.status with tapped := true } }
  !g.canActivate ⟨0⟩ (namedPermanent g "Rogue's Passage") passageAbility

-- Instant-speed: Passage can activate during the end step.
#guard
  let g := skipTo passageReady .end 80
  g.step == .end && g.canActivate ⟨0⟩ (passageSource g) passageAbility

-- The {T}: Add {C} mana ability still works when the land is untapped.
#guard
  match passageReady.tapForMana ⟨0⟩ (passageSource passageReady).id .colorless with
  | .ok g =>
    (g.player ⟨0⟩).manaPool.get .colorless >= 1 &&
      (namedPermanent g "Rogue's Passage").status.tapped
  | .error _ => false

-- The heuristic does not dump {4} in the main phase.
#guard
  match Agent.choose passageReady ⟨0⟩ with
  | some (.activate id 0) => (passageReady.object! id).name != "Rogue's Passage"
  | _ => true

def proposedPassage : Game :=
  mustApply passageReady ⟨0⟩ (.activate (passageSource passageReady).id 0)

#guard
  match proposedPassage.pending with
  | .chooseTargets ⟨0⟩ => true
  | _ => false
#guard proposedPassage.proposedSpell.isSome
#guard proposedPassage.stack.size == 1
#guard (proposedPassage.object! proposedPassage.stack.back!.objectId).abilityEffect ==
  some .targetCantBeBlockedThisTurn
#guard (namedPermanent proposedPassage "Rogue's Passage").isOnBattlefield
#guard !(namedPermanent proposedPassage "Rogue's Passage").status.tapped
#guard proposedPassage.log.any (fun s => mentions s "begins activating Rogue's Passage")
#guard proposedPassage.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- Opponent cannot choose Chandra's target.
#guard
  match proposedPassage.apply ⟨1⟩
      (.target (Target.permanent (namedPermanent proposedPassage "Gray Ogre").id)) with
  | .error msg => mentions msg "may choose targets"
  | .ok _ => false

-- The heuristic targets Chandra's creature, not Nissa's.
#guard
  match Agent.choose proposedPassage ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (proposedPassage.object! tid).name == "Gray Ogre"
  | _ => false

def targetedPassage : Game :=
  mustApply proposedPassage ⟨0⟩
    (.target (Target.permanent (namedPermanent proposedPassage "Gray Ogre").id))

#guard targetedPassage.pending == .activateManaAbilities ⟨0⟩
#guard targetedPassage.stack.back!.targets ==
  #[Target.permanent (namedPermanent targetedPassage "Gray Ogre").id]
#guard targetedPassage.log.any (fun s => mentions s "chooses Gray Ogre as a target")

-- Cannot tap Passage for mana while its {T} is part of the activation cost.
#guard
  match targetedPassage.tapForMana ⟨0⟩ (passageSource targetedPassage).id .colorless with
  | .error msg => mentions msg "needed to pay"
  | .ok _ => false

-- Opponent cannot pay Chandra's activation.
#guard
  match targetedPassage.apply ⟨1⟩ .pay with
  | .error msg => mentions msg "Only Chandra"
  | .ok _ => false

def paidPassage : Game := mustApply targetedPassage ⟨0⟩ .pay

#guard paidPassage.hasPriority ⟨0⟩
#guard paidPassage.stack.size == 1
#guard (namedPermanent paidPassage "Rogue's Passage").status.tapped
#guard !(namedPermanent paidPassage "Gray Ogre").status.untilEotKeywords.cantBeBlocked
#guard paidPassage.log.any (fun s => mentions s "activates Rogue's Passage")

def passageResolved : Game := passBoth paidPassage

#guard passageResolved.stack.isEmpty
#guard (namedPermanent passageResolved "Gray Ogre").status.untilEotKeywords.cantBeBlocked
#guard passageResolved.hasCantBeBlocked (namedPermanent passageResolved "Gray Ogre")
#guard !passageResolved.hasCantBeBlocked (namedPermanent passageResolved "Grizzly Bears")
#guard passageResolved.log.any (fun s => mentions s "Gray Ogre can't be blocked this turn")

-- Targeting an opponent's creature is legal.
#guard
  let g := mustApply proposedPassage ⟨0⟩
    (.target (Target.permanent (namedPermanent proposedPassage "Grizzly Bears").id))
  g.stack.back!.targets ==
    #[Target.permanent (namedPermanent g "Grizzly Bears").id]

-- Hexproof makes an opposing creature an illegal target (CR 702.11b).
#guard
  let bears := namedPermanent proposedPassage "Grizzly Bears"
  let g := proposedPassage.setObject { bears with
    status := { bears.status with untilEotKeywords := Keyword.hexproof } }
  match g.apply ⟨0⟩
      (.target (Target.permanent (namedPermanent g "Grizzly Bears").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

/-- If the target leaves before the ability resolves, it does nothing. -/
def passageTargetGone : Game :=
  let id := (namedPermanent paidPassage "Gray Ogre").id
  let (g, _) := paidPassage.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard passageTargetGone.log.any (fun s => mentions s "no longer in play")
#guard !(passageTargetGone.battlefield.any (fun o => o.name == "Gray Ogre"))

/-- The can't-be-blocked grant wears off in cleanup. -/
def afterPassageCleanup : Game :=
  passBoth (skipTo passageResolved .end 80)

#guard !(namedPermanent afterPassageCleanup "Gray Ogre").status.untilEotKeywords.cantBeBlocked
#guard !afterPassageCleanup.hasCantBeBlocked
  (namedPermanent afterPassageCleanup "Gray Ogre")

/-- Gray Ogre attacks after becoming unblockable; Bears cannot block. -/
def passageOgreAttacking : Game :=
  let g := passBoth (skipTo passageResolved .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])

def passageReadyToBlock : Game := passBoth passageOgreAttacking

#guard passageReadyToBlock.pending == .declareBlockers
#guard !passageReadyToBlock.canBlock
  (namedPermanent passageReadyToBlock "Grizzly Bears")
  (namedPermanent passageReadyToBlock "Gray Ogre")
#guard
  match passageReadyToBlock.apply ⟨1⟩ (.declareBlockers #[(
    (namedPermanent passageReadyToBlock "Grizzly Bears").id,
    (namedPermanent passageReadyToBlock "Gray Ogre").id)]) with
  | .error msg => mentions msg "cannot block"
  | .ok _ => false

def passageUnblockedDamage : Game :=
  passBoth (mustApply passageReadyToBlock ⟨1⟩ (.declareBlockers #[]))

#guard (passageUnblockedDamage.player ⟨1⟩).life == 18
#guard passageUnblockedDamage.log.any (fun s =>
  mentions s "Gray Ogre deals 2 combat damage to Nissa")
#guard !passageUnblockedDamage.log.any (fun s =>
  mentions s "Grizzly Bears blocks Gray Ogre")

/-- After attackers are declared, the heuristic activates Passage with {4} in the pool. -/
def passageAfterAttack : Game :=
  let g := passBoth (skipTo passageReady .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])
  withRedMana g ⟨0⟩ 4

#guard passageAfterAttack.hasPriority ⟨0⟩
#guard (namedPermanent passageAfterAttack "Gray Ogre").status.attacking
#guard
  match Agent.choose passageAfterAttack ⟨0⟩ with
  | some (.activate id 0) => id == (passageSource passageAfterAttack).id
  | _ => false

/-- Three Mountains plus Passage is not enough {4} once Passage must stay untapped. -/
def passageThreeMountainsAttacking : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  let g := addPermanent g roguesPassage ⟨0⟩ ⟨0⟩
  let g := addPermanent g grayOgre ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addUntappedLand g mountain
  let g := addUntappedLand g mountain
  let g := addUntappedLand g mountain
  let g := passBoth (skipTo g .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])

#guard
  (passageThreeMountainsAttacking.availableMana ⟨0⟩).canPay (ManaCost.ofGeneric 4)
#guard
  !(passageThreeMountainsAttacking.availableManaExcept ⟨0⟩
    (some (passageSource passageThreeMountainsAttacking).id)).canPay (ManaCost.ofGeneric 4)
#guard
  match Agent.choose passageThreeMountainsAttacking ⟨0⟩ with
  | some (.activate id 0) => (passageThreeMountainsAttacking.object! id).name != "Rogue's Passage"
  | _ => true

/-- Four Mountains plus Passage: the heuristic activates and taps Mountains, not Passage. -/
def passageFourMountainsAttacking : Game :=
  let g := addUntappedLand passageThreeMountainsAttacking mountain
  g

#guard
  (passageFourMountainsAttacking.availableManaExcept ⟨0⟩
    (some (passageSource passageFourMountainsAttacking).id)).canPay (ManaCost.ofGeneric 4)
#guard
  match Agent.choose passageFourMountainsAttacking ⟨0⟩ with
  | some (.activate id 0) => id == (passageSource passageFourMountainsAttacking).id
  | _ => false

def targetedPassageFromLands : Game :=
  let g := mustApply passageFourMountainsAttacking ⟨0⟩
    (.activate (passageSource passageFourMountainsAttacking).id 0)
  mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Gray Ogre").id))

#guard targetedPassageFromLands.pending == .activateManaAbilities ⟨0⟩
#guard
  match Agent.choose targetedPassageFromLands ⟨0⟩ with
  | some (.tapForMana id _) =>
    (targetedPassageFromLands.object! id).name != "Rogue's Passage"
  | _ => false

/- Smite the Deathless: 3 damage, lose indestructible until EOT, exile if it
would die this turn (CR 702.12 / 614.1 / 700.4). -/

def indestructibleBeast : CardDef :=
  creature "Indestructible Beast" ManaCost.empty #[] 2 2
    (keywords := Keyword.indestructible)

def indestructibleFlyer : CardDef :=
  creature "Indestructible Flyer" ManaCost.empty #[] 4 4
    (keywords := Keyword.flying.merge Keyword.indestructible)

def indestructibleZero : CardDef :=
  creature "Indestructible Zero" ManaCost.empty #[] 0 0
    (keywords := Keyword.indestructible)

def smiteOn (card : CardDef) : Game :=
  let g := addPermanent afterDraw card ⟨1⟩ ⟨1⟩
  withRedMana (addToHand g smiteTheDeathless ⟨0⟩) ⟨0⟩ 2

def smiteSetup : Game := smiteOn grizzlyBears

#guard smiteTheDeathless.isInstant
#guard smiteTheDeathless.requiresTarget
#guard smiteTheDeathless.spellEffect == some (.dealDamageLoseIndestructibleExile 3)
#guard smiteSetup.canCast ⟨0⟩ (handCardNamed smiteSetup ⟨0⟩ "Smite the Deathless")
#guard smiteSetup.asSorcery? ⟨0⟩
#guard (smiteSetup.legalTargets ⟨0⟩ (.dealDamageLoseIndestructibleExile 3)).size == 1

-- Cannot cast with no creature on the battlefield.
#guard
  let g := withRedMana (addToHand afterDraw smiteTheDeathless ⟨0⟩) ⟨0⟩ 2
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Smite the Deathless")
#guard
  let g := withRedMana (addToHand afterDraw smiteTheDeathless ⟨0⟩) ⟨0⟩ 2
  match g.apply ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Smite the Deathless").id) with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

def proposedSmite : Game :=
  mustApply smiteSetup ⟨0⟩ (.cast (handCardNamed smiteSetup ⟨0⟩ "Smite the Deathless").id)

#guard
  match proposedSmite.pending with
  | .chooseTargets ⟨0⟩ => true
  | _ => false
#guard proposedSmite.log.any (fun s => mentions s "begins casting Smite the Deathless")
#guard proposedSmite.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- Smite cannot target a player.
#guard
  match proposedSmite.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The heuristic targets an opposing creature.
#guard
  match Agent.choose proposedSmite ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (proposedSmite.object! tid).name == "Grizzly Bears"
  | _ => false

def paidSmite : Game :=
  let g := mustApply proposedSmite ⟨0⟩
    (.target (Target.permanent (namedPermanent proposedSmite "Grizzly Bears").id))
  mustApply g ⟨0⟩ .pay

#guard paidSmite.hasPriority ⟨0⟩
#guard paidSmite.log.any (fun s => mentions s "casts Smite the Deathless")

def resolvedSmiteOnBears : Game := passBoth paidSmite

#guard resolvedSmiteOnBears.stack.isEmpty
#guard !(resolvedSmiteOnBears.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard resolvedSmiteOnBears.objects.any (fun o =>
  o.name == "Grizzly Bears" && o.zone == .exile)
#guard !(resolvedSmiteOnBears.objects.any (fun o =>
  o.name == "Grizzly Bears" && o.zone == .graveyard ⟨1⟩))
#guard resolvedSmiteOnBears.log.any (fun s =>
  mentions s "is dealt 3 damage, loses indestructible until end of turn")
#guard resolvedSmiteOnBears.log.any (fun s => mentions s "dies from lethal damage")
#guard resolvedSmiteOnBears.log.any (fun s => mentions s "is exiled instead of dying")
#guard (resolvedSmiteOnBears.player ⟨0⟩).graveyard.any (fun id =>
  (resolvedSmiteOnBears.object! id).name == "Smite the Deathless")

/-- 3 damage is not lethal to a 4-toughness creature; the replacement lasts. -/
def resolvedSmiteOnWurm : Game :=
  let g := smiteOn crawWurm
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Smite the Deathless").id)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Craw Wurm").id))
  passBoth (mustApply g ⟨0⟩ .pay)

#guard resolvedSmiteOnWurm.battlefield.any (fun o => o.name == "Craw Wurm")
#guard (namedPermanent resolvedSmiteOnWurm "Craw Wurm").status.damage == 3
#guard (namedPermanent resolvedSmiteOnWurm "Craw Wurm").status.untilEotLosesIndestructible
#guard (namedPermanent resolvedSmiteOnWurm "Craw Wurm").status.untilEotExileIfDies
#guard !resolvedSmiteOnWurm.objects.any (fun o =>
  o.name == "Craw Wurm" && o.zone == .exile)

/-- Later this turn, 0 toughness is replaced by exile. -/
def smiteWurmThenZeroToughness : Game :=
  let o := namedPermanent resolvedSmiteOnWurm "Craw Wurm"
  let g := resolvedSmiteOnWurm.setObject { o with
    status := { o.status with pump := (o.status.pump.1, -4) } }
  g.receivePriority ⟨0⟩

#guard !(smiteWurmThenZeroToughness.battlefield.any (fun o => o.name == "Craw Wurm"))
#guard smiteWurmThenZeroToughness.objects.any (fun o =>
  o.name == "Craw Wurm" && o.zone == .exile)
#guard smiteWurmThenZeroToughness.log.any (fun s => mentions s "dies (toughness 0)")
#guard smiteWurmThenZeroToughness.log.any (fun s => mentions s "is exiled instead of dying")

/-- The until-EOT flags and marked damage wear off in cleanup. -/
def afterSmiteWurmCleanup : Game :=
  passBoth (skipTo resolvedSmiteOnWurm .end 80)

#guard (namedPermanent afterSmiteWurmCleanup "Craw Wurm").status.damage == 0
#guard !(namedPermanent afterSmiteWurmCleanup "Craw Wurm").status.untilEotLosesIndestructible
#guard !(namedPermanent afterSmiteWurmCleanup "Craw Wurm").status.untilEotExileIfDies

/-- Printed indestructible ignores lethal damage (CR 702.12b / 704.5g). -/
def indestructibleSurvivesDamage : Game :=
  let g := addPermanent afterDraw indestructibleBeast ⟨1⟩ ⟨1⟩
  let g := g.applyEffect ⟨0⟩ (.dealDamage 3)
    #[Target.permanent (namedPermanent g "Indestructible Beast").id]
  g.receivePriority ⟨0⟩

#guard indestructibleSurvivesDamage.battlefield.any (fun o =>
  o.name == "Indestructible Beast")
#guard (namedPermanent indestructibleSurvivesDamage "Indestructible Beast").status.damage == 3
#guard indestructibleSurvivesDamage.hasIndestructible
  (namedPermanent indestructibleSurvivesDamage "Indestructible Beast")
#guard !indestructibleSurvivesDamage.log.any (fun s => mentions s "dies from lethal damage")

/-- Indestructible does not save a creature with 0 toughness (CR 704.5f). -/
def indestructibleZeroDies : Game :=
  let g := addPermanent afterDraw indestructibleZero ⟨1⟩ ⟨1⟩
  g.receivePriority ⟨0⟩

#guard !(indestructibleZeroDies.battlefield.any (fun o => o.name == "Indestructible Zero"))
#guard indestructibleZeroDies.objects.any (fun o =>
  o.name == "Indestructible Zero" && o.zone == .graveyard ⟨1⟩)
#guard indestructibleZeroDies.log.any (fun s => mentions s "dies (toughness 0)")
#guard !indestructibleZeroDies.log.any (fun s => mentions s "exiled instead")

/-- Destroy does nothing to an indestructible creature (CR 701.7b / 702.12b). -/
def destroyIndestructibleFlyer : Game :=
  let g := addPermanent afterDraw indestructibleFlyer ⟨1⟩ ⟨1⟩
  g.applyEffect ⟨0⟩ .destroyCreatureWithFlying
    #[Target.permanent (namedPermanent g "Indestructible Flyer").id]

#guard destroyIndestructibleFlyer.battlefield.any (fun o =>
  o.name == "Indestructible Flyer")
#guard destroyIndestructibleFlyer.log.any (fun s =>
  mentions s "is indestructible and isn't destroyed")
#guard !destroyIndestructibleFlyer.log.any (fun s =>
  mentions s "Indestructible Flyer is destroyed")

/-- Smite strips indestructible from a 2/2 and exiles it to lethal damage. -/
def resolvedSmiteOnIndestructibleBeast : Game :=
  let g := smiteOn indestructibleBeast
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Smite the Deathless").id)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Indestructible Beast").id))
  passBoth (mustApply g ⟨0⟩ .pay)

#guard !(resolvedSmiteOnIndestructibleBeast.battlefield.any (fun o =>
  o.name == "Indestructible Beast"))
#guard resolvedSmiteOnIndestructibleBeast.objects.any (fun o =>
  o.name == "Indestructible Beast" && o.zone == .exile)
#guard resolvedSmiteOnIndestructibleBeast.log.any (fun s =>
  mentions s "is exiled instead of dying")

/-- After Smite, a 4/4 flyer can be destroyed and is exiled instead of dying. -/
def resolvedSmiteOnIndestructibleFlyer : Game :=
  let g := smiteOn indestructibleFlyer
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Smite the Deathless").id)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Indestructible Flyer").id))
  passBoth (mustApply g ⟨0⟩ .pay)

#guard resolvedSmiteOnIndestructibleFlyer.battlefield.any (fun o =>
  o.name == "Indestructible Flyer")
#guard !resolvedSmiteOnIndestructibleFlyer.hasIndestructible
  (namedPermanent resolvedSmiteOnIndestructibleFlyer "Indestructible Flyer")
#guard (namedPermanent resolvedSmiteOnIndestructibleFlyer "Indestructible Flyer").status.damage
  == 3
#guard (resolvedSmiteOnIndestructibleFlyer.effectiveKeywords
  (namedPermanent resolvedSmiteOnIndestructibleFlyer "Indestructible Flyer")).flying
#guard !(resolvedSmiteOnIndestructibleFlyer.effectiveKeywords
  (namedPermanent resolvedSmiteOnIndestructibleFlyer "Indestructible Flyer")).indestructible

def smiteFlyerThenDestroy : Game :=
  resolvedSmiteOnIndestructibleFlyer.applyEffect ⟨0⟩ .destroyCreatureWithFlying
    #[Target.permanent
      (namedPermanent resolvedSmiteOnIndestructibleFlyer "Indestructible Flyer").id]

#guard !(smiteFlyerThenDestroy.battlefield.any (fun o => o.name == "Indestructible Flyer"))
#guard smiteFlyerThenDestroy.objects.any (fun o =>
  o.name == "Indestructible Flyer" && o.zone == .exile)
#guard smiteFlyerThenDestroy.log.any (fun s => mentions s "is destroyed")
#guard smiteFlyerThenDestroy.log.any (fun s => mentions s "is exiled instead of dying")

/-- Exile-instead-of-dying means dies triggers do not go on the stack (CR 700.4). -/
def smiteOnFireleaper : Game :=
  let g := addPermanent afterDraw goblinFireleaper ⟨1⟩ ⟨1⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  withRedMana (addToHand g smiteTheDeathless ⟨0⟩) ⟨0⟩ 2

def resolvedSmiteOnFireleaper : Game :=
  let g := mustApply smiteOnFireleaper ⟨0⟩
    (.cast (handCardNamed smiteOnFireleaper ⟨0⟩ "Smite the Deathless").id)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Goblin Fireleaper").id))
  passBoth (mustApply g ⟨0⟩ .pay)

#guard resolvedSmiteOnFireleaper.objects.any (fun o =>
  o.name == "Goblin Fireleaper" && o.zone == .exile)
#guard resolvedSmiteOnFireleaper.stack.isEmpty
#guard !resolvedSmiteOnFireleaper.log.any (fun s => mentions s "dies trigger")
#guard resolvedSmiteOnFireleaper.battlefield.any (fun o => o.name == "Grizzly Bears")
#guard (namedPermanent resolvedSmiteOnFireleaper "Grizzly Bears").status.damage == 0

/-- The heuristic casts Smite when it is the playable spell. -/
def agentSmite : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  withRedMana (addToHand g smiteTheDeathless ⟨0⟩) ⟨0⟩ 2

#guard
  match Agent.choose agentSmite ⟨0⟩ with
  | some (.cast id) => (agentSmite.object! id).name == "Smite the Deathless"
  | _ => false

/- Ravening Warg: deathtouch (CR 702.2 / 704.5h) and Ferocious attack-gain-life. -/

#guard raveningWarg.keywords.deathtouch
#guard raveningWarg.triggeredAbilities == #[.onAttackFerociousGainLife 2]
#guard raveningWarg.power == some 2
#guard raveningWarg.toughness == some 2
#guard withWarg.hasDeathtouch (namedPermanent withWarg "Ravening Warg")
#guard (withWarg.effectiveKeywords (namedPermanent withWarg "Ravening Warg")).deathtouch
#guard withWarg.power (namedPermanent withWarg "Ravening Warg") == 2

/-- Alone, Ravening Warg is 2/2, so Ferocious does not trigger. -/
def wargAloneAttackDeclared : Game :=
  let g := passBoth (skipTo withWarg .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Ravening Warg").id])

#guard wargAloneAttackDeclared.stack.isEmpty
#guard !wargAloneAttackDeclared.log.any (fun s => mentions s "attack trigger")
#guard (namedPermanent wargAloneAttackDeclared "Ravening Warg").status.attacking
#guard (wargAloneAttackDeclared.player ⟨0⟩).life == 20

/-- A 3-power creature you control is not enough for Ferocious. -/
def wargAndGiant : Game :=
  addPermanent withWarg hillGiant ⟨0⟩ ⟨0⟩

def wargAttackWithGiant : Game :=
  let g := passBoth (skipTo wargAndGiant .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Ravening Warg").id])

#guard wargAttackWithGiant.stack.isEmpty
#guard !wargAttackWithGiant.log.any (fun s => mentions s "attack trigger")
#guard wargAndGiant.greatestPowerAmongCreatures ⟨0⟩ == 3

/-- An opponent's 4-power creature does not enable Ferocious. -/
def wargVsOppBaloth : Game :=
  addPermanent withWarg rumblingBaloth ⟨1⟩ ⟨1⟩

def wargAttackVsOppBaloth : Game :=
  let g := passBoth (skipTo wargVsOppBaloth .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Ravening Warg").id])

#guard wargAttackVsOppBaloth.stack.isEmpty
#guard !wargAttackVsOppBaloth.log.any (fun s => mentions s "attack trigger")
#guard wargVsOppBaloth.greatestPowerAmongCreatures ⟨0⟩ == 2
#guard wargVsOppBaloth.greatestPowerAmongCreatures ⟨1⟩ == 4

/-- A 4-power creature you control makes Ferocious trigger. -/
def wargAndBaloth : Game :=
  addPermanent withWarg rumblingBaloth ⟨0⟩ ⟨0⟩

#guard wargAndBaloth.greatestPowerAmongCreatures ⟨0⟩ == 4
#guard wargAndBaloth.triggerConditionHolds ⟨0⟩ (.onAttackFerociousGainLife 2)
#guard !withWarg.triggerConditionHolds ⟨0⟩ (.onAttackFerociousGainLife 2)
#guard withWarg.triggerConditionHolds ⟨0⟩ (.onAttackScry 1)

def wargFerociousDeclared : Game :=
  let g := passBoth (skipTo wargAndBaloth .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Ravening Warg").id])

#guard wargFerociousDeclared.stack.size == 1
#guard (wargFerociousDeclared.object! wargFerociousDeclared.stack.back!.objectId).name ==
  "Ravening Warg's ability"
#guard (wargFerociousDeclared.object! wargFerociousDeclared.stack.back!.objectId).triggeredAbility ==
  some (.onAttackFerociousGainLife 2)
#guard (wargFerociousDeclared.object! wargFerociousDeclared.stack.back!.objectId).sourceId ==
  some (namedPermanent wargFerociousDeclared "Ravening Warg").id
#guard wargFerociousDeclared.log.any (fun s => mentions s "attack trigger is put on the stack")
#guard wargFerociousDeclared.hasPriority ⟨0⟩
#guard (namedPermanent wargFerociousDeclared "Ravening Warg").status.attacking
#guard !(namedPermanent wargFerociousDeclared "Rumbling Baloth").status.attacking

def wargFerociousResolved : Game := passBoth wargFerociousDeclared

#guard wargFerociousResolved.stack.isEmpty
#guard (wargFerociousResolved.player ⟨0⟩).life == 22
#guard wargFerociousResolved.log.any (fun s => mentions s "Chandra gains 2 life (22 life)")
#guard wargFerociousResolved.battlefield.any (fun o => o.name == "Ravening Warg")

/-- The 4-power creature need not attack; another creature attacking without the
Warg does not trigger Ferocious. -/
def balothAttacksWhileWargIdle : Game :=
  let g := passBoth (skipTo wargAndBaloth .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Rumbling Baloth").id])

#guard balothAttacksWhileWargIdle.stack.isEmpty
#guard !balothAttacksWhileWargIdle.log.any (fun s => mentions s "attack trigger")
#guard (namedPermanent balothAttacksWhileWargIdle "Rumbling Baloth").status.attacking
#guard !(namedPermanent balothAttacksWhileWargIdle "Ravening Warg").status.attacking

/-- Ferocious is not rechecked on resolution (CR 603.4). -/
def wargFerociousBalothGone : Game :=
  let id := (namedPermanent wargFerociousDeclared "Rumbling Baloth").id
  let (g, _) := wargFerociousDeclared.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard (wargFerociousBalothGone.player ⟨0⟩).life == 22
#guard !(wargFerociousBalothGone.battlefield.any (fun o => o.name == "Rumbling Baloth"))
#guard wargFerociousBalothGone.log.any (fun s => mentions s "Chandra gains 2 life (22 life)")

/-- The trigger still gains life if Ravening Warg has left (CR 113.7a). -/
def wargFerociousSourceGone : Game :=
  let id := (namedPermanent wargFerociousDeclared "Ravening Warg").id
  let (g, _) := wargFerociousDeclared.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard (wargFerociousSourceGone.player ⟨0⟩).life == 22
#guard !(wargFerociousSourceGone.battlefield.any (fun o => o.name == "Ravening Warg"))
#guard wargFerociousSourceGone.log.any (fun s => mentions s "Chandra gains 2 life (22 life)")

/-- Ravening Warg itself at power 4 or greater also enables Ferocious. -/
def wargPumpedToFive : Game :=
  let o := namedPermanent withWarg "Ravening Warg"
  withWarg.setObject { o with status := { o.status with pump := (3, 3) } }

#guard wargPumpedToFive.power (namedPermanent wargPumpedToFive "Ravening Warg") == 5
#guard wargPumpedToFive.triggerConditionHolds ⟨0⟩ (.onAttackFerociousGainLife 2)

def wargPumpedAttackDeclared : Game :=
  let g := passBoth (skipTo wargPumpedToFive .beginningOfCombat 80)
  mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Ravening Warg").id])

#guard wargPumpedAttackDeclared.stack.size == 1
#guard (wargPumpedAttackDeclared.object! wargPumpedAttackDeclared.stack.back!.objectId).triggeredAbility ==
  some (.onAttackFerociousGainLife 2)

def wargPumpedAttackResolved : Game := passBoth wargPumpedAttackDeclared

#guard (wargPumpedAttackResolved.player ⟨0⟩).life == 22

/-- 2 deathtouch combat damage destroys a 3/3 (CR 704.5h); the Warg dies to 3. -/
def wargVsGiant : Game :=
  addPermanent withWarg hillGiant ⟨1⟩ ⟨1⟩

def wargVsGiantAfterDamage : Game :=
  let g := passBoth (skipTo wargVsGiant .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Ravening Warg").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Hill Giant").id,
    (namedPermanent g "Ravening Warg").id)])
  passBoth g

#guard !(wargVsGiantAfterDamage.battlefield.any (fun o => o.name == "Hill Giant"))
#guard !(wargVsGiantAfterDamage.battlefield.any (fun o => o.name == "Ravening Warg"))
#guard wargVsGiantAfterDamage.objects.any (fun o =>
  o.name == "Hill Giant" && o.zone == .graveyard ⟨1⟩)
#guard wargVsGiantAfterDamage.objects.any (fun o =>
  o.name == "Ravening Warg" && o.zone == .graveyard ⟨0⟩)
#guard wargVsGiantAfterDamage.log.any (fun s =>
  mentions s "Ravening Warg deals 2 combat damage to Hill Giant")
#guard wargVsGiantAfterDamage.log.any (fun s => mentions s "Hill Giant dies from deathtouch")
#guard wargVsGiantAfterDamage.log.any (fun s =>
  mentions s "Ravening Warg dies from lethal damage")

/-- Without deathtouch, 2 damage does not kill a 3/3. -/
def ogreVsGiantAfterDamage : Game :=
  let g := addPermanent (addPermanent started grayOgre ⟨0⟩ ⟨0⟩) hillGiant ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Hill Giant").id,
    (namedPermanent g "Gray Ogre").id)])
  passBoth g

#guard ogreVsGiantAfterDamage.battlefield.any (fun o => o.name == "Hill Giant")
#guard !(ogreVsGiantAfterDamage.battlefield.any (fun o => o.name == "Gray Ogre"))
#guard (namedPermanent ogreVsGiantAfterDamage "Hill Giant").status.damage == 2
#guard !ogreVsGiantAfterDamage.log.any (fun s => mentions s "dies from deathtouch")

/-- Indestructible ignores deathtouch (CR 702.12b / 704.5h); the flag clears. -/
def wargVsIndestructibleFlyer : Game :=
  addPermanent withWarg indestructibleFlyer ⟨1⟩ ⟨1⟩

def wargVsIndestructibleAfterDamage : Game :=
  let g := passBoth (skipTo wargVsIndestructibleFlyer .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Ravening Warg").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Indestructible Flyer").id,
    (namedPermanent g "Ravening Warg").id)])
  passBoth g

#guard wargVsIndestructibleAfterDamage.battlefield.any (fun o =>
  o.name == "Indestructible Flyer")
#guard !(wargVsIndestructibleAfterDamage.battlefield.any (fun o =>
  o.name == "Ravening Warg"))
#guard (namedPermanent wargVsIndestructibleAfterDamage "Indestructible Flyer").status.damage == 2
#guard !(namedPermanent wargVsIndestructibleAfterDamage "Indestructible Flyer").status.dealtDeathtouch
#guard !wargVsIndestructibleAfterDamage.log.any (fun s =>
  mentions s "Indestructible Flyer dies from deathtouch")

/-- Deathtouch plus trample: 1 damage is lethal, so leftover tramples (CR 702.2c). -/
def deathtouchTrampler : CardDef :=
  creature "Deathtouch Trampler" ManaCost.empty #[] 2 2
    (keywords := Keyword.deathtouch.merge Keyword.trample)

def tramplerVsBalothAfterDamage : Game :=
  let g := addPermanent started deathtouchTrampler ⟨0⟩ ⟨0⟩
  let g := addPermanent g rumblingBaloth ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Deathtouch Trampler").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Rumbling Baloth").id,
    (namedPermanent g "Deathtouch Trampler").id)])
  passBoth g

#guard tramplerVsBalothAfterDamage.log.any (fun s =>
  mentions s "Deathtouch Trampler deals 1 combat damage to Rumbling Baloth")
#guard tramplerVsBalothAfterDamage.log.any (fun s =>
  mentions s "Deathtouch Trampler tramples for 1 to Nissa")
#guard (tramplerVsBalothAfterDamage.player ⟨1⟩).life == 19
#guard !(tramplerVsBalothAfterDamage.battlefield.any (fun o => o.name == "Rumbling Baloth"))
#guard tramplerVsBalothAfterDamage.log.any (fun s =>
  mentions s "Rumbling Baloth dies from deathtouch")

/-- Quarrel from Ravening Warg applies deathtouch to the damage it deals. -/
def quarrelWargVsGiant : Game :=
  let g := addPermanent afterDraw raveningWarg ⟨0⟩ ⟨0⟩
  let g := addPermanent g hillGiant ⟨1⟩ ⟨1⟩
  withGreenMana (addToHand g quarrel ⟨0⟩) ⟨0⟩ 2

def resolvedQuarrelWarg : Game :=
  let g := mustApply quarrelWargVsGiant ⟨0⟩
    (.cast (handCardNamed quarrelWargVsGiant ⟨0⟩ "Quarrel").id)
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Ravening Warg").id))
  let g := mustApply g ⟨0⟩
    (.target (Target.permanent (namedPermanent g "Hill Giant").id))
  passBoth (mustApply g ⟨0⟩ .pay)

#guard resolvedQuarrelWarg.battlefield.any (fun o => o.name == "Ravening Warg")
#guard !(resolvedQuarrelWarg.battlefield.any (fun o => o.name == "Hill Giant"))
#guard resolvedQuarrelWarg.log.any (fun s =>
  mentions s "Ravening Warg deals 2 damage to Hill Giant")
#guard resolvedQuarrelWarg.log.any (fun s => mentions s "Hill Giant dies from deathtouch")

/- Night's Whisper: you draw two cards and lose 2 life (CR 121 / 118.3a). -/

#guard nightsWhisper.isSorcery
#guard nightsWhisper.hasSorcerySpeed
#guard !nightsWhisper.hasInstantSpeed
#guard nightsWhisper.spellEffect == some (.drawAndLoseLife 2 2)
#guard nightsWhisper.hasCastKind .draw
#guard !nightsWhisper.requiresTarget
#guard mentions nightsWhisper.summary "draw two cards"
#guard mentions nightsWhisper.summary "lose 2 life"

-- Direct resolution draws that many cards and loses that much life.
#guard
  let g := addToLibraryTop (addToLibraryTop afterDraw forest ⟨0⟩) swamp ⟨0⟩
  let beforeHand := (g.player ⟨0⟩).hand.size
  let g := g.applyEffect ⟨0⟩ (.drawAndLoseLife 2 2) #[]
  (g.player ⟨0⟩).hand.size == beforeHand + 2 &&
    (g.player ⟨0⟩).life == 18 &&
    (g.handObjects ⟨0⟩).any (fun o => o.name == "Swamp") &&
    (g.handObjects ⟨0⟩).any (fun o => o.name == "Forest") &&
    g.log.any (fun s => mentions s "draws Swamp") &&
    g.log.any (fun s => mentions s "draws Forest") &&
    g.log.any (fun s => mentions s "loses 2 life (18 life)") &&
    !g.log.any (fun s => mentions s "is dealt 2 damage")

-- Losing 0 life does nothing (CR 118.9). Drawing 0 cards is a no-op.
#guard
  let g := afterDraw.applyEffect ⟨0⟩ (.drawAndLoseLife 0 0) #[]
  (g.player ⟨0⟩).life == 20 &&
    (g.player ⟨0⟩).hand.size == (afterDraw.player ⟨0⟩).hand.size &&
    !g.log.any (fun s => mentions s "loses 0 life")

/-- Night's Whisper in hand with enough black mana. -/
def nightsWhisperSetup : Game :=
  let g := afterDraw.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })
  withBlackMana (addToHand g nightsWhisper ⟨0⟩) ⟨0⟩ 2

#guard nightsWhisperSetup.canCast ⟨0⟩
  (handCardNamed nightsWhisperSetup ⟨0⟩ "Night's Whisper")
#guard nightsWhisperSetup.asSorcery? ⟨0⟩

-- Sorcery speed: illegal in the end step.
#guard
  let g := afterDraw.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })
  let g := withBlackMana (addToHand g nightsWhisper ⟨0⟩) ⟨0⟩ 2
  let g := skipTo g .end 80
  g.step == .end && !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Night's Whisper")

def proposedNightsWhisper : Game :=
  mustApply nightsWhisperSetup ⟨0⟩
    (.cast (handCardNamed nightsWhisperSetup ⟨0⟩ "Night's Whisper").id)

#guard proposedNightsWhisper.pending == .activateManaAbilities ⟨0⟩
#guard proposedNightsWhisper.log.any (fun s => mentions s "begins casting Night's Whisper")
#guard proposedNightsWhisper.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")
#guard !proposedNightsWhisper.log.any (fun s => mentions s "must choose a target")

def paidNightsWhisper : Game := mustApply proposedNightsWhisper ⟨0⟩ .pay

#guard paidNightsWhisper.hasPriority ⟨0⟩
#guard paidNightsWhisper.stack.size == 1
#guard (paidNightsWhisper.object! paidNightsWhisper.stack.back!.objectId).name ==
  "Night's Whisper"
#guard paidNightsWhisper.log.any (fun s => mentions s "casts Night's Whisper")

/-- Known library: Swamp then Forest are drawn on resolution (CR 121). -/
def nightsWhisperKnownLib : Game :=
  addToLibraryTop (addToLibraryTop paidNightsWhisper forest ⟨0⟩) swamp ⟨0⟩

def resolvedNightsWhisper : Game := passBoth nightsWhisperKnownLib

#guard resolvedNightsWhisper.stack.isEmpty
#guard resolvedNightsWhisper.hasPriority ⟨0⟩
#guard (resolvedNightsWhisper.player ⟨0⟩).hand.size ==
  (nightsWhisperKnownLib.player ⟨0⟩).hand.size + 2
#guard (resolvedNightsWhisper.handObjects ⟨0⟩).any (fun o => o.name == "Swamp")
#guard (resolvedNightsWhisper.handObjects ⟨0⟩).any (fun o => o.name == "Forest")
#guard (resolvedNightsWhisper.player ⟨0⟩).life == 18
#guard (resolvedNightsWhisper.player ⟨0⟩).graveyard.any (fun id =>
  (resolvedNightsWhisper.object! id).name == "Night's Whisper")
#guard resolvedNightsWhisper.log.any (fun s => mentions s "draws Swamp")
#guard resolvedNightsWhisper.log.any (fun s => mentions s "draws Forest")
#guard resolvedNightsWhisper.log.any (fun s => mentions s "loses 2 life (18 life)")
#guard !resolvedNightsWhisper.log.any (fun s => mentions s "is dealt 2 damage")

/-- Drawing from an empty library is a state-based loss (CR 704.5b / 121.4). -/
def nightsWhisperEmptyLib : Game :=
  let g := paidNightsWhisper.modifyPlayer ⟨0⟩ (fun pl => { pl with library := #[] })
  passBoth g

#guard nightsWhisperEmptyLib.over
#guard nightsWhisperEmptyLib.result == some (.won ⟨1⟩)
#guard (nightsWhisperEmptyLib.player ⟨0⟩).lost
#guard nightsWhisperEmptyLib.log.any (fun s => mentions s "tries to draw from an empty library")
#guard nightsWhisperEmptyLib.log.any (fun s => mentions s "loses the game (drew from empty library)")

/-- Losing the last 2 life ends the game (CR 704.5a). The spell is still legal. -/
def nightsWhisperPaysLastLife : Game :=
  let g := paidNightsWhisper.modifyPlayer ⟨0⟩ (fun pl => { pl with life := 2 })
  passBoth g

#guard (nightsWhisperPaysLastLife.player ⟨0⟩).life == 0
#guard nightsWhisperPaysLastLife.over
#guard nightsWhisperPaysLastLife.result == some (.won ⟨1⟩)
#guard nightsWhisperPaysLastLife.log.any (fun s => mentions s "loses 2 life (0 life)")
#guard nightsWhisperPaysLastLife.log.any (fun s => mentions s "loses the game (life total 0)")

/-- The agent casts Night's Whisper when that is the playable spell. -/
def agentNightsWhisperOnly : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  withBlackMana (addToHand g nightsWhisper ⟨0⟩) ⟨0⟩ 2

#guard
  match Agent.choose agentNightsWhisperOnly ⟨0⟩ with
  | some (.cast id) => (agentNightsWhisperOnly.object! id).name == "Night's Whisper"
  | _ => false

-- The heuristic will not lose the last 2 life.
#guard
  let g := agentNightsWhisperOnly.modifyPlayer ⟨0⟩ (fun pl => { pl with life := 2 })
  match Agent.choose g ⟨0⟩ with
  | some (.cast _) => false
  | _ => true

-- The heuristic will not draw into an empty library.
#guard
  let g := agentNightsWhisperOnly.modifyPlayer ⟨0⟩ (fun pl => { pl with library := #[] })
  match Agent.choose g ⟨0⟩ with
  | some (.cast _) => false
  | _ => true

-- The heuristic still casts at 3 life (survives at 1).
#guard
  let g := agentNightsWhisperOnly.modifyPlayer ⟨0⟩ (fun pl => { pl with life := 3 })
  match Agent.choose g ⟨0⟩ with
  | some (.cast id) => (g.object! id).name == "Night's Whisper"
  | _ => false

-- The heuristic still attacks with Ravening Warg.
#guard
  let g := passBoth (skipTo wargAndBaloth .beginningOfCombat 80)
  match Agent.choose g ⟨0⟩ with
  | some (.declareAttackers ids) =>
    ids.contains (namedPermanent g "Ravening Warg").id
  | _ => false


/- Black Hobbit Welcome Deck: structured abilities for each remaining card. -/

/-- Empty `p`'s hand so injected spells are the only playable cards. -/
def emptyHand (g : Game) (p : PlayerId) : Game :=
  g.modifyPlayer p (fun pl => { pl with hand := #[] })

def readyMain (g : Game) : Game :=
  g.modifyPlayer ⟨0⟩ (fun pl => { pl with landsPlayedThisTurn := 1 })

/-- Front Porch Sentries: dies, target opposing creature gets -1 / -1. -/
def sentriesDied : Game :=
  let g := addPermanent afterDraw frontPorchSentries ⟨0⟩ ⟨0⟩
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
  let g := addPermanent afterDraw frontPorchSentries ⟨0⟩ ⟨0⟩
  let (g, _) := g.move (namedPermanent g "Front Porch Sentries").id (.graveyard ⟨0⟩) none
  let g := g.receivePriority ⟨0⟩
  g.stack.isEmpty && g.log.any (fun s => mentions s "no legal target")

/-- Great Fierce Bee: another creature dying scries 1. -/
def beeOtherDied : Game :=
  let g := addPermanent afterDraw greatFierceBee ⟨0⟩ ⟨0⟩
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
  let g := addPermanent afterDraw greatFierceBee ⟨0⟩ ⟨0⟩
  let (g, _) := g.move (namedPermanent g "Great Fierce Bee").id (.graveyard ⟨0⟩) none
  let g := g.receivePriority ⟨0⟩
  g.stack.isEmpty && g.creatureDiedThisTurn

#guard
  let g := addPermanent afterDraw greatFierceBee ⟨0⟩ ⟨0⟩
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
  withBlackMana (addToHand g stirUpTrouble ⟨0⟩) ⟨0⟩ 1

#guard stirReady.canCast ⟨0⟩ (handCardNamed stirReady ⟨0⟩ "Stir Up Trouble")
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := readyMain (emptyHand g ⟨0⟩)
  let g := withBlackMana (addToHand g stirUpTrouble ⟨0⟩) ⟨0⟩ 5
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
  withBlackMana (addToHand g stirUpTrouble ⟨0⟩) ⟨0⟩ 5

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
  addPermanent hauntInGy gollumSilentSlinker ⟨0⟩ ⟨0⟩

#guard hauntInGyWithLegend.canActivate ⟨0⟩
  (namedGraveyardCard hauntInGyWithLegend ⟨0⟩ "Haunt of the Dead Marshes") hauntAbility
#guard
  let g := addPermanent hauntInGy hauntOfTheDeadMarshes ⟨0⟩ ⟨0⟩
  let g := addPermanent g gollumSilentSlinker ⟨0⟩ ⟨0⟩
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
  let g := addPermanent afterDraw gollumSilentSlinker ⟨0⟩ ⟨0⟩
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
  withBlackMana (addToHand g bilbosDeadlySlice ⟨0⟩) ⟨0⟩ 3

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
  withBlackMana (addToHand g dreadedBatCloud ⟨0⟩) ⟨0⟩ 5

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
  gollumTheAbandoned.activatedAbilities[0]!

#guard
  let g := addPermanent afterDraw gollumTheAbandoned ⟨1⟩ ⟨1⟩
  !g.mayDeclareAsBlocker (namedPermanent g "Gollum the Abandoned")

#guard
  let g := addPermanent afterDraw gollumTheAbandoned ⟨1⟩ ⟨1⟩
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
  withBlackMana (addToHand g gollumTheAbandoned ⟨0⟩) ⟨0⟩ 2

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
  let g := addToGraveyard afterDraw gollumTheAbandoned ⟨0⟩
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
  withBlackMana (addToHand g gnashingOfTeeth ⟨0⟩) ⟨0⟩ 3

#guard gnashingOfTeeth.isModal
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
  withBlackMana (addToHand g reverentHowl ⟨0⟩) ⟨0⟩ 3

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
  withBlackMana (addToHand g stonyVoicedGoblins ⟨0⟩) ⟨0⟩ 2

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


/- Typecycling: Oliphaunt Mountaincycling and Troll of Khazad-dûm Swampcycling
(CR 702.29). -/

def oliphauntCycleAbility : ActivatedAbility :=
  oliphaunt.activatedAbilities[0]!

def trollCycleAbility : ActivatedAbility :=
  trollOfKhazadDum.activatedAbilities[0]!

/-- Nonbasic land with the Mountain type; Mountaincycling can find it (CR 305.7). -/
def stompingGround : CardDef :=
  land "Stomping Ground" "" (subtypes := #["Mountain", "Forest"])

#guard isLandTypeCard stompingGround "Mountain"
#guard !isBasicLandCard stompingGround

/-- Isolated library so the search finds a known card. -/
def withOnlyLibrary (g : Game) (p : PlayerId) (cards : Array CardDef) : Game :=
  let g := g.modifyPlayer p (fun pl => { pl with library := #[] })
  cards.foldl (fun g c => addToLibraryTop g c p) g

def oliphauntCycleReady : Game :=
  let g := readyMain (emptyHand afterDraw ⟨0⟩)
  let g := withOnlyLibrary g ⟨0⟩ #[mountain]
  withRedMana (addToHand g oliphaunt ⟨0⟩) ⟨0⟩ 1

#guard oliphauntCycleReady.canActivate ⟨0⟩
  (handCardNamed oliphauntCycleReady ⟨0⟩ "Oliphaunt") oliphauntCycleAbility
#guard !(oliphauntCycleReady.availableMana ⟨0⟩).canPay oliphaunt.manaCost
#guard
  let g := addPermanent afterDraw oliphaunt ⟨0⟩ ⟨0⟩
  !(g.canActivate ⟨0⟩ (namedPermanent g "Oliphaunt") oliphauntCycleAbility)
#guard
  let g := readyMain (addToGraveyard afterDraw oliphaunt ⟨0⟩)
  let g := withRedMana g ⟨0⟩ 1
  !(g.canActivate ⟨0⟩ (namedGraveyardCard g ⟨0⟩ "Oliphaunt") oliphauntCycleAbility)
#guard
  let g := addToHand afterDraw oliphaunt ⟨1⟩
  !(g.canActivate ⟨0⟩ (handCardNamed g ⟨1⟩ "Oliphaunt") oliphauntCycleAbility)

def oliphauntCycled : Game :=
  let g := oliphauntCycleReady
  let src := handCardNamed g ⟨0⟩ "Oliphaunt"
  let g := mustApply g ⟨0⟩ (.activate src.id 0)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard (oliphauntCycled.handObjects ⟨0⟩).any (fun o => o.name == "Mountain")
#guard (oliphauntCycled.player ⟨0⟩).graveyard.any (fun id =>
  (oliphauntCycled.object! id).name == "Oliphaunt")
#guard !(oliphauntCycled.handObjects ⟨0⟩).any (fun o => o.name == "Oliphaunt")
#guard oliphauntCycled.log.any (fun s => mentions s "discards Oliphaunt")
#guard oliphauntCycled.log.any (fun s =>
  mentions s "reveals Mountain and puts it into their hand")
#guard oliphauntCycled.log.any (fun s => mentions s "shuffles their library")
#guard oliphauntCycled.stack.isEmpty

#guard
  match Agent.choose oliphauntCycleReady ⟨0⟩ with
  | some (.activate id 0) =>
    (oliphauntCycleReady.object! id).name == "Oliphaunt"
  | _ => false

/-- Enough mana to cast Oliphaunt: the heuristic casts instead of cycling. -/
def oliphauntCastReady : Game :=
  let g := readyMain (emptyHand afterDraw ⟨0⟩)
  withRedMana (addToHand g oliphaunt ⟨0⟩) ⟨0⟩ 6

#guard oliphauntCastReady.canCast ⟨0⟩
  (handCardNamed oliphauntCastReady ⟨0⟩ "Oliphaunt")
#guard
  match Agent.choose oliphauntCastReady ⟨0⟩ with
  | some (.cast id) => (oliphauntCastReady.object! id).name == "Oliphaunt"
  | _ => false

/-- No Mountain in the library: still discard and shuffle. -/
def oliphauntCycleMiss : Game :=
  let g := readyMain (emptyHand afterDraw ⟨0⟩)
  let g := withOnlyLibrary g ⟨0⟩ #[forest]
  let g := withRedMana (addToHand g oliphaunt ⟨0⟩) ⟨0⟩ 1
  let src := handCardNamed g ⟨0⟩ "Oliphaunt"
  let g := mustApply g ⟨0⟩ (.activate src.id 0)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard oliphauntCycleMiss.log.any (fun s => mentions s "finds no Mountain card")
#guard oliphauntCycleMiss.log.any (fun s => mentions s "shuffles their library")
#guard (oliphauntCycleMiss.player ⟨0⟩).graveyard.any (fun id =>
  (oliphauntCycleMiss.object! id).name == "Oliphaunt")
#guard !(oliphauntCycleMiss.handObjects ⟨0⟩).any (fun o => o.name == "Mountain")

/-- A nonbasic Mountain is a legal find (CR 305.7). -/
def oliphauntCycleNonbasic : Game :=
  let g := readyMain (emptyHand afterDraw ⟨0⟩)
  let g := withOnlyLibrary g ⟨0⟩ #[stompingGround]
  let g := withRedMana (addToHand g oliphaunt ⟨0⟩) ⟨0⟩ 1
  let src := handCardNamed g ⟨0⟩ "Oliphaunt"
  let g := mustApply g ⟨0⟩ (.activate src.id 0)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard (oliphauntCycleNonbasic.handObjects ⟨0⟩).any (fun o =>
  o.name == "Stomping Ground")
#guard oliphauntCycleNonbasic.log.any (fun s =>
  mentions s "reveals Stomping Ground and puts it into their hand")

/-- Typecycling is instant-speed (CR 702.29 / 117.1). -/
def oliphauntCycleAtEnd : Game :=
  let g := applyIdle (passBoth (skipTo afterDraw .end 80))
  let g := emptyHand g ⟨0⟩
  let g := withOnlyLibrary g ⟨0⟩ #[mountain]
  withRedMana (addToHand g oliphaunt ⟨0⟩) ⟨0⟩ 1

#guard !oliphauntCycleAtEnd.asSorcery? ⟨0⟩
#guard oliphauntCycleAtEnd.canActivate ⟨0⟩
  (handCardNamed oliphauntCycleAtEnd ⟨0⟩ "Oliphaunt") oliphauntCycleAbility
#guard !oliphauntCycleAtEnd.canCast ⟨0⟩
  (handCardNamed oliphauntCycleAtEnd ⟨0⟩ "Oliphaunt")

def trollCycleReady : Game :=
  let g := readyMain (emptyHand afterDraw ⟨0⟩)
  let g := withOnlyLibrary g ⟨0⟩ #[swamp]
  withBlackMana (addToHand g trollOfKhazadDum ⟨0⟩) ⟨0⟩ 1

#guard trollCycleReady.canActivate ⟨0⟩
  (handCardNamed trollCycleReady ⟨0⟩ "Troll of Khazad-dûm") trollCycleAbility
#guard !(trollCycleReady.availableMana ⟨0⟩).canPay trollOfKhazadDum.manaCost
#guard
  let g := addPermanent afterDraw trollOfKhazadDum ⟨0⟩ ⟨0⟩
  !(g.canActivate ⟨0⟩ (namedPermanent g "Troll of Khazad-dûm") trollCycleAbility)

def trollCycled : Game :=
  let g := trollCycleReady
  let src := handCardNamed g ⟨0⟩ "Troll of Khazad-dûm"
  let g := mustApply g ⟨0⟩ (.activate src.id 0)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard (trollCycled.handObjects ⟨0⟩).any (fun o => o.name == "Swamp")
#guard (trollCycled.player ⟨0⟩).graveyard.any (fun id =>
  (trollCycled.object! id).name == "Troll of Khazad-dûm")
#guard trollCycled.log.any (fun s => mentions s "discards Troll of Khazad-dûm")
#guard trollCycled.log.any (fun s =>
  mentions s "reveals Swamp and puts it into their hand")
#guard trollCycled.log.any (fun s => mentions s "shuffles their library")
#guard
  match Agent.choose trollCycleReady ⟨0⟩ with
  | some (.activate id 0) =>
    (trollCycleReady.object! id).name == "Troll of Khazad-dûm"
  | _ => false

/- Gollum, Silent Slinker: menace (CR 702.111 / 509.1c). -/

#guard gollumSilentSlinker.keywords.menace
#guard gollumSilentSlinker.power == some 4
#guard gollumSilentSlinker.toughness == some 3
#guard withGollum.hasMenace (namedPermanent withGollum "Gollum, Silent Slinker")
#guard (withGollum.effectiveKeywords (namedPermanent withGollum "Gollum, Silent Slinker")).menace
#guard withGollum.legalBlockerCount
  (namedPermanent withGollum "Gollum, Silent Slinker") 0
#guard !withGollum.legalBlockerCount
  (namedPermanent withGollum "Gollum, Silent Slinker") 1
#guard withGollum.legalBlockerCount
  (namedPermanent withGollum "Gollum, Silent Slinker") 2
#guard withGollum.legalBlockerCount
  (namedPermanent withGollum "Gollum, Silent Slinker") 3

/-- Chandra's Gollum attacks; Nissa has one Grizzly Bears. Pairwise blocking
is legal, but a one-blocker declaration is not. -/
def gollumVsOneBear : Game :=
  addPermanent (addPermanent started gollumSilentSlinker ⟨0⟩ ⟨0⟩) grizzlyBears ⟨1⟩ ⟨1⟩

def gollumVsOneBearReadyToBlock : Game :=
  let g := passBoth (skipTo gollumVsOneBear .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gollum, Silent Slinker").id])
  passBoth g

#guard gollumVsOneBearReadyToBlock.pending == .declareBlockers
#guard
  let g := gollumVsOneBearReadyToBlock
  g.canBlock (namedPermanent g "Grizzly Bears")
    (namedPermanent g "Gollum, Silent Slinker")
#guard
  match gollumVsOneBearReadyToBlock.apply ⟨1⟩ (.declareBlockers #[(
    (namedPermanent gollumVsOneBearReadyToBlock "Grizzly Bears").id,
    (namedPermanent gollumVsOneBearReadyToBlock "Gollum, Silent Slinker").id)]) with
  | .error msg => mentions msg "can't be blocked except by two or more creatures"
  | .ok _ => false

def gollumUnblockedDamage : Game :=
  passBoth (mustApply gollumVsOneBearReadyToBlock ⟨1⟩ (.declareBlockers #[]))

#guard (gollumUnblockedDamage.player ⟨1⟩).life == 16
#guard gollumUnblockedDamage.log.any (fun s =>
  mentions s "Gollum, Silent Slinker deals 4 combat damage to Nissa")
#guard !gollumUnblockedDamage.log.any (fun s =>
  mentions s "Grizzly Bears blocks Gollum, Silent Slinker")

/-- Two Bears can block Gollum. -/
def gollumVsTwoBears : Game :=
  addPermanent gollumVsOneBear grizzlyBears ⟨1⟩ ⟨1⟩

def gollumVsTwoBearsReadyToBlock : Game :=
  let g := passBoth (skipTo gollumVsTwoBears .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gollum, Silent Slinker").id])
  passBoth g

#guard
  let g := gollumVsTwoBearsReadyToBlock
  let bears := g.battlefield.filter (fun o => o.name == "Grizzly Bears")
  g.canBlock bears[0]! (namedPermanent g "Gollum, Silent Slinker") &&
    g.canBlock bears[1]! (namedPermanent g "Gollum, Silent Slinker")

def twoBearsBlockGollum : Game :=
  let g := gollumVsTwoBearsReadyToBlock
  let gollum := namedPermanent g "Gollum, Silent Slinker"
  let bears := g.battlefield.filter (fun o => o.name == "Grizzly Bears")
  mustApply g ⟨1⟩ (.declareBlockers #[(bears[0]!.id, gollum.id), (bears[1]!.id, gollum.id)])

#guard (namedPermanent twoBearsBlockGollum "Gollum, Silent Slinker").status.blocked
#guard (twoBearsBlockGollum.battlefield.filter (fun o =>
  o.name == "Grizzly Bears" && o.status.blocking ==
    #[(namedPermanent twoBearsBlockGollum "Gollum, Silent Slinker").id])).size == 2
#guard twoBearsBlockGollum.log.any (fun s =>
  mentions s "Grizzly Bears blocks Gollum, Silent Slinker")
#guard twoBearsBlockGollum.legalBlockerCount
  (namedPermanent twoBearsBlockGollum "Gollum, Silent Slinker")
  (twoBearsBlockGollum.blockersOf
    (namedPermanent twoBearsBlockGollum "Gollum, Silent Slinker").id).size

/-- Combat damage goes to the blockers, not the defending player. -/
def afterGollumBlockedDamage : Game :=
  let g := passBoth twoBearsBlockGollum
  mustApply g ⟨0⟩ (.assignCombatDamage #[])

#guard (afterGollumBlockedDamage.player ⟨1⟩).life == 20
#guard afterGollumBlockedDamage.log.any (fun s =>
  mentions s "Gollum, Silent Slinker deals 4 combat damage to Grizzly Bears")
#guard !afterGollumBlockedDamage.log.any (fun s =>
  mentions s "deals 4 combat damage to Nissa")

/-- Gollum and Gray Ogre attack; one Bear blocks the Ogre rather than
illegally solo-blocking Gollum. -/
def gollumAndOgreVsOneBear : Game :=
  addPermanent gollumVsOneBear grayOgre ⟨0⟩ ⟨0⟩

def gollumAndOgreVsOneBearReadyToBlock : Game :=
  let g := passBoth (skipTo gollumAndOgreVsOneBear .beginningOfCombat 80)
  let gollum := namedPermanent g "Gollum, Silent Slinker"
  let ogre := namedPermanent g "Gray Ogre"
  let g := mustApply g ⟨0⟩ (.declareAttackers #[gollum.id, ogre.id])
  passBoth g

/-- Until-end-of-turn menace uses the same declaration restriction. -/
def ogreGrantedMenaceReadyToBlock : Game :=
  let g := readyToDeclareBlockers
  let ogre := namedPermanent g "Gray Ogre"
  g.setObject { ogre with status := ogre.status.grantUntilEot Keyword.menace }

#guard ogreGrantedMenaceReadyToBlock.hasMenace
  (namedPermanent ogreGrantedMenaceReadyToBlock "Gray Ogre")
#guard
  match ogreGrantedMenaceReadyToBlock.apply ⟨1⟩ (.declareBlockers #[(
    (namedPermanent ogreGrantedMenaceReadyToBlock "Grizzly Bears").id,
    (namedPermanent ogreGrantedMenaceReadyToBlock "Gray Ogre").id)]) with
  | .error msg => mentions msg "can't be blocked except by two or more creatures"
  | .ok _ => false

/- Bilbo's Deadly Slice: destroy target creature (CR 701.8 / 701.7b / 608.2b). -/

#guard bilbosDeadlySlice.isInstant
#guard !bilbosDeadlySlice.hasSorcerySpeed
#guard bilbosDeadlySlice.hasInstantSpeed
#guard bilbosDeadlySlice.spellEffect == some .destroyCreature
#guard bilbosDeadlySlice.hasCastKind .destroyCreature
#guard bilbosDeadlySlice.requiresTarget
#guard mentions bilbosDeadlySlice.summary "Destroy target creature"

/-- Bilbo's Deadly Slice in hand, an opposing Grizzly Bears, enough mana. -/
def bilbosDeadlySliceSetup : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  withBlackMana (addToHand g bilbosDeadlySlice ⟨0⟩) ⟨0⟩ 3

#guard bilbosDeadlySliceSetup.canCast ⟨0⟩
  (handCardNamed bilbosDeadlySliceSetup ⟨0⟩ "Bilbo's Deadly Slice")
#guard
  (bilbosDeadlySliceSetup.legalTargets ⟨0⟩ .destroyCreature).contains
    (Target.permanent (namedPermanent bilbosDeadlySliceSetup "Grizzly Bears").id)

-- Cannot cast with no creature.
#guard
  let g := withBlackMana (addToHand afterDraw bilbosDeadlySlice ⟨0⟩) ⟨0⟩ 3
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Bilbo's Deadly Slice")
#guard
  let g := addPermanent afterDraw forest ⟨1⟩ ⟨1⟩
  let g := withBlackMana (addToHand g bilbosDeadlySlice ⟨0⟩) ⟨0⟩ 3
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Bilbo's Deadly Slice")
#guard
  let g := withBlackMana (addToHand afterDraw bilbosDeadlySlice ⟨0⟩) ⟨0⟩ 3
  match g.apply ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Bilbo's Deadly Slice").id) with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

-- Own creatures and non-flying creatures are legal; hexproof on an opponent's
-- creature is not (CR 702.11b).
#guard
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := withBlackMana (addToHand g bilbosDeadlySlice ⟨0⟩) ⟨0⟩ 3
  g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Bilbo's Deadly Slice") &&
    (g.legalTargets ⟨0⟩ .destroyCreature).contains
      (Target.permanent (namedPermanent g "Grizzly Bears").id)
#guard
  let g := addPermanent afterDraw velvetwingButterflies ⟨1⟩ ⟨1⟩
  let g := withBlackMana (addToHand g bilbosDeadlySlice ⟨0⟩) ⟨0⟩ 3
  (g.legalTargets ⟨0⟩ .destroyCreature).contains
    (Target.permanent (namedPermanent g "Velvetwing Butterflies").id)
#guard
  let g := addPermanent afterDraw hexproofFlyer ⟨1⟩ ⟨1⟩
  let g := withBlackMana (addToHand g bilbosDeadlySlice ⟨0⟩) ⟨0⟩ 3
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Bilbo's Deadly Slice")

def proposedBilbosDeadlySlice : Game :=
  mustApply bilbosDeadlySliceSetup ⟨0⟩
    (.cast (handCardNamed bilbosDeadlySliceSetup ⟨0⟩ "Bilbo's Deadly Slice").id)

#guard proposedBilbosDeadlySlice.pending == .chooseTargets ⟨0⟩
#guard proposedBilbosDeadlySlice.log.any (fun s =>
  mentions s "begins casting Bilbo's Deadly Slice")
#guard proposedBilbosDeadlySlice.log.any (fun s =>
  mentions s "must choose a target (CR 601.2c)")

-- Cannot target a player or a land.
#guard
  match proposedBilbosDeadlySlice.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false
#guard
  let g := addPermanent bilbosDeadlySliceSetup forest ⟨1⟩ ⟨1⟩
  let g := mustApply g ⟨0⟩
    (.cast (handCardNamed g ⟨0⟩ "Bilbo's Deadly Slice").id)
  match g.apply ⟨0⟩ (.target (Target.permanent (namedPermanent g "Forest").id)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

def targetedBilbosDeadlySlice : Game :=
  mustApply proposedBilbosDeadlySlice ⟨0⟩
    (.target (Target.permanent (namedPermanent proposedBilbosDeadlySlice
      "Grizzly Bears").id))

#guard targetedBilbosDeadlySlice.pending == .activateManaAbilities ⟨0⟩
#guard targetedBilbosDeadlySlice.stack.back!.targets ==
  #[Target.permanent (namedPermanent targetedBilbosDeadlySlice "Grizzly Bears").id]

#guard
  match Agent.choose proposedBilbosDeadlySlice ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (proposedBilbosDeadlySlice.object! tid).name == "Grizzly Bears"
  | _ => false

-- Prefer an opposing creature over your own (CR 601.2c heuristic).
#guard
  let g := addPermanent bilbosDeadlySliceSetup grayOgre ⟨0⟩ ⟨0⟩
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Bilbo's Deadly Slice").id)
  match Agent.choose g ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (g.object! tid).name == "Grizzly Bears"
  | _ => false

def paidBilbosDeadlySlice : Game := mustApply targetedBilbosDeadlySlice ⟨0⟩ .pay

#guard paidBilbosDeadlySlice.hasPriority ⟨0⟩
#guard paidBilbosDeadlySlice.stack.size == 1
#guard paidBilbosDeadlySlice.log.any (fun s => mentions s "casts Bilbo's Deadly Slice")

def resolvedBilbosDeadlySlice : Game := passBoth paidBilbosDeadlySlice

#guard resolvedBilbosDeadlySlice.stack.isEmpty
#guard !(resolvedBilbosDeadlySlice.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard resolvedBilbosDeadlySlice.objects.any (fun o =>
  o.name == "Grizzly Bears" && o.zone == .graveyard ⟨1⟩)
#guard resolvedBilbosDeadlySlice.log.any (fun s =>
  mentions s "Grizzly Bears is destroyed")
#guard (resolvedBilbosDeadlySlice.player ⟨0⟩).graveyard.any (fun id =>
  (resolvedBilbosDeadlySlice.object! id).name == "Bilbo's Deadly Slice")

-- If the target leaves before resolution, the spell does nothing (CR 608.2b).
def bilbosDeadlySliceTargetGone : Game :=
  let id := (namedPermanent paidBilbosDeadlySlice "Grizzly Bears").id
  let (g, _) := paidBilbosDeadlySlice.move id (.graveyard ⟨1⟩) none
  passBoth g

#guard bilbosDeadlySliceTargetGone.log.any (fun s => mentions s "no longer in play")
#guard !(bilbosDeadlySliceTargetGone.battlefield.any (fun o =>
  o.name == "Grizzly Bears"))

-- Destroy does nothing to an indestructible creature (CR 701.7b / 702.12b).
#guard
  let g := addPermanent afterDraw indestructibleBeast ⟨1⟩ ⟨1⟩
  let g := g.applyEffect ⟨0⟩ .destroyCreature
    #[Target.permanent (namedPermanent g "Indestructible Beast").id]
  g.battlefield.any (fun o => o.name == "Indestructible Beast") &&
    g.log.any (fun s => mentions s "is indestructible and isn't destroyed")

/-- The agent casts Bilbo's Deadly Slice when that is the playable spell. -/
def agentBilbosDeadlySliceOnly : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withBlackMana (addToHand g bilbosDeadlySlice ⟨0⟩) ⟨0⟩ 3

#guard
  match Agent.choose agentBilbosDeadlySliceOnly ⟨0⟩ with
  | some (.cast id) =>
    (agentBilbosDeadlySliceOnly.object! id).name == "Bilbo's Deadly Slice"
  | _ => false

end Mtg.Engine.Tests

