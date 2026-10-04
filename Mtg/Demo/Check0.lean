import Mtg.Demo
import Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Demo
open Mtg.Demo.Render

def parsedOneCombatTriple : Bool :=
  match parseCombatAssignments Tests.started ⟨0⟩ ["3", "#7", "2"] with
  | .ok asgns => asgns == #[{ source := ⟨3⟩, toCreatures := #[(⟨7⟩, 2)] }]
  | .error _ => false


def parsedTwoAmountsSameSource : Bool :=
  match parseCombatAssignments Tests.started ⟨0⟩ ["1", "2", "3", "1", "4", "0"] with
  | .ok asgns =>
    asgns == #[{ source := ⟨1⟩, toCreatures := #[(⟨2⟩, 3), (⟨4⟩, 0)] }]
  | .error _ => false


#guard demoFormat false == .limited

#guard
  match parsePlayerName demoSeats "Frodo" with
  | .error msg => msg == "No player named Frodo"
  | .ok _ => false


#guard assignDecider defaultDemoPlayers 1 none < 2


#guard humanChoosesFirst true true 1

#guard describeFirstChooser defaultDemoPlayers 1 false ==
  "Nissa will choose who takes the first turn (CR 103.1)."

#guard
  match parseFirstPlayer demoSeats ["nissa"] with
  | .ok 1 => true
  | _ => false


#guard
  match parseFirstPlayer demoSeats ["Chandra", "Nissa"] with
  | .error msg => msg == firstUsage demoSeats
  | .ok _ => false


#guard demoSeats[1]!.deck.any (fun c => c.name == "Elvish Archdruid")


#guard (seatsFromPlayers elspethJace)[1]!.deck.any (fun c => c.name == "Bilbo Baggins, Burglar")

#guard firstUsage (seatsFromPlayers elspethJaceLiliana) ==
  "usage: first <name> (Elspeth or Jace or Liliana)"

#guard duplicatePlayerName? #[
    { name := "Jace", deck := .welcome .blue },
    { name := "jace", deck := .welcome .white }] == some "Jace"


#guard
  match playersFromFlags #["Elspeth", "Jace"] #[.welcome .white] with
  | .error msg =>
    msg == "--name and --deck must be given the same number of times (got 2 names and 1 decks)"
  | .ok _ => false


#guard
  match Start.start (demoConfig 1 (some 0) elspethJaceLiliana) with
  | .error _ => false
  | .ok g =>
    match g.apply ⟨0⟩ .takeMulligan with
    | .error _ => false
    | .ok g =>
      match g.apply ⟨1⟩ .keep with
      | .error _ => false
      | .ok g =>
        match g.apply ⟨2⟩ .keep with
        | .error _ => false
        | .ok g =>
          g.pending == .declareMulligan ⟨0⟩ &&
          (g.player ⟨0⟩).hand.size == 7 &&
          (g.player ⟨0⟩).mulligansTaken == 1 &&
          g.countedMulligans ⟨0⟩ == 0 &&
          g.log.any (fun s => (s.splitOn "CR 103.5c").length > 1)


#guard ((helpInteractive false "Chandra").splitOn "Chandra can see").length > 1

#guard ((helpInteractive false).splitOn "scry top").length > 1

#guard ((helpInteractive false).splitOn "mode <n>").length > 1

#guard ((helpInteractive false).splitOn "CR 715.3").length > 1

#guard ((helpInteractive false).splitOn "CR 103.1").length > 1

#guard ((helpInteractive false).splitOn "stack <id>").length > 1

#guard ((helpInteractive false).splitOn "attach <id>").length > 1

#guard ((helpInteractive false).splitOn "Baron Strucker").length > 1

#guard ((helpInteractive false).splitOn "your turn").length > 1

#guard ((helpInteractive false).splitOn "attack step").length > 1

#guard ((helpInteractive false).splitOn "Each listed creature attacks that player").length > 1

#guard ((helpInteractive false).splitOn "CR 601.2b").length > 1

#guard (usage.splitOn "--check").length > 1

#guard (usage.splitOn "replays that file and appends").length > 1

#guard (usage.splitOn "do not interrupt a pending shortcut").length > 1

#guard (usage.splitOn "such as state and quit").length > 1

#guard (usage.splitOn "supported catalog").length > 1

#guard (usage.splitOn "--constructed").length > 1

#guard (usage.splitOn "white, blue, black, red, or green").length > 1

#guard (helpChooseFirst.splitOn "CR 103.1").length > 1

#guard (parseManaType? "12").isNone


#guard parseObjectId? "12" == some ⟨12⟩

#guard
  match parseObjectIds ["x"] attackUsage with
  | .error msg => msg == attackUsage
  | .ok _ => false

#guard
  let g := Tests.readyToDeclareAttackers
  match applyAttack g ⟨0⟩ ["Nissa"] with
  | .ok g' =>
    (Tests.namedPermanent g' "Grizzly Bears").status.attacking &&
    (Tests.namedPermanent g' "Grizzly Bears").status.attackingWhom == some ⟨1⟩ &&
    (Tests.namedPermanent g' "Gray Ogre").status.attackingWhom == some ⟨1⟩
  | .error _ => false


#guard
  match applyAttack Tests.readyToDeclareAttackers ⟨0⟩ ["nope"] with
  | .error msg => msg == attackUsage
  | .ok _ => false


#guard
  let g := Tests.threeTwoOgresReady
  let ogres := g.battlefield.filter (·.name == "Gray Ogre")
  match applyAttack g ⟨0⟩
      [toString ogres[0]!.id, "at", "Nissa", toString ogres[1]!.id, "at", "Liliana"] with
  | .ok g' =>
    let after := g'.battlefield.filter (·.name == "Gray Ogre")
    after[0]!.status.attackingWhom == some ⟨1⟩ &&
      after[1]!.status.attackingWhom == some ⟨2⟩
  | .error _ => false


#guard
  match parseBlockAssignments ["x", "1"] with
  | .error msg => msg == blockUsage
  | .ok _ => false


#guard
  match applyBlock Tests.readyToDeclareBlockers ⟨1⟩ ["99999", "1"] with
  | .error msg => msg == "no such object"
  | .ok _ => false


#guard
  let g := Tests.ogreVsCrusherReadyToBlock
  match applyBlock g ⟨1⟩ [
      toString (Tests.namedPermanent g "Olog-hai Crusher").id,
      toString (Tests.namedPermanent g "Gray Ogre").id] with
  | .error msg => Tests.mentions msg "cannot block"
  | .ok _ => false


#guard parsedOneCombatTriple


#guard parsedTwoAmountsSameSource


#guard
  match parseCombatAssignments Tests.started ⟨0⟩ ["1", "2"] with
  | .error msg => msg == assignUsage
  | .ok _ => false


#guard
  match parseCombatAssignments Tests.bearsBlockingTwoOgresReady ⟨1⟩
      ["3", "opponent", "2"] with
  | .error msg => msg == assignUsage
  | .ok _ => false


#guard
  let g := Tests.giantReadyToAssign
  let giant := Tests.namedPermanent g "Hill Giant"
  let g := g.setObject { giant with status := giant.status.grantUntilEot Keyword.trample }
  let giant := Tests.namedPermanent g "Hill Giant"
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  match applyAssign g ⟨0⟩
      [toString giant.id, toString elves[0]!.id, "1",
        toString giant.id, toString elves[1]!.id, "1",
        toString giant.id, "Nissa", "1"] with
  | .ok g' =>
    (g'.player ⟨1⟩).life == 19 &&
    (g'.battlefield.filter (fun o => o.name == "Llanowar Elves")).isEmpty &&
    g'.log.any (fun s => Tests.mentions s "tramples for 1 to Nissa")
  | .error _ => false


#guard
  match applyBottom Tests.afterChandraMulligan ⟨0⟩ ["nope"] with
  | .error msg => msg == bottomUsage
  | .ok _ => false


#guard
  match applyVisible ["on"] with
  | .ok (some true) => true
  | _ => false


#guard (humanView false).isNone

#guard (currentView Tests.nissaDraw false true).isNone

#guard
  match actingPlayer Tests.readyToDeclareBlockers with
  | .ok p => p == ⟨1⟩
  | .error _ => false


#guard
  match applyTap Tests.baubleReady ⟨0⟩ ["99999"] with
  | .error msg => msg == "no such object"
  | .ok _ => false


#guard
  let g := Tests.hiddenLairStuck
  let lair := Tests.namedPermanent g "Hidden Lair"
  match applyTap g ⟨0⟩ [toString lair.id, "U"] with
  | .error msg => Tests.mentions msg "cannot produce"
  | .ok _ => false


#guard
  let g := Tests.proposedBauble
  let lands := (g.permanentsOf ⟨0⟩).filter (·.printed.isLand)
  lands.size == 2 &&
  match applyTap g ⟨0⟩ [toString lands[0]!.id, toString lands[1]!.id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
    (g'.player ⟨0⟩).manaPool.canPay (ManaCost.ofGeneric 2) &&
    (g'.battlefield.filter (fun o => o.printed.isLand && o.status.tapped)).size == 2
  | .error _ => false


#guard
  match applyPlay Tests.afterDraw ⟨0⟩ ["1", "2"] with
  | .error msg => msg == playUsage
  | .ok _ => false


#guard
  match applyPayExtra Tests.stirChooseAdditional ⟨0⟩ ["extra"] with
  | .error msg => msg == payExtraUsage
  | .ok _ => false


#guard
  match applyActivate Tests.baubleReady ⟨0⟩ [] with
  | .error msg => msg == activateUsage
  | .ok _ => false


#guard
  match applyActivate Tests.baubleReady ⟨0⟩ ["1", "2", "3"] with
  | .error msg => msg == activateUsage
  | .ok _ => false


#guard
  let g := Tests.baubleReady
  let bauble := Tests.baubleSource g
  match applyActivate g ⟨0⟩ [toString bauble.id, "1"] with
  | .ok g' => g'.pending == .activateManaAbilities ⟨0⟩
  | .error _ => false


#guard
  let g := Tests.baubleReady
  let bauble := Tests.baubleSource g
  match applyActivate g ⟨0⟩ [s!"{bauble.id.raw}"] with
  | .ok g' => g'.stack.size == 1
  | .error _ => false


#guard
  match applySacrifice Tests.hunterReady ⟨0⟩ ["1", "2"] with
  | .error msg => msg == sacrificeUsage
  | .ok _ => false


#guard
  let g := Tests.paidClub
  let fodder := Tests.clubFodder g
  match applySacrifice g ⟨0⟩ [toString fodder.id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.log.any (fun s => Tests.mentions s "sacrifices Raging Goblin") &&
    g'.log.any (fun s => Tests.mentions s "casts Improvised Club")
  | .error _ => false


#guard
  match applyMode Tests.proposedCratermaker ⟨0⟩ ["0"] with
  | .error msg => msg == modeUsage
  | .ok _ => false


#guard
  match applyX Tests.proposedStature ⟨0⟩ [] with
  | .error msg => msg == xUsage
  | .ok _ => false


#guard
  match applyX Tests.afterDraw ⟨0⟩ ["3"] with
  | .error msg => Tests.mentions msg "Not time to choose X"
  | .ok _ => false


#guard
  match applyCast Tests.boltSetup ⟨0⟩ ["1", "2"] with
  | .error msg => msg == castUsage
  | .ok _ => false


#guard
  match applyCast Tests.giftSetup ⟨0⟩
      [toString (Tests.handCardNamed Tests.giftSetup ⟨0⟩ "Gift of Strands").id] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.stack.back!.targets.isEmpty &&
    g'.log.any (fun s => Tests.mentions s "begins casting Gift of Strands")
  | .error _ => false


#guard
  match applyCast Tests.bilbosDeadlySliceSetup ⟨0⟩
      [toString (Tests.handCardNamed Tests.bilbosDeadlySliceSetup ⟨0⟩
        "Bilbo's Deadly Slice").id] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.stack.back!.targets.isEmpty &&
    g'.log.any (fun s => Tests.mentions s "begins casting Bilbo's Deadly Slice") &&
    g'.log.any (fun s => Tests.mentions s "must choose a target (CR 601.2c)")
  | .error _ => false


#guard
  match applyTarget Tests.proposedBolt ⟨0⟩ ["1", "2"] with
  | .error msg => msg == sequentialTargetUsage
  | .ok _ => false


#guard
  let g := Tests.giftSetup
  let gid := (Tests.handCardNamed g ⟨0⟩ "Gift of Strands").id
  let tid := (Tests.namedPermanent g "Grizzly Bears").id
  match applyCast g ⟨0⟩ [toString gid] with
  | .error _ => false
  | .ok g' =>
    match applyTarget g' ⟨0⟩ [toString tid] with
    | .ok g'' =>
      g''.pending == .activateManaAbilities ⟨0⟩ &&
      g''.stack.back!.targets == #[Target.permanent tid]
    | .error _ => false


#guard
  match applyTarget Tests.gandalfEntered ⟨0⟩ ["opponent"] with
  | .ok g' =>
    g'.pending == .none &&
    g'.stack.back!.targets == #[Target.player ⟨1⟩] &&
    g'.stack.back!.dividedDamage == #[3] &&
    g'.log.any (fun s => Tests.mentions s "chooses Nissa to be dealt 3 damage")
  | .error _ => false


#guard
  match applyTarget Tests.gazeProposed ⟨0⟩ ["Grizzly Bears"] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
      g'.stack.back!.targets ==
        #[Target.permanent (Tests.namedPermanent g' "Grizzly Bears").id]
  | .error _ => false


#guard
  match applyTarget Tests.proposedMeagerMeal ⟨0⟩ ["Chandra"] with
  | .error msg => Tests.mentions msg "Illegal target"
  | .ok _ => false


#guard
  match Tests.proposedMeagerMeal.apply ⟨0⟩ .decline with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.stack.back!.targets.isEmpty &&
    g'.log.any (fun s => Tests.mentions s "chooses no target") &&
    match applyTarget g' ⟨0⟩ ["opponent"] with
    | .ok g'' =>
      g''.pending == .activateManaAbilities ⟨0⟩ &&
      g''.stack.back!.targets == #[Target.player ⟨1⟩]
    | .error _ => false
  | .error _ => false


#guard
  match applyMode Tests.proposedWarg ⟨0⟩ ["0"] with
  | .error msg => msg == modeUsage
  | .ok _ => false


#guard
  match applyMode Tests.proposedWarg ⟨0⟩ ["2"] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.stack.back!.chosenMode == some 1
  | .error _ => false


#guard
  match applyScry Tests.giftKnownScrying ⟨0⟩ ["top"] with
  | .error msg => msg == scryUsage
  | .ok _ => false


#guard
  match applyDiscard Tests.proposedTitania ⟨0⟩ [] with
  | .ok g' =>
    match g'.proposedSpell with
    | some prop => prop.needsDiscardCard
    | none => false
  | .error _ => false


#guard
  match applyDiscard Tests.spearMayDiscard ⟨0⟩ ["99999"] with
  | .error msg => msg == "no such object"
  | .ok _ => false


#guard
  match applyConniveChoice Tests.spearMayDiscard ⟨0⟩ [] with
  | .error msg => Tests.mentions msg "Not time to have a Villain connive"
  | .ok _ => false


#guard
  match applyAttach Tests.vowMayAttach ⟨0⟩ [] with
  | .error msg => msg == attachUsage
  | .ok _ => false


#guard
  match applyAttach Tests.spearMayDiscard ⟨0⟩
      [toString (Tests.namedPermanent Tests.spearMayDiscard "Ragged Short Spear").id] with
  | .error msg => Tests.mentions msg "Not time to choose permanents"
  | .ok _ => false


#guard
  match applyDecline Tests.vowMayAttach ⟨0⟩ [] with
  | .ok g' =>
    g'.pending == .none &&
    (Tests.namedPermanent g' "Ragged Short Spear").attachedTo.isNone &&
    g'.log.any (fun s => Tests.mentions s "declines to attach Equipment")
  | .error _ => false


#guard
  match applyAutopay Tests.drawnHands ⟨0⟩ [] with
  | .error msg => msg == "No spell or ability is waiting to be paid for (CR 601.2h)"
  | .ok _ => false


#guard
  match applyAutopay Tests.tappedForBolt ⟨0⟩ [] with
  | .ok r =>
    r.commands == #["pay"] &&
      r.game.log.any (fun s => Tests.mentions s "casts Lightning Bolt")
  | .error _ => false


#guard
  match applyAutopay Tests.forestFirstBolt ⟨0⟩ [] with
  | .ok r =>
    let mountain := Tests.namedPermanent Tests.forestFirstBolt "Mountain"
    r.commands == #[tapCommand mountain.id (.colored .red), "pay"] &&
      (Tests.namedPermanent r.game "Forest").status.tapped == false &&
      r.game.log.any (fun s => Tests.mentions s "casts Lightning Bolt")
  | .error _ => false


#guard
  match applyAutopay Tests.elvesFirstGrowth ⟨0⟩ [] with
  | .ok r =>
    let forest := Tests.namedPermanent Tests.elvesFirstGrowth "Forest"
    r.commands == #[tapCommand forest.id (.colored .green), "pay"] &&
      (Tests.namedPermanent r.game "Llanowar Elves").status.tapped == false &&
      r.game.log.any (fun s => Tests.mentions s "casts Giant Growth")
  | .error _ => false


#guard
  match applyAutopay Tests.hiddenLairStuckPayingDoombot ⟨0⟩ [] with
  | .error msg =>
    Tests.mentions msg "cannot pay" &&
      !(Tests.namedPermanent Tests.hiddenLairStuckPayingDoombot "Hidden Lair").status.tapped
  | .ok _ => false


#guard nextTurnPlayer Tests.nissaDraw == ⟨0⟩

#guard isPassShortcut "attack" ["step"]

#guard !isPassShortcut "pass" []

#guard isPassShortcutCmd "attack" ["step"]

#guard !reachedPassUntil { Tests.afterDraw with step := .declareAttackers }
  Tests.afterDraw.turnNumber .declareAttackers .nextDeclareAttackers

#guard isPassSequenceCommand "pass" []

#guard isPassSequenceCommand "ignore" []

#guard isPassSequenceAction (.declareAttackers #[])

#guard shortcutKind? "ignore" [] == some .ignore

#guard passUntilSkipsAttackers .nextMain

#guard passUntilGoalCommand? Tests.readyToDeclareAttackers
    (passUntilGoalAt Tests.readyToDeclareAttackers ⟨0⟩ (.named .nextMain)) ==
  some "noattack"

#guard (passUntilGoalCommand? Tests.readyToDeclareAttackers
    (passUntilGoalAt Tests.readyToDeclareAttackers ⟨1⟩ (.named .nextMain))).isNone

#guard (passUntilGoalCommand? Tests.readyToDeclareAttackers
    (passUntilGoalAt Tests.readyToDeclareAttackers ⟨0⟩
      (.named .nextDeclareAttackers))).isNone

#guard
  match applyInteractiveAsActor Tests.drawnHands "keep" [] with
  | .ok g' => (g'.player ⟨0⟩).keptOpeningHand && g'.actor == some ⟨1⟩
  | .error _ => false


#guard
  match applyStack Tests.twoAttercopsLandPending ⟨0⟩ [] with
  | .error msg => msg == stackUsage
  | .ok _ => false


#guard
  match applyInteractiveAsActor Tests.nissaDraw "concede" [] with
  | .ok g' =>
    match g'.result with
    | some (.won p) => p == ⟨0⟩
    | _ => false
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.hospitalityLandPlayed "target"
      [toString (Tests.namedPermanent Tests.hospitalityLandPlayed "Grizzly Bears").id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.hasPriority ⟨0⟩ &&
    g'.stack.back!.targets ==
      #[Target.permanent (Tests.namedPermanent g' "Grizzly Bears").id]
  | .error _ => false


#guard
  let sid := Tests.paidBolt.stack.back!.objectId
  match parseTarget Tests.paidBolt ⟨0⟩ (toString sid) with
  | .ok (Target.card id) => id == sid
  | _ => false


#guard
  match applyTarget Tests.elkEntered ⟨0⟩
      [toString (Tests.namedGraveyardCard Tests.elkEntered ⟨0⟩ "Llanowar Elves").id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.hasPriority ⟨0⟩ &&
    g'.stack.back!.targets ==
      #[Target.card (Tests.namedGraveyardCard Tests.elkEntered ⟨0⟩ "Llanowar Elves").id]
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.elkEntered "decline" [] with
  | .error msg => Tests.mentions msg "requires a target"
  | .ok _ => false


#guard
  let g := Tests.dunedainReady
  let blade := Tests.namedPermanent g "Dúnedain Blade"
  let bears := Tests.namedPermanent g "Grizzly Bears"
  match applyActivate g ⟨0⟩ [toString blade.id] with
  | .error _ => false
  | .ok g' =>
    match applyTarget g' ⟨0⟩ [toString bears.id] with
    | .error msg => Tests.mentions msg "Illegal target"
    | .ok _ => false


#guard
  match applyInteractiveAsActor Tests.galionAttackDeclared "target"
      [toString (Tests.namedPermanent Tests.galionAttackDeclared "Llanowar Elves").id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.hasPriority ⟨0⟩ &&
    g'.stack.back!.targets ==
      #[Target.permanent (Tests.namedPermanent g' "Llanowar Elves").id]
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.hospitalityAnimateSetup "activate"
      [toString (Tests.namedPermanent Tests.hospitalityAnimateSetup "Beorn's Hospitality").id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "begins activating Beorn's Hospitality")
  | .error _ => false


#guard
  match blockAssignmentsForCommand Tests.gollumVsOneBearReadyToBlock [] with
  | .ok asgn => asgn.isEmpty
  | .error _ => false


#guard
  match blockAssignmentsForCommand Tests.gollumAndOgreVsOneBearReadyToBlock [] with
  | .ok asgn =>
    let g := Tests.gollumAndOgreVsOneBearReadyToBlock
    asgn == #[(
      (Tests.namedPermanent g "Grizzly Bears").id,
      (Tests.namedPermanent g "Gray Ogre").id)]
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.spearMayDiscard "decline" [] with
  | .ok g' => g'.pending == .none && g'.hasPriority ⟨0⟩
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.vowMayAttach "decline" [] with
  | .ok g' =>
    g'.pending == .none &&
    g'.hasPriority ⟨0⟩ &&
    (Tests.namedPermanent g' "Ragged Short Spear").attachedTo.isNone &&
    g'.log.any (fun s => Tests.mentions s "declines to attach Equipment")
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.lookoutScrying "scry" [] with
  | .ok g' =>
    g'.pending == .none && g'.hasPriority ⟨0⟩ &&
      g'.battlefield.any (fun o => o.name == "Lothlórien Lookout")
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.woodElvesSetup "cast"
      [toString (Tests.handCardNamed Tests.woodElvesSetup ⟨0⟩ "Wood Elves").id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
      g'.log.any (fun s => Tests.mentions s "begins casting Wood Elves")
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.weavemasterElfSetup "cast"
      [toString (Tests.handCardNamed Tests.weavemasterElfSetup ⟨0⟩ "Llanowar Elves").id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
      g'.log.any (fun s => Tests.mentions s "begins casting Llanowar Elves")
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.pathmakerSetup "cast"
      [toString (Tests.handCardNamed Tests.pathmakerSetup ⟨0⟩ "Mirkwood Pathmaker").id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
      g'.log.any (fun s => Tests.mentions s "begins casting Mirkwood Pathmaker")
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.proposedStature "x" ["3"] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
      (g'.object! g'.stack.back!.objectId).chosenX == some 3
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.drawnHands "xyzzy" [] with
  | .error msg => msg == "Unknown command: xyzzy"
  | .ok _ => false


#guard
  match applyLoggedAction Tests.proposedOgre "autopay" [] "autopay" with
  | .error msg => Tests.mentions msg "cannot pay"
  | .ok _ => false


#guard
  match applyAttackStep Tests.afterDraw ⟨0⟩ [] with
  | .error msg => msg == attackStepUsage
  | .ok _ => false


#guard
  match applyLoggedAction Tests.readyToDeclareAttackers "attack" ["step"] "attack step" with
  | .error msg => msg == "A player must take an action other than pass"
  | .ok _ => false


#guard
  match applyLoggedAction Tests.started "attack" ["step"] "attack step" with
  | .ok (g', cmds) =>
    cmds == #["pass"] &&
      !cmds.contains "attack step" &&
      g'.step == .upkeep &&
      g'.turnNumber == 1 &&
      g'.hasPriority ⟨1⟩
  | .error _ => false


#guard
  match Tests.nissaDraw.apply ⟨1⟩ .pass with
  | .error _ => false
  | .ok g =>
    match applyLoggedAction g "my" ["turn"] "my turn" with
    | .ok (g', cmds) =>
      cmds == #["pass"] &&
        !cmds.contains "my turn" &&
        g'.step == .precombatMain &&
        g'.turnNumber == 2 &&
        g'.activePlayer == ⟨1⟩ &&
        g'.hasPriority ⟨1⟩ &&
        (goalsAfterCommand g g' ⟨0⟩ "my" ["turn"] #[]).size == 1
    | .error _ => false


#guard
  match applyLoggedAction Tests.afterDraw "ignore" [] "ignore" with
  | .ok (g', cmds) =>
    cmds == #["pass"] &&
      !cmds.contains "ignore" &&
      g'.step == .precombatMain &&
      g'.hasPriority ⟨1⟩ &&
      !(reachedIgnore g' (passUntilGoalAt Tests.afterDraw ⟨0⟩ .ignore))
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.drawnHands "shuffle" [] with
  | .error msg => msg == "No random event is waiting for a result"
  | .ok _ => false


#guard !isFlagLine "keep"

#guard commandsFromLines #["  keep  ", "", "pass"] == ["keep", "pass"]

#guard (inputScriptFromLines #["--visible", "keep", "pass"]).flags == ["--visible"]

#guard (inputScriptFromLines #["keep", "--visible", "pass"]).commands == ["keep", "pass"]

#guard flagTokens ["--name Elspeth --deck white"] ==
  ["--name", "Elspeth", "--deck", "white"]

#guard !sameInputOutput (some "opening.txt") (some "session.txt")

#guard shouldWriteInputFlags false ["--visible"]

#guard !shouldWriteInputFlags true []


#guard !shouldRecordCommand true true


#guard isNonStateCommand "help"

#guard !isNonStateCommand "first"

#guard !isCheckSkipCommand "quit"

#guard
  match takeStartingPlayer demoSeats true 0 ["help", "first Nissa"] with
  | .ok (1, []) => true
  | _ => false


#guard
  match replayCompleteGame Tests.drawnHands ["keep", "keep", "concede"] with
  | .ok g' => g'.over
  | .error _ => false


#guard
  match replayCompleteGame Tests.started ["help", "state", "concede"] with
  | .ok g' => g'.over
  | .error _ => false


#guard
  match replayCompleteGame Tests.afterDraw ["main phase", "concede"] with
  | .ok g' =>
    match g'.result with
    | some (.won p) =>
      p == ⟨0⟩ && g'.log.any (fun s => Tests.mentions s "Nissa concedes") &&
        !g'.log.any (fun s => Tests.mentions s "postcombat main")
    | _ => false
  | .error _ => false


#guard
  match replayCompleteGame Tests.afterDraw ["ignore", "pass", "concede"] with
  | .ok g' =>
    g'.over &&
      g'.log.any (fun s => Tests.mentions s "beginning of combat") &&
      match g'.result with
      | some (.won p) => p == ⟨0⟩
      | _ => false
  | .error _ => false


#guard
  let g0 := Tests.ogreDeclaredAttacker
  match applyLoggedAction g0 "main" ["phase"] "main phase" with
  | .ok (g1, cmds) =>
    cmds == #["pass"] &&
      g1.step == .declareAttackers &&
      g1.hasPriority ⟨1⟩ &&
      (goalsAfterCommand g0 g1 ⟨0⟩ "main" ["phase"] #[]).size == 1 &&
      match replayCompleteGame g0 ["main phase", "main phase", "concede"] with
      | .ok g' =>
        g'.over && g'.log.any (fun s => Tests.mentions s "postcombat main") &&
          match g'.result with
          | some (.won p) => p == ⟨1⟩
          | _ => false
      | .error _ => false
  | .error _ => false

-- A non-pass action by the other player cancels an interruptible shortcut.

#guard
  match applyLoggedAction Tests.readyToDeclareBlockers "main" ["phase"]
      "main phase" true with
  | .ok (g', cmds) =>
    cmds.contains "noblock" &&
      g'.pending != .declareBlockers &&
      g'.hasPriority ⟨0⟩
  | .error _ => false


#guard shouldWriteOutput false false true "keep"

#guard shouldWriteOutput true false true "keep"

#guard !shouldWriteOutput false false true "help"

#guard !shouldWriteOutput true true true "keep"


#guard !shouldAutoPay Tests.proposedOgre []

#guard shouldAutoPay Tests.targetedClub []

#guard shouldAutoPay Tests.paidClub []

#guard
  match autoPayStep? Tests.paidClub [] with
  | some (.ok (g', cmds)) =>
    cmds == #[s!"sacrifice {(Tests.clubFodder Tests.paidClub).id}"] &&
      g'.pending == .none &&
      g'.log.any (fun s => Tests.mentions s "casts Improvised Club")
  | _ => false


#guard !shouldAutoPass Tests.drawnHands []


#guard
  let g := { Tests.readyToDeclareBlockers with
    objects := Tests.readyToDeclareBlockers.objects.map (fun o =>
      if o.controlledBy ⟨1⟩ then
        { o with status := { o.status with tapped := true } }
      else o) }
  shouldAutoNoBlock g []

#guard shouldAutoTarget Tests.proposedSmite []

#guard !shouldAutoTarget Tests.started []

#guard !shouldAutoTarget Tests.galionAloneDeclared []

#guard
  match applyTarget Tests.proposedSmite ⟨0⟩
      [targetCommandArg Tests.proposedSmite ⟨0⟩
        (Target.permanent (Tests.namedPermanent Tests.proposedSmite "Grizzly Bears").id)] with
  | .ok g' =>
    g'.stack.back!.targets ==
      #[Target.permanent (Tests.namedPermanent Tests.proposedSmite "Grizzly Bears").id]
  | .error _ => false


#guard
  let tid := (Tests.namedPermanent Tests.hospitalityLandPlayed "Grizzly Bears").id
  match autoTargetStep? Tests.hospitalityLandPlayed [] with
  | some (.ok (g', cmd)) =>
    cmd == s!"target {tid}" &&
      g'.stack.back!.targets == #[Target.permanent tid]
  | _ => false

#guard
  match parseWelcomeDeck "gold" with
  | .error msg => msg == "Unknown Welcome Deck: gold (white, blue, black, red, or green)"
  | .ok _ => false


#guard !looksLikeDeckFile "gold"

#guard
  match parseDemoDeck "gold" with
  | .error msg =>
    msg == "Unknown Welcome Deck: gold (white, blue, black, red, or green, or a deck list file)"
  | .ok _ => false


#guard
  match parseArgs ["--interactive"] with
  | .ok opt => opt.interactive && !opt.multiplayer && !opt.playerView
  | _ => false


#guard
  match parseArgs ["--multiplayer", "--interactive"] with
  | .ok opt => opt.interactive && !opt.multiplayer
  | _ => false


#guard
  match parseArgs ["--multiplayer", "--input", "opening.txt"] with
  | .ok opt => opt.interactive && opt.multiplayer && opt.inputFile == some "opening.txt"
  | _ => false


#guard
  match parseArgs ["--interactive", "--norandom"] with
  | .ok opt => opt.norandom && opt.interactive
  | _ => false


#guard
  match parseArgsWithFlags ["--constructed"] ["--constructed"] with
  | .ok opt => opt.constructed
  | _ => false


#guard (demoConfig 1 (constructed := true)).format == .constructed


#guard
  match parseArgs ["--norandom", "--input", "opening.txt"] with
  | .ok opt => opt.norandom && opt.inputFile == some "opening.txt"
  | _ => false


#guard
  match parseArgs ["--check", "--interactive", "--input", "foo.txt"] with
  | .ok opt => opt.check && opt.interactive && !opt.multiplayer
  | _ => false


#guard
  match parseArgs ["--check", "--norandom", "--input", "foo.txt"] with
  | .ok opt => opt.check && opt.norandom && opt.interactive && opt.multiplayer
  | _ => false


#guard
  match parseArgs ["--interactive", "--input"] with
  | .error msg => msg == "Missing input file path"
  | .ok _ => false


#guard
  match parseArgs ["--multiplayer", "--output", "session.txt"] with
  | .ok opt => opt.interactive && opt.multiplayer && opt.outputFile == some "session.txt"
  | _ => false


#guard
  match parseArgs ["--output", "session.txt"] with
  | .error msg => msg == "--output requires --interactive or --multiplayer"
  | .ok _ => false


#guard
  match parseArgs [] with
  | .ok opt =>
    opt.players == defaultDemoPlayers && opt.decides.isNone && !opt.constructed
  | _ => false


#guard
  match parseArgs ["--auto", "--name", "Liliana", "--deck", "black",
      "--name", "Nissa", "--deck", "green"] with
  | .ok opt =>
    !opt.interactive &&
    opt.players[0]!.name == "Liliana" && opt.players[0]!.deck == .welcome .black &&
    opt.players[1]!.name == "Nissa" && opt.players[1]!.deck == .welcome .green
  | _ => false


#guard
  match parseArgs [
      "--name", "Alice", "--deck", "decks/a.txt",
      "--name", "Bob", "--deck", "./b"] with
  | .ok opt =>
    opt.players[0]!.deck == .file "decks/a.txt" &&
    opt.players[1]!.deck == .file "./b"
  | _ => false


#guard
  match parseArgs ["--name", "--interactive"] with
  | .error msg => msg == "Missing player name"
  | .ok _ => false


#guard
  match parseArgs ["--name", "Jace", "--deck", "blue", "--name", "jace", "--deck", "white"] with
  | .error msg => msg == "Duplicate player name: Jace"
  | .ok _ => false


#guard
  match parseArgs ["--interactive", "--decides", "Nissa"] with
  | .ok opt => opt.interactive && !opt.multiplayer && opt.decides == some 1
  | _ => false


#guard
  match parseArgs ["--decides", "Frodo"] with
  | .error msg => msg == "No player named Frodo"
  | .ok _ => false


#guard
  match parseArgsWithFlags ["--interactive", "--input", "opening.txt"] [] with
  | .ok opt => opt.interactive && opt.inputFile == some "opening.txt" && !opt.playerView
  | _ => false


#guard
  match parseArgsWithFlags
      ["--interactive", "--input", "opening.txt"] ["--fuel 12"] with
  | .ok opt => opt.fuel == 12
  | _ => false


#guard
  match parseArgsWithFlags
      ["--interactive", "--input", "a.txt", "--output", "b.txt"]
      ["--output c.txt", "--input d.txt", "--visible"] with
  | .ok opt =>
    opt.inputFile == some "a.txt" && opt.outputFile == some "b.txt" && opt.playerView
  | _ => false


#guard
  match parseArgsWithFlags ["--interactive"] ["--chandra"] with
  | .error msg => msg == "Unknown argument: --chandra"
  | .ok _ => false

