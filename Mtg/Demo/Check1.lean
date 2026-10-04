import Mtg.Demo
import Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Demo
open Mtg.Demo.Render

#guard demoFormat true == .constructed


#guard assignDecider defaultDemoPlayers 1 (some 1) == 1

#guard
  let picks := (List.range 64).map (fun n =>
    assignDecider defaultDemoPlayers (UInt64.ofNat n) none)
  picks.all (fun i => i < 2) && picks.any (fun i => i == 0) && picks.any (fun i => i == 1)


#guard !humanChoosesFirst false false 0

#guard heuristicChoseToGoFirst "Nissa" == "Nissa chooses to take the first turn."


#guard
  match parseFirstPlayer demoSeats ["Nissa"] with
  | .ok 1 => true
  | _ => false


#guard
  match Start.start (demoConfig 1 (some 1)) with
  | .ok g =>
    g.startingPlayer == ⟨1⟩ &&
    g.pending == .declareMulligan ⟨1⟩ &&
    g.actor == some ⟨1⟩ &&
    (g.player ⟨1⟩).name == "Nissa" &&
    g.log.any (· == "Starting player: Nissa")
  | .error _ => false


#guard (seatsFromPlayers elspethJace)[0]!.name == "Elspeth"

#guard (seatsFromPlayers #[
    { name := "Liliana", deck := .welcome .black },
    { name := "Chandra", deck := .welcome .red }])[0]!.deck.any
  (fun c => c.name == "Gollum, Silent Slinker")

#guard describeFirstChooser elspethJaceLiliana 2 true ==
  "Liliana is chosen at random to decide who takes the first turn (CR 103.1)."

#guard
  match playersFromFlags #[] #[] with
  | .ok ps => ps == defaultDemoPlayers
  | .error _ => false


#guard
  match playersFromFlags #["Jace", "jace"] #[.welcome .blue, .welcome .white] with
  | .error msg => msg == "Duplicate player name: Jace"
  | .ok _ => false


#guard
  match Start.start (demoConfig 1 (some 0) #[
      { name := "Elspeth", deck := .welcome .white },
      { name := "Liliana", deck := .welcome .black }]) with
  | .ok g =>
    g.objects.any (fun o => o.name == "Bofur, Reliable Guardian") &&
    g.objects.any (fun o => o.name == "Gollum, Silent Slinker") &&
    !g.objects.any (fun o => o.name == "Smaug, the Great Calamity")
  | .error _ => false


#guard ((helpInteractive true).splitOn "the acting player can see").length > 1

#guard ((helpInteractive false).splitOn "target <id|name|opponent>").length > 1

#guard ((helpInteractive false).splitOn "x <n>").length > 1

#guard ((helpInteractive false).splitOn "assign <s> <t> <n>").length > 1

#guard ((helpInteractive false).splitOn "103.5c").length > 1

#guard ((helpInteractive false).splitOn "CR 603.3b").length > 1

#guard ((helpInteractive false).splitOn "decline").length > 1

#guard ((helpInteractive false).splitOn "choose no target").length > 1

#guard ((helpInteractive false).splitOn "only you pass").length > 5

#guard ((helpInteractive false).splitOn "uses noattack").length > 4

#guard ((helpInteractive false).splitOn "ignore").length > 1

#guard ((helpInteractive false).splitOn "resolved trigger requires").length > 1

#guard (usage.splitOn "the game ends (a winner or a draw)").length > 1

#guard (usage.splitOn "Unique automatic cost payments").length > 1

#guard (usage.splitOn "only pass for the player who issued them").length > 1

#guard (usage.splitOn "--name NAME").length > 1

#guard (usage.splitOn "--decides NAME").length > 1

#guard (usage.splitOn "constructed play").length > 1

#guard (usage.splitOn "first <name>").length > 1

#guard (helpChooseFirst.splitOn "quit").length > 1


#guard splitAtKeyword "bottom" ["1", "2", "bottom", "3"] == (["1", "2"], some ["3"])

#guard parseObjectId? "#12" == some ⟨12⟩

#guard
  match parseObjectIds [] attackUsage with
  | .error _ => true
  | .ok _ => false


#guard
  let g := Tests.readyToDeclareAttackers
  let bears := Tests.namedPermanent g "Grizzly Bears"
  match applyAttack g ⟨0⟩ [toString bears.id, "at", "opponent"] with
  | .ok g' =>
    (Tests.namedPermanent g' "Grizzly Bears").status.attackingWhom == some ⟨1⟩ &&
    !(Tests.namedPermanent g' "Gray Ogre").status.attacking
  | .error _ => false


#guard
  match applyAttack Tests.threeReadyToAttack ⟨0⟩ ["Liliana"] with
  | .ok g' =>
    (Tests.namedPermanent g' "Gray Ogre").status.attackingWhom == some ⟨2⟩ &&
      g'.defendingPlayer == ⟨2⟩
  | .error _ => false


#guard
  match parseBlockAssignments ["3", "#7"] with
  | .ok asgn => asgn == #[(⟨3⟩, ⟨7⟩)]
  | .error _ => false


#guard
  match blockAssignmentsForCommand Tests.readyToDeclareBlockers [] with
  | .ok asgn =>
    let g := Tests.readyToDeclareBlockers
    asgn == #[(
      (Tests.namedPermanent g "Grizzly Bears").id,
      (Tests.namedPermanent g "Gray Ogre").id)]
  | .error _ => false


#guard
  match applyBlock Tests.readyToDeclareBlockers ⟨1⟩ ["nope"] with
  | .error msg => msg == blockUsage
  | .ok _ => false


#guard
  match applyBlock Tests.ogreVsCrusherReadyToBlock ⟨1⟩ [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Olog-hai Crusher").status.blocking.isEmpty &&
      !(Tests.namedPermanent g' "Gray Ogre").status.blocked
  | .error _ => false


#guard
  match parseCombatAssignments Tests.giantReadyToAssign ⟨0⟩ ["3", "Nissa", "2"] with
  | .ok asgns => asgns == #[{ source := ⟨3⟩, toPlayer := 2 }]
  | .error _ => false


#guard
  match parseCombatAssignments Tests.started ⟨0⟩ ["3", "1", "2", "3", "Nissa", "1"] with
  | .ok asgns =>
    asgns == #[{ source := ⟨3⟩, toCreatures := #[(⟨1⟩, 2)], toPlayer := 1 }]
  | .error _ => false


#guard
  match applyAssign Tests.readyToDeclareBlockers ⟨0⟩ [] with
  | .error msg => msg == "Not time to assign combat damage (CR 510.1)"
  | .ok _ => false


#guard
  match applyBottom Tests.afterChandraMulligan ⟨0⟩ [] with
  | .error msg => msg == bottomUsage
  | .ok _ => false


#guard
  match applyVisible ["off"] with
  | .ok (some false) => true
  | _ => false


#guard humanView true == some ⟨0⟩


#guard (currentView Tests.drawnHands true true) == some ⟨0⟩


#guard
  match actingPlayer Tests.afterChandraDeclaresMulligan with
  | .ok p => p == ⟨1⟩
  | .error _ => false


#guard
  let g := Tests.baubleReady
  let bauble := Tests.baubleSource g
  match applyTap g ⟨0⟩ [toString bauble.id] with
  | .error msg => Tests.mentions msg "has no mana ability"
  | .ok _ => false


#guard
  let g := Tests.hiddenLairWithIsland
  let lair := Tests.namedPermanent g "Hidden Lair"
  match applyTap g ⟨0⟩ [toString lair.id, "blue"] with
  | .ok g' =>
    (Tests.namedPermanent g' "Hidden Lair").status.tapped &&
    (g'.player ⟨0⟩).manaPool.canPay (ManaCost.ofColor .blue)
  | .error _ => false


#guard
  let g := Tests.withMountain
  let mtn := Tests.lastPermanent g
  match applyTap g ⟨0⟩ [toString mtn.id, toString mtn.id] with
  | .error msg => Tests.mentions msg "already tapped"
  | .ok _ => false


#guard
  match applyPlay Tests.afterDraw ⟨0⟩ ["99999"] with
  | .error msg => msg == "no such object"
  | .ok _ => false


#guard
  match applySacrifice Tests.stirChooseAdditional ⟨0⟩ [] with
  | .ok g' =>
    match g'.proposedSpell with
    | some prop => prop.needsSacrificeOther
    | none => false
  | .error _ => false


#guard
  match applyActivate Tests.baubleReady ⟨0⟩ ["nope"] with
  | .error msg => msg == activateUsage
  | .ok _ => false


#guard
  match applyActivate Tests.baubleReady ⟨0⟩ ["99999"] with
  | .error msg => msg == "no such object"
  | .ok _ => false


#guard
  let g := Tests.baubleReady
  let bauble := Tests.baubleSource g
  match applyActivate g ⟨0⟩ [toString bauble.id, "2"] with
  | .error msg => Tests.mentions msg "has no such activated ability"
  | .ok _ => false


#guard
  let g := Tests.hunterReady
  let hunter := Tests.hunterSource g
  match applyActivate g ⟨0⟩ [toString hunter.id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "begins activating Snowslope Hunter")
  | .error _ => false


#guard
  let g := Tests.hunterReady
  match applySacrifice g ⟨0⟩ [toString (Tests.hunterFodder g).id] with
  | .error msg => Tests.mentions msg "Not time to sacrifice"
  | .ok _ => false


#guard
  let g := Tests.bladeMustSac
  let bears := Tests.namedPermanent g "Grizzly Bears"
  match applySacrifice g ⟨1⟩ [toString bears.id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.log.any (fun s => Tests.mentions s "sacrifices Grizzly Bears")
  | .error _ => false


#guard
  match applyMode Tests.proposedCratermaker ⟨0⟩ ["1", "2"] with
  | .error msg => msg == modeUsage
  | .ok _ => false


#guard
  match applyX Tests.proposedStature ⟨0⟩ ["nope"] with
  | .error msg => msg == xUsage
  | .ok _ => false


#guard
  let g := Tests.cratermakerDestroyReady
  let src := Tests.cratermakerSource g
  match applyActivate g ⟨0⟩ [toString src.id] with
  | .error _ => false
  | .ok g' =>
    match applyMode g' ⟨0⟩ ["2"] with
    | .ok g'' =>
      g''.pending == .chooseTargets ⟨0⟩ &&
      (g''.object! g''.stack.back!.objectId).abilityEffect ==
        some (Effect.destroyTargetColorlessNonland)
    | .error _ => false


#guard
  match applyCast Tests.boltSetup ⟨0⟩ ["1", "2", "3"] with
  | .error msg => msg == castUsage
  | .ok _ => false


#guard
  match applyCast Tests.smaugSetup ⟨0⟩
      [toString (Tests.handCardNamed Tests.smaugSetup ⟨0⟩ "Smaug, the Great Calamity").id,
        "adventure"] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    (g'.object! g'.stack.back!.objectId).name == "Spew Flame" &&
    g'.log.any (fun s => Tests.mentions s "begins casting Spew Flame")
  | .error _ => false


#guard
  match applyCast Tests.boltSetup ⟨0⟩ [toString Tests.boltInHand.id, "adventure"] with
  | .error msg => Tests.mentions msg "has no Adventure"
  | .ok _ => false


#guard
  match applyTarget Tests.proposedBolt ⟨0⟩ ["99999"] with
  | .error msg => msg == "no such object"
  | .ok _ => false


#guard
  let g := Tests.quarrelSetup
  let qid := (Tests.handCardNamed g ⟨0⟩ "Quarrel").id
  let src := (Tests.namedPermanent g "Llanowar Elves").id
  let dest := (Tests.namedPermanent g "Grizzly Bears").id
  match applyCast g ⟨0⟩ [toString qid] with
  | .error _ => false
  | .ok g' =>
    match applyTarget g' ⟨0⟩ ["Llanowar Elves"] with
    | .error _ => false
    | .ok g'' =>
      g''.pending == .chooseTargets ⟨0⟩ &&
      g''.stack.back!.targets == #[Target.permanent src] &&
      match applyTarget g'' ⟨0⟩ [toString dest] with
      | .ok g''' =>
        g'''.pending == .activateManaAbilities ⟨0⟩ &&
        g'''.stack.back!.targets == #[Target.permanent src, Target.permanent dest]
      | .error _ => false


#guard
  match applyTarget Tests.gandalfSplitSetup ⟨0⟩
      ["opponent", "2", toString (Tests.namedPermanent Tests.gandalfSplitSetup "Grizzly Bears").id, "1"] with
  | .ok g' =>
    g'.pending == .none &&
    g'.stack.back!.dividedDamage == #[2, 1] &&
    (g'.player ⟨1⟩).life == 20
  | .error _ => false


#guard
  match applyTarget Tests.gazeProposed ⟨0⟩ ["Grizzly Bears", "Gray Ogre"] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
      g'.stack.back!.targets ==
        #[Target.permanent (Tests.namedPermanent g' "Grizzly Bears").id,
          Target.permanent (Tests.namedPermanent g' "Gray Ogre").id]
  | .error _ => false


#guard
  match applyTarget Tests.proposedMeagerMeal ⟨0⟩ ["opponent"] with
  | .error msg => Tests.mentions msg "Illegal target"
  | .ok _ => false


#guard
  match applyTarget Tests.gandalfEntered ⟨0⟩ ["opponent", "x"] with
  | .error msg => msg == divideTargetUsage
  | .ok _ => false


#guard
  match applyMode Tests.proposedWarg ⟨0⟩ ["1", "2"] with
  | .error msg => msg == modeUsage
  | .ok _ => false


#guard
  match applyScry Tests.giftScrying ⟨0⟩ [] with
  | .ok g' => g'.pending == .none && g'.hasPriority ⟨0⟩
  | .error _ => false


#guard
  let g := Tests.giftKnownScrying
  let looked := g.scryLookedIds ⟨0⟩ 2
  match looked[0]?, looked[1]? with
  | some forest, some elves =>
    match applyScry g ⟨0⟩ ["top", toString elves, toString forest] with
    | .ok g' =>
      (g'.object! (g'.player ⟨0⟩).library.back!).name == "Forest" &&
        g'.log.any (fun s => Tests.mentions s "puts Forest on top of their library")
    | .error _ => false
  | _, _ => false


#guard
  match applyDiscard Tests.spearMayDiscard ⟨0⟩ [] with
  | .error msg => msg == discardUsage
  | .ok _ => false


#guard
  let g := Tests.spearKnownMayDiscard
  let forest := Tests.handCardNamed g ⟨0⟩ "Forest"
  match applyDiscard g ⟨0⟩ [toString forest.id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.log.any (fun s => Tests.mentions s "discards Forest")
  | .error _ => false


#guard
  match applyDecline Tests.spearMayDiscard ⟨0⟩ ["extra"] with
  | .error msg => msg == declineUsage
  | .ok _ => false


#guard
  match applyAttach Tests.vowMayAttach ⟨0⟩ ["nope"] with
  | .error msg => msg == attachUsage
  | .ok _ => false


#guard
  match applyAttach Tests.vowMayAttach ⟨1⟩
      [toString (Tests.namedPermanent Tests.vowMayAttach "Ragged Short Spear").id] with
  | .error msg => Tests.mentions msg "Only Chandra may attach Equipment"
  | .ok _ => false


#guard tapCommand ⟨12⟩ (.colored .red) == "tap #12 R"

#guard
  match applyAutopay Tests.proposedBolt ⟨0⟩ [] with
  | .error msg => Tests.mentions msg "Choose a target first"
  | .ok _ => false


#guard
  match applyAutopay Tests.proposedVisionary ⟨0⟩ [] with
  | .ok r =>
    r.commands == #["pay"] &&
      r.game.log.any (fun s => Tests.mentions s "casts Elvish Visionary")
  | .error _ => false


#guard
  match applyAutopay Tests.weavemasterForestGrowth ⟨0⟩ [] with
  | .ok r =>
    let forest := Tests.namedPermanent Tests.weavemasterForestGrowth "Forest"
    r.commands == #[tapCommand forest.id (.colored .green), "pay"] &&
      (Tests.namedPermanent r.game "Woodland Weavemaster").status.tapped == false &&
      r.game.log.any (fun s => Tests.mentions s "casts Giant Growth")
  | .error _ => false


#guard
  match applyAutopay Tests.mountainThenPassageBauble ⟨0⟩ [] with
  | .ok r =>
    let passage := Tests.namedPermanent Tests.mountainThenPassageBauble "Rogue's Passage"
    let mountain := Tests.namedPermanent Tests.mountainThenPassageBauble "Mountain"
    r.commands ==
      #[tapCommand passage.id .colorless,
        tapCommand mountain.id (.colored .red), "pay"] &&
      r.game.pending == .none &&
      r.game.log.any (fun s => Tests.mentions s "activates Wayfarer's Bauble")
  | .error _ => false


#guard
  match applyAutopay Tests.hiddenLairScientistWithIsland ⟨0⟩ [] with
  | .ok r =>
    let lair := Tests.namedPermanent Tests.hiddenLairScientistWithIsland "Hidden Lair"
    let isl := Tests.namedPermanent Tests.hiddenLairScientistWithIsland "Island"
    r.commands ==
      #[tapCommand lair.id (.colored .black),
        tapCommand isl.id (.colored .blue), "pay"] &&
      (Tests.namedPermanent r.game "Hidden Lair").status.tapped &&
      (Tests.namedPermanent r.game "Island").status.tapped &&
      r.game.log.any (fun s => Tests.mentions s "casts Scientist Supreme")
  | .error _ => false


#guard isPassShortcut "your" ["turn"]

#guard isPassShortcut "ignore" []

#guard !isPassShortcut "ignore" ["now"]

#guard !isPassShortcutCmd "attack" []

#guard !reachedPassUntil Tests.afterDraw Tests.afterDraw.turnNumber
  Tests.afterDraw.step .nextMain

#guard isPassSequenceCommand "noattack" []
