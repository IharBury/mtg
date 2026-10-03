import Mtg.Demo
import Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Demo
open Mtg.Demo.Render

#guard
  match parsePlayerName demoSeats "Chandra" with
  | .ok 0 => true
  | _ => false


#guard assignDecider defaultDemoPlayers 1 (some 0) == 0

#guard humanChoosesFirst true false 0

#guard !humanChoosesFirst false true 0


#guard firstUsage demoSeats == "usage: first <name> (Chandra or Nissa)"


#guard
  match parseFirstPlayer demoSeats ["Frodo"] with
  | .error msg => msg == "No player named Frodo"
  | .ok _ => false


#guard
  match Start.start (demoConfig 1) with
  | .ok g =>
    g.startingPlayer == ⟨0⟩ &&
    g.pending == .declareMulligan ⟨0⟩
  | .error _ => false


#guard (seatsFromPlayers elspethJace)[1]!.name == "Jace"

#guard (seatsFromPlayers #[
    { name := "Liliana", deck := .welcome .black },
    { name := "Chandra", deck := .welcome .red }])[1]!.deck.any
  (fun c => c.name == "Smaug, the Great Calamity")

#guard
  let picks := (List.range 64).map (fun n =>
    assignDecider elspethJaceLiliana (UInt64.ofNat n) none)
  picks.all (fun i => i < 3) &&
    picks.any (fun i => i == 0) &&
    picks.any (fun i => i == 1) &&
    picks.any (fun i => i == 2)

#guard
  match playersFromFlags #["Elspeth", "Jace"] #[.welcome .white, .welcome .blue] with
  | .ok ps => ps == elspethJace
  | .error _ => false


#guard
  match playersFromFlags #["Alice", "Bob"] #[.file "alice.txt", .welcome .red] with
  | .ok ps =>
    ps.size == 2 &&
    ps[0]!.name == "Alice" && ps[0]!.deck == .file "alice.txt" &&
    ps[1]!.name == "Bob" && ps[1]!.deck == .welcome .red
  | .error _ => false


#guard ((helpInteractive false).splitOn "visible").length > 1

#guard ((helpInteractive false).splitOn "tap <id> [id...]").length > 1

#guard ((helpInteractive false).splitOn "together").length > 1

#guard ((helpInteractive false).splitOn "cast <id> adventure").length > 1

#guard ((helpInteractive false).splitOn "defending player").length > 1

#guard ((helpInteractive false).splitOn "keep <id>").length > 1

#guard ((helpInteractive false).splitOn "discard <id>").length > 1

#guard ((helpInteractive false).splitOn "optional discard, attach").length > 1

#guard ((helpInteractive false).splitOn "pay-extra").length > 1

#guard ((helpInteractive false).splitOn "my turn").length > 1

#guard (usage.splitOn "use noattack when declaring").length > 1

#guard ((helpInteractive false).splitOn "never interrupted").length > 1

#guard (usage.splitOn "--input FILE").length > 1

#guard (usage.splitOn "additional flags instead of commands").length > 1

#guard (usage.splitOn "Pass-until shortcuts").length > 1

#guard (usage.splitOn "ignore is never interrupted").length > 1

#guard (usage.splitOn "--deck COLOR").length > 1

#guard (usage.splitOn "random player").length > 1

#guard ((helpInteractive false).splitOn "shuffle [id...]").length > 1

#guard (usage.splitOn "CR 103.1").length > 1


#guard parseManaType? "G" == some (.colored .green)

#guard splitAtKeyword "bottom" ["1", "2"] == (["1", "2"], none)

#guard (parseObjectId? "x").isNone

#guard
  match attackerIdsForCommand Tests.readyToDeclareAttackers [] with
  | .ok ids => ids.size == 2
  | .error _ => false


#guard
  match applyAttack Tests.readyToDeclareAttackers ⟨0⟩ ["Chandra"] with
  | .error msg => msg == "cannot attack yourself"
  | .ok _ => false


#guard
  let g := Tests.threeReadyToAttack
  let ogre := Tests.namedPermanent g "Gray Ogre"
  match applyAttack g ⟨0⟩ [toString ogre.id, "at", "Liliana"] with
  | .ok g' => (Tests.namedPermanent g' "Gray Ogre").status.attackingWhom == some ⟨2⟩
  | .error _ => false


#guard
  match parseBlockAssignments ["1", "2", "#3", "4"] with
  | .ok asgn => asgn == #[(⟨1⟩, ⟨2⟩), (⟨3⟩, ⟨4⟩)]
  | .error _ => false


#guard
  let g := Tests.readyToDeclareBlockers
  let bears := Tests.namedPermanent g "Grizzly Bears"
  let ogre := Tests.namedPermanent g "Gray Ogre"
  match applyBlock g ⟨1⟩ [toString bears.id, toString ogre.id] with
  | .ok g' =>
    (Tests.namedPermanent g' "Grizzly Bears").status.blocking == #[ogre.id]
  | .error _ => false


#guard
  match applyBlock Tests.readyToDeclareAttackers ⟨0⟩ [] with
  | .error msg => msg == "Not time to declare blockers"
  | .ok _ => false


#guard
  match applyBlock Tests.ogreVsCrusherAndGoblinReadyToBlock ⟨1⟩ [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Olog-hai Crusher").status.blocking ==
      #[(Tests.namedPermanent g' "Gray Ogre").id]
  | .error _ => false


#guard
  match parseCombatAssignments Tests.giantReadyToAssign ⟨0⟩ ["3", "opponent", "2"] with
  | .ok asgns => asgns == #[{ source := ⟨3⟩, toPlayer := 2 }]
  | .error _ => false


#guard
  match applyAssign Tests.giantReadyToAssign ⟨0⟩ [] with
  | .ok g' =>
    g'.pending == .none &&
    (g'.battlefield.filter (fun o => o.name == "Llanowar Elves")).size == 1
  | .error _ => false


#guard
  match applyBottom Tests.afterChandraMulligan ⟨0⟩
      [toString Tests.chandraBottomCard.id] with
  | .ok g' => (g'.player ⟨0⟩).hand.size == 6
  | .error _ => false


#guard
  match applyBottom Tests.drawnHands ⟨0⟩
      [toString (Tests.drawnHands.player ⟨0⟩).hand[0]!] with
  | .error msg => msg == "Not time to put cards on the bottom (CR 103.5)"
  | .ok _ => false


#guard
  match applyVisible ["nope"] with
  | .error msg => msg == visibleUsage
  | .ok _ => false


#guard (currentView Tests.nissaDraw true false) == some ⟨0⟩

#guard
  match actingPlayer Tests.drawnHands with
  | .ok p => p == ⟨0⟩
  | .error _ => false


#guard
  match applyTap Tests.baubleReady ⟨0⟩ [] with
  | .error msg => msg == tapUsage
  | .ok _ => false


#guard
  let g := Tests.withMountain
  let mtn := Tests.lastPermanent g
  match applyTap g ⟨0⟩ [toString mtn.id] with
  | .ok g' =>
    (Tests.lastPermanent g').status.tapped &&
    (g'.player ⟨0⟩).manaPool.canPay (ManaCost.ofColor .red)
  | .error _ => false


#guard
  let g := Tests.archAndElves
  let arch := Tests.namedPermanent g "Elvish Archdruid"
  match applyTap g ⟨0⟩ [toString arch.id] with
  | .ok g' =>
    (Tests.namedPermanent g' "Elvish Archdruid").status.tapped &&
    (g'.player ⟨0⟩).manaPool.green == 2 &&
    g'.log.any (fun s => Tests.mentions s "green ×2")
  | .error _ => false


#guard
  match applyPlay Tests.afterDraw ⟨0⟩ [] with
  | .error msg => msg == playUsage
  | .ok _ => false


#guard
  let g := Tests.afterDraw
  match (g.handObjects ⟨0⟩).find? (·.printed.isLand) with
  | none => false
  | some land =>
    match applyPlay g ⟨0⟩ [toString land.id] with
    | .ok g' =>
      (g'.player ⟨0⟩).landsPlayedThisTurn == 1 &&
      g'.battlefield.any (fun o => o.name == land.name)
    | .error _ => false


#guard
  match applySacrifice Tests.proposedTitania ⟨0⟩ [] with
  | .error msg => msg == sacrificeUsage
  | .ok _ => false


#guard
  match applyActivate Tests.baubleReady ⟨0⟩ ["1", "nope"] with
  | .error msg => msg == activateUsage
  | .ok _ => false


#guard
  let g := Tests.baubleReady
  match (g.permanentsOf ⟨0⟩).find? (·.printed.isLand) with
  | none => false
  | some land =>
    match applyActivate g ⟨0⟩ [toString land.id] with
    | .error msg => Tests.mentions msg "has no activated ability"
    | .ok _ => false


#guard
  let g := Tests.dunedainReady
  let blade := Tests.namedPermanent g "Dúnedain Blade"
  match applyActivate g ⟨0⟩ [toString blade.id] with
  | .ok g' => g'.pending == .chooseTargets ⟨0⟩
  | .error _ => false


#guard
  match applySacrifice Tests.hunterReady ⟨0⟩ [] with
  | .error msg => msg == sacrificeUsage
  | .ok _ => false


#guard
  let g := Tests.paidHunter
  match applySacrifice g ⟨0⟩ ["99999"] with
  | .error msg => msg == "no such object"
  | .ok _ => false


#guard
  match applyMode Tests.proposedCratermaker ⟨0⟩ [] with
  | .error msg => msg == modeUsage
  | .ok _ => false


#guard
  match applyMode Tests.proposedCratermaker ⟨0⟩ ["1"] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "chooses a mode")
  | .error _ => false


#guard
  match applyX Tests.proposedStature ⟨0⟩ ["3", "1"] with
  | .error msg => msg == xUsage
  | .ok _ => false


#guard
  match applyCast Tests.boltSetup ⟨0⟩ [] with
  | .error msg => msg == castUsage
  | .ok _ => false


#guard
  match applyCast Tests.boltSetup ⟨0⟩ ["99999"] with
  | .error msg => msg == "no such object"
  | .ok _ => false


#guard
  match applyCast Tests.beornSetup ⟨0⟩
      [toString (Tests.handCardNamed Tests.beornSetup ⟨0⟩ "Beorn, Reluctant Host").id,
        "adventure"] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
    (g'.object! g'.stack.back!.objectId).name == "Till and Tend" &&
    (g'.object! g'.stack.back!.objectId).isAdventureSpell &&
    g'.log.any (fun s => Tests.mentions s "begins casting Till and Tend")
  | .error _ => false


#guard
  match applyTarget Tests.proposedBolt ⟨0⟩ [] with
  | .error msg => msg == targetUsage
  | .ok _ => false


#guard
  match applyTarget Tests.proposedBolt ⟨0⟩ ["opponent"] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
    g'.stack.back!.targets == #[Target.player ⟨1⟩] &&
    g'.log.any (fun s => Tests.mentions s "chooses Nissa as a target (CR 601.2c)")
  | .error _ => false


#guard
  let g := Tests.smiteSetup
  match applyCast g ⟨0⟩ [toString (Tests.handCardNamed g ⟨0⟩ "Smite the Deathless").id] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "begins casting Smite the Deathless") &&
    g'.log.any (fun s => Tests.mentions s "must choose a target (CR 601.2c)")
  | .error _ => false


#guard
  match applyTarget Tests.gandalfEntered ⟨0⟩ ["opponent", "2"] with
  | .error msg => Tests.mentions msg "Must assign all remaining damage"
  | .ok _ => false


#guard
  match applyTarget Tests.gazeOneTarget ⟨0⟩ ["Gray Ogre"] with
  | .error msg => Tests.mentions msg "Not time to choose targets"
  | .ok _ => false


#guard
  match applyTarget Tests.proposedMeagerMeal ⟨0⟩ ["Grizzly Bears", "Chandra"] with
  | .error msg => msg == sequentialTargetUsage
  | .ok _ => false


#guard
  match applyMode Tests.proposedWarg ⟨0⟩ [] with
  | .error msg => msg == modeUsage
  | .ok _ => false


#guard
  match applyMode Tests.proposedWarg ⟨0⟩ ["3"] with
  | .error msg => Tests.mentions msg "No such mode"
  | .ok _ => false


#guard
  match applyScry Tests.giftSetup ⟨0⟩ [] with
  | .error msg => Tests.mentions msg "Not time to scry"
  | .ok _ => false


#guard
  let g := Tests.giftKnownScrying
  let looked := g.scryLookedIds ⟨0⟩ 2
  match looked[0]?, looked[1]? with
  | some forest, some elves =>
    match applyScry g ⟨0⟩ ["top", toString forest, "bottom", toString elves] with
    | .ok g' =>
      (g'.object! (g'.player ⟨0⟩).library.back!).name == "Forest" &&
        (g'.object! (g'.player ⟨0⟩).library[0]!).name == "Llanowar Elves"
    | .error _ => false
  | _, _ => false


#guard
  match applyDiscard Tests.spearMayDiscard ⟨0⟩ ["nope"] with
  | .error msg => msg == discardUsage
  | .ok _ => false


#guard
  match applyConniveChoice Tests.struckerMayConnive ⟨0⟩ ["extra"] with
  | .error msg => msg == conniveUsage
  | .ok _ => false


#guard
  match applyDecline Tests.spearMayDiscard ⟨0⟩ [] with
  | .ok g' =>
    g'.pending == .none &&
    g'.log.any (fun s => Tests.mentions s "declines to discard")
  | .error _ => false


#guard
  match applyAttach Tests.vowMayAttach ⟨0⟩ ["1", "2"] with
  | .error msg => msg == attachUsage
  | .ok _ => false


#guard
  match applyAttach Tests.vowMayAttach ⟨0⟩
      [toString (Tests.namedPermanent Tests.vowMayAttach "Bofur, Reliable Guardian").id] with
  | .error msg => Tests.mentions msg "is not an Equipment you control"
  | .ok _ => false


#guard tapCommand ⟨3⟩ .colorless == "tap #3 C"


#guard
  match applyAutopay Tests.proposedOgre ⟨0⟩ [] with
  | .error msg => Tests.mentions msg "cannot pay"
  | .ok _ => false


#guard
  let g := Tests.proposedBauble
  let lands := (g.permanentsOf ⟨0⟩).filter (·.printed.isLand)
  lands.size == 2 &&
  match applyAutopay g ⟨0⟩ [] with
  | .ok r =>
    r.commands ==
      #[tapCommand lands[0]!.id (.colored .red),
        tapCommand lands[1]!.id (.colored .red), "pay"] &&
      r.game.pending == .none &&
      r.game.log.any (fun s => Tests.mentions s "activates Wayfarer's Bauble")
  | .error _ => false


#guard
  match applyAutopay Tests.delightedHalflingForestGrowth ⟨0⟩ [] with
  | .ok r =>
    let forest := Tests.namedPermanent Tests.delightedHalflingForestGrowth "Forest"
    r.commands == #[tapCommand forest.id (.colored .green), "pay"] &&
      (Tests.namedPermanent r.game "Delighted Halfling").status.tapped == false &&
      r.game.log.any (fun s => Tests.mentions s "casts Giant Growth")
  | .error _ => false


#guard
  match applyAutopay Tests.hiddenLairPayingDoombot ⟨0⟩ [] with
  | .ok r =>
    let lair := Tests.namedPermanent Tests.hiddenLairPayingDoombot "Hidden Lair"
    r.commands == #[tapCommand lair.id (.colored .blue), "pay"] &&
      (Tests.namedPermanent r.game "Hidden Lair").status.tapped &&
      r.game.log.any (fun s => Tests.mentions s "casts Aerial Doombot")
  | .error _ => false


#guard
  match applyAutopay Tests.hiddenLairScientistWithSwamp ⟨0⟩ [] with
  | .ok r =>
    let lair := Tests.namedPermanent Tests.hiddenLairScientistWithSwamp "Hidden Lair"
    let sw := Tests.namedPermanent Tests.hiddenLairScientistWithSwamp "Swamp"
    r.commands ==
      #[tapCommand lair.id (.colored .blue),
        tapCommand sw.id (.colored .black), "pay"] &&
      r.game.log.any (fun s => Tests.mentions s "casts Scientist Supreme")
  | .error _ => false


#guard isPassShortcut "my" ["turn"]

#guard !isPassShortcut "your" []

#guard isPassShortcutCmd "your" []

#guard reachedPassUntil { Tests.afterDraw with step := .declareAttackers }
  Tests.afterDraw.turnNumber Tests.afterDraw.step .nextDeclareAttackers

#guard reachedPassUntil { Tests.afterDraw with step := .postcombatMain }
  Tests.afterDraw.turnNumber Tests.afterDraw.step .nextMain

#guard isPassSequenceCommand "noblock" []

#guard !isPassSequenceCommand "attack" ["3"]

#guard !isPassSequenceAction .concede

#guard passUntilSkipsAttackers .nextTurnCombat

#guard passUntilCommand? Tests.readyToDeclareAttackers == none

#guard passUntilGoalCommand? Tests.readyToDeclareAttackers
    (passUntilGoalAt Tests.readyToDeclareAttackers ⟨0⟩ (.named .nextTurnMain)) ==
  some "noattack"

#guard (passUntilGoalCommand? Tests.readyToDeclareAttackers
    (passUntilGoalAt Tests.readyToDeclareAttackers ⟨1⟩ .ignore)).isNone

#guard
  let named := passUntilGoalAt Tests.afterDraw ⟨0⟩ (.named .nextMain)
  let ign := passUntilGoalAt Tests.afterDraw ⟨0⟩ .ignore
  !named.uninterruptible && ign.uninterruptible &&
    !reachedPassUntilGoal Tests.afterDraw named &&
    reachedPassUntilGoal { Tests.afterDraw with step := .postcombatMain } named

#guard
  match applyKeep Tests.twoBofursSBA ⟨0⟩ [] with
  | .error msg => msg == keepUsage
  | .ok _ => false


#guard
  match applyInteractiveAsActor Tests.afterChandraDeclaresMulligan "keep" [] with
  | .ok g' => (g'.player ⟨1⟩).keptOpeningHand
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.guttersnipeBoltSetup "cast"
      [toString (Tests.handCardNamed Tests.guttersnipeBoltSetup ⟨0⟩ "Lightning Bolt").id] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "begins casting Lightning Bolt")
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.titanEntered "target" ["opponent"] with
  | .ok g' =>
    g'.pending == .none &&
    g'.stack.back!.dividedDamage == #[3]
  | .error _ => false


#guard
  match applyTarget Tests.proposedDecree ⟨1⟩ ["Lightning Bolt"] with
  | .ok g' =>
    g'.stack.back!.targets == #[Target.card Tests.paidBolt.stack.back!.objectId]
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.elkEntered "target"
      [toString (Tests.namedGraveyardCard Tests.elkEntered ⟨0⟩ "Llanowar Elves").id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.hasPriority ⟨0⟩ &&
    g'.stack.back!.targets ==
      #[Target.card (Tests.namedGraveyardCard g' ⟨0⟩ "Llanowar Elves").id]
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.titanPumpReady "activate"
      [toString (Tests.titanSource Tests.titanPumpReady).id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "begins activating Inferno Titan")
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.dunedainReady "activate"
      [toString (Tests.namedPermanent Tests.dunedainReady "Dúnedain Blade").id, "2"] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "begins activating Dúnedain Blade")
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.oliphauntAttackDeclared "target"
      [toString (Tests.namedPermanent Tests.oliphauntAttackDeclared "Gray Ogre").id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.hasPriority ⟨0⟩ &&
    g'.stack.back!.targets ==
      #[Target.permanent (Tests.namedPermanent g' "Gray Ogre").id]
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.ogreVsCrusherReadyToBlock "block" [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Olog-hai Crusher").status.blocking.isEmpty &&
      !(Tests.namedPermanent g' "Gray Ogre").status.blocked
  | .error _ => false


#guard
  match blockAssignmentsForCommand Tests.gollumVsTwoBearsReadyToBlock [] with
  | .ok asgn =>
    let g := Tests.gollumVsTwoBearsReadyToBlock
    let gollum := Tests.namedPermanent g "Gollum, Silent Slinker"
    asgn.size == 2 && asgn.all (fun (_, a) => a == gollum.id)
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.readyToDeclareAttackers "noattack" [] with
  | .ok g' => !(g'.battlefield.any (·.status.attacking))
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.struckerMayConnive "decline" [] with
  | .ok g' =>
    !(Tests.namedPermanent g' "Baron Strucker, HYDRA Overlord").status.optionalOnceUsed &&
      g'.pending == .none &&
      g'.log.any (fun s => Tests.mentions s "declines to have the Villain connive")
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.guideSetup "cast"
      [toString (Tests.handCardNamed Tests.guideSetup ⟨0⟩ "Galadhrim Guide").id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
      g'.log.any (fun s => Tests.mentions s "begins casting Galadhrim Guide")
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.visionarySetup "cast"
      [toString (Tests.handCardNamed Tests.visionarySetup ⟨0⟩ "Elvish Visionary").id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
      g'.log.any (fun s => Tests.mentions s "begins casting Elvish Visionary")
  | .error _ => false


#guard
  let g := Tests.weavemasterReady
  let w := Tests.namedPermanent g "Woodland Weavemaster"
  match applyTap g ⟨0⟩ [toString w.id] with
  | .ok g' =>
    (Tests.namedPermanent g' "Woodland Weavemaster").status.tapped &&
      (g'.player ⟨0⟩).manaPool.elfGreen == 1 &&
      (g'.player ⟨0⟩).manaPool.canPay (ManaCost.ofColor .green) true
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.attercopLandPlayed "pass" [] with
  | .ok g1 =>
    match applyInteractiveAsActor g1 "pass" [] with
    | .ok g' =>
      g'.power (Tests.namedPermanent g' "Attercop") == 3 &&
        g'.toughness (Tests.namedPermanent g' "Attercop") == 2 &&
        g'.log.any (fun s => Tests.mentions s "Attercop gets +1/+1 until end of turn")
    | .error _ => false
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.archAndElves "tap"
      [toString (Tests.namedPermanent Tests.archAndElves "Elvish Archdruid").id] with
  | .ok g' =>
    (g'.player ⟨0⟩).manaPool.green == 2 &&
      (Tests.namedPermanent g' "Elvish Archdruid").status.tapped &&
      g'.log.any (fun s => Tests.mentions s "taps Elvish Archdruid for green ×2")
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.giantReadyToAssign "assign" [] with
  | .ok g' =>
    g'.pending == .none &&
    g'.log.any (fun s => Tests.mentions s "Hill Giant deals 3 combat damage")
  | .error _ => false


#guard
  match applyLoggedAction Tests.targetedBolt "autopay" [] "autopay" with
  | .ok (g', cmds) =>
    cmds == #[tapCommand Tests.boltMountain.id (.colored .red), "pay"] &&
      g'.log.any (fun s => Tests.mentions s "casts Lightning Bolt")
  | .error _ => false


#guard
  match applyMyTurn Tests.afterDraw ⟨0⟩ ["turn", "now"] with
  | .error msg => msg == myTurnUsage
  | .ok _ => false


#guard
  match Tests.nissaDraw.apply ⟨1⟩ .pass with
  | .error _ => false
  | .ok g =>
    match applyLoggedAction g "your" ["turn"] "your turn" with
    | .error msg => msg == "The next turn is yours"
    | .ok _ => false


#guard
  match applyLoggedAction Tests.started "main" ["phase"] "main phase" with
  | .ok (g', cmds) =>
    cmds == #["pass"] &&
      g'.step == .upkeep &&
      g'.turnNumber == 1 &&
      g'.activePlayer == ⟨0⟩ &&
      g'.hasPriority ⟨1⟩ &&
      (goalsAfterCommand Tests.started g' ⟨0⟩ "main" ["phase"] #[]).size == 1
  | .error _ => false


#guard
  match applyLoggedAction Tests.afterDraw "main" ["phase"] "main phase" with
  | .ok (g', cmds) =>
    cmds == #["pass"] &&
      !cmds.contains "main phase" &&
      g'.step == .precombatMain &&
      g'.turnNumber == 1 &&
      g'.activePlayer == ⟨0⟩ &&
      g'.hasPriority ⟨1⟩ &&
      (goalsAfterCommand Tests.afterDraw g' ⟨0⟩ "main" ["phase"] #[]).size == 1
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.afterDraw "attack" ["step"] with
  | .ok g' =>
    g'.step == .precombatMain && g'.hasPriority ⟨1⟩ &&
      g'.pending != .declareAttackers
  | .error _ => false


#guard
  match applyShuffle Tests.norandomOpening [] with
  | .ok g' =>
    match g'.pendingRandom? with
    | some (.shuffleLibrary p) => p == ⟨1⟩ && (g'.player ⟨0⟩).hand.isEmpty
    | _ => false
  | .error _ => false


#guard isFlagLine "--seed 42"

#guard !isFlagLine "visible"


#guard commandsFromLines #["keep\r", "bottom 3 4"] == ["keep", "bottom 3 4"]

#guard (inputScriptFromLines #["--seed 42", "--name Elspeth", "keep"]).flags ==
  ["--seed 42", "--name Elspeth"]

#guard flagTokens ["--visible"] == ["--visible"]

#guard flagTokens [] == []


#guard !sameInputOutput (some "session.txt") none

#guard !shouldWriteInputFlags true ["--visible"]

#guard shouldRecordCommand false true

#guard isNonStateCommand "quit"

#guard !isNonStateCommand "keep"

#guard isCheckSkipCommand "help"

#guard
  match takeStartingPlayer demoSeats false 1 ["keep"] with
  | .ok (1, ["keep"]) => true
  | _ => false


#guard
  match takeStartingPlayer demoSeats true 0 ["keep"] with
  | .error msg => msg == "Choose who takes the first turn (CR 103.1): first <name>"
  | _ => false


#guard
  match replayCompleteGame Tests.started ["pass"] with
  | .error msg => msg == "Game is not complete"
  | .ok _ => false


#guard
  match replayCompleteGame Tests.afterDraw ["your turn", "concede"] with
  | .ok g' =>
    match g'.result with
    | some (.won p) =>
      p == ⟨0⟩ && g'.log.any (fun s => Tests.mentions s "Nissa concedes") &&
        !g'.log.any (fun s => Tests.mentions s "beginning of combat")
    | _ => false
  | .error _ => false


#guard
  match Tests.nissaDraw.apply ⟨1⟩ .pass with
  | .error _ => false
  | .ok g =>
    match replayCompleteGame g ["my turn", "concede"] with
    | .ok g' =>
      match g'.result with
      | some (.won p) => p == ⟨0⟩ && g'.turnNumber == 2 && g'.step == .precombatMain
      | _ => false
    | .error _ => false


#guard
  match replayCompleteGame Tests.afterDraw
      ["ignore", "pass", "pass", "pass", "pass", "concede"] with
  | .ok g' =>
    match g'.result with
    | some (.won p) =>
      p == ⟨1⟩ && g'.log.any (fun s => Tests.mentions s "postcombat main")
    | _ => false
  | .error _ => false

-- `main phase` only passes for the issuer; `noattack` waits until that
-- player is declaring attackers (after the opponent passes).

#guard
  match replayCompleteGame Tests.afterDraw ["ignore", "main phase", "concede"] with
  | .ok g' =>
    g'.over && g'.log.any (fun s => Tests.mentions s "postcombat main") &&
      match g'.result with
      | some (.won p) => p == ⟨1⟩
      | _ => false
  | .error _ => false


#guard describeCheckResult { Tests.started with result := some .draw } == "The game is a draw."

#guard shouldWriteOutput false false true "target"

#guard !shouldWriteOutput false false true "quit"

#guard !shouldWriteOutput false false false "keep"

#guard !shouldAutoPay Tests.targetedBolt ["pay"]

#guard shouldAutoPay Tests.tappedForBolt []

#guard
  let g := Tests.addUntappedLand Tests.targetedBolt Catalog.mountain
  !shouldAutoPay g []

#guard (autoPayStep? Tests.targetedBolt ["pay"]).isNone

#guard !shouldAutoPass Tests.started ["pass"]

#guard
  let g := { Tests.readyToDeclareAttackers with
    objects := Tests.readyToDeclareAttackers.objects.map (fun o =>
      { o with status := { o.status with tapped := true } }) }
  !shouldAutoNoAttack g ["noattack"]

#guard !shouldAutoNoBlock Tests.readyToDeclareBlockers []

#guard !shouldAutoTarget Tests.proposedBolt []

#guard shouldAutoTarget Tests.hospitalityLandPlayed []

#guard targetCommand Tests.proposedBolt ⟨0⟩ (Target.player ⟨0⟩) == "target Chandra"

#guard (autoTargetStep? Tests.proposedSmite ["target opponent"]).isNone

#guard
  match parseWelcomeDeck "white" with
  | .ok .white => true
  | _ => false


#guard looksLikeDeckFile "decks/nissa.txt"

#guard
  match parseDemoDeck "red" with
  | .ok (.welcome .red) => true
  | _ => false


#guard deckAssignmentLine { name := "Alice", deck := .file "alice.txt" } ==
  "Alice uses the deck list alice.txt."


#guard
  match parseArgs ["--multiplayer", "--visible"] with
  | .ok opt => opt.interactive && opt.multiplayer && opt.playerView
  | _ => false


#guard
  match parseArgs ["--interactive"] with
  | .ok opt => opt.inputFile.isNone
  | _ => false


#guard
  match parseArgs ["--auto", "--input", "opening.txt"] with
  | .error msg => msg == "--input requires --interactive or --multiplayer"
  | .ok _ => false


#guard
  match parseArgs ["--constructed"] with
  | .ok opt => opt.constructed && !opt.interactive
  | _ => false


#guard
  match parseArgs ["--check", "--constructed", "--input", "foo.txt"] with
  | .ok opt =>
    opt.constructed &&
      match checkCompleteGame opt demoSeats ["first Chandra", "keep", "keep", "concede"] with
      | .error msg => msg == "Chandra: Deck has 40 cards; minimum is 60"
      | .ok _ => false
  | _ => false


#guard
  match Start.start (demoConfig 1 (constructed := true)) with
  | .error msg => msg == "Chandra: Deck has 40 cards; minimum is 60"
  | .ok _ => false


#guard
  match parseArgs ["--check", "--input", "examples/foo.txt"] with
  | .ok opt =>
    opt.check && opt.interactive && opt.multiplayer &&
      opt.inputFile == some "examples/foo.txt"
  | _ => false


#guard
  match parseArgs ["--interactive"] with
  | .ok opt => !opt.check
  | _ => false


#guard
  match parseArgs ["--check", "--input", "foo.txt"] with
  | .ok opt =>
    match checkCompleteGame opt demoSeats ["keep"] with
    | .error msg =>
      msg == "Choose who takes the first turn (CR 103.1): first <name>"
    | .ok _ => false
  | _ => false


#guard
  match parseArgs ["--interactive"] with
  | .ok opt => opt.outputFile.isNone
  | _ => false


#guard
  match parseArgs ["--interactive", "--input", "session.txt", "--output", "session.txt"] with
  | .ok opt =>
    opt.inputFile == some "session.txt" && opt.outputFile == some "session.txt" &&
    sameInputOutput opt.inputFile opt.outputFile
  | _ => false


#guard
  match parseArgs ["--interactive", "--output"] with
  | .error msg => msg == "Missing output file path"
  | .ok _ => false


#guard
  match parseArgs [
      "--name", "Elspeth", "--name", "Jace", "--name", "Liliana",
      "--deck", "W", "--deck", "U", "--deck", "B"] with
  | .ok opt => opt.players == elspethJaceLiliana
  | _ => false


#guard
  match parseArgs ["--deck", "gold", "--name", "Elspeth", "--name", "Jace", "--deck", "blue"] with
  | .error msg =>
    msg == "Unknown Welcome Deck: gold (white, blue, black, red, or green, or a deck list file)"
  | .ok _ => false


#guard
  match parseArgs ["--name"] with
  | .error msg => msg == "Missing player name"
  | .ok _ => false


#guard
  match parseArgs ["--name", "Elspeth", "--deck", "white"] with
  | .error msg => msg == "A game needs at least two players (CR 100.1)"
  | .ok _ => false


#guard
  match parseArgs ["--decides", "Nissa"] with
  | .ok opt => !opt.interactive && opt.decides == some 1 && opt.players == defaultDemoPlayers
  | _ => false


#guard
  match parseArgs [
      "--name", "Elspeth", "--deck", "white",
      "--name", "Jace", "--deck", "blue",
      "--decides", "Jace"] with
  | .ok opt => opt.players == elspethJace && opt.decides == some 1
  | _ => false


#guard
  match parseArgs ["--decides"] with
  | .error msg => msg == "Missing player name for --decides"
  | .ok _ => false


#guard
  match parseArgsWithFlags
      ["--interactive", "--input", "opening.txt"] ["--seed 42"] with
  | .ok opt => opt.seed == 42 && opt.interactive
  | _ => false


#guard
  match parseArgsWithFlags
      ["--interactive", "--input", "opening.txt"] ["--multiplayer"] with
  | .ok opt => opt.interactive && opt.multiplayer
  | _ => false


#guard
  match parseArgsWithFlags
      ["--interactive", "--name", "Chandra", "--deck", "red",
        "--name", "Nissa", "--deck", "green", "--input", "opening.txt"]
      ["--name Elspeth --deck white", "--name Jace --deck blue"] with
  | .ok opt => opt.players == elspethJace
  | _ => false


#guard
  match parseDecider defaultDemoPlayers ["frodo"] with
  | .error msg => msg == "No player named frodo"
  | .ok _ => false

