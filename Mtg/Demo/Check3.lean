import Mtg.Demo
import Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Demo
open Mtg.Demo.Render

#guard
  match parsePlayerName demoSeats "nissa" with
  | .ok 1 => true
  | _ => false


#guard assignDecider defaultDemoPlayers 1 none == assignDecider defaultDemoPlayers 1 none

#guard !humanChoosesFirst true false 1

#guard describeFirstChooser defaultDemoPlayers 0 true ==
  "Chandra is chosen at random to decide who takes the first turn (CR 103.1)."

#guard
  match parseFirstPlayer demoSeats ["Chandra"] with
  | .ok 0 => true
  | _ => false


#guard
  match parseFirstPlayer demoSeats [] with
  | .error msg => msg == firstUsage demoSeats
  | .ok _ => false


#guard demoSeats[0]!.deck.any (fun c => c.name == "Smaug, the Great Calamity")

#guard (seatsFromPlayers elspethJace)[0]!.deck.any (fun c => c.name == "Bofur, Reliable Guardian")

#guard (seatsFromPlayers #[
    { name := "Nissa", deck := .welcome .green },
    { name := "Elspeth", deck := .welcome .white }])[0]!.deck.any
  (fun c => c.name == "Elvish Archdruid")

#guard (duplicatePlayerName? defaultDemoPlayers).isNone

#guard
  match playersFromFlags #["Elspeth"] #[.welcome .white] with
  | .error msg => msg == "A game needs at least two players (CR 100.1)"
  | .ok _ => false


#guard
  match Start.start (demoConfig 1 (some 0) elspethJaceLiliana) with
  | .ok g =>
    g.players.size == 3 &&
    (g.player ⟨0⟩).name == "Elspeth" &&
    (g.player ⟨1⟩).name == "Jace" &&
    (g.player ⟨2⟩).name == "Liliana" &&
    g.isMultiplayer &&
    g.freeFirstMulligan &&
    g.objects.any (fun o => o.name == "Bofur, Reliable Guardian") &&
    g.objects.any (fun o => o.name == "Bilbo Baggins, Burglar") &&
    g.objects.any (fun o => o.name == "Gollum, Silent Slinker") &&
    !g.objects.any (fun o => o.name == "Smaug, the Great Calamity")
  | .error _ => false

-- CR 103.5c: three-player Welcome Decks treat the first mulligan as free.

#guard ((helpInteractive false).splitOn "the first player can see").length > 1

#guard ((helpInteractive false).splitOn "scry bottom").length > 1

#guard ((helpInteractive false).splitOn "CR 601.2d").length > 1

#guard ((helpInteractive false).splitOn "activate <id> [n]").length > 1

#guard ((helpInteractive false).splitOn "first <name>").length > 1

#guard ((helpInteractive false).splitOn "CR 704.5j").length > 1

#guard ((helpInteractive false).splitOn "Choose to discard as an additional cost").length > 1

#guard ((helpInteractive false).splitOn "connive").length > 1

#guard ((helpInteractive false).splitOn "autopay").length > 1

#guard ((helpInteractive false).splitOn "main phase").length > 1

#guard ((helpInteractive false).splitOn "attack [id...] [at] <name|opponent>").length > 1

#guard ((helpInteractive false).splitOn "CR 601.2g").length > 1

#guard (usage.splitOn "--output FILE").length > 1

#guard (usage.splitOn "Flags from --input are written first").length > 1

#guard (usage.splitOn "individual pass commands they perform").length > 1

#guard (usage.splitOn "Incorrect commands and session commands").length > 1

#guard (usage.splitOn "--deck FILE").length > 1

#guard (usage.splitOn "--norandom").length > 1

#guard ((helpInteractive false).splitOn "flip heads").length > 1

#guard (helpChooseFirst.splitOn "first <name>").length > 1

#guard parseManaType? "white" == some (.colored .white)

#guard splitAtKeyword "bottom" ["bottom", "3"] == ([], some ["3"])


#guard
  match parseObjectIds ["3", "#7"] attackUsage with
  | .ok ids => ids == #[⟨3⟩, ⟨7⟩]
  | .error _ => false

#guard
  let g := Tests.readyToDeclareAttackers
  let bears := Tests.namedPermanent g "Grizzly Bears"
  match applyAttack g ⟨0⟩ [toString bears.id] with
  | .ok g' =>
    (Tests.namedPermanent g' "Grizzly Bears").status.attacking &&
    (Tests.namedPermanent g' "Grizzly Bears").status.attackingWhom == some ⟨1⟩ &&
    !(Tests.namedPermanent g' "Gray Ogre").status.attacking
  | .error _ => false


#guard
  match applyAttack Tests.readyToDeclareAttackers ⟨0⟩ ["99999"] with
  | .error msg => msg == "no such object"
  | .ok _ => false


#guard
  let g := Tests.threeTwoOgresReady
  let ogres := g.battlefield.filter (·.name == "Gray Ogre")
  match applyAttack g ⟨0⟩
      [toString ogres[0]!.id, "Nissa", toString ogres[1]!.id, "Liliana"] with
  | .ok g' =>
    let after := g'.battlefield.filter (·.name == "Gray Ogre")
    after[0]!.status.attackingWhom == some ⟨1⟩ &&
      after[1]!.status.attackingWhom == some ⟨2⟩
  | .error _ => false


#guard
  match parseBlockAssignments ["12"] with
  | .error msg => msg == blockUsage
  | .ok _ => false


#guard
  match applyBlock Tests.readyToDeclareBlockers ⟨1⟩ [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Grizzly Bears").status.blocking ==
      #[(Tests.namedPermanent g' "Gray Ogre").id]
  | .error _ => false


#guard
  match blockAssignmentsForCommand Tests.ogreVsCrusherReadyToBlock [] with
  | .ok asgn => asgn.isEmpty
  | .error _ => false


#guard
  match parseCombatAssignments Tests.started ⟨0⟩ [] with
  | .ok asgns => asgns.isEmpty
  | .error _ => false


#guard
  match parseCombatAssignments Tests.giantReadyToAssign ⟨0⟩ ["3", "Chandra", "2"] with
  | .error msg => msg == assignUsage
  | .ok _ => false


#guard
  let g := Tests.giantReadyToAssign
  let giant := Tests.namedPermanent g "Hill Giant"
  let elves := g.battlefield.filter (fun o => o.name == "Llanowar Elves")
  match applyAssign g ⟨0⟩
      [toString giant.id, toString elves[0]!.id, "1",
        toString giant.id, toString elves[1]!.id, "2"] with
  | .ok g' => (g'.battlefield.filter (fun o => o.name == "Llanowar Elves")).isEmpty
  | .error _ => false


#guard
  match applyBottom Tests.afterChandraMulligan ⟨0⟩ ["99999"] with
  | .error msg => msg == "no such object"
  | .ok _ => false


#guard
  match applyVisible [] with
  | .ok none => true
  | _ => false


#guard
  match applyVisible ["on", "off"] with
  | .error msg => msg == visibleUsage
  | .ok _ => false


#guard (currentView Tests.nissaDraw true true) == some ⟨1⟩

#guard
  match actingPlayer Tests.nissaDraw with
  | .ok p => p == ⟨1⟩
  | .error _ => false


#guard
  match applyTap Tests.baubleReady ⟨0⟩ ["nope"] with
  | .error msg => msg == tapUsage
  | .ok _ => false


#guard
  let g := Tests.hiddenLairEntered
  let lair := Tests.namedPermanent g "Hidden Lair"
  match applyTap g ⟨0⟩ [toString lair.id, "U"] with
  | .ok g' =>
    (Tests.namedPermanent g' "Hidden Lair").status.tapped &&
    (g'.player ⟨0⟩).manaPool.canPay (ManaCost.ofColor .blue)
  | .error _ => false


#guard
  let g := Tests.baubleReady
  let lands := (g.permanentsOf ⟨0⟩).filter (·.printed.isLand)
  lands.size == 2 &&
  match applyTap g ⟨0⟩ [toString lands[0]!.id, s!"{lands[1]!.id.raw}"] with
  | .ok g' =>
    (g'.battlefield.filter (fun o => o.printed.isLand && o.status.tapped)).size == 2 &&
    (g'.player ⟨0⟩).manaPool.canPay (ManaCost.ofGeneric 2)
  | .error _ => false


#guard
  match applyPlay Tests.afterDraw ⟨0⟩ ["nope"] with
  | .error msg => msg == playUsage
  | .ok _ => false


#guard
  match applyPayExtra Tests.stirChooseAdditional ⟨0⟩ [] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "chooses to pay {4} as an additional cost")
  | .error _ => false


#guard
  match applyPayExtra Tests.proposedTitania ⟨0⟩ [] with
  | .ok g' =>
    match g'.proposedSpell with
    | some prop => !prop.needsDiscardCard &&
        prop.cost.manaValue == Catalog.titaniaRuggedRumbler.manaValue + 2
    | none => false
  | .error _ => false


#guard
  match applyActivate Tests.baubleReady ⟨0⟩ ["1", "0"] with
  | .error msg => msg == activateUsage
  | .ok _ => false


#guard
  let g := Tests.baubleReady
  let bauble := Tests.baubleSource g
  match applyActivate g ⟨0⟩ [toString bauble.id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "begins activating Wayfarer's Bauble")
  | .error _ => false


#guard
  let g := Tests.dunedainReady
  let blade := Tests.namedPermanent g "Dúnedain Blade"
  match applyActivate g ⟨0⟩ [toString blade.id, "2"] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "begins activating Dúnedain Blade")
  | .error _ => false


#guard
  match applySacrifice Tests.hunterReady ⟨0⟩ ["nope"] with
  | .error msg => msg == sacrificeUsage
  | .ok _ => false


#guard
  let g := Tests.paidHunter
  let fodder := Tests.hunterFodder g
  match applySacrifice g ⟨0⟩ [toString fodder.id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.log.any (fun s => Tests.mentions s "sacrifices Raging Goblin") &&
    g'.log.any (fun s => Tests.mentions s "activates Snowslope Hunter")
  | .error _ => false


#guard
  match applyMode Tests.proposedCratermaker ⟨0⟩ ["nope"] with
  | .error msg => msg == modeUsage
  | .ok _ => false


#guard
  match applyMode Tests.proposedCratermaker ⟨0⟩ ["2"] with
  | .error msg => Tests.mentions msg "requires a target"
  | .ok _ => false


#guard
  match applyX Tests.proposedStature ⟨0⟩ ["3"] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
      (g'.object! g'.stack.back!.objectId).chosenX == some 3 &&
      g'.log.any (fun s => Tests.mentions s "chooses X = 3")
  | .error _ => false


#guard
  match applyCast Tests.boltSetup ⟨0⟩ ["nope"] with
  | .error msg => msg == castUsage
  | .ok _ => false


#guard
  match applyCast Tests.boltSetup ⟨0⟩ [toString Tests.boltInHand.id] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.stack.back!.targets.isEmpty &&
    g'.log.any (fun s => Tests.mentions s "begins casting Lightning Bolt") &&
    g'.log.any (fun s => Tests.mentions s "must choose a target (CR 601.2c)")
  | .error _ => false


#guard
  match applyCast Tests.fireOfOrthancSetup ⟨0⟩
      [toString (Tests.handCardNamed Tests.fireOfOrthancSetup ⟨0⟩ "Fire of Orthanc").id] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.stack.back!.targets.isEmpty &&
    g'.log.any (fun s => Tests.mentions s "begins casting Fire of Orthanc") &&
    g'.log.any (fun s => Tests.mentions s "must choose a target (CR 601.2c)")
  | .error _ => false


#guard
  match applyTarget Tests.proposedBolt ⟨0⟩ ["nope"] with
  | .error msg => msg == targetUsage
  | .ok _ => false


#guard
  match applyTarget Tests.proposedBolt ⟨0⟩ ["Nissa"] with
  | .ok g' => g'.stack.back!.targets == #[Target.player ⟨1⟩]
  | .error _ => false


#guard
  match applyTarget Tests.gandalfEntered ⟨0⟩ [] with
  | .error msg => msg == divideTargetUsage
  | .ok _ => false


#guard
  match applyTarget Tests.proposedQuarrel ⟨0⟩ ["Llanowar Elves", "Grizzly Bears"] with
  | .error msg => msg == sequentialTargetUsage
  | .ok _ => false


#guard
  match applyCast Tests.meagerMealSetup ⟨0⟩
      [toString (Tests.handCardNamed Tests.meagerMealSetup ⟨0⟩
        "Gollum, Silent Slinker").id, "adventure"] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    (g'.object! g'.stack.back!.objectId).name == "Meager Meal" &&
    g'.log.any (fun s => Tests.mentions s "begins casting Meager Meal") &&
    g'.log.any (fun s => Tests.mentions s "must choose a target (CR 601.2c)")
  | .error _ => false


#guard
  match applyTarget Tests.proposedMeagerMeal ⟨0⟩ ["Grizzly Bears"] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.stack.back!.targets ==
      #[Target.permanent (Tests.namedPermanent g' "Grizzly Bears").id] &&
    match applyTarget g' ⟨0⟩ ["Chandra"] with
    | .ok g'' =>
      g''.pending == .activateManaAbilities ⟨0⟩ &&
      g''.stack.back!.targets ==
        #[Target.permanent (Tests.namedPermanent g'' "Grizzly Bears").id,
          Target.player ⟨0⟩]
    | .error _ => false
  | .error _ => false


#guard
  match applyMode Tests.proposedWarg ⟨0⟩ ["nope"] with
  | .error msg => msg == modeUsage
  | .ok _ => false


#guard
  match applyMode Tests.proposedWarg ⟨0⟩ ["1"] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.stack.back!.chosenMode == some 0 &&
    g'.log.any (fun s => Tests.mentions s "chooses mode 1")
  | .error _ => false


#guard
  match applyScry Tests.giftScrying ⟨0⟩ ["keep"] with
  | .error msg => msg == scryUsage
  | .ok _ => false


#guard
  let g := Tests.giftKnownScrying
  let looked := g.scryLookedIds ⟨0⟩ 2
  match looked[0]? with
  | some forest =>
    match applyScry g ⟨0⟩ ["top", toString forest] with
    | .ok g' =>
      (g'.object! (g'.player ⟨0⟩).library.back!).name == "Forest" &&
        (g'.object! (g'.player ⟨0⟩).library[0]!).name == "Llanowar Elves"
    | .error _ => false
  | none => false


#guard
  match applyDiscard Tests.spearMayDiscard ⟨0⟩ ["1", "2"] with
  | .error msg => msg == discardUsage
  | .ok _ => false


#guard
  match applyConniveChoice Tests.struckerMayConnive ⟨0⟩ [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Baron Strucker, HYDRA Overlord").status.optionalOnceUsed &&
      (g'.player ⟨0⟩).hand.size == (Tests.struckerMayConnive.player ⟨0⟩).hand.size + 1 &&
      g'.log.any (fun s => Tests.mentions s "connives")
  | .error _ => false


#guard
  match applyDecline Tests.proposedMeagerMeal ⟨0⟩ [] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.stack.back!.targets.isEmpty &&
    g'.log.any (fun s => Tests.mentions s "chooses no target")
  | .error _ => false


#guard
  match applyAttach Tests.vowMayAttach ⟨0⟩ ["99999"] with
  | .error msg => msg == "no such object"
  | .ok _ => false


#guard
  let g := Tests.vowMayAttach
  let spear := Tests.namedPermanent g "Ragged Short Spear"
  match applyAttach g ⟨0⟩ [toString spear.id] with
  | .ok g' =>
    g'.pending == .none &&
    (Tests.namedPermanent g' "Ragged Short Spear").attachedTo ==
      some (Tests.namedPermanent g' "Bofur, Reliable Guardian").id &&
    g'.log.any (fun s => Tests.mentions s "attaches to Bofur")
  | .error _ => false


#guard
  match applyAutopay Tests.targetedBolt ⟨0⟩ ["extra"] with
  | .error msg => msg == autopayUsage
  | .ok _ => false


#guard
  match applyAutopay Tests.targetedBolt ⟨0⟩ [] with
  | .ok r =>
    r.commands == #[tapCommand Tests.boltMountain.id (.colored .red), "pay"] &&
      r.game.pending == .none &&
      r.game.proposedSpell.isNone &&
      (r.game.player ⟨0⟩).manaPool.isEmpty &&
      r.game.log.any (fun s => Tests.mentions s "casts Lightning Bolt")
  | .error _ => false


#guard
  let g0 := Tests.weavemasterElfSetup.emptyManaPools
  let elves := Tests.handCardNamed g0 ⟨0⟩ "Llanowar Elves"
  match g0.apply ⟨0⟩ (.cast elves.id) with
  | .error _ => false
  | .ok proposed =>
    let w := Tests.namedPermanent proposed "Woodland Weavemaster"
    match applyAutopay proposed ⟨0⟩ [] with
    | .ok r =>
      r.commands == #[tapCommand w.id (.colored .green), "pay"] &&
        (Tests.namedPermanent r.game "Woodland Weavemaster").status.tapped &&
        r.game.log.any (fun s => Tests.mentions s "casts Llanowar Elves")
    | .error _ => false


#guard
  match applyAutopay Tests.delightedHalflingGrowth ⟨0⟩ [] with
  | .error msg =>
    Tests.mentions msg "cannot pay" &&
      !(Tests.namedPermanent Tests.delightedHalflingGrowth "Delighted Halfling").status.tapped
  | .ok _ => false


#guard
  match applyAutopay Tests.hiddenLairPayingDeathlok ⟨0⟩ [] with
  | .ok r =>
    let lair := Tests.namedPermanent Tests.hiddenLairPayingDeathlok "Hidden Lair"
    r.commands == #[tapCommand lair.id (.colored .black), "pay"] &&
      (Tests.namedPermanent r.game "Hidden Lair").status.tapped &&
      r.game.log.any (fun s => Tests.mentions s "casts Project Deathlok Soldier")
  | .error _ => false


#guard nextTurnPlayer Tests.afterDraw == ⟨1⟩

#guard isPassShortcut "main" ["phase"]

#guard !isPassShortcut "attack" []

#guard isPassShortcutCmd "ignore" []

#guard !reachedPassUntil { Tests.afterDraw with step := .beginningOfCombat }
  Tests.afterDraw.turnNumber Tests.afterDraw.step .nextDeclareAttackers

#guard
  let goal := passUntilGoalAt Tests.afterDraw ⟨0⟩ .ignore
  !reachedIgnore Tests.afterDraw goal &&
    reachedIgnore { Tests.afterDraw with step := .postcombatMain } goal &&
    !reachedIgnore { Tests.afterDraw with
      turnNumber := 2, activePlayer := ⟨1⟩, step := .precombatMain } goal &&
    reachedIgnore { Tests.afterDraw with
      turnNumber := 3, activePlayer := ⟨0⟩, step := .precombatMain } goal

#guard isPassSequenceCommand "main" ["phase"]

#guard isPassSequenceAction .pass

#guard shortcutKind? "main" ["phase"] == some (.named .nextMain)

#guard passUntilSkipsAttackers .nextTurnMain

#guard passUntilCommand? Tests.readyToDeclareAttackers false true == some "noattack"

#guard (passUntilGoalCommand? Tests.readyToDeclareAttackers
    (passUntilGoalAt Tests.readyToDeclareAttackers ⟨1⟩
      (.named .nextTurnCombat))).isNone

#guard passUntilGoalCommand? Tests.readyToDeclareAttackers
    (passUntilGoalAt Tests.readyToDeclareAttackers ⟨0⟩ .ignore) ==
  some "noattack"

#guard
  let chandra := passUntilGoalAt Tests.afterDraw ⟨0⟩ (.named .nextMain)
  let kept := interruptPassUntilGoals #[chandra] ⟨1⟩
  kept.isEmpty &&
    (interruptPassUntilGoals #[passUntilGoalAt Tests.afterDraw ⟨0⟩ .ignore] ⟨1⟩).size == 1


#guard
  match Tests.twoBofursSBA.pending with
  | .chooseLegend _ _ ids =>
    match applyInteractiveAsActor Tests.twoBofursSBA "keep" [toString ids[0]!] with
    | .ok g' =>
      (g'.battlefield.filter (·.name == "Bofur, Reliable Guardian")).size == 1 &&
      g'.log.any (fun s => Tests.mentions s "704.5j")
    | .error _ => false
  | _ => false


#guard
  match applyInteractiveAsActor Tests.nissaDraw "pass" [] with
  | .ok g' => g'.hasPriority ⟨0⟩ && g'.actor == some ⟨0⟩
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.paidGuttersnipeBolt "pass" [] with
  | .ok g1 =>
    match applyInteractiveAsActor g1 "pass" [] with
    | .ok g' =>
      (g'.player ⟨1⟩).life == 18 &&
      g'.stack.size == 1 &&
      (g'.object! g'.stack.back!.objectId).name == "Lightning Bolt"
    | .error _ => false
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.titanAttackDeclared "target" ["opponent"] with
  | .ok g' =>
    g'.pending == .none &&
    g'.stack.back!.dividedDamage == #[3]
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.proposedDecree "target"
      [toString Tests.paidBolt.stack.back!.objectId] with
  | .ok g' =>
    g'.stack.back!.targets == #[Target.card Tests.paidBolt.stack.back!.objectId]
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.elkEntered "target" ["Llanowar Elves"] with
  | .ok g' =>
    g'.stack.back!.targets ==
      #[Target.card (Tests.namedGraveyardCard Tests.elkEntered ⟨0⟩ "Llanowar Elves").id]
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.passageReady "activate"
      [toString (Tests.passageSource Tests.passageReady).id] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "begins activating Rogue's Passage")
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.oliphauntCycleReady "activate"
      [toString (Tests.handCardNamed Tests.oliphauntCycleReady ⟨0⟩ "Oliphaunt").id] with
  | .ok g' =>
    g'.pending == .activateManaAbilities ⟨0⟩ &&
    g'.log.any (fun s => Tests.mentions s "begins activating Oliphaunt")
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.oliphauntAttackDeclared "decline" [] with
  | .error msg => Tests.mentions msg "requires a target"
  | .ok _ => false


#guard
  match applyInteractiveAsActor Tests.ogreVsCrusherAndGoblinReadyToBlock "block" [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Olog-hai Crusher").status.blocking ==
      #[(Tests.namedPermanent g' "Gray Ogre").id]
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.gollumVsTwoBearsReadyToBlock "block" [] with
  | .ok g' =>
    (Tests.namedPermanent g' "Gollum, Silent Slinker").status.blocked &&
      (g'.battlefield.filter (fun o =>
        o.name == "Grizzly Bears" && o.status.blocking ==
          #[(Tests.namedPermanent g' "Gollum, Silent Slinker").id])).size == 2
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.giftScrying "scry" [] with
  | .ok g' => g'.pending == .none && g'.hasPriority ⟨0⟩
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.vowMayAttach "attach"
      [toString (Tests.namedPermanent Tests.vowMayAttach "Ragged Short Spear").id] with
  | .ok g' =>
    g'.pending == .none &&
    g'.hasPriority ⟨0⟩ &&
    (Tests.namedPermanent g' "Ragged Short Spear").attachedTo ==
      some (Tests.namedPermanent g' "Bofur, Reliable Guardian").id &&
    g'.log.any (fun s => Tests.mentions s "attaches to Bofur")
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.guideScrying "scry" [] with
  | .ok g' =>
    g'.pending == .none && g'.hasPriority ⟨0⟩ &&
      g'.battlefield.any (fun o => o.name == "Galadhrim Guide")
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.visionaryKnownLib "pass" [] with
  | .ok g1 =>
    match applyInteractiveAsActor g1 "pass" [] with
    | .ok g' =>
      g'.stack.isEmpty &&
      g'.log.any (fun s => Tests.mentions s "draws Forest") &&
      (g'.handObjects ⟨0⟩).any (fun o => o.name == "Forest")
    | .error _ => false
  | .error _ => false


#guard
  let g := Tests.weavemasterReady
  let w := Tests.namedPermanent g "Woodland Weavemaster"
  match applyTap g ⟨0⟩ [toString w.id, "W"] with
  | .ok g' =>
    (g'.player ⟨0⟩).manaPool.elfWhite == 1 &&
      (g'.player ⟨0⟩).manaPool.green == 0
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.weavemasterAttackDeclared "pass" [] with
  | .ok g' =>
    !(Tests.namedPermanent g' "Woodland Weavemaster").status.tapped &&
      (Tests.namedPermanent g' "Woodland Weavemaster").status.attacking
  | .error _ => false


#guard
  match applyInteractiveAsActor Tests.proposedWarg "mode" ["1"] with
  | .ok g' =>
    g'.pending == .chooseTargets ⟨0⟩ &&
    g'.stack.back!.chosenMode == some 0
  | .error _ => false


#guard
  let g := Tests.giftKnownScrying
  let looked := g.scryLookedIds ⟨0⟩ 2
  match looked[0]?, looked[1]? with
  | some forest, some elves =>
    match applyInteractiveAsActor g "scry" ["top", toString elves, toString forest] with
    | .ok g' => (g'.object! (g'.player ⟨0⟩).library.back!).name == "Forest"
    | .error _ => false
  | _, _ => false


#guard
  match applyLoggedAction Tests.drawnHands "keep" [] "keep" with
  | .ok (_, cmds) => cmds == #["keep"]
  | .error _ => false


#guard
  match applyMainPhase Tests.afterDraw ⟨0⟩ ["phase", "now"] with
  | .error msg => msg == mainPhaseUsage
  | .ok _ => false


#guard
  match applyLoggedAction Tests.readyToDeclareAttackers "your" ["turn"] "your turn" with
  | .ok (g', cmds) =>
    cmds == #["noattack", "pass"] &&
      g'.step == .declareAttackers &&
      g'.turnNumber == 1 &&
      g'.activePlayer == ⟨0⟩ &&
      g'.hasPriority ⟨1⟩ &&
      (goalsAfterCommand Tests.readyToDeclareAttackers g' ⟨0⟩ "your" ["turn"] #[]).size == 1
  | .error _ => false


#guard
  match applyLoggedAction Tests.afterDraw "attack" ["step"] "attack step" with
  | .ok (g', cmds) =>
    cmds == #["pass"] &&
      !cmds.contains "attack step" &&
      g'.step == .precombatMain &&
      g'.turnNumber == 1 &&
      g'.activePlayer == ⟨0⟩ &&
      g'.hasPriority ⟨1⟩ &&
      (goalsAfterCommand Tests.afterDraw g' ⟨0⟩ "attack" ["step"] #[]).size == 1
  | .error _ => false


#guard
  match applyLoggedAction Tests.afterDraw "your" ["turn"] "your turn" with
  | .ok (g', cmds) =>
    cmds == #["pass"] &&
      !cmds.contains "your turn" &&
      g'.step == .precombatMain &&
      g'.turnNumber == 1 &&
      g'.activePlayer == ⟨0⟩ &&
      g'.hasPriority ⟨1⟩ &&
      (goalsAfterCommand Tests.afterDraw g' ⟨0⟩ "your" ["turn"] #[]).size == 1
  | .error _ => false


#guard
  match applyIgnore Tests.afterDraw ⟨0⟩ ["now"] with
  | .error msg => msg == ignoreUsage
  | .ok _ => false


#guard
  match applyInteractiveAsActor Tests.norandomOpening "shuffle" [] with
  | .ok g1 =>
    match applyInteractiveAsActor g1 "shuffle" [] with
    | .ok g2 =>
      g2.pending == .declareMulligan ⟨0⟩ &&
        (g2.player ⟨0⟩).hand.size == 7 &&
        (g2.player ⟨1⟩).hand.size == 7
    | .error _ => false
  | .error _ => false


#guard isFlagLine "--name Elspeth --deck white"

#guard commandsFromLines #["keep", "pass"] == ["keep", "pass"]

#guard commandsFromLines #["--visible", "keep", "pass"] == ["keep", "pass"]

#guard (inputScriptFromLines #["keep", "--visible", "pass"]).flags == ["--visible"]

#guard flagTokens ["--seed 42", "--visible"] == ["--seed", "42", "--visible"]

#guard sameInputOutput (some "session.txt") (some "session.txt")

#guard !sameInputOutput none none


#guard !shouldWriteInputFlags false []

#guard shouldRecordCommand true false

#guard isNonStateCommand "exit"

#guard !isNonStateCommand "pass"

#guard isCheckSkipCommand "visible"

#guard
  match takeStartingPlayer demoSeats true 0 ["first Chandra", "keep"] with
  | .ok (0, ["keep"]) => true
  | _ => false


#guard
  match replayCompleteGame Tests.started ["concede"] with
  | .ok g' =>
    match g'.result with
    | some (.won p) => p == ⟨1⟩
    | _ => false
  | .error _ => false


#guard
  match replayCompleteGame Tests.started ["concede", "pass"] with
  | .error msg => msg == "Unused command after the game ended: pass"
  | .ok _ => false


#guard
  match replayCompleteGame Tests.afterDraw ["your turn", "pass", "concede"] with
  | .ok g' =>
    g'.over &&
      g'.log.any (fun s => Tests.mentions s "beginning of combat") &&
      match g'.result with
      | some (.won p) => p == ⟨0⟩
      | _ => false
  | .error _ => false


#guard
  match replayCompleteGame Tests.afterDraw ["ignore", "concede"] with
  | .ok g' =>
    match g'.result with
    | some (.won p) => p == ⟨0⟩ && g'.log.any (fun s => Tests.mentions s "Nissa concedes")
    | _ => false
  | .error _ => false


#guard
  let g0 := passBoth (skipTo Tests.ogreVsBears .precombatMain 80)
  match applyLoggedAction g0 "main" ["phase"] "main phase" with
  | .ok (g1, cmds) =>
    cmds == #["pass"] &&
      g1.step == .beginningOfCombat &&
      g1.hasPriority ⟨1⟩ &&
      (goalsAfterCommand g0 g1 ⟨0⟩ "main" ["phase"] #[]).size == 1 &&
      match replayCompleteGame g0 ["main phase", "pass", "concede"] with
      | .ok g' =>
        g'.over && g'.log.any (fun s => Tests.mentions s "does not attack") &&
          match g'.result with
          | some (.won p) => p == ⟨0⟩
          | _ => false
      | .error _ => false
  | .error _ => false

-- Chandra's `main phase` after declaring attackers only passes for her;
-- Nissa still has priority. Nissa's `main phase` can then accept empty
-- combat and both shortcuts resume to postcombat.

#guard
  match applyLoggedAction Tests.readyToDeclareBlockers "main" ["phase"] "main phase" with
  | .error msg => msg == "A player must take an action other than pass"
  | .ok _ => false


#guard describeCheckResult Tests.started == "Game is not complete"


#guard shouldWriteOutput false true true "pass"

#guard !shouldWriteOutput false false true "exit"

#guard !shouldWriteOutput false false false "first"

#guard !shouldAutoPay Tests.started []

#guard shouldAutoPay Tests.proposedHunter []

#guard
  let g := Tests.addUntappedLand Tests.targetedBolt Catalog.forest
  shouldAutoPay g []

#guard
  match autoPayStep? Tests.targetedBolt [], applyAutopay Tests.targetedBolt ⟨0⟩ [] with
  | some (.ok (g', cmds)), .ok r =>
    cmds == r.commands && g'.pending == .none &&
      cmds == #[tapCommand Tests.boltMountain.id (.colored .red), "pay"] &&
      g'.log.any (fun s => Tests.mentions s "casts Lightning Bolt")
  | _, _ => false

#guard !shouldAutoPass { Tests.started with step := .precombatMain } []

#guard !shouldAutoNoAttack Tests.readyToDeclareAttackers []


#guard shouldAutoNoBlock Tests.gollumVsOneBearReadyToBlock []


#guard !shouldAutoTarget Tests.proposedPassage []

#guard shouldAutoTarget Tests.galionAttackDeclared []

#guard
  let tid := (Tests.namedPermanent Tests.proposedSmite "Grizzly Bears").id
  soleLegalTarget? Tests.proposedSmite == some (Target.permanent tid) &&
    targetCommand Tests.proposedSmite ⟨0⟩ (Target.permanent tid) == s!"target {tid}"

#guard
  let tid := (Tests.namedPermanent Tests.proposedSmite "Grizzly Bears").id
  match autoTargetStep? Tests.proposedSmite [] with
  | some (.ok (g', cmd)) =>
    cmd == s!"target {tid}" &&
      g'.stack.back!.targets == #[Target.permanent tid] &&
      g'.log.any (fun s => Tests.mentions s "chooses Grizzly Bears as a target (CR 601.2c)")
  | _ => false

#guard
  match parseWelcomeDeck "U" with
  | .ok .blue => true
  | _ => false


#guard looksLikeDeckFile "./red"

#guard
  match parseDemoDeck "decks/nissa.txt" with
  | .ok (.file "decks/nissa.txt") => true
  | _ => false


#guard
  match parseArgs ["--interactive", "--visible"] with
  | .ok opt => opt.interactive && !opt.multiplayer && opt.playerView
  | _ => false


#guard
  match parseArgs ["--interactive", "--multiplayer"] with
  | .ok opt => opt.interactive && opt.multiplayer
  | _ => false


#guard
  match parseArgs ["--interactive", "--input", "opening.txt"] with
  | .ok opt => opt.interactive && !opt.multiplayer && opt.inputFile == some "opening.txt"
  | _ => false


#guard
  match parseArgs ["--norandom"] with
  | .ok opt => opt.norandom && !opt.interactive
  | _ => false


#guard
  match parseArgs ["--interactive", "--constructed"] with
  | .ok opt => opt.constructed && opt.interactive
  | _ => false


#guard (demoConfig 1).format == .limited

#guard
  match Start.start {
      seats := #[
        { name := "Alice", deck := Catalog.copies 60 Catalog.mountain },
        { name := "Bob", deck := Catalog.copies 60 Catalog.forest }
      ]
      format := demoFormat true
      seed := 1
      startingPlayer := some 0 } with
  | .ok g => g.format == .constructed
  | .error _ => false


#guard
  match parseArgs ["--check"] with
  | .error msg => msg == "--check requires --input"
  | .ok _ => false


#guard
  match parseArgsWithFlags ["--check", "--input", "foo.txt"] ["--multiplayer"] with
  | .ok opt => opt.check && opt.multiplayer
  | _ => false


#guard
  match parseArgs ["--check", "--input", "foo.txt"] with
  | .ok opt =>
    match checkCompleteGame opt demoSeats ["first Chandra", "keep", "keep"] with
    | .error msg => msg == "Game is not complete"
    | .ok _ => false
  | _ => false


#guard
  match parseArgs ["--interactive", "--output", "session.txt"] with
  | .ok opt => opt.interactive && !opt.multiplayer && opt.outputFile == some "session.txt"
  | _ => false


#guard
  match parseArgs ["--multiplayer", "--input", "session.txt", "--output", "session.txt"] with
  | .ok opt =>
    opt.interactive && opt.multiplayer &&
    sameInputOutput opt.inputFile opt.outputFile
  | _ => false


#guard
  match parseArgs ["--interactive", "--output", "--visible"] with
  | .error msg => msg == "Missing output file path"
  | .ok _ => false


#guard
  match parseArgs ["--name", "Nissa", "--deck", "green", "--name", "Chandra", "--deck", "r"] with
  | .ok opt =>
    opt.players.size == 2 &&
    opt.players[0]!.name == "Nissa" && opt.players[0]!.deck == .welcome .green &&
    opt.players[1]!.name == "Chandra" && opt.players[1]!.deck == .welcome .red
  | _ => false


#guard
  match parseArgs [
      "--name", "Alice", "--deck", "alice.txt",
      "--name", "Bob", "--deck", "red"] with
  | .ok opt =>
    opt.players[0]!.name == "Alice" && opt.players[0]!.deck == .file "alice.txt" &&
    opt.players[1]!.name == "Bob" && opt.players[1]!.deck == .welcome .red
  | _ => false


#guard
  match parseArgs ["--deck"] with
  | .error msg => msg == "Missing Welcome Deck color or deck list file"
  | .ok _ => false


#guard
  match parseArgs ["--name", "Elspeth", "--name", "Jace", "--deck", "white"] with
  | .error msg =>
    msg == "--name and --deck must be given the same number of times (got 2 names and 1 decks)"
  | .ok _ => false


#guard
  match parseArgs ["--decides", "chandra"] with
  | .ok opt => opt.decides == some 0
  | _ => false


#guard
  match parseArgs [
      "--decides", "Liliana",
      "--name", "Elspeth", "--name", "Jace", "--name", "Liliana",
      "--deck", "W", "--deck", "U", "--deck", "B"] with
  | .ok opt => opt.players == elspethJaceLiliana && opt.decides == some 2
  | _ => false


#guard
  match parseArgs ["--decides", "--seed", "1"] with
  | .error msg => msg == "Missing player name for --decides"
  | .ok _ => false


#guard
  match parseArgsWithFlags
      ["--interactive", "--seed", "99", "--input", "opening.txt"] ["--seed 42"] with
  | .ok opt => opt.seed == 42
  | _ => false


#guard
  match parseArgsWithFlags ["--input", "opening.txt"] [] with
  | .error msg => msg == "--input requires --interactive or --multiplayer"
  | .ok _ => false


#guard
  match parseArgsWithFlags
      ["--interactive", "--input", "opening.txt"] ["--decides Nissa"] with
  | .ok opt => opt.decides == some 1
  | _ => false


#guard ((helpChooseDecider defaultDemoPlayers).splitOn "decides").length > 1

