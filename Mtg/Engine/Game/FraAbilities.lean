import Mtg.Engine.Game.FraHelpers

/-!
# Reality Fracture activated and loyalty abilities

Resolutions used by FRA activated abilities, loyalty abilities, and the
emblems and effects those create. `applyFra` delegates them here.
-/

namespace Mtg.Engine
namespace Game

/-- Keyword coded by `code` in `FraResolution.plusOneThenChooseKeyword`. -/
def fraKeywordOfCode : Nat → Keywords
  | 0 => Keyword.trample
  | 1 => Keyword.hexproof
  | 2 => Keyword.haste
  | 3 => Keyword.deathtouch
  | _ => Keywords.none

/-- Name of the keyword coded by `code`. -/
def fraKeywordName : Nat → String
  | 0 => "trample"
  | 1 => "hexproof"
  | 2 => "haste"
  | 3 => "deathtouch"
  | _ => "nothing"

/-- Ask `p` which of `options` the permanent `id` gains until end of turn. -/
def beginChooseKeyword (g : Game) (p : PlayerId) (id : ObjectId) (options : Array Nat) : Game :=
  match g.findObject? id with
  | some o =>
    if !o.isOnBattlefield then g
    else
      let names := String.intercalate ", " (options.toList.map fraKeywordName)
      g.beginFraChoice p (.chooseKeyword id options)
        s!"{(g.player p).name} chooses {names} for {o.name}"
  | none => g

/-- Give `p` an emblem or effect object in the command zone (CR 114). -/
def createCommandObject (g : Game) (p : PlayerId) (card : CardDef)
    (untilTurnOf : Option PlayerId := none) : Game :=
  let (g, obj) := g.allocObject card p .command (some p)
  g.setObject { obj with fraEffectUntilTurnOf := untilTurnOf }

/-- Each player in APNAP order who controls a creature. -/
def playersWithCreaturesApnap (g : Game) : Array PlayerId :=
  g.apnapOrder.filter (fun p => !(g.creaturesControlledBy p).isEmpty)

/-- Ask the next player in `players` to sacrifice a creature for Garruk,
Veiled Butcher, or sacrifice the chosen creatures and finish. -/
def continueSacrificeEach (g : Game) (controller : PlayerId) (players : Array PlayerId)
    (chosen : Array ObjectId) : Game :=
  match (players.filter (fun p => !(g.creaturesControlledBy p).isEmpty)).toList with
  | p :: rest =>
    g.beginFraChoice p (.sacrificeCreatureEach controller rest.toArray chosen)
      s!"{(g.player p).name} sacrifices a creature"
  | [] =>
    let youSacrificed := chosen.any (fun id =>
      (g.findObject? id).any (fun o => o.controlledBy controller))
    let g := chosen.foldl (fun g id =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield then
          g.sacrificeToGraveyard o s!"{(g.player (o.controller.getD o.owner)).name} sacrifices {o.name}"
        else g
      | none => g) g
    if youSacrificed then g.createKindTokens controller .beast44trample 1 else g

/-- Ask the next opponent in `players` to discard two cards for Garruk,
Veiled Butcher, or draw `draws` cards for `controller` and finish. -/
partial def continueDiscardTwo (g : Game) (controller : PlayerId) (players : Array PlayerId)
    (draws : Nat) : Game :=
  match players.toList with
  | [] => g.draw controller draws
  | p :: rest =>
    let hand := (g.player p).hand
    if hand.size ≤ 2 then
      let nonland := (hand.filter (fun id => !(g.object! id).printed.isLand)).size
      let g := hand.foldl (fun g id => g.discardFromHand p id) g
      let g :=
        if hand.isEmpty then g.logMsg s!"{(g.player p).name} has no cards to discard" else g
      g.continueDiscardTwo controller rest.toArray (if nonland < 2 then draws + 1 else draws)
    else
      g.beginFraChoice p (.discardTwo controller rest.toArray draws)
        s!"{(g.player p).name} discards two cards"

/-- Creatures attacking `p` directly (not a planeswalker). -/
def creaturesAttackingPlayer (g : Game) (p : PlayerId) : Array GameObject :=
  g.battlefield.filter (fun o =>
    o.isCreature && o.status.attacking && o.status.attackingWhom == some p &&
      o.status.attackingPlaneswalker.isNone)

/-- Resolve an FRA activated or loyalty ability resolution. -/
def applyFraAbility (g : Game) (controller : PlayerId) (effect : Effect) (r : FraResolution)
    (targets : Array Target) (sourceId : Option ObjectId) : Game :=
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := (g.resolvingAbilityObject?.bind (·.chosenX)).getD 0
  match r with
  | .emrakulGrantMana =>
    match source? with
    | none => g
    | some card =>
      let g :=
        if card.zone == .exile then
          let perm : PlayPermission :=
            { player := controller, turnEndsRemaining := 0, whileExiled := true }
          (g.setObject { card with playPermission := some perm }).logMsg
            s!"{(g.player controller).name} may cast {card.name} for as long as it remains exiled"
        else g
      g.withLegalKindPermanent controller kind targets (fun g land =>
        let g := g.mapObjectStatus land (fun s =>
          { s with colorlessGrantUntilCast := s.colorlessGrantUntilCast.push card.id })
        g.logMsg s!"{land.name} gains \"\{T}: Add \{C}\{C}\" until {card.name} is cast from exile")
        sourceId illegal
  | .nextSpellCantBeCountered =>
    (g.modifyPlayer controller (fun pl => { pl with nextSpellCantBeCountered := true })).logMsg
      s!"The next spell {(g.player controller).name} casts this turn can't be countered"
  | .identityEcho =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let (g, _) := g.move o.id .exile none
      let g := g.logMsg s!"{o.name} is exiled"
      let lib := (g.player controller).library
      let (revealed, hit) := Id.run do
        let mut revealed : Array ObjectId := #[]
        for i in [0:lib.size] do
          let id := lib[lib.size - 1 - i]!
          let c := g.object! id
          if c.printed.isCreature || c.printed.isPlaneswalker then
            return (revealed, some id)
          revealed := revealed.push id
        return (revealed, none)
      let g := (revealed ++ hit.toArray).foldl (fun g id =>
        g.logMsg s!"{(g.player controller).name} reveals {(g.object! id).name}") g
      let g :=
        match hit with
        | some id =>
          let (g, newId) := g.putOntoBattlefield id controller
          let g := g.logMsg s!"{(g.object! newId).name} enters the battlefield"
          g.afterPermanentEnters (g.object! newId)
        | none => g.logMsg "No creature or planeswalker card is revealed"
      if revealed.isEmpty then g
      else
        let (rng, ordered) := if g.norandom then (g.rng, revealed) else g.rng.shuffle revealed
        ({ g with rng }.moveIdsInOrder ordered (.library controller)).logMsg
          s!"{(g.player controller).name} puts the rest on the bottom of their library in a random order")
      sourceId illegal
  | .destroyDrawIfLegendaryEnchantment =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let legendaryEnchantment := o.isLegendary && o.printed.isEnchantment
      let g := g.destroyPermanent o
      if legendaryEnchantment then g.draw controller 1 else g) sourceId illegal
  | .plusOneThenChooseKeyword options =>
    onSource (fun g o =>
      let g := g.addPlusOnePlusOneTo o 1
      g.beginChooseKeyword controller o.id options.toArray)
  | .chooseKeyword options =>
    onSource (fun g o => g.beginChooseKeyword controller o.id options.toArray)
  | .graveyardCardToLibraryBottom =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        let card := g.object! id
        (g.moveIdsInOrder #[id] (.library card.owner)).logMsg
          s!"{card.name} is put on the bottom of {(g.player card.owner).name}'s library"
      | _ => g) sourceId illegal
  | .destroyAllCreatures =>
    (g.battlefield.filter (·.isCreature)).foldl (fun g o =>
      match g.findObject? o.id with
      | some o => if o.isOnBattlefield then g.destroyPermanent o else g
      | none => g) g
  | .ownerShufflesIntoLibrary =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let (g, _) := g.move o.id (.library o.owner) none
      let g := g.logMsg s!"{(g.player o.owner).name} shuffles {o.name} into their library"
      g.shuffleLibrary o.owner) sourceId illegal
  | .grantCombatDamageDrawTwo =>
    onSource (fun g o =>
      let ab := TriggeredAbility.fra .combatDamageToPlayer
        "Whenever this creature deals combat damage to a player, draw two cards." (.draw 2)
      (g.mapObjectStatus o (fun s =>
        { s with grantedTriggersUntilEot := s.grantedTriggersUntilEot.push ab })).logMsg
        s!"Until end of turn, whenever {o.name} deals combat damage to a player, {(g.player controller).name} draws two cards")
  | .sourceGetsPowerPerArtifact =>
    let n : Int := Int.ofNat ((g.permanentsOf controller).filter (·.printed.isArtifact)).size
    match source? with
    | some o => if o.isOnBattlefield then g.pumpPermanent o n 0 else g
    | none => g
  | .pumpPerArtifact =>
    let n : Int := Int.ofNat ((g.permanentsOf controller).filter (·.printed.isArtifact)).size
    g.withLegalKindPermanent controller kind targets (fun g o => g.pumpPermanent o n 0)
      sourceId illegal
  | .plusOneOnEachWithPlusOne =>
    let ids := ((g.creaturesControlledBy controller).filter (·.status.plusOnePlusOne > 0)).map (·.id)
    ids.foldl (fun g id =>
      match g.findObject? id with
      | some o => g.addPlusOnePlusOneTo o 1
      | none => g) g
  | .bounceEachTarget =>
    (List.range targets.size).foldl (fun g i =>
      match targets[i]! with
      | t@(Target.permanent id) =>
        if g.targetLegalAt controller kind i t sourceId then
          match g.findObject? id with
          | some o => g.returnToHand id o.owner
          | none => g
        else g.illegalAbilityTarget t
      | _ => g) g
  | .drawThreeThenCountersPerHand =>
    let g := g.draw controller 3
    let x := (g.player controller).hand.size
    if x == 0 then g
    else
      ((g.creaturesControlledBy controller).map (·.id)).foldl (fun g id =>
        match g.findObject? id with
        | some o => g.addPlusOnePlusOneTo o x
        | none => g) g
  | .surveilReturnNoncreatureNonland =>
    let g := g.beginSurveil controller 1
    match g.pending with
    | .surveil .. => { g with surveilReturnNoncreatureNonland := true }
    | _ => g
  | .addBlueNoncreatureOnly =>
    (g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .blue) 1 (fra := some .noncreatureSpell) })).logMsg
      s!"{(g.player controller).name} adds \{U} (noncreature spells only)"
  | .tapAndStunX =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let g := if o.status.tapped then g else g.becomeTapped o
      if chosenX == 0 then g
      else
        let n := g.countersYouPut (g.object! o.id) chosenX (putter := some controller)
        (g.mapObjectStatus (g.object! o.id) (fun s => { s with stun := s.stun + n })).logMsg
          s!"{n} stun counter(s) are put on {o.name}") sourceId illegal
  | .emblemDrawOnCast =>
    let emblem : CardDef := {
      name := "Chandra, Chill of Compliance Emblem", types := #[]
      triggeredAbilities := #[TriggeredAbility.fra .youCastSpell
        "Whenever you cast a spell, draw a card." (.draw 1)] }
    (g.createCommandObject controller emblem).logMsg
      s!"{(g.player controller).name} gets an emblem with \"Whenever you cast a spell, draw a card.\""
  | .empowerJacePerIsland =>
    let n := ((g.permanentsOf controller).filter (fun o => g.hasSubtype o "Island")).size
    g.empowerJace controller n
  | .attackersGetMinusFiveUntilYourTurn =>
    let effectCard : CardDef := {
      name := s!"{srcName} effect", types := #[]
      triggeredAbilities := #[TriggeredAbility.fra (.fra .creatureAttacksYouOrYourPlaneswalker)
        "Whenever a creature attacks you or a planeswalker you control, it gets -5/-0 until end of turn."
        (.fra (.causeGetsPump (-5) 0))] }
    (g.createCommandObject controller effectCard (untilTurnOf := some controller)).logMsg
      s!"Until {(g.player controller).name}'s next turn, whenever a creature attacks them or a planeswalker they control, it gets -5/-0 until end of turn"
  | .exileOpponentLibrariesButBottom =>
    g.forEachOpponent controller (fun g pid =>
      let lib := (g.player pid).library
      let g := (lib.extract 1 lib.size).foldl (fun g id => (g.move id .exile none).1) g
      g.logMsg s!"All but the bottom card of {(g.player pid).name}'s library are exiled")
  | .minusFourMinusOneUntilYourTurn =>
    if targets.isEmpty then g
    else
      g.withLegalKindPermanent controller kind targets (fun g o =>
        (g.mapObjectStatus o (fun s =>
          { s with untilTurnOfPump := s.untilTurnOfPump.push (controller, -4, -1) })).logMsg
          s!"{o.name} gets -4/-1 until {(g.player controller).name}'s next turn") sourceId illegal
  | .eachPlayerSacrificesThenBeast =>
    g.continueSacrificeEach controller g.apnapOrder #[]
  | .eachOpponentDiscardsTwoDrawPerShort =>
    g.continueDiscardTwo controller (g.apnapOrder.filter (· != controller)) 0
  | .discardHandDrawPerCreature =>
    let g := (g.player controller).hand.foldl (fun g id => g.discardFromHand controller id) g
    g.draw controller (g.creaturesControlledBy controller).size
  | .damageEachCreatureExceptYourTokens n =>
    let victims := g.battlefield.filter (fun o =>
      o.isCreature && !(o.printed.isToken && o.controlledBy controller))
    victims.foldl (fun g o =>
      match g.findObject? o.id with
      | some o => if o.isOnBattlefield then g.dealDamageFrom srcName o n (source := src?) else g
      | none => g) g
  | .emblemCreaturesGetTwoTwo =>
    let emblem : CardDef := {
      name := s!"{srcName} Emblem", types := #[]
      staticAbilities := #[.fra .emblemCreaturesGetTwoTwo] }
    (g.createCommandObject controller emblem).logMsg
      s!"{(g.player controller).name} gets an emblem with \"Creatures you control get +2/+2.\""
  | .untapTargets =>
    (List.range targets.size).foldl (fun g i =>
      match targets[i]! with
      | t@(Target.permanent id) =>
        if g.targetLegalAt controller kind i t sourceId then
          match g.findObject? id with
          | some o => g.applyPermanentAction o .untap
          | none => g
        else g.illegalAbilityTarget t
      | _ => g) g
  | .attackersGetTwoTwoTrampleUntilYourTurn =>
    let effectCard : CardDef := {
      name := s!"{srcName} effect", types := #[]
      triggeredAbilities := #[TriggeredAbility.fra (.fra .creaturesAttackYourOpponent)
        "Whenever one or more creatures attack one of your opponents, those creatures get +2/+2 and gain trample until end of turn."
        (.fra .attackersOfPlayerGetTwoTwoTrample)] }
    (g.createCommandObject controller effectCard (untilTurnOf := some controller)).logMsg
      s!"Until {(g.player controller).name}'s next turn, creatures attacking their opponents get +2/+2 and gain trample"
  | .plusOnePerLand =>
    let n := ((g.permanentsOf controller).filter (·.printed.isLand)).size
    g.withLegalKindPermanent controller kind targets (fun g o =>
      if n == 0 then g else g.addPlusOnePlusOneTo o n) sourceId illegal
  | .maySacrificeCreatureForBeast =>
    if (g.creaturesControlledBy controller).isEmpty then g
    else
      g.beginFraChoice controller (.maySacrificeThen .creature .beastToken sourceId)
        s!"{(g.player controller).name} may sacrifice a creature"
  | .damageUpToOneAndPlayer n =>
    targets.foldl (fun g t =>
      match t with
      | Target.permanent id =>
        if g.targetLegalAt controller kind 0 t sourceId then
          g.dealDamageFrom srcName (g.object! id) n (source := src?)
        else g.illegalAbilityTarget t
      | Target.player pid =>
        if g.targetLegalAt controller kind 1 t sourceId then
          g.dealDamageToPlayer pid n (source := src?)
        else g.illegalAbilityTarget t
      | _ => g) g
  | .beastToken => g.createKindTokens controller .beast44trample 1
  | .putCauseCountersOnSource =>
    match g.resolvingAbilityObject?.bind (·.fraCauseStatus), source? with
    | some st, some o =>
      if !o.isOnBattlefield then g
      else
        let g := g.setObject { o with status := o.status.addCountersExceptPlusOne st }
        let g := if st.plusOnePlusOne > 0 then g.addPlusOnePlusOneTo (g.object! o.id) st.plusOnePlusOne else g
        g.logMsg s!"Counters are put on {o.name}"
    | _, _ => g
  | .mayMoveSourceCountersToTarget =>
    match source? with
    | some src =>
      g.withLegalKindPermanent controller kind targets (fun g o =>
        if src.isOnBattlefield && src.status.hasCounters then
          g.beginFraChoice controller (.mayMoveAllCounters src.id o.id)
            s!"{(g.player controller).name} may move all counters from {src.name} onto {o.name}"
        else g) sourceId illegal
    | none => g
  | .mayPayThenProliferate pay times =>
    g.beginFraChoice controller (.mayPayThen pay (.proliferate times) sourceId)
      s!"{(g.player controller).name} may pay \{{pay}}"
  | .becomeArtifactCreatureUntilEot =>
    onSource (fun g o =>
      (g.mapObjectStatus o (fun s => { s with additionalCreatureUntilEot := true })).logMsg
        s!"{o.name} becomes an artifact creature until end of turn")
  | .queueMshReflexive kind paid =>
    if kind == 2 then
      g.beginFraChoice controller (.hawkeyeModes paid #[] sourceId)
        s!"{(g.player controller).name} chooses up to {paid} Trick Arrows modes"
    else g.queueModeledReflexive controller sourceId kind paid
  | .mshReflexive kind paid =>
    g.resolveModeledReflexive controller sourceId kind paid targets g.resolvingDivision
  | .hawkeyeArrows modes =>
    let src := sourceId.bind g.findObject?
    let illegal := some "The target is no longer legal"
    let (g, _) := modes.foldl (fun (acc : Game × Nat) m =>
      let (g, i) := acc
      let slice := targets.extract i (i + 1)
      match m with
      | 0 =>
        (g.withLegalKindPermanent controller .creature slice (fun g o =>
          (g.mapObjectStatus o (fun s => { s with cantBlockUntilEot := true })).logMsg
            s!"{o.name} can't block this turn") sourceId illegal, i + 1)
      | 1 =>
        (g.withLegalKindPlayer controller .player slice
          (fun g pid => g.dealDamageToPlayer pid 2 (source := src)) sourceId illegal, i + 1)
      | _ =>
        if (g.player controller).hand.isEmpty then (g.draw controller 1, i)
        else
          (g.beginFraChoice controller .discardThenDraw
            s!"{(g.player controller).name} discards a card, then draws a card", i)) (g, 0)
    g
  | .copySourceSpellXTimes =>
    match sourceId.bind g.findObject? with
    | some spell =>
      if spell.zone != .stack then g.logMsg s!"{spell.name} is no longer on the stack"
      else
        let x := spell.chosenX.getD 0
        let (g, copies) := (List.range x).foldl (fun (acc : Game × Array ObjectId) _ =>
          let g := acc.1.copyStackSpell spell controller
          (g, acc.2.push ((g.stack.back?.map (·.objectId)).getD spell.id))) (g, #[])
        let targeted := ((g.stackEntry? spell.id).map (!·.targets.isEmpty)).getD false
        if copies.isEmpty || !targeted then g
        else
          g.beginFraChoice controller (.newTargetsForCopies copies)
            s!"{(g.player controller).name} may choose new targets for the copies"
    | none => g
  | .gainLife n => g.gainLife controller n
  | .drawAndCreateTreasure =>
    let g := g.draw controller 1
    g.createTreasureTokens controller 1
  | .damageEqualSourcePower =>
    let n :=
      match sourceId.bind g.findObject? with
      | some o => (g.power o).toNat
      | none => 0
    let srcName := (sourceId.bind g.findObject?).map (·.name) |>.getD "The creature"
    g.withLegalKindPermanent controller .creature targets (fun g o =>
      g.dealDamageFrom srcName o n (source := sourceId.bind g.findObject?))
      sourceId (some "The target is no longer legal")
  | .returnSourceToHand =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.zone == .graveyard o.owner then g.returnToHand o.id o.owner
      else g.logMsg s!"{o.name} is no longer in the graveyard"
    | none => g.logMsg "The ability's source is no longer in the graveyard"
  | .sarumanExileCopyMayCast =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        match g.findObject? id with
        | some o =>
          if !(o.zone == .graveyard o.owner) ||
              !(o.printed.isEnchantment || o.printed.isInstantOrSorcery) then
            g.logMsg "The target is no longer legal"
          else
            let name := o.name
            let (g, exId) := g.move id .exile none
            let g := g.logMsg s!"{name} is exiled"
            let card := g.object! exId
            let (g, copy) := g.allocObject card.printed controller .exile (some controller)
            let g := g.setObject { copy with isCopy := true }
            g.beginFraChoice controller (.mayCastCopy copy.id)
              s!"{(g.player controller).name} may cast the copy of {name} without paying its mana cost"
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "The target is no longer legal") sourceId illegal
  | .zemoBoastCopies =>
    let exiled := (g.resolvingAbilityObject?.map (·.boastExiled)).getD #[]
    let (g, copies) := exiled.foldl (fun (acc : Game × Array ObjectId) id =>
      let (g, cs) := acc
      match g.findObject? id with
      | some card =>
        if card.zone != .exile then (g, cs)
        else
          let (g, copy) := g.allocObject { card.printed with isToken := card.printed.isPermanentCard }
            controller .exile (some controller)
          let g := g.setObject { copy with
            isCopy := true
            playPermission := some { player := controller, turnEndsRemaining := 0
                                     whileExiled := true, withoutManaCost := true, ignoreTiming := true } }
          (g, cs.push copy.id)
      | none => (g, cs)) (g, #[])
    if copies.isEmpty then g.logMsg "No exiled card is left to copy"
    else
      g.beginFraChoice controller (.castCopiesFree copies 1000 3)
        s!"{(g.player controller).name} may cast up to three of the copies without paying their mana costs"
  | .extort =>
    g.beginFraChoice controller (.mayPayExtort sourceId)
      s!"{(g.player controller).name} may pay \{W/B} (extort)"
  | .proliferate times =>
    if times == 0 then g
    else
      { g with pending := .chooseProliferate controller times }.logMsg
        s!"{(g.player controller).name} proliferates {times} time(s)"
  | .causeGetsPump p t =>
    match g.fraCause? with
    | some o => if o.isOnBattlefield then g.pumpPermanent o p t else g
    | none => g
  | .attackersOfPlayerGetTwoTwoTrample =>
    match g.fraCauseController? with
    | some defender =>
      (g.creaturesAttackingPlayer defender).foldl (fun g o =>
        let g := g.pumpPermanent (g.object! o.id) 2 2
        g.grantKeywordsUntilEot (g.object! o.id) Keyword.trample) g
    | none => g
  | _ => g

end Game
end Mtg.Engine
