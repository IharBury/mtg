import Mtg.Engine.Game.FraAbilities

/-!
# Reality Fracture effect resolution

`applyFra` resolves `Resolution.fra` for spells, activated abilities, and
triggered abilities. Choices made while one resolves leave a
`Pending.fraChoice`; `FraChoices` finishes them.
-/

namespace Mtg.Engine
namespace Game

partial def applyFra (g : Game) (controller : PlayerId) (effect : Effect) (r : FraResolution)
    (targets : Array Target) (sourceId : Option ObjectId) : Game :=
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  match r with
  | .bounce =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.permanent id =>
        match g.findObject? id with
        | some o => g.returnToHand id o.owner
        | none => g
      | Target.card id =>
        match g.findObject? id with
        | some o =>
          if o.zone == .stack then
            if o.isCopy then
              (g.removeFromZoneList o.id .stack |>.ceaseToExist o.id).logMsg
                s!"The copy of {o.name} ceases to exist (CR 704.5e)"
            else g.returnToHand id o.owner
          else g
        | none => g
      | Target.player _ => g) sourceId illegal
  | .exile =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let (g, _) := g.move o.id .exile none
      g.logMsg s!"{o.name} is exiled") sourceId illegal
  | .destroyDrawIfNotAttacking =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let wasAttacking := o.status.attacking
      let ctrl := o.controller.getD o.owner
      let g := g.destroyPermanent o
      if wasAttacking then g else g.draw ctrl 1) sourceId illegal
  | .loseLife n => g.loseLife controller n
  | .damageEachOpponentGainLife n => g.drainOpponents controller n src?
  | .damageEachPlayer n =>
    g.livingPlayers.foldl (fun g pl => g.dealDamageToPlayer pl.id n (source := src?)) g
  | .drawAndGainLife c l => (g.draw controller c).gainLife controller l
  | .damageThenPlusOneOnSecond n =>
    let g :=
      match g.legalPermanentAt? controller kind targets 0 sourceId with
      | some o => g.dealDamageFrom srcName o n (source := src?)
      | none => g.logMsg "The first target is no longer legal"
    match g.legalPermanentAt? controller kind targets 1 sourceId with
    | some o => g.addPlusOnePlusOneTo o 1
    | none => g
  | .returnFromGyToBattlefield plusOnes =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        let (g, newId) := g.returnCardToBattlefield controller id plusOnes
        g.afterPermanentEnters (g.object! newId)
      | _ => g) sourceId illegal
  | .returnFromGyToHand =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        match g.findObject? id with
        | some o => g.returnToHand id o.owner
        | none => g
      | _ => g) sourceId illegal
  | .destroyAllNotChosenType =>
    let chosen := g.chooseCreatureTypeFor controller
    let g := g.logMsg s!"{(g.player controller).name} chooses {chosen}"
    let doomed := g.battlefield.filter (fun o => o.isCreature && !g.hasSubtype o chosen)
    doomed.foldl (fun g o =>
      match g.findObject? o.id with
      | some o => g.destroyPermanent o
      | none => g) g
  | .searchPlaneswalkerToTop =>
    match g.findLibraryCard? controller (·.isPlaneswalker) with
    | none =>
      (g.logMsg s!"{(g.player controller).name} searches their library and finds no planeswalker card").shuffleLibrary controller
    | some id =>
      let name := (g.object! id).name
      let g := g.logMsg s!"{(g.player controller).name} reveals {name}"
      let g := g.shuffleLibrary controller
      let g := g.modifyPlayer controller (fun pl =>
        { pl with library := (pl.library.filter (· != id)).push id })
      g.logMsg s!"{(g.player controller).name} puts {name} on top of their library"
  | .plusOneOnEachTarget n =>
    targets.foldl (fun g t =>
      match t with
      | Target.permanent id =>
        if g.targetLegalAt controller kind 0 t sourceId then
          g.addPlusOnePlusOneTo (g.object! id) n
        else g.illegalAbilityTarget t
      | _ => g) g
  | .returnAllNonlandPermanentsFromGy =>
    let ids := (g.player controller).graveyard.filter (fun id =>
      (g.findObject? id).any (fun o =>
        o.printed.isPermanentCard && !o.printed.isLand && !o.printed.isAura))
    let (g, newIds) := ids.foldl (fun (acc : Game × Array ObjectId) id =>
      let (g, newId) := acc.1.returnCardToBattlefield controller id
      (g, acc.2.push newId)) (g, #[])
    newIds.foldl (fun g id =>
      match g.findObject? id with
      | some o => g.afterPermanentEnters o
      | none => g) g
  | .drawMilledThisTurn =>
    g.withLegalKindPlayer controller kind targets (fun g pid =>
      g.draw controller (g.player pid).cardsMilledThisTurn) sourceId illegal
  | .exileAllCreaturesEmpower =>
    let creatures := g.battlefield.filter (·.isCreature)
    let g := creatures.foldl (fun g o =>
      let (g, _) := g.move o.id .exile none
      g.logMsg s!"{o.name} is exiled") g
    g.empowerJace controller creatures.size
  | .drawGreatestPowerLoseLife =>
    let n := (g.greatestPowerAmongCreatures controller).toNat
    let before := (g.player controller).cardsDrawnThisTurn
    let g := g.draw controller n
    let drawn := (g.player controller).cardsDrawnThisTurn - before
    g.loseLife controller drawn
  | .revealHandDiscardNonland permanentOnly =>
    g.withLegalKindPlayer controller kind targets (fun g pid =>
      g.beginRevealDiscard controller pid permanentOnly) sourceId illegal
  | .damageThenRevealDiscardNonland n =>
    g.withLegalKindPlayer controller kind targets (fun g pid =>
      let g := g.dealDamageToPlayer pid n (source := src?)
      g.beginRevealDiscard controller pid false) sourceId illegal
  | .extrapolate =>
    let g := g.materializeSideboard controller
    let names := (g.outsideCards controller).foldl (fun acc o =>
      if acc.contains o.name then acc else acc.push o.name) (#[] : Array String)
    if names.size < 2 then
      g.logMsg s!"{(g.player controller).name} has no two cards with different names outside the game"
    else
      g.beginFraChoice controller .extrapolateReveal
        s!"{(g.player controller).name} may reveal two cards with different names from outside the game"
  | .sphinxsApproach =>
    let g := g.draw controller 2
    match g.resolvingSpell.bind g.findObject? with
    | some spell =>
      if spell.zone == .stack && !spell.isCopy &&
          (g.sphinxsApproachesInGraveyard controller).size ≥ 4 then
        g.beginFraChoice controller (.sphinxsApproach spell.id)
          s!"{(g.player controller).name} may exile Sphinx's Approach and four cards named Sphinx's Approach"
      else g
    | none => g
  | .cadetThenPlusOneOtherWizardTokens =>
    let (g, cadet) := g.createOneKindToken controller .cadet
    (g.permanentsOf controller).foldl (fun g o =>
      if o.id != cadet.id && o.printed.isToken && g.hasSubtype o "Wizard" then
        g.addPlusOnePlusOneTo o 1
      else g) g
  | .damageEachOppCreatureAndPlaneswalker n =>
    let victims := g.battlefield.filter (fun o =>
      (o.isCreature || o.printed.isPlaneswalker) && o.controller.isSome &&
        !o.controlledBy controller)
    victims.foldl (fun g o =>
      match g.findObject? o.id with
      | some o => g.dealDamageFrom srcName o n (source := src?)
      | none => g) g
  | .loseAbilitiesThenFight =>
    match g.legalPermanentAt? controller kind targets 0 sourceId with
    | none => g.logMsg "The first target is no longer legal. No damage is dealt"
    | some victim =>
      let g := g.mapObjectStatus victim (fun s => { s with losesAbilitiesUntilEot := true })
      let g := g.logMsg s!"{victim.name} loses all abilities until end of turn"
      match g.legalPermanentAt? controller kind targets 1 sourceId with
      | some striker =>
        g.dealDamageFrom striker.name (g.object! victim.id) (max (g.power striker) 0)
          (source := some striker)
      | none => g.logMsg "The second target is no longer legal. No damage is dealt"
  | .pumpGrantUntap p t k =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let g := g.pumpPermanent o p t
      let g := g.grantKeywordsUntilEot (g.object! o.id) k
      g.applyPermanentAction (g.object! o.id) .untap) sourceId illegal
  | .pumpGrantPlusOne p t k n =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let g := g.pumpPermanent o p t
      let g := g.grantKeywordsUntilEot (g.object! o.id) k
      g.addPlusOnePlusOneTo (g.object! o.id) n) sourceId illegal
  | .plusOneThenGrant n k =>
    if targets.isEmpty then g
    else
      g.withLegalKindPermanent controller kind targets (fun g o =>
        let g := g.addPlusOnePlusOneTo o n
        g.grantKeywordsUntilEot (g.object! o.id) k) sourceId illegal
  | .clashOfElements =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      g.beginFraChoice o.owner (.topOrBottomDamage o.id 2)
        s!"{(g.player o.owner).name} may put {o.name} on top of their library") sourceId illegal
  | .entrustTheSpark =>
    if (g.permanentsOf controller).any (·.printed.isPlaneswalker) then
      g.beginFraChoice controller .maySacrificePlaneswalker
        s!"{(g.player controller).name} may sacrifice a planeswalker"
    else g.logMsg s!"{(g.player controller).name} controls no planeswalker to sacrifice"
  | .cadetsPlusOnePerThreeIfFromGy n =>
    let fromGy := (g.resolvingSpell.bind g.findObject?).any (·.castFromGraveyard)
    let counters := if fromGy then (g.player controller).graveyard.size / 3 else 0
    Id.run do
      let mut g := g
      for _ in [0:n] do
        let (g', tok) := g.createOneKindToken controller .cadet
        g := g'
        if counters > 0 then
          match g.findObject? tok.id with
          | some o => g := g.addPlusOnePlusOneTo o counters
          | none => pure ()
      return g
  | .cadetWithHaste =>
    let (g, tok) := g.createOneKindToken controller .cadet
    match g.findObject? tok.id with
    | some o => g.grantKeywordsUntilEot o Keyword.haste
    | none => g
  | .drawOneOrTwoIfNotFromHand =>
    let fromHand := (g.resolvingSpell.bind g.findObject?).any (·.castFromHand)
    g.draw controller (if fromHand then 1 else 2)
  | .destroyThenPlusOneEachOfPlayer =>
    let g :=
      match g.legalPermanentAt? controller kind targets 0 sourceId with
      | some o => g.destroyPermanent o
      | none => g.logMsg "The first target is no longer legal"
    match targets[1]? with
    | some (Target.player pid) =>
      if g.targetLegalAt controller kind 1 (Target.player pid) sourceId then
        (g.creaturesControlledBy pid).foldl (fun g o => g.addPlusOnePlusOneTo o 1) g
      else g.logMsg "The second target is no longer legal"
    | _ => g
  | .exileReturnBrieflyIfMvAtMost n =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      -- Ruling: the mana value is that of the permanent as it last existed
      -- on the battlefield.
      let mv := g.objectManaValue o
      let (g, exiled) := g.move o.id .exile none
      let g := g.logMsg s!"{o.name} is exiled"
      if mv ≤ n && !o.printed.isToken then
        let (g, back) := g.putOntoBattlefield exiled controller (tapped := true)
        let g := g.logMsg s!"{o.name} returns to the battlefield tapped under {(g.player controller).name}'s control"
        let g := { g with delayedEndStepExiles := g.delayedEndStepExiles.push back }
        g.afterPermanentEnters (g.object! back)
      else g) sourceId illegal
  | .eachPlayerMayWheel n =>
    match g.apnapFrom.toList with
    | [] => g
    | p :: rest =>
      g.beginFraChoice p (.mayWheel n rest.toArray)
        s!"{(g.player p).name} may discard their hand and draw {n} cards"
  | .mountainsAddExtraRed =>
    let g := g.modifyPlayer controller (fun pl =>
      { pl with mountainExtraRedThisTurn := pl.mountainExtraRedThisTurn + 1 })
    g.logMsg s!"Until end of turn, whenever {(g.player controller).name} taps a Mountain for mana, they add an additional \{R}"
  | .searchLandToGraveyard =>
    g.resolveLibrarySearch controller (·.isLand) "land card" fun g id =>
      let name := (g.object! id).name
      let (g, _) := g.move id (.graveyard controller) none
      g.logMsg s!"{(g.player controller).name} puts {name} into their graveyard"
  | .counter =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id => g.counterStackSpell id
      | _ => g) sourceId illegal
  | .counterUnlessPays n =>
    g.withLegalKindTarget controller kind targets (fun g _ =>
      g.beginPayOrLetCounter targets n) sourceId illegal
  | .millThenDraw m d => (g.mill controller m).draw controller d
  | .destroy =>
    g.withLegalKindPermanent controller kind targets (fun g o => g.destroyPermanent o)
      sourceId illegal
  | .damageExileIfDies n =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let g := g.mapObjectStatus o (fun s => { s with untilEotExileIfDies := true })
      g.dealDamageFrom srcName (g.object! o.id) n (source := src?)) sourceId illegal
  | .millMayPutPermanentGainLife n life =>
    let before := (g.player controller).graveyard.size
    let g := g.mill controller n
    let gy := (g.player controller).graveyard
    let milled := gy.extract before gy.size
    let choices := milled.filter (fun id => (g.findObject? id).any (·.printed.isPermanentCard))
    if choices.isEmpty then g.gainLife controller life
    else
      g.beginFraChoice controller (.mayPutMilledPermanent choices life)
        s!"{(g.player controller).name} may put a permanent card milled this way into their hand"
  | .chooseTriggerModes _ => g
  | .untapAllLandsYouControl =>
    (g.permanentsOf controller).foldl (fun g o =>
      if o.printed.isLand && o.status.tapped then g.applyPermanentAction (g.object! o.id) .untap
      else g) g
  | .blink =>
    if targets.isEmpty then g
    else
      g.withLegalKindPermanent controller kind targets (fun g o =>
        g.exileThenReturn o "is exiled and returns to the battlefield") sourceId illegal
  | .mayMovePlusOneToEachOther =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield && o.status.plusOnePlusOne > 0 then
        g.beginFraChoice controller (.mayMovePlusOne o.id)
          s!"{(g.player controller).name} may remove a +1/+1 counter from {o.name}"
      else g
    | none => g
  | .empowerJacePerCreature =>
    g.empowerJace controller (g.creaturesControlledBy controller).size
  | .tapEnchantedUnprepare =>
    match (sourceId.bind g.findObject?).bind (·.attachedTo) |>.bind g.findObject? with
    | some host =>
      let g := if host.status.tapped then g else g.becomeTapped host
      g.unprepare (g.object! host.id)
    | none => g.logMsg "The Aura isn't attached to a creature"
  | .ownerPutsOnTopOrBottom =>
    if targets.isEmpty then g
    else
      g.withLegalKindPermanent controller kind targets (fun g o =>
        g.beginFraChoice o.owner (.topOrBottomDamage o.id 0)
          s!"{(g.player o.owner).name} puts {o.name} on the top or bottom of their library")
        sourceId illegal
  | .drawTwoDiscardTwoStun =>
    let g := g.draw controller 2
    let n := Nat.min 2 (g.player controller).hand.size
    if n == 0 then g
    else
      g.beginFraChoice controller (.discardThenStun n sourceId)
        s!"{(g.player controller).name} discards {n} card(s)"
  | .copyTokenOfSourceIfNotToken =>
    match sourceId with
    | none => g
    | some id =>
      match g.findObject? (g.followMoved id) with
      | some card =>
        let (g, tok) := g.createToken controller { card.printed with isToken := true }
        let g := g.logMsg s!"{(g.player controller).name} creates a token copy of {card.name}"
        g.afterPermanentEnters (g.object! tok.id)
      | none => g.logMsg "The card can't be found"
  | .returnSourceFromGy toHand tapped plusOnes =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.zone != .graveyard o.owner then g.logMsg s!"{o.name} is no longer in the graveyard"
      else if toHand then g.returnToHand o.id o.owner
      else
        let (g, newId) := g.returnCardToBattlefield controller o.id plusOnes (tapped := tapped)
        g.afterPermanentEnters (g.object! newId)
    | none => g.logMsg "The card is no longer in the graveyard"
  | .mayPayThenDestroyPerOpponent n =>
    g.beginFraChoice controller (.mayPayThen n .reflexiveDestroyPerOpponent sourceId)
      s!"{(g.player controller).name} may pay \{{n}}"
  | .damageX =>
    let x := (sourceId.bind g.findObject?).bind (·.chosenX) |>.getD 0
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.player pid => g.dealDamageToPlayer pid x (source := src?)
      | Target.permanent id => g.dealDamageFrom srcName (g.object! id) x (source := src?)
      | Target.card _ => g) sourceId illegal
  | .trampleAndPowerPerArtifact =>
    let n : Int := Int.ofNat ((g.permanentsOf controller).filter (·.printed.isArtifact)).size
    (g.creaturesControlledBy controller).foldl (fun g o =>
      let g := g.pumpPermanent (g.object! o.id) n 0
      g.grantKeywordsUntilEot (g.object! o.id) Keyword.trample) g
  | .searchCardThenDiscardRandom =>
    let g := g.resolveLibrarySearchToHand controller (fun _ => true) "card"
    let hand := (g.player controller).hand
    if hand.isEmpty then g
    else
      let (rng, r) := g.rng.next
      let g := { g with rng }
      g.discardFromHandRandomly controller hand[(r.toNat % hand.size)]!
  | .grantFlashbackUntilEot =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        match g.findObject? id with
        | some o =>
          (g.setObject { o with flashbackUntilEot := true }).logMsg
            s!"{o.name} gains flashback until end of turn"
        | none => g
      | _ => g) sourceId illegal
  | .mayDiscardThenDamage n =>
    if (g.player controller).hand.isEmpty then g
    else
      g.beginFraChoice controller (.mayDiscardThen (.reflexiveDamageAnyTarget n) sourceId)
        s!"{(g.player controller).name} may discard a card"
  | .maySearchLandsEqualDamage =>
    let n := (g.resolvingAbilityObject?.bind (·.lastKnownPower)).getD 0 |>.toNat
    if n == 0 then g
    else
      g.beginFraChoice controller (.mayThen (.searchLandsTapped n) sourceId)
        s!"{(g.player controller).name} may search for up to {n} land cards"
  | .maySearchBasicLandTapped =>
    g.beginFraChoice controller (.mayThen .searchBasicLandTapped sourceId)
      s!"{(g.player controller).name} may search for a basic land card"
  | .returnCauseTapped =>
    match g.fraCause? with
    | some card =>
      if card.zone == .graveyard card.owner then
        let (g, newId) := g.putOntoBattlefield card.id card.owner (tapped := true)
        let g := g.logMsg s!"{card.name} returns to the battlefield tapped"
        g.afterPermanentEnters (g.object! newId)
      else g.logMsg s!"{card.name} is no longer in the graveyard"
    | none => g.logMsg "The card is no longer in the graveyard"
  | .sacrificeSource =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield then g.sacrificeToGraveyard o s!"{(g.player controller).name} sacrifices {o.name}"
      else g
    | none => g
  | .causeDealsDamageToEachOpponent n =>
    let cause := g.fraCause?
    let name := (cause.map (·.name)).getD "The creature"
    g.forEachOpponent controller (fun g pid =>
      (g.dealDamageToPlayer pid n (source := cause)).logMsg s!"{name} deals {n} damage")
  | .exileFromHandUntilLeaves =>
    g.withLegalKindPlayer controller kind targets (fun g pid =>
      let g := g.revealHand pid
      if (g.revealedHandChoices pid false).isEmpty then
        g.logMsg s!"{(g.player pid).name} has no nonland card"
      else
        g.beginFraChoice controller (.exileFromRevealedHand pid sourceId)
          s!"{(g.player controller).name} chooses a nonland card to exile") sourceId illegal
  | .millThenReturnLandTapped n =>
    let g := g.mill controller n
    g.applyFra controller effect .reflexiveReturnLandTapped #[] sourceId
  | .maySacrificeLandForHeartwoods =>
    if (g.permanentsOf controller).any (·.printed.isLand) then
      g.beginFraChoice controller (.maySacrificeThen .land (.tappedHeartwoods 2) sourceId)
        s!"{(g.player controller).name} may sacrifice a land"
    else g
  | .uldarosCopies =>
    -- Exile the still-legal targets (one card per card type, no card twice).
    -- One card for each card type: each chosen card needs a type no earlier
    -- card used.
    let (ids, _) := targets.foldl (fun (acc : Array ObjectId × Array CardType) t =>
      let (ids, used) := acc
      match t with
      | Target.card id =>
        match g.findObject? id with
        | some o =>
          if ids.contains id || o.zone != .graveyard controller || o.printed.isLand then acc
          else
            match o.printed.types.find? (fun ty => !used.contains ty) with
            | some ty => (ids.push id, used.push ty)
            | none => acc
        | none => acc
      | _ => acc) (#[], #[])
    let (g, copies) := ids.foldl (fun (acc : Game × Array ObjectId) id =>
      let (g, cs) := acc
      let card := g.object! id
      let (g, ex) := g.move id .exile none
      let g := g.logMsg s!"{card.name} is exiled"
      let printed := (g.object! ex).printed
      -- Permanent spells cast this way become tokens.
      let (g, copy) := g.allocObject { printed with isToken := printed.isPermanentCard }
        controller .exile (some controller)
      let g := g.setObject { copy with
        isCopy := true
        playPermission := some { player := controller, turnEndsRemaining := 0
                                 whileExiled := true, withoutManaCost := true, ignoreTiming := true } }
      (g, cs.push copy.id)) (g, #[])
    if copies.isEmpty then g
    else
      g.beginFraChoice controller (.castCopiesFree copies 6 copies.size)
        s!"{(g.player controller).name} may cast copies with total mana value 6 or less"
  | .damageThenGainLife n =>
    let g := g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.player pid => g.dealDamageToPlayer pid n (source := src?)
      | Target.permanent id => g.dealDamageFrom srcName (g.object! id) n (source := src?)
      | Target.card _ => g) sourceId illegal
    g.gainLife controller n
  | .exileCardFromGraveyard =>
    if targets.isEmpty then g
    else
      g.withLegalKindTarget controller kind targets (fun g t =>
        match t with
        | Target.card id =>
          let name := (g.object! id).name
          let (g, _) := g.move id .exile none
          g.logMsg s!"{name} is exiled"
        | _ => g) sourceId illegal
  | .copyCauseSpell =>
    match g.fraCause? with
    | some spell =>
      if spell.zone != .stack then g.logMsg s!"{spell.name} is no longer on the stack"
      else
        let (g, copy) := g.allocObject spell.printed controller .stack (some controller)
        let g := g.setObject { copy with
          chosenX := spell.chosenX, isCopy := true, adventurerCard := spell.adventurerCard }
        let g := g.putStackEntry controller copy.id
        let g :=
          match g.stack.find? (fun e => e.objectId == spell.id),
              g.stack.findIdx? (fun e => e.objectId == copy.id) with
          | some orig, some i =>
            { g with stack := g.stack.set! i { g.stack[i]! with
                targets := orig.targets, dividedDamage := orig.dividedDamage
                chosenMode := orig.chosenMode, targetsAnnounced := true } }
          | _, _ => g
        g.logMsg s!"A copy of {spell.name} is created"
    | none => g.logMsg "The spell is no longer on the stack"
  | .eyeOfJace =>
    let g := g.beginSurveil controller 1
    match g.pending with
    | .surveil .. => { g with fraAfterLook := some (controller, sourceId, .eyeOfJaceCheck) }
    | _ => g.applyFra controller effect .eyeOfJaceCheck targets sourceId
  | .eyeOfJaceCheck =>
    if (g.player controller).graveyard.size < 7 then g
    else
      match sourceId.bind g.findObject? with
      | some o =>
        if !o.isOnBattlefield then g
        else
          let g := g.sacrificeToGraveyard o s!"{(g.player controller).name} sacrifices {o.name}"
          g.drainOpponents controller 2 (some o)
      | none => g
  | .loyaltyOnEachPlaneswalkerYouControl => g.loyaltyOnEachPlaneswalkerOf controller
  | .causeGains k =>
    match g.fraCause? with
    | some o => if o.isOnBattlefield then g.grantKeywordsUntilEot o k else g
    | none => g
  | .untapSource =>
    match sourceId.bind g.findObject? with
    | some o => if o.isOnBattlefield && o.status.tapped then g.applyPermanentAction o .untap else g
    | none => g
  | .tapAndStunPerOpponent =>
    targets.foldl (fun g t =>
      match t with
      | Target.permanent id =>
        match g.findObject? id with
        | some o =>
          if o.isOnBattlefield && o.isCreature && g.canBeTargetedBy controller o then
            g.applyPermanentAction o .tapAndStun
          else g.illegalAbilityTarget t
        | none => g
      | _ => g) g
  | .damageCauseController n =>
    match g.fraCauseController? with
    | some pid => g.dealDamageToPlayer pid n (source := src?)
    | none => g
  | .removeUpToCounters n =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      g.removeUpToCountersFrom controller o n) sourceId illegal
  | .damageTargetGainLife n =>
    let g := g.withLegalKindPlayer controller kind targets (fun g pid =>
      g.dealDamageToPlayer pid n (source := src?)) sourceId illegal
    g.gainLife controller n
  | .maySacrificeThenEdict =>
    if (g.permanentsOf controller).any (fun o => o.isCreature || o.printed.isPlaneswalker) then
      g.beginFraChoice controller
        (.maySacrificeThen .creatureOrPlaneswalker .eachOpponentSacrificesCreature sourceId)
        s!"{(g.player controller).name} may sacrifice a creature or planeswalker"
    else g
  | .sourceGetsCausePower =>
    let x : Int :=
      match g.fraCause? with
      | some o => if o.isOnBattlefield then g.power o
                  else (g.resolvingAbilityObject?.bind (·.fraCausePower)).getD 0
      | none => (g.resolvingAbilityObject?.bind (·.fraCausePower)).getD 0
    match sourceId.bind g.findObject? with
    | some o => if o.isOnBattlefield then g.pumpPermanent o x 0 else g
    | none => g
  | .jiangYangguAlone =>
    if (g.player controller).hand.isEmpty then
      g.applyFra controller effect .drawThenCountersPerDiscard targets sourceId
    else
      g.beginFraChoice controller
        (.discardThen .drawThenCountersPerDiscard sourceId
          (g.resolvingAbilityObject?.bind (·.fraCauseId)))
        s!"{(g.player controller).name} discards a card"
  | .drawThenCountersPerDiscard =>
    let g := g.draw controller 1
    let n := (g.player controller).cardsDiscardedThisTurn
    match g.fraCause? with
    | some o => if o.isOnBattlefield && n > 0 then g.addPlusOnePlusOneTo o n else g
    | none => g
  | .kothGeomancer =>
    let g := g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid 1 (source := src?))
    match g.fraCause? with
    | some land => if g.hasSubtype land "Mountain" then g.addManaLogged controller #[.colored .red] else g
    | none => g
  | .fblthpSearch =>
    let x := (sourceId.bind g.findObject?).bind (·.chosenX) |>.getD 0
    let (g, _) := (g.player controller).library.foldl (fun (acc : Game × Array String) id =>
      let (g, names) := acc
      if names.size ≥ x then acc
      else
        match g.findObject? id with
        | some o =>
          if isBasicLandCard o.printed && !names.contains o.name then
            let g := g.logMsg s!"{(g.player controller).name} reveals {o.name}"
            let (g, _) := g.move id (.hand controller) none
            (g, names.push o.name)
          else acc
        | none => acc) (g, #[])
    g.shuffleLibrary controller
  | .untapAllTokensYouControl =>
    (g.permanentsOf controller).foldl (fun g o =>
      if o.printed.isToken && o.status.tapped then g.applyPermanentAction (g.object! o.id) .untap
      else g) g
  | .mayDiscardThenSearchEnchantment =>
    if (g.player controller).hand.isEmpty then g
    else
      g.beginFraChoice controller (.mayDiscardThen .searchEnchantmentToHand sourceId)
        s!"{(g.player controller).name} may discard a card"
  | .gainLifeAndExtraLand n =>
    let g := g.gainLife controller n
    (g.modifyPlayer controller (fun pl =>
      { pl with additionalLandsThisTurn := pl.additionalLandsThisTurn + 1 })).logMsg
      s!"{(g.player controller).name} may play an additional land this turn"
  | .firstFightsSecond =>
    match g.legalPermanentAt? controller kind targets 0 sourceId,
        g.legalPermanentAt? controller kind targets 1 sourceId with
    | some a, some b => g.fightCreatures a b
    | _, _ => g
  | .minusOnesPerOpponent =>
    let x := (g.player controller).graveyard.foldl (fun acc id =>
      match g.findObject? id with
      | some o => Nat.max acc (g.objectManaValue o)
      | none => acc) 0
    targets.foldl (fun g t =>
      match t with
      | Target.permanent id =>
        match g.findObject? id with
        | some o =>
          if o.isOnBattlefield && o.isCreature && g.canBeTargetedBy controller o && x > 0 then
            (g.mapObjectStatus o (fun s => { s with minusOneMinusOne := s.minusOneMinusOne + x })).logMsg
              s!"{x} -1/-1 counter(s) are put on {o.name}"
          else g
        | none => g
      | _ => g) g
  | .drawPerColorAmongOtherArtifacts =>
    let colors := (g.permanentsOf controller).foldl (fun (acc : ColorSet) o =>
      if o.printed.isArtifact && some o.id != sourceId then ColorSet.union acc o.printed.colors
      else acc) ColorSet.empty
    g.draw controller ((Color.all.filter colors.contains).length)
  | .untapUnblockable =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let g := g.applyPermanentAction o .untap
      g.applyPermanentAction (g.object! o.id) .cantBeBlocked) sourceId illegal
  | .minusPowerPerGraveyard =>
    let n : Int := Int.ofNat (g.player controller).graveyard.size
    g.withLegalKindPermanent controller kind targets (fun g o => g.pumpPermanent o (-n) 0)
      sourceId illegal
  | .plusOneOnEachCreatureYouControl => g.plusOneOnEachCreatureOf controller
  | .plusOneOnSource n =>
    match sourceId.bind g.findObject? with
    | some o => if o.isOnBattlefield then g.addPlusOnePlusOneTo o n else g
    | none => g
  | .sourceFightsTarget =>
    if targets.isEmpty then g
    else
      match sourceId.bind g.findObject? with
      | some src =>
        g.withLegalKindPermanent controller kind targets (fun g o =>
          if src.isOnBattlefield then g.fightCreatures (g.object! src.id) o else g) sourceId illegal
      | none => g
  | .exileUntilSourceLeaves =>
    match sourceId.bind g.findObject? with
    | some src =>
      if !src.isOnBattlefield then g.logMsg s!"{src.name} has left the battlefield"
      else
        g.withLegalKindPermanent controller kind targets (fun g o =>
          let (g, ex) := g.move o.id .exile none
          let src := g.object! src.id
          let g := g.setObject { src with linkedExile := src.linkedExile.push ex }
          g.logMsg s!"{o.name} is exiled until {src.name} leaves the battlefield") sourceId illegal
    | none => g
  | .destroyEachTarget =>
    targets.foldl (fun g t =>
      match t with
      | Target.permanent id =>
        match g.findObject? id with
        | some o =>
          if o.isOnBattlefield && g.canBeTargetedBy controller o then g.destroyPermanent o
          else g.illegalAbilityTarget t
        | none => g
      | _ => g) g
  | .damageEachOpponent n =>
    g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid n (source := src?))
  | .damageAny n =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.player pid => g.dealDamageToPlayer pid n (source := src?)
      | Target.permanent id => g.dealDamageFrom srcName (g.object! id) n (source := src?)
      | Target.card _ => g) sourceId illegal
  | .returnFromGyToBattlefieldTapped =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        let (g, newId) := g.returnCardToBattlefield controller id 0 (tapped := true)
        g.afterLandEnters (g.object! newId)
      | _ => g) sourceId illegal
  | .searchBasicLandTapped => g.resolveSearchBasicLandTapped controller
  | .searchLandsTapped n => g.searchLandsOntoBattlefieldTapped controller n (fun _ => true)
  | .searchEnchantmentToHand =>
    g.resolveLibrarySearchToHand controller (·.isEnchantment) "enchantment card"
  | .tappedHeartwoods n => g.createKindTokens controller .heartwood n (tapped := true)
  | .eachOpponentSacrificesCreature =>
    g.beginSacrificeCreatures ((g.livingOpponents controller).map (·.id)) #[]
  | .reflexiveDamageAnyTarget n =>
    g.putReflexiveTrigger controller sourceId
      { targeting := .of .playerOrCreature, resolution := .fra (.damageAny n)
        phrase := s!"This deals {n} damage to any target" }
  | .reflexiveDestroyPerOpponent =>
    g.putReflexiveTrigger controller sourceId
      { targeting := .of (g.perOpponentKind controller
          { noun := "up to one target creature or planeswalker that player controls"
            types := #[.creature, .planeswalker] })
        allowsZeroTargets := true
        resolution := .fra .destroyEachTarget
        phrase := "For each opponent, destroy up to one target creature or planeswalker that player controls" }
  | .reflexiveReturnLandTapped =>
    g.putReflexiveTrigger controller sourceId
      { targeting := .of (.filtered { noun := "target land card from your graveyard"
                                      zone := .yourGraveyard, types := #[.land] })
        resolution := .fra .returnFromGyToBattlefieldTapped
        phrase := "Return target land card from your graveyard to the battlefield tapped" }

  | .emrakulGrantMana
  | .nextSpellCantBeCountered
  | .identityEcho
  | .destroyDrawIfLegendaryEnchantment
  | .plusOneThenChooseKeyword _
  | .chooseKeyword _
  | .heartwoodThenPowerPerArtifact
  | .cadetThenTeamHaste
  | .graveyardCardToLibraryBottom
  | .destroyAllCreatures
  | .ownerShufflesIntoLibrary
  | .grantCombatDamageDrawTwo
  | .returnTargetThenPlusOneSource
  | .pumpPerArtifact
  | .plusOneOnEachWithPlusOne
  | .bounceEachTarget
  | .drawThreeThenCountersPerHand
  | .surveilReturnNoncreatureNonland
  | .addBlueNoncreatureOnly
  | .tapAndStunX
  | .emblemDrawOnCast
  | .empowerJacePerIsland
  | .attackersGetMinusFiveUntilYourTurn
  | .exileOpponentLibrariesButBottom
  | .minusFourMinusOneUntilYourTurn
  | .eachPlayerSacrificesThenBeast
  | .eachOpponentDiscardsTwoDrawPerShort
  | .discardHandDrawPerCreature
  | .damageEachCreatureExceptYourTokens _
  | .emblemCreaturesGetTwoTwo
  | .untapTargets
  | .attackersGetTwoTwoTrampleUntilYourTurn
  | .plusOnePerLand
  | .maySacrificeCreatureForBeast
  | .damageUpToOneAndPlayer _
  | .beastToken
  | .causeGetsPump _ _
  | .attackersOfPlayerGetTwoTwoTrample
  | .putCauseCountersOnSource
  | .mayMoveSourceCountersToTarget
  | .mayPayThenProliferate _ _
  | .proliferate _
  | .becomeArtifactCreatureUntilEot
  | .queueMshReflexive _ _
  | .mshReflexive _ _
  | .hawkeyeArrows _
  | .zemoBoastCopies
  | .copySourceSpellXTimes
  | .extort =>
    g.applyFraAbility controller effect r targets sourceId

end Game
end Mtg.Engine
