import Mtg.Engine.Game.FraAbilities
import Mtg.Engine.Game.FrcResolve

/-!
# Reality Fracture effect resolution

`applyFra` resolves former Reality Fracture steps of `Resolution` for
spells, activated abilities, and triggered abilities. Choices made while
one resolves leave a `Pending.fraChoice`; `FraChoices` finishes them.
-/

namespace Mtg.Engine
namespace Game

partial def applyFra (g : Game) (controller : PlayerId) (effect : Effect) (r : Resolution)
    (targets : Array Target) (sourceId : Option ObjectId)
    (lastKnownPower : Option Int := none) : Game :=
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.damageSourceById?).orElse (fun _ => sourceId.bind g.damageSourceById?)
  match r with
  | .frc e => g.applyFrc controller effect e targets sourceId (lastKnownPower := lastKnownPower)
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
              (g.ceaseToExist o.id (cause := some (.stateBased .copyOutsideStackOrBf))).logMsg
                s!"The copy of {o.name} ceases to exist (CR 704.5e)"
            else g.returnToHand id o.owner
          else g
        | none => g
      | Target.player _ => g) sourceId illegal
  | .exileTarget =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let (g, _) := g.move o.id .exile none
      g.logMsg s!"{o.name} is exiled") sourceId illegal
  | .destroyDrawIfNotAttacking =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let wasAttacking := o.status.attacking
      let ctrl := (g.controllerOf o).getD o.owner
      let g := g.destroyPermanent o
      if wasAttacking then g else g.draw ctrl 1) sourceId illegal
  | .damageEachPlayer n =>
    if n == 0 then g
    else
      g.withBatch (g.resolvingBatchCause controller sourceId) fun g =>
        g.livingPlayers.foldl (fun g pl => g.dealDamageToPlayer pl.id n (source := src?)) g
  | .damageSourceAt index n =>
    match g.legalPermanentAt? controller kind targets index sourceId with
    | some o => g.dealDamageFrom srcName o n (source := src?)
    | none => g.logMsg "The target is no longer legal"
  | .plusOneAt index n =>
    match g.legalPermanentAt? controller kind targets index sourceId with
    | some o => g.addPlusOnePlusOneTo o n
    | none => g
  | .returnFromGyToBattlefield plusOnes =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        let (g, newId) := g.returnCardToBattlefield controller id plusOnes
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishPostStep 20 controller 0 none (some id) (shuffle := false))
        else
          g.afterPermanentEnters (g.object! newId)
      | _ => g) sourceId illegal
  | .returnFromGyToHand =>
    -- `none` so an “up to one” sequence with no target still continues.
    -- An announced illegal target is reported by `withLegalTarget`.
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        match g.findObject? id with
        | some o => g.returnToHand id o.owner
        | none => g
      | _ => g) sourceId none
  | .destroyAllNotChosenType =>
    let chosen := g.chooseCreatureTypeFor controller
    let g := g.logMsg s!"{(g.player controller).name} chooses {chosen}"
    let preBf := g.battlefield
    let doomed := (preBf.filter (fun o => g.isCreature o && !g.hasSubtype o chosen)).map (·.id)
    g.withBatch none fun g =>
      g.destroyPermanentsLoop doomed (preBattlefield := some preBf)
  | .searchPlaneswalkerToTop =>
    g.beginLibrarySearch controller (·.isPlaneswalker) "a planeswalker card" .topAfterShuffle
  | .plusOneOnEachTarget n =>
    g.withBatch none fun g =>
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
        g.isPermanentCard o && !g.isLand o && !g.isAura o))
    let g := ids.foldl (fun g id =>
      match g.findObject? id with
      | some o => g.logMsg s!"{o.name} returns to the battlefield"
      | none => g) g
    g.withBatch none fun g =>
      g.putToBattlefieldLoop controller ids
  | .drawMilledThisTurn =>
    g.withLegalKindPlayer controller kind targets (fun g pid =>
      g.draw controller (g.loggedMilled pid)) sourceId illegal
  | .exileAllCreaturesEmpower =>
    let creatures := g.battlefield.filter (g.isCreature ·)
    let g := g.withBatch none fun g =>
      creatures.foldl (fun g o =>
        let nm := g.name o
        let (g, _) := g.move o.id .exile none
        g.logMsg s!"{nm} is exiled") g
    g.empowerJace controller creatures.size
  | .drawGreatestPowerLoseLife =>
    let n := (g.greatestPowerAmongCreatures controller).toNat
    let before := g.loggedDraws controller
    let g := g.draw controller n
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep 13 controller before)
    else
      let drawn := g.loggedDraws controller - before
      g.loseLife controller drawn
  | .revealHandDiscardNonland permanentOnly =>
    g.withLegalKindPlayer controller kind targets (fun g pid =>
      g.beginRevealDiscard controller pid permanentOnly) sourceId illegal
  | .discardHand =>
    g.withBatch none fun g =>
      (g.player controller).hand.foldl (fun g id => g.discardFromHand controller id) g
  | .drawPerCreatureYouControl =>
    g.draw controller (g.creaturesControlledBy controller).size
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
    match g.resolvingSpell.bind g.findObject? with
    | some spell =>
      if spell.zone == .stack && !spell.isCopy &&
          (g.sphinxsApproachesInGraveyard controller).size ≥ 4 then
        g.beginFraChoice controller (.sphinxsApproach spell.id)
          s!"{(g.player controller).name} may exile Sphinx's Approach and four cards named Sphinx's Approach"
      else g
    | none => g
  | .plusOneOnWizardTokensExceptRecent =>
    g.withBatch none fun g =>
      (g.permanentsOf controller).foldl (fun g o =>
        if !g.recentTokenIds.contains o.id && o.printed.isToken && g.hasSubtype o .wizard then
          g.addPlusOnePlusOneTo o 1
        else g) g
  | .damageEachOppCreatureAndPlaneswalker n =>
    let victims := g.battlefield.filter (fun o =>
      (g.isCreature o || g.isPlaneswalker o) && (g.controllerOf o).isSome &&
        !g.controlledBy o controller)
    if n == 0 || victims.isEmpty then g
    else
      g.withBatch (g.resolvingBatchCause controller sourceId) fun g =>
        victims.foldl (fun g o =>
          match g.findObject? o.id with
          | some o => g.dealDamageFrom srcName o n (source := src?)
          | none => g) g
  | .loseAbilitiesAt index =>
    match g.legalPermanentAt? controller kind targets index sourceId with
    | none => g.logMsg "The target is no longer legal"
    | some o =>
      let nm := g.name o
      let g := g.createEffect (.losesAbilitiesUntilEot o.id)
      g.logMsg s!"{nm} loses all abilities until end of turn"
  | .powerDamageFromTo fromIdx toIdx =>
    match g.legalPermanentAt? controller kind targets toIdx sourceId with
    | none => g.logMsg "The target is no longer legal. No damage is dealt"
    | some victim =>
      match g.legalPermanentAt? controller kind targets fromIdx sourceId with
      | some striker =>
        g.dealDamageFrom (g.name striker) (g.object! victim.id) (max (g.power striker) 0)
          (source := some striker)
      | none => g.logMsg "The target is no longer legal. No damage is dealt"
  | .clashOfElements =>
    let sid := sourceId.orElse (fun _ => g.resolvingSpell)
    g.withLegalKindPermanent controller kind targets (fun g o =>
      g.beginFraChoice o.owner (.topOrBottomDamage o.id 2 sid)
        s!"{(g.player o.owner).name} may put {g.name o} on top of their library") sourceId illegal
  | .entrustTheSpark =>
    if (g.permanentsOf controller).any (g.isPlaneswalker ·) then
      g.beginFraChoice controller .maySacrificePlaneswalker
        s!"{(g.player controller).name} may sacrifice a planeswalker"
    else g.logMsg s!"{(g.player controller).name} controls no planeswalker to sacrifice"
  | .plusOnePerThreeGraveyardOnRecentIfFromGy =>
    let fromGy := g.resolvingSpell.any g.castFromGraveyard
    let counters := if fromGy then (g.player controller).graveyard.size / 3 else 0
    if counters == 0 then g
    else
      g.withBatch none fun g =>
        g.recentTokenIds.foldl (fun g id =>
          match g.findObject? id with
          | some o => if o.isOnBattlefield then g.addPlusOnePlusOneTo o counters else g
          | none => g) g
  | .grantHasteToRecentTokens =>
    g.withBatch none fun g =>
      g.recentTokenIds.foldl (fun g id =>
        match g.findObject? id with
        | some o => g.grantKeywordsUntilEot o Keyword.haste
        | none => g) g
  | .drawOneOrTwoIfNotFromHand =>
    let fromHand := g.resolvingSpell.any g.castFromHand
    g.draw controller (if fromHand then 1 else 2)
  | .destroyAt index =>
    match g.legalPermanentAt? controller kind targets index sourceId with
    | some o => g.destroyPermanent o
    | none => g.logMsg "The target is no longer legal"
  | .plusOneOnCreaturesOfPlayerAt index =>
    match targets[index]? with
    | some t@(Target.player pid) =>
      if g.targetLegalAt controller kind index t sourceId then
        g.withBatch none fun g =>
          (g.creaturesControlledBy pid).foldl (fun g o => g.addPlusOnePlusOneTo o 1) g
      else g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | .exileReturnBrieflyIfMvAtMost n =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      -- Ruling: the mana value is that of the permanent as it last existed
      -- on the battlefield.
      let mv := g.objectManaValue o
      let oName := o.name
      let (g, cause) := g.allocDelayedCause (some controller) sourceId
      let (g, exiled) := g.move o.id .exile none (cause := some cause)
      let g := g.logMsg s!"{oName} is exiled"
      if mv ≤ n && !o.printed.isToken then
        let (g, back) := g.putOntoBattlefield exiled controller (tapped := true) (cause := some cause)
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement
            (.finishPostStep 14 controller 0 sourceId (some exiled) (cause := some cause))
        else
          let g := g.logMsg s!"{oName} returns to the battlefield tapped under {(g.player controller).name}'s control"
          let src := (sourceId.bind g.findObject?).orElse (fun _ => g.findObject? back)
          let g := g.registerDelayedTrigger { controller, source := src, kind := .endStepExile back, cause }
          g.afterPermanentEnters (g.object! back)
      else g) sourceId illegal
  | .eachPlayerMayWheel n =>
    match g.apnapFrom.toList with
    | [] => g
    | p :: rest =>
      g.beginFraChoice p (.mayWheel n rest.toArray)
        s!"{(g.player p).name} may discard their hand and draw {n} cards"
  | .mountainsAddExtraRed =>
    let g := g.createEffect (.mountainExtraRedThisTurn controller)
    g.logMsg s!"Until end of turn, whenever {(g.player controller).name} taps a Mountain for mana, they add an additional \{R}"
  | .searchLandToGraveyard =>
    g.beginLibrarySearch controller (·.isLand) "a land card" .graveyard
  | .counterTarget =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id => g.counterStackSpell id
      | _ => g) sourceId illegal
  | .counterUnlessPays n =>
    g.withLegalKindTarget controller kind targets (fun g _ =>
      g.beginPayOrLetCounter targets n) sourceId illegal
  | .destroyTarget =>
    g.withLegalKindPermanent controller kind targets (fun g o => g.destroyPermanent o)
      sourceId illegal
  | .damageExileIfDies n =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let g := g.createEffect (.exileIfDiesUntilEot o.id)
      g.dealDamageFrom srcName (g.object! o.id) n (source := src?)) sourceId illegal
  | .millMayPutPermanentGainLife n life =>
    let before := (g.player controller).graveyard.size
    let g := g.mill controller n
    let gy := (g.player controller).graveyard
    let milled := gy.extract before gy.size
    let choices := milled.filter (fun id => (g.findObject? id).any (g.isPermanentCard ·))
    if choices.isEmpty then g.gainLife controller life
    else
      g.beginFraChoice controller (.mayPutMilledPermanent choices life)
        s!"{(g.player controller).name} may put a permanent card milled this way into their hand"
  | .chooseTriggerModes _ => g
  | .untapAllLandsYouControl =>
    g.withBatch none fun g =>
      (g.permanentsOf controller).foldl (fun g o =>
        if g.isLand o && o.status.tapped then g.applyPermanentAction (g.object! o.id) .untap
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
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep 15 controller 0 sourceId)
    else
      let n := Nat.min 2 (g.player controller).hand.size
      if n == 0 then g
      else
        g.beginFraChoice controller (.discardThenStun n sourceId)
          s!"{(g.player controller).name} discards {n} card(s)"
  | .copyTokenOfSourceIfNotToken =>
    match sourceId with
    | none => g
    | some id =>
      let copiable? : Option (CardDef × Bool) :=
        match g.findObject? id with
        | some card => some (g.copiableValues card, card.printed.isToken)
        | none =>
          match g.lastKnownBefore? id with
          | some eo => some (eo.copiable.getD eo.toCardDef, eo.token)
          | none =>
            match g.followMovedToZone? id (fun | .graveyard _ => true | _ => false) with
            | some card => some (g.copiableValues card, card.printed.isToken)
            | none => none
      match copiable? with
      | some (base, false) =>
        let g := g.change (.recentTokenIds #[])
        let (g, tok) := g.createToken controller { base with isToken := true } (recordRecent := true)
        let g := g.logMsg s!"{(g.player controller).name} creates a token copy of {base.name}"
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishPostStep 16 controller)
        else if tok.zone == .battlefield then
          g.recentTokenIds.foldl (fun g tid =>
            match g.findObject? tid with
            | some entered => if entered.isOnBattlefield then g.afterPermanentEnters entered else g
            | none => g) g
        else g
      | some (_, true) => g
      | none => g.logMsg "The card can't be found"
  | .returnSourceFromGy toHand tapped plusOnes =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.zone != .graveyard o.owner then g.logMsg s!"{o.name} is no longer in the graveyard"
      else if toHand then g.returnToHand o.id o.owner
      else
        let (g, newId) := g.returnCardToBattlefield controller o.id plusOnes (tapped := tapped)
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishPostStep 20 controller 0 none (some o.id) (shuffle := false))
        else
          g.afterPermanentEnters (g.object! newId)
    | none => g.logMsg "The card is no longer in the graveyard"
  | .mayPayThenDestroyPerOpponent n =>
    g.beginFraChoice controller (.mayPayThen n .reflexiveDestroyPerOpponent sourceId)
      s!"{(g.player controller).name} may pay \{{n}}"
  | .damageX =>
    let x := (sourceId.bind g.chosenXOf?).getD 0
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.player pid => g.dealDamageToPlayer pid x (source := src?)
      | Target.permanent id => g.dealDamageFrom srcName (g.object! id) x (source := src?)
      | Target.card _ => g) sourceId illegal
  | .creaturesGetPowerPerArtifact =>
    let n : Int := Int.ofNat ((g.permanentsOf controller).filter (g.isArtifact ·)).size
    g.withBatch none fun g =>
      (g.creaturesControlledBy controller).foldl (fun g o =>
        g.pumpPermanent (g.object! o.id) n 0) g
  | .plusOnesEqualToHandOnEachCreature =>
    let x := (g.player controller).hand.size
    if x == 0 then g
    else
      g.withBatch none fun g =>
        ((g.creaturesControlledBy controller).map (·.id)).foldl (fun g id =>
          match g.findObject? id with
          | some o => g.addPlusOnePlusOneTo o x
          | none => g) g
  | .searchCardThenDiscardRandom =>
    g.beginLibrarySearch controller (fun _ => true) "card" .handThenDiscardRandom
  | .grantFlashbackUntilEot =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        match g.findObject? id with
        | some o =>
          (g.createEffect (.flashbackUntilEot o.id)).logMsg
            s!"{o.name} gains flashback until end of turn"
        | none => g
      | _ => g) sourceId illegal
  | .mayDiscardThenDamage n =>
    if (g.player controller).hand.isEmpty then g
    else
      g.beginFraChoice controller (.mayDiscardThen (.reflexiveDamageAnyTarget n) sourceId)
        s!"{(g.player controller).name} may discard a card"
  | .maySearchLandsEqualDamage =>
    let n := ((lastKnownPower.orElse (fun _ => g.resolvingAbility.bind g.lastKnownPowerOf?)).getD 0).toNat
    if n == 0 then g
    else
      g.beginFraChoice controller (.mayThen (.searchLandsTapped n) sourceId)
        s!"{(g.player controller).name} may search for up to {n} land cards"
  | .maySearchBasicLandTapped =>
    g.beginFraChoice controller (.mayThen .searchBasicLandTapped sourceId)
      s!"{(g.player controller).name} may search for a basic land card"
  | .returnCauseTapped =>
    match (g.resolvingAbilityObject?.bind (·.fraCauseId)).bind
        (fun id => g.followMovedToZone? id (fun | .graveyard _ => true | _ => false)) with
    | some card =>
      if card.zone == .graveyard card.owner then
        let cardName := card.name
        let (g, newId) := g.putOntoBattlefield card.id card.owner (tapped := true)
        let g := g.logMsg s!"{cardName} returns to the battlefield tapped"
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishPostStep 20 card.owner 0 none (some card.id) (shuffle := false))
        else
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
    let cause := (g.resolvingAbilityObject?.bind (·.fraCauseId)).bind g.damageSourceById?
    let name := (cause.map g.name).getD "The creature"
    if n == 0 then g
    else
      g.withBatch (g.resolvingBatchCause controller sourceId) fun g =>
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
    if (g.permanentsOf controller).any (g.isLand ·) then
      g.beginFraChoice controller (.maySacrificeThen #[.land] (.tappedHeartwoods 2) sourceId)
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
          if ids.contains id || o.zone != .graveyard controller || g.isLand o then acc
          else
            match (g.types o).find? (fun ty => !used.contains ty) with
            | some ty => (ids.push id, used.push ty)
            | none => acc
        | none => acc
      | _ => acc) (#[], #[])
    let (g, cause?) : Game × Option EventCause :=
      if ids.isEmpty then (g, none)
      else
        let (g, c) := g.allocDelayedCause (some controller) sourceId
        (g, some c)
    let (g, copies) := ids.foldl (fun (acc : Game × Array ObjectId) id =>
      let (g, cs) := acc
      let card := g.object! id
      let (g, ex) := g.move id .exile none (cause := cause?)
      let g := g.logMsg s!"{card.name} is exiled"
      let printed := g.copiableValues (g.object! ex)
      -- Permanent spells cast this way become tokens.
      let copyId : ObjectId := ⟨g.nextObjectId⟩
      let copyTs := g.timestamp + 1
      let copyObj : GameObject := {
        id := copyId
        printed := { printed with isToken := printed.isPermanentCard }
        owner := controller
        controller := some controller
        zone := .exile
        timestamp := copyTs
        isCopy := true
      }
      let g := g.record (GameEvent.created g.turnNumber controller (g.snapshot copyObj)
        (cause := g.resolveOptionalCause cause? (fallbackSrc := sourceId) (fallbackCtrl := some controller)))
      let g := g.createEffect (.playPermission copyId {
        player := controller,
        whileExiled := true, withoutManaCost := true, ignoreTiming := true })
        (cause := cause?)
      (g, cs.push copyId)) (g, #[])
    if copies.isEmpty then g
    else
      g.beginFraChoice controller (.castCopiesFree copies 6 copies.size)
        s!"{(g.player controller).name} may cast copies with total mana value 6 or less"
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
    if (g.player controller).lost then g
    else
      match g.fraCause? with
      | some spell =>
        if spell.zone != .stack then g.logMsg s!"{spell.name} is no longer on the stack"
        else
          let copyId : ObjectId := ⟨g.nextObjectId⟩
          let copySnap : EventObject := {
            (g.snapshot spell) with
            id := some copyId
            owner := controller
            controller := some controller
            zone := .stack
            isCopy := true
            isCommander := false
          }
          let g := g.record (GameEvent.stackObjectCopied g.turnNumber spell.id copySnap controller
            (cause := g.resolveOptionalCause (g.resolvingOneShotCause controller sourceId)
              (fallbackSrc := sourceId) (fallbackCtrl := some controller)))
          g.logMsg s!"A copy of {spell.name} is created"
      | none => g.logMsg "The spell is no longer on the stack"
  | .eyeOfJace =>
    let g := g.beginSurveil controller 1
    match g.pending with
    | .surveil .. => g.change (.fraAfterLook (some (controller, sourceId, .eyeOfJaceCheck)))
    | _ => g.applyFra controller effect .eyeOfJaceCheck targets sourceId
  | .eyeOfJaceCheck =>
    if (g.player controller).graveyard.size < 7 then g
    else
      match sourceId.bind g.findObject? with
      | some o =>
        if !o.isOnBattlefield then g
        else
          let (g, cause?) : Game × Option EventCause :=
            match g.currentResolvingContext? with
            | some (src, ctrl) =>
              let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some controller)) (src.orElse (fun _ => sourceId))
              (g, some c)
            | none => (g, none)
          let g := g.sacrificeToGraveyard o s!"{(g.player controller).name} sacrifices {o.name}" (cause := cause?)
          if let .chooseReplacement .. := g.pending then
            g.chainPendingReplacement (.finishPostStep 17 controller 2 (some o.id) (cause := cause?))
          else
            g.drainOpponents controller 2 (some o) (cause := cause?)
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
    g.withBatch none fun g =>
      targets.foldl (fun g t =>
        match t with
        | Target.permanent id =>
          match g.findObject? id with
          | some o =>
            if o.isOnBattlefield && g.isCreature o && g.canBeTargetedBy controller o then
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
  | .maySacrificeThenEdict =>
    if (g.permanentsOf controller).any (fun o => g.isCreature o || g.isPlaneswalker o) then
      g.beginFraChoice controller
        (.maySacrificeThen #[.creature, .planeswalker] .eachOpponentSacrificesCreature sourceId)
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
    let causeId? := g.resolvingAbilityObject?.bind (·.fraCauseId)
    let g := g.draw controller 1
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep 18 controller 0 causeId?)
    else
      let n := g.loggedDiscards controller
      match g.fraCause? with
      | some o => if o.isOnBattlefield && n > 0 then g.addPlusOnePlusOneTo o n else g
      | none => g
  | .kothGeomancer =>
    let isMtn :=
      match g.fraCause? with
      | some land => g.hasSubtype land .mountain
      | none =>
        match (g.resolvingAbilityObject?.bind (·.fraCauseId)).bind g.lastKnownBefore? with
        | some eo => eo.subtypes.contains .mountain || eo.changeling
        | none => false
    let g := g.dealDamageToEachOpponent controller 1 (source := src?)
    if !isMtn then g
    else if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep 19 controller 1 sourceId)
    else
      g.addManaLogged controller #[.colored .red] (source := sourceId)
  | .fblthpSearch =>
    let x := (sourceId.bind g.chosenXOf?).getD 0
    let (pickedIds, _) := (g.player controller).library.foldl
      (fun (acc : Array ObjectId × Array String) id =>
        let (picked, names) := acc
        if names.size ≥ x then acc
        else
          match g.findObject? id with
          | some o =>
            if isBasicLandCard (g.baseCard o) && !names.contains (g.name o) then
              (picked.push id, names.push (g.name o))
            else acc
          | none => acc) (#[], #[])
    let (g, cause) := g.allocDelayedCause (some controller) sourceId
    let g := g.record (GameEvent.searched g.turnNumber controller controller pickedIds (cause := some cause))
    let g :=
      if pickedIds.isEmpty then g
      else g.record (GameEvent.revealed g.turnNumber controller pickedIds (cause := some cause))
    let g := pickedIds.foldl (fun g id =>
      match g.findObject? id with
      | some o =>
        let g := g.logMsg s!"{(g.player controller).name} reveals {o.name}"
        (g.move id (.hand controller) none (cause := some cause)).1
      | none => g) g
    g.shuffleLibrary controller
  | .untapAllTokensYouControl =>
    g.withBatch none fun g =>
      (g.permanentsOf controller).foldl (fun g o =>
        if o.printed.isToken && o.status.tapped then g.applyPermanentAction (g.object! o.id) .untap
        else g) g
  | .mayDiscardThenSearchEnchantment =>
    if (g.player controller).hand.isEmpty then g
    else
      g.beginFraChoice controller (.mayDiscardThen .searchEnchantmentToHand sourceId)
        s!"{(g.player controller).name} may discard a card"
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
    g.withBatch none fun g =>
      targets.foldl (fun g t =>
        match t with
        | Target.permanent id =>
          match g.findObject? id with
          | some o =>
            let shielded :=
              match g.controllerOf o with
              | some c =>
                (g.permanentsOf c).any (fun src =>
                  (g.baseCard src).creaturesCantGetMinusCounters && g.retainsPrintedAbilities src)
              | none => false
            if o.isOnBattlefield && g.isCreature o && g.canBeTargetedBy controller o && x > 0 &&
                !shielded then
              (g.recordPutCounters o.id .minusOneMinusOne x (byPlayer := some controller)).logMsg
                s!"{x} -1/-1 counter(s) are put on {g.name o}"
            else g
          | none => g
        | _ => g) g
  | .drawPerColorAmongOtherArtifacts =>
    let colors := (g.permanentsOf controller).foldl (fun (acc : ColorSet) o =>
      if g.isArtifact o && some o.id != sourceId then ColorSet.union acc (g.colors o)
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
          let (g, linkCause) := g.allocDelayedCause (some controller) sourceId
          let (g, ex) := g.move o.id .exile none (cause := some linkCause)
          let g := g.changeObject src.id (.pushLinkedExile ex)
          g.logMsg s!"{o.name} is exiled until {src.name} leaves the battlefield") sourceId illegal
    | none => g
  | .destroyEachTarget =>
    let preBf := g.battlefield
    let (g, validIds) := targets.foldl (fun (acc : Game × Array ObjectId) t =>
      let (g, ids) := acc
      match t with
      | Target.permanent id =>
        match g.findObject? id with
        | some o =>
          if o.isOnBattlefield && g.canBeTargetedBy controller o then (g, ids.push id)
          else (g.illegalAbilityTarget t, ids)
        | none => (g, ids)
      | _ => (g, ids)) (g, #[])
    g.withBatch none fun g =>
      g.destroyPermanentsLoop validIds (preBattlefield := some preBf)
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
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishPostStep 20 controller 0 none (some id) (shuffle := true))
        else
          g.afterLandEnters (g.object! newId)
      | _ => g) sourceId illegal
  | .searchBasicLandTapped => g.resolveSearchBasicLandTapped controller
  | .searchLandsTapped n =>
    g.beginLibrarySearch controller (·.isLand) "a land card" (.battlefield true) (count := n)
  | .searchEnchantmentToHand =>
    g.resolveLibrarySearchToHand controller (·.isEnchantment) "enchantment card"
  | .tappedHeartwoods n => g.createKindTokens controller .heartwood n (tapped := true)
  | .eachOpponentSacrificesCreature =>
    g.beginSacrificeCreatures ((g.livingOpponents controller).map (·.id)) #[]
  | .reflexiveDamageAnyTarget n =>
    g.putReflexiveTrigger controller sourceId
      { targeting := .of .playerOrCreature, resolution := .damageAny n
        phrase := s!"This deals {n} damage to any target" }
  | .reflexiveDestroyPerOpponent =>
    g.putReflexiveTrigger controller sourceId
      { targeting := .of (g.perOpponentKind controller
          { noun := "up to one target creature or planeswalker that player controls"
            types := #[.creature, .planeswalker] })
        allowsZeroTargets := true
        resolution := .destroyEachTarget
        phrase := "For each opponent, destroy up to one target creature or planeswalker that player controls" }
  | .reflexiveReturnLandTapped =>
    g.putReflexiveTrigger controller sourceId
      { targeting := .of (.filtered { noun := "target land card from your graveyard"
                                      zone := .yourGraveyard, types := #[.land] })
        resolution := .returnFromGyToBattlefieldTapped
        phrase := "Return target land card from your graveyard to the battlefield tapped" }

  | .emrakulGrantMana
  | .nextSpellCantBeCountered
  | .identityEcho
  | .destroyDrawIfLegendaryEnchantment
  | .chooseKeyword _
  | .graveyardCardToLibraryBottom
  | .destroyAllCreatures
  | .ownerShufflesIntoLibrary
  | .grantCombatDamageDrawTwo
  | .sourceGetsPowerPerArtifact
  | .pumpPerArtifact
  | .plusOneOnEachWithPlusOne
  | .bounceEachTarget
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
  | .damageEqualSourcePower
  | .returnSourceToHand
  | .sarumanExileCopyMayCast
  | .extort =>
    g.applyFraAbility controller effect r targets sourceId
  | _ => g

end Game
end Mtg.Engine
