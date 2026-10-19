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
    (targets : Array Target) (sourceId : Option ObjectId) : Game :=
  match g.applyFrc? controller effect r targets sourceId with
  | some g => g
  | none =>
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  match r with
  | .returnToHand .target _ =>
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
  | .exile .target .forLater .none =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let (g, _) := g.move o.id .exile none
      g.logMsg s!"{o.name} is exiled") sourceId illegal
  | .destroy .target .drawIfNotAttacking =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let wasAttacking := o.status.attacking
      let ctrl := o.controller.getD o.owner
      let g := g.destroyPermanent o
      if wasAttacking then g else g.draw ctrl 1) sourceId illegal
  | .dealDamage (.fixed n) (.player .eachPlayer) _ =>
    g.livingPlayers.foldl (fun g pl => g.dealDamageToPlayer pl.id n.toNat (source := src?)) g
  | .dealDamage (.fixed n) (.targetAt index) _ =>
    if kind.isOptionalSlot 0 then
      match index with
      | 0 =>
        match targets.find? (fun | Target.permanent _ => true | _ => false) with
        | some t@(Target.permanent id) =>
          if g.targetLegalAt controller kind 0 t sourceId then
            g.dealDamageFrom srcName (g.object! id) n.toNat (source := src?)
          else g.illegalAbilityTarget t
        | _ => g
      | _ =>
        match targets.find? (fun | Target.player _ => true | _ => false) with
        | some t@(Target.player pid) =>
          if g.targetLegalAt controller kind index t sourceId then
            g.dealDamageToPlayer pid n.toNat (source := src?)
          else g.illegalAbilityTarget t
        | _ => g
    else
      match g.legalPermanentAt? controller kind targets index sourceId with
      | some o => g.dealDamageFrom srcName o n.toNat (source := src?)
      | none => g.logMsg "The target is no longer legal"
  | .putCounters (.ofKind .plusOnePlusOne n) (.targetAt index) =>
    match g.legalPermanentAt? controller kind targets index sourceId with
    | some o => g.addPlusOnePlusOneTo o n
    | none => g
  | .put .graveyardCard .asPrinted mod =>
    let plusOnes := match mod with
      | .entering [.counter .plusOnePlusOne n _] => n
      | _ => 0
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        let (g, newId) := g.returnCardToBattlefield controller id plusOnes
        g.afterPermanentEnters (g.object! newId)
      | _ => g) sourceId illegal
  | .returnToHand (.target .graveyardCard) _ =>
    -- `none` so an “up to one” sequence with no target still continues.
    -- An announced illegal target is reported by `withLegalTarget`.
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        match g.findObject? id with
        | some o => g.returnToHand id o.owner
        | none => g
      | _ => g) sourceId none
  | .destroy .creaturesNotChosenType _ =>
    let chosen := g.chooseCreatureTypeFor controller
    let g := g.logMsg s!"{(g.player controller).name} chooses {chosen}"
    let doomed := g.battlefield.filter (fun o => o.isCreature && !g.hasSubtype o chosen)
    doomed.foldl (fun g o =>
      match g.findObject? o.id with
      | some o => g.destroyPermanent o
      | none => g) g
  | .searchLibrary (.putOnLibrary .top .planeswalkerCard) =>
    g.beginLibrarySearch controller (·.isPlaneswalker) "a planeswalker card" .topAfterShuffle
  | .putCounters (.ofKind .plusOnePlusOne n) (.target .eachPermanent) =>
    targets.foldl (fun g t =>
      match t with
      | Target.permanent id =>
        if g.targetLegalAt controller kind 0 t sourceId then
          g.addPlusOnePlusOneTo (g.object! id) n
        else g.illegalAbilityTarget t
      | _ => g) g
  | .put .allNonlandPermanentsInGraveyard .asPrinted .none =>
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
  | .draw .milledByTargetPlayerThisTurn _ =>
    g.withLegalKindPlayer controller kind targets (fun g pid =>
      g.draw controller (g.player pid).cardsMilledThisTurn) sourceId illegal
  | .exile .allCreatures .forLater .empowerJace =>
    let creatures := g.battlefield.filter (·.isCreature)
    let g := creatures.foldl (fun g o =>
      let (g, _) := g.move o.id .exile none
      g.logMsg s!"{o.name} is exiled") g
    g.empowerJace controller creatures.size
  | .draw .greatestPowerAndLoseLife _ =>
    let n := (g.greatestPowerAmongCreatures controller).toNat
    let before := (g.player controller).cardsDrawnThisTurn
    let g := g.draw controller n
    let drawn := (g.player controller).cardsDrawnThisTurn - before
    g.loseLife controller drawn
  | .discard .chosenNonland =>
    g.withLegalKindPlayer controller kind targets (fun g pid =>
      g.beginRevealDiscard controller pid false) sourceId illegal
  | .discard .chosenNonlandPermanent =>
    g.withLegalKindPlayer controller kind targets (fun g pid =>
      g.beginRevealDiscard controller pid true) sourceId illegal
  | .discard .hand =>
    (g.player controller).hand.foldl (fun g id => g.discardFromHand controller id) g
  | .draw (.perControlled .creature) _ =>
    g.draw controller (g.creaturesControlledBy controller).size
  | .returnToHand .outsideGameOpponentChoice _ =>
    let g := g.materializeSideboard controller
    let names := (g.outsideCards controller).foldl (fun acc o =>
      if acc.contains o.name then acc else acc.push o.name) (#[] : Array String)
    if names.size < 2 then
      g.logMsg s!"{(g.player controller).name} has no two cards with different names outside the game"
    else
      g.beginFraChoice controller .extrapolateReveal
        s!"{(g.player controller).name} may reveal two cards with different names from outside the game"
  | .exile .sphinxsApproach .forLater _ =>
    match g.resolvingSpell.bind g.findObject? with
    | some spell =>
      if spell.zone == .stack && !spell.isCopy &&
          (g.sphinxsApproachesInGraveyard controller).size ≥ 4 then
        g.beginFraChoice controller (.sphinxsApproach spell.id)
          s!"{(g.player controller).name} may exile Sphinx's Approach and four cards named Sphinx's Approach"
      else g
    | none => g
  | .putCounters (.ofKind .plusOnePlusOne 1) .wizardTokensExceptRecent =>
    (g.permanentsOf controller).foldl (fun g o =>
      if !g.recentTokenIds.contains o.id && o.printed.isToken && g.hasSubtype o "Wizard" then
        g.addPlusOnePlusOneTo o 1
      else g) g
  | .dealDamage (.fixed n) .oppCreaturesAndPlaneswalkers _ =>
    let victims := g.battlefield.filter (fun o =>
      (o.isCreature || o.printed.isPlaneswalker) && o.controller.isSome &&
        !o.controlledBy controller)
    victims.foldl (fun g o =>
      match g.findObject? o.id with
      | some o => g.dealDamageFrom srcName o n.toNat (source := src?)
      | none => g) g
  | .lose .allAbilities (.targetAt index) =>
    match g.legalPermanentAt? controller kind targets index sourceId with
    | none => g.logMsg "The target is no longer legal"
    | some o =>
      let g := g.mapObjectStatus o (fun s => { s with losesAbilitiesUntilEot := true })
      g.logMsg s!"{o.name} loses all abilities until end of turn"
  | .dealDamage (.power (.targetAt fromIdx)) (.targetAt toIdx) _ =>
    match g.legalPermanentAt? controller kind targets toIdx sourceId with
    | none => g.logMsg "The target is no longer legal. No damage is dealt"
    | some victim =>
      match g.legalPermanentAt? controller kind targets fromIdx sourceId with
      | some striker =>
        g.dealDamageFrom striker.name (g.object! victim.id) (max (g.power striker) 0)
          (source := some striker)
      | none => g.logMsg "The target is no longer legal. No damage is dealt"
  | .dealDamage (.loyalty (.targetAt fromIdx)) (.targetAt toIdx) _ =>
    match g.legalPermanentAt? controller kind targets toIdx sourceId with
    | none => g.logMsg "The target is no longer legal. No damage is dealt"
    | some victim =>
      match g.legalPermanentAt? controller kind targets fromIdx sourceId with
      | some striker =>
        g.dealDamageFrom striker.name (g.object! victim.id) (Int.ofNat striker.status.loyaltyCounters)
          (source := some striker)
      | none => g.logMsg "The target is no longer legal. No damage is dealt"
  | .putOnLibrary .topOrBottomDamage2 .target =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      g.beginFraChoice o.owner (.topOrBottomDamage o.id 2)
        s!"{(g.player o.owner).name} may put {o.name} on top of their library") sourceId illegal
  | .may (.sacrifice .planeswalker _) (.searchLibrary (.put .planeswalkerCard _ _)) .ifYouDo =>
    if (g.permanentsOf controller).any (·.printed.isPlaneswalker) then
      g.beginFraChoice controller .maySacrificePlaneswalker
        s!"{(g.player controller).name} may sacrifice a planeswalker"
    else g.logMsg s!"{(g.player controller).name} controls no planeswalker to sacrifice"
  | .putCounters .plusOnePerThreeGraveyardIfFromGy .createdToken =>
    let fromGy := (g.resolvingSpell.bind g.findObject?).any (·.castFromGraveyard)
    let counters := if fromGy then (g.player controller).graveyard.size / 3 else 0
    if counters == 0 then g
    else
      g.recentTokenIds.foldl (fun g id =>
        match g.findObject? id with
        | some o => if o.isOnBattlefield then g.addPlusOnePlusOneTo o counters else g
        | none => g) g
  | .grant (.keywords _) .createdToken =>
    g.recentTokenIds.foldl (fun g id =>
      match g.findObject? id with
      | some o => g.grantKeywordsUntilEot o Keyword.haste
      | none => g) g
  | .destroy (.targetAt index) _ =>
    match g.legalPermanentAt? controller kind targets index sourceId with
    | some o => g.destroyPermanent o
    | none => g.logMsg "The target is no longer legal"
  | .putCounters (.ofKind .plusOnePlusOne 1) (.creaturesControlledBy (.targetAt index)) =>
    match targets[index]? with
    | some t@(Target.player pid) =>
      if g.targetLegalAt controller kind index t sourceId then
        (g.creaturesControlledBy pid).foldl (fun g o => g.addPlusOnePlusOneTo o 1) g
      else g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | .exile .target (.returnBrieflyIfMvAtMost n) _ =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      -- Ruling: the mana value is that of the permanent as it last existed
      -- on the battlefield.
      let mv := g.objectManaValue o
      let (g, exiled) := g.move o.id .exile none
      let g := g.logMsg s!"{o.name} is exiled"
      if mv ≤ n && !o.printed.isToken then
        let (g, back) := g.putOntoBattlefield exiled controller (tapped := true)
        let g := g.logMsg s!"{o.name} returns to the battlefield tapped under {(g.player controller).name}'s control"
        let g := { g with delayedEndStep := g.delayedEndStep.push (.exilePermanent back) }
        g.afterPermanentEnters (g.object! back)
      else g) sourceId illegal
  | .discard (.mayWheel n .eachPlayer) =>
    match g.apnapFrom.toList with
    | [] => g
    | p :: rest =>
      g.beginFraChoice p (.mayWheel n rest.toArray)
        s!"{(g.player p).name} may discard their hand and draw {n} cards"
  | .grant .mountainsAddExtraRed .landsYouControl =>
    let g := g.modifyPlayer controller (fun pl =>
      { pl with mountainExtraRedThisTurn := pl.mountainExtraRedThisTurn + 1 })
    g.logMsg s!"Until end of turn, whenever {(g.player controller).name} taps a Mountain for mana, they add an additional \{R}"
  | .searchLibrary (.mill (.fixed 1) _ _) =>
    g.beginLibrarySearch controller (·.isLand) "a land card" .graveyard
  | .chooseModes _ (.fraTrigger _) => g
  | .untap .landsYouControl =>
    (g.permanentsOf controller).foldl (fun g o =>
      if o.printed.isLand && o.status.tapped then g.applyPermanentAction (g.object! o.id) .untap
      else g) g
  | .exile .target .returnImmediately _ =>
    if targets.isEmpty then g
    else
      g.withLegalKindPermanent controller kind targets (fun g o =>
        g.exileThenReturn o "is exiled and returns to the battlefield") sourceId illegal
  | .may (.removeCounters (.upTo 1) .source) (.putCounters (.ofKind .plusOnePlusOne 1) .eachOther) .ifYouDo =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield && o.status.plusOnePlusOne > 0 then
        g.beginFraChoice controller (.mayMovePlusOne o.id)
          s!"{(g.player controller).name} may remove a +1/+1 counter from {o.name}"
      else g
    | none => g
  | .empowerJace (.count .creaturesYouControl) =>
    g.empowerJace controller (g.creaturesControlledBy controller).size
  | .becomePrepared .enchanted false =>
    match (sourceId.bind g.findObject?).bind (·.attachedTo) |>.bind g.findObject? with
    | some host =>
      let g := if host.status.tapped then g else g.becomeTapped host
      g.unprepare (g.object! host.id)
    | none => g.logMsg "The Aura isn't attached to a creature"
  | .putOnLibrary .topOrBottom .target =>
    if targets.isEmpty then g
    else
      g.withLegalKindPermanent controller kind targets (fun g o =>
        g.beginFraChoice o.owner (.topOrBottomDamage o.id 0)
          s!"{(g.player o.owner).name} puts {o.name} on the top or bottom of their library")
        sourceId illegal
  | .discard .drawTwoDiscardTwoStun =>
    let g := g.draw controller 2
    let n := Nat.min 2 (g.player controller).hand.size
    if n == 0 then g
    else
      g.beginFraChoice controller (.discardThenStun n sourceId)
        s!"{(g.player controller).name} discards {n} card(s)"
  | .becomeCopy .sourceIfNotToken =>
    match sourceId with
    | none => g
    | some id =>
      match g.findObject? (g.followMoved id) with
      | some card =>
        let (g, tok) := g.createToken controller { card.printed with isToken := true }
        let g := g.logMsg s!"{(g.player controller).name} creates a token copy of {card.name}"
        g.afterPermanentEnters (g.object! tok.id)
      | none => g.logMsg "The card can't be found"
  | .put .source how note =>
    let tapped := how == .tapped
    let plusOnes := match note with
      | .entering [.counter .plusOnePlusOne n _] => n
      | _ => 0
    match sourceId.bind g.findObject? with
    | some o =>
      if o.zone != .graveyard o.owner then g.logMsg s!"{o.name} is no longer in the graveyard"
      else
        let (g, newId) := g.returnCardToBattlefield controller o.id plusOnes (tapped := tapped)
        g.afterPermanentEnters (g.object! newId)
    | none => g.logMsg "The card is no longer in the graveyard"
  | .may (.pay (.mana #[.generic n])) (.queueReflexive (.destroy (.target .eachPermanent) _)) .ifYouDo =>
    g.beginFraChoice controller (.mayPayThen n .reflexiveDestroyPerOpponent sourceId)
      s!"{(g.player controller).name} may pay \{{n}}"
  | .dealDamage .chosenX .target _ =>
    let x := (sourceId.bind g.findObject?).bind (·.chosenX) |>.getD 0
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.player pid => g.dealDamageToPlayer pid x (source := src?)
      | Target.permanent id => g.dealDamageFrom srcName (g.object! id) x (source := src?)
      | Target.card _ => g) sourceId illegal
  | .pump (.count .artifact) (.fixed 0) .creaturesYouControl =>
    let n : Int := Int.ofNat ((g.permanentsOf controller).filter (·.printed.isArtifact)).size
    (g.creaturesControlledBy controller).foldl (fun g o =>
      g.pumpPermanent (g.object! o.id) n 0) g
  | .putCounters .plusOneEqualToHand .creaturesYouControl =>
    let x := (g.player controller).hand.size
    if x == 0 then g
    else
      ((g.creaturesControlledBy controller).map (·.id)).foldl (fun g id =>
        match g.findObject? id with
        | some o => g.addPlusOnePlusOneTo o x
        | none => g) g
  | .searchLibrary (.returnToHand .card _) =>
    g.resolveLibrarySearchToHand controller (fun _ => true) "card"
  | .discard .random =>
    let hand := (g.player controller).hand
    if hand.isEmpty then g
    else
      let (rng, r) := g.rng.next
      let g := { g with rng }
      g.discardFromHandRandomly controller hand[(r.toNat % hand.size)]!
  | .grant .flashback .target =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        match g.findObject? id with
        | some o =>
          (g.setObject { o with flashbackUntilEot := true }).logMsg
            s!"{o.name} gains flashback until end of turn"
        | none => g
      | _ => g) sourceId illegal
  | .may (.discard (.cards 1 .you)) (.queueReflexive (.dealDamage (.fixed n) .target _)) .ifYouDo =>
    if (g.player controller).hand.isEmpty then g
    else
      g.beginFraChoice controller (.mayDiscardThen (.reflexiveDamageAnyTarget n.toNat) sourceId)
        s!"{(g.player controller).name} may discard a card"
  | .may (.searchLibrary (.put .landsEqualDamage .tapped _)) (.sequence []) _ =>
    let n := (g.resolvingAbilityObject?.bind (·.lastKnownPower)).getD 0 |>.toNat
    if n == 0 then g
    else
      g.beginFraChoice controller (.mayThen (.searchLandsTapped n) sourceId)
        s!"{(g.player controller).name} may search for up to {n} land cards"
  | .may (.searchLibrary (.put .basicLand .tapped _)) (.sequence []) .ifYouDo =>
    g.beginFraChoice controller (.mayThen .searchBasicLandTapped sourceId)
      s!"{(g.player controller).name} may search for a basic land card"
  | .put .cause .tapped _ =>
    match g.fraCause? with
    | some card =>
      if card.zone == .graveyard card.owner then
        let (g, newId) := g.putOntoBattlefield card.id card.owner (tapped := true)
        let g := g.logMsg s!"{card.name} returns to the battlefield tapped"
        g.afterPermanentEnters (g.object! newId)
      else g.logMsg s!"{card.name} is no longer in the graveyard"
    | none => g.logMsg "The card is no longer in the graveyard"
  | .sacrifice .source .none =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield then g.sacrificeToGraveyard o s!"{(g.player controller).name} sacrifices {o.name}"
      else g
    | none => g
  | .dealDamage (.fixed n) (.player .eachOpponent) .fromCause =>
    let cause := g.fraCause?
    let name := (cause.map (·.name)).getD "The creature"
    g.forEachOpponent controller (fun g pid =>
      (g.dealDamageToPlayer pid n.toNat (source := cause)).logMsg s!"{name} deals {n.toNat} damage")
  | .revealFromHand .hand (.exile .chosenNonland .untilSourceLeaves _) =>
    g.withLegalKindPlayer controller kind targets (fun g pid =>
      let g := g.revealHand pid
      if (g.revealedHandChoices pid false).isEmpty then
        g.logMsg s!"{(g.player pid).name} has no nonland card"
      else
        g.beginFraChoice controller (.exileFromRevealedHand pid sourceId)
          s!"{(g.player controller).name} chooses a nonland card to exile") sourceId illegal
  | .may (.sacrifice .land) (.createTokens .heartwood (.fixed 2) true _ _) .ifYouDo =>
    if (g.permanentsOf controller).any (·.printed.isLand) then
      g.beginFraChoice controller (.maySacrificeThen .land (.tappedHeartwoods 2) sourceId)
        s!"{(g.player controller).name} may sacrifice a land"
    else g
  | .mayCast .uldarosGraveyardTypes .unlimited .withoutPaying _ =>
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
        castState := { copy.castState with isCopy := true }
        playPermission := some { player := controller, turnEndsRemaining := 0
                                 whileExiled := true, withoutManaCost := true, ignoreTiming := true } }
      (g, cs.push copy.id)) (g, #[])
    if copies.isEmpty then g
    else
      g.beginFraChoice controller (.castCopiesFree copies 6 copies.size)
        s!"{(g.player controller).name} may cast copies with total mana value 6 or less"
  | .exile .graveyardCard .forLater _ | .exile (.target .graveyardCard) .forLater _ =>
    if targets.isEmpty then g
    else
      g.withLegalKindTarget controller kind targets (fun g t =>
        match t with
        | Target.card id =>
          let name := (g.object! id).name
          let (g, _) := g.move id .exile none
          g.logMsg s!"{name} is exiled"
        | _ => g) sourceId illegal
  | .becomeCopy .causingSpell =>
    match g.fraCause? with
    | some spell =>
      if spell.zone != .stack then g.logMsg s!"{spell.name} is no longer on the stack"
      else
        let (g, copy) := g.allocObject spell.printed controller .stack (some controller)
        let g := g.setObject { copy with
          chosenX := spell.chosenX
          castState := { copy.castState with isCopy := true }
          adventurerCard := spell.adventurerCard }
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
  | .surveil (.fixed 1) .eyeOfJace =>
    let g := g.beginSurveil controller 1
    match g.pending with
    | .surveil .. => { g with afterScrySurveil := { g.afterScrySurveil with fraAfterLook := some (controller, sourceId, .eyeOfJaceCheck) } }
    | _ => g.applyFra controller effect (.sacrifice .source .eyeOfJaceIfSevenInGy) targets sourceId
  | .sacrifice .source .eyeOfJaceIfSevenInGy =>
    if (g.player controller).graveyard.size < 7 then g
    else
      match sourceId.bind g.findObject? with
      | some o =>
        if !o.isOnBattlefield then g
        else
          let g := g.sacrificeToGraveyard o s!"{(g.player controller).name} sacrifices {o.name}"
          g.drainOpponents controller 2 (some o)
      | none => g
  | .putCounters (.ofKind .loyalty _) .planeswalkersYouControl => g.loyaltyOnEachPlaneswalkerOf controller
  | .grant (.keywords k) (.cause none) =>
    match g.fraCause? with
    | some o => if o.isOnBattlefield then g.grantKeywordsUntilEot o k else g
    | none => g
  | .untap .source =>
    match sourceId.bind g.findObject? with
    | some o => if o.isOnBattlefield && o.status.tapped then g.applyPermanentAction o .untap else g
    | none => g
  | .putCounters (.ofKind .stun _) (.creaturesControlledBy .eachOpponent) =>
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
  | .dealDamage (.fixed n) (.player (.controller .cause)) _ =>
    match g.fraCauseController? with
    | some pid => g.dealDamageToPlayer pid n.toNat (source := src?)
    | none => g
  | .removeCounters (.upTo n) .target =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      g.removeUpToCountersFrom controller o n) sourceId illegal
  | .may (.sacrifice .creatureOrPlaneswalker) (.sacrifice .eachOpponentsCreature _) .ifYouDo =>
    if (g.permanentsOf controller).any (fun o => o.isCreature || o.printed.isPlaneswalker) then
      g.beginFraChoice controller
        (.maySacrificeThen .creatureOrPlaneswalker .eachOpponentSacrificesCreature sourceId)
        s!"{(g.player controller).name} may sacrifice a creature or planeswalker"
    else g
  | .pump .causePower (.fixed 0) .source =>
    let x : Int :=
      match g.fraCause? with
      | some o => if o.isOnBattlefield then g.power o
                  else (g.resolvingAbilityObject?.bind (·.fraCausePower)).getD 0
      | none => (g.resolvingAbilityObject?.bind (·.fraCausePower)).getD 0
    match sourceId.bind g.findObject? with
    | some o => if o.isOnBattlefield then g.pumpPermanent o x 0 else g
    | none => g
  | .discard .lootThenCountersPerDiscard =>
    if (g.player controller).hand.isEmpty then
      g.applyFra controller effect (.putCounters .plusOnePerDiscardAfterDraw .cause) targets sourceId
    else
      g.beginFraChoice controller
        (.discardThen .drawThenCountersPerDiscard sourceId
          (g.resolvingAbilityObject?.bind (·.fraCauseId)))
        s!"{(g.player controller).name} discards a card"
  | .putCounters .plusOnePerDiscardAfterDraw .cause =>
    let g := g.draw controller 1
    let n := (g.player controller).cardsDiscardedThisTurn
    match g.fraCause? with
    | some o => if o.isOnBattlefield && n > 0 then g.addPlusOnePlusOneTo o n else g
    | none => g
  | .dealDamage (.fixed 1) (.player .eachOpponent) .addRedIfMountain =>
    let g := g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid 1 (source := src?))
    match g.fraCause? with
    | some land => if g.hasSubtype land "Mountain" then g.addManaLogged controller #[.colored .red] else g
    | none => g
  | .searchLibrary (.returnToHand .basicLandsDifferentNamesX _) =>
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
  | .untap .tokensYouControl =>
    (g.permanentsOf controller).foldl (fun g o =>
      if o.printed.isToken && o.status.tapped then g.applyPermanentAction (g.object! o.id) .untap
      else g) g
  | .may (.discard (.cards 1 .you)) (.searchLibrary (.returnToHand .enchantmentCard _)) .ifYouDo =>
    if (g.player controller).hand.isEmpty then g
    else
      g.beginFraChoice controller (.mayDiscardThen .searchEnchantmentToHand sourceId)
        s!"{(g.player controller).name} may discard a card"
  | .fight (.targetAt 0) .mutual =>
    match g.legalPermanentAt? controller kind targets 0 sourceId,
        g.legalPermanentAt? controller kind targets 1 sourceId with
    | some a, some b => g.fightCreatures a b
    | _, _ => g
  | .putCounters .minusOneGreatestGraveyardMv (.creaturesControlledBy .eachOpponent) =>
    let x := (g.player controller).graveyard.foldl (fun acc id =>
      match g.findObject? id with
      | some o => Nat.max acc (g.objectManaValue o)
      | none => acc) 0
    targets.foldl (fun g t =>
      match t with
      | Target.permanent id =>
        match g.findObject? id with
        | some o =>
          let shielded :=
            match o.controller with
            | some c => (g.permanentsOf c).any (·.printed.creaturesCantGetMinusCounters)
            | none => false
          if o.isOnBattlefield && o.isCreature && g.canBeTargetedBy controller o && x > 0 &&
              !shielded then
            let n := g.countersYouPut o x (putter := some controller)
            (g.mapObjectStatus o (fun s => { s with minusOneMinusOne := s.minusOneMinusOne + n })).logMsg
              s!"{n} -1/-1 counter(s) are put on {o.name}"
          else g
        | none => g
      | _ => g) g
  | .draw .colorsAmongOtherArtifacts _ =>
    let colors := (g.permanentsOf controller).foldl (fun (acc : ColorSet) o =>
      if o.printed.isArtifact && some o.id != sourceId then ColorSet.union acc o.printed.colors
      else acc) ColorSet.empty
    g.draw controller ((Color.all.filter colors.contains).length)
  | .pump .minusGraveyardCards (.fixed 0) .target =>
    let n : Int := Int.ofNat (g.player controller).graveyard.size
    g.withLegalKindPermanent controller kind targets (fun g o => g.pumpPermanent o (-n) 0)
      sourceId illegal
  | .putCounters (.ofKind .plusOnePlusOne n) .source =>
    match sourceId.bind g.findObject? with
    | some o => if o.isOnBattlefield then g.addPlusOnePlusOneTo o n else g
    | none => g
  | .fight .source .mutual =>
    if targets.isEmpty then g
    else
      match sourceId.bind g.findObject? with
      | some src =>
        g.withLegalKindPermanent controller kind targets (fun g o =>
          if src.isOnBattlefield then g.fightCreatures (g.object! src.id) o else g) sourceId illegal
      | none => g
  | .exile .target .untilSourceLeaves _ =>
    match sourceId.bind g.findObject? with
    | some src =>
      if !src.isOnBattlefield then g.logMsg s!"{src.name} has left the battlefield"
      else
        g.withLegalKindPermanent controller kind targets (fun g o =>
          let (g, ex) := g.move o.id .exile none
          let src := g.object! src.id
          let g := g.setObject { src with exileLinks := { src.exileLinks with linkedExile := src.linkedExile.push ex } }
          g.logMsg s!"{o.name} is exiled until {src.name} leaves the battlefield") sourceId illegal
    | none => g
  | .destroy (.target .eachPermanent) _ =>
    targets.foldl (fun g t =>
      match t with
      | Target.permanent id =>
        match g.findObject? id with
        | some o =>
          if o.isOnBattlefield && g.canBeTargetedBy controller o then g.destroyPermanent o
          else g.illegalAbilityTarget t
        | none => g
      | _ => g) g
  | .dealDamage (.fixed n) .target _ =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.player pid => g.dealDamageToPlayer pid n.toNat (source := src?)
      | Target.permanent id => g.dealDamageFrom srcName (g.object! id) n.toNat (source := src?)
      | Target.card _ => g) sourceId illegal
  | .put .landCard .tapped _ =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        let (g, newId) := g.returnCardToBattlefield controller id 0 (tapped := true)
        g.afterLandEnters (g.object! newId)
      | _ => g) sourceId illegal
  | .searchLibrary (.put .basicLand .tapped _) => g.resolveSearchBasicLandTapped controller
  | .searchLibrary (.put (.landsUpTo n) .tapped _) =>
    g.beginLibrarySearch controller (·.isLand) "a land card" (.battlefield true) (count := n)
  | .searchLibrary (.returnToHand .enchantmentCard _) =>
    g.resolveLibrarySearchToHand controller (·.isEnchantment) "enchantment card"
  | .createTokens .heartwood (.fixed n) true _ _ => g.createKindTokens controller .heartwood n.toNat (tapped := true)
  | .sacrifice .eachOpponentsCreature _ =>
    g.beginSacrificeCreatures ((g.livingOpponents controller).map (·.id)) #[]
  | .queueReflexive (.dealDamage (.fixed n) .target _) =>
    g.putReflexiveTrigger controller sourceId
      { targeting := .of .playerOrCreature, resolution := .dealDamage (.fixed n) .target
        phrase := s!"This deals {n.toNat} damage to any target" }
  | .queueReflexive (.destroy (.target .eachPermanent) _) =>
    g.putReflexiveTrigger controller sourceId
      { targeting := .of (g.perOpponentKind controller
          { noun := "up to one target creature or planeswalker that player controls"
            types := #[.creature, .planeswalker] })
        allowsZeroTargets := true
        resolution := .destroy (.target .eachPermanent)
        phrase := "For each opponent, destroy up to one target creature or planeswalker that player controls" }
  | .queueReflexive (.put .landCard .tapped _) =>
    g.putReflexiveTrigger controller sourceId
      { targeting := .of (.filtered { noun := "target land card from your graveyard"
                                      zone := .yourGraveyard, types := #[.land] })
        resolution := .put .landCard .tapped
        phrase := "Return target land card from your graveyard to the battlefield tapped" }

  | .grant .emrakulManaAndCast .target
  | .cant (.beCountered .nextSpellThisTurn)
  | .exile .target .forLater .revealUntilCreatureOrPlaneswalker
  | .destroy .target .drawIfLegendaryEnchantment
  | .grant (.choiceOfKeywords _) .source
  | .putOnLibrary .bottom .graveyardCard
  | .destroy .allCreatures _
  | .putOnLibrary .shuffled .target
  | .grant .combatDamageDrawTwo .source
  | .pump (.count .artifact) (.fixed 0) .source
  | .pump (.count .artifact) (.fixed 0) .target
  | .putCounters (.ofKind .plusOnePlusOne 1) .creaturesWithPlusOne
  | .returnToHand (.target .eachPermanent) _
  | .surveil (.fixed 1) .returnNoncreatureNonland
  | .addMana #[.colored .blue] (.fixed 1) .noncreatureSpell
  | .putCounters .stunRemovedLoyalty .target
  | .grant .emblemDrawOnCast .youIfCast
  | .empowerJace (.subtypeCount "Island")
  | .pump (.fixed (-5)) (.fixed 0) .attackersAgainstYouUntilYourTurn
  | .exile .opponentLibrariesButBottom .forLater _
  | .pump (.fixed (-4)) (.fixed (-1)) (.target .untilYourNextTurn)
  | .sacrifice .eachPlayersCreature .ifYouDoCreateBeast
  | .discard .eachOpponentTwoDrawPerNonlandShortfall
  | .dealDamage (.fixed _) .creaturesExceptYourTokens _
  | .grant .emblemCreaturesGetTwoTwo .youIfCast
  | .untap (.target .eachPermanent)
  | .pump (.fixed 2) (.fixed 2) .attackersAgainstOpponentsUntilYourTurn
  | .putCounters .plusOnePerLand .target
  | .may (.sacrifice .another) (.createTokens .beast44trample (.fixed 1) false _ _) .ifYouDo
  | .createTokens .beast44trample (.fixed 1) false _ _
  | .pump (.fixed _) (.fixed _) (.cause none)
  | .pump (.fixed 2) (.fixed 2) .attackersOfCauseControllerWithTrample
  | .putCounters .causeCounters .source
  | .may (.removeCounters .all .source) (.putCounters .sourceCounters .target) .ifYouDo
  | .may (.pay (.mana #[.generic _])) (.proliferate (.fixed _) _) .ifYouDo
  | .proliferate (.fixed _) .youControl
  | .grant .artifactCreatureVehicle .source
  | .queueReflexive (.mshReflexive _ _)
  | .mshReflexive _ _
  | .chooseModes _ (.hawkeyeIndices _)
  | .mayCast .boastExiled .unlimited .withoutPaying _
  | .becomeCopy .sourceSpellXTimes
  | .dealDamage .equalSourcePower .target _ | .dealDamage (.power .source) .target _
  | .returnToHand .source _
  | .mayCast .milledSpell .causingSpell .withoutPaying _
  | .loseLife (.fixed 1) .extort =>
    g.applyFraAbility controller effect r targets sourceId
  | _ => g

end Game
end Mtg.Engine
