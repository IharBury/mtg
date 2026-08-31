import Mtg.Engine.Game.Chapters

/-!
# Triggered-ability resolution (CR 603)

`applyTriggeredAbility` — resolving every modeled triggered ability —
plus attack triggers (CR 508.2) and becomes-blocked triggers (CR 509.5c)
going on the stack.
-/

namespace Mtg.Engine
namespace Game

partial def applyTriggeredAbility (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target := #[])
    (dividedDamage : Array Nat := #[]) (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none)
    (sourceName : String := "This creature") : Game :=
  if !g.interveningStillHolds controller ab then
    g.logMsg "The intervening condition is no longer true. The ability doesn't resolve."
  else
  match ab.effect.resolution with
  | .sequence rs =>
    (rs.flatMap Resolution.flatten).foldl (fun g r =>
      let step : TriggeredAbility :=
        match ab with
        | .triggered w _ opts =>
          .triggered w { ab.effect with resolution := r } opts
      g.applyTriggeredAbility controller step sourceId targets dividedDamage
        lastKnownPower lastKnownToughness sourceName) g
  | .draw n => g.draw controller n
  | .scry n => g.beginScry controller n
  | .onPermanent a =>
    g.applyOnPermanent controller ab.targetKind targets a sourceId
      (some "The target is no longer legal")
  | .onSource a => g.applyOnTriggerSource sourceId a
  | .gainLife n => g.gainLife controller n
  | .recruit => g.beginRecruit controller
  | .amassGoblins n => g.amassGoblins controller n
  | .createTokens kind n tapped =>
    g.createKindTokens controller kind n (tapped := tapped)
  | .addMana types =>
    g.addManaLogged controller types
  | .discard n => g.beginDiscardCards #[controller] n
  | .spell r =>
    g.applyUnified controller { ab.effect with resolution := .spell r } targets
  | .ability r =>
    g.applyUnifiedAbility controller { ab.effect with resolution := .ability r }
      targets sourceId lastKnownPower
  | .trigger _ =>
  match ab.resolution with
  | .pumpGreatestPower =>
    g.applyOnTriggerSource sourceId (.pump (g.greatestPowerAmongCreatures controller) 0)
  | .setOtherBasePT =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let (pw, tw) := g.sourcePTAtResolution sourceId lastKnownPower lastKnownToughness
      let g := g.mapObjectStatus o (fun s => { s with setBasePT := some (pw, tw) })
      g.logMsg
        s!"{o.name}'s base power and toughness become {pw}/{tw} until end of turn")
      "No target was chosen"
  | .damageBlockers n =>
    g.withTriggerSource sourceId fun g o =>
      let blockers := g.blockersOf o.id
      if blockers.isEmpty then
        g.logMsg s!"there are no creatures blocking {o.name}"
      else
        Id.run do
          let mut g := g
          for b in blockers do
            g := g.dealDamageFrom o.name (g.object! b.id) n
              (deathtouch := g.hasDeathtouch o)
          return g
  | .scry n =>
    g.beginScry controller n
  | .draw n =>
    g.draw controller n
  | .searchForest =>
    g.resolveSearchForest controller
  | .mayDiscardDraw n =>
    g.beginMayDiscardDraw controller n
  | .opponentSacrificesCreature =>
    g.withLegalTriggerPlayer controller ab sourceId targets (fun g pid =>
      g.beginSacrificeCreature pid)
  | .onPermanent action =>
    g.applyOnPermanent controller ab.targetKind targets action sourceId
      (some "The target is no longer legal")
  | .dividedDamage =>
    Id.run do
      let mut g := g
      for i in [0:targets.size] do
        let t := targets[i]!
        let n := dividedDamage[i]?.getD 0
        if n > 0 then
          g := g.applyEffect controller (Effect.dealDamage n) #[t]
      return g
  | .damageFromLastKnownPower =>
    let n := (lastKnownPower.getD 0).toNat
    g.withLegalTriggerPermanent controller ab sourceId targets fun g o =>
      g.dealDamageFrom sourceName o n
  | .returnElfGainLife =>
    g.withLegalTriggerTarget controller ab sourceId targets fun g t =>
      match t with
      | Target.card oid =>
        match g.findObject? oid with
        | none => g.logMsg "The target is no longer in the graveyard"
        | some o =>
          let n := (g.power o).toNat
          let g := g.returnToHand oid controller
          g.gainLife controller n
      | _ => g.logMsg "The target is no longer legal"
  | .damageEachOpponent n =>
    g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid n)
  | .pumpByLookedAt =>
    let n := (lastKnownPower.getD 0).toNat
    g.applyOnTriggerSource sourceId (.pump (n : Int) (n : Int))
  | .onSource action =>
    g.applyOnTriggerSource sourceId action
  | .gainLife n =>
    g.gainLife controller n
  | .eachPlayerSacrificesCreature =>
    g.beginSacrificeCreatures (g.apnapOrder)
  | .eachOpponentDiscards =>
    g.beginDiscardCards (g.apnapOrder.filter (· != controller))
  | .exileOppGyCardOppsLoseLife n =>
    let g :=
      match targets[0]? with
      | some (Target.card oid) =>
        match g.findObject? oid with
        | some o =>
          let name := o.name
          let (g, _) := g.move oid .exile none
          g.logMsg s!"{name} is exiled"
        | none => g.logMsg "The target is no longer in the graveyard"
      | _ => g
    g.forEachOpponent controller (fun g pid => g.loseLife pid n)
  | .creaturesYouControlPumpAndFirstStrike pw =>
    g.forEachControlledCreature controller fun g o =>
      let g := g.pumpPermanent o pw 0
      g.grantUntilEotLogged (g.object! o.id) Keyword.firstStrike
  | .pumpForEachOtherCreature =>
    g.withTriggerSource sourceId fun g o =>
      let others :=
        g.battlefield.filter (fun c =>
          c.isCreature && c.controlledBy controller && c.id != o.id) |>.size
      g.pumpPermanent o others others
  | .grantFlying =>
    g.applyOnPermanent controller ab.targetKind targets
      (.grantKeywords Keyword.flying) sourceId (some "The target is no longer legal")
  | .mayPayGenericDraw n =>
    { g with pending := .mayPayGeneric controller n }.logMsg
      s!"{(g.player controller).name} may pay \{{n}}. If they do, they draw a card"
  | .drawThenBottomIfNoLegendary =>
    let g := g.draw controller 1
    if g.controlsLegendaryCreature controller then g
    else if (g.player controller).hand.isEmpty then g
    else
      { g with pending := .putOnBottom controller 1 }.logMsg
        s!"{(g.player controller).name} puts a card from their hand on the bottom of their library"
  | .exileTarget =>
    g.withLegalKindPermanent controller ab.targetKind targets (fun g o =>
      g.exileForLeaveTrigger sourceId o) sourceId (some "The target is no longer legal")
  | .exileUntilLeaves =>
    g.withSourceStillOnBattlefield sourceId fun g _ =>
      g.withLegalKindPermanent controller ab.targetKind targets (fun g o =>
        g.exileUntilSourceLeaves sourceId o) sourceId (some "The target is no longer legal")
  | .returnLinkedExile =>
    match sourceId.bind g.findObject? with
    | some src => g.returnLinkedExile src
    | none => g
  | .removeHopeDrawSac =>
    g.withTriggerSource sourceId fun g src =>
      if src.status.hope == 0 then g
      else
        let g := g.setObject { src with status := { src.status with hope := src.status.hope - 1 } }
        let g := g.logMsg s!"{src.name} loses a hope counter"
        let g := g.draw controller 1
        match g.findObject? src.id with
        | some src =>
          if src.status.hope == 0 then
            let g := g.logMsg s!"{src.name} is sacrificed"
            let (g, _) := g.move src.id (.graveyard src.owner) none
            g.gainLife controller 4
          else g
        | none => g
  | .loot =>
    g.drawThenBeginDiscard controller
  | .tapHumansDraw =>
    { g with pending := .tapHumans controller }.logMsg
      s!"{(g.player controller).name} may tap any number of untapped Humans they control"
  | .pumpAndUnblockable =>
    g.withTriggerSource sourceId fun g o =>
      let g := g.pumpPermanent o 1 0
      g.grantCantBeBlockedThisTurn (g.object! o.id)
  | .recruit =>
    g.beginRecruit controller
  | .youRecruit =>
    g.beginRecruit controller
  | .exileTop =>
    g.resolveExileTopPlayUntilEndOfNextTurn controller
  | .untapPlusOneIfSubtype subtype =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let g := g.applyPermanentAction o .untap
      let o := g.object! o.id
      if g.hasSubtype o subtype then g.addPlusOnePlusOneTo o 1 else g)
  | .plusOneEachYouControl =>
    g.forEachControlledCreature controller (fun g o => g.addPlusOnePlusOneTo o 1)
  | .sourceGetsAndTeamTrample p =>
    let g := g.applyOnTriggerSource sourceId (.pump p 0)
    g.grantUntilEotToControlledCreatures controller Keyword.trample "trample"
  | .drawAndLoseLife =>
    g.drawThenLoseLife controller 1 1
  | .amassGoblins n =>
    g.amassGoblins controller n
  | .createTokens kind n tapped =>
    g.createKindTokens controller kind n (tapped := tapped)
  | .createThenAttach kind =>
    let (g, tok) := g.createToken controller (tokenPrinted kind)
    g.withSourceOnBattlefield sourceId (fun g src => g.attachSourceTo src tok)
      "The Equipment is no longer in play"
  | .amassThenAttach n =>
    let g := g.amassGoblins controller n
    let army :=
      (g.permanentsOf controller).find? (fun o => g.hasSubtype o "Army")
    match army, sourceId.bind g.findObject? with
    | some host, some src =>
      if src.isOnBattlefield then g.attachSourceTo src host else g
    | _, _ => g
  | .attachSourceToTarget =>
    g.withLegalKindPermanent controller ab.targetKind targets (fun g host =>
      g.withSourceOnBattlefield sourceId (fun g src => g.attachSourceTo src host)
        "The Equipment is no longer in play")
      sourceId (some "The target is no longer legal")
  | .searchBasicToHand =>
    g.resolveSearchBasicLandToHand controller
  | .gainLifeSearchBasicOnTop n =>
    let g := g.gainLife controller n
    g.resolveLibrarySearch controller isBasicLandCard "basic land card"
      fun g cardId =>
        let cardName := (g.object! cardId).name
        let pl := g.player controller
        let lib := pl.library.filter (· != cardId) |>.push cardId
        let g := g.setPlayer { pl with library := lib }
        g.logMsg s!"{(g.player controller).name} puts {cardName} on top of their library"
  | .plusOneEachOtherGainLife =>
    let others :=
      g.battlefield.filter (fun o =>
        o.isCreature && o.controlledBy controller && some o.id != sourceId)
    let g := others.foldl (fun acc o => acc.addPlusOnePlusOneTo o 1) g
    if others.isEmpty then g else g.gainLife controller others.size
  | .destroyOppArtifactsEnchantmentsGainLife =>
    Id.run do
      let mut g := g
      let mut n : Nat := 0
      for o in g.battlefield do
        if !o.controlledBy controller &&
            (o.printed.isArtifact || o.printed.isEnchantment) then
          let name := o.name
          let (g', _) := g.move o.id (.graveyard o.owner) none
          g := g'.logMsg s!"{name} is destroyed"
          n := n + 1
      return if n == 0 then g else g.gainLife controller n
  | .damageEqualSubtypeToEachOpponent subtype =>
    let n := g.countSubtype controller subtype
    Id.run do
      let mut g := g
      for pl in g.livingOpponents controller do
        g := g.loseLife pl.id n
      return g
  | .damageEqualTreasures =>
    let n := g.countSubtype controller "Treasure"
    g.applyEffect controller (Effect.dealDamage n) targets
  | .loseLifeCreateTreasure =>
    let g := g.loseLife controller 1
    g.createTreasureTokens controller 1
  | .dealDamageDestroyIfSubtype n subtype =>
    g.withLegalKindTarget controller ab.targetKind targets (fun g tgt =>
      match tgt with
      | Target.player _pid => g.applyEffect controller (Effect.dealDamage n) #[tgt]
      | Target.permanent oid =>
        match g.findObject? oid with
        | none => g.logMsg "The target is no longer legal"
        | some o =>
          let g := g.applyEffect controller (Effect.dealDamage n) #[tgt]
          if g.hasSubtype o subtype then
            match g.findObject? oid with
            | some o =>
              let name := o.name
              let (g, _) := g.move o.id (.graveyard o.owner) none
              g.logMsg s!"{name} is destroyed"
            | none => g
          else g
      | _ => g.logMsg "The target is no longer legal")
  | .attachEquipmentToCreature =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent eqId), some (Target.permanent hostId) =>
      match g.findObject? eqId, g.findObject? hostId with
      | some eq, some host =>
        if eq.isOnBattlefield && host.isOnBattlefield then
          g.attachSourceTo eq host
        else g.logMsg "The target is no longer legal"
      | _, _ => g.logMsg "The target is no longer legal"
    | some (Target.permanent _), none =>
      g.logMsg "No creature was chosen"
    | _, _ => g.logMsg "The target is no longer legal"
  | .addMana types =>
    g.addManaLogged controller types
  | .defenderSacsLeastPower =>
    let defn := g.opponent controller
    let chosen :=
      match targets[0]? with
      | some (Target.permanent id) => some id
      | _ => none
    g.sacrificeLeastPowerCreature defn chosen
  | .createAxe =>
    let (g, _) := g.createToken controller axeToken
    g.logMsg "An Axe token is created"
  | .tapOppOrUntapYours =>
    g.logMsg "Choose tap an opposing creature or untap yours"
  | .becomePT p t =>
    g.withTriggerSource sourceId fun g o =>
      g.setObject { o with status := { o.status with setBasePT := some (p, t) } }
  | .returnOtherPlusOne =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let owner := o.owner
      let (g, _) := g.move o.id (.hand owner) none
      g.applyOnTriggerSource sourceId (.plusOne 1))
  | .lookAtTopRevealTypes n types =>
    Id.run do
      let mut g := g
      let ids := g.scryLookedIds controller n
      g := g.logLookAtTop controller n
      let picked :=
        ids.find? (fun id =>
          match g.findObject? id with
          | some o =>
            types.any (fun t =>
              t == "permanent" && o.printed.isPermanentCard ||
                o.printed.hasSubtype t ||
                (t == "creature" && o.printed.isCreature))
          | none => false)
      match picked with
      | none => pure ()
      | some id =>
        let name := (g.object! id).name
        let (g', _) := g.move id (.hand controller) none
        g := g'.logMsg s!"{name} is put into {(g'.player controller).name}'s hand"
      return g.shuffleLibrary controller
  | .pumpAndDamageOpponents n =>
    g.applyOnTriggerSource sourceId (.pump 1 1)
      |>.forEachOpponent controller (fun g pid => g.loseLife pid n)
  | .createTappedTreasuresEqualOppArtifacts =>
    let n := g.countOpponentArtifacts controller
    g.createTreasureTokens controller n (tapped := true)
  | .gainControlOppUntilEot =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let g := g.giveControlUntilEot o controller
      let g := g.applyPermanentAction (g.object! o.id) .untap
      g.mapObjectStatus (g.object! o.id) (·.grantUntilEot Keyword.haste))
  | .othersGetAndOppsGet subtypes p t oppP oppT =>
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.isCreature && o.controlledBy controller &&
            subtypes.any (fun s => g.hasSubtype o s) && some o.id != sourceId then
          g := g.pumpPermanent o p t
        else if o.isCreature && !o.controlledBy controller then
          g := g.pumpPermanent o oppP oppT
      return g
  | .putNonlandMvAtMostFromGy _mv =>
    g.logMsg "A nonland permanent card may enter from a graveyard"
  | .honeEachEquipment =>
    let eqs :=
      g.battlefield.filter (fun o => o.controlledBy controller && o.printed.isEquipment)
    eqs.foldl (init := g) fun acc eq =>
      acc.mapObjectStatus eq (fun s => { s with hone := s.hone + 1 })
        |>.logMsg s!"{eq.name} received a hone counter"
  | .cascade =>
    let maxMv :=
      match sourceId with
      | some sid =>
        match g.findObject? sid with
        | some src => src.printed.manaCost.manaValue
        | none => 0
      | none => 0
    g.resolveCascade controller maxMv
  | .belladonnaTokenReward =>
    let n := (g.player controller).belladonnaResolvesThisTurn + 1
    let g := g.modifyPlayer controller (fun pl =>
      { pl with belladonnaResolvesThisTurn := n })
    if n == 1 then
      g.gainLife controller 1
    else if n == 2 then
      g.draw controller 1
    else if n == 3 then
      g.forEachControlledCreature controller (fun g o => g.addPlusOnePlusOneTo o 1)
        |>.logMsg
          s!"{(g.player controller).name} puts a +1/+1 counter on each creature they control"
    else
      g.logMsg
        s!"Belladonna Took's ability has no effect (resolved {n} times this turn)"
  | .bolgMaySacrifice =>
    match sourceId with
    | some sid =>
      { g with pending := .maySacrificeAnotherBolg controller sid }.logMsg
        s!"{(g.player controller).name} may sacrifice another creature (Bolg reflexive trigger)"
    | none => g.logMsg "Bolg is no longer in play"
  | .bolgDealSacrificedPower =>
    let amt := lastKnownPower.getD 0
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let remain := g.toughness o - o.status.damage
      let raw := amt - remain
      let excess : Nat := if raw > 0 then raw.toNat else 0
      let g := g.dealDamageFrom sourceName o amt
      if excess > 0 then
        g.amassGoblins controller excess |>.logMsg
          s!"excess damage {excess} — amass Goblins {excess}"
      else g) "The target is no longer legal"
  | .createSpiritsForEquipped =>
    match sourceId.bind g.findObject? with
    | none => g.logMsg "The Equipment is no longer in play"
    | some eq =>
      let hostOk :=
        match eq.attachedTo.bind g.findObject? with
        | some host =>
          host.isOnBattlefield && host.isLegendary &&
            host.controller == some controller
        | none => false
      let attacking := hostOk
      let g :=
        g.createKindTokens controller .spirit 2 (tapped := true) (attacking := attacking)
      if attacking then
        g.logMsg
          s!"{(g.player controller).name} creates two tapped and attacking Spirit tokens"
      else
        g.logMsg
          s!"{(g.player controller).name} creates two tapped Spirit tokens"
  | .createTreasuresEqualDamagedPlayerArtifacts =>
    let pid := g.lastCombatDamagePlayer.getD (g.opponent controller)
    let n := g.countArtifactsControlledBy pid
    g.createTreasureTokens controller n |>.logMsg
      s!"{(g.player controller).name} creates {n} Treasure token(s) (artifacts that player controls)"
  | .deal1ThenAmassOrcs =>
    let g := g.applyEffect controller (Effect.dealDamage 1) targets
    g.amassOrcs controller 1
  | .untapAttackersExtraCombat =>
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.status.attacking then
          g := g.applyPermanentAction o .untap
      return g.logMsg
        "Attacking creatures untap. An additional combat phase will occur"
  | .eaglesCreateBirds =>
    let n := lastKnownPower.getD 0
    g.createKindTokens controller .birdSoldier n.toNat |>.logMsg
      s!"{(g.player controller).name} creates {n} Bird Soldier token(s)"
  | .allianceMode =>
    g.applyNextUnusedMode sourceId (g.unusedAllianceModes)
      applyAllianceMode
      "all three modes have been chosen this turn. The ability is removed from the stack with no effect"
  | .gollumMode =>
    g.applyNextUnusedMode sourceId (g.unusedGollumModes)
      applyGollumMode
      "all three modes have been chosen. The ability is removed from the stack with no effect"
  | .destroyOtherAmassControllerPower =>
    match targets[0]? with
    | none =>
      g.logMsg
        "No target was chosen. Its controller is undefined and no player amasses Goblins."
    | some (Target.permanent oid) =>
      match g.findObject? oid with
      | none =>
        g.logMsg "The target is no longer legal"
      | some o =>
        if !o.isOnBattlefield then
          g.logMsg "The target is no longer legal"
        else
          let pw := lastKnownPower.getD (g.power o)
          let ctrl := o.controller
          let youControlled := ctrl == some controller
          let g := g.destroyPermanent o
          match ctrl with
          | none => g
          | some pid =>
            let n := if pw > 0 then pw.toNat else 0
            let g := g.amassGoblins pid n
            if youControlled then g.draw controller 1 else g
    | _ =>
      g.logMsg "No target was chosen. Its controller is undefined and no player amasses Goblins."
  | .returnCreatureFromGyToHand =>
    g.withLegalTriggerTarget controller ab sourceId targets fun g t =>
      match t with
      | Target.card oid =>
        match g.findObject? oid with
        | none => g.logMsg "The target is no longer in the graveyard"
        | some o =>
          let name := o.name
          let (g, _) := g.move oid (.hand controller) none
          g.logMsg s!"{name} is returned to {(g.player controller).name}'s hand"
      | _ => g.logMsg "The target is no longer legal"
  | .discardHandDrawDamageIfStory =>
    let n := (g.player controller).hand.size
    let g := g.mayDiscardHandDrawThatMany controller true
    if g.hasEnduringStory controller then
      g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid n)
    else g
  | .plusOneAndLifelink =>
    match targets[0]? with
    | some (Target.permanent oid) => g.applyBardBowman oid
    | _ => g.logMsg "The target is no longer legal"
  | .wolfPlusOneOrTreasure =>
    match targets[0]? with
    | some (Target.permanent oid) =>
      match g.findObject? oid with
      | some o =>
        if g.hasSubtype o "Wolf" then g.addPlusOnePlusOneTo o 1
        else g.createTreasureTokens controller 1
      | none => g.createTreasureTokens controller 1
    | _ => g.createTreasureTokens controller 1
  | .trampleCounterBecomeBear =>
    let g :=
      match targets[0]? with
      | some (Target.permanent oid) =>
        match g.findObject? oid with
        | some o =>
          let extra :=
            if g.hasSubtype o "Bear" then o.status.additionalSubtypes
            else o.status.additionalSubtypes.push "Bear"
          let g := g.setObject { o with status :=
            { o.status with
              trampleCounters := o.status.trampleCounters + 1
              additionalSubtypes := extra } }
          g.logMsg s!"{o.name} gets a trample counter and becomes a Bear"
        | none => g
      | _ => g
    if g.countSubtype controller "Bear" >= 3 then g.draw controller 2 else g
  | .castFromGyArtifactInstantSorcery =>
    match (g.player controller).graveyard.findSome? (fun id =>
      match g.findObject? id with
      | some o =>
        if o.printed.isArtifact || o.printed.isInstantOrSorcery then some id
        else none
      | none => none) with
    | none => g.logMsg s!"{(g.player controller).name} has no artifact, instant, or sorcery in the graveyard"
    | some id => g.castAsPartOfResolution controller id
  | .millThenSubtypeToHand n subtype =>
    let before := (g.player controller).graveyard
    let g := g.mill controller n
    let after := (g.player controller).graveyard
    let newIds := after.filter (fun id => !before.contains id)
    newIds.foldl (fun acc id =>
      match acc.findObject? id with
      | some o =>
        if o.printed.hasSubtype subtype then
          let name := o.name
          let (acc, _) := acc.move id (.hand controller) none
          acc.logMsg s!"{name} is put into {(acc.player controller).name}'s hand"
        else acc
      | none => acc) g
  | .exileOppNonlandEachUntilLeaves =>
    g.withSourceStillOnBattlefield sourceId fun g _ =>
      targets.foldl (fun acc t =>
        match t with
        | Target.permanent oid =>
          match acc.findObject? oid with
          | some o => acc.exileUntilSourceLeaves sourceId o
          | none => acc
        | _ => acc) g
  | .plusOneEqualLastKnownMv =>
    let n := (lastKnownPower.getD 0).toNat
    g.applyOnPermanent controller ab.targetKind targets (.plusOne n) sourceId
      (some "The target is no longer legal")
  | .createAxeAttach =>
    let (g, tok) := g.createToken controller axeToken
    g.withLegalKindPermanent controller .creatureYouControl targets (fun g host =>
      g.attachSourceTo tok host) sourceId (some "No creature was chosen")
  | .equippedAttackersGainDoubleStrike =>
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.status.attacking && o.attachedTo.isSome ||
            (o.status.attacking &&
              g.battlefield.any (fun eq => eq.attachedTo == some o.id)) then
          if o.isCreature && o.status.attacking &&
              g.battlefield.any (fun eq => eq.attachedTo == some o.id) then
            g := g.grantUntilEotLogged o Keyword.doubleStrike
      return g
  | .tapEnchantedRemoveCounters =>
    match sourceId.bind g.findObject? with
    | none => g
    | some src =>
      match src.attachedTo.bind g.findObject? with
      | none => g.logMsg "Nothing is enchanted"
      | some host =>
        let g := g.applyPermanentAction host .tap
        let host := g.object! host.id
        let g := g.setObject { host with status :=
          { host.status with
            plusOnePlusOne := 0
            hope := 0
            hone := 0
            shadow := 0
            burden := 0
            quest := 0
            trampleCounters := 0
            influence := 0
            lore := 0
            invasion := 0
            indestructibleCounters := 0
            lifelinkCounters := 0 } }
        g.logMsg s!"counters are removed from {host.name}"
  | .revealTopPutRandomCreature n =>
    Id.run do
      let mut g := g
      let ids := g.scryLookedIds controller n
      let creatures :=
        ids.filter (fun id =>
          match g.findObject? id with
          | some o => o.printed.isCreature
          | none => false)
      if g.norandom && creatures.size > 1 then
        return { g with
          pending := .resolveRandom (.chooseObject creatures)
          afterRandom := .putCreatureThenShuffle controller }
          |>.logMsg
            s!"{(g.player controller).name} reveals the top {n} cards and puts a random creature onto the battlefield"
      match creatures[0]? with
      | none =>
        g := g.logMsg "No creature card was revealed"
      | some cid =>
        let name := (g.object! cid).name
        let (g', _) := g.putOntoBattlefield cid controller
        g := g'.logMsg s!"{name} enters the battlefield"
        g := g.afterPermanentEnters (g.object! cid)
      for id in ids do
        if creatures[0]? != some id then
          match g.findObject? id with
          | some o =>
            if o.zone == .library controller then
              let (g', _) := g.move id (.library controller) none
              g := g'
          | none => pure ()
      return g.shuffleLibrary controller
  | .beginCombatIfDrawnTwoPump =>
    if (g.player controller).cardsDrawnThisTurn < 2 then g
    else
      g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
        let g := g.pumpPermanent o 3 0
        g.grantUntilEotLogged (g.object! o.id) Keyword.firstStrike)
        "The target is no longer legal"
  | .mountainQuestDragon =>
    g.withTriggerSource sourceId fun g src =>
      let g := g.setObject { src with status :=
        { src.status with quest := src.status.quest + 1 } }
      let src := g.object! src.id
      let g := g.logMsg s!"{src.name} gets a quest counter ({src.status.quest})"
      if src.status.quest >= 6 then
        let name := src.name
        let (g, _) := g.move src.id (.graveyard src.owner) none
        let g := g.logMsg s!"{name} is sacrificed"
        match (g.player controller).hand.findSome? (fun id =>
          match g.findObject? id with
          | some o => if o.printed.hasSubtype "Dragon" then some id else none
          | none => none) with
        | some id =>
          let (g, _) := g.putOntoBattlefield id controller
          g.afterPermanentEnters (g.object! id)
        | none =>
          g.resolveLibrarySearch controller (fun c => c.hasSubtype "Dragon")
            "Dragon card" fun g cardId =>
              let (g, _) := g.putOntoBattlefield cardId controller
              g.afterPermanentEnters (g.object! cardId)
      else g
  | .millPlayer n =>
    g.withLegalTriggerPlayer controller ab sourceId targets (fun g pid => g.mill pid n)
  | .treasuresPerChosenType =>
    let n := g.countCreaturesControlledBy controller
    g.createTreasureTokens controller n
  | .revealUntilCreature =>
    Id.run do
      let mut g := g
      let mut found : Option ObjectId := none
      let mut rest : Array ObjectId := #[]
      while found.isNone && !(g.player controller).library.isEmpty do
        let top := (g.player controller).library.back!
        let o := g.object! top
        g := g.logMsg s!"{(g.player controller).name} reveals {o.name}"
        if o.printed.isCreature then
          found := some top
        else
          let (g', newId) := g.move top .exile none
          g := g'
          rest := rest.push newId
      match found with
      | none =>
        return rest.foldl (fun acc id => (acc.move id (.library controller) none).1) g
      | some cid =>
        let o := g.object! cid
        let lands := g.landsYouControl controller
        let (g', newId) :=
          if o.printed.manaValue <= lands then
            g.putOntoBattlefield cid controller
          else
            g.move cid (.hand controller) none
        g := g'
        g := g.logMsg s!"{o.name} is put into play or hand"
        if o.printed.manaValue <= lands then
          g := g.afterPermanentEnters (g.object! newId)
        return rest.foldl (fun acc id => (acc.move id (.library controller) none).1) g
  | .attackSacPlusOneEqualPower =>
    match (g.permanentsOf controller).find? (fun o =>
      o.isCreature && some o.id != sourceId) with
    | none => g.logMsg "No other creature to sacrifice"
    | some sac =>
      let pw := g.power sac
      let (g, _) := g.move sac.id (.graveyard sac.owner) none
      g.applyOnTriggerSource sourceId (.plusOne pw.toNat)
  | .amassGoblinsEqualPower =>
    let n := (lastKnownPower.getD 0).toNat
    g.amassGoblins controller n
  | .payReturnFromGy =>
    g.returnSourceFromGraveyard sourceId controller (toHand := true)
  | .lootLandEntersTapped =>
    g.drawThenBeginDiscard controller
  | .honePerOppAttach =>
    let opp :=
      match targets[0]? with
      | some (Target.player pid) => pid
      | some (Target.permanent _) => g.opponent controller
      | _ => g.opponent controller
    let n := g.countCreaturesControlledBy opp
    let g :=
      g.withTriggerSource sourceId fun g src =>
        g.mapObjectStatus src (fun s => { s with hone := s.hone + n })
          |>.logMsg s!"{src.name} gets {n} hone counter(s)"
    match targets[1]?, targets[0]? with
    | some (Target.permanent hid), _
    | none, some (Target.permanent hid) =>
      match g.findObject? hid, sourceId.bind g.findObject? with
      | some host, some src =>
        if host.isCreature then g.attachSourceTo src host else g
      | _, _ => g
    | _, _ => g
  | .damageTargetOpponent n =>
    g.withLegalTriggerPlayer controller ab sourceId targets (fun g pid =>
      g.dealDamageToPlayer pid n)
  | .millThatManyLost =>
    match g.lastLifeLost with
    | some (pid, n) => g.mill pid n
    | none => g
  | .drawPerFatGraveyard =>
    g.drawPerSevenCardGraveyard controller
  | .copySelfNonlegendary =>
    match sourceId.bind g.findObject? with
    | none => g
    | some src =>
      if src.printed.isToken then g
      else
        let face := { src.printed with
          isToken := true
          supertypes := src.printed.supertypes.filter (· != .legendary) }
        let (g, _) := g.createToken controller face
        let (g, _) := g.createToken controller face
        g.logMsg s!"two nonlegendary tokens that are copies of {src.name} are created"
  | .maySacDrawTreasure =>
    match (g.permanentsOf controller).find? (fun o =>
      (o.isCreature || o.printed.isArtifact) && some o.id != sourceId) with
    | none => g.logMsg "Nothing to sacrifice"
    | some sac =>
      let g := g.sacrificeToGraveyard sac
        s!"{(g.player controller).name} sacrifices {sac.name}"
      let g := g.draw controller 1
      g.createTreasureTokens controller 1
  | .targetOpponentLosesLife n =>
    g.withLegalTriggerPlayer controller ab sourceId targets (fun g pid =>
      g.loseLife pid n)
  | .attachEquipmentThenFight =>
    match targets[0]? with
    | some (Target.permanent hid) =>
      match g.findObject? hid with
      | none => g.logMsg "The target is no longer legal"
      | some host =>
        let eqs :=
          (g.permanentsOf controller).filter (fun o => o.printed.isEquipment)
        let g := eqs.foldl (fun acc eq => acc.attachSourceTo eq host) g
        let host := g.object! host.id
        let pw := g.power host
        match (g.battlefield.find? (fun o =>
          o.isCreature && !o.controlledBy controller)) with
        | none => g
        | some opp => g.dealDamageFrom host.name opp pw
    | _ => g.logMsg "The target is no longer legal"
  | .plusOneVigilance n =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let g := g.addPlusOnePlusOneTo o n
      g.grantUntilEotLogged (g.object! o.id) Keyword.vigilance)
  | .drawThenDiscardN n =>
    g.drawThenBeginDiscard controller n
  | .returnAsArtifact =>
    match sourceId.bind g.findObject? with
    | none => g
    | some src =>
      if src.zone != .graveyard src.owner then g
      else
        let (g, newId) := g.putOntoBattlefield src.id controller
        let o := g.object! newId
        let g := g.setObject { o with status :=
          { o.status with additionalCreature := false, onlyFoodArtifact := false } }
        let o := g.object! newId
        -- Force artifact-only by using additionalArtifact and clearing creature
        -- via onlyFoodArtifact-style flag is too strong; grant artifact type.
        let g := g.mapObjectStatus o (fun s => { s with returnedAsArtifact := true })
        g.logMsg s!"{o.name} returns as an artifact"
  | .mayDrawXDiscard2 =>
    let n := (lastKnownPower.getD 0).toNat
    g.drawThenBeginDiscard controller n (discardRounds := 2)
  | .plusOneEachIfCityBlessing =>
    let n := if (g.player controller).citysBlessing then 2 else 1
    (g.permanentsOf controller).foldl (fun acc o =>
      if o.isCreature then acc.addPlusOnePlusOneTo o n else acc) g
  | .castInstantSorceryFromHand =>
    let wizards :=
      (g.permanentsOf controller).filter (fun o =>
        o.isLegendary && g.hasSubtype o "Wizard") |>.size
    g.castInstantSorceryFromHandMvAtMost controller (wizards * 2)
  | .drawPlusOneSource =>
    let g := g.draw controller 1
    g.applyOnTriggerSource sourceId (.plusOne 1)
  | .exileLandsThenReturnTapped =>
    g.foldPermanentTargets targets (fun g o =>
      if o.controlledBy controller && o.printed.isLand then
        g.exileThenReturn o "is exiled, then returned tapped"
          (tapped := true) (land := true)
      else g)
  | .castInstantSorceryMvAtMost =>
    g.castInstantSorceryFromHandMvAtMost controller (lastKnownPower.getD 0).toNat
  | .grimaImpulse =>
    let victim := g.lastCombatDamagePlayer.getD (g.opponent controller)
    g.grimaExileUntilInstantOrSorcery controller victim true
  | .palantir =>
    let tgt :=
      match targets[0]? with
      | some (Target.player pid) => some pid
      | _ => none
    match sourceId with
    | none => g.logMsg "The source is no longer in play"
    | some sid =>
      let g := g.applyPalantir sid tgt
      match tgt with
      | none => g
      | some _ =>
        -- Opponent declines the optional draw; mill and lose life.
        match g.findObject? sid with
        | none => g
        | some src =>
          let n := src.status.influence
          let before := (g.player controller).graveyard.size
          let g := g.mill controller n
          let milled := (g.player controller).graveyard.size - before
          let mv :=
            (g.player controller).graveyard.extract
              ((g.player controller).graveyard.size - milled)
              (g.player controller).graveyard.size
            |>.foldl (fun acc id =>
              acc + (g.object! id).printed.manaValue) 0
          match tgt with
          | some pid => g.loseLife pid mv
          | none => g
  | .millThenCopy =>
    let opps := (g.livingOpponents controller).map (·.id)
    let (g, milled) := g.millThenReflexive opps 2
    if !milled then g
    else
      match (opps.foldl (fun acc pid =>
        acc ++ (g.player pid).graveyard) #[]).findSome? (fun id =>
          match g.findObject? id with
          | some o =>
            if o.printed.isEnchantment || o.printed.isInstant || o.printed.isSorcery then
              some id
            else none
          | none => none) with
      | none => g
      | some id =>
        let o := g.object! id
        let (g, newId) := g.move id .exile none
        let g := g.logMsg s!"{o.name} is exiled"
        g.castAsPartOfResolution controller newId
  | .amassOrcs n =>
    g.amassOrcs controller n
  | .ringTempts =>
    g.temptWithTheRing controller
  | .mayDiscardHandDraw n =>
    let g := g.mayDiscardHandDrawThatMany controller true
    if (g.player controller).hand.size == 0 && n > 0 then
      g.draw controller n
    else g
  | .treasuresEqualLastKnown =>
    let n := (lastKnownPower.getD 0).toNat
    g.createTreasureTokens controller n
  | .protectionEverything =>
    g.modifyPlayer controller (fun pl => { pl with protectionFromEverything := true })
      |>.logMsg s!"{(g.player controller).name} gains protection from everything"
  | .loseLifePerBurden =>
    match sourceId.bind g.findObject? with
    | none => g
    | some src => g.loseLife controller src.status.burden
  | .revealSaga =>
    Id.run do
      let mut g := g
      let mut found : Option ObjectId := none
      let mut rest : Array ObjectId := #[]
      while found.isNone && !(g.player controller).library.isEmpty do
        let top := (g.player controller).library.back!
        let o := g.object! top
        g := g.logMsg s!"{(g.player controller).name} reveals {o.name}"
        if o.printed.saga.isSome then found := some top
        else
          let (g', newId) := g.move top .exile none
          g := g'
          rest := rest.push newId
      match found with
      | none =>
        return rest.foldl (fun acc id => (acc.move id (.library controller) none).1) g
      | some sid =>
        let (g', newId) := g.putOntoBattlefield sid controller
        g := g'.afterPermanentEnters (g.object! newId)
        return rest.foldl (fun acc id => (acc.move id (.library controller) none).1) g
  | .sacDamagersRingTempts =>
    let g :=
      (g.livingOpponents controller).foldl (fun acc pl =>
        acc.beginSacrificeCreature pl.id) g
    g.temptWithTheRing controller
  | .chapter _ =>
    g.applyChapterEffect controller ab.effect sourceId targets
  | .pumpTargetPerPlains =>
    let n := g.countSubtype controller "Plains"
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      g.pumpPermanent o n n)
      "No target was chosen"
  | .investigate =>
    let (g, _) := g.createToken controller clueToken
    g.logMsg s!"{(g.player controller).name} investigates"
  | .plusOneOnSourceAndDraw =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let g := g.setObject { o with status := { o.status with
        plusOnePlusOne := o.status.plusOnePlusOne + 1 } }
      g.draw controller 1
  | .connive =>
    g.applyConnive controller sourceId
  | .targetConnive =>
    match targets[0]? with
    | some (Target.permanent id) => g.applyConnive controller (some id)
    | _ => g.applyConnive controller sourceId
  | .pumpCause p t =>
    match (g.battlefield.find? (fun o => o.status.attacking && o.controlledBy controller)) with
    | some o => g.pumpPermanent o p t
    | none => g
  | .othersOfSubtypeGetEqualSourceToughness subtype =>
    let (x, srcId?) :=
      match sourceId.bind g.findObject? with
      | some src =>
        if src.isOnBattlefield then (g.toughness src, some src.id)
        else (lastKnownToughness.getD (g.toughness src), some src.id)
      | none => (lastKnownToughness.getD (0 : Int), none)
    g.foldBattlefield (fun o =>
        o.controlledBy controller &&
          (match srcId? with
           | some sid => o.id != sid
           | none => true) &&
          g.hasSubtype o subtype)
      (fun g o => g.pumpPermanent o x x)
  | .drawIfAttackedOrEnteredSubtype subtype =>
    let pl := g.player controller
    if (subtype == "Hero" && (pl.attackedWithHeroThisTurn || pl.heroEnteredThisTurn)) ||
        (g.battlefield.any (fun o =>
          o.controlledBy controller && g.hasSubtype o subtype &&
            (o.status.attacking || o.status.enteredThisTurn))) then
      g.draw controller 1
    else g
  | .scryAndPlan n =>
    g.incrementPlanThen controller sourceId (fun g _ => g.beginScry controller n)
  | .lootAndPlan =>
    g.incrementPlanThen controller sourceId (fun g _ =>
      g.drawThenBeginDiscard controller)
  | .createVillainAndPlan =>
    g.incrementPlanThen controller sourceId (fun g _ =>
      (g.createToken controller villain21menaceToken).1)
  | .drainAndPlan n =>
    g.incrementPlanThen controller sourceId (fun g _ =>
      let g := (g.livingOpponents controller).foldl (fun acc pl =>
        acc.loseLife pl.id n) g
      g.modifyPlayer controller (fun pl => { pl with life := pl.life + (n : Int) }))
  | .drawLoseLifeAndPlan =>
    g.incrementPlanThen controller sourceId (fun g _ =>
      g.drawThenLoseLife controller 1 1)
  | .treasureTappedAndPlan =>
    g.incrementPlanThen controller sourceId (fun g _ =>
      (g.createToken controller treasureToken (tapped := true)).1)
  | .plusOneOnTargetAndPlan =>
    g.withSourceOnBattlefield sourceId fun g src =>
      g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
        let src := g.object! src.id
        let g := g.setObject { src with status :=
          { src.status with plan := src.status.plan + 1 } }
        let src := g.object! src.id
        let g := g.putMatchingSourceTriggers controller src
          (.nthPlanCounter src.status.plan)
        g.mapObjectStatus o (fun s => { s with plusOnePlusOne := s.plusOnePlusOne + 1 }))
        "The target is no longer legal. You won't put counters on anything."
  | .planFinishDrawPlusOneEach =>
    let g := g.sacrificePlanIfOnBattlefield sourceId
    let g := g.draw controller 1
    g.foldBattlefield (fun c => c.controlledBy controller && c.isCreature)
      (fun g c => g.mapObjectStatus c (fun s =>
        { s with plusOnePlusOne := s.plusOnePlusOne + 1 }))
  | .planFinishReturnInstants =>
    g.sacrificePlanThenQueueReflexive controller sourceId 11
  | .planFinishControlOpponent =>
    g.sacrificePlanThenQueueReflexive controller sourceId 4
  | .planFinishExileTopCast =>
    g.sacrificePlanThenQueueReflexive controller sourceId 5
  | .planFinishCreateRobots n =>
    let g := g.sacrificePlanIfOnBattlefield sourceId
    Id.run do
      let mut g := g
      for _ in [0:n] do
        let (g', _) := g.createToken controller robotVillain22Token
        g := g'
      return g
  | .planFinishDividedDamage _n =>
    g.sacrificePlanThenQueueReflexive controller sourceId 10
  | .planFinishIndestructibleOnTarget =>
    g.sacrificePlanThenQueueReflexive controller sourceId 3
  | .drawAndLoseLife1 =>
    let g := g.draw controller 1
    g.loseLife controller 1
  | .onEnchanted action =>
    g.withSourceOnBattlefield sourceId (fun g src =>
      match src.attachedTo.bind g.findObject? with
      | some host => g.applyPermanentAction host action
      | none => g) "The Aura is no longer in play"
  | .attachThen action =>
    g.withLegalKindPermanent controller ab.targetKind targets (fun g host =>
      g.withSourceOnBattlefield sourceId (fun g src =>
        let g := g.attachSourceTo src host
        g.applyPermanentAction (g.object! host.id) action)
        "The Equipment is no longer in play")
      sourceId (some "The target is no longer legal")
  | .exileOtherCopyEnchanted =>
    g.withSourceStillOnBattlefield sourceId fun g src =>
      match targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some tgt =>
          let host? := src.attachedTo.bind g.findObject?
          let g := g.exileUntilSourceLeaves sourceId tgt
          match host? with
          | some host =>
            match g.findObject? host.id with
            | some host =>
              g.becomeCopyOf host tgt (untilSourceLeaves := some src.id)
            | none => g
          | none => g
        | none => g.logMsg "The target is no longer legal"
      | _ => g
  | .exileUntilNextEndStep =>
    g.withLegalKindPermanent controller ab.targetKind targets (fun g o =>
      g.exileUntilNextEndStep o) sourceId none
  | .tapOrUntapNonland =>
    match targets[0]? with
    | some (Target.permanent id) =>
      { g with pending := .chooseTapOrUntap controller id }.logMsg
        s!"{(g.player controller).name} chooses tap or untap"
    | _ => g.logMsg "The target is no longer legal"
  | .createFoodOrTreasure =>
    { g with pending := .chooseFoodOrTreasure controller }.logMsg
      s!"{(g.player controller).name} creates a Food token or a Treasure token"
  | .villainIfGyElseMill =>
    let gy := (g.player controller).graveyard.filter (fun id =>
      (g.object! id).printed.isCreature) |>.size
    if gy >= 2 then
      g.createKindTokens controller .villain21menace 1 (tapped := true)
    else
      g.mill controller 2
  | .drawMayPutLandTapped =>
    let g := g.draw controller 1
    { g with pending := .mayPutLandFromHand controller }.logMsg
      s!"{(g.player controller).name} may put a land card from their hand onto the battlefield tapped"
  | .drawGainLifeIfAnotherHero =>
    let g := g.draw controller 1
    if (g.permanentsOf controller).any (fun o =>
        g.hasSubtype o "Hero" && some o.id != sourceId) then
      g.gainLife controller 2
    else g
  | .plusOneOrTwoIfAnotherHero =>
    g.withLegalKindPermanent controller .creature targets (fun g o =>
      let n :=
        if g.hasSubtype o "Hero" && some o.id != sourceId then 2 else 1
      g.addPlusOnePlusOneTo o n) sourceId (some "The target is no longer legal")
  | .maySacArtifactOrDiscardDraw =>
    { g with pending := .maySacArtifactOrDiscard controller }.logMsg
      s!"{(g.player controller).name} may sacrifice an artifact or discard a card. If they do, they draw a card"
  | .targetOpponentDiscards n =>
    g.withLegalKindTarget controller .opponent targets (fun g tgt =>
      match tgt with
      | Target.player pid =>
        g.beginDiscardCards #[pid] n
      | _ => g) sourceId none
  | .pumpTargetBySourcePower =>
    let x := g.sourcePowerAtResolution sourceId lastKnownPower
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      g.pumpPermanent o x 0) "The target is no longer legal"
  | .createAlienPerInvasion =>
    let n :=
      match sourceId.bind g.findObject? with
      | some src => src.status.invasion
      | none => 0
    let (g, tok) := g.createToken controller alien11redHasteToken
    let g := if n == 0 then g else g.addPlusOnePlusOneTo (g.object! tok.id) n
    g.withSourceOnBattlefield sourceId (fun g src =>
      g.mapObjectStatus src (fun s => { s with invasion := s.invasion + 1 })
        |>.logMsg s!"{src.name} gets an invasion counter")
      "The source is no longer in play"
  | .mayPutArtifactAttachEquipment =>
    let arts :=
      (g.player controller).hand.filterMap (fun id =>
        match g.findObject? id with
        | some o => if o.printed.isArtifact then some o else none
        | none => none)
    if arts.isEmpty then
      g.logMsg "There is no artifact card in your hand"
    else
      { g with pending := .mayPutArtifactFromHand controller (sourceId.getD ⟨0⟩) }.logMsg
        s!"{(g.player controller).name} may put an artifact card from their hand onto the battlefield"
  | .fightUpToOne =>
    match sourceId.bind g.findObject?, targets[0]? with
    | some src, some (Target.permanent id) =>
      match g.findObject? id with
      | some dest =>
        if src.isOnBattlefield && dest.isOnBattlefield then
          g.fightCreatures src dest
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    | _, none => g
    | _, _ => g.logMsg "The source is no longer in play"
  | .returnToOwnerHand =>
    g.withLegalKindPermanent controller ab.targetKind targets (fun g o =>
      g.returnToHand o.id o.owner) sourceId none
  | .createZabu =>
    g.createNamedToken controller zabuToken
  | .oppCreatesTheVoid =>
    match targets[0]? with
    | some (Target.player pid) => g.createNamedToken pid theVoidToken
    | _ => g.createNamedToken controller theVoidToken
  | .createSturdyShieldAttach =>
    let (g, shield) := g.createToken controller sturdyShieldToken
    match sourceId.bind g.findObject? with
    | some src => g.attachSourceTo (g.object! shield.id) src
    | none => g
  | .exileGyPlayUntilNextTurn =>
    g.withLegalKindTarget controller ab.targetKind targets (fun g tgt =>
      match tgt with
      | Target.card id | Target.permanent id =>
        match g.findObject? id with
        | some o =>
          let name := o.name
          let (g, newId) := g.move o.id .exile none
          let o := g.object! newId
          let g := g.setObject { o with
            playPermission := some { player := controller, turnEndsRemaining := 2 } }
          g.logMsg
            s!"{(g.player controller).name} exiles {name} and may play it until the end of their next turn"
        | none => g.logMsg "The target is no longer in the graveyard"
      | _ => g) sourceId (some "The target is no longer legal")
  | .returnGyPermanentThisTurn =>
    g.withLegalKindTarget controller ab.targetKind targets (fun g tgt =>
      match tgt with
      | Target.card id | Target.permanent id =>
        g.returnToHand id controller
      | _ => g) sourceId (some "The target is no longer legal")
  | .tapCantUntapWhileControl =>
    g.withLegalKindPermanent controller .oppCreature targets
      (fun g o =>
        let g := g.applyPermanentAction o .tap
        let o := g.object! o.id
        let sid := sourceId.getD ⟨0⟩
        g.mapObjectStatus o (fun s =>
          { s with cantUntapGrantedBy := s.cantUntapGrantedBy.push sid }))
      sourceId (some "The target is no longer legal")
  | .maySacAnotherThenDestroyOppNonland =>
    let others :=
      (g.permanentsOf controller).filter (fun o =>
        o.isCreature && some o.id != sourceId)
    match others[0]? with
    | none =>
      g.logMsg "No other creature was sacrificed. The reflexive ability doesn't trigger."
    | some victim =>
      let g := g.sacrificeToGraveyard victim "Killmonger"
      g.queueModeledReflexive controller sourceId 7
  | .maySacOrDiscardNonlandThenDamage =>
    g.queueModeledReflexive controller sourceId 1
  | .revealHandExileUntilLeaves =>
    let opp? :=
      match targets[0]? with
      | some (Target.player pid) => some pid
      | _ =>
        match (g.livingOpponents controller)[0]? with
        | some pl => some pl.id
        | none => none
    match opp? with
    | none => g
    | some opp =>
      let g := g.revealHand opp
      g.withSourceStillOnBattlefield sourceId (fun g _ =>
        match targets[1]? with
        | some (Target.permanent id) =>
          match g.findObject? id with
          | some o =>
            if o.controlledBy opp then
              g.exileUntilSourceLeaves sourceId o
            else
              g.logMsg "The creature is an illegal target. The ability may still resolve."
          | none => g
        | some (Target.card id) =>
          match g.findObject? id with
          | some o =>
            if o.zone == .hand opp && !o.printed.isLand then
              g.exileUntilSourceLeaves sourceId o
            else g
          | none => g
        | _ => g)
        "Cloak and Dagger have left the battlefield. Nothing is exiled."
  | .plusOnesOrReturnArtEnch =>
    match targets[0]? with
    | some (Target.card id) =>
      g.returnToHand id controller
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        let g := g.addPlusOnePlusOneTo o 1
        match targets[1]? with
        | some (Target.permanent id2) =>
          match g.findObject? id2 with
          | some o2 => g.addPlusOnePlusOneTo o2 1
          | none => g
        | _ => g
      | none => g.logMsg "The target is no longer legal"
    | _ => g
  | .chooseUpToXModes =>
    let modes :=
      match sourceId.bind g.findObject? with
      | some o => o.status.chosenModes
      | none => #[]
    Id.run do
      let mut g := g
      for m in modes do
        if m == 0 then
          g := g.drawThenBeginDiscard controller
        else if m == 1 then
          g := g.forEachOpponent controller (fun g pid => g.loseLife pid 2)
        else if m == 2 then
          match targets[0]? with
          | some (Target.permanent id) =>
            match g.findObject? id with
            | some o =>
              if o.isOnBattlefield && o.printed.isToken then
                g := g.destroyPermanent o
            | none => pure ()
          | _ => pure ()
        else if m == 3 then
          match targets[1]? with
          | some (Target.permanent id) =>
            match g.findObject? id with
            | some o =>
              if o.isOnBattlefield then
                g := (g.move id (.graveyard o.owner) none).1
                  |>.logMsg s!"{o.name} is sacrificed"
              else
                g := g.logMsg "The token was already destroyed and can't be sacrificed"
            | none =>
              g := g.logMsg "The token was already destroyed and can't be sacrificed"
          | _ =>
            g := g.logMsg "The token was already destroyed and can't be sacrificed"
      return g
  | .mayTapThenGrantIndestructible =>
    match sourceId.bind g.findObject? with
    | some src =>
      if src.isOnBattlefield && !src.status.tapped then
        let g := g.applyPermanentAction src PermanentAction.tap
        g.queueModeledReflexive controller sourceId 0
      else
        g.logMsg "The source is not tapped this way. The reflexive ability doesn't trigger."
    | none =>
      g.logMsg "The source is no longer on the battlefield. The reflexive ability doesn't trigger."
  | .tapLoseAbilitiesWhileSource =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some tgt =>
        if !tgt.isOnBattlefield then g
        else
          let g := g.applyPermanentAction tgt .tap
          match sourceId.bind g.findObject? with
          | some src =>
            if src.isOnBattlefield then
              let tgt := g.object! id
              g.mapObjectStatus tgt (fun s =>
                { s with losesAbilitiesGrantedBy :=
                  s.losesAbilitiesGrantedBy.push src.id })
            else
              g.logMsg s!"The source has left. {tgt.name} is tapped but keeps its abilities."
          | none =>
            g.logMsg s!"The source has left. {tgt.name} is tapped but keeps its abilities."
      | none => g
    | _ => g
  | .revealDiscardFromHand =>
    match targets[0]? with
    | some (Target.player pid) =>
      let n :=
        1 + ((g.player controller).graveyard.filter (fun id =>
          match g.findObject? id with
          | some o => o.printed.isCreature
          | none => false)).size
      let hand :=
        (g.player pid).hand.filterMap (fun id => g.findObject? id)
      let shown := if hand.size ≤ n then hand else hand.take n
      let g := g.revealHand pid
      g.logMsg
        s!"{(g.player pid).name} reveals {shown.size} card(s) (all, if fewer than {n})"
    | _ => g
  | .createRedwing =>
    g.createNamedToken controller redwingToken
  | .step e =>
    g.applyModeledTrigger controller (.onStep (Effect.ofTrigger (.step e))) sourceId targets sourceName lastKnownPower
  | .death e =>
    g.applyModeledTrigger controller (.onDeath (Effect.ofTrigger (.death e))) sourceId targets sourceName lastKnownPower
  | .thisAttack e =>
    g.applyModeledTrigger controller (.onThisAttack (Effect.ofTrigger (.thisAttack e))) sourceId targets sourceName lastKnownPower
  | .enterOrAttack e =>
    g.applyModeledTrigger controller (.onEnterOrAttack (Effect.ofTrigger (.enterOrAttack e))) sourceId targets sourceName lastKnownPower
  | .watch e =>
    g.applyModeledTrigger controller (.onWatch (Effect.ofTrigger (.watch e))) sourceId targets sourceName lastKnownPower
  | .youAttacking e =>
    g.applyModeledTrigger controller (.onYouAttacking (Effect.ofTrigger (.youAttacking e))) sourceId targets sourceName lastKnownPower
  | .casting e =>
    g.applyModeledTrigger controller (.onCasting (Effect.ofTrigger (.casting e))) sourceId targets sourceName lastKnownPower
  | .resource e =>
    g.applyModeledTrigger controller (.onResource (Effect.ofTrigger (.resource e))) sourceId targets sourceName lastKnownPower

/-- Put attack-triggered abilities of `attackerIds` onto the stack (CR 508.2),
including “whenever you attack with one or more Elves” (once if any Elf attacks). -/
def putAttackTriggersOnStack (g : Game) (p : PlayerId) (attackerIds : Array ObjectId) : Game :=
  Id.run do
    let mut g := g
    for id in attackerIds do
      let o := g.object! id
      let skipIronMan :=
        o.printed.triggeredAbilities.any (fun t =>
          match t.shared with
          | .thisAttack .ifArtifactEnteredDraw =>
            !(g.player p).artifactEnteredThisTurn
          | _ => false)
      if !skipIronMan then
        g := g.putMatchingSourceTriggers p o .attacking
          (some (g.snapshotPower o)) (some (g.snapshotToughness o))
    let attackedWithElves := attackerIds.any (fun id => g.hasSubtype (g.object! id) "Elf")
    if attackedWithElves then
      g := g.putControlledTriggers p .youAttackWithElves
    let attacksSamePlayer :=
      attackerIds.any (fun id =>
        match (g.object! id).status.attackingWhom with
        | none => attackerIds.size >= 2
        | some d =>
          (attackerIds.filter (fun id' =>
            (g.object! id').status.attackingWhom == some d)).size >= 2)
    if attacksSamePlayer then
      g := g.putControlledTriggers p .youAttackWithTwoOrMore
    if !attackerIds.isEmpty then
      if attackerIds.any (fun id => g.hasSubtype (g.object! id) "Hero") then
        g := g.modifyPlayer p (fun pl => { pl with attackedWithHeroThisTurn := true })
      let merfolkDefenders :=
        attackerIds.foldl (fun acc id =>
          let o := g.object! id
          if !g.hasSubtype o "Merfolk" then acc
          else
            let d := o.status.attackingWhom.getD g.defendingPlayer
            if acc.any (· == d) then acc else acc.push d)
          (#[] : Array PlayerId)
      for _ in merfolkDefenders do
        g := g.putControlledTriggers p .merfolkAttackPlayer
      for id in attackerIds do
        let o := g.object! id
        if g.battlefield.any (fun eq =>
            eq.printed.isEquipment && eq.attachedTo == some o.id &&
              eq.controlledBy p) then
          g := g.putControlledTriggers p .equippedCreatureYouControlAttacks
      g := g.putControlledTriggers p .youAttack
      let pumps := (g.player p).attackPumpPerPlainsThisTurn
      if pumps > 0 then
        let src :=
          match (g.permanentsOf p).find? (fun o => o.printed.saga.isSome) with
          | some o => o
          | none =>
            { printed := { name := "Roads Go Ever, Ever On", types := #[.enchantment] }
              id := ⟨0⟩, owner := p, controller := some p, zone := .battlefield }
        for _ in [0:pumps] do
          g := g.queueTrigger p src .onYouAttackPumpTargetPerPlains .youAttack
    -- Destination does not matter: two attackers at different players
    -- still are not attacking alone (MSH 223).
    let attackingNow :=
      (g.permanentsOf p).filter (fun o => o.isCreature && o.status.attacking)
    if attackingNow.size == 1 then
      let attacker := attackingNow[0]!
      let aid := attacker.id
      for o in g.permanentsOf p do
        g := g.putMatchingSourceTriggers p o .creatureYouControlAttacksAlone
          (cause := some attacker)
        if o.attachedTo == some aid then
          g := g.putMatchingSourceTriggers p o .equippedAttacksAlone
    let totalPower :=
      attackerIds.foldl (fun acc id => acc + g.snapshotPower (g.object! id)) 0
    if totalPower >= 12 then
      g := g.putControlledTriggers p .youAttackWithTotalPower
    for id in attackerIds do
      for eq in g.battlefield do
        if eq.attachedTo == some id then
          match eq.controller with
          | some c =>
            g := g.putMatchingSourceTriggers c eq .equippedAttacks
          | none => pure ()
    return g

/-- Put becomes-blocked triggers for unique attackers in `assignments` (CR 509.5c). -/
def putBlockedTriggersOnStack (g : Game) (assignments : Array (ObjectId × ObjectId)) : Game :=
  Id.run do
    let mut g := g
    let mut seen : Array ObjectId := #[]
    for (_, attackerId) in assignments do
      if !seen.contains attackerId then
        seen := seen.push attackerId
        let o := g.object! attackerId
        match o.controller with
        | none => pure ()
        | some p =>
          g := g.putMatchingSourceTriggers p o .becomesBlocked
    return g

end Game
end Mtg.Engine
