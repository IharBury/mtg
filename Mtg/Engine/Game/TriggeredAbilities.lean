import Mtg.Engine.Game.Chapters

/-!
# Triggered-ability resolution (CR 603)

`applyTriggeredAbility` — resolving every modeled triggered ability —
plus attack triggers (CR 508.2) and becomes-blocked triggers (CR 509.5c)
going on the stack.
-/

namespace Mtg.Engine
namespace Game

/-- The target opponent may have `controller` draw a card (Palantír). -/
def offerPalantirChoice (g : Game) (controller opp : PlayerId) (sid : ObjectId) : Game :=
  g.beginFraChoice opp (.palantirMayDraw controller sid)
    s!"{(g.player opp).name} may have {(g.player controller).name} draw a card"

/-- Scry first when there are cards to look at; otherwise ask immediately. -/
def schedulePalantirChoice (g : Game) (controller opp : PlayerId) (sid : ObjectId) : Game :=
  match g.pending with
  | .scry _ _ => { g with palantirAfterScry := some (controller, opp, sid) }
  | _ => g.offerPalantirChoice controller opp sid

/-- Each opponent sacrifices a creature that dealt combat damage to
`controller` this turn, then the Ring tempts `controller`. -/
partial def beginSacDamagers (g : Game) (controller : PlayerId)
    (opponents : Array PlayerId) : Game :=
  match opponents[0]? with
  | none => g.temptWithTheRing controller
  | some p =>
    let rest := opponents.extract 1 opponents.size
    let ids :=
      ((g.creaturesControlledBy p).filter (fun o =>
        o.status.combatDamageToPlayers.contains controller)).map (·.id)
    if ids.isEmpty then
      let g :=
        g.logMsg s!"{(g.player p).name} controls no creature that dealt combat damage this turn"
      g.beginSacDamagers controller rest
    else if ids.size == 1 then
      let o := g.object! ids[0]!
      let g := g.sacrificeToGraveyard o
        s!"{(g.player p).name} sacrifices {o.name}"
      g.beginSacDamagers controller rest
    else
      g.beginFraChoice p (.sacrificeDamager ids rest controller)
        s!"{(g.player p).name} chooses a creature that dealt combat damage to sacrifice"

/-- You may cast an instant or sorcery from your hand with mana value at
most `maxMv`, without paying its mana cost. -/
def beginMayCastInstantSorceryFromHand (g : Game) (p : PlayerId) (maxMv : Nat) : Game :=
  let eligible := (g.player p).hand.filter (fun id =>
    (g.findObject? id).any (fun o =>
      o.printed.isInstantOrSorcery && o.printed.manaValue ≤ maxMv))
  if eligible.isEmpty then
    g.logMsg
      s!"{(g.player p).name} has no instant or sorcery with mana value {maxMv} or less"
  else
    g.beginFraChoice p (.mayCastInstantSorceryFromHand eligible)
      s!"{(g.player p).name} may cast an instant or sorcery spell with mana value {maxMv} or less without paying its mana cost"

/-- Exile until an instant or sorcery, then ask whether to cast it. -/
def beginGrimaImpulse (g : Game) (controller victim : PlayerId) : Game :=
  let (g, found, others) := g.exileUntilInstantOrSorcery victim
  match found with
  | none =>
    g.requestOrderInto others (.library victim)
      s!"{(g.player victim).name} randomizes the exiled cards; they become that player's library"
  | some cardId =>
    let name := (g.object! cardId).name
    g.beginFraChoice controller (.mayCastGrima cardId others victim)
      s!"{(g.player controller).name} may cast {name} without paying its mana cost"

/-- Apply one Alliance mode of `sourceId` if it has not been chosen this turn.
If every mode was already chosen, the ability is removed with no effect. -/
def applyAllianceMode (g : Game) (sourceId : ObjectId) (mode : Nat) : Game :=
  match g.findObject? sourceId with
  | none =>
    g.logMsg "The ability is removed from the stack with no effect"
  | some src =>
    if src.status.allianceModesChosen.size >= 3 ||
        (g.unusedAllianceModes src).isEmpty then
      g.logMsg
        "all three modes have been chosen this turn. The ability is removed from the stack with no effect"
    else if src.status.allianceModesChosen.contains mode then
      g.logMsg "That Alliance mode has already been chosen this turn"
    else
      let g := g.setObject { src with status :=
        { src.status with allianceModesChosen := src.status.allianceModesChosen.push mode } }
      match src.controller, mode with
      | some c, 0 =>
        let g := g.modifyPlayer c (fun pl =>
          { pl with manaPool := pl.manaPool.add (.colored .green) 3 })
        g.logMsg s!"{(g.player c).name} adds \{G}\{G}\{G}"
      | some c, 1 =>
        let creatures := (g.battlefield.filter (fun o => o.isCreature && o.controlledBy c)).map (·.id)
        let g := creatures.foldl (fun g id =>
          match g.findObject? id with
          | some o => g.addPlusOnePlusOneTo o 1
          | none => g) g
        g.logMsg s!"{(g.player c).name} puts a +1/+1 counter on each creature they control"
      | some c, 2 =>
        g.scryThenDraw c 2 1
      | _, _ => g

/-- Apply one unused Gollum mode. If every mode was already chosen, the
ability is removed with no effect and Gollum remains. -/
def applyGollumMode (g : Game) (sourceId : ObjectId) (mode : Nat) : Game :=
  match g.findObject? sourceId with
  | none =>
    g.logMsg "The ability is removed from the stack with no effect"
  | some src =>
    if (g.unusedGollumModes src).isEmpty then
      g.logMsg
        "all three modes have been chosen. The ability is removed from the stack with no effect"
    else if src.status.chosenModes.contains mode then
      g.logMsg "That mode has already been chosen"
    else
      let g := g.setObject { src with status :=
        { src.status with chosenModes := src.status.chosenModes.push mode } }
      match src.controller, mode with
      | some _, 0 =>
        g.addPlusOnePlusOneTo (g.object! sourceId) 1
      | some c, 1 =>
        let g := g.forEachOpponent c (fun g pid => g.loseLife pid 2)
        g.gainLife c 2
      | some c, 2 =>
        g.draw c 1
      | _, _ => g

/-- Ask `sourceId`'s controller for an Alliance mode that hasn't been chosen. -/
def offerAllianceMode (g : Game) (sourceId : Option ObjectId) : Game :=
  match sourceId.bind g.findObject? with
  | none => g.logMsg "The ability is removed from the stack with no effect"
  | some src =>
    let available := g.unusedAllianceModes src
    match src.controller with
    | none => g.logMsg "The ability is removed from the stack with no effect"
    | some p =>
      if available.isEmpty then
        g.logMsg
          "all three modes have been chosen this turn. The ability is removed from the stack with no effect"
      else
        { g with pending := .fraChoice p (.allianceMode src.id available) }.logMsg
          s!"{(g.player p).name} chooses an Alliance mode that hasn't been chosen this turn"

/-- Ask `sourceId`'s controller for a Gollum mode that hasn't been chosen. -/
def offerGollumMode (g : Game) (sourceId : Option ObjectId) : Game :=
  match sourceId.bind g.findObject? with
  | none => g.logMsg "The ability is removed from the stack with no effect"
  | some src =>
    let available := g.unusedGollumModes src
    match src.controller with
    | none => g.logMsg "The ability is removed from the stack with no effect"
    | some p =>
      if available.isEmpty then
        g.logMsg
          "all three modes have been chosen. The ability is removed from the stack with no effect"
      else
        { g with pending := .fraChoice p (.gollumMode src.id available) }.logMsg
          s!"{(g.player p).name} chooses a mode that hasn't been chosen"

/-- One of `ids`, chosen with the game's RNG. An empty list yields none. -/
def chooseRandomId (g : Game) (ids : Array ObjectId) : Game × Option ObjectId :=
  if ids.size ≤ 1 then (g, ids[0]?)
  else
    let (rng, shuffled) := g.rng.shuffle ids
    ({ g with rng }, shuffled[0]?)

/-- Put `chosen` from the revealed cards onto the battlefield, then the other
revealed cards on the bottom of the library in a random order. -/
def resolveRandomCreatureReveal (g : Game) (p : PlayerId) (revealed : Array ObjectId)
    (chosen : ObjectId) : Game :=
  let g :=
    match g.findObject? chosen with
    | some o =>
      let name := o.name
      let (g, newId) := g.putOntoBattlefield chosen p
      let g := g.logMsg s!"{name} enters the battlefield"
      g.afterPermanentEnters (g.object! newId)
    | none => g
  g.putRestOnBottomRandom p (revealed.filter (· != chosen))

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
    match rs.flatMap Resolution.flatten with
    | [.onPermanent .tap, .scry scryN, .draw drawN] =>
      g.resolveTapScryDraw controller ab.effect targets scryN drawN sourceId
        (fizzle := fun g => g.logIllegalSequenceTargets targets)
    | steps =>
      if g.sequenceAllTargetsIllegal controller ab.effect targets sourceId then
        g.logIllegalSequenceTargets targets
      else
        match steps with
        | [.shuffleSource, .draw n] =>
          g.shuffleSourceIntoLibrary sourceId (.draw controller n)
        | steps =>
          steps.foldl (fun g r =>
            let step : TriggeredAbility :=
              match ab with
              | .triggered w _ opts =>
                .triggered w { ab.effect with resolution := r } opts
            g.applyTriggeredAbility controller step sourceId targets dividedDamage
              lastKnownPower lastKnownToughness sourceName) g
  | .shuffleSource =>
    g.shuffleSourceIntoLibrary sourceId
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
  | .trigger _ => (
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
            g := g.dealDamageFrom o.name (g.object! b.id) n (source := some o)
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
      g.dealDamageFrom sourceName o n (source := sourceId.bind g.findObject?)
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
    let src := sourceId.bind g.findObject?
    if ab.opts.untargeted then
      g.forEachOpponent controller (fun g pid =>
        g.dealDamageToPlayer pid n (source := src))
    else
      g.withLegalTriggerPlayer controller ab sourceId targets (fun g pid =>
        g.dealDamageToPlayer pid n (source := src))
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
            let g := g.sacrificeToGraveyard src s!"{src.name} is sacrificed"
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
    g.amass controller "Goblin" n (attach := sourceId)
  | .attachSourceToTarget =>
    g.withLegalKindPermanent controller ab.targetKind targets (fun g host =>
      g.withSourceOnBattlefield sourceId (fun g src => g.attachSourceTo src host)
        "The Equipment is no longer in play")
      sourceId (some "The target is no longer legal")
  | .searchBasicToHand =>
    g.resolveSearchBasicLandToHand controller
  | .gainLifeSearchBasicOnTop n =>
    let g := g.gainLife controller n
    g.beginLibrarySearch controller isBasicLandCard "a basic land card" .topAfterShuffle
      (optional := true)
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
        if o.isOnBattlefield && !o.controlledBy controller &&
            (o.types.contains .artifact || o.types.contains .enchantment) then
          g := g.destroyPermanent o
          -- Only permanents actually destroyed count (indestructible ones stay).
          if !(g.findObject? o.id).any (·.isOnBattlefield) then
            n := n + 1
      return if n == 0 then g else g.gainLife controller n
  | .damageEqualSubtypeToEachOpponent subtype =>
    let n := g.countSubtype controller subtype
    let src := sourceId.bind g.findObject?
    g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid n (source := src))
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
          let before := o.status.damage
          let g := g.applyEffect controller (Effect.dealDamage n) #[tgt]
          -- “If a Dragon is dealt damage this way, destroy it.”
          match g.findObject? oid with
          | some o =>
            if g.hasSubtype o subtype && o.status.damage > before then g.destroyPermanent o
            else g
          | none => g
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
    let defn :=
      match sourceId.bind g.findObject? with
      | some src => src.status.attackingWhom.getD (g.opponent controller)
      | none => g.opponent controller
    let chosen :=
      match targets[0]? with
      | some (Target.permanent id) => some id
      | _ => none
    g.sacrificeLeastPowerCreature defn chosen
  | .createAxe =>
    let (g, _) := g.createToken controller axeToken
    g.logMsg "An Axe token is created"
  | .tapOppOrUntapYours =>
    g.logMsg "No mode was chosen"
  | .becomePT p t =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield then
        g.beginFraChoice controller (.mayBecomeBasePT o.id p t)
          s!"{(g.player controller).name} may have {o.name}'s base power and toughness become {p}/{t}"
      else g
    | none => g
  | .returnOtherPlusOne =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let owner := o.owner
      let (g, _) := g.move o.id (.hand owner) none
      g.applyOnTriggerSource sourceId (.plusOne 1))
  | .lookAtTopRevealTypes n types =>
    let ids := g.scryLookedIds controller n
    let g := g.logLookAtTop controller n
    let eligible := ids.filter (fun id =>
      match g.findObject? id with
      | some o =>
        types.any (fun t =>
          (t.toLower == "permanent" && o.printed.isPermanentCard) ||
            (t.toLower == "creature" && o.printed.isCreature) ||
            o.printed.hasSubtype t)
      | none => false)
    g.beginFraChoice controller (.mayRevealToHand ids eligible false)
      s!"{(g.player controller).name} may reveal a card from among them and put it into their hand"
  | .pumpAndDamageOpponents n =>
    let g := g.applyOnTriggerSource sourceId (.pump 1 1)
    let src := sourceId.bind g.findObject?
    g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid n (source := src))
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
  | .putNonlandMvAtMostFromGy _ =>
    g.withLegalTriggerTarget controller ab sourceId targets (fun g t =>
      match t with
      | Target.card id =>
        match g.findObject? id with
        | some card =>
          let (g, newId) := g.putOntoBattlefield id card.owner
          let g := g.logMsg s!"{card.name} is put onto the battlefield under its owner's control"
          g.afterPermanentEnters (g.object! newId)
        | none => g
      | _ => g) "No card was chosen"
  | .honeEachEquipment =>
    let eqs :=
      g.battlefield.filter (fun o => o.controlledBy controller && o.printed.isEquipment)
    eqs.foldl (init := g) fun acc eq =>
      let n := acc.countersYouPut eq 1 (putter := some controller)
      acc.mapObjectStatus eq (fun s => { s with hone := s.hone + n })
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
      let g := g.dealDamageFrom sourceName o amt (source := sourceId.bind g.findObject?)
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
      return { g with additionalCombatPhases := g.additionalCombatPhases + 1 }.logMsg
        "Attacking creatures untap. After this phase, there is an additional combat phase"
  | .eaglesCreateBirds =>
    let n := lastKnownPower.getD 0
    g.createKindTokens controller .birdSoldier n.toNat |>.logMsg
      s!"{(g.player controller).name} creates {n} Bird Soldier token(s)"
  | .allianceMode =>
    g.offerAllianceMode sourceId
  | .gollumMode =>
    g.offerGollumMode sourceId
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
    g.beginFraChoice controller (.mayDiscardHandBalin sourceId)
      s!"{(g.player controller).name} may discard their hand"
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
          let n := g.countersYouPut o 1 (putter := some controller)
          let g := g.setObject { o with status :=
            { o.status with
              trampleCounters := o.status.trampleCounters + n
              additionalSubtypes := extra } }
          g.logMsg s!"{o.name} gets a trample counter and becomes a Bear"
        | none => g
      | _ => g
    if g.countSubtype controller "Bear" >= 3 then g.draw controller 2 else g
  | .castFromGyArtifactInstantSorcery =>
    let eligible := (g.player controller).graveyard.filter (fun id =>
      (g.findObject? id).any (fun o => o.printed.isArtifact || o.printed.isInstantOrSorcery))
    if eligible.isEmpty then
      g.logMsg s!"{(g.player controller).name} has no artifact, instant, or sorcery in the graveyard"
    else
      { g with pending := .fraChoice controller (.mayCastFromGraveyard eligible) }.logMsg
        s!"{(g.player controller).name} may cast an artifact, instant, or sorcery spell from their graveyard"
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
    g.putReflexiveTrigger controller (some tok.id) {
      targeting := .of .creatureYouControl
      resolution := .attach
      phrase := "Attach it to target creature you control" }
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
        let g := g.setObject { host with status := host.status.withoutCounters }
        g.logMsg s!"counters are removed from {host.name}"
  | .revealTopPutRandomCreature n =>
    let ids := g.scryLookedIds controller n
    let g := ids.foldl (fun g id =>
      match g.findObject? id with
      | some o => g.logMsg s!"{(g.player controller).name} reveals {o.name}"
      | none => g) g
    let creatures := ids.filter (fun id => (g.findObject? id).any (·.printed.isCreature))
    if creatures.isEmpty then
      (g.logMsg "No creature card was revealed").putRestOnBottomRandom controller ids
    else if g.norandom && creatures.size > 1 then
      { g with
        pending := .resolveRandom (.chooseObject creatures)
        afterRandom := .revealRandomCreatureThenBottom controller ids }
        |>.logMsg
          s!"{(g.player controller).name} puts a random creature from among them onto the battlefield"
    else
      let (g, chosen) := g.chooseRandomId creatures
      match chosen with
      | some id => g.resolveRandomCreatureReveal controller ids id
      | none => g.putRestOnBottomRandom controller ids
  | .beginCombatIfDrawnTwoPump =>
    if (g.player controller).cardsDrawnThisTurn < 2 then g
    else
      g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
        let g := g.pumpPermanent o 3 0
        g.grantUntilEotLogged (g.object! o.id) Keyword.firstStrike)
        "The target is no longer legal"
  | .mountainQuestDragon =>
    g.withTriggerSource sourceId fun g src =>
      let n := g.countersYouPut src 1 (putter := some controller)
      let g := g.setObject { src with status :=
        { src.status with quest := src.status.quest + n } }
      let src := g.object! src.id
      let g := g.logMsg s!"{src.name} gets a quest counter ({src.status.quest})"
      if src.status.quest >= 6 then
        let name := src.name
        let (g, _) := g.move src.id (.graveyard src.owner) none
        let g := g.logMsg s!"{name} is sacrificed"
        g.beginLibrarySearch controller (fun c => c.hasSubtype "Dragon") "a Dragon card"
          .battlefieldFromHandOrLibrary (alsoHand := true)
      else g
  | .millPlayer n =>
    g.withLegalTriggerPlayer controller ab sourceId targets (fun g pid => g.mill pid n)
  | .treasuresPerChosenType =>
    let types := (g.creaturesControlledBy controller).foldl (fun acc o =>
      o.subtypes.foldl (fun acc t => if acc.contains t then acc else acc.push t) acc) #[]
    if types.isEmpty then
      g.logMsg s!"{(g.player controller).name} controls no creatures, so no Treasures are created"
    else
      g.beginFraChoice controller (.chooseCreatureType types)
        s!"{(g.player controller).name} chooses a creature type"
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
        return g.putRestOnBottomRandom controller rest
      | some cid =>
        let o := g.object! cid
        let lands := g.landsYouControl controller
        let (g', newId) :=
          if o.printed.manaValue <= lands then
            g.putOntoBattlefield cid controller
          else
            g.move cid (.hand controller) none
        g := g'
        g :=
          if o.printed.manaValue <= lands then
            g.logMsg s!"{o.name} enters the battlefield"
          else
            g.logMsg s!"{o.name} is put into {(g.player controller).name}'s hand"
        if o.printed.manaValue <= lands then
          g := g.afterPermanentEnters (g.object! newId)
        return g.putRestOnBottomRandom controller rest
  | .attackSacPlusOneEqualPower =>
    match sourceId with
    | none => g.logMsg "No other creature to sacrifice"
    | some sid =>
      let others := (g.creaturesControlledBy controller).filter (·.id != sid)
      if others.isEmpty then g.logMsg "No other creature to sacrifice"
      else
        g.beginFraChoice controller (.maySacrificeAnotherCreatureForPower sid)
          s!"{(g.player controller).name} may sacrifice another creature"
  | .amassGoblinsEqualPower =>
    let n := (lastKnownPower.getD 0).toNat
    g.amassGoblins controller n
  | .payReturnFromGy =>
    match sourceId.bind g.findObject? with
    | none => g.logMsg "The ability's source is no longer in the graveyard"
    | some src =>
      if src.zone != .graveyard src.owner then
        g.logMsg s!"{src.name} is no longer in the graveyard"
      else
        let symbols := #[ManaSymbol.generic 1, ManaSymbol.colored .green, ManaSymbol.colored .blue]
        g.beginFraChoice controller (.mayPaySymbolsThen symbols .returnSourceToHand src.id)
          s!"{(g.player controller).name} may pay \{1}\{G}\{U} to return {src.name} to their hand"
  | .lootLandEntersTapped =>
    let g := { g with lootLandEntersTapped := true }
    let g := g.drawThenBeginDiscard controller
    match g.pending with
    | .chooseDiscardCard .. => g
    | _ => { g with lootLandEntersTapped := false }
  | .honePerOppAttach =>
    let opp :=
      match targets[0]? with
      | some (Target.player pid) => pid
      | some (Target.permanent _) => g.opponent controller
      | _ => g.opponent controller
    let n := g.countCreaturesControlledBy opp
    let g :=
      g.withTriggerSource sourceId fun g src =>
        let k := g.countersYouPut src n (putter := some controller)
        g.mapObjectStatus src (fun s => { s with hone := s.hone + k })
          |>.logMsg s!"{src.name} gets {k} hone counter(s)"
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
    match lastKnownPower, lastKnownToughness with
    | some n, some idx => g.mill ⟨idx.toNat⟩ n.toNat
    | _, _ => g
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
    match sourceId with
    | none => g.logMsg "Nothing to sacrifice"
    | some sid =>
      let any := (g.permanentsOf controller).any (fun o =>
        o.id != sid && (o.isCreature || o.printed.isArtifact))
      if !any then g.logMsg "Nothing to sacrifice"
      else
        g.beginFraChoice controller (.maySacrificeAnotherForDrawTreasure sid)
          s!"{(g.player controller).name} may sacrifice another creature or artifact"
  | .targetOpponentLosesLife n =>
    g.withLegalTriggerPlayer controller ab sourceId targets (fun g pid =>
      g.loseLife pid n)
  | .attachEquipmentThenFight =>
    match targets[0]? with
    | some (Target.permanent hid) =>
      match g.findObject? hid with
      | none => g.logMsg "The target is no longer legal"
      | some host =>
        if !host.isOnBattlefield || !host.isCreature then
          g.logMsg "The target is no longer legal"
        else
          let eligible :=
            ((g.permanentsOf controller).filter (fun o =>
              o.printed.isEquipment && o.attachedTo != some host.id)).map (·.id)
          if eligible.isEmpty then
            g.logMsg "No Equipment was attached this way"
          else
            g.beginFraChoice controller (.attachAnyEquipment host.id eligible)
              s!"{(g.player controller).name} chooses any number of Equipment to attach to {host.name}"
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
    -- X is the mana spent to cast the triggering spell.
    let n := ((g.resolvingAbilityObject?.bind (·.fraCauseStatus)).map (·.manaSpentToCast)).getD 0
    if n == 0 then g.logMsg "No mana was spent to cast that spell"
    else
      g.beginFraChoice controller (.mayDrawThenDiscard n 2)
        s!"{(g.player controller).name} may draw {n} cards, then discard two"
  | .plusOneEachIfCityBlessing =>
    let n := if (g.player controller).citysBlessing then 2 else 1
    (g.permanentsOf controller).foldl (fun acc o =>
      if o.isCreature then acc.addPlusOnePlusOneTo o n else acc) g
  | .castInstantSorceryFromHand =>
    let wizards :=
      (g.permanentsOf controller).filter (fun o =>
        o.isLegendary && g.hasSubtype o "Wizard") |>.size
    g.beginMayCastInstantSorceryFromHand controller (wizards * 2)
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
    g.beginMayCastInstantSorceryFromHand controller (lastKnownPower.getD 0).toNat
  | .grimaImpulse =>
    let victim := g.lastCombatDamagePlayer.getD (g.opponent controller)
    g.beginGrimaImpulse controller victim
  | .palantir =>
    let tgt :=
      match targets[0]? with
      | some (Target.player pid) => some pid
      | _ => none
    match sourceId with
    | none => g.logMsg "The source is no longer in play"
    | some sid =>
      let before := ((g.findObject? sid).map (·.status.influence)).getD 0
      let g := g.applyPalantir sid tgt
      match tgt with
      | none => g
      | some opp =>
        match g.findObject? sid with
        | some src =>
          if src.status.influence > before then
            g.schedulePalantirChoice controller opp sid
          else g
        | none => g
  | .millThenCopy =>
    let opps := (g.livingOpponents controller).map (·.id)
    let (g, milled) := g.millThenReflexive opps 2
    if !milled then g
    else
      let mv :=
        match g.fraCause? with
        | some spell => g.objectManaValue spell
        | none => (lastKnownPower.getD 0).toNat
      g.putReflexiveTrigger controller sourceId {
        targeting := .of (.filtered {
          noun := s!"target enchantment, instant, or sorcery card with mana value {mv} or less from an opponent's graveyard"
          zone := .anyGraveyard
          types := #[.enchantment, .instant, .sorcery]
          controller := .opponent
          mvAtMost := some mv })
        resolution := .fra .sarumanExileCopyMayCast
        phrase := "Exile that card. Copy it. You may cast the copy without paying its mana cost" }
  | .amassOrcs n =>
    g.amassOrcs controller n
  | .ringTempts =>
    g.temptWithTheRing controller
  | .mayDiscardHandDraw n =>
    g.beginFraChoice controller (.mayDiscardHandDrawFixed n)
      s!"{(g.player controller).name} may discard their hand. If they do, they draw {n} cards"
  | .treasuresEqualLastKnown =>
    let n := (lastKnownPower.getD 0).toNat
    g.createTreasureTokens controller n
  | .protectionEverything =>
    if !(sourceId.bind g.findObject?).any (·.wasCast) then
      g.logMsg "It wasn't cast. The ability does nothing."
    else
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
        return g.putRestOnBottomRandom controller rest
      | some sid =>
        let name := (g.object! sid).name
        let (g', newId) := g.putOntoBattlefield sid controller
        g := g'.logMsg s!"{name} enters the battlefield"
        g := g.afterPermanentEnters (g.object! newId)
        return g.putRestOnBottomRandom controller rest
  | .sacDamagersRingTempts =>
    g.beginSacDamagers controller ((g.livingOpponents controller).map (·.id))
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
      let g := g.addPlusOnePlusOneTo o 1
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
      g.gainLife controller n)
  | .drawLoseLifeAndPlan =>
    g.incrementPlanThen controller sourceId (fun g _ =>
      g.drawThenLoseLife controller 1 1)
  | .treasureTappedAndPlan =>
    g.incrementPlanThen controller sourceId (fun g _ =>
      (g.createToken controller treasureToken (tapped := true)).1)
  | .plusOneOnTargetAndPlan =>
    g.withSourceOnBattlefield sourceId fun g src =>
      g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
        let n := g.countersYouPut src 1 (putter := some controller)
        let g := Id.run do
          let mut g := g
          for _ in [0:n] do
            match g.findObject? src.id with
            | some cur =>
              g := g.setObject { cur with status :=
                { cur.status with plan := cur.status.plan + 1 } }
              let cur := g.object! cur.id
              g := g.putMatchingSourceTriggers controller cur
                (.nthPlanCounter cur.status.plan)
            | none => pure ()
          return g
        g.addPlusOnePlusOneTo o 1 (byPlayer := some controller))
        "The target is no longer legal. You won't put counters on anything."
  | .planFinishDrawPlusOneEach =>
    let g := g.sacrificePlanIfOnBattlefield sourceId
    let g := g.draw controller 1
    g.foldBattlefield (fun c => c.controlledBy controller && c.isCreature)
      (fun g c => g.addPlusOnePlusOneTo c 1)
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
    { g with pending := .maySacArtifactOrDiscard controller 1 }.logMsg
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
      let n := g.countersYouPut src 1 (putter := some controller)
      g.mapObjectStatus src (fun s => { s with invasion := s.invasion + n })
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
    match sourceId with
    | some sid =>
      let pick := CostPick.sacrificeAnotherSubtype "Creature"
      if (g.costPickCandidates controller sid pick).isEmpty then
        g.logMsg "There is no other creature to sacrifice. The reflexive ability doesn't trigger."
      else
        g.beginFraChoice controller (.mayPayPickThen pick (.mshReflexive 7 0) sid)
          s!"{(g.player controller).name} may sacrifice another creature"
    | none => g
  | .maySacOrDiscardNonlandThenDamage =>
    match sourceId with
    | some sid =>
      if (g.costPickCandidates controller sid .sacrificeArtifactOrDiscardNonland).isEmpty then g
      else
        g.beginFraChoice controller
          (.mayPayPickThen .sacrificeArtifactOrDiscardNonland (.reflexiveDamageAnyTarget 2) sid)
          s!"{(g.player controller).name} may sacrifice an artifact or discard a nonland card"
    | none => g
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
        g.beginFraChoice controller (.mayTapSourceThen (.mshReflexive 0 0) src.id)
          s!"{(g.player controller).name} may tap {src.name}"
      else
        g.logMsg s!"{src.name} can't be tapped this way. The reflexive ability doesn't trigger."
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
  | .surveil n =>
    g.beginSurveil controller n
  | .empowerJace n =>
    g.empowerJace controller n
  | .prepareSourceIfNot =>
    match sourceId.bind g.findObject? with
    | some o =>
      if !o.isOnBattlefield then g.logMsg s!"{o.name} is no longer on the battlefield"
      else if o.status.prepared then g.logMsg s!"{o.name} is already prepared"
      else g.becomePrepared o
    | none => g.logMsg "The source is no longer on the battlefield"
  | .drawIfRemovedTwoLoyalty =>
    g.draw controller 1
  | .creaturesYouControlGet pw tw =>
    g.pumpControlledCreatures controller pw tw
  | .pumpIfFiveOtherForests =>
    -- Rulings 818 / 819: count Forests other than the one that caused the
    -- trigger, whether or not that one is still on the battlefield.
    let cause : Option ObjectId := lastKnownPower.map (fun n => ⟨n.toNat⟩)
    let others := ((g.permanentsOf controller).filter (fun o =>
      g.hasSubtype o "Forest" && some o.id != cause)).size
    if others < 5 then
      g.logMsg "You control fewer than five other Forests. The ability doesn't resolve"
    else
      g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
        g.pumpPermanent o 3 3)
  | .surveilReturnIfGainedLife =>
    -- Ruling 750: the life gained is checked as the ability resolves.
    let n := (g.player controller).lifeGainedThisTurn
    let g := g.beginSurveil controller 1
    match g.pending with
    | .surveil _ _ => { g with surveilReturnMvAtMost := some n }
    | _ => g
  | .drawTwoWinIfEmptyShuffleSource =>
    -- Ruling 835: you win while the ability resolves, before the
    -- state-based action for drawing from an empty library.
    let g := g.draw controller 2
    if (g.player controller).library.isEmpty then
      { g with result := some (.won controller) }.logMsg
        s!"{(g.player controller).name} wins the game"
    else g.shuffleSourceIntoLibrary sourceId
  | .putSourceCountersOnTarget =>
    -- Rulings 756 / 758: each kind of counter it had as it died, in the same
    -- numbers; nothing moves from the dead creature.
    match sourceId.bind (fun id => g.lastKnownStatus.reverse.find? (·.1 == id)) with
    | none => g.logMsg "The source had no counters"
    | some (_, last) =>
      g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
        let extra := g.docSamsonBonus (some controller) o.controller
        let g := g.mapObjectStatus o (fun s => s.addCountersExceptPlusOne last extra)
        let o := g.object! o.id
        let g :=
          if last.plusOnePlusOne > 0 then
            g.addPlusOnePlusOneTo o last.plusOnePlusOne (byPlayer := some controller)
          else g
        g.logMsg s!"The counters are put on {o.name}") "No target was chosen"
  | .chargeCounterOnSource =>
    g.withSourceOnBattlefield sourceId (fun g o =>
      let n := g.countersYouPut o 1 (putter := some controller)
      let g := g.mapObjectStatus o (fun s => { s with charge := s.charge + n })
      g.logMsg s!"A charge counter is put on {o.name}")
  | .addGreenPerChargeCounter =>
    -- Ruling 792: if the source left, use its last-known charge counters.
    let n :=
      match sourceId.bind g.findObject? with
      | some o => if o.isOnBattlefield then o.status.charge else 0
      | none => 0
    let n :=
      if n == 0 then
        match sourceId.bind (fun id => g.lastKnownStatus.reverse.find? (·.1 == id)) with
        | some (_, last) => last.charge
        | none => n
      else n
    g.addManaLogged controller (Array.replicate n (.colored .green))
  | .mayPayPlusOneAndDraw n =>
    { g with pending := .mayPayGeneric controller n, mayPayAlsoPlusOneOn := sourceId }.logMsg
      s!"{(g.player controller).name} may pay \{{n}} to put a +1/+1 counter on it and draw a card"
  | .loyaltyOnSource =>
    g.withSourceOnBattlefield sourceId (fun g o =>
      let n := g.countersYouPut o 1 (putter := some controller)
      let g := g.mapObjectStatus o (fun s => { s with loyaltyCounters := s.loyaltyCounters + n })
      let g := g.queueLoyaltyPutTriggers controller
      g.logMsg s!"A loyalty counter is put on {o.name}")
  | .grantThenCounterByType k =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let g := g.grantUntilEotLogged o k
      let o := g.object! o.id
      let g := if o.isCreature then g.addPlusOnePlusOneTo o 1 else g
      let o := g.object! o.id
      if o.printed.isPlaneswalker then
        let n := g.countersYouPut o 1 (putter := some controller)
        let g := g.mapObjectStatus o (fun s => { s with loyaltyCounters := s.loyaltyCounters + n })
        let g := g.queueLoyaltyPutTriggers controller
        g.logMsg s!"A loyalty counter is put on {o.name}"
      else g)
  | .destroyOppPermanentIfSixLands =>
    if ((g.permanentsOf controller).filter (·.printed.isLand)).size < 6 then
      g.logMsg "You control fewer than six lands. The ability doesn't resolve (ruling 889)"
    else
      g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
        let owner := o.controller.getD o.owner
        let g := g.destroyPermanent o
        g.createTreasureTokens owner 1)
  | .pumpOrCounterIfScried =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      if (g.player controller).scriedOrSurveilledThisTurn then g.addPlusOnePlusOneTo o 1
      else g.pumpPermanent o 1 1)
  | .sacrificeSourceIfNoPlaneswalker =>
    if (g.permanentsOf controller).any (·.printed.isPlaneswalker) then
      g.logMsg "You control a planeswalker. The ability does nothing"
    else
      g.withSourceOnBattlefield sourceId (fun g o =>
        g.sacrificeToGraveyard o s!"{(g.player controller).name} sacrifices {o.name}")
  | .plusOneOnEachSubtypeYouControl s =>
    (g.permanentsOf controller).foldl (fun g o =>
      if g.hasSubtype o s then g.addPlusOnePlusOneTo (g.object! o.id) 1 else g) g
  | .prepareSourceIfThreeDied =>
    if g.battlefieldCreaturesToGyThisTurn.size < 3 then
      g.logMsg "Fewer than three creatures died this turn"
    else
      match sourceId.bind g.findObject? with
      | some o =>
        if o.isOnBattlefield then g.becomePrepared o
        else g.logMsg s!"{o.name} is no longer on the battlefield"
      | none => g.logMsg "The source is no longer on the battlefield"
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
    g.applyModeledTrigger controller (.onResource (Effect.ofTrigger (.resource e))) sourceId targets sourceName lastKnownPower)
  | r =>
    g.applyUnifiedAbility controller { ab.effect with resolution := r }
      targets sourceId lastKnownPower

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
      -- Reality Fracture: each attacking creature, and one attacking a player
      -- alone (no other creature attacks that player; ruling 861).
      g := g.putFraEventTriggers p .creatureYouControlAttacks (cause := some o)
      let whom := o.status.attackingWhom.getD g.defendingPlayer
      let alone := !attackerIds.any (fun id' =>
        id' != id && (g.object! id').status.attackingWhom.getD g.defendingPlayer == whom &&
          (g.object! id').status.attackingPlaneswalker.isNone) &&
        o.status.attackingPlaneswalker.isNone
      if alone then
        g := g.putFraEventTriggers p .creatureYouControlAttacksPlayerAlone (cause := some o)
      -- “Whenever enchanted creature attacks or blocks” (Super-Soldier Serum).
      for aura in g.battlefield do
        if aura.attachedTo == some o.id then
          match aura.controller with
          | some c => g := g.putMatchingSourceTriggers c aura .enchantedAttacksOrBlocks
          | none => pure ()
      -- Jace, Reality Sculptor's effect: a creature attacks that player or a
      -- planeswalker they control.
      g := g.putFraEventTriggers whom .creatureAttacksYouOrYourPlaneswalker (cause := some o)
    -- Garruk, Curse Breaker's effect: once for each opponent attacked. The
    -- cause records the attacked player as its controller.
    let attackedPlayers := attackerIds.foldl (fun (acc : Array PlayerId) id =>
      let o := g.object! id
      if o.status.attackingPlaneswalker.isSome then acc
      else
        let d := o.status.attackingWhom.getD g.defendingPlayer
        if acc.contains d then acc else acc.push d) #[]
    for d in attackedPlayers do
      match attackerIds.find? (fun id =>
          let o := g.object! id
          o.status.attackingPlaneswalker.isNone &&
            o.status.attackingWhom.getD g.defendingPlayer == d) with
      | some id =>
        for q in g.livingPlayers do
          if q.id != d then
            g := g.putFraEventTriggers q.id .creaturesAttackYourOpponent
              (cause := some { g.object! id with controller := some d })
      | none => pure ()
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
      g := g.modifyPlayer p (fun pl => { pl with
        creaturesAttackedWithThisTurn := pl.creaturesAttackedWithThisTurn + attackerIds.size })
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
    -- Tetsuko Umezawa, Pursuer: a small creature an opponent controls blocks.
    let mut blockers : Array ObjectId := #[]
    for (blockerId, _) in assignments do
      if !blockers.contains blockerId then
        blockers := blockers.push blockerId
        let b := g.object! blockerId
        for aura in g.battlefield do
          if aura.attachedTo == some b.id then
            match aura.controller with
            | some c => g := g.putMatchingSourceTriggers c aura .enchantedAttacksOrBlocks
            | none => pure ()
        if g.power b ≤ 1 || g.toughness b ≤ 1 then
          for pl in g.livingPlayers do
            if some pl.id != b.controller then
              g := g.putFraEventTriggers pl.id .opponentSmallCreatureBlocks (cause := some b)
    return g

end Game
end Mtg.Engine
