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
`controller` this turn. The Ring tempts `controller` as a following sequence
step. -/
partial def beginSacDamagers (g : Game) (controller : PlayerId)
    (opponents : Array PlayerId) : Game :=
  match opponents[0]? with
  | none => g
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

/-- Ask for one mode in `modes` that `how` has not already recorded on the
source. `oneUnusedThisTurn` is an Alliance choice. `oneUnused` is a Gollum
choice. The chosen resolution runs later from `chooseModesRest`. -/
def offerChooseModes (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (dividedDamage : Array Nat) (lastKnownPower : Option Int)
    (lastKnownToughness : Option Int) (sourceName : String)
    (cardPower : Option Nat) (modes : List TriggeredAbility.TriggerResolution)
    (how : TriggeredAbility.TriggerModeHow) : Game :=
  match sourceId.bind g.findObject? with
  | none => g.logMsg "The ability is removed from the stack with no effect"
  | some src =>
    let memory :=
      match how with
      | .oneUnusedThisTurn => src.status.allianceModesChosen
      | .vision => src.status.modesChosenThisTurn
      | .oneUnused | .alreadyChosen | .plusOneOrRemoveCounter | .fromLastKnown =>
        src.status.chosenModes
    let available := unusedModes memory (List.range modes.length).toArray
    match src.controller with
    | none => g.logMsg "The ability is removed from the stack with no effect"
    | some p =>
      if available.isEmpty then
        match how with
        | .oneUnusedThisTurn =>
          g.logMsg
            "all three modes have been chosen this turn. The ability is removed from the stack with no effect"
        | .vision =>
          g.logMsg "The Vision's ability is removed from the stack with no effect"
        | .oneUnused | .alreadyChosen | .plusOneOrRemoveCounter | .fromLastKnown =>
          g.logMsg
            "all three modes have been chosen. The ability is removed from the stack with no effect"
      else
        let rest : ChooseModesRest := {
          controller, ability := ab, sourceId, targets, dividedDamage,
          lastKnownPower, lastKnownToughness, sourceName, cardPower, modes, how }
        match how with
        | .oneUnusedThisTurn =>
          { g with
              pending := .fraChoice p (.allianceMode src.id available)
              chooseModesRest := some rest }.logMsg
            s!"{(g.player p).name} chooses an Alliance mode that hasn't been chosen this turn"
        | .oneUnused =>
          { g with
              pending := .fraChoice p (.gollumMode src.id available)
              chooseModesRest := some rest }.logMsg
            s!"{(g.player p).name} chooses a mode that hasn't been chosen"
        | .vision =>
          { g with
              pending := .fraChoice p (.visionMode src.id available)
              chooseModesRest := some rest }.logMsg
            "Choose one that hasn't been chosen this turn"
        | .alreadyChosen | .plusOneOrRemoveCounter | .fromLastKnown => g

/-- Destroy `targets[0]` when it is a token still on the battlefield. -/
def destroyChosenToken (g : Game) (targets : Array Target) : Game :=
  match targets[0]? with
  | some (Target.permanent id) =>
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield && o.printed.isToken then g.destroyPermanent o else g
    | none => g
  | _ => g

/-- Sacrifice `targets[1]`, or log that the token is already gone. -/
def sacrificeChosenOrGone (g : Game) (targets : Array Target) : Game :=
  match targets[1]? with
  | some (Target.permanent id) =>
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield then
        (g.move id (.graveyard o.owner) none).1.logMsg s!"{o.name} is sacrificed"
      else
        g.logMsg "The token was already destroyed and can't be sacrificed"
    | none =>
      g.logMsg "The token was already destroyed and can't be sacrificed"
  | _ =>
    g.logMsg "The token was already destroyed and can't be sacrificed"

/-- Apply one entry of `TriggerResolution.chooseModes`. Destroying the
announced token and sacrificing the announced creature stay on those
targets. Every other resolution runs through `generic`. -/
def applyChooseModeStep (g : Game) (targets : Array Target)
    (r : TriggeredAbility.TriggerResolution)
    (generic : Game → TriggeredAbility.TriggerResolution → Game) : Game :=
  match r with
  | .destroy .target .chosenToken => g.destroyChosenToken targets
  | .sacrifice .eachPlayersCreature _ => g.sacrificeChosenOrGone targets
  | other => generic g other

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

/-- The announced permanent target when it is still legal, with the same
logs as `withLegalTriggerPermanent`. -/
def legalTriggerPermanent? (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target) : Game × Option GameObject :=
  let legal := g.legalTargetsForKind controller ab.targetKind sourceId
  match targets[0]? with
  | none => (g.logMsg "The target is no longer legal", none)
  | some t =>
    if !legal.contains t then (g.illegalAbilityTarget t, none)
    else
      match t with
      | Target.permanent oid =>
        match g.findObject? oid with
        | some o => (g, some o)
        | none => (g.logMsg "The target is no longer in play", none)
      | _ => (g.logMsg "The target is no longer legal", none)

/-- Object id recorded as the cause of the ability now resolving. -/
def resolvingCauseId (g : Game) : Option ObjectId :=
  ((g.resolvingAbility.bind g.findObject?).bind (·.fraCauseId)).map g.followMoved

/-- Whether `cond` holds as this trigger resolves. One-shot notes that the
action does not read are cleared here. -/
def triggerIfHolds (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target) (lastKnownPower : Option Int)
    (cond : TriggeredAbility.TriggerIf) : Game × Bool :=
  match cond with
  | .noLegendaryCreature => (g, !g.controlsLegendaryCreature controller)
  | .removedHope =>
    let removed := g.removedHopeThisWay
    ({ g with removedHopeThisWay := false }, removed)
  | .noHopeOnSource =>
    match sourceId.bind g.findObject? with
    | some src => (g, src.isOnBattlefield && src.status.hope == 0)
    | none => (g, false)
  | .drewAtLeast n => (g, (g.player controller).cardsDrawnThisTurn ≥ n)
  | .dealtDamageToSubtype subtype =>
    match g.permanentDealtDamageThisWay with
    | none => (g, false)
    | some oid =>
      match g.findObject? oid with
      | some o =>
        if o.isOnBattlefield && g.hasSubtype o subtype then (g, true)
        else ({ g with permanentDealtDamageThisWay := none }, false)
      | none => ({ g with permanentDealtDamageThisWay := none }, false)
  | .attackedOrEntered subtype =>
    let pl := g.player controller
    let holds :=
      (subtype == "Hero" && (pl.attackedWithHeroThisTurn || pl.heroEnteredThisTurn)) ||
        (g.battlefield.any (fun o =>
          o.controlledBy controller && g.hasSubtype o subtype &&
            (o.status.attacking || o.status.enteredThisTurn)))
    (g, holds)
  | .removedLoyaltyAtLeast n => (g, (lastKnownPower.getD 0) ≥ Int.ofNat n)
  | .landsAtLeast n =>
    let lands := ((g.permanentsOf controller).filter (·.printed.isLand)).size
    if lands < n then
      let g :=
        if n == 6 then
          g.logMsg "You control fewer than six lands. The ability doesn't resolve (ruling 889)"
        else g
      (g, false)
    else (g, true)
  | .noPlaneswalker =>
    if (g.permanentsOf controller).any (·.printed.isPlaneswalker) then
      (g.logMsg "You control a planeswalker. The ability does nothing", false)
    else (g, true)
  | .otherForestsAtLeast n =>
    -- Rulings 818 / 819: count Forests other than the one that caused the
    -- trigger, whether or not that one is still on the battlefield.
    let cause : Option ObjectId := lastKnownPower.map (fun k => ⟨k.toNat⟩)
    let others := ((g.permanentsOf controller).filter (fun o =>
      g.hasSubtype o "Forest" && some o.id != cause)).size
    if others < n then
      let g :=
        if n == 5 then
          g.logMsg "You control fewer than five other Forests. The ability doesn't resolve"
        else g
      (g, false)
    else (g, true)
  | .returnedPermanent =>
    let returned := g.returnedPermanentThisWay
    ({ g with returnedPermanentThisWay := false }, returned)
  | .nthResolve n => (g, g.nthResolveThisWay == some n)
  | .youControlledDestroyed =>
    let draw? := g.destroyedForAmassThisWay && g.amassYouControlledThisWay
    let g := { g with
      destroyedForAmassThisWay := false
      amassControllerThisWay := none
      amassAmountThisWay := 0
      amassYouControlledThisWay := false }
    (g, draw?)
  | .enduringStoryNoted =>
    match g.handDiscardedThisWay with
    | none => ({ g with notedSourceThisWay := none }, false)
    | some n =>
      let srcId := g.notedSourceThisWay
      let holds :=
        g.hasEnduringStory controller && n != 0 &&
          (srcId.bind g.findObject?).any (·.isOnBattlefield)
      if holds then (g, true)
      else ({ g with handDiscardedThisWay := none, notedSourceThisWay := none }, false)
  | .bearsAtLeast n => (g, g.countSubtype controller "Bear" ≥ n)
  | .controlsAtLeast subtype n => (g, g.countSubtype controller subtype ≥ n)
  | .sourceWasSacrificed =>
    let yes := g.sourceWasSacrificed
    ({ g with sourceWasSacrificed := false }, yes)
  | .planWasSacrificed =>
    let yes := g.planWasSacrificed
    ({ g with planWasSacrificed := false }, yes)
  | .questAtLeast n =>
    match sourceId.bind g.findObject? with
    | none => (g.logMsg "The triggered ability's source is no longer in play", false)
    | some src =>
      if src.isOnBattlefield then (g, src.status.quest ≥ n)
      else (g.logMsg s!"{src.name} is no longer on the battlefield", false)
  | .equipmentAttached =>
    match g.equipmentAttachedHost with
    | none => (g, false)
    | some hostId =>
      match g.findObject? hostId with
      | some host =>
        if host.isOnBattlefield then (g, true)
        else ({ g with equipmentAttachedHost := none }, false)
      | none => ({ g with equipmentAttachedHost := none }, false)
  | .opponentsMilled =>
    let milled := g.opponentsMilledThisWay
    ({ g with opponentsMilledThisWay := false }, milled)
  | .anotherHero =>
    (g, (g.permanentsOf controller).any (fun o =>
      g.hasSubtype o "Hero" && some o.id != sourceId))
  | .libraryEmpty => (g, (g.player controller).library.isEmpty)
  | .libraryNotEmpty => (g, !(g.player controller).library.isEmpty)
  | .equippedLegendaryYouControl =>
    match sourceId.bind g.findObject? with
    | none => (g.logMsg "The Equipment is no longer in play", false)
    | some eq =>
      let hostOk :=
        match eq.attachedTo.bind g.findObject? with
        | some host =>
          host.isOnBattlefield && host.isLegendary && host.controller == some controller
        | none => false
      if hostOk then (g, true)
      else
        (g.logMsg s!"{(g.player controller).name} creates two tapped Spirit tokens", false)
  | .targetIsCreature =>
    let (g, o?) := g.legalTriggerPermanent? controller ab sourceId targets
    match o? with
    | some o => (g, o.isCreature)
    | none => (g, false)
  | .targetIsPlaneswalker =>
    let (g, o?) := g.legalTriggerPermanent? controller ab sourceId targets
    match o? with
    | some o => (g, o.printed.isPlaneswalker)
    | none => (g, false)
  | .creatureCardsInGraveyardAtLeast n =>
    let gy := ((g.player controller).graveyard.filter (fun id =>
      (g.object! id).printed.isCreature)).size
    (g, gy ≥ n)
  | .targetIsAnotherSubtype subtype =>
    let legal := g.legalTargetsForKind controller ab.targetKind sourceId
    let holds :=
      match targets[0]? with
      | some (Target.permanent oid) =>
        legal.contains (Target.permanent oid) &&
          match g.findObject? oid with
          | some o => g.hasSubtype o subtype && some o.id != sourceId
          | none => false
      | _ => false
    (g, holds)
  | .scriedOrSurveilledThisTurn =>
    (g, (g.player controller).scriedOrSurveilledThisTurn)
  | .putArtifactIsEquipment =>
    match g.putArtifactThisWay with
    | none => (g, false)
    | some (id, _) =>
      match g.findObject? id with
      | some o =>
        if o.printed.isEquipment then (g, true)
        else ({ g with putArtifactThisWay := none }, false)
      | none => ({ g with putArtifactThisWay := none }, false)
  | .revealedManaValueAtMostLands => (g, false)
  | .sourceHarnessed =>
    match sourceId.bind g.findObject? with
    | none => (g, false)
    | some src =>
      if src.status.harnessed then (g, true)
      else (g.logMsg "The Mind Stone is not harnessed", false)
  | .artifactEnteredThisTurn =>
    if (g.player controller).artifactEnteredThisTurn then (g, true)
    else
      (g.logMsg
        "No artifact entered under your control this turn. Iron Man's ability doesn't trigger.",
        false)
  | .sourcePowerAtLeast n =>
    let pw := g.sourcePowerAtResolution sourceId lastKnownPower
    if pw ≥ Int.ofNat n then (g, true)
    else
      let g :=
        if n == 4 then g.logMsg "Viv Vision's power is not 4 or greater"
        else g.logMsg s!"Its power is not {n} or greater"
      (g, false)
  | .attachedEquipment =>
    let x := g.attachedEquipmentAtResolution sourceId lastKnownPower
    if x == 0 then (g.logMsg "Whiplash isn't equipped", false)
    else (g, true)
  | .sourceAttacking =>
    match sourceId.bind g.findObject? with
    | some o => (g, o.isOnBattlefield && o.status.attacking)
    | none => (g, false)
  | .enrageGrantsCombat =>
    if g.enrageGrantsAdditionalCombat > 0 then
      ({ g with enrageGrantsAdditionalCombat := g.enrageGrantsAdditionalCombat - 1 }, true)
    else (g, false)
  | .causeGreaterPowerOrToughness =>
    match sourceId.bind g.findObject? with
    | none => (g.logMsg "The source is no longer in play", false)
    | some hulkling =>
      if !hulkling.isOnBattlefield then
        (g.logMsg s!"{hulkling.name} is no longer on the battlefield", false)
      else
        let entered :=
          match targets[0]? with
          | some (Target.permanent id) | some (Target.card id) => g.findObject? id
          | _ => (g.resolvingCauseId).bind g.findObject?
        match entered with
        | none => (g, false)
        | some other =>
          if other.id == hulkling.id then (g, false)
          else
            let op :=
              if other.isOnBattlefield then g.power other
              else other.lastKnownPower.getD (g.power other)
            let ot :=
              if other.isOnBattlefield then g.toughness other
              else other.lastKnownToughness.getD (g.toughness other)
            (g, op > g.power hulkling || ot > g.toughness hulkling)
  | .manaSpent =>
    let spent :=
      ((g.resolvingAbilityObject?.bind (·.fraCauseStatus)).map (·.manaSpentToCast)).getD 0
    (g, spent > 0)

/-- Log line when a `TriggerResolution.or` asks the controller to choose. -/
def triggerOrLog (name : String) (rs : List TriggeredAbility.TriggerResolution) : String :=
  match rs with
  | [.createTokens .food 1 false, .createTokens .treasure 1 false] =>
    s!"{name} creates a Food token or a Treasure token"
  | [.tap .target, .untap .target] =>
    s!"{name} chooses tap or untap"
  | _ =>
    s!"{name} chooses one"

/-- Pending-header text for a `TriggerResolution.or` choice. -/
def triggerOrPendingText (rs : List TriggeredAbility.TriggerResolution) : String :=
  match rs with
  | [.createTokens .food 1 false, .createTokens .treasure 1 false] =>
    "create a Food token or a Treasure token"
  | [.tap .target, .untap .target] =>
    "choose tap or untap"
  | _ =>
    "choose one"

/-- The optional action of `mayThen` cannot be performed. Skip the conditional
steps still in this sequence. -/
def failMayThen (g : Game) : Game :=
  { g with mayThenSkip := g.mayThenDrop, mayThenDrop := 0, mayThenConditional := none }

/-- Offer to pay {2} to copy the nontoken artifact that caused this trigger.
An announced permanent is used when one was chosen; otherwise the recorded
cause. A token, a nonartifact, or the source itself skips the copy. -/
def offerCopyCause (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (targets : Array Target) : Game :=
  let fromTarget :=
    match targets[0]? with
    | some (Target.permanent id) => some id
    | _ => none
  match fromTarget.orElse (fun _ => g.resolvingCauseId) with
  | none => (g.logMsg "Ultron has nothing to copy").failMayThen
  | some id =>
    match g.findObject? (g.followMoved id) with
    | some src =>
      if src.printed.isToken || !src.printed.isArtifact || some src.id == sourceId then
        (g.logMsg "That permanent isn't another nontoken artifact").failMayThen
      else
        { g with pending := .fraChoice controller (.ultronMayPay id) }
          |>.logMsg s!"{(g.player controller).name} may pay {2} to copy {src.name}"
    | none => (g.logMsg "Ultron has nothing to copy").failMayThen

/-- Apply `f` to the permanent `who` names.
`.target` is the announced permanent, and an illegal target is reported.
`.source` requires the source still on the battlefield.
`.enchanted` is the creature the source enchants; nothing enchanted is silent.
`.targetWhileSource` is silent when the source has already left. -/
def withAffected (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (who : TriggeredAbility.TriggerAffected)
    (f : Game → GameObject → Game) : Game :=
  match who with
  | .target =>
    g.withLegalTriggerPermanent controller ab sourceId targets f
      "The target is no longer legal"
  | .source =>
    g.withTriggerSource sourceId f
  | .enchanted =>
    g.withSourceOnBattlefield sourceId (fun g src =>
      match src.attachedTo.bind g.findObject? with
      | some host => f g host
      | none => g) "The Aura is no longer in play"
  | .targetWhileSource =>
    match sourceId.bind g.findObject? with
    | some src =>
      if !src.isOnBattlefield then g
      else
        g.withLegalKindPermanent controller ab.targetKind targets
          (fun g host => f g (g.object! host.id))
          sourceId (some "The target is no longer legal")
    | none => g

/-- Put `n` counters of `kind` on the permanent `who` names.
`+1/+1`, and a single indestructible, double strike, or burden counter, go
through `applyPermanentAction`. Other counts use the same bodies as the
announced-permanent arms. -/
def applyAffectedCounters (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (kind : CounterKind) (n : Nat) (who : TriggeredAbility.TriggerAffected) : Game :=
  g.withAffected controller ab sourceId targets who fun g o =>
    match kind with
    | .plusOnePlusOne => g.applyPermanentAction o (.plusOne n)
    | .indestructible =>
      if n == 1 then g.applyPermanentAction o .indestructibleCounter
      else g.addIndestructibleCounter o n
    | .doubleStrike =>
      if n == 1 then g.applyPermanentAction o .doubleStrikeCounter
      else
        let g := g.mapObjectStatus o (fun s => { s with keywordCounters :=
          { s.keywordCounters with doubleStrike := s.keywordCounters.doubleStrike + n } })
        g.logMsg s!"{o.name} gets {n} double strike counters"
    | .burden =>
      if n == 1 then g.applyPermanentAction o .burdenCounter
      else g.addBurdenCounter o n
    | .stun =>
      let k := g.countersYouPut o n
      let g := g.mapObjectStatus o (fun s => { s with stun := s.stun + k })
      let phrase :=
        if n == 1 then "A stun counter is put" else s!"{k} stun counters are put"
      g.logMsg s!"{phrase} on {o.name}"
    | _ => g

/-- Resolve `TriggerResolution.pump`. `power` and `toughness` are read
separately, then applied to each permanent `who` names. -/
def applyTriggerPump (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (lastKnownPower lastKnownToughness : Option Int)
    (power toughness : TriggeredAbility.NumberSelector)
    (who : TriggeredAbility.ObjectSelector) : Game :=
  let shared (amount : TriggeredAbility.NumberSelector) : Option Int :=
    match amount with
    | .fixed n => some n
    | .greatestPower => some (g.greatestPowerAmongCreatures controller)
    | .perLookedAt => some (lastKnownPower.getD 0).toNat
    | .perOtherCreature =>
      some (g.battlefield.filter (fun c =>
        c.isCreature && c.controlledBy controller && some c.id != sourceId)).size
    | .perPlains => some (g.countSubtype controller "Plains")
    | .equalSourcePower => some (g.sourcePowerAtResolution sourceId lastKnownPower)
    | .equalSourceToughness =>
      some <|
        match sourceId.bind g.findObject? with
        | some src =>
          if src.isOnBattlefield then g.toughness src
          else lastKnownToughness.getD (g.toughness src)
        | none => lastKnownToughness.getD 0
    | .double => none
    | _ => some 0
  let powerShared := shared power
  let toughnessShared := shared toughness
  let pumpOne (game : Game) (o : GameObject) : Game :=
    game.pumpPermanent o (powerShared.getD (game.power o))
      (toughnessShared.getD (game.toughness o))
  match who with
  | .source =>
    g.withAffected controller ab sourceId targets .source pumpOne
  | .target =>
    let missing :=
      match power, toughness with
      | .perPlains, .perPlains => "No target was chosen"
      | _, _ => "The target is no longer legal"
    g.withLegalTriggerPermanent controller ab sourceId targets pumpOne missing
  | .enchanted =>
    g.withAffected controller ab sourceId targets .enchanted pumpOne
  | .targetWhileSource =>
    g.withAffected controller ab sourceId targets .targetWhileSource pumpOne
  | .cause =>
    match g.battlefield.find? (fun o => o.status.attacking && o.controlledBy controller) with
    | some o => pumpOne g o
    | none => g
  | .creaturesYouControl =>
    g.forEachControlledCreature controller pumpOne
  | .othersOfSubtypes subtypes =>
    g.foldBattlefield (fun o =>
        o.isCreature && o.controlledBy controller && some o.id != sourceId &&
          subtypes.any (fun s => g.hasSubtype o s))
      pumpOne
  | .othersOfSubtype subtype =>
    let srcId? := (sourceId.bind g.findObject?).map (·.id)
    g.foldBattlefield (fun o =>
        o.controlledBy controller &&
          (match srcId? with
           | some sid => o.id != sid
           | none => true) &&
          g.hasSubtype o subtype)
      pumpOne
  | .opponentsCreatures =>
    g.foldBattlefield (fun o => o.isCreature && !o.controlledBy controller) pumpOne
  | .youControlSubtype subtype =>
    g.forEachControlledCreature controller fun game o =>
      if game.hasSubtype o subtype then pumpOne game o else game
  | _ => g

/-- Resolve `TriggerResolution.dealDamage`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyTriggerDamage (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (lastKnownPower : Option Int) (sourceName : String)
    (amount : TriggeredAbility.NumberSelector)
    (who : TriggeredAbility.ObjectSelector)
    (note : TriggeredAbility.TriggerDamageNote) : Game :=
  match who, amount, note with
  | .blockers, .fixed n, _ =>
    let n := n.toNat
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
  | .permanent, .lastKnownPower, .excess =>
    let amt := lastKnownPower.getD 0
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let remain := g.toughness o - o.status.damage
      let raw := amt - remain
      let excess : Nat := if raw > 0 then raw.toNat else 0
      let g := { g with excessDamageThisWay := excess }
      g.dealDamageFrom sourceName o amt (source := sourceId.bind g.findObject?))
      "The target is no longer legal"
  | .permanent, .lastKnownPower, _ =>
    let amt := (lastKnownPower.getD 0).toNat
    g.withLegalTriggerPermanent controller ab sourceId targets fun g o =>
      g.dealDamageFrom sourceName o amt (source := sourceId.bind g.findObject?)
  | .player .eachOpponent, .fixed n, .fromEquipped =>
    let n := n.toNat
    let src :=
      match g.attachedHost? sourceId with
      | some host => some host
      | none => none
    g.forEachOpponent controller (fun g pid =>
      g.dealDamageToPlayer pid n (source := src))
  | .player .eachOpponent, .fixed n, _ =>
    let n := n.toNat
    let src := sourceId.bind g.findObject?
    if ab.opts.untargeted || !ab.requiresTarget then
      g.forEachOpponent controller (fun g pid =>
        g.dealDamageToPlayer pid n (source := src))
    else
      g.withLegalTriggerPlayer controller ab sourceId targets (fun g pid =>
        g.dealDamageToPlayer pid n (source := src))
  | .player .eachOpponent, .subtypeCount subtype, _ =>
    let amt := g.countSubtype controller subtype
    let src := sourceId.bind g.findObject?
    g.forEachOpponent controller (fun g pid =>
      g.dealDamageToPlayer pid amt (source := src))
  | .player .eachOpponent, .discardedHand, _ =>
    match g.handDiscardedThisWay with
    | none => { g with notedSourceThisWay := none }
    | some discarded =>
      let srcId := g.notedSourceThisWay
      let g := { g with handDiscardedThisWay := none, notedSourceThisWay := none }
      if !g.hasEnduringStory controller || discarded == 0 then g
      else
        match srcId.bind g.findObject? with
        | some src =>
          if src.isOnBattlefield then
            g.forEachOpponent controller (fun g pid =>
              g.dealDamageToPlayer pid (discarded : Int) (source := some src))
          else g
        | none => g
  | .target, .subtypeCount subtype, _ =>
    let amt := g.countSubtype controller subtype
    g.applyEffect controller (Effect.dealDamage amt) targets
  | .target, .fixed n, .markedPermanent =>
    let n := n.toNat
    let g := { g with permanentDealtDamageThisWay := none }
    g.withLegalKindTarget controller ab.targetKind targets (fun g tgt =>
      match tgt with
      | Target.player _ =>
        g.applyEffect controller (Effect.dealDamage n) #[tgt]
      | Target.permanent oid =>
        match g.findObject? oid with
        | none => g.logMsg "The target is no longer legal"
        | some o =>
          let before := o.status.damage
          let g := g.applyEffect controller (Effect.dealDamage n) #[tgt]
          let marked :=
            match g.findObject? oid with
            | some o => o.isOnBattlefield && o.status.damage > before
            | none => false
          if marked then { g with permanentDealtDamageThisWay := some oid } else g
      | _ => g.logMsg "The target is no longer legal")
  | .player .targetOpponent, .greatestArtifactMv, _ =>
    let x := g.greatestManaValueAmong controller (·.printed.isArtifact)
    g.withLegalTriggerPlayer controller ab sourceId targets (fun g pid =>
      g.dealDamageToPlayer pid x)
  | .eachNonSubtypeAndOpponents subtype, .fixed n, _ =>
    let n := n.toNat
    let g :=
      g.dealDamageToEachCreatureMatching n (fun o => !g.hasSubtype o subtype)
    g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid n)
  | .player .targetOpponent, .fixed n, _ =>
    let n := n.toNat
    g.withLegalTriggerPlayer controller ab sourceId targets (fun g pid =>
      g.dealDamageToPlayer pid n)
  | .target, .fixed n, .none =>
    let n := n.toNat
    g.applyDamageToKindTarget controller ab.targetKind targets n sourceId
      (some "The target is no longer legal")
  | .target, .spellManaValue, _ =>
    let n := g.castSpellManaValue controller lastKnownPower
    g.applyDamageToKindTarget controller ab.targetKind targets n sourceId none
  | .source, .fixed n, _ =>
    let n := n.toNat
    g.withAffected controller ab sourceId targets .source fun g o =>
      g.applyPermanentAction o (.dealDamage n)
  | .enchanted, .fixed n, _ =>
    let n := n.toNat
    g.withAffected controller ab sourceId targets .enchanted fun g o =>
      g.applyPermanentAction o (.dealDamage n)
  | .targetWhileSource, .fixed n, _ =>
    let n := n.toNat
    g.withAffected controller ab sourceId targets .targetWhileSource fun g o =>
      g.applyPermanentAction o (.dealDamage n)
  | _, _, _ => g

/-- Put one keyword counter on `src` when `other` has that keyword and `src`
does not. -/
def copyKeywordCounter (g : Game) (src other : GameObject)
    (has : GameObject → Bool) (apply : Status → Status) (name : String) : Game :=
  if has other && !has src then
    let n := g.countersYouPut src 1
    let src := g.object! src.id
    let status := Id.run do
      let mut s := src.status
      for _ in [0:n] do
        s := apply s
      return s
    g.setObject { src with status := status }
      |>.logMsg s!"{src.name} gets a {name} counter"
  else g

/-- Put a counter on `src` for each keyword `other` has that `src` does not.
Haste, flying, first strike, double strike, deathtouch, indestructible,
lifelink, menace, reach, trample, and vigilance. -/
def copyMissingKeywordCounters (g : Game) (src other : GameObject) : Game :=
  let g := g.copyKeywordCounter src other g.hasHaste
    (fun s => { s with keywordCounters :=
      { s.keywordCounters with haste := s.keywordCounters.haste + 1 } }) "haste"
  let src := g.object! src.id
  let g := g.copyKeywordCounter src other g.hasFlying
    (fun s => { s with keywordCounters :=
      { s.keywordCounters with flying := s.keywordCounters.flying + 1 } }) "flying"
  let src := g.object! src.id
  let g := g.copyKeywordCounter src other
    (fun o => g.hasKeyword o (·.firstStrike))
    (fun s => { s with keywordCounters :=
      { s.keywordCounters with
        firstStrike := s.keywordCounters.firstStrike + 1 } }) "first strike"
  let src := g.object! src.id
  let g := g.copyKeywordCounter src other g.hasDoubleStrike
    (fun s => { s with keywordCounters :=
      { s.keywordCounters with
        doubleStrike := s.keywordCounters.doubleStrike + 1 } }) "double strike"
  let src := g.object! src.id
  let g := g.copyKeywordCounter src other g.hasDeathtouch
    (fun s => { s with keywordCounters :=
      { s.keywordCounters with
        deathtouch := s.keywordCounters.deathtouch + 1 } }) "deathtouch"
  let src := g.object! src.id
  let g := g.copyKeywordCounter src other g.hasIndestructible
    (fun s => { s with
      indestructibleCounters := s.indestructibleCounters + 1 }) "indestructible"
  let src := g.object! src.id
  let g := g.copyKeywordCounter src other g.hasLifelink
    (fun s => { s with lifelinkCounters := s.lifelinkCounters + 1 }) "lifelink"
  let src := g.object! src.id
  let g := g.copyKeywordCounter src other g.hasMenace
    (fun s => { s with keywordCounters :=
      { s.keywordCounters with menace := s.keywordCounters.menace + 1 } }) "menace"
  let src := g.object! src.id
  let g := g.copyKeywordCounter src other (fun o => g.hasKeyword o (·.reach))
    (fun s => { s with keywordCounters :=
      { s.keywordCounters with reach := s.keywordCounters.reach + 1 } }) "reach"
  let src := g.object! src.id
  let g := g.copyKeywordCounter src other g.hasTrample
    (fun s => { s with trampleCounters := s.trampleCounters + 1 }) "trample"
  let src := g.object! src.id
  g.copyKeywordCounter src other g.hasVigilance
    (fun s => { s with keywordCounters :=
      { s.keywordCounters with
        vigilance := s.keywordCounters.vigilance + 1 } }) "vigilance"

/-- Resolve `TriggerResolution.putCounters`. Each printed combination keeps
the behavior of the constructor it replaced. Any other selector puts nothing. -/
def applyPutCounters (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (lastKnownPower : Option Int)
    (what : TriggeredAbility.CounterSelector)
    (who : TriggeredAbility.ObjectSelector) : Game :=
  match what, who with
  | .ofKind .plusOnePlusOne _, .youControl which =>
    match which with
    | .eachCreature =>
      g.forEachControlledCreature controller (fun g o => g.addPlusOnePlusOneTo o 1)
    | .subtype s =>
      (g.permanentsOf controller).foldl (fun g o =>
        if g.hasSubtype o s then g.addPlusOnePlusOneTo (g.object! o.id) 1 else g) g
    | .citysBlessing =>
      let n := if (g.player controller).citysBlessing then 2 else 1
      (g.permanentsOf controller).foldl (fun acc o =>
        if o.isCreature then acc.addPlusOnePlusOneTo o n else acc) g
  | .ofKind .plusOnePlusOne _, .eachOther =>
    (g.creaturesControlledBy controller).foldl (fun acc o =>
      if some o.id != sourceId then acc.addPlusOnePlusOneTo o 1 else acc) g
  | .plusOneLastKnownMv, .permanent _ =>
    let n := (lastKnownPower.getD 0).toNat
    g.applyOnPermanent controller ab.targetKind targets (.plusOne n) sourceId
      (some "The target is no longer legal")
  | .ofKind .loyalty _, .source =>
    g.withSourceOnBattlefield sourceId (fun g o =>
      let n := g.countersYouPut o 1 (putter := some controller)
      let g := g.mapObjectStatus o (fun s => { s with loyaltyCounters := s.loyaltyCounters + n })
      let g := g.queueLoyaltyPutTriggers controller
      g.logMsg s!"A loyalty counter is put on {o.name}")
  | .sourceCounters, .permanent _ =>
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
  | .ofKind .charge _, .source =>
    g.withSourceOnBattlefield sourceId (fun g o =>
      let n := g.countersYouPut o 1 (putter := some controller)
      let g := g.mapObjectStatus o (fun s => { s with charge := s.charge + n })
      g.logMsg s!"A charge counter is put on {o.name}")
  | .ofKind .quest _, .source =>
    g.withTriggerSource sourceId fun g src =>
      let n := g.countersYouPut src 1 (putter := some controller)
      let g := g.setObject { src with status :=
        { src.status with quest := src.status.quest + n } }
      let src := g.object! src.id
      g.logMsg s!"{src.name} gets a quest counter ({src.status.quest})"
  | .honePerOpponent, .source =>
    let opp :=
      match targets[0]? with
      | some (Target.player pid) => pid
      | some (Target.permanent _) => g.opponent controller
      | _ => g.opponent controller
    let n := g.countCreaturesControlledBy opp
    g.withTriggerSource sourceId fun g src =>
      let k := g.countersYouPut src n (putter := some controller)
      g.mapObjectStatus src (fun s => { s with hone := s.hone + k })
        |>.logMsg s!"{src.name} gets {k} hone counter(s)"
  | .ofKind .plan _, .source =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield then
        g.incrementPlanThen controller sourceId (fun g _ => g)
      else
        { g with skipTriggerSequenceRest := true }.logMsg
          s!"{o.name} is no longer on the battlefield"
    | none =>
      { g with skipTriggerSequenceRest := true }.logMsg
        "The ability's source is no longer in play"
  | .ofKind .plusOnePlusOne _, .permanent true =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      g.addPlusOnePlusOneTo o 1 (byPlayer := some controller))
      "The target is no longer legal. You won't put counters on anything."
  | .plusOneNoted, .createdToken =>
    let n := g.notedCountThisWay
    let id? := g.createdTokenThisWay
    let g := { g with createdTokenThisWay := none }
    if n == 0 then g
    else
      match id?.bind g.findObject? with
      | some o => g.addPlusOnePlusOneTo o n
      | none => g
  | .ofKind .invasion _, .source =>
    let g := { g with notedCountThisWay := 0 }
    g.withSourceOnBattlefield sourceId (fun g src =>
      let n := g.countersYouPut src 1 (putter := some controller)
      g.mapObjectStatus src (fun s => { s with invasion := s.invasion + n })
        |>.logMsg s!"{src.name} gets an invasion counter")
      "The source is no longer in play"
  | .ofKind .trample _, .permanent _ =>
    match targets[0]? with
    | some (Target.permanent oid) =>
      match g.findObject? oid with
      | some o =>
        let n := g.countersYouPut o 1 (putter := some controller)
        let g := g.setObject { o with status :=
          { o.status with trampleCounters := o.status.trampleCounters + n } }
        if n == 0 then g else g.logMsg s!"{o.name} gets a trample counter"
      | none => g
    | _ => g
  | .ofKind .influence _, .source =>
    let g := { g with palantirChoiceReady := none }
    let tgt :=
      match targets[0]? with
      | some (Target.player pid) => some pid
      | _ => none
    match sourceId with
    | none =>
      { g with skipTriggerSequenceRest := true }.logMsg
        "The source is no longer in play"
    | some sid =>
      let (g, ok) := g.putPalantirInfluence sid tgt
      match ok with
      | none => { g with skipTriggerSequenceRest := true }
      | some increased =>
        match tgt with
        | some opp =>
          if increased then
            { g with palantirChoiceReady := some (controller, opp, sid) }
          else g
        | none => g
  | .ofKind .loyalty _, .permanent _ =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let n := g.countersYouPut o 1 (putter := some controller)
      let g := g.mapObjectStatus o (fun s => { s with loyaltyCounters := s.loyaltyCounters + n })
      let g := g.queueLoyaltyPutTriggers controller
      g.logMsg s!"A loyalty counter is put on {o.name}")
  | .plusOneSacrificedPower, .source =>
    let n := g.sacrificedPowerThisWay.getD 0
    let g := { g with sacrificedPowerThisWay := none }
    match sourceId.bind g.findObject? with
    | some src => if src.isOnBattlefield then g.addPlusOnePlusOneTo src n else g
    | none => g
  | .ofKind .plusOnePlusOne n, .permanent false =>
    if targets.isEmpty && ab.allowsZeroTargets then g
    else
      g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
        g.addPlusOnePlusOneTo o n)
        "The target is no longer legal"
  | .ofKind .indestructible n, .permanent false =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      g.addIndestructibleCounter o n)
      "The target is no longer legal"
  | .ofKind .doubleStrike n, .permanent false =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let g := g.mapObjectStatus o (fun s => { s with keywordCounters :=
        { s.keywordCounters with doubleStrike := s.keywordCounters.doubleStrike + n } })
      let phrase :=
        if n == 1 then "a double strike counter" else s!"{n} double strike counters"
      g.logMsg s!"{o.name} gets {phrase}")
      "The target is no longer legal"
  | .ofKind .burden n, .permanent false =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      g.addBurdenCounter o n)
      "The target is no longer legal"
  | .ofKind .stun n, .permanent false =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let k := g.countersYouPut o n
      let g := g.mapObjectStatus o (fun s => { s with stun := s.stun + k })
      let phrase :=
        if n == 1 then "A stun counter is put" else s!"{k} stun counters are put"
      g.logMsg s!"{phrase} on {o.name}")
      "The target is no longer legal"
  | .ofKind kind n, .source =>
    g.applyAffectedCounters controller ab sourceId targets kind n .source
  | .ofKind kind n, .enchanted =>
    g.applyAffectedCounters controller ab sourceId targets kind n .enchanted
  | .ofKind kind n, .targetWhileSource =>
    g.applyAffectedCounters controller ab sourceId targets kind n .targetWhileSource
  | .ofKind .plusOnePlusOne n, .sourceIfPresent =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield then g.addPlusOnePlusOneTo o n
      else g.logMsg s!"{o.name} is no longer on the battlefield. No counter is put."
    | none =>
      g.logMsg "The source is no longer on the battlefield. No counter is put."
  | .ofKind .plusOnePlusOne _, .eachUpToLastKnown =>
    g.putPlusOnesUpToLastKnown controller targets lastKnownPower
  | .missingKeywordsFromTarget, .source =>
    g.withSourceOnBattlefield sourceId (fun g src =>
      match targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some other =>
          if !other.isOnBattlefield || !other.isCreature || other.id == src.id then
            g.logMsg "The target is no longer legal"
          else
            g.copyMissingKeywordCounters src other
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "The target is no longer legal")
      "The source is no longer in play"
  | _, _ => g

/-- Resolve `TriggerResolution.createTokens`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyCreateTokens (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (targets : Array Target)
    (lastKnownPower : Option Int) (kind : TokenKind) (n : Nat) (tapped : Bool)
    (token : TriggeredAbility.TriggerToken)
    (who : TriggeredAbility.TriggerTokenWho)
    (qty : TriggeredAbility.TriggerTokenQty)
    (note : TriggeredAbility.TriggerTokenNote) : Game :=
  match token, who, qty, note with
  | .axe, _, _, .attachReflexive =>
    let (g, tok) := g.createToken controller axeToken
    g.putReflexiveTrigger controller (some tok.id) {
      targeting := .of .creatureYouControl
      resolution := .attach
      phrase := "Attach it to target creature you control" }
  | .axe, _, _, _ =>
    let (g, _) := g.createToken controller axeToken
    g.logMsg "An Axe token is created"
  | .kind, .you, .oppArtifacts, _ =>
    let n := g.countOpponentArtifacts controller
    g.createTreasureTokens controller n (tapped := true)
  | .kind, .you, .damagedPlayerArtifacts, _ =>
    let pid := g.lastCombatDamagePlayer.getD (g.opponent controller)
    let n := g.countArtifactsControlledBy pid
    g.createTreasureTokens controller n |>.logMsg
      s!"{(g.player controller).name} creates {n} Treasure token(s) (artifacts that player controls)"
  | .kind, .you, .lastKnown, _ =>
    if kind == .birdSoldier then
      let n := lastKnownPower.getD 0
      g.createKindTokens controller .birdSoldier n.toNat |>.logMsg
        s!"{(g.player controller).name} creates {n} Bird Soldier token(s)"
    else
      let n := (lastKnownPower.getD 0).toNat
      g.createTreasureTokens controller n
  | .kind, .you, .perSubtype subtype, _ =>
    g.createKindTokens controller kind (g.countSubtype controller subtype) (tapped := tapped)
  | .kind, .you, .chosenCreatureType, _ =>
    let types := (g.creaturesControlledBy controller).foldl (fun acc o =>
      o.subtypes.foldl (fun acc t => if acc.contains t then acc else acc.push t) acc) #[]
    if types.isEmpty then
      g.logMsg s!"{(g.player controller).name} controls no creatures, so no Treasures are created"
    else
      g.beginFraChoice controller (.chooseCreatureType types)
        s!"{(g.player controller).name} chooses a creature type"
  | .zabu, _, _, _ =>
    g.createNamedToken controller zabuToken
  | .theVoid, _, _, _ =>
    match targets[0]? with
    | some (Target.player pid) => g.createNamedToken pid theVoidToken
    | _ => g.createNamedToken controller theVoidToken
  | .redwing, _, _, _ =>
    g.createNamedToken controller redwingToken
  | .alien, _, _, _ =>
    let n :=
      match sourceId.bind g.findObject? with
      | some src => src.status.invasion
      | none => 0
    let (g, tok) := g.createToken controller alien11redHasteToken
    { g with notedCountThisWay := n, createdTokenThisWay := some tok.id }
  | .galactus, _, _, _ =>
    g.createNamedToken controller galactusToken
  | .sturdyShield, _, _, _ =>
    let (g, shield) := g.createToken controller sturdyShieldToken
    { g with createdTokenThisWay := some shield.id }
  | .merfolk, _, _, _ =>
    g.createMerfolkForBlueSymbols controller lastKnownPower
  | .kind, .targetController, _, _ =>
    -- Destroy may already have moved the permanent. The controller who
    -- creates the Treasure is the one it had on the battlefield.
    match targets[0]? with
    | some (Target.permanent oid) =>
      match g.findObject? (g.followMoved oid) with
      | some o =>
        let pid := (o.controller.orElse (fun _ => o.lastController)).getD o.owner
        g.createTreasureTokens pid 1
      | none => g
    | _ => g
  | _, _, _, _ =>
    g.createKindTokens controller kind n (tapped := tapped)

/-- Resolve `TriggerResolution.exile`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyExile (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (what : TriggeredAbility.TriggerExileWhat)
    (how : TriggeredAbility.TriggerExileHow)
    (note : TriggeredAbility.TriggerExileNote) : Game :=
  match what, how, note with
  | .target, .leaveTrigger, .none =>
    g.withLegalKindPermanent controller ab.targetKind targets (fun g o =>
      g.exileForLeaveTrigger sourceId o) sourceId (some "The target is no longer legal")
  | .target, .untilSourceLeaves, .copyAndHost =>
    let g := { g with notedCopyObject := none, notedHostId := none }
    g.withSourceStillOnBattlefield sourceId fun g src =>
      match targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some tgt =>
          let hostId := src.attachedTo
          let g := g.exileUntilSourceLeaves sourceId tgt
          { g with notedCopyObject := some tgt, notedHostId := hostId }
        | none => g.logMsg "The target is no longer legal"
      | _ => g
  | .target, .untilSourceLeaves, .none =>
    g.withSourceStillOnBattlefield sourceId fun g _ =>
      g.withLegalKindPermanent controller ab.targetKind targets (fun g o =>
        g.exileUntilSourceLeaves sourceId o) sourceId (some "The target is no longer legal")
  | .top, .playUntilNextTurn, .none =>
    g.resolveExileTopPlayUntilEndOfNextTurn controller
  | .eachTarget, .untilSourceLeaves, .none =>
    g.withSourceStillOnBattlefield sourceId fun g _ =>
      targets.foldl (fun acc t =>
        match t with
        | Target.permanent oid =>
          match acc.findObject? oid with
          | some o => acc.exileUntilSourceLeaves sourceId o
          | none => acc
        | _ => acc) g
  | .landsYouControl, .forLater, .lands =>
    let g := { g with exiledIdsThisWay := #[] }
    g.foldPermanentTargets targets (fun g o =>
      if o.controlledBy controller && o.printed.isLand then
        let (g, newId) := g.move o.id .exile none
        { g with exiledIdsThisWay := g.exiledIdsThisWay.push newId }
      else g)
  | .target, .nextEndStep, .none =>
    g.withLegalKindPermanent controller ab.targetKind targets (fun g o =>
      g.exileUntilNextEndStep o) sourceId none
  | .graveyardCard, .forLater, .playCard =>
    let g := { g with playExiledThisWay := none }
    g.withLegalKindTarget controller ab.targetKind targets (fun g tgt =>
      match tgt with
      | Target.card id | Target.permanent id =>
        match g.findObject? id with
        | some o =>
          let (g, newId) := g.move o.id .exile none
          { g with playExiledThisWay := some newId }
        | none => g.logMsg "The target is no longer in the graveyard"
      | _ => g) sourceId (some "The target is no longer legal")
  | .target, .forLater, .none =>
    g.withLegalKindPermanent controller ab.targetKind targets (fun g o =>
      (g.move o.id .exile none).1) sourceId (some "The target is no longer legal")
  | .source, .forLater, .none =>
    g.withAffected controller ab sourceId targets .source fun g o =>
      g.applyPermanentAction o .exile
  | .enchanted, .forLater, .none =>
    g.withAffected controller ab sourceId targets .enchanted fun g o =>
      g.applyPermanentAction o .exile
  | .targetWhileSource, .forLater, .none =>
    g.withAffected controller ab sourceId targets .targetWhileSource fun g o =>
      g.applyPermanentAction o .exile
  | .basicUpTo subtype max, .forLater, .linked =>
    g.beginLibrarySearch controller
      (fun c => isBasicLandCard c && c.hasSubtype subtype)
      s!"a basic {subtype} card" (.exileLinked sourceId) (count := max)
  | .target, .returnImmediately, .none =>
    g.flickerChosenNonland controller sourceId targets
  | .target, .returnTapped, .none =>
    g.returnNontokenTapped targets
  | .top, .playThisTurn, .ifHero =>
    g.applyDaredevilExile controller sourceId
  | _, _, _ => g

/-- Resolve `TriggerResolution.sacrifice`. Each printed selector keeps
the behavior of the combination it replaced. Any other selector sacrifices
nothing. -/
def applySacrifice (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (what : TriggeredAbility.ObjectSelector)
    (note : TriggeredAbility.TriggerSacrificeNote) : Game :=
  let sacrificeSource (how : TriggeredAbility.SacrificeSourceHow) (noted : Bool) : Game :=
    let g := if noted then { g with sourceWasSacrificed := false } else g
    let mark (game : Game) : Game :=
      if noted then { game with sourceWasSacrificed := true } else game
    match how with
    | .isSacrificed =>
      g.withSourceOnBattlefield sourceId (fun g src =>
        mark (g.sacrificeToGraveyard src s!"{src.name} is sacrificed"))
    | .controllerSacrifices =>
      g.withSourceOnBattlefield sourceId (fun g src =>
        mark (g.sacrificeToGraveyard src
          s!"{(g.player controller).name} sacrifices {src.name}"))
    | .movedAsSacrificed =>
      g.withTriggerSource sourceId fun g src =>
        let name := src.name
        let (g, _) := g.move src.id (.graveyard src.owner) none
        (mark g).logMsg s!"{name} is sacrificed"
  match what, note with
  | .opponentChosenCreature, .none =>
    g.withLegalTriggerPlayer controller ab sourceId targets (fun g pid =>
      g.beginSacrificeCreature pid)
  | .eachPlayersCreature, .none =>
    g.beginSacrificeCreatures (g.apnapOrder)
  | .leastPower, .none =>
    let defn :=
      match sourceId.bind g.findObject? with
      | some src => src.status.attackingWhom.getD (g.opponent controller)
      | none => g.opponent controller
    let chosen :=
      match targets[0]? with
      | some (Target.permanent id) => some id
      | _ => none
    g.sacrificeLeastPowerCreature defn chosen
  | .combatDamager, .none =>
    g.beginSacDamagers controller ((g.livingOpponents controller).map (·.id))
  | .chosenNontokenCreature, .none =>
    g.continueNontokenSacrifices ((g.livingOpponents controller).map (·.id)) #[]
  | .source, .noted =>
    sacrificeSource .isSacrificed true
  | .sacrificedSource how, .noted =>
    sacrificeSource how true
  | .source, .none =>
    sacrificeSource .isSacrificed false
  | .sacrificedSource how, .none =>
    sacrificeSource how false
  | .plan, .none =>
    g.sacrificePlanIfOnBattlefield sourceId
  | .plan, .forReflexive =>
    let stillThere :=
      match sourceId.bind g.findObject? with
      | some o => o.isOnBattlefield
      | none => false
    let g := g.sacrificePlanIfOnBattlefield sourceId
      (gone := fun name =>
        s!"{name} is no longer on the battlefield. The reflexive ability doesn't trigger.")
      (missing :=
        "The Plan is no longer on the battlefield. The reflexive ability doesn't trigger.")
    { g with planWasSacrificed := stillThere }
  | .another, _ =>
    match sourceId with
    | some sid =>
      { g with pending := .maySacrificeAnotherBolg controller sid }.logMsg
        s!"{(g.player controller).name} may sacrifice another creature (Bolg reflexive trigger)"
    | none => g.logMsg "Bolg is no longer in play"
  | _, _ => g

/-- Resolve `TriggerResolution.attach`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyAttach (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (what : TriggeredAbility.TriggerAttachWhat)
    (host : TriggeredAbility.TriggerAttachTo) : Game :=
  match what, host with
  | .source, .created =>
    match (g.recentTokenIds.back?).bind g.findObject? with
    | some tok =>
      g.withSourceOnBattlefield sourceId (fun g src => g.attachSourceTo src tok)
        "The Equipment is no longer in play"
    | none => g
  | .source, .target =>
    g.withLegalKindPermanent controller ab.targetKind targets (fun g host =>
      g.withSourceOnBattlefield sourceId (fun g src => g.attachSourceTo src host)
        "The Equipment is no longer in play")
      sourceId (some "The target is no longer legal")
  | .target, .optionalCreature =>
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
  | .source, .creatureTarget =>
    match targets[1]?, targets[0]? with
    | some (Target.permanent hid), _
    | none, some (Target.permanent hid) =>
      match g.findObject? hid, sourceId.bind g.findObject? with
      | some host, some src =>
        if host.isCreature then g.attachSourceTo src host else g
      | _, _ => g
    | _, _ => g
  | .anyYouControl, .target =>
    let g := { g with equipmentAttachedHost := none }
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
  | .putArtifact, .notedHost =>
    match g.putArtifactThisWay with
    | none => g
    | some (id, hostId) =>
      let g := { g with putArtifactThisWay := none }
      match g.findObject? id with
      | none => g
      | some o =>
        match g.findObject? hostId with
        | some host =>
          if host.isOnBattlefield then g.attachSourceTo o host
          else g.logMsg s!"{host.name} is no longer on the battlefield"
        | none => g.logMsg "The source is no longer in play"
  | .created, .source =>
    match g.createdTokenThisWay.bind g.findObject? with
    | none => { g with createdTokenThisWay := none }
    | some tok =>
      let g := { g with createdTokenThisWay := none }
      match sourceId.bind g.findObject? with
      | some src => g.attachSourceTo tok src
      | none => g
  | .announcedEquipment, .announcedCreature =>
    match targets.toList with
    | [Target.permanent eqId, Target.permanent crId] =>
      match g.findObject? eqId, g.findObject? crId with
      | some eq, some cr =>
        if eq.isOnBattlefield && cr.isOnBattlefield && eq.printed.isEquipment &&
            cr.isCreature then
          g.attachSourceTo eq cr
        else
          g.logMsg "The Equipment won't move"
      | _, _ => g.logMsg "The Equipment won't move"
    | [Target.permanent id] =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield && o.printed.isEquipment then
          g.logMsg "The Equipment won't move"
        else
          g.logMsg "No Equipment was chosen"
      | none => g.logMsg "The Equipment won't move"
    | _ => g.logMsg "The Equipment won't move"
  | .eachTargetEquipment, .enchantedCreature =>
    match sourceId.bind g.findObject? with
    | some src =>
      match src.attachedTo.bind g.findObject? with
      | none =>
        g.logMsg "The enchanted creature has left. Equipment stays where it is."
      | some host =>
        targets.foldl (fun (g : Game) (t : Target) =>
          match t with
          | Target.permanent id =>
            match g.findObject? id with
            | some eq =>
              if eq.isOnBattlefield && eq.printed.isEquipment then
                g.attachSourceTo eq host
              else g
            | none => g
          | _ => g) g
    | none =>
      g.logMsg "The enchanted creature has left. Equipment stays where it is."
  | _, _ => g

/-- Resolve `TriggerResolution.mayCast`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyMayCast (g : Game) (controller : PlayerId) (lastKnownPower : Option Int)
    (origin : TriggeredAbility.TriggerCastFrom)
    (maxMv : TriggeredAbility.TriggerCastMv)
    (cost : TriggeredAbility.TriggerCastCost)
    (note : TriggeredAbility.TriggerCastNote) : Game :=
  match origin, maxMv, cost, note with
  | .graveyard, .unlimited, .pay, .exileInstead =>
    let eligible := (g.player controller).graveyard.filter (fun id =>
      (g.findObject? id).any (fun o => o.printed.isArtifact || o.printed.isInstantOrSorcery))
    if eligible.isEmpty then
      g.logMsg s!"{(g.player controller).name} has no artifact, instant, or sorcery in the graveyard"
    else
      { g with pending := .fraChoice controller (.mayCastFromGraveyard eligible) }.logMsg
        s!"{(g.player controller).name} may cast an artifact, instant, or sorcery spell from their graveyard"
  | .hand, .twiceLegendaryWizards, .withoutPaying, .none =>
    let wizards :=
      (g.permanentsOf controller).filter (fun o =>
        o.isLegendary && g.hasSubtype o "Wizard") |>.size
    g.beginMayCastInstantSorceryFromHand controller (wizards * 2)
  | .hand, .lastKnown, .withoutPaying, .none =>
    g.beginMayCastInstantSorceryFromHand controller (lastKnownPower.getD 0).toNat
  | .nextRedOrGreenCreature, .unlimited, .withoutPaying, .none =>
    { g with pendingFreeRGCreature := some controller }
      |>.logMsg "The next red or green creature spell you cast this turn can be cast without paying its mana cost"
  | .impulse, .unlimited, .withoutPaying, .none =>
    if !g.grimaImpulseReady then g
    else
      let victim := g.grimaImpulseVictim.getD (g.opponent controller)
      let found := g.grimaImpulseFound
      let others := g.grimaImpulseOthers
      let g := { g with
        grimaImpulseReady := false
        grimaImpulseVictim := none
        grimaImpulseFound := none
        grimaImpulseOthers := #[] }
      match found with
      | none =>
        g.requestOrderInto others (.library victim)
          s!"{(g.player victim).name} randomizes the exiled cards; they become that player's library"
      | some cardId =>
        let name := (g.object! cardId).name
        g.beginFraChoice controller (.mayCastGrima cardId others victim)
          s!"{(g.player controller).name} may cast {name} without paying its mana cost"
  | _, _, _, _ => g

/-- Resolve `TriggerResolution.amass`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyAmass (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (lastKnownPower : Option Int) (n : Nat) (subtype : String)
    (amount : AmassAmount) (attachSource : Bool)
    (who : TriggeredAbility.AmassWho) : Game :=
  match amount, who with
  | .fixed, .you =>
    if attachSource then g.amass controller subtype n (attach := sourceId)
    else g.amass controller subtype n
  | .sourcePower, .you =>
    let n := (lastKnownPower.getD 0).toNat
    if attachSource then g.amass controller subtype n (attach := sourceId)
    else g.amass controller subtype n
  | .notedExcess, .you =>
    let excess := g.excessDamageThisWay
    let g := { g with excessDamageThisWay := 0 }
    if excess > 0 then
      let g :=
        if attachSource then g.amass controller subtype excess (attach := sourceId)
        else g.amass controller subtype excess
      g.logMsg s!"excess damage {excess} — amass {subtype}s {excess}"
    else g
  | .notedPower, .notedController =>
    if g.destroyedForAmassThisWay then
      match g.amassControllerThisWay with
      | some pid =>
        if attachSource then
          g.amass pid subtype g.amassAmountThisWay (attach := sourceId)
        else g.amass pid subtype g.amassAmountThisWay
      | none => g
    else g
  | _, _ => g

/-- Resolve `TriggerResolution.discard`. Each printed combination keeps
the behavior of the constructor it replaced. Any other selector discards
nothing. -/
def applyDiscard (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (targets : Array Target)
    (what : TriggeredAbility.ObjectSelector) : Game :=
  match what with
  | .cards n .you =>
    if g.mayThenDrop > 0 && n == 1 then
      let drawN :=
        match g.mayThenConditional with
        | some (.draw (.fixed k)) => k.toNat
        | _ => 1
      let g := g.beginMayDiscardDraw controller drawN
      if g.pending == .none then g.failMayThen else g
    else
      let g := { g with discardedCardThisWay := none }
      g.beginDiscardCards #[controller] n
  | .cards n .eachOpponent =>
    g.beginDiscardCards (g.apnapOrder.filter (· != controller)) n
  | .chosenNonland =>
    g.withLegalKindPlayer controller .opponent targets
      (fun g pid => g.discardNonlandFrom controller pid)
      sourceId (some "The target is no longer legal")
  | .cards n .targetOpponent =>
    g.withLegalKindTarget controller .opponent targets (fun g tgt =>
      match tgt with
      | Target.player pid => g.beginDiscardCards #[pid] n
      | _ => g) sourceId none
  | .hand =>
    if g.mayThenDrop > 0 then
      let drawN :=
        match g.mayThenConditional with
        | some (.draw (.fixed k)) => k.toNat
        | _ => 0
      g.beginFraChoice controller (.mayDiscardHandDrawFixed drawN)
        s!"{(g.player controller).name} may discard their hand. If they do, they draw {drawN} cards"
    else
      { g with handDiscardedThisWay := none, notedSourceThisWay := sourceId }
        |>.beginFraChoice controller (.mayDiscardHandBalin sourceId)
          s!"{(g.player controller).name} may discard their hand"
  | _ => g

/-- Resolve `TriggerResolution.destroy`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyDestroy (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (lastKnownPower : Option Int) (what : TriggeredAbility.TriggerDestroyWhat)
    (note : TriggeredAbility.TriggerDestroyNote) : Game :=
  match what, note with
  | .oppArtifactsEnchantments, .countDestroyed =>
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
      return { g with permanentsDestroyedThisWay := n }
  | .permanentDealtDamage, .none =>
    match g.permanentDealtDamageThisWay with
    | none => g
    | some oid =>
      let g := { g with permanentDealtDamageThisWay := none }
      match g.findObject? oid with
      | some o => if o.isOnBattlefield then g.destroyPermanent o else g
      | none => g
  | .target, .forAmass =>
    let clear := { g with
      destroyedForAmassThisWay := false
      amassControllerThisWay := none
      amassAmountThisWay := 0
      amassYouControlledThisWay := false }
    match targets[0]? with
    | none =>
      clear.logMsg
        "No target was chosen. Its controller is undefined and no player amasses Goblins."
    | some (Target.permanent oid) =>
      match g.findObject? oid with
      | none => clear.logMsg "The target is no longer legal"
      | some o =>
        if !o.isOnBattlefield then clear.logMsg "The target is no longer legal"
        else
          let pw := lastKnownPower.getD (g.power o)
          let n := if pw > 0 then pw.toNat else 0
          let g := g.destroyPermanent o
          { g with
            destroyedForAmassThisWay := true
            amassControllerThisWay := o.controller
            amassAmountThisWay := n
            amassYouControlledThisWay := o.controller == some controller }
    | _ =>
      clear.logMsg
        "No target was chosen. Its controller is undefined and no player amasses Goblins."
  | .target, .none =>
    if targets.isEmpty && ab.allowsZeroTargets then g
    else
      g.withLegalKindPermanent controller ab.targetKind targets (fun g o =>
        g.destroyPermanent o) sourceId (some "The target is no longer legal")
  | .target, .chosenToken =>
    g.destroyChosenToken targets
  | .source, _ =>
    g.withAffected controller ab sourceId targets .source fun g o =>
      g.applyPermanentAction o .destroy
  | .enchanted, _ =>
    g.withAffected controller ab sourceId targets .enchanted fun g o =>
      g.applyPermanentAction o .destroy
  | .targetWhileSource, _ =>
    g.withAffected controller ab sourceId targets .targetWhileSource fun g o =>
      g.applyPermanentAction o .destroy
  | _, _ => g

/-- Resolve `TriggerResolution.addMana`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyAddMana (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (types : Array ManaType) (amount : TriggeredAbility.TriggerManaAmount) : Game :=
  match amount with
  | .fixed =>
    g.addManaLogged controller types
  | .perChargeCounter =>
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
    let types := types.foldl (fun acc t => acc ++ Array.replicate n t) #[]
    g.addManaLogged controller types

/-- Resolve `TriggerResolution.draw`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyTriggerDraw (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (amount : TriggeredAbility.NumberSelector)
    (who : TriggeredAbility.PlayerSelector) : Game :=
  match who, amount with
  | .enchantedController, _ =>
    g.drawForEnchantedController sourceId
  | .you, .upToHandSize k =>
    g.drawUpToHandSize controller k
  | .opponentHasYou, _ =>
    match g.palantirChoiceReady with
    | none => g
    | some (c, opp, sid) =>
      ({ g with palantirChoiceReady := none }).offerPalantirChoice c opp sid
  | .you, .perControlled ty =>
    let n := ((g.permanentsOf controller).filter (fun o => o.printed.hasType ty)).size
    if n == 0 then g else g.draw controller n
  | .eachOpponent, .fixed n =>
    g.forEachOpponent controller (fun g pid => g.draw pid n.toNat)
  | .you, .fixed n =>
    g.draw controller n.toNat
  | .you, .forEachTappedHuman =>
    let n := g.humansTappedThisWay
    let g := { g with humansTappedThisWay := 0 }
    if n == 0 then g else g.draw controller n
  | .you, .perFatGraveyard =>
    g.drawPerSevenCardGraveyard controller
  | .you, .discardedHand =>
    match g.handDiscardedThisWay with
    | some n => if n == 0 then g else g.draw controller n
    | none => g
  | .you, .equalToManaSpent =>
    let spent :=
      ((g.resolvingAbilityObject?.bind (·.fraCauseStatus)).map (·.manaSpentToCast)).getD 0
    if spent == 0 then
      { g with skipTriggerSequenceRest := true }.logMsg
        "No mana was spent to cast that spell"
    else g.draw controller spent
  | _, _ => g

/-- Resolve `TriggerResolution.returnToHand`. Each printed combination keeps
the behavior of the constructor it replaced. Any other selector returns
nothing. -/
def applyReturnToHand (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (what : TriggeredAbility.ObjectSelector)
    (note : TriggeredAbility.TriggerReturnNote) : Game :=
  match what, note with
  | .graveyardCard, .none =>
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
  | .permanent, .returnedPermanent =>
    let g := { g with returnedPermanentThisWay := false }
    g.withLegalKindPermanent controller ab.targetKind targets (fun g o =>
      let g := g.returnToHand o.id o.owner
      { g with returnedPermanentThisWay := true }) sourceId none
  | .graveyardPermanent, .none =>
    g.withLegalKindTarget controller ab.targetKind targets (fun g tgt =>
      match tgt with
      | Target.card id | Target.permanent id =>
        g.returnToHand id controller
      | _ => g) sourceId (some "The target is no longer legal")
  | .milledSubtype subtype, .none =>
    let ids := g.milledIdsThisWay
    let g := { g with milledIdsThisWay := #[] }
    ids.foldl (fun acc id =>
      match acc.findObject? id with
      | some o =>
        if o.printed.hasSubtype subtype then
          let name := o.name
          let (acc, _) := acc.move id (.hand controller) none
          acc.logMsg s!"{name} is put into {(acc.player controller).name}'s hand"
        else acc
      | none => acc) g
  | .source, .none =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.zone == .graveyard o.owner then g.returnToHand o.id o.owner
      else g.logMsg s!"{o.name} is no longer in the graveyard"
    | none => g.logMsg "The ability's source is no longer in the graveyard"
  | .linkedExile, .none =>
    g.returnLinkedExileToHand sourceId
  | .cause, .none =>
    g.returnCauseToOwnerHand targets
  | _, _ => g

/-- Resolve `TriggerResolution.put`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyPut (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (what : TriggeredAbility.TriggerPutWhat)
    (how : TriggeredAbility.TriggerPutHow)
    (note : TriggeredAbility.TriggerPutNote) : Game :=
  match what, how, note with
  | .linkedExile, _, _ =>
    match sourceId.bind g.findObject? with
    | some src => g.returnLinkedExile src
    | none => g
  | .creatureMvAtMost _, _, _ =>
    g.withLegalKindTarget controller ab.targetKind targets
      (fun g t =>
        match t with
        | Target.card oid =>
          match g.findObject? oid with
          | none => g.logMsg "The target is no longer in the graveyard"
          | some o =>
            let name := o.name
            let (g, newId) := g.putOntoBattlefield oid controller
            g.logMsg s!"{name} returns to the battlefield"
              |>.afterPermanentEnters (g.object! newId)
        | _ => g.logMsg "The target is no longer legal")
      sourceId (some "The target is no longer legal")
  | .nonlandMvAtMost _, _, _ =>
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
  | .source, .asArtifact, _ =>
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
  | .notedLands, .tapped, _ =>
    let ids := g.exiledIdsThisWay
    let g := { g with exiledIdsThisWay := #[] }
    ids.foldl (fun g id =>
      match g.findObject? id with
      | none => g
      | some o =>
        let name := o.name
        let (g, retId) := g.move id .battlefield (some o.owner)
        let ret := g.object! retId
        let g := g.setObject { ret with status := { ret.status with tapped := true } }
        let g := g.logMsg s!"{name} is exiled, then returned tapped"
        g.afterLandEnters (g.object! retId)) g
  | .discardedLand, .tapped, _ =>
    match g.discardedCardThisWay with
    | none => g
    | some (pid, id) =>
      let g := { g with discardedCardThisWay := none }
      match g.findObject? id with
      | some o =>
        if o.printed.isLand && o.zone == .graveyard o.owner then
          let entered := g.putOntoBattlefield o.id pid (tapped := true) (summoningSick := false)
          let g := entered.1.logMsg s!"{o.name} enters the battlefield tapped"
          g.afterLandEnters (g.object! entered.2)
        else g
      | none => g
  | .landFromHand, .tapped, _ =>
    { g with pending := .mayPutLandFromHand controller }.logMsg
      s!"{(g.player controller).name} may put a land card from their hand onto the battlefield tapped"
  | .artifactFromHand, _, .forAttach =>
    let g := { g with putArtifactThisWay := none }
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
  | .source, .underOwner, note =>
    g.returnSourceUnderOwner controller sourceId note.enterMods
  | .cause subtype, .underOwner, note =>
    g.returnCauseUnderOwner controller targets subtype note.enterMods
  | _, _, _ => g

/-- Resolve `TriggerResolution.grant`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyGrant (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (what : TriggeredAbility.TriggerGrantWhat)
    (who : TriggeredAbility.TriggerGrantWho) : Game :=
  match what, who with
  | .doubleStrike, .equippedAttackers =>
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
  | .protectionEverything, .youIfCast =>
    if !(sourceId.bind g.findObject?).any (·.wasCast) then
      g.logMsg "It wasn't cast. The ability does nothing."
    else
      g.modifyPlayer controller (fun pl => { pl with protectionFromEverything := true })
        |>.logMsg s!"{(g.player controller).name} gains protection from everything"
  | .keywords k, .target =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      g.grantUntilEotLogged o k)
      "The target is no longer legal"
  | .keywords k, .source =>
    g.withAffected controller ab sourceId targets .source fun g o =>
      g.applyPermanentAction o (.grantKeywords k)
  | .keywords k, .enchanted =>
    g.withAffected controller ab sourceId targets .enchanted fun g o =>
      g.applyPermanentAction o (.grantKeywords k)
  | .keywords k, .targetWhileSource =>
    g.withAffected controller ab sourceId targets .targetWhileSource fun g o =>
      g.applyPermanentAction o (.grantKeywords k)
  | .keywords k, .creaturesYouControl =>
    g.forEachControlledCreature controller fun g o =>
      g.grantUntilEotLogged o k
  | .keywords k, .youControlSubtype subtype =>
    g.forEachControlledCreature controller fun g o =>
      if g.hasSubtype o subtype then g.grantUntilEotLogged o k else g
  | .keywords k, .attackingAlone =>
    match g.attackingAlone? controller with
    | none => g.logMsg "No creature is attacking alone"
    | some o => g.grantUntilEotLogged o k
  | .landfallCreateElf, .source =>
    g.gainLandfallCreateElf sourceId
  | .hexproofWhileSource, .target =>
    g.grantHexproofWhileSource controller sourceId targets ab.targetKind
  | .preventDamageWhileSource, .target =>
    g.preventDamageWhileSource controller sourceId targets ab.targetKind
  | .assignCombatDamageEqualToughness, .creaturesYouControl =>
    { g with assignCombatDamageEqualToughness := some controller }
      |>.logMsg "Creatures you control assign combat damage equal to their toughness"
  | .basePowerEqualHand, .source =>
    g.grantHandSizePower sourceId
  | .ironFistTap, .source =>
    g.grantIronFistTap sourceId
  | .keywords k, .spellTargets =>
    g.grantKeywordsToSpellCreatureTargets k
  | _, _ => g

/-- Resolve `TriggerResolution.fight`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyFight (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (targets : Array Target) (who : TriggeredAbility.TriggerFightWho)
    (how : TriggeredAbility.TriggerFightHow) : Game :=
  match who, how with
  | .source, .mutual =>
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
  | .announced, .upToOneOther =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent srcId), some (Target.permanent destId) =>
      match g.findObject? srcId, g.findObject? destId with
      | some src, some dest =>
        if src.id != dest.id && src.isOnBattlefield && dest.isOnBattlefield &&
            src.isCreature && dest.isCreature && src.controlledBy controller then
          g.fightCreatures src dest
        else g.logMsg "The target is no longer legal"
      | _, _ => g.logMsg "The target is no longer legal"
    | some (Target.permanent srcId), none =>
      match g.findObject? srcId with
      | some src => g.logMsg s!"{src.name} has nothing to fight"
      | none => g.logMsg "The target is no longer legal"
    | _, _ => g.logMsg "The target is no longer legal"
  | .announced, .mutual =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent srcId), some (Target.permanent destId) =>
      let srcOk := (g.legalCreatureYouControlTargets controller).contains
        (Target.permanent srcId)
      let destOk := (g.legalOppCreatureTargets controller).contains
        (Target.permanent destId)
      if srcOk && destOk then
        g.fightCreatures (g.object! srcId) (g.object! destId)
      else
        let logIllegal (g : Game) (ok : Bool) (id : ObjectId) : Game :=
          if ok then g else g.illegalAbilityTarget (Target.permanent id)
        logIllegal (logIllegal g srcOk srcId) destOk destId
    | _, _ => g.logMsg "The target is no longer legal"
  | .equipmentHost, .reflexive =>
    match g.equipmentAttachedHost with
    | none => g
    | some hostId =>
      let g := { g with equipmentAttachedHost := none }
      match g.findObject? hostId with
      | some host =>
        if !host.isOnBattlefield then g
        else
          let effect : Effect :=
            { targeting := .of .creature, allowsZeroTargets := true
              resolution := .fra .damageEqualSourcePower
              phrase := s!"{host.name} deals damage equal to its power to up to one target creature" }
          g.putReflexiveTrigger controller (some hostId) effect
      | none => g
  | _, _ => g

/-- Resolve `TriggerResolution.mill`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyMill (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (lastKnownPower lastKnownToughness : Option Int) (n : Nat)
    (who : TriggeredAbility.TriggerMillWho)
    (amount : TriggeredAbility.TriggerMillAmount)
    (note : TriggeredAbility.TriggerMillNote) : Game :=
  match who, amount, note with
  | .you, .fixed, .none =>
    g.mill controller n
  | .you, .fixed, .milledCards =>
    let before := (g.player controller).graveyard
    let g := g.mill controller n
    let after := (g.player controller).graveyard
    { g with milledIdsThisWay := after.filter (fun id => !before.contains id) }
  | .target, .fixed, .none =>
    g.withLegalTriggerPlayer controller ab sourceId targets (fun g pid => g.mill pid n)
  | .thatPlayer, .thatManyLost, .none =>
    match lastKnownPower, lastKnownToughness with
    | some k, some idx => g.mill ⟨idx.toNat⟩ k.toNat
    | _, _ => g
  | .eachOpponent, .fixed, .opponentsMilled =>
    let opps := (g.livingOpponents controller).map (·.id)
    let (g, milled) := g.millThenReflexive opps n
    { g with opponentsMilledThisWay := milled }
  | _, _, _ => g

/-- Resolve `TriggerResolution.untap`. Each printed combination keeps
the behavior of the constructor it replaced. A stun counter is removed
instead of untapping (CR 122.1d). -/
def applyUntap (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (who : TriggeredAbility.TriggerUntapWho) : Game :=
  match who with
  | .attackingCreatures =>
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.status.attacking then
          g := g.applyPermanentAction o .untap
      return g
  | .target =>
    g.withAffected controller ab sourceId targets .target fun g o =>
      g.applyPermanentAction o .untap
  | .source =>
    g.withAffected controller ab sourceId targets .source fun g o =>
      g.applyPermanentAction o .untap
  | .enchanted =>
    g.withAffected controller ab sourceId targets .enchanted fun g o =>
      g.applyPermanentAction o .untap
  | .targetWhileSource =>
    g.withAffected controller ab sourceId targets .targetWhileSource fun g o =>
      g.applyPermanentAction o .untap
  | .equipped =>
    match g.attachedHost? sourceId with
    | some host =>
      if host.isOnBattlefield then g.applyPermanentAction host .untap
      else
        { g with skipTriggerSequenceRest := true }.logMsg "The equipped creature has left"
    | none =>
      { g with skipTriggerSequenceRest := true }.logMsg "The equipped creature has left"
  | .firstThisTurn =>
    let id := g.resolvingCauseId.orElse (fun _ => g.lastBecameTapped)
    match id.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield && o.status.tapped then g.applyPermanentAction o .untap else g
    | none => g

/-- Resolve `TriggerResolution.tap`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyTap (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (who : TriggeredAbility.TriggerTapWho) : Game :=
  match who with
  | .humans =>
    { g with pending := .tapHumans controller, humansTappedThisWay := 0 }.logMsg
      s!"{(g.player controller).name} may tap any number of untapped Humans they control"
  | .enchanted =>
    match sourceId.bind g.findObject? with
    | none => g
    | some src =>
      match src.attachedTo.bind g.findObject? with
      | none => g.logMsg "Nothing is enchanted"
      | some host => g.applyPermanentAction host .tap
  | .targetIfPresent =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some tgt =>
        if tgt.isOnBattlefield then g.applyPermanentAction tgt .tap else g
      | none => g
    | _ => g
  | .target =>
    g.withLegalKindPermanent controller ab.targetKind targets (fun g o =>
      g.applyPermanentAction o .tap) sourceId (some "The target is no longer legal")
  | .source =>
    if g.mayThenDrop > 0 then
      match sourceId.bind g.findObject? with
      | some src =>
        if src.isOnBattlefield && !src.status.tapped then
          g.beginFraChoice controller (.mayTapSourceThen (.mshReflexive 0 0) src.id)
            s!"{(g.player controller).name} may tap {src.name}"
        else
          (g.logMsg s!"{src.name} can't be tapped this way. The reflexive ability doesn't trigger.").failMayThen
      | none =>
        (g.logMsg "The source is no longer on the battlefield. The reflexive ability doesn't trigger.").failMayThen
    else
      g.withAffected controller ab sourceId targets .source fun g o =>
        g.applyPermanentAction o .tap
  | .enchantedWhileSource =>
    g.withAffected controller ab sourceId targets .enchanted fun g o =>
      g.applyPermanentAction o .tap
  | .targetWhileSource =>
    g.withAffected controller ab sourceId targets .targetWhileSource fun g o =>
      g.applyPermanentAction o .tap

/-- Resolve `TriggerResolution.removeCounters`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyRemoveCounters (g : Game) (sourceId : Option ObjectId)
    (what : TriggeredAbility.TriggerRemoveWhat)
    (who : TriggeredAbility.TriggerRemoveWho) : Game :=
  match what, who with
  | .hope, .source =>
    let g := { g with removedHopeThisWay := false }
    g.withTriggerSource sourceId fun g src =>
      if src.status.hope == 0 then g
      else
        let g := g.setObject { src with status := { src.status with hope := src.status.hope - 1 } }
        let g := g.logMsg s!"{src.name} loses a hope counter"
        { g with removedHopeThisWay := true }
  | .all, .enchanted =>
    match sourceId.bind g.findObject? with
    | none => g
    | some src =>
      match src.attachedTo.bind g.findObject? with
      | none => g
      | some host =>
        let host := g.object! host.id
        let g := g.setObject { host with status := host.status.withoutCounters }
        g.logMsg s!"counters are removed from {host.name}"
  | _, _ => g

/-- Resolve `TriggerResolution.loseLife`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyLoseLife (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target) (n : Nat)
    (who : TriggeredAbility.TriggerLifeLossWho)
    (amount : TriggeredAbility.TriggerLifeLossAmount)
    (lastKnownPower : Option Int := none) : Game :=
  match who, amount with
  | .you, .fixed =>
    g.loseLife controller n
  | .targetOpponent, .fixed =>
    g.withLegalTriggerPlayer controller ab sourceId targets (fun g pid =>
      g.loseLife pid n)
  | .eachOpponent, .fixed =>
    g.forEachOpponent controller (fun g pid => g.loseLife pid n)
  | .you, .perBurden =>
    match sourceId.bind g.findObject? with
    | none => g
    | some src => g.loseLife controller src.status.burden
  | .eachOpponent, .attachedEquipment =>
    let x := g.attachedEquipmentAtResolution sourceId lastKnownPower
    if x == 0 then g
    else g.forEachOpponent controller (fun g pid => g.loseLife pid x)
  | _, _ => g

/-- Resolve `TriggerResolution.gainLife`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyGainLife (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target) (n : Nat)
    (amount : TriggeredAbility.TriggerLifeAmount)
    (sequencedCardPower : Option Nat)
    (lastKnownPower : Option Int := none) : Game :=
  match amount with
  | .fixed =>
    g.gainLife controller n
  | .attachedEquipment =>
    let x := g.attachedEquipmentAtResolution sourceId lastKnownPower
    if x == 0 then g else g.gainLife controller x
  | .equalToTargetPower =>
    match sequencedCardPower with
    | some k => g.gainLife controller k
    | none =>
      g.withLegalTriggerTarget controller ab sourceId targets fun g t =>
        match t with
        | Target.card oid | Target.permanent oid =>
          match g.findObject? oid with
          | some o => g.gainLife controller (g.power o).toNat
          | none => g.logMsg "The target is no longer in the graveyard"
        | _ => g.logMsg "The target is no longer legal"
  | .forEachDestroyedThisWay =>
    let k := g.permanentsDestroyedThisWay
    let g := { g with permanentsDestroyedThisWay := 0 }
    if k == 0 then g else g.gainLife controller k
  | .forEachOtherCreature =>
    let k :=
      ((g.creaturesControlledBy controller).filter (fun o => some o.id != sourceId)).size
    if k == 0 then g else g.gainLife controller k

/-- Resolve `TriggerResolution.revealLibrary`. Each printed combination
keeps the behavior of the constructor it replaced. -/
partial def applyRevealLibrary (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (targets : Array Target)
    (how : TriggeredAbility.TriggerLibraryHow)
    (thenDo : TriggeredAbility.TriggerResolution)
    (who : TriggeredAbility.TriggerLibraryWho) : Game :=
  match how, thenDo, who with
  | .top n, .put .randomCreature .asPrinted .none, .you =>
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
  | .untilCreature,
    .ifElse .revealedManaValueAtMostLands
      (.put .revealed .asPrinted .none) (.returnToHand .revealed .none),
    .you =>
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
  | .untilSaga, .put .revealed .asPrinted .none, .you =>
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
  | .untilInstantOrSorcery, .exile .top .forLater .impulse, .damagedPlayer =>
    let victim := g.lastCombatDamagePlayer.getD (g.opponent controller)
    let (g, found, others) := g.exileUntilInstantOrSorcery victim
    { g with
      grimaImpulseReady := true
      grimaImpulseVictim := some victim
      grimaImpulseFound := found
      grimaImpulseOthers := others }
  | .untilNonland,
    .may (.putCounters (.ofKind .plusOnePlusOne 1) .source)
      (.exile .top .forLater .anyManaThisTurn) .ifYouDont,
    .announced =>
    let pid :=
      match targets[0]? with
      | some (Target.player p) => some p
      | _ =>
        (g.resolvingAbility.bind g.findObject?).bind (·.lastKnownToughness)
          |>.map (fun n => ⟨n.toNat⟩)
    match pid with
    | none => g.logMsg "Black Widow didn't deal combat damage to a player"
    | some pid =>
      let (g, nonland?) := g.exileLibraryUntilNonland pid
      let onBf :=
        match sourceId.bind g.findObject? with
        | some o => o.isOnBattlefield
        | none => false
      if onBf then
        { g with pending := .fraChoice controller (.widowMayCounter sourceId nonland?) }
          |>.logMsg "You may put a +1/+1 counter on Black Widow"
      else
        g.grantWidowCast controller nonland?
  | .top n, .mayCast .looked .greatestAttackingPower .withoutPaying .none, .you =>
    g.offerLookSixCast controller n
  | _, _, _ => g

/-- Resolve `TriggerResolution.revealFromHand`. Each printed combination
keeps the behavior of the constructor it replaced. -/
def applyRevealFromHand (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (targets : Array Target)
    (count : TriggeredAbility.TriggerRevealCount)
    (thenDo : TriggeredAbility.TriggerResolution) : Game :=
  match count, thenDo with
  | .hand, .exile .target .untilSourceLeaves .none =>
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
  | .onePlusCreatureCards, .discard (.cards 1 .targetOpponent) =>
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
  | _, _ => g

/-- Resolve `TriggerResolution.searchLibrary`. Each printed follow-up keeps
the behavior of the constructor it replaced. Any other resolution does nothing. -/
def applySearchLibrary (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (thenDo : TriggeredAbility.TriggerResolution) : Game :=
  match thenDo with
  | .put .forest .asPrinted .none => g.resolveSearchForest controller
  | .returnToHand .basicLand .none => g.resolveSearchBasicLandToHand controller
  | .put .basicLandOnTop .asPrinted .none =>
    g.beginLibrarySearch controller isBasicLandCard "a basic land card" .topAfterShuffle
      (optional := true)
  | .put .dragon .asPrinted .none =>
    g.beginLibrarySearch controller (fun c => c.hasSubtype "Dragon") "a Dragon card"
      .battlefieldFromHandOrLibrary (alsoHand := true)
  | .exile (.basicUpTo subtype max) .forLater .linked =>
    g.beginLibrarySearch controller
      (fun c => isBasicLandCard c && c.hasSubtype subtype)
      s!"a basic {subtype} card" (.exileLinked sourceId) (count := max)
  | _ => g

/-- Resolve `TriggerResolution.lose`. Each printed combination keeps
the behavior of the constructor it replaced. Any other combination
loses nothing. -/
def applyLose (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (what : TriggeredAbility.TriggerLoseWhat)
    (who : TriggeredAbility.TriggerLoseWho) : Game :=
  match what, who with
  | .indestructible, .target =>
    loseIndestructible .target
  | .indestructible, .source =>
    loseIndestructible .source
  | .indestructible, .enchanted =>
    loseIndestructible .enchanted
  | .indestructible, .targetWhileSource =>
    loseIndestructible .targetWhileSource
  | .allAbilities, .targetIfPresent =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some tgt =>
        if !tgt.isOnBattlefield then g
        else
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
  | _, _ => g
where
  loseIndestructible (affected : TriggeredAbility.TriggerAffected) : Game :=
    g.withAffected controller ab sourceId targets affected fun g o =>
      g.applyPermanentAction o .loseIndestructible

/-- Resolve `TriggerResolution.cant`. Each printed combination keeps
the behavior of the constructor it replaced. Any other combination
does nothing. -/
def applyCant (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (what : TriggeredAbility.TriggerCantWhat)
    (who : TriggeredAbility.TriggerAffected) : Game :=
  match what, who with
  | .beBlocked, _ =>
    g.withAffected controller ab sourceId targets who fun g o =>
      g.applyPermanentAction o .cantBeBlocked
  | .beBlockedExceptByHaste, _ =>
    g.withAffected controller ab sourceId targets who fun g o =>
      g.mapObjectStatus o (fun s => { s with cantBeBlockedExceptByHasteUntilEot := true })
        |>.logMsg s!"{o.name} can't be blocked this turn except by creatures with haste"
  | .untapWhileYouControl, .target =>
    g.withLegalKindPermanent controller .oppCreature targets (fun g o =>
      let o := g.object! o.id
      let sid := sourceId.getD ⟨0⟩
      g.mapObjectStatus o (fun s =>
        { s with cantUntapGrantedBy := s.cantUntapGrantedBy.push sid }))
      sourceId (some "The target is no longer legal")
  | .untapWhileYouControl, _ => g

/-- Resolve `TriggerResolution.putOnLibrary`. Each printed combination keeps
the behavior of the constructor it replaced. A card from hand on top
puts nothing. -/
def applyPutOnLibrary (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (place : TriggeredAbility.TriggerLibraryPlace)
    (what : TriggeredAbility.TriggerLibraryWhat) : Game :=
  match place, what with
  | .top, .permanent who =>
    g.withAffected controller ab sourceId targets who fun g o =>
      g.applyPermanentAction o .putOnTopOfLibrary
  | .bottom, .permanent who =>
    g.withAffected controller ab sourceId targets who fun g o =>
      g.applyPermanentAction o .putOnBottomOfLibrary
  | .bottom, .cardFromHand =>
    if (g.player controller).hand.isEmpty then g
    else
      { g with pending := .putOnBottom controller 1 }.logMsg
        s!"{(g.player controller).name} puts a card from their hand on the bottom of their library"
  | .top, .cardFromHand => g

/-- Resolve `TriggerResolution.setBasePT`. Each printed combination keeps
the behavior of the constructor it replaced. Any other combination sets
nothing. -/
def applySetBasePT (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (lastKnownPower lastKnownToughness : Option Int)
    (power toughness : Int) (who : TriggeredAbility.TriggerAffected)
    (amount : TriggeredAbility.TriggerBasePTAmount) : Game :=
  match amount, who with
  | .fixed, _ =>
    g.withAffected controller ab sourceId targets who fun g o =>
      g.applyPermanentAction o (.setBasePT power toughness)
  | .equalSource, .target =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let (pw, tw) := g.sourcePTAtResolution sourceId lastKnownPower lastKnownToughness
      let g := g.mapObjectStatus o (fun s => { s with setBasePT := some (pw, tw) })
      g.logMsg
        s!"{o.name}'s base power and toughness become {pw}/{tw} until end of turn")
      "No target was chosen"
  | .equalSource, _ => g

partial def applyTriggeredAbility (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target := #[])
    (dividedDamage : Array Nat := #[]) (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none)
    (sourceName : String := "This creature")
    (resolutionOverride : Option TriggeredAbility.TriggerResolution := none)
    (sequencedCardPower : Option Nat := none) : Game :=
  if resolutionOverride.isNone && !g.interveningStillHolds controller ab then
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
  | .amass n => g.amassGoblins controller n
  | .createTokens kind n tapped =>
    g.createKindTokens controller kind n (tapped := tapped)
  | .addMana types =>
    g.addManaLogged controller types
  | .discard n => g.beginDiscardCards #[controller] n
  | .spell r =>
    g.applyUnified controller { ab.effect with resolution := .spell r } targets
  | .trigger _ => (
  match resolutionOverride.getD ab.resolution with
  | .pump power toughness who =>
    g.applyTriggerPump controller ab sourceId targets lastKnownPower lastKnownToughness
      power toughness who
  | .dealDamage amount who note =>
    g.applyTriggerDamage controller ab sourceId targets lastKnownPower sourceName
      amount who note
  | .scry (.fixed n) =>
    g.beginScry controller n.toNat
  | .scry _ => g
  | .draw amount who =>
    g.applyTriggerDraw controller sourceId amount who
  | .searchLibrary thenDo =>
    g.applySearchLibrary controller sourceId thenDo
  | .discard what =>
    g.applyDiscard controller sourceId targets what
  | .sacrifice what note =>
    g.applySacrifice controller ab sourceId targets what note
  | .lose what who =>
    g.applyLose controller ab sourceId targets what who
  | .cant what who =>
    g.applyCant controller ab sourceId targets what who
  | .becomeArtifact who =>
    g.withAffected controller ab sourceId targets who fun g o =>
      let g := g.mapObjectStatus o (fun s => { s with additionalArtifactUntilEot := true })
      g.logMsg s!"{o.name} becomes an artifact until end of turn"
  | .becomePrepared who =>
    g.withAffected controller ab sourceId targets who fun g o =>
      g.applyPermanentAction o .becomePrepared
  | .setBasePT power toughness who amount =>
    g.applySetBasePT controller ab sourceId targets lastKnownPower lastKnownToughness
      power toughness who amount
  | .putOnLibrary place what =>
    g.applyPutOnLibrary controller ab sourceId targets place what
  | .dividedDamage =>
    Id.run do
      let mut g := g
      for i in [0:targets.size] do
        let t := targets[i]!
        let n := dividedDamage[i]?.getD 0
        if n > 0 then
          g := g.applyEffect controller (Effect.dealDamage n) #[t]
      return g
  | .sequence rs =>
    -- One legality check for the whole sequence (CR 608.2b). Power is read
    -- before any step moves the card, then each step runs in order. A step
    -- that opens a pending choice pauses the rest until that choice finishes.
    if g.sequenceAllTargetsIllegal controller ab.effect targets sourceId then
      g.logIllegalSequenceTargets targets
    else
      let cardPower :=
        match sequencedCardPower with
        | some n => some n
        | none =>
          match targets[0]? with
          | some (Target.card oid) | some (Target.permanent oid) =>
            (g.findObject? oid).map fun o => (g.power o).toNat
          | _ => none
      let steps := rs.flatMap TriggeredAbility.TriggerResolution.flatten
      let (g, rest, _, _) :=
        steps.foldl
          (fun (acc : Game × List TriggeredAbility.TriggerResolution × Bool × Bool) step =>
            let (g, waiting, paused, dropped) := acc
            if dropped then
              (g, [], true, true)
            else if paused then
              (g, waiting ++ [step], true, false)
            else if g.mayThenSkip > 0 then
              ({ g with mayThenSkip := g.mayThenSkip - 1 }, waiting, false, false)
            else
              let pendingBefore := g.pending
              let g :=
                g.applyTriggeredAbility controller ab sourceId targets dividedDamage
                  lastKnownPower lastKnownToughness sourceName (some step) cardPower
              if g.skipTriggerSequenceRest then
                ({ g with skipTriggerSequenceRest := false }, [], true, true)
              else
                -- Pause only when this step opens a choice. A choice that was
                -- already pending belongs to an earlier ability.
                let opened := g.pending != pendingBefore && g.pending != .none
                (g, waiting, opened, false))
          (g, [], false, false)
      -- The ordinal belongs to this resolution. A paused sequence still
      -- needs it for the `«if» (.nthResolve _)` steps that have not run.
      let usesNth := steps.any fun
        | .noteResolveThisTurn _ => true
        | .«if» (.nthResolve _) _ => true
        | _ => false
      -- A nested `mayThen` stores its conditional here. Later steps of this
      -- sequence follow that conditional.
      let already :=
        match g.triggerSequenceRest with
        | some stored => stored.steps
        | none => []
      let combined := already ++ rest
      let g := { g with triggerSequenceRest := none, mayThenSkip := 0 }
      let g :=
        if combined.isEmpty && usesNth then { g with nthResolveThisWay := none } else g
      let g :=
        if combined.isEmpty && g.pending == .none then
          { g with mayThenDrop := 0, mayThenConditional := none }
        else g
      if combined.isEmpty then g
      else
        { g with triggerSequenceRest := some {
            controller
            ability := ab
            sourceId
            targets
            dividedDamage
            lastKnownPower
            lastKnownToughness
            sourceName
            cardPower
            steps := combined } }
  | .gainLife n amount =>
    g.applyGainLife controller ab sourceId targets n amount sequencedCardPower
      lastKnownPower
  | .exile what how note =>
    g.applyExile controller ab sourceId targets what how note
  | .may (.put (.creatureFromHand subtype maxMv) _ _) (.draw (.fixed _) _) =>
    g.mayPutHeroOrDraw controller maxMv subtype
  | .put what how note | .may (.put what how note) _ =>
    g.applyPut controller ab sourceId targets what how note
  | .removeCounters what who =>
    g.applyRemoveCounters sourceId what who
  | .tap who | .may (.tap who) _ =>
    g.applyTap controller ab sourceId targets who
  | .untap who =>
    g.applyUntap controller ab sourceId targets who
  | .destroy what note =>
    g.applyDestroy controller ab sourceId targets lastKnownPower what note
  | .recruit _ =>
    g.beginRecruit controller
  | .putCounters what who =>
    g.applyPutCounters controller ab sourceId targets lastKnownPower what who
  | .amass n subtype amount attachSource who =>
    g.applyAmass controller sourceId lastKnownPower n subtype amount attachSource who
  | .createTokens kind n tapped token who qty note =>
    g.applyCreateTokens controller sourceId targets lastKnownPower
      kind n tapped token who qty note
  | .attach what host =>
    g.applyAttach controller ab sourceId targets what host
  | .addMana types amount =>
    g.applyAddMana controller sourceId types amount
  | .becomePT p t =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield then
        g.beginFraChoice controller (.mayBecomeBasePT o.id p t)
          s!"{(g.player controller).name} may have {o.name}'s base power and toughness become {p}/{t}"
      else g
    | none => g
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
  | .gainControl how =>
    match how with
    | .untilEndOfTurn =>
      g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
        let g := g.giveControlUntilEot o controller
        let g := g.applyPermanentAction (g.object! o.id) .untap
        g.mapObjectStatus (g.object! o.id) (·.grantUntilEot Keyword.haste))
    | .whileSourceRemains =>
      g.gainControlWhileSource controller sourceId targets
    | .duringNextTurn =>
      g.withLegalKindPlayer controller .opponent targets (fun g pid =>
        let g := g.setPlayerControl controller pid
        { g with controlOnNextTakenTurn := true })
        sourceId (some "The target is no longer legal")
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
  | .noteResolveThisTurn limit =>
    let n := (g.player controller).belladonnaResolvesThisTurn + 1
    let g := g.modifyPlayer controller (fun pl =>
      { pl with belladonnaResolvesThisTurn := n })
    let g := { g with nthResolveThisWay := some n }
    if n > limit then
      let name :=
        match sourceId.bind g.findObject? with
        | some o => o.name
        | none => sourceName
      g.logMsg s!"{name}'s ability has no effect (resolved {n} times this turn)"
    else g
  | .«if» .anotherHero (.dealDamage (.fixed 1) (.player .targetOpponent)) =>
    let (g, holds) :=
      g.triggerIfHolds controller ab sourceId targets lastKnownPower .anotherHero
    if holds then
      g.applyTriggeredAbility controller ab sourceId targets dividedDamage
        lastKnownPower lastKnownToughness sourceName
        (some (.dealDamage (.fixed 1) (.player .targetOpponent))) sequencedCardPower
    else
      g.logMsg "Human Torch's ability has no effect"
  | .«if» cond thenDo =>
    let (g, holds) :=
      g.triggerIfHolds controller ab sourceId targets lastKnownPower cond
    if holds then
      g.applyTriggeredAbility controller ab sourceId targets dividedDamage
        lastKnownPower lastKnownToughness sourceName (some thenDo) sequencedCardPower
    else g
  | .ifElse cond whenTrue whenFalse =>
    let (g, holds) :=
      g.triggerIfHolds controller ab sourceId targets lastKnownPower cond
    let branch := if holds then whenTrue else whenFalse
    g.applyTriggeredAbility controller ab sourceId targets dividedDamage
      lastKnownPower lastKnownToughness sourceName (some branch) sequencedCardPower
  | .or rs =>
    match rs with
    | [] => g
    | [r] =>
      g.applyTriggeredAbility controller ab sourceId targets dividedDamage
        lastKnownPower lastKnownToughness sourceName (some r) sequencedCardPower
    | rs =>
      let hasPermanent :=
        match targets[0]? with
        | some (Target.permanent _) => true
        | _ => false
      if ab.targetKind == .nonland && !hasPermanent then
        g.logMsg "The target is no longer legal"
      else
        { g with
            pending := .chooseTriggerOr controller
            triggerOr := some {
              controller
              ability := ab
              sourceId
              targets
              dividedDamage
              lastKnownPower
              lastKnownToughness
              sourceName
              cardPower := sequencedCardPower
              alternatives := rs.toArray } }.logMsg
          (triggerOrLog (g.player controller).name rs)
  | .may (.sacrifice .another _) _ =>
    g.applySacrifice controller ab sourceId targets .another .none
  | .markRecentTokensAttacking =>
    let dest := some g.defendingPlayer
    let g :=
      g.recentTokenIds.foldl (fun g id =>
        match g.findObject? id with
        | some o =>
          g.setObject { o with status := { o.status with
            attacking := true, attackingWhom := dest } }
        | none => g) g
    g.logMsg
      s!"{(g.player controller).name} creates two tapped and attacking Spirit tokens"
  | .additionalCombatPhase =>
    { g with additionalCombatPhases := g.additionalCombatPhases + 1 }.logMsg
      "Attacking creatures untap. After this phase, there is an additional combat phase"
  | .chooseModes modes how =>
    match how with
    | .plusOneOrRemoveCounter =>
      g.offerHydeChoice controller sourceId
    | .alreadyChosen =>
      let chosen :=
        match sourceId.bind g.findObject? with
        | some o => o.status.chosenModes
        | none => #[]
      chosen.foldl (init := g) fun g idx =>
        match modes[idx]? with
        | none => g
        | some r =>
          g.applyChooseModeStep targets r (fun g r =>
            g.applyTriggeredAbility controller ab sourceId targets dividedDamage
              lastKnownPower lastKnownToughness sourceName (some r)
              sequencedCardPower)
    | .oneUnusedThisTurn | .oneUnused =>
      g.offerChooseModes controller ab sourceId targets dividedDamage
        lastKnownPower lastKnownToughness sourceName sequencedCardPower modes how
    | .vision =>
      g.offerVisionModes controller ab sourceId targets lastKnownPower sourceName
    | .fromLastKnown =>
      match modes[(lastKnownPower.getD 0).toNat]? with
      | none => g
      | some r =>
        g.applyTriggeredAbility controller ab sourceId targets dividedDamage
          lastKnownPower lastKnownToughness sourceName (some r) sequencedCardPower
  | .returnToHand what note =>
    g.applyReturnToHand controller ab sourceId targets what note
  | .may (.discard .hand) _ =>
    g.applyDiscard controller sourceId targets .hand
  | .becomeBear =>
    match targets[0]? with
    | some (Target.permanent oid) =>
      match g.findObject? oid with
      | some o =>
        if g.hasSubtype o "Bear" then g
        else
          let g := g.setObject { o with status :=
            { o.status with additionalSubtypes := o.status.additionalSubtypes.push "Bear" } }
          g.logMsg s!"{o.name} becomes a Bear in addition to its other types"
      | none => g
    | _ => g
  | .mayCast origin maxMv cost note =>
    g.applyMayCast controller lastKnownPower origin maxMv cost note
  | .mill n who amount note =>
    g.applyMill controller ab sourceId targets lastKnownPower lastKnownToughness
      n who amount note
  | .grant what who =>
    g.applyGrant controller ab sourceId targets what who
  | .revealLibrary how thenDo who =>
    g.applyRevealLibrary controller sourceId targets how thenDo who
  | .fight who how =>
    g.applyFight controller sourceId targets who how
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
  | .loseLife n who amount =>
    g.applyLoseLife controller ab sourceId targets n who amount lastKnownPower
  | .may (.draw _ .opponentHasYou) _ =>
    g.applyTriggerDraw controller sourceId (.fixed 1) .opponentHasYou
  | .may (.sequence [.draw .equalToManaSpent _, .«if» .manaSpent (.discard (.cards n))]) _ =>
    -- X is the mana spent to cast the triggering spell.
    let spent := ((g.resolvingAbilityObject?.bind (·.fraCauseStatus)).map (·.manaSpentToCast)).getD 0
    if spent == 0 then g.logMsg "No mana was spent to cast that spell"
    else
      let disc := if n == 2 then "two" else toString n
      g.beginFraChoice controller (.mayDrawThenDiscard spent n)
        s!"{(g.player controller).name} may draw {spent} cards, then discard {disc}"
  | .winTheGame =>
    -- Ruling 835: you win while the ability resolves, before the
    -- state-based action for drawing from an empty library.
    { g with result := some (.won controller) }.logMsg
      s!"{(g.player controller).name} wins the game"
  | .shuffleSource =>
    g.shuffleSourceIntoLibrary sourceId
  | .ringTempts =>
    g.temptWithTheRing controller
  | .spellsCostLess which n =>
    match which with
    | .cardType ty => g.grantTypeCostLessThisTurn controller ty n
    | .supertype s => g.grantSupertypeCostLessThisTurn controller s n
  | .investigate =>
    let (g, _) := g.createToken controller clueToken
    g.logMsg s!"{(g.player controller).name} investigates"
  | .connive who =>
    match who with
    | .source => g.applyConnive controller sourceId
    | .target _ =>
      match targets[0]? with
      | some (Target.permanent id) => g.applyConnive controller (some id)
      | _ => g.applyConnive controller sourceId
    | .enteringVillain =>
      match sourceId.bind g.findObject? with
      | none =>
        g.logMsg "Baron Strucker is no longer on the battlefield. The ability has no effect."
      | some src =>
        if src.status.optionalOnceUsed then
          g.logMsg
            "The optional connive was already chosen this turn. This instance has no effect."
        else
          match g.villainConniveTarget? controller src.id targets lastKnownPower with
          | none => g.logMsg "The Villain does not connive"
          | some vid => g.beginMayHaveVillainConnive controller src.id vid
  | .grantPlayNotedUntilNextTurn =>
    match g.playExiledThisWay with
    | none => g
    | some newId =>
      let g := { g with playExiledThisWay := none }
      match g.findObject? newId with
      | some o =>
        let name := o.name
        let g := g.setObject { o with
          playPermission := some { player := controller, turnEndsRemaining := 2 } }
        g.logMsg
          s!"{(g.player controller).name} exiles {name} and may play it until the end of their next turn"
      | none => g
  | .revealFromHand count thenDo =>
    g.applyRevealFromHand controller sourceId targets count thenDo
  | .surveil n =>
    let armed := g.armSurveilReturn
    let life := (g.player controller).lifeGainedThisTurn
    let g := { g with armSurveilReturn := false }
    let g := g.beginSurveil controller n
    if armed then
      match g.pending with
      | .surveil _ _ => { g with surveilReturnMvAtMost := some life }
      | _ => g
    else g
  | .empowerJace n =>
    g.empowerJace controller n
  | .prepareSource .ifNotPrepared =>
    match sourceId.bind g.findObject? with
    | some o =>
      if !o.isOnBattlefield then g.logMsg s!"{o.name} is no longer on the battlefield"
      else if o.status.prepared then g.logMsg s!"{o.name} is already prepared"
      else g.becomePrepared o
    | none => g.logMsg "The source is no longer on the battlefield"
  | .armSurveilReturnLifeGained =>
    -- Ruling 750: the following surveil reads life gained as this ability resolves.
    { g with armSurveilReturn := true }
  | .prepareSource .ifThreeCreaturesDied =>
    if g.battlefieldCreaturesToGyThisTurn.size < 3 then
      g.logMsg "Fewer than three creatures died this turn"
    else
      match sourceId.bind g.findObject? with
      | some o =>
        if o.isOnBattlefield then g.becomePrepared o
        else g.logMsg s!"{o.name} is no longer on the battlefield"
      | none => g.logMsg "The source is no longer on the battlefield"
  | .becomeCopy of =>
    g.applyBecomeCopy controller sourceId targets of
  | .retargetCause =>
    let targetingSource (e : StackEntry) : Bool :=
      e.targets.any (fun t =>
        match t, sourceId with
        | Target.permanent id, some sid => id == sid
        | _, _ => false)
    let fromStack :=
      g.stack.foldl (fun acc e =>
        if targetingSource e then some e.objectId else acc) none
    match g.resolvingCauseId.orElse (fun _ => fromStack) with
    | none => g
    | some spellId => g.offerSpellRetarget controller spellId 0
  | .may (.loseLife 2 .you .fixed)
      (.grant .assignCombatDamageEqualToughness .creaturesYouControl) .ifYouDo =>
    g.offerPay2LifeToughness controller
  | .may (.exile .top .playThisTurn .ifHero) (.sequence []) _ =>
    g.offerExileTopHeroPump controller sourceId
  | .copyCause =>
    g.copyCastTriggerSpell controller
  | .may (.exile .discarded .playUntilNextTurn) (.sequence []) .ifYouDo =>
    g.offerMayExileDiscarded controller lastKnownPower
  | .may (.draw (.perControlled ty) _) (.draw (.fixed 1) .eachOpponent) .ifYouDo =>
    g.mayDrawPerArtifact controller ty
  | .may (.draw (.fixed 1) _) (.sequence []) .ifYouDo =>
    g.ifPaid (lastKnownPower.getD 1).toNat "The optional draw was declined"
      fun g => g.draw controller 1
  | .may (.dealDamage .lastKnownPower .target .none) (.sequence []) .ifYouDo =>
    if g.sheHulkDamageUsedThisTurn then
      g.logMsg "The Sensational She-Hulk already dealt damage this turn. The ability has no effect."
    else
      let legal := g.legalTargetsForKind controller .playerOrCreature sourceId
      match targets.find? (legal.contains ·) with
      | none => g.logMsg "The target is no longer legal"
      | some t =>
        let amt := lastKnownPower.getD 0
        { g with pending := .fraChoice controller (.sheHulkMayDamage amt t sourceId) }
          |>.logMsg "You may have The Sensational She-Hulk deal that much damage"
  | .may .retargetCause (.sequence []) .ifYouDo =>
    g.applyTriggeredAbility controller ab sourceId targets dividedDamage
      lastKnownPower lastKnownToughness sourceName (some .retargetCause)
      sequencedCardPower
  | .may (.pay (.mana symbols)) (.queueReflexive followup) .ifYouDo =>
    -- Paying more than once records that count for the reflexive ability.
    match TriggeredAbility.TriggerResolution.queuedReflexive followup with
    | .modeled kind times =>
      if times > 1 then
        g.offerPayForReflexive controller sourceId symbols kind times
      else
        let follow := TriggeredAbility.TriggerResolution.queueReflexive followup
        let g := { g with mayThenDrop := 1, mayThenConditional := some follow }
        g.applyTriggeredAbility controller ab sourceId targets dividedDamage
          lastKnownPower lastKnownToughness sourceName
          (some (.sequence [.pay (.mana symbols), follow])) sequencedCardPower
    | _ =>
      let follow := TriggeredAbility.TriggerResolution.queueReflexive followup
      let g := { g with mayThenDrop := 1, mayThenConditional := some follow }
      g.applyTriggeredAbility controller ab sourceId targets dividedDamage
        lastKnownPower lastKnownToughness sourceName
        (some (.sequence [.pay (.mana symbols), follow])) sequencedCardPower
  | .may (.createTokens .wall04defender 1 false) (.sequence []) .ifYouDo =>
    g.offerMayCreateWall controller
  | .may optional conditional .ifYouDo =>
    let cond := TriggeredAbility.TriggerResolution.flatten conditional
    let g := { g with mayThenDrop := cond.length, mayThenConditional := some conditional }
    g.applyTriggeredAbility controller ab sourceId targets dividedDamage
      lastKnownPower lastKnownToughness sourceName
      (some (.sequence (optional :: cond))) sequencedCardPower
  | .pay what =>
    match what with
    | .mana symbols =>
      match g.mayThenConditional, symbols.toList with
      | some (.queueReflexive followup), _ =>
        match TriggeredAbility.TriggerResolution.queuedReflexive followup with
        | .modeled kind times =>
          g.offerPayForReflexive controller sourceId symbols kind times
        | _ =>
          match symbols.toList with
          | [.generic n] =>
            let g := { g with pending := .mayPayGeneric controller n }
            g.logMsg s!"{(g.player controller).name} may pay \{{n}}. If they do, they draw a card"
          | _ =>
            match sourceId.bind g.findObject? with
            | none =>
              (g.logMsg "The ability's source is no longer in the graveyard").failMayThen
            | some src =>
              if src.zone != .graveyard src.owner then
                (g.logMsg s!"{src.name} is no longer in the graveyard").failMayThen
              else
                let shown := String.join (symbols.toList.map ManaSymbol.toNotation)
                g.beginFraChoice controller (.mayPaySymbolsThen symbols .returnSourceToHand src.id)
                  s!"{(g.player controller).name} may pay {shown} to return {src.name} to their hand"
      | some (.becomeCopy .cause), [.generic 2] =>
        g.offerCopyCause controller sourceId targets
      | _, _ =>
        match symbols.toList with
        | [.generic n] =>
          let plusOne :=
            match g.mayThenConditional with
            | some (.sequence [.putCounters (.ofKind .plusOnePlusOne 1) .source, .draw (.fixed 1)]) => true
            | _ => false
          let g := { g with pending := .mayPayGeneric controller n }
          g.logMsg <|
            if plusOne then
              s!"{(g.player controller).name} may pay \{{n}} to put a +1/+1 counter on it and draw a card"
            else
              s!"{(g.player controller).name} may pay \{{n}}. If they do, they draw a card"
        | _ =>
          match sourceId.bind g.findObject? with
          | none =>
            (g.logMsg "The ability's source is no longer in the graveyard").failMayThen
          | some src =>
            if src.zone != .graveyard src.owner then
              (g.logMsg s!"{src.name} is no longer in the graveyard").failMayThen
            else
              let shown := String.join (symbols.toList.map ManaSymbol.toNotation)
              g.beginFraChoice controller (.mayPaySymbolsThen symbols .returnSourceToHand src.id)
                s!"{(g.player controller).name} may pay {shown} to return {src.name} to their hand"
    | .anotherCreature =>
      let reflexive :=
        match g.mayThenConditional with
        | some (.queueReflexive _) => true
        | _ => false
      match sourceId with
      | some sid =>
        if reflexive then
          let pick := CostPick.sacrificeAnotherSubtype "Creature"
          if (g.costPickCandidates controller sid pick).isEmpty then
            (g.logMsg "There is no other creature to sacrifice. The reflexive ability doesn't trigger.").failMayThen
          else
            g.beginFraChoice controller (.mayPayPickThen pick (.mshReflexive 7 0) sid)
              s!"{(g.player controller).name} may sacrifice another creature"
        else
          let others := (g.creaturesControlledBy controller).filter (·.id != sid)
          if others.isEmpty then
            (g.logMsg "No other creature to sacrifice").failMayThen
          else
            g.beginFraChoice controller (.maySacrificeAnotherCreatureForPower sid)
              s!"{(g.player controller).name} may sacrifice another creature"
      | none =>
        if reflexive then g.failMayThen
        else (g.logMsg "No other creature to sacrifice").failMayThen
    | .anotherCreatureOrArtifact =>
      match sourceId with
      | none => (g.logMsg "Nothing to sacrifice").failMayThen
      | some sid =>
        let any := (g.permanentsOf controller).any (fun o =>
          o.id != sid && (o.isCreature || o.printed.isArtifact))
        if !any then (g.logMsg "Nothing to sacrifice").failMayThen
        else
          g.beginFraChoice controller (.maySacrificeAnotherForDrawTreasure sid)
            s!"{(g.player controller).name} may sacrifice another creature or artifact"
    | .artifactOrDiscard =>
      { g with pending := .maySacArtifactOrDiscard controller 1 }.logMsg
        s!"{(g.player controller).name} may sacrifice an artifact or discard a card. If they do, they draw a card"
    | .artifactOrDiscardNonland =>
      match sourceId with
      | some sid =>
        if (g.costPickCandidates controller sid .sacrificeArtifactOrDiscardNonland).isEmpty then
          g.failMayThen
        else
          g.beginFraChoice controller
            (.mayPayPickThen .sacrificeArtifactOrDiscardNonland (.reflexiveDamageAnyTarget 2) sid)
            s!"{(g.player controller).name} may sacrifice an artifact or discard a nonland card"
      | none => g.failMayThen
  | .queueReflexive followup =>
    match TriggeredAbility.TriggerResolution.queuedReflexive followup with
    | .modeled kind _ => g.queueModeledReflexive controller sourceId kind 0
    | .counters kind =>
      match sourceId.bind g.findObject? with
      | some o =>
        if o.isOnBattlefield then
          g.queueModeledReflexive controller sourceId kind o.status.plusOnePlusOne
        else
          g.logMsg "Red Hulk is no longer on the battlefield. The reflexive ability doesn't trigger."
      | none =>
        g.logMsg "Red Hulk is no longer on the battlefield. The reflexive ability doesn't trigger."
    | .damage n =>
      g.putReflexiveTrigger controller sourceId
        { targeting := .of .playerOrCreature, resolution := .fra (.damageAny n)
          phrase := s!"This deals {n} damage to any target" }
    | .copy =>
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
    | .divided amount =>
      g.putReflexiveTrigger controller sourceId {
        targeting := .of .playerOrCreature
        dividedDamage := some (amount, 2)
        resolution := .fra (.mshReflexive 10 0)
        phrase := s!"It deals {amount} damage divided as you choose among one or two targets" }
    | .attackPump =>
      g.attackPumpPerPlains controller
    | .none => g
  | .may _ _ =>
    g.logMsg s!"{(g.player controller).name}'s optional action doesn't resolve")
  | r =>
    g.applyUnifiedAbility controller { ab.effect with resolution := r }
      targets sourceId lastKnownPower

/-- Finish trigger-sequence steps that waited on a pending choice.
Those steps are still part of the resolution that opened the choice. -/
def resumeTriggerSequence (g : Game) : Game :=
  match g.triggerSequenceRest with
  | none => g
  | some c =>
    let g := { g with triggerSequenceRest := none }
    g.applyTriggeredAbility c.controller c.ability c.sourceId c.targets
      c.dividedDamage c.lastKnownPower c.lastKnownToughness c.sourceName
      (some (.sequence c.steps)) c.cardPower

/-- Record that `sourceId` has used mode `idx`, as `how` says. -/
def rememberChosenMode (g : Game) (sourceId : ObjectId)
    (how : TriggeredAbility.TriggerModeHow) (mode : Nat) : Game :=
  match how, g.findObject? sourceId with
  | .alreadyChosen, _ | .plusOneOrRemoveCounter, _ | .fromLastKnown, _ => g
  | _, none => g.logMsg "The ability is removed from the stack with no effect"
  | .oneUnusedThisTurn, some src =>
    g.setObject { src with status :=
      { src.status with allianceModesChosen := src.status.allianceModesChosen.push mode } }
  | .vision, some src =>
    if src.isOnBattlefield then
      g.setObject { src with status :=
        { src.status with modesChosenThisTurn := src.status.modesChosenThisTurn.push mode } }
    else g
  | .oneUnused, some src =>
    g.setObject { src with status :=
      { src.status with chosenModes := src.status.chosenModes.push mode } }

/-- Apply one stored `chooseModes` resolution with the ability context from
the offer. -/
def applyListedMode (g : Game) (rest : ChooseModesRest)
    (r : TriggeredAbility.TriggerResolution) : Game :=
  g.applyChooseModeStep rest.targets r fun g r =>
    g.applyTriggeredAbility rest.controller rest.ability rest.sourceId rest.targets
      rest.dividedDamage rest.lastKnownPower rest.lastKnownToughness rest.sourceName
      (some r) rest.cardPower

/-- Apply one stored Vision mode. A source that has left still draws, and
does not gain a keyword or record the choice. -/
def resolveVisionChoice (g : Game) (rest : ChooseModesRest) (mode : Nat) : Game :=
  let controller := rest.controller
  match rest.sourceId.bind (fun id => g.findObject? (g.followMoved id)) with
  | none =>
    match rest.modes[mode]? with
    | some (.draw (.fixed _)) => g.draw controller 1
    | _ => g.logMsg "The Vision is no longer in play"
  | some src =>
    if src.status.modesChosenThisTurn.contains mode ||
        src.status.modesChosenThisTurn.size >= 3 then
      g.logMsg "The Vision's ability is removed from the stack with no effect"
    else if !src.isOnBattlefield then
      match rest.modes[mode]? with
      | some (.draw (.fixed _)) => g.draw controller 1
      | _ => g.logMsg "The Vision is no longer in play"
    else
      let g := g.mapObjectStatus src (fun s =>
        { s with modesChosenThisTurn := s.modesChosenThisTurn.push mode })
      match rest.modes[mode]? with
      | none => g
      | some r => g.applyListedMode rest r

/-- Apply mode `idx` from `chooseModesRest` when the offer stored one.
Otherwise `fallback` is the direct Alliance, Gollum, or Vision resolution. -/
def answerChooseMode (g : Game) (sourceId : ObjectId) (idx : Nat)
    (fallback : Game → Game) : Game :=
  match g.chooseModesRest with
  | none => fallback g
  | some rest =>
    let g := { g with chooseModesRest := none }
    match rest.how with
    | .vision => g.resolveVisionChoice rest idx
    | _ =>
      let g := g.rememberChosenMode sourceId rest.how idx
      if (g.findObject? sourceId).isNone then g
      else
        match rest.modes[idx]? with
        | none => g
        | some r => g.applyListedMode rest r

/-- Apply alternative `idx` of a pending `TriggerResolution.or`. -/
def chooseTriggerOr (g : Game) (p : PlayerId) (idx : Nat) : Except String Game := do
  match g.pending, g.triggerOr with
  | .chooseTriggerOr q, some rest =>
    if p != q then throw s!"Only {(g.player q).name} may choose"
    match rest.alternatives[idx]? with
    | none => throw "No such choice"
    | some r =>
      let g := { g with pending := .none, triggerOr := none }
      let g := g.applyTriggeredAbility rest.controller rest.ability rest.sourceId
        rest.targets rest.dividedDamage rest.lastKnownPower rest.lastKnownToughness
        rest.sourceName (some r) rest.cardPower
      if g.pending != .none || g.over then return g
      let g := g.resumeTriggerSequence
      if g.pending != .none || g.over then return g
      return g.receivePriority g.activePlayer
  | _, _ => throw "Not time to choose"

/-- Put attack-triggered abilities of `attackerIds` onto the stack (CR 508.2),
including “whenever you attack with one or more Elves” (once if any Elf attacks). -/
def putAttackTriggersOnStack (g : Game) (p : PlayerId) (attackerIds : Array ObjectId) : Game :=
  Id.run do
    let mut g := g
    for id in attackerIds do
      let o := g.object! id
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
