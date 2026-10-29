import Mtg.Engine.Game.TriggerArgs

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
  | .scry .. => g.change (.palantirAfterScry (some (controller, opp, sid)))
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
        (g.combatDamageToPlayers o.id).contains controller)).map (·.id)
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
  let (g, cause) := g.allocDelayedCause (some controller)
  let (g, found, others) := g.exileUntilInstantOrSorcery victim (cause := some cause)
  match found with
  | none =>
    g.requestOrderInto others (.library victim)
      s!"{(g.player victim).name} randomizes the exiled cards; they become that player's library"
      (cause := some cause)
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
    let chosen := g.modesChosenThisTurn sourceId
    if chosen.size >= 3 || (g.unusedAllianceModes src).isEmpty then
      g.logMsg
        "all three modes have been chosen this turn. The ability is removed from the stack with no effect"
    else if chosen.contains mode then
      g.logMsg "That Alliance mode has already been chosen this turn"
    else
      let g := g.record (GameEvent.triggerModeChosen g.turnNumber sourceId mode)
      match g.controllerOf src, mode with
      | some c, 0 =>
        let g := g.changePlayer c (.addMana (.colored .green) 3)
        g.logMsg s!"{(g.player c).name} adds \{G}\{G}\{G}"
      | some c, 1 =>
        let creatures := (g.battlefield.filter (fun o => g.isCreature o && g.controlledBy o c)).map (·.id)
        let g := g.withBatch none fun g =>
          creatures.foldl (fun g id =>
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
    let chosen := g.modesChosenEver sourceId
    if (g.unusedGollumModes src).isEmpty then
      g.logMsg
        "all three modes have been chosen. The ability is removed from the stack with no effect"
    else if chosen.contains mode then
      g.logMsg "That mode has already been chosen"
    else
      let g := g.record (GameEvent.triggerModeChosen g.turnNumber sourceId mode (lifetime := true))
      match g.controllerOf src, mode with
      | some _, 0 =>
        g.addPlusOnePlusOneTo (g.object! sourceId) 1
      | some c, 1 =>
        g.eachOpponentLosesYouGain c 2
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
      | .oneUnusedThisTurn | .vision => g.modesChosenThisTurn src.id
      | .oneUnused | .alreadyChosen | .plusOneOrRemoveCounter | .fromLastKnown =>
        g.modesChosenEver src.id
    let available := unusedModes memory (List.range modes.length).toArray
    match g.controllerOf src with
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
          g.changes #[
            .pending (.fraChoice p (.allianceMode src.id available)),
            .chooseModesRest (some rest)]
            |>.logMsg s!"{(g.player p).name} chooses an Alliance mode that hasn't been chosen this turn"
        | .oneUnused =>
          g.changes #[
            .pending (.fraChoice p (.gollumMode src.id available)),
            .chooseModesRest (some rest)]
            |>.logMsg s!"{(g.player p).name} chooses a mode that hasn't been chosen"
        | .vision =>
          g.changes #[
            .pending (.fraChoice p (.visionMode src.id available)),
            .chooseModesRest (some rest)]
            |>.logMsg "Choose one that hasn't been chosen this turn"
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
        let name := g.name o
        (g.move id (.graveyard o.owner) none).1.logMsg s!"{name} is sacrificed"
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

/-- Put `chosen` from the revealed cards onto the battlefield, then the other
revealed cards on the bottom of their owner's library in a random order. -/
def resolveRandomCreatureReveal (g : Game) (p : PlayerId) (revealed : Array ObjectId)
    (chosen : ObjectId) (cause : Option EventCause := none) : Game :=
  let stashed :=
    cause.orElse (fun _ => g.stashedCause.orElse (fun _ => revealed[0]?.bind g.lastMoveCauseOf?))
  let g := if g.stashedCause.isSome then g.change (.stashedCause none) else g
  let (g, cause) : Game × Option EventCause :=
    match stashed with
    | some c => (g, some c)
    | none =>
      let (g, c) := g.allocDelayedCause (some p)
      (g, some c)
  let g :=
    match g.findObject? chosen with
    | some o =>
      let name := o.name
      let (g, newId) := g.putOntoBattlefield chosen p (cause := cause)
      let g := g.logMsg s!"{name} enters the battlefield"
      g.afterPermanentEnters (g.object! newId)
    | none => g
  let rest := revealed.filter (· != chosen)
  let libraryOwner :=
    match rest[0]?.bind g.findObject? with
    | some o => o.owner
    | none => p
  g.putRestOnBottomRandom libraryOwner rest (cause := cause)

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

/-- Power and toughness of the cause, then of the source.
`none` when the source is missing or has left, there is no cause, or the
cause is the source. A missing or departed source is reported. -/
def causeAndSourcePT? (g : Game) (sourceId : Option ObjectId) (targets : Array Target) :
    Game × Option (Int × Int × Int × Int) :=
  match sourceId.bind g.findObject? with
  | none => (g.logMsg "The source is no longer in play", none)
  | some src =>
    if !src.isOnBattlefield then
      (g.logMsg s!"{src.name} is no longer on the battlefield", none)
    else
      let cause :=
        match targets[0]? with
        | some (Target.permanent id) | some (Target.card id) => g.findObject? id
        | _ => g.resolvingCauseId.bind g.findObject?
      match cause with
      | none => (g, none)
      | some other =>
        if other.id == src.id then (g, none)
        else
          let op :=
            if other.isOnBattlefield then g.power other
            else (g.lastKnownPowerOf? other.id).getD (g.power other)
          let ot :=
            if other.isOnBattlefield then g.toughness other
            else (g.lastKnownToughnessOf? other.id).getD (g.toughness other)
          (g, some (op, ot, g.power src, g.toughness src))

/-- Whether `cond` holds as this trigger resolves. One-shot notes that the
action does not read are cleared here. -/
def triggerIfHolds (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target) (lastKnownPower : Option Int)
    (cond : TriggeredAbility.ConditionSelector) : Game × Bool :=
  match cond with
  | (.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1)) => (g, g.controlsLegendaryCreature controller)
  | .not cond =>
    let (g, holds) :=
      g.triggerIfHolds controller ab sourceId targets lastKnownPower cond
    (g, !holds)
  | .or conds =>
    -- Once one condition holds, later ones are not checked. A later condition
    -- that only repeats the log lines of the previous one does not report
    -- them again, so a shared failure is reported once.
    let rec go (g : Game) (cs : List TriggeredAbility.ConditionSelector)
        (prev : Option (Array String)) : Game × Bool :=
      match cs with
      | [] => (g, false)
      | c :: rest =>
        let start := g.log.size
        let (g, holds) :=
          g.triggerIfHolds controller ab sourceId targets lastKnownPower c
        if holds then (g, true)
        else
          let added := g.log.extract start g.log.size
          let g :=
            match prev with
            | some earlier =>
              if !added.isEmpty && added == earlier then
                g.change (.log (g.log.extract 0 start))
              else g
            | none => g
          go g rest (some added)
    go g conds none
  | .removedHope =>
    let removed := g.removedHopeThisWay
    (g.change (.removedHopeThisWay false), removed)
  | .hopeOnSource =>
    match sourceId.bind g.findObject? with
    | some src => (g, !(src.isOnBattlefield && src.status.hope == 0))
    | none => (g, true)
  | .dealtDamageToSubtype subtype =>
    match g.permanentDealtDamageThisWay with
    | none => (g, false)
    | some oid =>
      match g.findObject? oid with
      | some o =>
        if o.isOnBattlefield && g.hasSubtype o subtype then (g, true)
        else (g.change (.permanentDealtDamageThisWay none), false)
      | none => (g.change (.permanentDealtDamageThisWay none), false)
  | .attackedWithSubtype subtype =>
    (g, g.loggedAttackedWithSubtype controller subtype)
  | .subtypeEntered subtype =>
    (g, g.loggedSubtypeEntered controller subtype)
  | (.atLeast (.count .landsYouControl) (.fixed n)) =>
    let n := n.toNat
    let lands := ((g.permanentsOf controller).filter (g.isLand ·)).size
    if lands < n then
      let g :=
        if n == 6 then
          g.logMsg "You control fewer than six lands. The ability doesn't resolve (ruling 889)"
        else g
      (g, false)
    else (g, true)
  | (.atLeast (.count .planeswalkersYouControl) (.fixed 1)) =>
    if (g.permanentsOf controller).any (g.isPlaneswalker ·) then
      (g.logMsg "You control a planeswalker. The ability does nothing", true)
    else (g, false)
  | (.atLeast (.count .forestsExceptCause) (.fixed n)) =>
    -- Rulings 818 / 819: count Forests other than the one that caused the
    -- trigger, whether or not that one is still on the battlefield.
    let cause : Option ObjectId := lastKnownPower.map (fun k => ⟨k.toNat⟩)
    let others := ((g.permanentsOf controller).filter (fun o =>
      g.hasSubtype o .forest && some o.id != cause)).size
    let n := n.toNat
    if others < n then
      let g :=
        if n == 5 then
          g.logMsg "You control fewer than five other Forests. The ability doesn't resolve"
        else g
      (g, false)
    else (g, true)
  | .returnedPermanent =>
    let returned := g.returnedPermanentThisWay
    (g.change (.returnedPermanentThisWay false), returned)
  | .nthResolve n => (g, g.nthResolveThisWay == some n)
  | .youControlledDestroyed =>
    let draw? := g.destroyedForAmassThisWay && g.amassYouControlledThisWay
    let g := g.changes #[
      .destroyedForAmassThisWay false,
      .amassControllerThisWay none,
      .amassAmountThisWay 0,
      .amassYouControlledThisWay false]
    (g, draw?)
  | .enduringStoryNoted =>
    match g.handDiscardedThisWay with
    | none => (g.change (.notedSourceThisWay none), false)
    | some n =>
      let srcId := g.notedSourceThisWay
      let holds :=
        g.hasEnduringStory controller && n != 0 &&
          (srcId.bind g.findObject?).any (·.isOnBattlefield)
      if holds then (g, true)
      else (g.changes #[.handDiscardedThisWay none, .notedSourceThisWay none], false)
  | (.atLeast (.count (.youControl (.subtype .bear))) (.fixed n)) =>
    (g, g.countSubtype controller .bear ≥ n.toNat)
  | (.atLeast (.count (.youControl (.subtype subtype))) (.fixed n)) =>
    (g, g.countSubtype controller subtype ≥ n.toNat)
  | .sourceWasSacrificed =>
    let yes := g.sourceWasSacrificed
    (g.change (.sourceWasSacrificed false), yes)
  | .planWasSacrificed =>
    let yes := g.planWasSacrificed
    (g.change (.planWasSacrificed false), yes)
  | (.atLeast (.count .questCounters) (.fixed n)) =>
    match sourceId.bind g.findObject? with
    | none => (g.logMsg "The triggered ability's source is no longer in play", false)
    | some src =>
      if src.isOnBattlefield then (g, src.status.quest ≥ n.toNat)
      else (g.logMsg s!"{src.name} is no longer on the battlefield", false)
  | .equipmentAttached =>
    match g.equipmentAttachedHost with
    | none => (g, false)
    | some hostId =>
      match g.findObject? hostId with
      | some host =>
        if host.isOnBattlefield then (g, true)
        else (g.change (.equipmentAttachedHost none), false)
      | none => (g.change (.equipmentAttachedHost none), false)
  | .opponentsMilled =>
    let milled := g.opponentsMilledThisWay
    (g.change (.opponentsMilledThisWay false), milled)
  | (.atLeast (.count (.othersOfSubtype .hero)) (.fixed 1)) =>
    (g, (g.permanentsOf controller).any (fun o =>
      g.hasSubtype o .hero && some o.id != sourceId))
  | (.atLeast (.count (.intersection [.equipped, .legendaryCreaturesYouControl])) (.fixed 1)) =>
    match sourceId.bind g.findObject? with
    | none => (g.logMsg "The Equipment is no longer in play", false)
    | some eq =>
      let hostOk :=
        match eq.attachedTo.bind g.findObject? with
        | some host =>
          host.isOnBattlefield && g.isLegendary host && g.controllerOf host == some controller
        | none => false
      if hostOk then (g, true)
      else
        (g.logMsg s!"{(g.player controller).name} creates two tapped Spirit tokens", false)
  | (.atLeast (.count .creature) (.fixed 1))
  | (.atLeast (.count (.target .creature)) (.fixed 1)) =>
    let (g, o?) := g.legalTriggerPermanent? controller ab sourceId targets
    match o? with
    | some o => (g, g.isCreature o)
    | none => (g, false)
  | (.atLeast (.count .planeswalker) (.fixed 1))
  | (.atLeast (.count (.target .planeswalker)) (.fixed 1)) =>
    let (g, o?) := g.legalTriggerPermanent? controller ab sourceId targets
    match o? with
    | some o => (g, g.isPlaneswalker o)
    | none => (g, false)
  | (.atLeast (.count .creatureCardsInGraveyard) (.fixed n)) =>
    let gy := ((g.player controller).graveyard.filter (fun id =>
      (g.object! id).printed.isCreature)).size
    (g, gy ≥ n.toNat)
  | (.atLeast (.count (.anotherSubtype subtype)) (.fixed 1))
  | (.atLeast (.count (.target (.anotherSubtype subtype))) (.fixed 1)) =>
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
  | .scriedThisTurn => (g, g.loggedScried controller)
  | .surveilledThisTurn => (g, g.loggedSurveilled controller)
  | (.atLeast (.count .putEquipment) (.fixed 1)) =>
    match g.putArtifactThisWay with
    | none => (g, false)
    | some (id, _) =>
      match g.findObject? id with
      | some o =>
        let isEq := if o.isOnBattlefield then g.isEquipment o else o.printed.isEquipment
        if isEq then (g, true)
        else (g.change (.putArtifactThisWay none), false)
      | none => (g.change (.putArtifactThisWay none), false)
  | .revealedManaValueAtMostLands =>
    match g.revealedIdsThisWay[0]?.bind g.findObject? with
    | some o => (g, o.printed.manaValue ≤ g.landsYouControl controller)
    | none => (g, false)
  | (.atLeast (.count .harnessedSource) (.fixed 1)) =>
    match sourceId.bind g.findObject? with
    | none => (g, false)
    | some src =>
      if src.status.harnessed then (g, true)
      else (g.logMsg "The Mind Stone is not harnessed", false)
  | .artifactEnteredThisTurn =>
    if g.loggedArtifactEntered controller then (g, true)
    else
      (g.logMsg
        "No artifact entered under your control this turn. Iron Man's ability doesn't trigger.",
        false)
  | .atLeast .equalSourcePower (.fixed n) =>
    let pw := g.sourcePowerAtResolution sourceId lastKnownPower
    if pw ≥ n then (g, true)
    else
      let g :=
        if n == 4 then g.logMsg "Viv Vision's power is not 4 or greater"
        else g.logMsg s!"Its power is not {n} or greater"
      (g, false)
  | .attachedEquipment =>
    let x := g.attachedEquipmentAtResolution sourceId lastKnownPower
    if x == 0 then (g.logMsg "Whiplash isn't equipped", false)
    else (g, true)
  | .enrageGrantsCombat =>
    let attacking :=
      match sourceId with
      | none => false
      | some sid =>
        match g.findObject? sid with
        | some o =>
          if o.isOnBattlefield then o.status.attacking
          else
            (g.events.reverse.findSome? fun e =>
              match e.change with
              | .rules (.zone (.moved before _ .battlefield _ ..)) =>
                if before.id == some sid then some before.attacking else none
              | _ => none).getD false
        | none =>
          (g.events.reverse.findSome? fun e =>
            match e.change with
            | .rules (.zone (.moved before _ .battlefield _ ..)) =>
              if before.id == some sid then some before.attacking else none
            | _ => none).getD false
    (g, attacking)
  | .causeGreaterPower =>
    let (g, stats?) := g.causeAndSourcePT? sourceId targets
    match stats? with
    | some (op, _, hp, _) => (g, op > hp)
    | none => (g, false)
  | .causeGreaterToughness =>
    let (g, stats?) := g.causeAndSourcePT? sourceId targets
    match stats? with
    | some (_, ot, _, ht) => (g, ot > ht)
    | none => (g, false)
  | .manaSpent =>
    let spent :=
      match g.resolvingAbilityObject?.bind (·.fraCauseId) with
      | some id => GameEvent.manaSpentOn g.events id
      | none => 0
    (g, spent > 0)
  | .atLeast (.count what) amount =>
    -- Printed counts above keep their logs and notes. Every other counted
    -- selector is the number of objects `what` names, compared with `amount`.
    let ctx : TriggerRead := { controller, sourceId, targets, lastKnownPower }
    let (g, counted) :=
      match what with
      | .creature | .target .creature =>
        let (g, o?) := g.legalTriggerPermanent? controller ab sourceId targets
        let n :=
          match o? with
          | some o => if g.isCreature o then 1 else 0
          | none => 0
        (g, some n)
      | .planeswalker | .target .planeswalker =>
        let (g, o?) := g.legalTriggerPermanent? controller ab sourceId targets
        let n :=
          match o? with
          | some o => if g.isPlaneswalker o then 1 else 0
          | none => 0
        (g, some n)
      | .anotherSubtype subtype | .target (.anotherSubtype subtype) =>
        let legal := g.legalTargetsForKind controller ab.targetKind sourceId
        let n :=
          match targets[0]? with
          | some (Target.permanent oid) =>
            if legal.contains (Target.permanent oid) then
              match g.findObject? oid with
              | some o => if g.hasSubtype o subtype && some o.id != sourceId then 1 else 0
              | none => 0
            else 0
          | _ => 0
        (g, some n)
      | .putEquipment =>
        match g.putArtifactThisWay with
        | none => (g, some 0)
        | some (id, _) =>
          match g.findObject? id with
          | some o =>
            let isEq := if o.isOnBattlefield then g.isEquipment o else o.printed.isEquipment
            if isEq then (g, some 1)
            else (g.change (.putArtifactThisWay none), some 0)
          | none => (g.change (.putArtifactThisWay none), some 0)
      | .questCounters =>
        match sourceId.bind g.findObject? with
        | none => (g.logMsg "The triggered ability's source is no longer in play", none)
        | some src =>
          if src.isOnBattlefield then (g, some src.status.quest)
          else (g.logMsg s!"{src.name} is no longer on the battlefield", none)
      | .intersection [.equipped, .legendaryCreaturesYouControl] =>
        match sourceId.bind g.findObject? with
        | none => (g.logMsg "The Equipment is no longer in play", some 0)
        | some eq =>
          let n :=
            match eq.attachedTo.bind g.findObject? with
            | some host =>
              if host.isOnBattlefield && g.isLegendary host && g.controllerOf host == some controller then
                1
              else 0
            | none => 0
          (g, some n)
      | .harnessedSource =>
        match sourceId.bind g.findObject? with
        | none => (g, some 0)
        | some src =>
          if src.status.harnessed then (g, some 1)
          else (g.logMsg "The Mind Stone is not harnessed", some 0)
      | _ => (g, g.countNamed ctx what)
    match g.triggerCount ctx amount, counted with
    | some k, some c => (g, c ≥ k)
    | _, _ => (g, false)
  | .atLeast left right =>
    -- Printed pairs above keep their logs. Every other pair compares the
    -- two numbers. A number that cannot be read does not hold.
    let ctx : TriggerRead := { controller, sourceId, targets, lastKnownPower }
    match g.triggerInt ctx left, g.triggerInt ctx right with
    | some a, some b => (g, a ≥ b)
    | _, _ => (g, false)
  | .subtype subtype =>
    let holds :=
      match targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some o => g.hasSubtype o subtype
        | none => false
      | some (Target.card id) =>
        match g.findObject? id with
        | some o => g.hasSubtype o subtype
        | none => false
      | _ => false
    (g, holds)
  | .mvAtMost n =>
    match targets[0]? with
    | some (Target.card id) =>
      match g.findObject? (g.followMoved id) with
      | some o =>
        let mv := o.printed.manaValue + (g.chosenXOf? o.id).getD 0
        (g, mv ≤ n)
      | none => (g, false)
    | _ => (g, false)
  | .teamwork =>
    (g, match g.resolvingSpell with
      | some id => GameEvent.teamwork g.events id
      | none => false)
  | .castFromGraveyard =>
    (g, match g.resolvingSpell with
      | some id => g.castFromGraveyard id
      | none => false)
  | .giftPromised =>
    (g, match g.resolvingSpell with
      | some id => GameEvent.giftPromised g.events id
      | none => false)

/-- Log line when a `TriggerResolution.or` asks the controller to choose. -/
def triggerOrLog (name : String) (rs : List TriggeredAbility.TriggerResolution) : String :=
  match rs with
  | [.createTokens .food (.fixed 1) false, .createTokens .treasure (.fixed 1) false] =>
    s!"{name} creates a Food token or a Treasure token"
  | [.tap .target, .untap .target] =>
    s!"{name} chooses tap or untap"
  | _ =>
    s!"{name} chooses one"

/-- Pending-header text for a `TriggerResolution.or` choice. -/
def triggerOrPendingText (rs : List TriggeredAbility.TriggerResolution) : String :=
  match rs with
  | [.createTokens .food (.fixed 1) false, .createTokens .treasure (.fixed 1) false] =>
    "create a Food token or a Treasure token"
  | [.tap .target, .untap .target] =>
    "choose tap or untap"
  | _ =>
    "choose one"

/-- The optional action of `mayThen` cannot be performed. Skip the conditional
steps still in this sequence. -/
def failMayThen (g : Game) : Game :=
  g.changes #[.mayThenSkip g.mayThenDrop, .mayThenDrop 0, .mayThenConditional none]

/-- Permanents that can pay `CostSelector.sacrifice` of `what`.
`.another` is each other creature. `.intersection` is the permanents every
selector names. `.union` is the permanents any selector names. Every other
selector is the permanents it names. A selector that does not name
permanents names none. -/
def sacrificeCostCandidates (g : Game) (ctx : TriggerRead)
    (what : TriggeredAbility.ObjectSelector) : Array GameObject :=
  match what with
  | .another =>
    match ctx.sourceId with
    | some sid => (g.creaturesControlledBy ctx.controller).filter (·.id != sid)
    | none => #[]
  | .intersection sels =>
    match sels with
    | [] => #[]
    | s :: rest =>
      rest.foldl (fun acc t => intersectObjects acc (g.sacrificeCostCandidates ctx t))
        (g.sacrificeCostCandidates ctx s)
  | .union sels =>
    sels.foldl (fun acc s => unionObjects acc (g.sacrificeCostCandidates ctx s)) #[]
  | _ =>
    (g.permanentsNamed ctx what).getD #[]

/-- Cards in the controller's hand that can pay `CostSelector.discard` of `what`.
`.card` is each card in that hand. `.nonland` is each nonland card.
`.intersection` is the cards every selector names. `.union` is the cards
any selector names. A selector that does not name cards in hand names none.
A permanent is not discarded. -/
def discardCostCandidates (g : Game) (controller : PlayerId)
    (what : TriggeredAbility.ObjectSelector) : Array GameObject :=
  let hand := (g.player controller).hand.filterMap g.findObject?
  match what with
  | .card => hand
  | .nonland => hand.filter (!·.printed.isLand)
  | .intersection sels =>
    match sels with
    | [] => #[]
    | s :: rest =>
      rest.foldl (fun acc t => intersectObjects acc (g.discardCostCandidates controller t))
        (g.discardCostCandidates controller s)
  | .union sels =>
    sels.foldl (fun acc s => unionObjects acc (g.discardCostCandidates controller s)) #[]
  | _ => #[]

/-- Whether `cost` can be paid as this ability resolves.
An `or` can be paid when any of its costs can. Mana needs a pool that
can pay it. A sacrifice needs at least `n` permanents `what` names.
A discard needs at least `n` cards `what` names. -/
def costPayable (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (cost : TriggeredAbility.CostSelector)
    (targets : Array Target := #[])
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none) : Bool :=
  match cost with
  | .mana symbols =>
    (g.player controller).manaPool.canPay { symbols := symbols }
  | .sacrifice n what =>
    let ctx : TriggerRead :=
      { controller, sourceId, targets, lastKnownPower, lastKnownToughness }
    match g.triggerCount ctx n with
    | some k => k > 0 && (g.sacrificeCostCandidates ctx what).size ≥ k
    | none => false
  | .discard n what =>
    let ctx : TriggerRead :=
      { controller, sourceId, targets, lastKnownPower, lastKnownToughness }
    match g.triggerCount ctx n with
    | some k => k > 0 && (g.discardCostCandidates controller what).size ≥ k
    | none => false
  | .or costs =>
    let rec go : List TriggeredAbility.CostSelector → Bool
      | [] => false
      | c :: rest =>
        costPayable g controller sourceId c targets lastKnownPower lastKnownToughness || go rest
    go costs

/-- Offer `pick` as an optional payment. Nothing legal skips the follow-up
of a `may`. Outside `may`, paying finishes the ability. Gaining no life is
that empty follow-up. -/
def offerMayPayPick (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (pick : CostPick) (msg : String) : Game :=
  let sid := sourceId.getD ⟨0⟩
  if (g.costPickCandidates controller sid pick).isEmpty then
    g.failMayThen
  else
    g.beginFraChoice controller (.mayPayPickThen pick (.gainLife 0) sid) msg

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
      let isArt := if src.isOnBattlefield then g.isArtifact src else src.printed.isArtifact
      if src.printed.isToken || !isArt || some src.id == sourceId then
        (g.logMsg "That permanent isn't another nontoken artifact").failMayThen
      else
        g.change (.pending (.fraChoice controller (.ultronMayPay id)))
          |>.logMsg s!"{(g.player controller).name} may pay {2} to copy {g.name src}"
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
        let g := g.recordPutCounters o.id .doubleStrike n (byPlayer := g.controllerOf o)
        g.logMsg s!"{g.name o} gets {n} double strike counters"
    | .burden =>
      if n == 1 then g.applyPermanentAction o .burdenCounter
      else g.addBurdenCounter o n
    | .stun =>
      let k := g.countersYouPut o n
      let g := g.recordPutCounters o.id .stun k (byPlayer := g.controllerOf o)
      let phrase :=
        if n == 1 then "A stun counter is put" else s!"{k} stun counters are put"
      g.logMsg s!"{phrase} on {g.name o}"
    | .loyalty =>
      let k := g.countersYouPut o n (putter := some controller)
      let g := g.recordPutCounters o.id .loyalty k (byPlayer := some controller)
      let phrase :=
        if n == 1 then "A loyalty counter is put" else s!"{k} loyalty counters are put"
      g.logMsg s!"{phrase} on {g.name o}"
    | kind =>
      g.addCounters o kind n (byPlayer := some controller)

/-- Resolve `TriggerResolution.pump`. `power` and `toughness` are read
separately, then applied to each permanent `who` names. -/
def applyTriggerPump (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (lastKnownPower lastKnownToughness : Option Int)
    (power toughness : TriggeredAbility.NumberSelector)
    (who : TriggeredAbility.ObjectSelector) : Game :=
  let ctx : TriggerRead := {
    controller, sourceId, targets, lastKnownPower, lastKnownToughness }
  -- `.double` adds the current statistic. Every other selector is the bonus
  -- it names. A selector that is not a number here adds zero.
  let shared (amount : TriggeredAbility.NumberSelector) : Option Int :=
    if amount == .double then none
    else
      match g.triggerInt ctx amount with
      | some n => some n
      | none => some 0
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
  | .whileSource | .target .whileSource =>
    g.withAffected controller ab sourceId targets .targetWhileSource pumpOne
  | .cause _ =>
    match g.battlefield.find? (fun o => o.status.attacking && g.controlledBy o controller) with
    | some o => pumpOne g o
    | none => g
  | .creaturesYouControl =>
    g.forEachControlledCreature controller pumpOne
  | .othersOfSubtype subtype =>
    let srcId? := (sourceId.bind g.findObject?).map (·.id)
    g.foldBattlefield (fun o =>
        g.controlledBy o controller &&
          (match srcId? with
           | some sid => o.id != sid
           | none => true) &&
          g.hasSubtype o subtype)
      pumpOne
  | .opponentsCreatures =>
    g.foldBattlefield (fun o => g.isCreature o && !g.controlledBy o controller) pumpOne
  | who =>
    match g.permanentsNamed ctx who with
    | some objs => g.withBatch none fun g => objs.foldl (fun game o => pumpOne game o) g
    | none => g

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
        g.logMsg s!"there are no creatures blocking {g.name o}"
      else if n == 0 then g
      else
        g.withBatch (g.resolvingBatchCause controller sourceId) fun g =>
          Id.run do
            let mut g := g
            for b in blockers do
              g := g.dealDamageFrom (g.name o) (g.object! b.id) n (source := some o)
            return g
  | .permanent, .lastKnownPower, .excess =>
    let amt := lastKnownPower.getD 0
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let remain := g.toughness o - o.status.damage
      let raw := amt - remain
      let excess : Nat := if raw > 0 then raw.toNat else 0
      let g := g.change (.excessDamageThisWay excess)
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
    g.dealDamageToEachOpponent controller n (source := src)
  | .player .eachOpponent, .fixed n, _ =>
    let n := n.toNat
    let src := sourceId.bind g.findObject?
    if ab.opts.untargeted || !ab.requiresTarget then
      g.dealDamageToEachOpponent controller n (source := src)
    else
      g.withLegalTriggerPlayer controller ab sourceId targets (fun g pid =>
        g.dealDamageToPlayer pid n (source := src))
  | .player .eachOpponent, .subtypeCount subtype, _ =>
    let amt := g.countSubtype controller subtype
    let src := sourceId.bind g.findObject?
    g.dealDamageToEachOpponent controller amt (source := src)
  | .player .eachOpponent, .discardedHand, _ =>
    match g.handDiscardedThisWay with
    | none => g.change (.notedSourceThisWay none)
    | some discarded =>
      let srcId := g.notedSourceThisWay
      let g := g.changes #[.handDiscardedThisWay none, .notedSourceThisWay none]
      if !g.hasEnduringStory controller || discarded == 0 then g
      else
        match srcId.bind g.findObject? with
        | some src =>
          if src.isOnBattlefield then
            g.dealDamageToEachOpponent controller (discarded : Int) (source := some src)
          else g
        | none => g
  | .target, .subtypeCount subtype, _ =>
    let amt := g.countSubtype controller subtype
    g.applyEffect controller (Effect.dealDamage amt) targets (sourceId := sourceId)
  | .target, .fixed n, .markedPermanent =>
    let n := n.toNat
    let g := g.change (.permanentDealtDamageThisWay none)
    g.withLegalKindTarget controller ab.targetKind targets (fun g tgt =>
      match tgt with
      | Target.player _ =>
        g.applyEffect controller (Effect.dealDamage n) #[tgt] (sourceId := sourceId)
      | Target.permanent oid =>
        match g.findObject? oid with
        | none => g.logMsg "The target is no longer legal"
        | some o =>
          let before := o.status.damage
          let g := g.applyEffect controller (Effect.dealDamage n) #[tgt] (sourceId := sourceId)
          let marked :=
            match g.findObject? oid with
            | some o => o.isOnBattlefield && o.status.damage > before
            | none => false
          if marked then g.change (.permanentDealtDamageThisWay (some oid)) else g
      | _ => g.logMsg "The target is no longer legal")
  | .player (.target .opponent), .greatestArtifactMv, _ =>
    let x := g.greatestManaValueAmong controller (g.isArtifact ·)
    g.withLegalTriggerPlayer controller ab sourceId targets (fun g pid =>
      g.dealDamageToPlayer pid x (source := sourceId.bind g.findObject?))
  | .eachNonSubtypeAndOpponents subtype, .fixed n, _ =>
    let n := n.toNat
    let src? := sourceId.bind g.findObject?
    if n == 0 then g
    else
      g.withBatch (g.resolvingBatchCause controller sourceId) fun g =>
        let g :=
          g.dealDamageToEachCreatureMatching n (fun o => !g.hasSubtype o subtype)
            (source := src?.map g.snapshot)
        g.dealDamageToEachOpponent controller n (source := src?)
  | .player (.target .opponent), .fixed n, _ =>
    let n := n.toNat
    g.withLegalTriggerPlayer controller ab sourceId targets (fun g pid =>
      g.dealDamageToPlayer pid n (source := sourceId.bind g.findObject?))
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
      g.applyPermanentAction o (.dealDamage n) (sourceId := sourceId)
  | .enchanted, .fixed n, _ =>
    let n := n.toNat
    g.withAffected controller ab sourceId targets .enchanted fun g o =>
      g.applyPermanentAction o (.dealDamage n) (sourceId := sourceId)
  | .whileSource, .fixed n, _ | .target .whileSource, .fixed n, _ =>
    let n := n.toNat
    g.withAffected controller ab sourceId targets .targetWhileSource fun g o =>
      g.applyPermanentAction o (.dealDamage n) (sourceId := sourceId)
  | who, amount, .divided =>
    let ctx : TriggerRead :=
      { controller, sourceId, targets, lastKnownPower }
    match g.triggerCount ctx amount with
    | none => g
    | some n =>
      let recipients : Array (Sum PlayerId GameObject) :=
        match g.permanentsNamed ctx who with
        | some objs =>
          if objs.isEmpty then
            targets.filterMap fun
              | Target.player pid => some (.inl pid)
              | Target.permanent id =>
                match g.findObject? id with
                | some o => if o.isOnBattlefield then some (.inr o) else none
                | none => none
              | _ => none
          else objs.map .inr
        | none =>
          targets.filterMap fun
            | Target.player pid => some (.inl pid)
            | Target.permanent id =>
              match g.findObject? id with
              | some o => if o.isOnBattlefield then some (.inr o) else none
              | none => none
            | _ => none
      if recipients.isEmpty || n == 0 then g
      else
        let base := n / recipients.size
        let extra := n % recipients.size
        g.withBatch (g.resolvingBatchCause controller sourceId) fun g =>
          Id.run do
            let mut game := g
            for i in [0:recipients.size] do
              let share := base + if i < extra then 1 else 0
              if share > 0 then
                match recipients[i]? with
                | some (.inl pid) =>
                  game := game.dealDamageToPlayer pid share (source := sourceId.bind game.findObject?)
                | some (.inr o) =>
                  game := game.dealDamageFrom sourceName o (Int.ofNat share)
                    (source := sourceId.bind game.findObject?)
                | none => pure ()
            return game
  | who, amount, note =>
    let ctx : TriggerRead :=
      { controller, sourceId, targets, lastKnownPower }
    match g.triggerCount ctx amount with
    | none => g
    | some n =>
      let src :=
        match note with
        | .fromEquipped => g.attachedHost? sourceId
        | _ => sourceId.bind g.findObject?
      let dealPermanent (game : Game) (o : GameObject) : Game :=
        match note with
        | .excess =>
          let amt := Int.ofNat n
          let remain := game.toughness o - o.status.damage
          let raw := amt - remain
          let excess : Nat := if raw > 0 then raw.toNat else 0
          let game := game.change (.excessDamageThisWay excess)
          game.dealDamageFrom sourceName o amt (source := src)
        | .markedPermanent =>
          let before := o.status.damage
          let game := game.dealDamageFrom sourceName o (Int.ofNat n) (source := src)
          let marked :=
            match game.findObject? o.id with
            | some cur => cur.isOnBattlefield && cur.status.damage > before
            | none => false
          if marked then game.change (.permanentDealtDamageThisWay (some o.id)) else game
        | _ =>
          game.dealDamageFrom sourceName o (Int.ofNat n) (source := src)
      let batchCause := g.resolvingBatchCause controller sourceId
      match who with
      | .player sel =>
        match g.collectPlayers ctx sel with
        | some pids =>
          if n == 0 || pids.isEmpty then g
          else
            g.withBatch batchCause fun g =>
              pids.foldl (fun game pid => game.dealDamageToPlayer pid n (source := src)) g
        | none => g
      | .target =>
        match note with
        | .none | .fromEquipped =>
          g.applyDamageToKindTarget controller ab.targetKind targets n sourceId none
        | _ =>
          match g.permanentsNamed ctx .target with
          | some objs =>
            if n == 0 || objs.isEmpty then g
            else g.withBatch batchCause fun g => objs.foldl dealPermanent g
          | none => g
      | _ =>
        match g.permanentsNamed ctx who with
        | some objs =>
          if n == 0 || objs.isEmpty then g
          else g.withBatch batchCause fun g => objs.foldl dealPermanent g
        | none => g

/-- Put one keyword counter on `src` when `other` has that keyword and `src`
does not. -/
def copyKeywordCounter (g : Game) (src other : GameObject)
    (has : GameObject → Bool) (kind : CounterKind) (name : String) : Game :=
  if has other && !has src then
    let n := g.countersYouPut src 1
    g.recordPutCounters src.id kind n (byPlayer := g.controllerOf src)
      |>.logMsg s!"{g.name src} gets a {name} counter"
  else g

/-- Put a counter on `src` for each keyword `other` has that `src` does not.
Haste, flying, first strike, double strike, deathtouch, indestructible,
lifelink, menace, reach, trample, and vigilance. -/
def copyMissingKeywordCounters (g : Game) (src other : GameObject) : Game :=
  g.withBatch none fun g =>
    let g := g.copyKeywordCounter src other g.hasHaste .haste "haste"
    let src := g.object! src.id
    let g := g.copyKeywordCounter src other g.hasFlying .flying "flying"
    let src := g.object! src.id
    let g := g.copyKeywordCounter src other
      (fun o => g.hasKeyword o (·.firstStrike)) .firstStrike "first strike"
    let src := g.object! src.id
    let g := g.copyKeywordCounter src other g.hasDoubleStrike .doubleStrike "double strike"
    let src := g.object! src.id
    let g := g.copyKeywordCounter src other g.hasDeathtouch .deathtouch "deathtouch"
    let src := g.object! src.id
    let g := g.copyKeywordCounter src other g.hasIndestructible .indestructible "indestructible"
    let src := g.object! src.id
    let g := g.copyKeywordCounter src other g.hasLifelink .lifelink "lifelink"
    let src := g.object! src.id
    let g := g.copyKeywordCounter src other g.hasMenace .menace "menace"
    let src := g.object! src.id
    let g := g.copyKeywordCounter src other (fun o => g.hasKeyword o (·.reach)) .reach "reach"
    let src := g.object! src.id
    let g := g.copyKeywordCounter src other g.hasTrample .trample "trample"
    let src := g.object! src.id
    g.copyKeywordCounter src other g.hasVigilance .vigilance "vigilance"

/-- Resolve `TriggerResolution.putCounters`. Each printed combination keeps
the behavior of the constructor it replaced. Any other permanent the
selector names receives that counter. A missing count or permanent puts
nothing. -/
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
      g.withBatch none fun g =>
        (g.permanentsOf controller).foldl (fun g o =>
          if g.hasSubtype o s then g.addPlusOnePlusOneTo (g.object! o.id) 1 else g) g
    | .citysBlessing =>
      let n := if (g.player controller).citysBlessing then 2 else 1
      g.withBatch none fun g =>
        (g.permanentsOf controller).foldl (fun acc o =>
          if acc.isCreature o then acc.addPlusOnePlusOneTo o n else acc) g
  | .ofKind .plusOnePlusOne _, .eachOther =>
    g.withBatch none fun g =>
      (g.creaturesControlledBy controller).foldl (fun acc o =>
        if some o.id != sourceId then acc.addPlusOnePlusOneTo o 1 else acc) g
  | .plusOneLastKnownMv, .permanent _ =>
    let n := (lastKnownPower.getD 0).toNat
    g.applyOnPermanent controller ab.targetKind targets (.plusOne n) sourceId
      (some "The target is no longer legal")
  | .ofKind .loyalty _, .source =>
    g.withSourceOnBattlefield sourceId (fun g o =>
      let n := g.countersYouPut o 1 (putter := some controller)
      let g := g.recordPutCounters o.id .loyalty n (byPlayer := some controller)
      g.logMsg s!"A loyalty counter is put on {g.name o}")
  | .sourceCounters, .permanent _ =>
    -- Rulings 756 / 758: each kind of counter it had as it died, in the same
    -- numbers; nothing moves from the dead creature.
    match sourceId.bind g.lastKnownCounterStatus? with
    | none => g.logMsg "The source had no counters"
    | some last =>
      g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
        g.withBatch none fun g =>
          let extra := g.docSamsonBonus (some controller) (g.controllerOf o)
          let g := g.putCountersExceptPlusOne o.id last extra (byPlayer := some controller)
          let o := g.object! o.id
          let g :=
            if last.plusOnePlusOne > 0 then
              g.addPlusOnePlusOneTo o last.plusOnePlusOne (byPlayer := some controller)
            else g
          g.logMsg s!"The counters are put on {g.name o}") "No target was chosen"
  | .ofKind .charge _, .source =>
    g.withSourceOnBattlefield sourceId (fun g o =>
      let n := g.countersYouPut o 1 (putter := some controller)
      let g := g.recordPutCounters o.id .charge n (byPlayer := some controller)
      g.logMsg s!"A charge counter is put on {g.name o}")
  | .ofKind .quest _, .source =>
    g.withTriggerSource sourceId fun g src =>
      let n := g.countersYouPut src 1 (putter := some controller)
      let g := g.recordPutCounters src.id .quest n (byPlayer := some controller)
      let src := g.object! src.id
      g.logMsg s!"{g.name src} gets a quest counter ({src.status.quest})"
  | .honePerOpponent, .source =>
    let opp :=
      match targets[0]? with
      | some (Target.player pid) => pid
      | some (Target.permanent _) => g.opponent controller
      | _ => g.opponent controller
    let n := g.countCreaturesControlledBy opp
    g.withTriggerSource sourceId fun g src =>
      let k := g.countersYouPut src n (putter := some controller)
      g.recordPutCounters src.id .hone k (byPlayer := some controller)
        |>.logMsg s!"{g.name src} gets {k} hone counter(s)"
  | .ofKind .plan _, .source =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield then
        g.incrementPlanThen controller sourceId (fun g _ => g)
      else
        g.change (.skipTriggerSequenceRest true)
          |>.logMsg s!"{o.name} is no longer on the battlefield"
    | none =>
      g.change (.skipTriggerSequenceRest true)
        |>.logMsg "The ability's source is no longer in play"
  | .ofKind .plusOnePlusOne _, .permanent true =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      g.addPlusOnePlusOneTo o 1 (byPlayer := some controller))
      "The target is no longer legal. You won't put counters on anything."
  | .plusOneNoted, .createdToken =>
    let n := g.notedCountThisWay
    let id? := g.createdTokenThisWay
    let g := g.change (.createdTokenThisWay none)
    if n == 0 then g
    else
      match id?.bind g.findObject? with
      | some o => g.addPlusOnePlusOneTo o n
      | none => g
  | .ofKind .invasion _, .source =>
    let g := g.change (.notedCountThisWay 0)
    g.withSourceOnBattlefield sourceId (fun g src =>
      let n := g.countersYouPut src 1 (putter := some controller)
      g.recordPutCounters src.id .invasion n (byPlayer := some controller)
        |>.logMsg s!"{g.name src} gets an invasion counter")
      "The source is no longer in play"
  | .ofKind .trample _, .permanent _ =>
    match targets[0]? with
    | some (Target.permanent oid) =>
      match g.findObject? oid with
      | some o =>
        let n := g.countersYouPut o 1 (putter := some controller)
        let g := g.recordPutCounters o.id .trample n (byPlayer := some controller)
        if n == 0 then g else g.logMsg s!"{g.name o} gets a trample counter"
      | none => g
    | _ => g
  | .ofKind .influence _, .source =>
    let g := g.change (.palantirChoiceReady none)
    let tgt :=
      match targets[0]? with
      | some (Target.player pid) => some pid
      | _ => none
    match sourceId with
    | none =>
      g.change (.skipTriggerSequenceRest true)
        |>.logMsg "The source is no longer in play"
    | some sid =>
      let (g, ok) := g.putPalantirInfluence sid tgt
      match ok with
      | none => g.change (.skipTriggerSequenceRest true)
      | some increased =>
        match tgt with
        | some opp =>
          if increased then
            g.change (.palantirChoiceReady (some (controller, opp, sid)))
          else g
        | none => g
  | .ofKind .loyalty _, .permanent _ =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let n := g.countersYouPut o 1 (putter := some controller)
      let g := g.recordPutCounters o.id .loyalty n (byPlayer := some controller)
      g.logMsg s!"A loyalty counter is put on {g.name o}")
  | .plusOneSacrificedPower, .source =>
    let n := g.sacrificedPowerThisWay.getD 0
    let g := g.change (.sacrificedPowerThisWay none)
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
      let g := g.recordPutCounters o.id .doubleStrike n (byPlayer := some controller)
      let phrase :=
        if n == 1 then "a double strike counter" else s!"{n} double strike counters"
      g.logMsg s!"{g.name o} gets {phrase}")
      "The target is no longer legal"
  | .ofKind .burden n, .permanent false =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      g.addBurdenCounter o n)
      "The target is no longer legal"
  | .ofKind .stun n, .permanent false =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let k := g.countersYouPut o n
      let g := g.recordPutCounters o.id .stun k (byPlayer := g.controllerOf o)
      let phrase :=
        if n == 1 then "A stun counter is put" else s!"{k} stun counters are put"
      g.logMsg s!"{phrase} on {g.name o}")
      "The target is no longer legal"
  | .ofKind kind n, .source =>
    g.applyAffectedCounters controller ab sourceId targets kind n .source
  | .ofKind kind n, .enchanted =>
    g.applyAffectedCounters controller ab sourceId targets kind n .enchanted
  | .ofKind kind n, .whileSource | .ofKind kind n, .target .whileSource =>
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
          if !other.isOnBattlefield || !g.isCreature other || other.id == src.id then
            g.logMsg "The target is no longer legal"
          else
            g.copyMissingKeywordCounters src other
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "The target is no longer legal")
      "The source is no longer in play"
  | .ofKind kind n, who =>
    let ctx : TriggerRead :=
      { controller, sourceId, targets, lastKnownPower }
    match g.permanentsNamed ctx who with
    | some objs =>
      g.withBatch none fun g =>
        objs.foldl (fun game o =>
          game.addCounters o kind n (byPlayer := some controller)) g
    | none => g
  | what, who =>
    let ctx : TriggerRead :=
      { controller, sourceId, targets, lastKnownPower }
    let putN (kind : CounterKind) (n : Nat) : Game :=
      match g.permanentsNamed ctx who with
      | some objs =>
        g.withBatch none fun g =>
          objs.foldl (fun game o =>
            game.addCounters o kind n (byPlayer := some controller)) g
      | none => g
    match what with
    | .plusOneLastKnownMv => putN .plusOnePlusOne (lastKnownPower.getD 0).toNat
    | .plusOneSacrificedPower =>
      putN .plusOnePlusOne (g.sacrificedPowerThisWay.getD 0)
    | .honePerOpponent =>
      let opp :=
        match targets[0]? with
        | some (Target.player pid) => pid
        | _ => g.opponent controller
      putN .hone (g.countCreaturesControlledBy opp)
    | .plusOneNoted => putN .plusOnePlusOne g.notedCountThisWay
    | .sourceCounters =>
      match sourceId.bind g.lastKnownCounterStatus? with
      | none => g
      | some last =>
        match g.permanentsNamed ctx who with
        | none => g
        | some objs =>
          g.withBatch none fun g =>
            objs.foldl (fun game o =>
              let extra := game.docSamsonBonus (some controller) (game.controllerOf o)
              let game := game.putCountersExceptPlusOne o.id last extra (byPlayer := some controller)
              if last.plusOnePlusOne > 0 then
                game.addPlusOnePlusOneTo (game.object! o.id) last.plusOnePlusOne
                  (byPlayer := some controller)
              else game) g
    | .missingKeywordsFromTarget =>
      let other? :=
        match targets[0]? with
        | some (Target.permanent id) => g.findObject? id
        | _ => none
      match other?, g.permanentsNamed ctx who with
      | some other, some objs =>
        if !other.isOnBattlefield || !g.isCreature other then g
        else
          g.withBatch none fun g =>
            objs.foldl (fun game o =>
              game.copyMissingKeywordCounters (game.object! o.id) other) g
      | _, _ => g
    | .ofKind .. => g

/-- Resolve `TriggerResolution.createTokens`. Each printed combination keeps
the behavior of the constructor it replaced. Any other count is created
for the players the selector names. A missing count creates nothing. -/
def applyCreateTokens (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (targets : Array Target)
    (lastKnownPower : Option Int) (kind : TokenKind)
    (amount : TriggeredAbility.NumberSelector) (tapped : Bool)
    (token : TriggeredAbility.TriggerToken)
    (who : TriggeredAbility.PlayerSelector)
    (note : TriggeredAbility.TriggerTokenNote)
    (lastKnownToughness : Option Int := none) : Game :=
  let ctx : TriggerRead :=
    { controller, sourceId, targets, lastKnownPower, lastKnownToughness }
  let counted := g.triggerCount ctx amount
  let recipients (token : TriggeredAbility.TriggerToken) (who : TriggeredAbility.PlayerSelector) :=
    g.tokenRecipients ctx token who
  match token, who, amount, note with
  | .axe, who, _, note =>
    let n := counted.getD 0
    let (g, last) := g.spawnFace (recipients .axe who) axeToken n (tapped := tapped)
    match note, last with
    | .attachReflexive, some id =>
      g.putReflexiveTrigger controller (some id) {
        targeting := .of .creatureYouControl
        resolution := .attach .source .target
        phrase := "Attach it to target creature you control" }
    | _, some _ =>
      g.logMsg "An Axe token is created"
    | _, none => g
  | .kind, .you, .oppArtifacts, _ =>
    let n := g.countOpponentArtifacts controller
    g.createTreasureTokens controller n (tapped := true)
  | .kind, .you, .damagedPlayerArtifacts, _ =>
    let pid := g.loggedLastCombatDamagePlayer.getD (g.opponent controller)
    let n := g.countArtifactsControlledBy pid
    g.createTreasureTokens controller n |>.logMsg
      s!"{(g.player controller).name} creates {n} Treasure token(s) (artifacts that player controls)"
  | .kind, .you, .lastKnownPower, _ =>
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
  | .zabu, who, _, _ =>
    (g.spawnFace (recipients .zabu who) zabuToken (counted.getD 0) (tapped := tapped)).1
  | .theVoid, who, _, _ =>
    (g.spawnFace (recipients .theVoid who) theVoidToken (counted.getD 0)
      (tapped := tapped)).1
  | .redwing, who, _, _ =>
    (g.spawnFace (recipients .redwing who) redwingToken (counted.getD 0)
      (tapped := tapped)).1
  | .alien, who, _, _ =>
    let inv :=
      match sourceId.bind g.findObject? with
      | some src => src.status.invasion
      | none => 0
    let (g, last) :=
      g.spawnFace (recipients .alien who) alien11redHasteToken (counted.getD 0)
        (tapped := tapped)
    match last with
    | some id => g.changes #[.notedCountThisWay inv, .createdTokenThisWay (some id)]
    | none => g
  | .galactus, who, _, _ =>
    (g.spawnFace (recipients .galactus who) galactusToken (counted.getD 0)
      (tapped := tapped)).1
  | .sturdyShield, who, _, _ =>
    let (g, last) :=
      g.spawnFace (recipients .sturdyShield who) sturdyShieldToken (counted.getD 0)
        (tapped := tapped)
    match last with
    | some id => g.change (.createdTokenThisWay (some id))
    | none => g
  | .merfolk, _, .blueManaSymbols, _ =>
    g.createMerfolkForBlueSymbols controller lastKnownPower
  | .kind, .you, .fixed n, _ =>
    g.createKindTokens controller kind n.toNat (tapped := tapped)
  | .kind, .controller .target, _, _ =>
    -- Destroy may already have moved the permanent. The controller who
    -- creates the token is the one it had on the battlefield.
    let n := counted.getD 0
    match (g.collectPlayers ctx (.controller .target)).bind (·[0]?) with
    | some pid =>
      if kind == .treasure && !tapped then g.createTreasureTokens pid n
      else g.createKindTokens pid kind n (tapped := tapped)
    | none => g
  | .kind, _who, .chosenCreatureType, _ =>
    let types := (g.creaturesControlledBy controller).foldl (fun acc o =>
      o.subtypes.foldl (fun acc t => if acc.contains t then acc else acc.push t) acc) #[]
    if types.isEmpty then
      g.logMsg s!"{(g.player controller).name} controls no creatures, so no Treasures are created"
    else
      g.beginFraChoice controller (.chooseCreatureType types)
        s!"{(g.player controller).name} chooses a creature type"
  | token, who, _, note =>
    let n := counted.getD 0
    let pids := recipients token who
    if n == 0 || pids.isEmpty then g
    else
      let (g, last) :=
        match token with
        | .kind =>
          let g : Game := g.withBatch none fun g =>
            pids.foldl (fun (g : Game) (pid : PlayerId) =>
              g.createKindTokens pid kind n (tapped := tapped)) g
          (g, g.recentTokenIds.back?)
        | .merfolk =>
          g.spawnFace pids merfolk11blueToken n (tapped := tapped)
        | .axe => g.spawnFace pids axeToken n (tapped := tapped)
        | .zabu => g.spawnFace pids zabuToken n (tapped := tapped)
        | .theVoid => g.spawnFace pids theVoidToken n (tapped := tapped)
        | .redwing => g.spawnFace pids redwingToken n (tapped := tapped)
        | .alien => g.spawnFace pids alien11redHasteToken n (tapped := tapped)
        | .galactus => g.spawnFace pids galactusToken n (tapped := tapped)
        | .sturdyShield => g.spawnFace pids sturdyShieldToken n (tapped := tapped)
      match note, last with
      | .remember, some id => g.change (.createdTokenThisWay (some id))
      | .invasion, some id =>
        let inv :=
          match sourceId.bind g.findObject? with
          | some src => src.status.invasion
          | none => 0
        g.changes #[.notedCountThisWay inv, .createdTokenThisWay (some id)]
      | .attachReflexive, some id =>
        g.putReflexiveTrigger controller (some id) {
          targeting := .of .creatureYouControl
          resolution := .attach .source .target
          phrase := "Attach it to target creature you control" }
      | _, _ => g

/-- Resolve `TriggerResolution.exile`. Each printed combination keeps
the behavior of the constructor it replaced. Any other card the selector
names is exiled as `how` and `note` say. A hand or an unmade choice
exiles nothing. -/
def applyExile (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (what : TriggeredAbility.ObjectSelector)
    (how : TriggeredAbility.TriggerExileHow)
    (note : TriggeredAbility.TriggerExileNote) : Game :=
  match what, how, note with
  | .target, .leaveTrigger, .none =>
    g.withLegalKindPermanent controller ab.targetKind targets (fun g o =>
      g.exileForLeaveTrigger sourceId o) sourceId (some "The target is no longer legal")
  | .target, .untilSourceLeaves, .copyAndHost =>
    let g := g.changes #[.notedCopyObject none, .notedHostId none]
    g.withSourceStillOnBattlefield sourceId fun g src =>
      match targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some tgt =>
          let hostId := src.attachedTo
          let g := g.exileUntilSourceLeaves sourceId tgt
          g.changes #[.notedCopyObject (some tgt), .notedHostId hostId]
        | none => g.logMsg "The target is no longer legal"
      | _ => g
  | .target, .untilSourceLeaves, .none =>
    g.withSourceStillOnBattlefield sourceId fun g _ =>
      g.withLegalKindPermanent controller ab.targetKind targets (fun g o =>
        g.exileUntilSourceLeaves sourceId o) sourceId (some "The target is no longer legal")
  | .top, .playUntilNextTurn, .none =>
    g.resolveExileTopPlayUntilEndOfNextTurn controller
  | .eachPermanent, .untilSourceLeaves, .none
  | .target .eachPermanent, .untilSourceLeaves, .none =>
    g.withSourceStillOnBattlefield sourceId fun g _ =>
      let (g, linkCause) := g.allocDelayedCause (some controller) sourceId
      g.withBatch (some linkCause) fun g =>
        targets.foldl (fun acc t =>
          match t with
          | Target.permanent oid =>
            match acc.findObject? oid with
            | some o => acc.exileUntilSourceLeaves sourceId o (cause := some linkCause)
            | none => acc
          | _ => acc) g
  | .landsYouControl, .forLater, .lands =>
    let g := g.change (.exiledIdsThisWay #[])
    let (g, cause) := g.allocDelayedCause (some controller) sourceId
    g.foldPermanentTargets targets (fun g o =>
      if g.controlledBy o controller && g.isLand o then
        let (g, newId) := g.move o.id .exile none (cause := some cause)
        g.change (.pushExiledIdThisWay newId)
      else g)
  | .target, .nextEndStep, .none =>
    g.withLegalKindPermanent controller ab.targetKind targets (fun g o =>
      g.exileUntilNextEndStep o) sourceId none
  | .graveyardCard, .forLater, .playCard =>
    let g := g.change (.playExiledThisWay none)
    g.withLegalKindTarget controller ab.targetKind targets (fun g tgt =>
      match tgt with
      | Target.card id | Target.permanent id =>
        match g.findObject? id with
        | some o =>
          let (g, newId) := g.move o.id .exile none
          g.change (.playExiledThisWay (some newId))
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
  | .whileSource, .forLater, .none | .target .whileSource, .forLater, .none =>
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
  | what, how, note =>
    let ctx : TriggerRead := { controller, sourceId, targets }
    let fromIds (ids : Array ObjectId) : Option (Array GameObject) :=
      some (ids.filterMap g.findObject?)
    let cards : Option (Array GameObject) :=
      match g.permanentsNamed ctx what with
      | some objs => some objs
      | none =>
        match what with
        | .top =>
          match note with
          | .impulse | .anyManaThisTurn =>
            if g.revealedIdsThisWay.isEmpty then none
            else fromIds g.revealedIdsThisWay
          | _ =>
            match (g.player controller).library.back?.bind g.findObject? with
            | some o => some #[o]
            | none => some #[]
        | .linkedExile =>
          match sourceId.bind g.findObject? with
          | some src => fromIds src.linkedExile
          | none => some #[]
        | .graveyardCard | .graveyardPermanent | .creatureCard =>
          some (targets.filterMap fun
            | Target.card id | Target.permanent id =>
              match g.findObject? id with
              | some o => if o.zone == .graveyard o.owner then some o else none
              | none => none
            | _ => none)
        | .opponentTop n =>
          let pid :=
            match targets.findSome? fun
              | Target.player p => some p
              | _ => none with
            | some p => p
            | none => g.opponent controller
          fromIds (g.scryLookedIds pid n)
        | .milledSubtype subtype =>
          fromIds (g.milledIdsThisWay.filter fun id =>
            (g.findObject? id).any (·.printed.hasSubtype subtype))
        | .notedLands => fromIds g.exiledIdsThisWay
        | .discarded | .discardedLand =>
          match g.discardedCardThisWay with
          | some (_, id) => fromIds #[id]
          | none => some #[]
        | .revealed => fromIds g.revealedIdsThisWay
        | _ => none
    match cards with
    | none => g
    | some objs =>
      let g :=
        match note with
        | .lands => g.change (.exiledIdsThisWay #[])
        | .copyAndHost => g.changes #[.notedCopyObject none, .notedHostId none]
        | .playCard => g.change (.playExiledThisWay none)
        | .impulse | .anyManaThisTurn => g.change (.revealedIdsThisWay #[])
        | _ => g
      let stashedCause? :=
        g.stashedCause.orElse (fun _ => objs[0]?.bind (fun o => g.lastMoveCauseOf? o.id))
      let g := if g.stashedCause.isSome then g.change (.stashedCause none) else g
      let (g, sharedCause?) : Game × Option EventCause :=
        match stashedCause? with
        | some c => (g, some c)
        | none =>
          if !objs.isEmpty then
            let (g, c) := g.allocDelayedCause (some controller) sourceId
            (g, some c)
          else (g, none)
      let exileOne (g : Game) (o : GameObject) : Game :=
        match how with
        | .leaveTrigger => g.exileForLeaveTrigger sourceId o (cause := sharedCause?)
        | .untilSourceLeaves =>
          match sourceId.bind g.findObject? with
          | some src =>
            if src.isOnBattlefield then g.exileUntilSourceLeaves sourceId o (cause := sharedCause?)
            else g
          | none => g
        | .nextEndStep => g.exileUntilNextEndStep o (cause := sharedCause?)
        | .playUntilNextTurn =>
          let name := if o.isOnBattlefield then g.name o else o.name
          let (g, newId) := g.move o.id .exile none (cause := sharedCause?)
          let g := g.createEffect
            (.playPermission newId { player := controller } (turnEnds := 2))
            (cause := sharedCause?)
          g.logMsg
            s!"{(g.player controller).name} exiles {name} and may play it until the end of their next turn"
        | .playThisTurn =>
          let name := if o.isOnBattlefield then g.name o else o.name
          let (g, newId) := g.move o.id .exile none (cause := sharedCause?)
          let g := g.createEffect
            (.playPermission newId { player := controller })
            (cause := sharedCause?)
          g.logMsg s!"{(g.player controller).name} exiles {name} and may play it this turn"
        | .forLater =>
          let name := if o.isOnBattlefield then g.name o else o.name
          let wasLand := if o.isOnBattlefield then g.isLand o else o.printed.isLand
          let (g, newId) := g.move o.id .exile none (cause := sharedCause?)
          match note with
          | .lands =>
            if wasLand then
              g.change (.pushExiledIdThisWay newId)
            else g
          | .playCard => g.change (.playExiledThisWay (some newId))
          | .copyAndHost =>
            let hostId :=
              match sourceId.bind g.findObject? with
              | some src => src.attachedTo
              | none => none
            g.changes #[.notedCopyObject (some o), .notedHostId hostId]
          | .impulse =>
            g.changes #[
              .grimaImpulseReady true,
              .grimaImpulseVictim (some o.owner),
              .grimaImpulseFound (some newId),
              .grimaImpulseOthers g.grimaImpulseOthers]
          | .linked =>
            match sourceId.bind g.findObject? with
            | some src =>
              g.changeObject src.id (.pushLinkedExile newId)
            | none => g
          | .ifHero =>
            if g.hasSubtype o .hero then
              match sourceId.bind g.findObject? with
              | some src =>
                if src.isOnBattlefield then g.pumpPermanent src 2 1 else g
              | none => g
            else g
          | .anyManaThisTurn => g.grantWidowCast controller (some newId) (cause := sharedCause?)
          | .none => g.logMsg s!"{name} is exiled"
        | .returnImmediately =>
          let owner := o.owner
          let name := if o.isOnBattlefield then g.name o else o.name
          let (g, exId) := g.move o.id .exile none (cause := sharedCause?)
          let ex := g.object! exId
          let (g, retId) := g.move exId .battlefield (some owner)
            (summoningSick := ex.printed.isCreature && !ex.printed.keywords.haste)
            (cause := sharedCause?)
          g.afterPermanentEnters (g.object! retId)
            |>.logMsg s!"{name} is exiled, then returned"
        | .returnTapped =>
          let isArtOrCreature :=
            if o.isOnBattlefield then g.isArtifact o || g.isCreature o
            else o.printed.isArtifact || o.printed.isCreature
          if o.printed.isToken || !isArtOrCreature then g
          else
            let owner := o.owner
            let name := if o.isOnBattlefield then g.name o else o.name
            let (g, exId) := g.move o.id .exile none (cause := sharedCause?)
            let ex := g.object! exId
            let (g, retId) := g.move exId .battlefield (some owner)
              (tapped := true) (summoningSick := ex.printed.isCreature && !ex.printed.keywords.haste)
              (cause := sharedCause?)
            g.afterPermanentEnters (g.object! retId)
              |>.logMsg s!"{name} is exiled, then returned tapped"
        | .mayCastUpTo casts =>
          let (g, newId) := g.move o.id .exile none (cause := sharedCause?)
          let prev :=
            match g.pending with
            | .fraChoice _ (.mayCastUpToFromExile ids _) => ids
            | _ => #[]
          g.change (.pending
            (.fraChoice controller (.mayCastUpToFromExile (prev.push newId) casts)))
      g.withBatch sharedCause? fun g => objs.foldl exileOne g

/-- Resolve `TriggerResolution.sacrifice`. Each printed selector keeps
the behavior of the combination it replaced. Any other permanent the
selector names is sacrificed, and the note records what it says. A card
or an unmade choice sacrifices nothing. -/
def applySacrifice (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (what : TriggeredAbility.ObjectSelector)
    (note : TriggeredAbility.TriggerSacrificeNote) : Game :=
  let sacrificeSource (how : TriggeredAbility.SacrificeSourceHow) (noted : Bool) : Game :=
    let g := if noted then g.change (.sourceWasSacrificed false) else g
    let mark (game : Game) : Game :=
      if noted then game.change (.sourceWasSacrificed true) else game
    match how with
    | .isSacrificed =>
      g.withSourceOnBattlefield sourceId (fun g src =>
        mark (g.sacrificeToGraveyard src s!"{g.name src} is sacrificed"))
    | .controllerSacrifices =>
      g.withSourceOnBattlefield sourceId (fun g src =>
        mark (g.sacrificeToGraveyard src
          s!"{(g.player controller).name} sacrifices {g.name src}"))
    | .movedAsSacrificed =>
      g.withTriggerSource sourceId fun g src =>
        let name := g.name src
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
      | some src =>
        if src.status.attackingTarget.isSome then g.defendingPlayerOf src
        else g.opponent controller
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
  | .sacrificedSource how, .forReflexive =>
    let stillThere :=
      match sourceId.bind g.findObject? with
      | some o => o.isOnBattlefield
      | none => false
    let g := sacrificeSource how false
    g.change (.planWasSacrificed stillThere)
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
    g.change (.planWasSacrificed stillThere)
  | .another, _ =>
    match sourceId with
    | some sid =>
      g.change (.pending (.maySacrificeAnotherBolg controller sid))
        |>.logMsg s!"{(g.player controller).name} may sacrifice another creature (Bolg reflexive trigger)"
    | none => g.logMsg "Bolg is no longer in play"
  | what, note =>
    let ctx : TriggerRead := { controller, sourceId, targets }
    match g.permanentsNamed ctx what with
    | none => g
    | some objs =>
      let g :=
        match note with
        | .noted => g.change (.sourceWasSacrificed false)
        | .forReflexive => g.change (.planWasSacrificed false)
        | .none => g
      g.withBatch none fun g =>
        objs.foldl (fun g o =>
          let g := g.sacrificeToGraveyard o s!"{g.name o} is sacrificed"
          match note with
          | .noted => g.change (.sourceWasSacrificed true)
          | .forReflexive => g.change (.planWasSacrificed true)
          | .none => g) g

/-- Resolve `TriggerResolution.attach`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyAttach (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (what host : TriggeredAbility.ObjectSelector) : Game :=
  match what, host with
  | .source, .createdToken =>
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
  | .source, .laterCreature | .source, .target .laterCreature =>
    match targets[1]?, targets[0]? with
    | some (Target.permanent hid), _
    | none, some (Target.permanent hid) =>
      match g.findObject? hid, sourceId.bind g.findObject? with
      | some host, some src =>
        if g.isCreature host then g.attachSourceTo src host else g
      | _, _ => g
    | _, _ => g
  | .anyYouControl, .target =>
    let g := g.change (.equipmentAttachedHost none)
    match targets[0]? with
    | some (Target.permanent hid) =>
      match g.findObject? hid with
      | none => g.logMsg "The target is no longer legal"
      | some host =>
        if !host.isOnBattlefield || !g.isCreature host then
          g.logMsg "The target is no longer legal"
        else
          let eligible :=
            ((g.permanentsOf controller).filter (fun o =>
              g.isEquipment o && o.attachedTo != some host.id)).map (·.id)
          if eligible.isEmpty then
            g.logMsg "No Equipment was attached this way"
          else
            g.beginFraChoice controller (.attachAnyEquipment host.id eligible)
              s!"{(g.player controller).name} chooses any number of Equipment to attach to {g.name host}"
    | _ => g.logMsg "The target is no longer legal"
  | .putArtifact, .notedHost =>
    match g.putArtifactThisWay with
    | none => g
    | some (id, hostId) =>
      let g := g.change (.putArtifactThisWay none)
      match g.findObject? id with
      | none => g
      | some o =>
        match g.findObject? hostId with
        | some host =>
          if host.isOnBattlefield then g.attachSourceTo o host
          else g.logMsg s!"{host.name} is no longer on the battlefield"
        | none => g.logMsg "The source is no longer in play"
  | .createdToken, .source =>
    match g.createdTokenThisWay.bind g.findObject? with
    | none => g.change (.createdTokenThisWay none)
    | some tok =>
      let g := g.change (.createdTokenThisWay none)
      match sourceId.bind g.findObject? with
      | some src => g.attachSourceTo tok src
      | none => g
  | .announcedEquipment, .announcedCreature =>
    match targets.toList with
    | [Target.permanent eqId, Target.permanent crId] =>
      match g.findObject? eqId, g.findObject? crId with
      | some eq, some cr =>
        if eq.isOnBattlefield && cr.isOnBattlefield && g.isEquipment eq &&
            g.isCreature cr then
          g.attachSourceTo eq cr
        else
          g.logMsg "The Equipment won't move"
      | _, _ => g.logMsg "The Equipment won't move"
    | [Target.permanent id] =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield && g.isEquipment o then
          g.logMsg "The Equipment won't move"
        else
          g.logMsg "No Equipment was chosen"
      | none => g.logMsg "The Equipment won't move"
    | _ => g.logMsg "The Equipment won't move"
  | .eachEquipment, .enchantedCreature | .target .eachEquipment, .enchantedCreature =>
    match sourceId.bind g.findObject? with
    | some src =>
      match src.attachedTo.bind g.findObject? with
      | none =>
        g.logMsg "The enchanted creature has left. Equipment stays where it is."
      | some host =>
        g.withBatch none fun g =>
          targets.foldl (fun (g : Game) (t : Target) =>
            match t with
            | Target.permanent id =>
              match g.findObject? id with
              | some eq =>
                if eq.isOnBattlefield && g.isEquipment eq then
                  g.attachSourceTo eq host
                else g
              | none => g
            | _ => g) g
    | none =>
      g.logMsg "The enchanted creature has left. Equipment stays where it is."
  | what, hostSel =>
    let ctx : TriggerRead := { controller, sourceId, targets }
    match g.permanentsNamed ctx what, g.permanentsNamed ctx hostSel with
    | some eqs, some hosts =>
      match hosts[0]? with
      | some h =>
        g.withBatch none fun g =>
          eqs.foldl (fun g eq =>
            if eq.id == h.id || !eq.isOnBattlefield || !h.isOnBattlefield then g
            else g.attachSourceTo eq h) g
      | none => g
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
      g.change (.pending (.fraChoice controller (.mayCastFromGraveyard eligible)))
        |>.logMsg s!"{(g.player controller).name} may cast an artifact, instant, or sorcery spell from their graveyard"
  | .hand, .twiceLegendaryWizards, .withoutPaying, .none =>
    let wizards :=
      (g.permanentsOf controller).filter (fun o =>
        o.isLegendary && g.hasSubtype o .wizard) |>.size
    g.beginMayCastInstantSorceryFromHand controller (wizards * 2)
  | .hand, .lastKnown, .withoutPaying, .none =>
    g.beginMayCastInstantSorceryFromHand controller (lastKnownPower.getD 0).toNat
  | .nextRedOrGreenCreature, .unlimited, .withoutPaying, .none =>
    g.createEffect (.pendingFreeRGCreatureThisTurn controller)
      |>.logMsg "The next red or green creature spell you cast this turn can be cast without paying its mana cost"
  | .impulse, .unlimited, .withoutPaying, .none =>
    if !g.grimaImpulseReady then g
    else
      let victim := g.grimaImpulseVictim.getD (g.opponent controller)
      let found := g.grimaImpulseFound
      let others := g.grimaImpulseOthers
      let g := g.changes #[
        .grimaImpulseReady false,
        .grimaImpulseVictim none,
        .grimaImpulseFound none,
        .grimaImpulseOthers #[]]
      let cause := (found.orElse (fun _ => others[0]?)).bind g.lastMoveCauseOf?
      match found with
      | none =>
        g.requestOrderInto others (.library victim)
          s!"{(g.player victim).name} randomizes the exiled cards; they become that player's library"
          (cause := cause)
      | some cardId =>
        let name := (g.object! cardId).name
        g.beginFraChoice controller (.mayCastGrima cardId others victim)
          s!"{(g.player controller).name} may cast {name} without paying its mana cost"
  | origin, maxMv, cost, note =>
    let limit : Option Nat :=
      match maxMv with
      | .unlimited => none
      | .twiceLegendaryWizards =>
        some (((g.permanentsOf controller).filter (fun o =>
          o.isLegendary && g.hasSubtype o .wizard)).size * 2)
      | .lastKnown => some (lastKnownPower.getD 0).toNat
      | .greatestAttackingPower => some (g.greatestPowerAmongAttacking controller).toNat
      | .causingSpell => some (g.castSpellManaValue controller lastKnownPower)
    let within (o : GameObject) : Bool :=
      match limit with
      | none => true
      | some m => o.printed.manaValue ≤ m
    let withoutPaying := cost == .withoutPaying
    let exileInstead := note == .exileInstead
    let offer (g : Game) (eligible : Array ObjectId) (phrase : String) : Game :=
      if eligible.isEmpty then
        g.logMsg s!"{(g.player controller).name} has nothing to cast this way"
      else
        g.change (.pending (.fraChoice controller (.mayCastCards eligible withoutPaying exileInstead)))
          |>.logMsg phrase
    match origin with
    | .nextRedOrGreenCreature =>
      if withoutPaying then
        g.createEffect (.pendingFreeRGCreatureThisTurn controller)
          |>.logMsg "The next red or green creature spell you cast this turn can be cast without paying its mana cost"
      else g.logMsg "That creature spell is cast for its mana cost"
    | .hand =>
      let eligible := (g.player controller).hand.filter fun id =>
        (g.findObject? id).any fun o => o.printed.isInstantOrSorcery && within o
      offer g eligible
        s!"{(g.player controller).name} may cast an instant or sorcery from their hand"
    | .graveyard =>
      let eligible := (g.player controller).graveyard.filter fun id =>
        (g.findObject? id).any fun o =>
          (o.printed.isArtifact || o.printed.isInstantOrSorcery) && within o
      offer g eligible
        s!"{(g.player controller).name} may cast a spell from their graveyard"
    | .impulse =>
      if !g.grimaImpulseReady then g
      else
        let victim := g.grimaImpulseVictim.getD (g.opponent controller)
        let found := g.grimaImpulseFound
        let others := g.grimaImpulseOthers
        let g := g.changes #[
          .grimaImpulseReady false,
          .grimaImpulseVictim none,
          .grimaImpulseFound none,
          .grimaImpulseOthers #[]]
        let eligible :=
          (match found with
            | some id =>
              match g.findObject? id with
              | some o => if within o then #[id] else #[]
              | none => #[]
            | none => #[]) ++
            others.filter fun id => (g.findObject? id).any within
        let cause := (found.orElse (fun _ => others[0]?)).bind g.lastMoveCauseOf?
        if eligible.isEmpty then
          g.requestOrderInto others (.library victim)
            s!"{(g.player victim).name} randomizes the exiled cards; they become that player's library"
            (cause := cause)
        else
          offer g eligible
            s!"{(g.player controller).name} may cast a spell from among the exiled cards"
    | .looked =>
      let recorded := g.revealedIdsThisWay
      if recorded.isEmpty then g
      else
        let g := g.change (.revealedIdsThisWay #[])
        let eligible := recorded.filter fun id =>
          (g.findObject? id).any fun o => !o.printed.isLand && within o
        offer g eligible
          s!"{(g.player controller).name} may cast a spell from among the looked-at cards"
    | .milledSpell =>
      let eligible := g.milledIdsThisWay.filter fun id =>
        (g.findObject? id).any fun o =>
          (o.printed.isEnchantment || o.printed.isInstantOrSorcery) && within o
      offer g eligible
        s!"{(g.player controller).name} may cast a spell from among the milled cards"

/-- Resolve `TriggerResolution.amass`. Each printed combination keeps
the behavior of the constructor it replaced. Any other selector amasses
nothing. -/
def applyAmass (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (lastKnownPower : Option Int) (amount : TriggeredAbility.NumberSelector)
    (subtype : CardSubtype) (attachSource : Bool)
    (who : TriggeredAbility.PlayerSelector)
    (targets : Array Target := #[])
    (lastKnownToughness : Option Int := none) : Game :=
  let ctx : TriggerRead :=
    { controller, sourceId, targets, lastKnownPower, lastKnownToughness }
  let amassOne (g : Game) (pid : PlayerId) (n : Nat) : Game :=
    if attachSource then g.amass pid subtype n (attach := sourceId)
    else g.amass pid subtype n
  let amassEach (g : Game) (n : Nat) : Game :=
    match g.collectPlayers ctx who with
    | some pids => pids.foldl (fun g pid => amassOne g pid n) g
    | none => g
  match amount with
  | .notedExcess =>
    let excess := g.excessDamageThisWay
    let g := g.change (.excessDamageThisWay 0)
    if excess > 0 then
      let g := amassEach g excess
      g.logMsg s!"excess damage {excess} — amass {subtype}s {excess}"
    else g
  | .notedPower =>
    if g.destroyedForAmassThisWay then
      match g.triggerCount ctx .notedPower with
      | some n => amassEach g n
      | none => g
    else g
  | amount =>
    match g.triggerCount ctx amount with
    | some n => amassEach g n
    | none => g

/-- Resolve `TriggerResolution.discard`. Each printed combination keeps
the behavior of the constructor it replaced. Any other player the
selector names discards that many cards. A selector that does not name
cards discards nothing. -/
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
      let g := g.change (.discardedCardThisWay none)
      g.beginDiscardCards #[controller] n
  | .cards n .eachOpponent =>
    g.beginDiscardCards (g.apnapOrder.filter (· != controller)) n
  | .chosenNonland =>
    g.withLegalKindPlayer controller .opponent targets
      (fun g pid => g.discardNonlandFrom controller pid)
      sourceId (some "The target is no longer legal")
  | .cards n (.target .opponent) =>
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
      g.changes #[.handDiscardedThisWay none, .notedSourceThisWay sourceId]
        |>.beginFraChoice controller (.mayDiscardHandBalin sourceId)
          s!"{(g.player controller).name} may discard their hand"
  | .cards n who =>
    let ctx : TriggerRead := { controller, sourceId, targets }
    match g.collectPlayers ctx who with
    | some pids =>
      let g := g.change (.discardedCardThisWay none)
      g.beginDiscardCards pids n
    | none => g
  | _ => g

/-- Resolve `TriggerResolution.destroy`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyDestroy (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (lastKnownPower : Option Int) (what : TriggeredAbility.ObjectSelector)
    (note : TriggeredAbility.TriggerDestroyNote) : Game :=
  match what, note with
  | .oppArtifactsEnchantments, .countDestroyed =>
    g.withBatch none fun g =>
      Id.run do
        let mut g := g
        let mut n : Nat := 0
        for o in g.battlefield do
          if o.isOnBattlefield && !g.controlledBy o controller &&
              (g.isArtifact o || g.isEnchantment o) then
            g := g.destroyPermanent o
            -- Only permanents actually destroyed count (indestructible ones stay).
            if !(g.findObject? o.id).any (·.isOnBattlefield) then
              n := n + 1
        return g.change (.permanentsDestroyedThisWay n)
  | .permanentDealtDamage, .none =>
    match g.permanentDealtDamageThisWay with
    | none => g
    | some oid =>
      let g := g.change (.permanentDealtDamageThisWay none)
      match g.findObject? oid with
      | some o => if o.isOnBattlefield then g.destroyPermanent o else g
      | none => g
  | .target, .forAmass =>
    let clear := g.changes #[
      .destroyedForAmassThisWay false,
      .amassControllerThisWay none,
      .amassAmountThisWay 0,
      .amassYouControlledThisWay false]
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
          let oCtrl := g.controllerOf o
          let pw := lastKnownPower.getD (g.power o)
          let n := if pw > 0 then pw.toNat else 0
          let g := g.destroyPermanent o
          g.changes #[
            .destroyedForAmassThisWay true,
            .amassControllerThisWay oCtrl,
            .amassAmountThisWay n,
            .amassYouControlledThisWay (oCtrl == some controller)]
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
  | .whileSource, _ | .target .whileSource, _ =>
    g.withAffected controller ab sourceId targets .targetWhileSource fun g o =>
      g.applyPermanentAction o .destroy
  | what, note =>
    let ctx : TriggerRead :=
      { controller, sourceId, targets, lastKnownPower }
    match g.permanentsNamed ctx what with
    | none => g
    | some objs =>
      match note with
      | .countDestroyed =>
        g.withBatch none fun g =>
          Id.run do
            let mut g := g
            let mut n : Nat := 0
            for o in objs do
              g := g.destroyPermanent o
              if !(g.findObject? o.id).any (·.isOnBattlefield) then
                n := n + 1
            return g.change (.permanentsDestroyedThisWay n)
      | .forAmass =>
        match objs[0]? with
        | none =>
          g.changes #[
            .destroyedForAmassThisWay false,
            .amassControllerThisWay none,
            .amassAmountThisWay 0,
            .amassYouControlledThisWay false]
        | some o =>
          let oCtrl := g.controllerOf o
          let pw := lastKnownPower.getD (g.power o)
          let n := if pw > 0 then pw.toNat else 0
          let g := g.withBatch none fun g => objs.foldl (fun g o => g.destroyPermanent o) g
          g.changes #[
            .destroyedForAmassThisWay true,
            .amassControllerThisWay oCtrl,
            .amassAmountThisWay n,
            .amassYouControlledThisWay (oCtrl == some controller)]
      | .chosenToken =>
        g.withBatch none fun g =>
          objs.foldl (fun g o => if o.printed.isToken then g.destroyPermanent o else g) g
      | .none =>
        g.withBatch none fun g =>
          objs.foldl (fun g o => g.destroyPermanent o) g

/-- Resolve `TriggerResolution.addMana`. Each printed combination keeps
the behavior of the constructor it replaced. Any other count adds that
much mana. A count that cannot be read adds nothing. -/
def applyAddMana (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (types : Array ManaType) (amount : TriggeredAbility.NumberSelector)
    (targets : Array Target := #[])
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none) : Game :=
  let ctx : TriggerRead :=
    { controller, sourceId, targets, lastKnownPower, lastKnownToughness }
  -- Zero additions log nothing. `.perChargeCounter` uses the last-known
  -- charge total when the source has left.
  match g.triggerCount ctx amount with
  | none => g
  | some n =>
    if n == 0 then g
    else
      let types := types.foldl (fun acc t => acc ++ Array.replicate n t) #[]
      g.addManaLogged controller types

/-- Resolve `TriggerResolution.draw`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyTriggerDraw (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (amount : TriggeredAbility.NumberSelector)
    (who : TriggeredAbility.PlayerSelector)
    (targets : Array Target := #[])
    (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none)
    (sequencedCardPower : Option Nat := none) : Game :=
  let ctx : TriggerRead := {
    controller, sourceId, targets, lastKnownPower, lastKnownToughness, sequencedCardPower }
  match who, amount with
  | .controller .enchanted, amount =>
    match g.attachedHost? sourceId with
    | some host =>
      match g.triggerCount ctx amount with
      | some n =>
        if n == 0 then g else g.draw ((g.controllerOf host).getD host.owner) n
      | none => g
    | none =>
      g.logMsg "The enchanted creature has left. No card is drawn."
  | .you, .upToHandSize k =>
    g.drawUpToHandSize controller k
  | .opponentHasYou, _ =>
    match g.palantirChoiceReady with
    | none => g
    | some (c, opp, sid) =>
      (g.change (.palantirChoiceReady none)).offerPalantirChoice c opp sid
  | .you, .perControlled ty =>
    let n := ((g.permanentsOf controller).filter (fun o => g.hasType o ty)).size
    if n == 0 then g else g.draw controller n
  | .eachOpponent, .fixed n =>
    if n.toNat == 0 then g
    else
      g.withBatch (g.resolvingBatchCause controller sourceId) fun g =>
        g.forEachOpponent controller (fun g pid => g.draw pid n.toNat)
  | .you, .fixed n =>
    g.draw controller n.toNat
  | .you, .forEachTappedHuman =>
    let n := g.humansTappedThisWay
    let g := g.change (.humansTappedThisWay 0)
    if n == 0 then g else g.draw controller n
  | .you, .perFatGraveyard =>
    g.drawPerSevenCardGraveyard controller
  | .you, .discardedHand =>
    match g.handDiscardedThisWay with
    | some n => if n == 0 then g else g.draw controller n
    | none => g
  | .you, .equalToManaSpent =>
    let spent :=
      match g.resolvingAbilityObject?.bind (·.fraCauseId) with
      | some id => GameEvent.manaSpentOn g.events id
      | none => 0
    if spent == 0 then
      g.change (.skipTriggerSequenceRest true)
        |>.logMsg "No mana was spent to cast that spell"
    else g.draw controller spent
  | who, amount =>
    match g.triggerCount ctx amount, g.collectPlayers ctx who with
    | some n, some pids =>
      let g :=
        match amount with
        | .forEachTappedHuman => g.change (.humansTappedThisWay 0)
        | _ => g
      if n == 0 || pids.isEmpty then g
      else
        g.withBatch (g.resolvingBatchCause controller sourceId) fun g =>
          pids.foldl (fun g pid => g.draw pid n) g
    | _, _ => g

/-- Resolve `TriggerResolution.returnToHand`. Each printed combination keeps
the behavior of the constructor it replaced. Any other permanent the
selector names returns to its owner's hand. A card or a hand returns
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
    let g := g.change (.returnedPermanentThisWay false)
    g.withLegalKindPermanent controller ab.targetKind targets (fun g o =>
      let g := g.returnToHand o.id o.owner
      g.change (.returnedPermanentThisWay true)) sourceId none
  | .graveyardPermanent, .none =>
    g.withLegalKindTarget controller ab.targetKind targets (fun g tgt =>
      match tgt with
      | Target.card id | Target.permanent id =>
        g.returnToHand id controller
      | _ => g) sourceId (some "The target is no longer legal")
  | .milledSubtype subtype, .none =>
    let ids := g.milledIdsThisWay
    let stashed :=
      g.stashedCause.orElse (fun _ => ids[0]?.bind g.lastMoveCauseOf?)
    let g := (if g.stashedCause.isSome then g.change (.stashedCause none) else g).change
      (.milledIdsThisWay #[])
    let (g, cause?) : Game × Option EventCause :=
      match stashed with
      | some c => (g, some c)
      | none =>
        if ids.any (fun id => (g.findObject? id).any (·.printed.hasSubtype subtype)) then
          match g.currentResolvingContext? with
          | some (src, ctrl) =>
            let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some controller)) (src.orElse (fun _ => sourceId))
            (g, some c)
          | none => (g, none)
        else (g, none)
    g.withBatch cause? fun g =>
      ids.foldl (fun acc id =>
        match acc.findObject? id with
        | some o =>
          if o.printed.hasSubtype subtype then
            let name := o.name
            let (acc, _) := acc.move id (.hand controller) none (cause := cause?)
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
  | .cause _, .none =>
    g.returnCauseToOwnerHand targets
  | .revealed, _ =>
    let ids := g.revealedIdsThisWay
    let stashed :=
      g.stashedCause.orElse (fun _ => ids[0]?.bind g.lastMoveCauseOf?)
    let g := (if g.stashedCause.isSome then g.change (.stashedCause none) else g).change
      (.revealedIdsThisWay #[])
    let (g, cause?) : Game × Option EventCause :=
      match stashed with
      | some c => (g, some c)
      | none =>
        if ids.isEmpty then (g, none)
        else
          let (g, c) := g.allocDelayedCause (some controller) sourceId
          (g, some c)
    g.withBatch cause? fun g =>
      ids.foldl (fun g id =>
        match g.findObject? id with
        | some o =>
          let name := o.name
          let (g, _) := g.move id (.hand controller) none (cause := cause?)
          g.logMsg s!"{name} is put into {(g.player controller).name}'s hand"
        | none => g) g
  | what, note =>
    let ctx : TriggerRead := { controller, sourceId, targets }
    match g.permanentsNamed ctx what with
    | none => g
    | some objs =>
      let g :=
        match note with
        | .returnedPermanent => g.change (.returnedPermanentThisWay false)
        | .none => g
      let (g, cause?) : Game × Option EventCause :=
        if objs.isEmpty then (g, none)
        else
          let (g, c) := g.allocDelayedCause (some controller) sourceId
          (g, some c)
      g.withBatch cause? fun g =>
        objs.foldl (fun g o =>
          let g := g.returnToHand o.id o.owner (cause := cause?)
          match note with
          | .returnedPermanent => g.change (.returnedPermanentThisWay true)
          | .none => g) g

/-- Resolve `TriggerResolution.put`. Each printed combination keeps
the behavior of the constructor it replaced. A graveyard card, the top
of the library, a graveyard source, or a recorded cause enters as `how`
and `note` say. A hand or an unmade choice puts nothing. -/
def applyPut (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (what : TriggeredAbility.ObjectSelector)
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
        let (g, newId) := g.putOntoBattlefield src.id controller (returnedAsArtifact := true)
        let o := g.object! newId
        g.logMsg s!"{o.name} returns as an artifact"
  | .notedLands, .tapped, _ =>
    let ids := g.exiledIdsThisWay
    let g := g.change (.exiledIdsThisWay #[])
    g.withBatch none fun g =>
      ids.foldl (fun g id =>
        match g.findObject? id with
        | none => g
        | some o =>
          let name := o.name
          let (g, retId) := g.move id .battlefield (some o.owner) (tapped := true)
          let g := g.logMsg s!"{name} is exiled, then returned tapped"
          g.afterLandEnters (g.object! retId)) g
  | .discardedLand, .tapped, _ =>
    match g.discardedCardThisWay with
    | none => g
    | some (pid, id) =>
      let g := g.change (.discardedCardThisWay none)
      match g.findObject? id with
      | some o =>
        if o.printed.isLand && o.zone == .graveyard o.owner then
          let entered := g.putOntoBattlefield o.id pid (tapped := true)
          let g := entered.1.logMsg s!"{o.name} enters the battlefield tapped"
          g.afterLandEnters (g.object! entered.2)
        else g
      | none => g
  | .landFromHand, .tapped, _ =>
    g.change (.pending (.mayPutLandFromHand controller))
      |>.logMsg s!"{(g.player controller).name} may put a land card from their hand onto the battlefield tapped"
  | .artifactFromHand, _, .forAttach =>
    let g := g.change (.putArtifactThisWay none)
    let arts :=
      (g.player controller).hand.filterMap (fun id =>
        match g.findObject? id with
        | some o => if o.printed.isArtifact then some o else none
        | none => none)
    if arts.isEmpty then
      g.logMsg "There is no artifact card in your hand"
    else
      g.change (.pending (.mayPutArtifactFromHand controller (sourceId.getD ⟨0⟩)))
        |>.logMsg s!"{(g.player controller).name} may put an artifact card from their hand onto the battlefield"
  | .source, .underOwner, note =>
    g.returnSourceUnderOwner controller sourceId note.enterMods
  | .cause subtype, .underOwner, note =>
    g.returnCauseUnderOwner controller targets subtype note.enterMods
  | .revealed, how, note =>
    let ids := g.revealedIdsThisWay
    let stashed :=
      g.stashedCause.orElse (fun _ => ids[0]?.bind g.lastMoveCauseOf?)
    let g := (if g.stashedCause.isSome then g.change (.stashedCause none) else g).change
      (.revealedIdsThisWay #[])
    let (g, cause?) : Game × Option EventCause :=
      match stashed with
      | some c => (g, some c)
      | none =>
        if ids.isEmpty then (g, none)
        else
          let (g, c) := g.allocDelayedCause (some controller) sourceId
          (g, some c)
    let tapped := how == .tapped
    let returnedAsArtifact := how == .asArtifact
    let extra := enterModsExtraCounters note.enterMods
    let items := ids.filterMap fun id =>
      match g.findObject? id with
      | none => none
      | some o =>
        let owner :=
          match how with
          | .underOwner => o.owner
          | _ => controller
        let options := g.enterModsAttackOptions owner note.enterMods
        some (EnteringAttackItem.card id owner controller tapped returnedAsArtifact
          extra note.enterMods .putOntoBattlefield options)
    g.promptEnteringAttackItems items (cause := cause?)
  | .randomCreature, _, _ =>
    let ids := g.revealedIdsThisWay
    if ids.isEmpty then g
    else
      let stashed :=
        g.stashedCause.orElse (fun _ => ids[0]?.bind g.lastMoveCauseOf?)
      let g := (if g.stashedCause.isSome then g.change (.stashedCause none) else g).change
        (.revealedIdsThisWay #[])
      let (g, cause) : Game × EventCause :=
        match stashed with
        | some c => (g, c)
        | none => g.allocDelayedCause (some controller) sourceId
      let creatures := ids.filter fun id =>
        (g.findObject? id).any (·.printed.isCreature)
      let libraryOwner :=
        match ids[0]?.bind g.findObject? with
        | some o => o.owner
        | none => controller
      if creatures.isEmpty then
        (g.logMsg "No creature card was revealed").putRestOnBottomRandom libraryOwner ids
          (cause := some cause)
      else if creatures.size > 1 then
        let g := g.change (.stashedCause (some cause))
        g.changes #[
          .pending (.resolveRandom (.chooseObject creatures)),
          .afterRandom (.revealRandomCreatureThenBottom controller ids)]
          |>.logMsg
            s!"{(g.player controller).name} puts a random creature from among them onto the battlefield"
      else
        g.resolveRandomCreatureReveal controller ids creatures[0]! (cause := some cause)
  | what, how, note =>
    let inGraveyard (o : GameObject) : Bool :=
      match o.zone with
      | .graveyard _ => true
      | _ => false
    let cards : Array GameObject :=
      match what with
      | .graveyardCard | .graveyardPermanent | .creatureCard =>
        targets.filterMap fun
          | Target.card id | Target.permanent id =>
            match g.findObject? id with
            | some o => if inGraveyard o then some o else none
            | none => none
          | _ => none
      | .top =>
        match (g.player controller).library.back?.bind g.findObject? with
        | some o => #[o]
        | none => #[]
      | .source =>
        match sourceId.bind g.findObject? with
        | some o => if inGraveyard o then #[o] else #[]
        | none => #[]
      | .cause subtype =>
        let causeId :=
          ((g.resolvingAbility.bind g.findObject?).bind (·.fraCauseId)).map g.followMoved
        match causeId.bind g.findObject? with
        | some o =>
          let zoneOk := o.zone != Zone.battlefield
          let subOk :=
            match subtype with
            | some s => g.hasSubtype o s
            | none => true
          if zoneOk && subOk then #[o] else #[]
        | none => #[]
      | _ => #[]
    if cards.isEmpty then g
    else
      let (g, cause) := g.allocDelayedCause (some controller) sourceId
      let tapped := how == .tapped
      let returnedAsArtifact := how == .asArtifact
      let extra := enterModsExtraCounters note.enterMods
      let items := cards.map fun o =>
        let owner :=
          match how with
          | .underOwner => o.owner
          | _ => controller
        let options := g.enterModsAttackOptions owner note.enterMods
        EnteringAttackItem.card o.id owner controller tapped returnedAsArtifact
          extra note.enterMods .putOntoBattlefield options
      g.promptEnteringAttackItems items (cause := some cause)

/-- Resolve `TriggerResolution.grant`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyGrant (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (what : TriggeredAbility.TriggerGrantWhat)
    (who : TriggeredAbility.ObjectSelector) : Game :=
  match what, who with
  | .doubleStrike, .equippedAttackers =>
    g.withBatch none fun g =>
      Id.run do
        let mut g := g
        for o in g.battlefield do
          if o.status.attacking && o.attachedTo.isSome ||
              (o.status.attacking &&
                g.battlefield.any (fun eq => eq.attachedTo == some o.id)) then
            if g.isCreature o && o.status.attacking &&
                g.battlefield.any (fun eq => eq.attachedTo == some o.id) then
              g := g.grantUntilEotLogged o Keyword.doubleStrike
        return g
  | .protectionEverything, .youIfCast =>
    if !sourceId.any g.wasCast then
      g.logMsg "It wasn't cast. The ability does nothing."
    else
      g.createEffect (.protectionFromEverything controller)
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
  | .keywords k, .whileSource | .keywords k, .target .whileSource =>
    g.withAffected controller ab sourceId targets .targetWhileSource fun g o =>
      g.applyPermanentAction o (.grantKeywords k)
  | .keywords k, .creaturesYouControl =>
    g.forEachControlledCreature controller fun g o =>
      g.grantUntilEotLogged o k
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
    g.createEffect (.assignCombatDamageEqualToughnessUntilEot controller)
      |>.logMsg "Creatures you control assign combat damage equal to their toughness"
  | .basePowerEqualHand, .source =>
    g.grantHandSizePower sourceId
  | .ironFistTap, .source =>
    g.grantIronFistTap sourceId
  | .keywords k, .spellTargets =>
    g.grantKeywordsToSpellCreatureTargets k
  | .protectionEverything, who =>
    let ctx : TriggerRead := { controller, sourceId, targets }
    match g.permanentsNamed ctx who with
    | none => g
    | some objs =>
      let pids := objs.foldl (fun acc o =>
        match g.controllerOf o with
        | some pid => if acc.contains pid then acc else acc.push pid
        | none => acc) #[]
      pids.foldl (fun g pid =>
        g.createEffect (.protectionFromEverything pid)
          |>.logMsg s!"{(g.player pid).name} gains protection from everything") g
  | .assignCombatDamageEqualToughness, who =>
    let ctx : TriggerRead := { controller, sourceId, targets }
    match g.permanentsNamed ctx who with
    | some objs =>
      match objs.findSome? (g.controllerOf ·) with
      | some pid =>
        g.createEffect (.assignCombatDamageEqualToughnessUntilEot pid)
          |>.logMsg "Creatures you control assign combat damage equal to their toughness"
      | none => g
    | none => g
  | .doubleStrike, who =>
    let ctx : TriggerRead := { controller, sourceId, targets }
    match g.permanentsNamed ctx who with
    | some objs =>
      g.withBatch none fun g =>
        objs.foldl (fun g o => g.grantUntilEotLogged o Keyword.doubleStrike) g
    | none => g
  | .keywords k, who =>
    let ctx : TriggerRead := { controller, sourceId, targets }
    match g.permanentsNamed ctx who with
    | some objs =>
      g.withBatch none fun g =>
        objs.foldl (fun g o => g.grantUntilEotLogged o k) g
    | none => g
  | what, who =>
    let ctx : TriggerRead := { controller, sourceId, targets }
    let grantOne (g : Game) (o : GameObject) : Game :=
      match what with
      | .hexproofWhileSource =>
        match sourceId with
        | some sid =>
          let g := g.createEffect (.hexproofWhileSource o.id sid)
          g.logMsg s!"{g.name o} gains hexproof for as long as the source remains"
        | none => g
      | .preventDamageWhileSource =>
        match sourceId with
        | some sid =>
          let g := g.createEffect (.preventDamageWhileSource o.id sid)
          g.logMsg
            s!"damage that would be dealt by {g.name o} is prevented while the source remains"
        | none => g
      | .landfallCreateElf => g.gainLandfallCreateElf (some o.id)
      | .basePowerEqualHand =>
        g.createEffect (.cardsInHandPowerUntilEot o.id)
          |>.logMsg
            s!"{g.name o}'s base power is the number of cards in your hand until end of turn"
      | .ironFistTap =>
        g.createEffect (.ironFistTapUntilEot o.id)
          |>.logMsg s!"{g.name o} gains a tap ability until end of turn"
      | .doubleStrike | .keywords _ | .protectionEverything
        | .assignCombatDamageEqualToughness => g
    match g.permanentsNamed ctx who with
    | some objs => g.withBatch none fun g => objs.foldl grantOne g
    | none => g

/-- Resolve `TriggerResolution.fight`. Each printed combination keeps
the behavior of the constructor it replaced. -/
def applyFight (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (targets : Array Target) (who : TriggeredAbility.ObjectSelector)
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
            g.isCreature src && g.isCreature dest && g.controlledBy src controller then
          g.fightCreatures src dest
        else g.logMsg "The target is no longer legal"
      | _, _ => g.logMsg "The target is no longer legal"
    | some (Target.permanent srcId), none =>
      match g.findObject? srcId with
      | some src => g.logMsg s!"{g.name src} has nothing to fight"
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
      let g := g.change (.equipmentAttachedHost none)
      match g.findObject? hostId with
      | some host =>
        if !host.isOnBattlefield then g
        else
          let effect : Effect :=
            { targeting := .of .creature, allowsZeroTargets := true
              resolution := .damageEqualSourcePower
              phrase := s!"{g.name host} deals damage equal to its power to up to one target creature" }
          g.putReflexiveTrigger controller (some hostId) effect
      | none => g
  | .announced, .timesPower k =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent srcId), some (Target.permanent destId) =>
      let srcOk := (g.legalCreatureYouControlTargets controller).contains
        (Target.permanent srcId)
      let destOk := (g.legalOppCreatureTargets controller).contains
        (Target.permanent destId)
      if srcOk && destOk then
        let src := g.object! srcId
        let dest := g.object! destId
        if k == 1 then g.dealFightDamage src dest
        else
          let pw := g.power src
          let n := if pw > 0 then pw * (k : Int) else 0
          g.dealDamageFrom (g.name src) dest n (source := some src)
      else
        let logIllegal (g : Game) (ok : Bool) (id : ObjectId) : Game :=
          if ok then g else g.illegalAbilityTarget (Target.permanent id)
        logIllegal (logIllegal g srcOk srcId) destOk destId
    | _, _ => g.logMsg "The target is no longer legal"
  | who, how =>
    let ctx : TriggerRead := { controller, sourceId, targets }
    match g.permanentsNamed ctx who with
    | none => g
    | some fighters =>
      let foe? :=
        targets.findSome? fun
          | Target.permanent id =>
            match g.findObject? id with
            | some o =>
              if o.isOnBattlefield && g.isCreature o && !fighters.any (·.id == o.id) then
                some o
              else none
            | none => none
          | _ => none
      match how with
      | .reflexive =>
        match foe? with
        | some foe =>
          if fighters.isEmpty then g
          else
            g.withBatch (g.resolvingBatchCause controller sourceId) fun g =>
              fighters.foldl (fun g f =>
                if f.isOnBattlefield && g.isCreature f then
                  g.dealDamageFrom (g.name f) foe (g.power f) (source := some f)
                else g) g
        | none =>
          fighters.foldl (fun g f =>
            if !f.isOnBattlefield || !g.isCreature f then g
            else
              let effect : Effect :=
                { targeting := .of .creature, allowsZeroTargets := true
                  resolution := .damageEqualSourcePower
                  phrase :=
                    s!"{g.name f} deals damage equal to its power to up to one target creature" }
              g.putReflexiveTrigger controller (some f.id) effect) g
      | .mutual | .upToOneOther =>
        match foe? with
        | some foe =>
          if fighters.isEmpty then g
          else
            g.withBatch (g.resolvingBatchCause controller sourceId) fun g =>
              fighters.foldl (fun g f =>
                if f.isOnBattlefield && g.isCreature f && f.id != foe.id then
                  g.fightCreatures f foe
                else g) g
        | none =>
          fighters.foldl (fun g f =>
            if f.isOnBattlefield && g.isCreature f then
              g.logMsg s!"{g.name f} has nothing to fight"
            else g) g
      | .timesPower k =>
        match foe? with
        | some foe =>
          if fighters.isEmpty then g
          else
            g.withBatch (g.resolvingBatchCause controller sourceId) fun g =>
              fighters.foldl (fun g f =>
                if f.isOnBattlefield && g.isCreature f && f.id != foe.id then
                  if k == 1 then g.dealFightDamage f foe
                  else
                    let pw := g.power f
                    let n := if pw > 0 then pw * (k : Int) else 0
                    g.dealDamageFrom (g.name f) foe n (source := some f)
                else g) g
        | none =>
          fighters.foldl (fun g f =>
            if f.isOnBattlefield && g.isCreature f then
              g.logMsg s!"{g.name f} has nothing to fight"
            else g) g

/-- Resolve `TriggerResolution.mill`. Each printed combination keeps
the behavior of the constructor it replaced. Any other count is milled
by the players the selector names. A missing count or player mills
nothing. -/
def applyMill (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (lastKnownPower lastKnownToughness : Option Int)
    (amount : TriggeredAbility.NumberSelector)
    (who : TriggeredAbility.PlayerSelector)
    (note : TriggeredAbility.TriggerMillNote) : Game :=
  match amount, who, note with
  | .fixed n, .you, .none =>
    g.mill controller n.toNat
  | .fixed n, .you, .milledCards =>
    g.millCollected controller #[controller] n.toNat .milledCards
  | .fixed n, .target .player, .none =>
    g.withLegalTriggerPlayer controller ab sourceId targets (fun g pid => g.mill pid n.toNat)
  | .thatManyLost, .thatPlayer, .none =>
    match lastKnownPower, lastKnownToughness with
    | some k, some idx => g.mill ⟨idx.toNat⟩ k.toNat
    | _, _ => g
  | .fixed n, .eachOpponent, .opponentsMilled =>
    let opps := (g.livingOpponents controller).map (·.id)
    let (g, milled) := g.millThenReflexive opps n.toNat
    g.change (.opponentsMilledThisWay milled)
  | amount, who, note =>
    let ctx : TriggerRead := {
      controller, sourceId, targets, lastKnownPower, lastKnownToughness }
    match g.triggerCount ctx amount with
    | none => g
    | some n =>
      match who with
      | .target .player | .target .opponent =>
        g.withLegalTriggerPlayer controller ab sourceId targets fun g pid =>
          g.millCollected controller #[pid] n note
      | _ =>
        match g.collectPlayers ctx who with
        | some pids => g.millCollected controller pids n note
        | none => g

/-- Resolve `TriggerResolution.untap`. Each printed combination keeps
the behavior of the constructor it replaced. A stun counter is removed
instead of untapping (CR 122.1d). -/
def applyUntap (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (who : TriggeredAbility.ObjectSelector) : Game :=
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
  | .whileSource | .target .whileSource =>
    g.withAffected controller ab sourceId targets .targetWhileSource fun g o =>
      g.applyPermanentAction o .untap
  | .equipped =>
    match g.attachedHost? sourceId with
    | some host =>
      if host.isOnBattlefield then g.applyPermanentAction host .untap
      else
        g.change (.skipTriggerSequenceRest true) |>.logMsg "The equipped creature has left"
    | none =>
      g.change (.skipTriggerSequenceRest true) |>.logMsg "The equipped creature has left"
  | .firstThisTurn =>
    let id := g.resolvingCauseId.orElse (fun _ => g.loggedLastBecameTapped)
    match id.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield && o.status.tapped then g.applyPermanentAction o .untap else g
    | none => g
  | who =>
    let ctx : TriggerRead := { controller, sourceId, targets }
    match g.permanentsNamed ctx who with
    | some objs => g.withBatch none fun g => objs.foldl (fun g o => g.applyPermanentAction o .untap) g
    | none => g

/-- Resolve `TriggerResolution.tap`. Each printed combination keeps
the behavior of the constructor it replaced. Any other permanent the
selector names is tapped. A card or a hand taps nothing. -/
def applyTap (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (who : TriggeredAbility.ObjectSelector) : Game :=
  match who with
  | .humans =>
    g.changes #[.pending (.tapHumans controller), .humansTappedThisWay 0]
      |>.logMsg s!"{(g.player controller).name} may tap any number of untapped Humans they control"
  | .enchanted =>
    match sourceId.bind g.findObject? with
    | none => g
    | some src =>
      match src.attachedTo.bind g.findObject? with
      | none => g.logMsg "Nothing is enchanted"
      | some host => g.applyPermanentAction host .tap
  | .ifPresent | .target .ifPresent =>
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
            s!"{(g.player controller).name} may tap {g.name src}"
        else
          (g.logMsg s!"{g.name src} can't be tapped this way. The reflexive ability doesn't trigger.").failMayThen
      | none =>
        (g.logMsg "The source is no longer on the battlefield. The reflexive ability doesn't trigger.").failMayThen
    else
      g.withAffected controller ab sourceId targets .source fun g o =>
        g.applyPermanentAction o .tap
  | .enchantedWhileSource =>
    g.withAffected controller ab sourceId targets .enchanted fun g o =>
      g.applyPermanentAction o .tap
  | .whileSource | .target .whileSource =>
    g.withAffected controller ab sourceId targets .targetWhileSource fun g o =>
      g.applyPermanentAction o .tap
  | who =>
    let ctx : TriggerRead := { controller, sourceId, targets }
    match g.permanentsNamed ctx who with
    | some objs => g.withBatch none fun g => objs.foldl (fun g o => g.applyPermanentAction o .tap) g
    | none => g

/-- Resolve `TriggerResolution.removeCounters`. Each printed combination keeps
the behavior of the constructor it replaced. Any other permanent the
selector names loses that counter. A card or a hand loses nothing. -/
def applyRemoveCounters (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (targets : Array Target)
    (what : TriggeredAbility.TriggerRemoveWhat)
    (who : TriggeredAbility.ObjectSelector) : Game :=
  match what, who with
  | .hope, .source =>
    let g := g.change (.removedHopeThisWay false)
    g.withTriggerSource sourceId fun g src =>
      if src.status.hope == 0 then g
      else
        let g := g.recordRemoveCounters src.id .hope 1 (byPlayer := some controller)
        let g := g.logMsg s!"{g.name src} loses a hope counter"
        g.change (.removedHopeThisWay true)
  | .all, .enchanted =>
    match sourceId.bind g.findObject? with
    | none => g
    | some src =>
      match src.attachedTo.bind g.findObject? with
      | none => g
      | some host =>
        let g := g.removeAllCountersFrom host.id (byPlayer := some controller)
        g.logMsg s!"counters are removed from {g.name host}"
  | what, who =>
    let ctx : TriggerRead := { controller, sourceId, targets }
    match g.permanentsNamed ctx who with
    | none => g
    | some objs =>
      match what with
      | .hope =>
        let g := g.change (.removedHopeThisWay false)
        g.withBatch none fun g =>
          objs.foldl (fun g o =>
            if o.status.hope == 0 then g
            else
              let g := g.recordRemoveCounters o.id .hope 1 (byPlayer := some controller)
              let g := g.logMsg s!"{g.name o} loses a hope counter"
              g.change (.removedHopeThisWay true)) g
      | .all =>
        g.withBatch none fun g =>
          objs.foldl (fun g o =>
            let g := g.removeAllCountersFrom o.id (byPlayer := some controller)
            g.logMsg s!"counters are removed from {g.name o}") g

/-- Resolve `TriggerResolution.loseLife`. Each printed combination keeps
the behavior of the constructor it replaced. Any other count is lost by
the players the selector names. A missing count or player loses nothing. -/
def applyLoseLife (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (amount : TriggeredAbility.NumberSelector)
    (who : TriggeredAbility.PlayerSelector)
    (lastKnownPower : Option Int := none)
    (cause : Option EventCause := none) : Game :=
  match amount, who with
  | .fixed n, .you =>
    g.loseLife controller n.toNat (cause := cause)
  | .fixed n, .target .opponent =>
    g.withLegalTriggerPlayer controller ab sourceId targets (fun g pid =>
      g.loseLife pid n.toNat (cause := cause))
  | .fixed n, .eachOpponent =>
    g.loseLifeEachOpponent controller n.toNat (cause := cause)
  | .perBurden, .you =>
    match sourceId.bind g.findObject? with
    | none => g
    | some src => g.loseLife controller src.status.burden (cause := cause)
  | .attachedEquipment, .eachOpponent =>
    let x := g.attachedEquipmentAtResolution sourceId lastKnownPower
    if x == 0 then g
    else g.loseLifeEachOpponent controller x (cause := cause)
  | amount, who =>
    let ctx : TriggerRead :=
      { controller, sourceId, targets, lastKnownPower }
    match g.triggerCount ctx amount with
    | none => g
    | some n =>
      match who with
      | .target .player | .target .opponent =>
        g.withLegalTriggerPlayer controller ab sourceId targets fun g pid =>
          g.loseLife pid n (cause := cause)
      | _ =>
        match g.collectPlayers ctx who with
        | some pids =>
          if n == 0 || pids.isEmpty then g
          else
            let batchCause := cause.orElse (fun _ => g.resolvingBatchCause controller sourceId)
            g.withBatch batchCause fun g =>
              pids.foldl (fun g pid => g.loseLife pid n (cause := cause)) g
        | none => g

/-- Resolve `TriggerResolution.gainLife`. Each printed combination keeps
the behavior of the constructor it replaced. Any other count is gained.
A count that cannot be read gains nothing. -/
def applyGainLife (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (amount : TriggeredAbility.NumberSelector)
    (sequencedCardPower : Option Nat)
    (lastKnownPower : Option Int := none)
    (cause : Option EventCause := none) : Game :=
  match amount with
  | .fixed n =>
    g.gainLife controller n.toNat (cause := cause)
  | .attachedEquipment =>
    let x := g.attachedEquipmentAtResolution sourceId lastKnownPower
    if x == 0 then g else g.gainLife controller x (cause := cause)
  | .equalToTargetPower =>
    match sequencedCardPower with
    | some k => g.gainLife controller k (cause := cause)
    | none =>
      g.withLegalTriggerTarget controller ab sourceId targets fun g t =>
        match t with
        | Target.card oid | Target.permanent oid =>
          match g.findObject? oid with
          | some o => g.gainLife controller (g.power o).toNat (cause := cause)
          | none => g.logMsg "The target is no longer in the graveyard"
        | _ => g.logMsg "The target is no longer legal"
  | .forEachDestroyedThisWay =>
    let k := g.permanentsDestroyedThisWay
    let g := g.change (.permanentsDestroyedThisWay 0)
    if k == 0 then g else g.gainLife controller k (cause := cause)
  | .perOtherCreature =>
    let k :=
      ((g.creaturesControlledBy controller).filter (fun o => some o.id != sourceId)).size
    if k == 0 then g else g.gainLife controller k (cause := cause)
  | amount =>
    let ctx : TriggerRead := {
      controller, sourceId, targets, lastKnownPower, sequencedCardPower }
    match amount with
    | .forEachDestroyedThisWay =>
      let k := (g.triggerCount ctx amount).getD 0
      let g := g.change (.permanentsDestroyedThisWay 0)
      g.gainLife controller k (cause := cause)
    | _ =>
      match g.triggerCount ctx amount with
      | some k => g.gainLife controller k (cause := cause)
      | none => g

/-- Reveal cards from the top of a library until `stop`, or `fuel` runs out.
Non-matching cards are exiled and returned in `rest`. -/
def revealUntil (g : Game) (pid : PlayerId) (fuel : Nat)
    (stop : GameObject → Bool) (rest : Array ObjectId)
    (cause : Option EventCause := none) :
    Game × Option ObjectId × Array ObjectId :=
  match fuel with
  | 0 => (g, none, rest)
  | fuel + 1 =>
    if (g.player pid).library.isEmpty then (g, none, rest)
    else
      let top := (g.player pid).library.back!
      let o := g.object! top
      let g := g.logMsg s!"{(g.player pid).name} reveals {o.name}"
      if stop o then (g, some top, rest)
      else
        let (g, newId) := g.move top .exile none (cause := cause)
        revealUntil g pid fuel stop (rest.push newId) (cause := cause)

/-- Look through the libraries `who` names, as `how` says, and remember the
cards that were found. Returns any remaining revealed cards to put on the
bottom of their owner's library after `thenDo` resolves. -/
def noteRevealedLibraries (g : Game) (controller : PlayerId)
    (targets : Array Target) (sourceId : Option ObjectId)
    (how : TriggeredAbility.TriggerLibraryHow)
    (who : TriggeredAbility.PlayerSelector)
    (lastKnownToughness : Option Int := none)
    (cause : Option EventCause := none) : Game × Array (PlayerId × Array ObjectId) :=
  let ctx : TriggerRead := { controller, sourceId, targets, lastKnownToughness }
  match g.collectPlayers ctx who with
  | none => (g, #[])
  | some pids =>
    Id.run do
      let mut g := g
      let mut found : Array ObjectId := #[]
      let mut rests : Array (PlayerId × Array ObjectId) := #[]
      for pid in pids do
        match how with
        | .top n =>
          let ids := g.scryLookedIds pid n
          for id in ids do
            match g.findObject? id with
            | some o => g := g.logMsg s!"{(g.player pid).name} reveals {o.name}"
            | none => pure ()
          found := found ++ ids
        | .untilCreature =>
          let (g', hit, rest) :=
            revealUntil g pid (g.player pid).library.size (·.printed.isCreature) #[] (cause := cause)
          g := g'
          if !rest.isEmpty then rests := rests.push (pid, rest)
          match hit with
          | some id => found := found.push id
          | none => pure ()
        | .untilSaga =>
          let (g', hit, rest) :=
            revealUntil g pid (g.player pid).library.size (fun o => o.printed.saga.isSome) #[] (cause := cause)
          g := g'
          if !rest.isEmpty then rests := rests.push (pid, rest)
          match hit with
          | some id => found := found.push id
          | none => pure ()
        | .untilInstantOrSorcery =>
          let (g', hit, rest) :=
            revealUntil g pid (g.player pid).library.size (·.printed.isInstantOrSorcery) #[] (cause := cause)
          g := g'
          if !rest.isEmpty then rests := rests.push (pid, rest)
          match hit with
          | some id => found := found.push id
          | none => pure ()
        | .untilNonland =>
          let (g', hit, rest) :=
            revealUntil g pid (g.player pid).library.size (fun o => !o.printed.isLand) #[] (cause := cause)
          g := g'
          if !rest.isEmpty then rests := rests.push (pid, rest)
          match hit with
          | some id => found := found.push id
          | none => pure ()
      match cause with
      | some c =>
        if !found.isEmpty then
          g := g.change (.stashedCause (some c))
      | none => pure ()
      return (g.change (.revealedIdsThisWay found), rests)

/-- Resolve `TriggerResolution.revealLibrary`. Each printed combination
keeps the behavior of the constructor it replaced. Any other selector
reveals as `how` and `who` say, then resolves `thenDo`. -/
partial def applyRevealLibrary (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (targets : Array Target)
    (how : TriggeredAbility.TriggerLibraryHow)
    (thenDo : TriggeredAbility.TriggerResolution)
    (who : TriggeredAbility.PlayerSelector)
    (lastKnownToughness : Option Int := none) : Option Game :=
  match how, thenDo, who with
  | .top n, .put .randomCreature .asPrinted .none, .you => some <|
    let (g, cause) := g.allocDelayedCause (some controller) sourceId
    let ids := g.scryLookedIds controller n
    let g := ids.foldl (fun g id =>
      match g.findObject? id with
      | some o => g.logMsg s!"{(g.player controller).name} reveals {o.name}"
      | none => g) g
    let creatures := ids.filter (fun id => (g.findObject? id).any (·.printed.isCreature))
    if creatures.isEmpty then
      (g.logMsg "No creature card was revealed").putRestOnBottomRandom controller ids
        (cause := some cause)
    else if creatures.size > 1 then
      let g := g.change (.stashedCause (some cause))
      g.changes #[
        .pending (.resolveRandom (.chooseObject creatures)),
        .afterRandom (.revealRandomCreatureThenBottom controller ids)]
        |>.logMsg
          s!"{(g.player controller).name} puts a random creature from among them onto the battlefield"
    else
      g.resolveRandomCreatureReveal controller ids creatures[0]! (cause := some cause)
  | .untilCreature,
    .ifElse .revealedManaValueAtMostLands
      (.put .revealed .asPrinted .none)       (.returnToHand .revealed .none),
    .you => some <|
    Id.run do
      let (g0, cause) := g.allocDelayedCause (some controller) sourceId
      let mut g := g0
      let mut found : Option ObjectId := none
      let mut rest : Array ObjectId := #[]
      while found.isNone && !(g.player controller).library.isEmpty do
        let top := (g.player controller).library.back!
        let o := g.object! top
        g := g.logMsg s!"{(g.player controller).name} reveals {o.name}"
        if o.printed.isCreature then
          found := some top
        else
          let (g', newId) := g.move top .exile none (cause := some cause)
          g := g'
          rest := rest.push newId
      match found with
      | none =>
        return g.putRestOnBottomRandom controller rest (cause := some cause)
      | some cid =>
        let o := g.object! cid
        let lands := g.landsYouControl controller
        let (g', newId) :=
          if o.printed.manaValue <= lands then
            g.putOntoBattlefield cid controller (cause := some cause)
          else
            g.move cid (.hand controller) none (cause := some cause)
        g := g'
        g :=
          if o.printed.manaValue <= lands then
            g.logMsg s!"{o.name} enters the battlefield"
          else
            g.logMsg s!"{o.name} is put into {(g.player controller).name}'s hand"
        if o.printed.manaValue <= lands then
          g := g.afterPermanentEnters (g.object! newId)
        return g.putRestOnBottomRandom controller rest (cause := some cause)
  | .untilSaga, .put .revealed .asPrinted .none, .you => some <|
    Id.run do
      let (g0, cause) := g.allocDelayedCause (some controller) sourceId
      let mut g := g0
      let mut found : Option ObjectId := none
      let mut rest : Array ObjectId := #[]
      while found.isNone && !(g.player controller).library.isEmpty do
        let top := (g.player controller).library.back!
        let o := g.object! top
        g := g.logMsg s!"{(g.player controller).name} reveals {o.name}"
        if o.printed.saga.isSome then found := some top
        else
          let (g', newId) := g.move top .exile none (cause := some cause)
          g := g'
          rest := rest.push newId
      match found with
      | none =>
        return g.putRestOnBottomRandom controller rest (cause := some cause)
      | some sid =>
        let name := (g.object! sid).name
        let (g', newId) := g.putOntoBattlefield sid controller (cause := some cause)
        g := g'.logMsg s!"{name} enters the battlefield"
        g := g.afterPermanentEnters (g.object! newId)
        return g.putRestOnBottomRandom controller rest (cause := some cause)
  | .untilInstantOrSorcery, .exile .top .forLater .impulse, .damagedPlayer => some <|
    let victim := g.loggedLastCombatDamagePlayer.getD (g.opponent controller)
    let (g, cause) := g.allocDelayedCause (some controller) sourceId
    let (g, found, others) := g.exileUntilInstantOrSorcery victim (cause := some cause)
    g.changes #[
      .grimaImpulseReady true,
      .grimaImpulseVictim (some victim),
      .grimaImpulseFound found,
      .grimaImpulseOthers others]
  | .untilNonland,
    .may (.putCounters (.ofKind .plusOnePlusOne 1) .source)
      (.exile .top .forLater .anyManaThisTurn) .ifYouDont,
      .announced => some <|
    let pid :=
      match targets[0]? with
      | some (Target.player p) => some p
      | _ =>
        lastKnownToughness.orElse (fun _ => g.resolvingAbility.bind g.lastKnownToughnessOf?)
          |>.map (fun n => ⟨n.toNat⟩)
    match pid with
    | none => g.logMsg "Black Widow didn't deal combat damage to a player"
    | some pid =>
      let (g, cause) := g.allocDelayedCause (some controller) sourceId
      let (g, nonland?) := g.exileLibraryUntilNonland pid (cause := some cause)
      let onBf :=
        match sourceId.bind g.findObject? with
        | some o => o.isOnBattlefield
        | none => false
      if onBf then
        g.change (.pending (.fraChoice controller (.widowMayCounter sourceId nonland?)))
          |>.logMsg "You may put a +1/+1 counter on Black Widow"
      else
        g.grantWidowCast controller nonland? (cause := some cause)
  | .top n, .mayCast .looked .greatestAttackingPower .withoutPaying .none, .you =>
    some (g.offerLookSixCast controller n)
  | _, _, _ => none

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
            if g.controlledBy o opp then
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
  | .onePlusCreatureCards, .discard (.cards 1 (.target .opponent)) =>
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
the behavior of the constructor it replaced. `none` means the follow-up
is not a library find; the caller resolves that follow-up itself. -/
def applySearchLibrary (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (thenDo : TriggeredAbility.TriggerResolution) : Option Game :=
  match thenDo with
  | .put .forest .asPrinted .none => some (g.resolveSearchForest controller)
  | .put .forest how _ =>
    some (g.resolveSearchLibrary controller isForestCard (how == .tapped) "a Forest card")
  | .returnToHand .basicLand _ => some (g.resolveSearchBasicLandToHand controller)
  | .returnToHand .forest _ =>
    some (g.resolveLibrarySearchToHand controller isForestCard "a Forest card")
  | .returnToHand .dragon _ =>
    some (g.resolveLibrarySearchToHand controller (fun c => c.hasSubtype .dragon) "a Dragon card")
  | .put .basicLandOnTop .tapped _ =>
    some (g.beginLibrarySearch controller isBasicLandCard "a basic land card"
      (.battlefield true) (optional := true))
  | .put .basicLandOnTop _ _ =>
    some (g.beginLibrarySearch controller isBasicLandCard "a basic land card" .topAfterShuffle
      (optional := true))
  | .put .dragon .asPrinted .none =>
    some (g.beginLibrarySearch controller (fun c => c.hasSubtype .dragon) "a Dragon card"
      .battlefieldFromHandOrLibrary (alsoHand := true))
  | .put .dragon how _ =>
    some (g.beginLibrarySearch controller (fun c => c.hasSubtype .dragon) "a Dragon card"
      (if how == .tapped then .battlefield true else .battlefieldFromHandOrLibrary)
      (alsoHand := true))
  | .put .creatureCard how _ =>
    some (g.beginLibrarySearch controller (fun c => c.isCreature) "a creature card"
      (.battlefield (how == .tapped)))
  | .exile (.basicUpTo subtype max) .forLater .linked =>
    some (g.beginLibrarySearch controller
      (fun c => isBasicLandCard c && c.hasSubtype subtype)
      s!"a basic {subtype} card" (.exileLinked sourceId) (count := max))
  | _ => none

/-- Resolve `TriggerResolution.lose`. Each printed combination keeps
the behavior of the constructor it replaced. Any other permanent the
selector names loses that ability. A card or a hand loses nothing. -/
def applyLose (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (what : TriggeredAbility.AbilitySelector)
    (who : TriggeredAbility.ObjectSelector) : Game :=
  match what, who with
  | .indestructible, .target =>
    loseIndestructible .target
  | .indestructible, .source =>
    loseIndestructible .source
  | .indestructible, .enchanted =>
    loseIndestructible .enchanted
  | .indestructible, .whileSource | .indestructible, .target .whileSource =>
    loseIndestructible .targetWhileSource
  | .allAbilities, .ifPresent | .allAbilities, .target .ifPresent =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some tgt =>
        if !tgt.isOnBattlefield then g
        else
          match sourceId.bind g.findObject? with
          | some src =>
            if src.isOnBattlefield then
              g.createEffect (.losesAbilitiesWhileSource id src.id)
            else
              g.logMsg s!"The source has left. {g.name tgt} is tapped but keeps its abilities."
          | none =>
            g.logMsg s!"The source has left. {g.name tgt} is tapped but keeps its abilities."
      | none => g
    | _ => g
  | .indestructible, who =>
    let ctx : TriggerRead := { controller, sourceId, targets }
    match g.permanentsNamed ctx who with
    | some objs =>
      objs.foldl (fun g o => g.applyPermanentAction o .loseIndestructible) g
    | none => g
  | .allAbilities, who =>
    let ctx : TriggerRead := { controller, sourceId, targets }
    match g.permanentsNamed ctx who with
    | none => g
    | some objs =>
      match sourceId.bind g.findObject? with
      | some src =>
        if src.isOnBattlefield then
          objs.foldl (fun g o =>
            g.createEffect (.losesAbilitiesWhileSource o.id src.id)) g
        else
          objs.foldl (fun g o =>
            g.logMsg s!"The source has left. {g.name o} is tapped but keeps its abilities.") g
      | none =>
        objs.foldl (fun g o =>
          g.logMsg s!"The source has left. {g.name o} is tapped but keeps its abilities.") g
where
  loseIndestructible (affected : TriggeredAbility.TriggerAffected) : Game :=
    g.withAffected controller ab sourceId targets affected fun g o =>
      g.applyPermanentAction o .loseIndestructible

/-- Resolve `TriggerResolution.cant`. Each printed selector keeps
the behavior of the combination it replaced. Any other permanent the
selector names can't do that. A card or a hand is unchanged. -/
def applyCant (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (action : TriggeredAbility.ActionSelector) : Game :=
  match action with
  | .beBlocked who =>
    match asAffected who with
    | some affected =>
      g.withAffected controller ab sourceId targets affected fun g o =>
        g.applyPermanentAction o .cantBeBlocked
    | none =>
      let ctx : TriggerRead := { controller, sourceId, targets }
      match g.permanentsNamed ctx who with
      | some objs => objs.foldl (fun g o => g.applyPermanentAction o .cantBeBlocked) g
      | none => g
  | .beBlockedExceptByHaste who =>
    match asAffected who with
    | some affected =>
      g.withAffected controller ab sourceId targets affected fun g o =>
        g.createEffect (.cantBeBlockedExceptByHasteUntilEot o.id)
          |>.logMsg s!"{g.name o} can't be blocked this turn except by creatures with haste"
    | none =>
      let ctx : TriggerRead := { controller, sourceId, targets }
      match g.permanentsNamed ctx who with
      | some objs =>
        objs.foldl (fun g o =>
          g.createEffect (.cantBeBlockedExceptByHasteUntilEot o.id)
            |>.logMsg s!"{g.name o} can't be blocked this turn except by creatures with haste") g
      | none => g
  | .untapWhileYouControl .target =>
    g.withLegalKindPermanent controller .oppCreature targets (fun g o =>
      let sid := sourceId.getD ⟨0⟩
      g.createEffect (.cantUntapWhileSource o.id sid))
      sourceId (some "The target is no longer legal")
  | .untapWhileYouControl who =>
    let ctx : TriggerRead := { controller, sourceId, targets }
    match g.permanentsNamed ctx who with
    | none => g
    | some objs =>
      objs.foldl (fun g o =>
        if g.controlledBy o controller then g
        else
          let sid := sourceId.getD ⟨0⟩
          g.createEffect (.cantUntapWhileSource o.id sid)) g
where
  asAffected : TriggeredAbility.ObjectSelector → Option TriggeredAbility.TriggerAffected
    | .any | .target .any => some .target
    | .source => some .source
    | .enchanted => some .enchanted
    | .whileSource | .target .whileSource => some .targetWhileSource
    | _ => none

/-- Resolve `TriggerResolution.becomeArtifact`. Each printed recipient keeps
the behavior of the constructor it replaced. Any other permanent the
selector names becomes an artifact until end of turn. A card or a hand
does not. -/
def applyBecomeArtifact (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (who : TriggeredAbility.ObjectSelector) : Game :=
  match who with
  | .target => become .target
  | .source => become .source
  | .enchanted => become .enchanted
  | .whileSource | .target .whileSource => become .targetWhileSource
  | who =>
    let ctx : TriggerRead := { controller, sourceId, targets }
    match g.permanentsNamed ctx who with
    | some objs =>
      objs.foldl (fun g o =>
        let g := g.createEffect (.additionalArtifactUntilEot o.id)
        g.logMsg s!"{g.name o} becomes an artifact until end of turn") g
    | none => g
where
  become (affected : TriggeredAbility.TriggerAffected) : Game :=
    g.withAffected controller ab sourceId targets affected fun g o =>
      let g := g.createEffect (.additionalArtifactUntilEot o.id)
      g.logMsg s!"{g.name o} becomes an artifact until end of turn"

/-- Resolve `TriggerResolution.becomePrepared`. Each printed recipient keeps
the behavior of the constructor it replaced. A creature that is already
prepared, or has no prepare spell, does not. Any other permanent the
selector names becomes prepared. A card or a hand does not. -/
def applyBecomePrepared (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (who : TriggeredAbility.ObjectSelector) : Game :=
  match who with
  | .target => become .target
  | .source => become .source
  | .enchanted => become .enchanted
  | .whileSource | .target .whileSource => become .targetWhileSource
  | who =>
    let ctx : TriggerRead := { controller, sourceId, targets }
    match g.permanentsNamed ctx who with
    | some objs => objs.foldl (fun g o => g.applyPermanentAction o .becomePrepared) g
    | none => g
where
  become (affected : TriggeredAbility.TriggerAffected) : Game :=
    g.withAffected controller ab sourceId targets affected fun g o =>
      g.applyPermanentAction o .becomePrepared

/-- Resolve `TriggerResolution.putOnLibrary`. Each printed combination keeps
the behavior of the constructor it replaced. A card from hand on top
puts nothing. Any other permanent the selector names is put there.
A card or a hand that is not that choice puts nothing. -/
def applyPutOnLibrary (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (place : TriggeredAbility.TriggerLibraryPlace)
    (what : TriggeredAbility.ObjectSelector) : Game :=
  match what with
  | .target => put .target
  | .source => put .source
  | .enchanted => put .enchanted
  | .whileSource | .target .whileSource => put .targetWhileSource
  | .cardFromHand =>
    match place with
    | .bottom =>
      if (g.player controller).hand.isEmpty then g
      else
        g.change (.pending (.putOnBottom controller 1))
          |>.logMsg s!"{(g.player controller).name} puts a card from their hand on the bottom of their library"
    | .top => g
  | what =>
    let ctx : TriggerRead := { controller, sourceId, targets }
    match g.permanentsNamed ctx what with
    | some objs => objs.foldl (fun g o => g.applyPermanentAction o action) g
    | none => g
where
  action : PermanentAction :=
    match place with
    | .top => .putOnTopOfLibrary
    | .bottom => .putOnBottomOfLibrary
  put (who : TriggeredAbility.TriggerAffected) : Game :=
    g.withAffected controller ab sourceId targets who fun g o =>
      g.applyPermanentAction o action

/-- Resolve `TriggerResolution.setBasePT`. `power` and `toughness` are read
separately. Each printed combination keeps the behavior of the constructor
it replaced. Any other combination sets nothing. -/
def applySetBasePT (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (lastKnownPower lastKnownToughness : Option Int)
    (power toughness : TriggeredAbility.NumberSelector)
    (who : TriggeredAbility.ObjectSelector) : Game :=
  match power, toughness, who with
  | .fixed pw, .fixed tw, .target =>
    fixed .target pw tw
  | .fixed pw, .fixed tw, .source =>
    fixed .source pw tw
  | .fixed pw, .fixed tw, .enchanted =>
    fixed .enchanted pw tw
  | .fixed pw, .fixed tw, .whileSource | .fixed pw, .fixed tw, .target .whileSource =>
    fixed .targetWhileSource pw tw
  | .equalSourcePower, .equalSourceToughness, .target =>
    g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
      let (pw, tw) := g.sourcePTAtResolution sourceId lastKnownPower lastKnownToughness
      let g := g.createEffect (.setBasePTUntilEot o.id (pw, tw))
      g.logMsg
        s!"{g.name o}'s base power and toughness become {pw}/{tw} until end of turn")
      "No target was chosen"
  | power, toughness, who =>
    let ctx : TriggerRead :=
      { controller, sourceId, targets, lastKnownPower, lastKnownToughness }
    match g.triggerInt ctx power, g.triggerInt ctx toughness, g.permanentsNamed ctx who with
    | some pw, some tw, some objs =>
      objs.foldl (fun g o => g.applyPermanentAction o (.setBasePT pw tw)) g
    | _, _, _ => g
where
  fixed (affected : TriggeredAbility.TriggerAffected) (pw tw : Int) : Game :=
    g.withAffected controller ab sourceId targets affected fun g o =>
      g.applyPermanentAction o (.setBasePT pw tw)

/-- Create `n` tokens of `kind` for `controller` (`tapped := tapped`) and, when
`holds` is true, have them enter attacking (CR 508.4 / ruling 181). When there
is a single legal attack target, the tokens enter attacking that target
immediately; when multiple players, planeswalkers, or battles are legal attack
targets, `controller` chooses once per token before the tokens enter. -/
def createAndMarkTokensAttacking (g : Game) (controller : PlayerId)
    (kind : TokenKind) (n : Nat) (tapped holds : Bool)
    (sourceId : Option ObjectId := none) : Game :=
  let (g, c) := g.allocDelayedCause (some controller) sourceId
  let cause := some c
  if !holds then
    g.createKindTokens controller kind n (tapped := tapped) (attacking := false) (cause := cause)
  else if (g.player controller).lost then
    let g := g.change (.recentTokenIds #[])
    if n == 0 then g
    else g.logMsg "no token is created (CR 800.4b)"
  else
    let rawPrinted := tokenPrinted kind
    let (batches, applied, choice?) := g.replaceTokenCreation {
      controller := controller
      printed := rawPrinted
      count := n
      tapped := tapped
      cause := cause
    } (includeKindReplacements := false)
    match choice? with
    | some (chooser, choices) =>
      g.promptChooseReplacement chooser choices
        (.createAndMarkTokensAttacking controller kind n tapped holds sourceId)
    | none =>
      let g := g.consumeReplacementOrder applied
      let total := batches.foldl (fun acc b => acc + b.count) 0
      let cause' := (batches[0]?.bind (·.cause)).orElse (fun _ => cause)
      let options := g.legalEnteringAttackTargets controller
      let items := Array.replicate total (EnteringAttackItem.token controller kind tapped options)
      g.promptEnteringAttackItems items (cause := cause')

partial def applyTriggeredAbility (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target := #[])
    (dividedDamage : Array Nat := #[]) (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none)
    (sourceName : String := "This creature")
    (resolutionOverride : Option TriggeredAbility.TriggerResolution := none)
    (sequencedCardPower : Option Nat := none) : Game :=
  if resolutionOverride.isNone && !g.interveningStillHolds controller ab then
    g.logMsg "The intervening condition is no longer true. The ability doesn't resolve."
  else if resolutionOverride.isSome || ab.effect.sharedTrigger.isSome then
  match resolutionOverride.getD ab.resolution with
  | .pump power toughness who =>
    g.applyTriggerPump controller ab sourceId targets lastKnownPower lastKnownToughness
      power toughness who
  | .dealDamage amount who note =>
    g.applyTriggerDamage controller ab sourceId targets lastKnownPower sourceName
      amount who note
  | .scry amount =>
    let ctx : TriggerRead := {
      controller, sourceId, targets, lastKnownPower, lastKnownToughness,
      sequencedCardPower }
    match g.triggerCount ctx amount with
    | some n => g.beginScry controller n
    | none => g
  | .draw amount who =>
    g.applyTriggerDraw controller sourceId amount who targets lastKnownPower
      lastKnownToughness sequencedCardPower
  | .searchLibrary thenDo =>
    match g.applySearchLibrary controller sourceId thenDo with
    | some g => g
    | none =>
      g.applyTriggeredAbility controller ab sourceId targets dividedDamage
        lastKnownPower lastKnownToughness sourceName (some thenDo) sequencedCardPower
  | .discard what =>
    g.applyDiscard controller sourceId targets what
  | .sacrifice what note =>
    g.applySacrifice controller ab sourceId targets what note
  | .lose what who =>
    g.applyLose controller ab sourceId targets what who
  | .cant action =>
    g.applyCant controller ab sourceId targets action
  | .becomeArtifact who =>
    g.applyBecomeArtifact controller ab sourceId targets who
  | .becomePrepared who =>
    g.applyBecomePrepared controller ab sourceId targets who
  | .setBasePT power toughness who =>
    g.applySetBasePT controller ab sourceId targets lastKnownPower lastKnownToughness
      power toughness who
  | .putOnLibrary place what =>
    g.applyPutOnLibrary controller ab sourceId targets place what
  | .dividedDamage =>
    let (g, cause?) : Game × Option EventCause :=
      if targets.isEmpty then (g, none)
      else
        match g.currentResolvingContext? with
        | some (src, ctrl) =>
          let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some controller)) (src.orElse (fun _ => sourceId))
          (g, some c)
        | none => (g, none)
    Id.run do
      let mut g := g
      for i in [0:targets.size] do
        let t := targets[i]!
        let n := dividedDamage[i]?.getD 0
        if n > 0 then
          g := g.applyDamageToKindTarget controller .playerOrCreature #[t] n sourceId (cause := cause?)
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
      match steps with
      | [.createTokens kind (.fixed n) tapped .kind .you .none,
          .«if» cond .markRecentTokensAttacking] =>
        let (g, holds) :=
          g.triggerIfHolds controller ab sourceId targets lastKnownPower cond
        g.createAndMarkTokensAttacking controller kind n.toNat tapped holds sourceId
      | steps =>
      let rec runSteps (g : Game) (waiting : List TriggeredAbility.TriggerResolution)
          (paused dropped : Bool) :
          List TriggeredAbility.TriggerResolution →
          Game × List TriggeredAbility.TriggerResolution × Bool × Bool
        | [] => (g, waiting, paused, dropped)
        | cur@(step :: restSteps) =>
          if dropped then
            (g, [], true, true)
          else if paused then
            (g, waiting ++ cur, true, false)
          else if g.mayThenSkip > 0 then
            runSteps (g.change (.mayThenSkip (g.mayThenSkip - 1))) waiting false false restSteps
          else
            match cur with
            | .loseLife loseAmt who :: .gainLife gainAmt :: tail =>
              let (g, cause?) : Game × Option EventCause :=
                match g.currentResolvingContext? with
                | some (src, ctrl) =>
                  let (g, c) := g.allocDelayedCause
                    (ctrl.orElse (fun _ => some controller))
                    (src.orElse (fun _ => sourceId))
                  (g, some c)
                | none => (g, none)
              let g :=
                g.applyLoseLife controller ab sourceId targets loseAmt who
                  lastKnownPower (cause := cause?)
              let g :=
                g.applyGainLife controller ab sourceId targets gainAmt
                  cardPower lastKnownPower (cause := cause?)
              runSteps g waiting false false tail
            | _ =>
              let pendingBefore := g.pending
              let g :=
                g.applyTriggeredAbility controller ab sourceId targets dividedDamage
                  lastKnownPower lastKnownToughness sourceName (some step) cardPower
              if g.skipTriggerSequenceRest then
                (g.change (.skipTriggerSequenceRest false), [], true, true)
              else
                -- Pause only when this step opens a choice. A choice that was
                -- already pending belongs to an earlier ability.
                let opened := g.pending != pendingBefore && g.pending != .none
                runSteps g waiting opened false restSteps
      let (g, rest, _, _) := runSteps g [] false false steps
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
      let g := g.changes #[.triggerSequenceRest none, .mayThenSkip 0]
      let g :=
        if combined.isEmpty && usesNth then g.change (.nthResolveThisWay none) else g
      let g :=
        if combined.isEmpty && g.pending == .none then
          g.changes #[.mayThenDrop 0, .mayThenConditional none]
        else g
      if combined.isEmpty then g
      else
        g.change (.triggerSequenceRest (some {
            controller
            ability := ab
            sourceId
            targets
            dividedDamage
            lastKnownPower
            lastKnownToughness
            sourceName
            cardPower
            steps := combined }))
  | .gainLife amount =>
    g.applyGainLife controller ab sourceId targets amount sequencedCardPower
      lastKnownPower
  | .exile what how note =>
    g.applyExile controller ab sourceId targets what how note
  | .may (.put (.creatureFromHand subtype maxMv) _ _) (.draw (.fixed _) _) =>
    g.mayPutHeroOrDraw controller maxMv subtype
  | .put what how note | .may (.put what how note) _ =>
    g.applyPut controller ab sourceId targets what how note
  | .removeCounters what who =>
    g.applyRemoveCounters controller sourceId targets what who
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
  | .amass amount subtype attachSource who =>
    g.applyAmass controller sourceId lastKnownPower amount subtype attachSource who
      targets lastKnownToughness
  | .createTokens kind amount tapped token who note =>
    g.applyCreateTokens controller sourceId targets lastKnownPower
      kind amount tapped token who note (lastKnownToughness := lastKnownToughness)
  | .attach what host =>
    g.applyAttach controller ab sourceId targets what host
  | .addMana types amount =>
    g.applyAddMana controller sourceId types amount targets lastKnownPower
      lastKnownToughness
  | .becomePT power toughness =>
    let ctx : TriggerRead := {
      controller, sourceId, targets, lastKnownPower, lastKnownToughness,
      sequencedCardPower }
    match g.triggerInt ctx power, g.triggerInt ctx toughness with
    | some p, some t =>
      match sourceId.bind g.findObject? with
      | some o =>
        if o.isOnBattlefield then
          g.beginFraChoice controller (.mayBecomeBasePT o.id p t)
            s!"{(g.player controller).name} may have {g.name o}'s base power and toughness become {p}/{t}"
        else g
      | none => g
    | _, _ => g
  | .lookAtTopRevealTypes amount types =>
    let ctx : TriggerRead := {
      controller, sourceId, targets, lastKnownPower, lastKnownToughness,
      sequencedCardPower }
    match g.triggerCount ctx amount with
    | none => g
    | some n =>
      let ids := g.scryLookedIds controller n
      let g := g.logLookAtTop controller n
      let eligible := ids.filter (fun id =>
        match g.findObject? id with
        | some o =>
          types.any (fun t =>
            (t.toLower == "permanent" && o.printed.isPermanentCard) ||
              (CardType.ofOracle? t).any o.printed.hasType ||
              (CardSubtype.ofOracle? t).any o.printed.hasSubtype)
        | none => false)
      g.beginFraChoice controller (.mayRevealToHand ids eligible false)
        s!"{(g.player controller).name} may reveal a card from among them and put it into their hand"
  | .gainControl how =>
    match how with
    | .untilEndOfTurn =>
      g.withLegalTriggerPermanent controller ab sourceId targets (fun g o =>
        let g := g.giveControlUntilEot o controller
        let g := g.applyPermanentAction (g.object! o.id) .untap
        g.createEffect (.keywordsUntilEot o.id Keyword.haste))
    | .whileSourceRemains =>
      g.gainControlWhileSource controller sourceId targets
    | .duringNextTurn =>
      g.withLegalKindPlayer controller .opponent targets (fun g pid =>
        g.setPlayerControl controller pid)
        sourceId (some "The target is no longer legal")
  | .honeEachEquipment =>
    let eqs :=
      g.battlefield.filter (fun o => g.controlledBy o controller && g.isEquipment o)
    g.withBatch none fun g =>
      eqs.foldl (init := g) fun acc eq =>
        let n := acc.countersYouPut eq 1 (putter := some controller)
        acc.recordPutCounters eq.id .hone n (byPlayer := some controller)
          |>.logMsg s!"{acc.name eq} received a hone counter"
  | .cascade =>
    let maxMv :=
      match sourceId with
      | some sid =>
        match g.findObject? sid with
        | some src => (g.copiableValues src).manaCost.manaValue
        | none => 0
      | none => 0
    g.resolveCascade controller maxMv
  | .noteResolveThisTurn limit =>
    let n := g.loggedResolutions controller + 1
    let g := g.record (GameEvent.resolved g.turnNumber controller n)
    let g := g.change (.nthResolveThisWay (some n))
    if n > limit then
      let name :=
        match sourceId.bind g.findObject? with
        | some o => if o.isOnBattlefield then g.name o else o.name
        | none => sourceName
      g.logMsg s!"{name}'s ability has no effect (resolved {n} times this turn)"
    else g
  | .«if» (.atLeast (.count (.othersOfSubtype .hero)) (.fixed 1)) (.dealDamage (.fixed 1) (.player (.target .opponent))) =>
    let (g, holds) :=
      g.triggerIfHolds controller ab sourceId targets lastKnownPower (.atLeast (.count (.othersOfSubtype .hero)) (.fixed 1))
    if holds then
      g.applyTriggeredAbility controller ab sourceId targets dividedDamage
        lastKnownPower lastKnownToughness sourceName
        (some (.dealDamage (.fixed 1) (.player (.target .opponent)))) sequencedCardPower
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
        g.changes #[
          .pending (.chooseTriggerOr controller),
          .triggerOr (some {
            controller
            ability := ab
            sourceId
            targets
            dividedDamage
            lastKnownPower
            lastKnownToughness
            sourceName
            cardPower := sequencedCardPower
            alternatives := rs.toArray })]
          |>.logMsg (triggerOrLog (g.player controller).name rs)
  | .may (.sacrifice .another _) _ =>
    g.applySacrifice controller ab sourceId targets .another .none
  | .additionalCombatPhase =>
    g.record (GameEvent.extraPhaseAdded g.turnNumber .combat
      (cause := g.resolvingOneShotCause controller sourceId))
      |>.logMsg "Attacking creatures untap. After this phase, there is an additional combat phase"
  | .chooseModes modes how =>
    match how with
    | .plusOneOrRemoveCounter =>
      g.offerHydeChoice controller sourceId
    | .alreadyChosen =>
      let chosen :=
        match sourceId.bind g.findObject? with
        | some o => g.modesChosenEver o.id
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
        if g.hasSubtype o .bear then g
        else
          let g := g.createEffect (.additionalSubtype o.id .bear)
          g.logMsg s!"{g.name o} becomes a Bear in addition to its other types"
      | none => g
    | _ => g
  | .mayCast origin maxMv cost note =>
    g.applyMayCast controller lastKnownPower origin maxMv cost note
  | .mill amount who note =>
    g.applyMill controller ab sourceId targets lastKnownPower lastKnownToughness
      amount who note
  | .grant what who =>
    g.applyGrant controller ab sourceId targets what who
  | .revealLibrary how thenDo who =>
    match g.applyRevealLibrary controller sourceId targets how thenDo who
        (lastKnownToughness := lastKnownToughness) with
    | some g => g
    | none =>
      let (g, cause) := g.allocDelayedCause (some controller) sourceId
      let (g, rests) := g.noteRevealedLibraries controller targets sourceId how who
        (lastKnownToughness := lastKnownToughness) (cause := some cause)
      let g := g.applyTriggeredAbility controller ab sourceId targets dividedDamage
        lastKnownPower lastKnownToughness sourceName (some thenDo) sequencedCardPower
      rests.foldl (fun g (pid, rest) => g.putRestOnBottomRandom pid rest (cause := some cause)) g
  | .fight who how =>
    g.applyFight controller sourceId targets who how
  | .copySelfNonlegendary =>
    match sourceId.bind g.findObject? with
    | none => g
    | some src =>
      if src.printed.isToken then g
      else
        let cv := if src.isOnBattlefield then g.copiableValues src else src.printed
        let srcName := if src.isOnBattlefield then g.name src else src.name
        let face := { cv with
          isToken := true
          supertypes := cv.supertypes.filter (· != .legendary) }
        g.withBatch none fun g =>
          let (g, _) := g.createToken controller face
          let (g, _) := g.createToken controller face
          g.logMsg s!"two nonlegendary tokens that are copies of {srcName} are created"
  | .loseLife amount who =>
    g.applyLoseLife controller ab sourceId targets amount who lastKnownPower
  | .may (.draw _ .opponentHasYou) _ =>
    g.applyTriggerDraw controller sourceId (.fixed 1) .opponentHasYou
  | .may (.sequence [.draw .equalToManaSpent _, .«if» .manaSpent (.discard (.cards n))]) _ =>
    -- X is the mana spent to cast the triggering spell.
    let spent :=
      match g.resolvingAbilityObject?.bind (·.fraCauseId) with
      | some id => GameEvent.manaSpentOn g.events id
      | none => 0
    if spent == 0 then g.logMsg "No mana was spent to cast that spell"
    else
      let disc := if n == 2 then "two" else toString n
      g.beginFraChoice controller (.mayDrawThenDiscard spent n)
        s!"{(g.player controller).name} may draw {spent} cards, then discard {disc}"
  | .winTheGame =>
    -- Ruling 835: you win while the ability resolves, before the
    -- state-based action for drawing from an empty library.
    g.record (GameEvent.gameEnded g.turnNumber (.won controller)
      (cause := g.resolvingOneShotCause controller sourceId))
      |>.logMsg s!"{(g.player controller).name} wins the game"
  | .shuffleSource =>
    g.shuffleSourceIntoLibrary sourceId
  | .ringTempts =>
    g.temptWithTheRing controller
  | .spellsCostLess which amount =>
    let ctx : TriggerRead := {
      controller, sourceId, targets, lastKnownPower, lastKnownToughness,
      sequencedCardPower }
    match g.triggerCount ctx amount with
    | none => g
    | some n =>
      match which with
      | .cardType ty => g.grantTypeCostLessThisTurn controller ty n
      | .supertype s => g.grantSupertypeCostLessThisTurn controller s n
  | .investigate =>
    let (g, _) := g.createToken controller clueToken
    g.logMsg s!"{(g.player controller).name} investigates"
  | .connive who =>
    match who with
    | .source => g.applyConnive controller sourceId
    | .target =>
      match targets[0]? with
      | some (Target.permanent id) => g.applyConnive controller (some id)
      | _ => g.applyConnive controller sourceId
    | .enteringVillain =>
      match sourceId.bind g.findObject? with
      | none =>
        g.logMsg "Baron Strucker is no longer on the battlefield. The ability has no effect."
      | some src =>
        if g.optionalOnceUsedThisTurn src.id then
          g.logMsg
            "The optional connive was already chosen this turn. This instance has no effect."
        else
          match g.villainConniveTarget? controller src.id targets lastKnownPower with
          | none => g.logMsg "The Villain does not connive"
          | some vid => g.beginMayHaveVillainConnive controller src.id vid
    | who =>
      let ctx : TriggerRead := { controller, sourceId, targets, lastKnownPower }
      match g.permanentsNamed ctx who with
      | some objs => objs.foldl (fun g o => g.applyConnive controller (some o.id)) g
      | none => g
  | .grantPlayNotedUntilNextTurn =>
    match g.playExiledThisWay with
    | none => g
    | some newId =>
      let g := g.change (.playExiledThisWay none)
      match g.findObject? newId with
      | some o =>
        let name := o.name
        let g := g.createEffect
          (.playPermission o.id { player := controller } (turnEnds := 2))
          (cause := g.lastMoveCauseOf? o.id)
        g.logMsg
          s!"{(g.player controller).name} exiles {name} and may play it until the end of their next turn"
      | none => g
  | .revealFromHand count thenDo =>
    match count, thenDo with
    | .hand, .exile .target .untilSourceLeaves .none
    | .onePlusCreatureCards, .discard (.cards 1 (.target .opponent)) =>
      g.applyRevealFromHand controller sourceId targets count thenDo
    | _, _ =>
      let pids :=
        let chosen :=
          targets.filterMap fun
            | Target.player pid => some pid
            | _ => none
        if chosen.isEmpty then (g.livingOpponents controller).map (·.id) else chosen
      let g :=
        pids.foldl (fun g pid =>
          match count with
          | .hand => g.revealHand pid
          | .onePlusCreatureCards =>
            let n :=
              1 + ((g.player controller).graveyard.filter (fun id =>
                (g.findObject? id).any (·.printed.isCreature))).size
            let hand := (g.player pid).hand.filterMap (fun id => g.findObject? id)
            let shown := if hand.size ≤ n then hand else hand.take n
            (g.revealHand pid).logMsg
              s!"{(g.player pid).name} reveals {shown.size} card(s) (all, if fewer than {n})") g
      g.applyTriggeredAbility controller ab sourceId targets dividedDamage
        lastKnownPower lastKnownToughness sourceName (some thenDo) sequencedCardPower
  | .surveil amount =>
    let ctx : TriggerRead := {
      controller, sourceId, targets, lastKnownPower, lastKnownToughness,
      sequencedCardPower }
    match g.triggerCount ctx amount with
    | none => g
    | some n =>
      let armed := g.armSurveilReturn
      let life := g.loggedLifeGained controller
      let g := g.change (.armSurveilReturn false)
      let g := g.beginSurveil controller n
      if armed then
        match g.pending with
        | .surveil .. => g.change (.surveilReturnMvAtMost (some life))
        | _ => g
      else g
  | .empowerJace amount =>
    let ctx : TriggerRead := {
      controller, sourceId, targets, lastKnownPower, lastKnownToughness,
      sequencedCardPower }
    match g.triggerCount ctx amount with
    | some n => g.empowerJace controller n
    | none => g
  | .prepareSource .ifNotPrepared =>
    match sourceId.bind g.findObject? with
    | some o =>
      if !o.isOnBattlefield then g.logMsg s!"{o.name} is no longer on the battlefield"
      else if o.status.prepared then g.logMsg s!"{g.name o} is already prepared"
      else g.becomePrepared o
    | none => g.logMsg "The source is no longer on the battlefield"
  | .armSurveilReturnLifeGained =>
    -- Ruling 750: the following surveil reads life gained as this ability resolves.
    g.change (.armSurveilReturn true)
  | .prepareSource .ifThreeCreaturesDied =>
    if g.loggedCreaturesToGraveyard.size < 3 then
      g.logMsg "Fewer than three creatures died this turn"
    else
      match sourceId.bind g.findObject? with
      | some o =>
        if o.isOnBattlefield then g.becomePrepared o
        else g.logMsg s!"{o.name} is no longer on the battlefield"
      | none => g.logMsg "The source is no longer on the battlefield"
  | .becomeCopy of =>
    match of with
    | .noted | .cause none | .artifactEnchantmentOrLand | .creatureOrGraveyardCard =>
      g.applyBecomeCopy controller sourceId targets of
    | of =>
      let ctx : TriggerRead := { controller, sourceId, targets }
      match sourceId.bind g.findObject? with
      | some src =>
        if !src.isOnBattlefield then g
        else
          match g.permanentsNamed ctx of with
          | some objs =>
            match objs.find? (·.id != src.id) with
            | some tgt => g.becomeCopyOf src tgt
            | none => g
          | none => g
      | none => g
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
  | .may (.loseLife (.fixed 2) .you)
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
    if g.loggedSheHulkDealtDamage then
      g.logMsg "The Sensational She-Hulk already dealt damage this turn. The ability has no effect."
    else
      let legal := g.legalTargetsForKind controller .playerOrCreature sourceId
      match targets.find? (legal.contains ·) with
      | none => g.logMsg "The target is no longer legal"
      | some t =>
        let amt := lastKnownPower.getD 0
        g.change (.pending (.fraChoice controller (.sheHulkMayDamage amt t sourceId)))
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
        let follow := Resolution.queueReflexive followup
        let g := g.changes #[.mayThenDrop 1, .mayThenConditional (some follow)]
        g.applyTriggeredAbility controller ab sourceId targets dividedDamage
          lastKnownPower lastKnownToughness sourceName
          (some (.sequence [.pay (.mana symbols), follow])) sequencedCardPower
    | _ =>
      let follow := Resolution.queueReflexive followup
      let g := g.changes #[.mayThenDrop 1, .mayThenConditional (some follow)]
      g.applyTriggeredAbility controller ab sourceId targets dividedDamage
        lastKnownPower lastKnownToughness sourceName
        (some (.sequence [.pay (.mana symbols), follow])) sequencedCardPower
  | .may (.createTokens .wall04defender (.fixed 1) false) (.sequence []) .ifYouDo =>
    g.offerMayCreateWall controller
  | .may optional conditional .ifYouDo =>
    let cond := TriggeredAbility.TriggerResolution.flatten conditional
    let g := g.changes #[.mayThenDrop cond.length, .mayThenConditional (some conditional)]
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
            let g := g.change (.pending (.mayPayGeneric controller n))
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
      | some (.becomeCopy (.cause none)), [.generic 2] =>
        g.offerCopyCause controller sourceId targets
      | _, _ =>
        match symbols.toList with
        | [.generic n] =>
          let plusOne :=
            match g.mayThenConditional with
            | some (.sequence [.putCounters (.ofKind .plusOnePlusOne 1) .source, .draw (.fixed 1)]) => true
            | _ => false
          let g := g.change (.pending (.mayPayGeneric controller n))
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
    | .sacrifice (.fixed 1) .another =>
      let reflexive :=
        match g.mayThenConditional with
        | some (.queueReflexive _) => true
        | _ => false
      match sourceId with
      | some sid =>
        if reflexive then
          let pick := CostPick.sacrificeAnotherCreature
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
    | .sacrifice (.fixed 1) .anotherCreatureOrArtifact =>
      match sourceId with
      | none => (g.logMsg "Nothing to sacrifice").failMayThen
      | some sid =>
        let any := (g.permanentsOf controller).any (fun o =>
          o.id != sid && (g.isCreature o || g.isArtifact o))
        if !any then (g.logMsg "Nothing to sacrifice").failMayThen
        else
          g.beginFraChoice controller (.maySacrificeAnotherForDrawTreasure sid)
            s!"{(g.player controller).name} may sacrifice another creature or artifact"
    | .sacrifice (.fixed 1) .artifact =>
      g.offerMayPayPick controller sourceId .sacrificeArtifact
        s!"{(g.player controller).name} may sacrifice an artifact"
    | .sacrifice n what =>
      -- Printed sacrifices above keep their choices and logs. Every other
      -- count offers that many permanents `what` names. A count that is not
      -- a positive number, or fewer permanents than that count, pays nothing.
      let ctx : TriggerRead := {
        controller, sourceId, targets, lastKnownPower, lastKnownToughness,
        sequencedCardPower }
      match g.triggerCount ctx n with
      | some k =>
        let ids := (g.sacrificeCostCandidates ctx what).map (·.id)
        if k == 0 || ids.size < k then
          (g.logMsg "Nothing to sacrifice").failMayThen
        else
          let noun := if k == 1 then "a permanent" else s!"{k} permanents"
          g.beginFraChoice controller (.maySacrificeThese k ids)
            s!"{(g.player controller).name} may sacrifice {noun}"
      | none =>
        (g.logMsg "Nothing to sacrifice").failMayThen
    | .discard (.fixed 1) .card =>
      g.offerMayPayPick controller sourceId .discardACard
        s!"{(g.player controller).name} may discard a card"
    | .discard (.fixed 1) .nonland =>
      g.offerMayPayPick controller sourceId .discardNonland
        s!"{(g.player controller).name} may discard a nonland card"
    | .discard n what =>
      -- Printed discards above keep their choices and logs. Every other
      -- count offers that many cards `what` names. A count that is not a
      -- positive number, or fewer cards than that count, pays nothing.
      let ctx : TriggerRead := {
        controller, sourceId, targets, lastKnownPower, lastKnownToughness,
        sequencedCardPower }
      match g.triggerCount ctx n with
      | some k =>
        let ids := (g.discardCostCandidates controller what).map (·.id)
        if k == 0 || ids.size < k then
          (g.logMsg "Nothing to discard").failMayThen
        else
          let noun := if k == 1 then "a card" else s!"{k} cards"
          g.beginFraChoice controller (.mayDiscardThese k ids)
            s!"{(g.player controller).name} may discard {noun}"
      | none =>
        (g.logMsg "Nothing to discard").failMayThen
    | .or costs =>
      -- Sacrificing an artifact or discarding is one choice of an object.
      -- Either order is that payment.
      if costs == [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .card] ||
          costs == [.discard (.fixed 1) .card, .sacrifice (.fixed 1) .artifact] then
        g.change (.pending (.maySacArtifactOrDiscard controller 1))
          |>.logMsg s!"{(g.player controller).name} may sacrifice an artifact or discard a card. If they do, they draw a card"
      else if costs == [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .nonland] ||
          costs == [.discard (.fixed 1) .nonland, .sacrifice (.fixed 1) .artifact] then
        match sourceId with
        | some sid =>
          if (g.costPickCandidates controller sid .sacrificeArtifactOrDiscardNonland).isEmpty then
            g.failMayThen
          else
            g.beginFraChoice controller
              (.mayPayPickThen .sacrificeArtifactOrDiscardNonland (.reflexiveDamageAnyTarget 2) sid)
              s!"{(g.player controller).name} may sacrifice an artifact or discard a nonland card"
        | none => g.failMayThen
      else
        match costs.filter (fun c =>
            g.costPayable controller sourceId c targets lastKnownPower lastKnownToughness) with
        | [] => g.failMayThen
        | [c] =>
          g.applyTriggeredAbility controller ab sourceId targets dividedDamage
            lastKnownPower lastKnownToughness sourceName
            (some (.pay c)) sequencedCardPower
        | cs =>
          g.applyTriggeredAbility controller ab sourceId targets dividedDamage
            lastKnownPower lastKnownToughness sourceName
            (some (.or (cs.map fun c => .pay c))) sequencedCardPower
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
        { targeting := .of .playerOrCreature, resolution := .damageAny n
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
        resolution := .sarumanExileCopyMayCast
        phrase := "Exile that card. Copy it. You may cast the copy without paying its mana cost" }
    | .divided amount =>
      g.putReflexiveTrigger controller sourceId {
        targeting := .of .playerOrCreature
        dividedDamage := some (amount, 2)
        resolution := .mshReflexive 10 0
        phrase := s!"It deals {amount} damage divided as you choose among one or two targets" }
    | .attackPump =>
      g.attackPumpPerPlains controller
    | .none => g.queueFollowupReflexive controller sourceId followup
  | .may action follow .ifYouDont =>
    let ctx : TriggerSequenceRest := {
      controller
      ability := ab
      sourceId
      targets
      dividedDamage
      lastKnownPower
      lastKnownToughness
      sourceName
      cardPower := sequencedCardPower
      steps := [] }
    g.changes #[
      .pending (.mayResolve controller),
      .mayOnAccept (some action),
      .mayOnDecline (some follow),
      .mayContext (some ctx)]
      |>.logMsg s!"{(g.player controller).name} may {TriggeredAbility.resolutionPhrase { resolution := action }}"
  | _ => g
  else
  match ab.effect.resolution with
  | .sequence rs =>
    match rs.flatMap Resolution.flatten with
    | [.onPermanent .tap, .scry (.fixed scryN), .draw (.fixed drawN)] =>
      g.resolveTapScryDraw controller ab.effect targets scryN.toNat drawN.toNat sourceId
        (fizzle := fun g => g.logIllegalSequenceTargets targets)
    | steps =>
      if g.sequenceAllTargetsIllegal controller ab.effect targets sourceId then
        g.logIllegalSequenceTargets targets
      else
        match steps with
        | [.shuffleSource, .draw (.fixed n)] =>
          g.shuffleSourceIntoLibrary sourceId (.draw controller n.toNat)
        | [.createTokens kind (.fixed n) tapped .kind .you .none,
            .«if» cond .markRecentTokensAttacking] =>
          let (g, holds) :=
            g.triggerIfHolds controller ab sourceId targets lastKnownPower cond
          g.createAndMarkTokensAttacking controller kind n.toNat tapped holds sourceId
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
  | .draw (.fixed n) .you => g.draw controller n.toNat
  | .scry (.fixed n) => g.beginScry controller n.toNat
  | .onPermanent a =>
    g.applyOnPermanent controller ab.targetKind targets a sourceId
      (some "The target is no longer legal")
  | .onSource a => g.applyOnTriggerSource sourceId a
  | .gainLife (.fixed n) => g.gainLife controller n.toNat
  | .recruit _ => g.beginRecruit controller
  | .amass (.fixed n) .goblin false .you => g.amassGoblins controller n.toNat
  | .createTokens kind (.fixed n) tapped .kind .you .none =>
    g.createKindTokens controller kind n.toNat (tapped := tapped)
  | .markRecentTokensAttacking =>
    let cause := g.resolvingOneShotCause controller sourceId
    let options := g.legalEnteringAttackTargets controller
    let tgt := options[0]?.getD (.player g.defendingPlayer)
    g.recentTokenIds.foldl (fun g id =>
      match g.findObject? id with
      | some o => g.record (GameEvent.becameAttacking g.turnNumber (g.snapshot o) tgt (cause := cause))
      | none => g) g
  | .addMana types (.fixed 1) =>
    g.addManaLogged controller types
  | .discard (.cards n) => g.beginDiscardCards #[controller] n
  | r =>
    match Resolution.toSpell r with
    | some _ =>
      g.applyUnified controller ab.effect targets (sourceId := sourceId)
    | none =>
      g.applyUnifiedAbility controller { ab.effect with resolution := r }
        targets sourceId lastKnownPower

/-- Finish trigger-sequence steps that waited on a pending choice.
Those steps are still part of the resolution that opened the choice. -/
def resumeTriggerSequence (g : Game) : Game :=
  match g.triggerSequenceRest with
  | none => g
  | some c =>
    let g := g.change (.triggerSequenceRest none)
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
    g.record (GameEvent.triggerModeChosen g.turnNumber src.id mode)
  | .vision, some src =>
    if src.isOnBattlefield then
      g.record (GameEvent.triggerModeChosen g.turnNumber src.id mode)
    else g
  | .oneUnused, some src =>
    g.record (GameEvent.triggerModeChosen g.turnNumber src.id mode (lifetime := true))

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
    let chosen := g.modesChosenThisTurn src.id
    if chosen.contains mode || chosen.size >= 3 then
      g.logMsg "The Vision's ability is removed from the stack with no effect"
    else if !src.isOnBattlefield then
      match rest.modes[mode]? with
      | some (.draw (.fixed _)) => g.draw controller 1
      | _ => g.logMsg "The Vision is no longer in play"
    else
      let g := g.record (GameEvent.triggerModeChosen g.turnNumber src.id mode)
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
    let g := g.change (.chooseModesRest none)
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
      let g := g.changes #[.pending .none, .triggerOr none]
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
  if attackerIds.isEmpty then g
  else
    let decls : Array (EventObject × AttackTarget) :=
      attackerIds.map fun id =>
        let o := g.object! id
        let tgt := o.status.attackingTarget.getD (.player (g.defendingPlayerOf o))
        ({ (g.snapshot o) with attacking := true, attackingTarget := some tgt }, tgt)
    g.record (GameEvent.attackersDeclared g.turnNumber p decls)

end Game
end Mtg.Engine
