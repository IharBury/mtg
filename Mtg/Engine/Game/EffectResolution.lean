import Mtg.Engine.Game.FraResolve

/-!
# Unified effect resolution (CR 608)

`applyUnified` and `applyUnifiedAbility`: the interpreters for the
unified `Effect` vocabulary shared by spells, activated abilities, and
triggered abilities.
-/

namespace Mtg.Engine
namespace Game

/-- Move the source into its owner's library and shuffle (CR 701.24).
A following draw is rewritten to that owner so a stolen source still
draws for the printed owner. -/
def shuffleSourceIntoLibrary (g : Game) (sourceId : Option ObjectId)
    (after : AfterRandom := .none) : Game :=
  match sourceId.bind g.findObject? with
  | none => g.logMsg "The source is no longer in play"
  | some src =>
    let owner := src.owner
    let after :=
      match after with
      | .draw _ n => .draw owner n
      | other => other
    let (g, _) := g.move src.id (.library owner) none
      (verb := some .shuffleIntoLibrary) (libraryPosition := some .shuffledIn)
    g.requestShuffle owner after |>.continueIfShuffled

/-- Damage beyond lethal damage dealt to `o` by `dealt` damage (CR 120.4a):
beyond its toughness minus damage already marked for a creature, beyond its
loyalty for a planeswalker (ruling 790), and beyond the greater of the two
when it is both. -/
def excessDamage (g : Game) (o : GameObject) (dealt : Nat) : Nat :=
  dealt - g.lethalDamageThreshold o

/-- `pid` sacrifices a creature or planeswalker with the greatest mana value
among creatures and planeswalkers they control, as one group (rulings
771–773). With a tie, the most recent of them is sacrificed. -/
def sacrificeGreatestManaValue (g : Game) (pid : PlayerId) : Game :=
  let candidates := (g.permanentsOf pid).filter (fun o =>
    g.isCreature o || g.isPlaneswalker o)
  let best := candidates.foldl (fun best o =>
    match best with
    | none => some o
    | some b =>
      let mo := g.objectManaValue o
      let mb := g.objectManaValue b
      if mo > mb || (mo == mb && o.timestamp ≥ b.timestamp) then some o else best) none
  match best with
  | none => g.logMsg s!"{(g.player pid).name} has no creature or planeswalker to sacrifice"
  | some o => g.sacrificeToGraveyard o s!"{(g.player pid).name} sacrifices {g.name o}"

/-- Step through `snapshots`, creating a token copy of each source under `p`
via `createToken` and pausing on `Pending.chooseReplacement`
(`PendingReplacement.copyNontokenCreatures`) if CR 616.1 choice is required. -/
partial def copyNontokenCreaturesStep (g : Game) (p : PlayerId)
    (snapshots : Array CardDef) (cause : Option EventCause := none) : Game :=
  match snapshots[0]? with
  | none => g
  | some printed =>
    let rem := snapshots.extract 1 snapshots.size
    let (g, _) := g.createToken p printed (recordRecent := true) (cause := cause)
    if let .chooseReplacement .. := g.pending then
      if rem.isEmpty then g
      else g.chainPendingReplacement (.copyNontokenCreatures p rem cause)
    else
      g.copyNontokenCreaturesStep p rem cause

/-- Resolutions added for Reality Fracture, shared by spells and activated
abilities. `none` for every other resolution. -/
def applyFraResolution? (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (sourceId : Option ObjectId)
    (lastKnownPower : Option Int := none) : Option Game :=
  match effect.resolution with
  | .empowerJace (.fixed n) => some (g.empowerJace controller n.toNat)
  | .surveil (.fixed n) => some (g.beginSurveil controller n.toNat)
  | .millSelf n => some (g.mill controller n)
  | .mayDiscardDraw n =>
    let pl := g.player controller
    if pl.hand.isEmpty then some (g.logMsg s!"{pl.name} has no card to discard")
    else
      some ((g.change (.pending (.mayDiscardDraw controller n))).logMsg
        s!"{pl.name} may discard a card. If they do, they draw {n}")
  | .createTokensLifeGained kind =>
    -- Ruling 755: counts life gained, ignoring life lost this turn.
    some (g.createKindTokens controller kind (g.loggedLifeGained controller))
  | .oppSacrificesGreatestMv =>
    some (g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.sacrificeGreatestManaValue pid) sourceId)
  | .createTigerGod => some (g.createNamedToken controller tigerGodToken)
  | .extraTurn =>
    let (g, cause) := g.allocDelayedCause (some controller) sourceId
    some (g.record (GameEvent.extraTurnAdded g.turnNumber controller (cause := cause))
      |>.logMsg s!"{(g.player controller).name} takes an extra turn after this one. During that turn, power-up abilities can't be activated.")
  | .drawEqualToBurdenCounters =>
    some (g.withSourceOnBattlefield sourceId fun g o => g.draw controller o.status.burden)
  | .creaturesWithoutFlyingCantBlock =>
    some (g.createEffect .creaturesWithoutFlyingCantBlockUntilEot
      |>.logMsg "Creatures without flying can't block this turn")
  | .targetPlayerLoseLife n =>
    some (g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.loseLife pid n))
  | .controllerOfTargetLosesLife n =>
    some (match targets[0]? with
      | some (Target.permanent id) =>
        let pid? :=
          match g.findObject? id with
          | some o =>
            if o.isOnBattlefield then g.controllerOf o
            else (g.lastKnownBefore? id).bind (fun eo => eo.controller.orElse (fun _ => some eo.owner))
          | none =>
            (g.lastKnownBefore? id).bind (fun eo => eo.controller.orElse (fun _ => some eo.owner))
        match pid? with
        | some pid => g.loseLife pid n
        | none => g
      | _ => g)
  | .returnTargetSpell =>
    some (match targets[0]? with
      | some (Target.card id) => g.returnStackSpell id
      | _ => g.logMsg "The target is no longer legal")
  | .chooseOddOrEvenDestroy =>
    some (g.change (.pending (.fraChoice controller (.oddOrEvenDestroy sourceId)))
      |>.logMsg s!"{(g.player controller).name} chooses odd or even")
  | .eachCreatureYouControlBecomesPrepared =>
    some (g.withBatch none fun g =>
      (g.permanentsOf controller).foldl (fun g o =>
        if g.isCreature o && (g.baseCard o).prepareFace.isSome then g.becomePrepared (g.object! o.id)
        else g) g)
  | .damageThenEmpowerExcess n =>
    some (g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let startIdx := g.events.size
      let lethal := g.lethalDamageThreshold o
      let g := g.dealDamageToPermanent o n
        (source := (sourceId.bind g.damageSourceById?).map g.snapshotDamageSource)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep 21 controller lethal none (some o.id) (modes := #[startIdx]))
      else
        let dealt := g.damageDealtToPermanentSince o.id startIdx
        let excess := dealt - lethal
        if excess > 0 then g.empowerJace controller excess
        else g) sourceId (some "The target is no longer legal"))
  | .exileTopMayCastElseDamageOpponents n =>
    let sid := sourceId.orElse (fun _ => g.resolvingSpell)
    let src? := sid.bind g.damageSourceById?
    match (g.player controller).library.back? with
    | none =>
      some (g.dealDamageToEachOpponent controller n (source := src?))
    | some top =>
      let (g, id) := g.move top .exile none
      let card := g.object! id
      let g := g.logMsg s!"{(g.player controller).name} exiles {card.name}"
      if g.isLand card then
        -- Ruling 855: a land can't be cast, so the damage is dealt.
        some (g.dealDamageToEachOpponent controller n (source := src?))
      else
        some ((g.change (.pending (.mayCastExiledElseDamage controller id n sid))).logMsg
          s!"{(g.player controller).name} may cast {card.name}")
  | .emblemCastSpellDamage n =>
    -- Ruling 858: the emblem is colorless.
    let emblem : CardDef := {
      name := "Chandra Emblem", types := #[]
      triggeredAbilities := #[.triggered .youCastSpell
        (Effect.ofTrigger (.onPermanent .playerOrCreature (.dealDamage n)))] }
    let (g, _) := g.allocObject emblem controller .command (some controller)
    some (g.logMsg s!"{(g.player controller).name} gets an emblem")
  | .firstDealsStatDamageToSecond useLoyalty =>
    -- Ruling 791: the power or loyalty is checked as the spell resolves; if
    -- that permanent is gone, no damage is dealt.
    let kinds := effect.targetKind.spec.slots
    let legalAt (i : Nat) (t : Target) : Bool :=
      match kinds[i]? with
      | some k => (g.legalTargetsForAtomicKind controller k none).contains t
      | none => false
    match targets[0]?, targets[1]? with
    | some (Target.permanent srcId), some (Target.permanent dstId) =>
      if !legalAt 0 (Target.permanent srcId) then
        some (g.logMsg "The first target is no longer legal. No damage is dealt")
      else if !legalAt 1 (Target.permanent dstId) then
        some (g.logMsg "The second target is no longer legal. No damage is dealt")
      else
        let src := g.object! srcId
        let dst := g.object! dstId
        let n : Int := if useLoyalty then Int.ofNat src.status.loyaltyCounters else g.power src
        some (g.dealDamageFrom (g.name src) dst (max n 0) (source := some src))
    | _, _ => some (g.logMsg "The targets are no longer legal")
  | .returnFromGyWithFinality =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.zone == .graveyard o.owner then
        let name := o.name
        let (g, newId) := g.putOntoBattlefield o.id controller
          (extraEntersWith := #[(.finality, 1)])
        let g := g.logMsg s!"{name} returns to the battlefield"
        if let .chooseReplacement .. := g.pending then
          some (g.chainPendingReplacement (.finishPostStep 20 controller 0 none (some o.id) (shuffle := false)))
        else
          some (g.afterPermanentEnters (g.object! newId))
      else some (g.logMsg s!"{o.name} is no longer in the graveyard")
    | none => some (g.logMsg "The card is no longer in the graveyard")
  | .copyNextInstantSorceryThisTurn =>
    let (g, cause) := g.allocDelayedCause (some controller) sourceId
    let src := sourceId.bind g.damageSourceById?
    let g := g.registerDelayedTrigger {
      controller
      source := src
      kind := .copyNextInstantSorceryThisTurn
      cause
    }
    some (g.logMsg s!"When {(g.player controller).name} next casts an instant or sorcery spell this turn, it is copied")
  | .proliferatePlaneswalkerTypesTimes =>
    -- Ruling 878: X is determined once, as the ability resolves.
    let types := (g.permanentsOf controller).foldl (fun acc o =>
      if g.isPlaneswalker o then
        (g.subtypes o).foldl (fun acc t => if acc.contains t then acc else acc.push t) acc
      else acc) (#[] : Array CardSubtype)
    if types.isEmpty then
      some (g.logMsg s!"{(g.player controller).name} controls no planeswalker types. X is 0")
    else
      some ((g.change (.pending (.chooseProliferate controller types.size))).logMsg
        s!"{(g.player controller).name} proliferates {types.size} time(s)")
  | .copyEachCreatureOfTargetPlayer =>
    -- Rulings 784–789: each token copies the creature's copiable values only
    -- (no counters or status). All tokens are created before any of them is
    -- treated as entering, so they see each other enter.
    some (g.withLegalKindPlayer controller effect.targetKind targets (fun g pid =>
      let sacrifice : TriggeredAbility :=
        .triggered .fromEffect (Effect.ofTrigger .sacrificeSourceIfNoPlaneswalker)
      let snapshots := (g.creaturesControlledBy pid).map fun c =>
        let cv := g.copiableValues c
        { cv with
          keywords := cv.keywords.merge Keyword.haste
          triggeredAbilities := cv.triggeredAbilities.push sacrifice
          isToken := true }
      let g := g.change (.recentTokenIds #[])
      let g := g.withBatch none fun g =>
        g.copyNontokenCreaturesStep controller snapshots
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep 16 controller)
      else
        g.recentTokenIds.foldl (fun g id =>
          match g.findObject? id with
          | some o => if o.isOnBattlefield then g.afterPermanentEnters o else g
          | none => g) g) sourceId)
  | .becomeCopyLegendRuleOff =>
    some (g.withLegalKindPermanent controller effect.targetKind targets (fun g target =>
      g.withSourceOnBattlefield sourceId (fun g src =>
        -- Rulings 812 / 815 / 816: copy the copiable values (already those
        -- of anything the target copies); the land doesn't enter, keeps its
        -- status, and both effects end together in cleanup (ruling 817).
        let g := g.becomeCopyOf src target (untilEot := true)
        let g := g.createEffect (.legendRuleOffThisTurn controller)
        g.logMsg s!"The legend rule doesn't apply to permanents {(g.player controller).name} controls this turn")
        "The source is no longer in play") sourceId (some "The target is no longer legal"))
  | .loseLife (.fixed n) .you => some (g.loseLife controller n.toNat)
  | .gainLife (.fixed n) => some (g.gainLife controller n.toNat)
  | .damageEachOpponent n =>
    let src? := (g.resolvingSpell.bind g.damageSourceById?).orElse (fun _ => sourceId.bind g.damageSourceById?)
    some (g.dealDamageToEachOpponent controller n (source := src?))
  | .teamGain k => some (g.grantUntilEotToControlledCreatures controller k k.joinedAnd)
  | .jaceLoyaltyAtInstantSpeed =>
    let g := g.createEffect (.jaceLoyaltyAtInstantSpeedThisTurn controller)
    some (g.logMsg s!"Until end of turn, {(g.player controller).name} may activate loyalty abilities of Jace planeswalkers they control any time they could cast an instant")
  | r =>
    if r.isFra then some (g.applyFra controller effect r targets sourceId (lastKnownPower := lastKnownPower)) else none

/-- Exile every card in `p`'s hand, then draw that many. Those cards may be
played until the end of `p`'s next turn (Hex Magic; ruling 421). -/
def exileHandDrawPlayUntilNext (g : Game) (p : PlayerId) : Game :=
  let ids := (g.player p).hand
  let n := ids.size
  let (g, cause?) : Game × Option EventCause :=
    if ids.isEmpty then (g, none)
    else
      let (g, c) := g.allocDelayedCause (some p)
      (g, some c)
  let g := g.withBatch cause? fun g =>
    ids.foldl (fun g id =>
      match g.findObject? id with
      | none => g
      | some _ =>
        let (g, newId) := g.move id .exile none (cause := cause?)
        g.createEffect (.playPermission newId { player := p } (turnEnds := 2))
          (cause := cause?)) g
  let g :=
    if n == 0 then g
    else g.logMsg s!"{(g.player p).name} may play the exiled cards until the end of their next turn"
  g.draw p n (cause := cause?)

/-- A token copy of each nontoken creature `p` controls, except it isn't
legendary (Multiversal Incursion; rulings 468 / 508). -/
def copyNontokenCreaturesYouControl (g : Game) (p : PlayerId) : Game :=
  g.withBatch none fun g =>
    let snapshots :=
      ((g.creaturesControlledBy p).filter (fun o => !o.printed.isToken)).map fun src =>
        let cv := g.copiableValues src
        { cv with
          supertypes := cv.supertypes.filter (· != .legendary)
          isToken := true }
    g.copyNontokenCreaturesStep p snapshots

/-- Gain control of the targeted creature until end of turn, or until the end
of your next turn when you control a Villain with greater mana value. Untap
it and it gains haste until end of turn (Evil's Thrall; ruling 514). -/
def applyEvilsThrall (g : Game) (controller : PlayerId) (targets : Array Target) : Game :=
  g.withLegalKindPermanent controller .creature targets (fun g o =>
    let mv := g.objectManaValue o
    let longer := (g.creaturesControlledBy controller).any (fun v =>
      g.hasSubtype v .villain && g.objectManaValue v > mv)
    let g :=
      if longer then
        g.changeControl o controller (turnEndsLeft := 2)
      else
        g.giveControlUntilEot o controller
    match g.findObject? o.id with
    | none => g
    | some o =>
      let g := g.applyPermanentAction o .untap
      match g.findObject? o.id with
      | none => g
      | some o => g.grantUntilEotLogged o Keyword.haste) none
    (some "The target is no longer legal")

/-- Finish `millMayPutPermanentGainLife` once `mill` completes (CR 701.17c). -/
def finishMillMayPutPermanentGainLife (g : Game) (p : PlayerId)
    (preIds : Array ObjectId) (life : Nat) : Game :=
  let permanents := preIds.filterMap (fun id =>
    match g.followMilledPublic? id with
    | some o => if g.isPermanentCard o then some o.id else none
    | none => none)
  if permanents.isEmpty then g.gainLife p life
  else
    g.change (.pending (.fraChoice p (.mayTakeMilled permanents life)))
      |>.logMsg s!"{(g.player p).name} may put a permanent card from among the milled cards into their hand"

/-- Mill `n`, then you may put one permanent card from among them into your
hand. `life` is gained either way (Rapid Rescue). -/
def millMayPutPermanentGainLife (g : Game) (p : PlayerId) (n life : Nat) : Game :=
  let lib := (g.player p).library
  let count := min n lib.size
  let tops := (lib.extract (lib.size - count) lib.size).reverse
  let g := g.mill p n
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishPostStep 68 p (n := life) (ids := tops))
  else
    g.finishMillMayPutPermanentGainLife p tops life

/-- Finish `millMayPutSubtypeOrEnchantment` once `mill` completes (CR 701.17c). -/
def finishMillSubtypeOrEnchantment (g : Game) (p : PlayerId)
    (preIds : Array ObjectId) (subtype : CardSubtype) : Game :=
  let eligible := preIds.filterMap (fun id =>
    match g.followMilledPublic? id with
    | some o =>
      if g.hasSubtype o subtype || g.isEnchantment o then some o.id else none
    | none => none)
  if eligible.isEmpty then
    g.logMsg s!"{(g.player p).name} has no {subtype} or enchantment card among the milled cards"
  else
    g.change (.pending (.fraChoice p (.mayTakeMilled eligible 0)))
      |>.logMsg s!"{(g.player p).name} may put a {subtype} or enchantment card into their hand"

/-- Mill `n`. You may put a card of subtype `subtype`, or an enchantment, from
among those cards into your hand (Rick Jones). -/
def millMayPutSubtypeOrEnchantment (g : Game) (p : PlayerId) (n : Nat) (subtype : CardSubtype) : Game :=
  let lib := (g.player p).library
  let count := min n lib.size
  let tops := (lib.extract (lib.size - count) lib.size).reverse
  let g := g.mill p n
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishMillSubtypeOrEnchantment p tops subtype)
  else
    g.finishMillSubtypeOrEnchantment p tops subtype

/-- Target player gains `life`, searches for a basic land tapped, then a
+1/+1 counter goes on the creature target if it is still legal
(Restorative Technique). -/
def applyGainLifeSearchBasicPlusOne (g : Game) (_controller : PlayerId)
    (targets : Array Target) (life : Nat) : Game :=
  let run (g : Game) : Game :=
    let player? := targets.findSome? (fun t =>
      match t with
      | Target.player pid => some pid
      | _ => none)
    let creature? := targets.findSome? (fun t =>
      match t with
      | Target.permanent id => some id
      | _ => none)
    match player? with
    | none => g.logMsg "The target is no longer legal"
    | some pid =>
      if (g.player pid).lost then g.logMsg "The target is no longer legal"
      else
        let g :=
          match creature? with
          | none => g
          | some id =>
            match g.findObject? id with
            | some o =>
              if o.isOnBattlefield && g.isCreature o then
                g.change (.plusOneAfterSearch (some id))
              else g.logMsg "The target is no longer legal"
            | none => g.logMsg "The target is no longer legal"
        let g := g.gainLife pid life
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishPostStep 22 pid)
        else
          g.beginLibrarySearch pid isBasicLandCard "a basic land card" (.battlefield true)
  g.withContinuationFrame run

/-- You may draw one card for each permanent of type `ty` you control. If you
do, each opponent draws a card (Armor Wars). -/
def mayDrawPerArtifact (g : Game) (p : PlayerId) (ty : CardType := .artifact) : Game :=
  let n := ((g.permanentsOf p).filter (fun o => g.hasType o ty)).size
  if n == 0 then
    let what := if ty == .artifact then "artifacts" else ty.pluralName
    g.logMsg s!"{(g.player p).name} controls no {what}, so no cards are drawn"
  else
    g.change (.pending (.fraChoice p (.mayDrawThenEachOpponentDraws n)))
      |>.logMsg s!"{(g.player p).name} may draw {n}"

/-- You may put a Hero creature card with mana value `maxMv` or less from
your hand onto the battlefield. If you don't, draw a card (Origin of the
Avengers; ruling 507). -/
def mayPutHeroOrDraw (g : Game) (p : PlayerId) (maxMv : Nat)
    (subtype : CardSubtype := .hero) : Game :=
  let ids := (g.player p).hand.filter (fun id =>
    (g.findObject? id).any (fun o =>
      g.isCreature o && g.hasSubtype o subtype && g.objectManaValue o ≤ maxMv))
  if ids.isEmpty then g.draw p 1
  else
    g.change (.pending (.fraChoice p (.mayPutHeroFromHandOrDraw ids)))
      |>.logMsg s!"{(g.player p).name} may put {indefinite subtype.englishName} {subtype} creature card onto the battlefield"

/-- Spells of type `ty` cost `{n}` less this turn. -/
def grantTypeCostLessThisTurn (g : Game) (p : PlayerId) (ty : CardType) (n : Nat) : Game :=
  g.createEffect (.typeSpellCostLessThisTurn p ty n)
    |>.logMsg s!"{ty} spells {(g.player p).name} casts this turn cost \{{n}} less"

/-- Spells with supertype `s` cost `{n}` less this turn. -/
def grantSupertypeCostLessThisTurn (g : Game) (p : PlayerId) (s : Supertype) (n : Nat) : Game :=
  g.createEffect (.supertypeSpellCostLessThisTurn p s n)
    |>.logMsg s!"{s} spells {(g.player p).name} casts this turn cost \{{n}} less"

/-- Return up to two graveyard cards, each using a different mode among
artifact, creature, enchantment, and land (Call Damage Control). -/
def returnChosenGraveyardCards (g : Game) (controller : PlayerId)
    (targets : Array Target) : Game :=
  let kinds : Array CardType := #[.artifact, .creature, .enchantment, .land]
  g.withBatch (g.resolvingBatchCause controller none) fun g =>
    Id.run do
      let mut g := g
      let mut used : Array CardType := #[]
      for t in targets.extract 0 2 do
        match t with
        | Target.card id =>
          match g.findObject? id with
          | some o =>
            if o.zone == .graveyard controller && o.owner == controller then
              let avail := kinds.filter (fun ty =>
                !used.contains ty && g.objectHasCardType o ty)
              match avail[0]? with
              | some ty =>
                g := g.returnToHand o.id controller
                used := used.push ty
              | none =>
                g := g.logMsg s!"{o.name} doesn't match a mode that is still available"
            else
              g := g.logMsg "The target is no longer legal"
          | none =>
            g := g.logMsg "The target is no longer legal"
        | _ =>
          g := g.logMsg "The target is no longer legal"
      return g

/-- Put a +1/+1 counter and a double strike counter on the source (Quicksilver). -/
def plusOneAndDoubleStrike (g : Game) (sourceId : Option ObjectId) : Game :=
  g.withSourceOnBattlefield sourceId (fun g o =>
    g.withBatch none fun g =>
      let g := g.addPlusOnePlusOneTo o 1
      let g := g.recordPutCounters o.id .doubleStrike 1
        (byPlayer := g.controllerOf o)
      g.logMsg s!"{g.name o} gets a double strike counter")
    "The source is no longer in play"

/-- Put a +1/+1 counter on the source, then it fights up to one creature an
opponent controls (Abomination). -/
def plusOneThenFight (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (targets : Array Target) : Game :=
  let g :=
    g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 1)
      "The source is no longer in play"
  match targets[0]? with
  | none => g
  | some _ =>
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep 23 controller 0 sourceId (targets := targets))
    else
      g.withLegalKindPermanent controller .oppCreature targets (fun g tgt =>
        match sourceId.bind g.findObject? with
        | some src =>
          if src.isOnBattlefield && g.isCreature src then g.fightCreatures src tgt
          else g.logMsg "The source is no longer in play"
        | none => g.logMsg "The source is no longer in play") sourceId
        (some "The target is no longer legal")

/-- Destroy each creature other than `sourceId` whose mana value is even
(`even := true`) or odd. Zero is even (Thanos). -/
def destroyCreaturesByManaParity (g : Game) (sourceId : Option ObjectId) (even : Bool) : Game :=
  let preBf := g.battlefield
  let ids := (preBf.filter (fun o =>
    some o.id != sourceId && g.isCreature o &&
      ((g.objectManaValue o % 2 == 0) == even))).map (·.id)
  let quality := if even then "even" else "odd"
  let g := g.logMsg s!"Destroy each other creature with {quality} mana value"
  g.withBatch none fun g =>
    g.destroyPermanentsLoop ids (preBattlefield := some preBf)

/-- Reveal the top card. Draw it when it is an artifact (Iron Lad). -/
def revealTopDrawIfArtifact (g : Game) (p : PlayerId) : Game :=
  match (g.player p).library.back? with
  | none => g.logMsg s!"{(g.player p).name} has no cards in their library"
  | some id =>
    let o := g.object! id
    let g := g.record (GameEvent.revealed g.turnNumber p #[id]
      (cause := some (g.resolvingOrRuleCause p)))
    let g := g.logMsg s!"{(g.player p).name} reveals {o.name}"
    if g.isArtifact o then g.draw p 1 else g

/-- Return up to one creature card from your graveyard, then put `n` +1/+1
counters on the source (Unliving Legionnaire). -/
def returnGyCreatureThenPlusOne (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (targets : Array Target) (n : Nat) : Game :=
  let g :=
    match targets[0]? with
    | none => g
    | some (Target.card id) =>
      match g.findObject? id with
      | some o =>
        if o.zone == Zone.graveyard controller && g.isCreature o then
          g.returnToHand o.id o.owner
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    | some _ => g.logMsg "The target is no longer legal"
  g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o n)
    "The source is no longer in play"

/-- Return the source from its owner's graveyard with a finality counter,
then you may attach an Equipment you control (Winter Soldier). -/
def returnFromGyFinalityAttach (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) : Game :=
  match sourceId.bind g.findObject? with
  | none => g.logMsg "The card is no longer in the graveyard"
  | some o =>
    if o.zone != .graveyard o.owner then
      g.logMsg s!"{o.name} is no longer in the graveyard"
    else
      let name := o.name
      let (g, newId) := g.putOntoBattlefield o.id controller
        (extraEntersWith := #[(.finality, 1)])
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep 24 controller 0 none (some o.id))
      else
        let g := g.afterPermanentEnters (g.object! newId)
        if g.pending != .none then g
        else if (g.permanentsOf controller).any (fun eq => g.isEquipment eq) then
          g.change (.pending (.mayAttachEquipment controller newId))
            |>.logMsg s!"{(g.player controller).name} may attach an Equipment to {name}"
        else g

/-- Put remaining counter kinds and any `+1/+1` counter on `targetId` during
`proliferateTarget`, chaining `.finishProliferateEachKind` on
`Pending.chooseReplacement` and recording `GameEvent.proliferated` only after
all counter puts finish (CR 701.34a / 616.1). -/
partial def finishProliferateEachKind (g : Game) (controller : PlayerId)
    (targetId : ObjectId) (remainingKinds : Array CounterKind)
    (hasPlusOne : Bool) (effCause : EventCause) : Game :=
  if hasPlusOne then
    let g :=
      match g.findObject? targetId with
      | some o => g.addPlusOnePlusOneTo o 1 (byPlayer := some controller) (cause := some effCause)
      | none => g
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishProliferateEachKind controller targetId remainingKinds false effCause)
    else
      g.finishProliferateEachKind controller targetId remainingKinds false effCause
  else
    match remainingKinds[0]? with
    | some kind =>
      let restKinds := remainingKinds.extract 1 remainingKinds.size
      let g := g.recordPutCounters targetId kind 1 (byPlayer := some controller) (cause := some effCause)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishProliferateEachKind controller targetId restKinds false effCause)
      else
        g.finishProliferateEachKind controller targetId restKinds false effCause
    | none =>
      let g := g.syncImpendingNotACreature targetId (cause := some effCause)
      let oName := ((g.findObject? targetId).map g.name).getD "permanent"
      (g.record (GameEvent.proliferated g.turnNumber controller (permanents := #[targetId]) (cause := some effCause))).logMsg
        s!"{oName} gets another counter of each kind"

/-- One more counter of each kind already on the target (Powerful Broker). -/
def proliferateTarget (g : Game) (controller : PlayerId) (targets : Array Target) : Game :=
  g.withLegalKindTarget controller .permanentOrPlayer targets (fun g t =>
    let cause := some (g.resolvingOrRuleCause controller)
    g.withBatch cause fun g =>
      let effCause := g.resolveOptionalCause cause (fallbackCtrl := some controller)
      match t with
      | Target.permanent id =>
        match g.findObject? id with
        | some o =>
          if o.isOnBattlefield && o.status.hasCounters then
            let hasPlusOne := o.status.plusOnePlusOne > 0
            let nonPlusKinds :=
              o.status.toCounterBag.filterMap (fun (kind, _) =>
                if kind == .plusOnePlusOne then none else some kind)
            g.finishProliferateEachKind controller id nonPlusKinds hasPlusOne effCause
          else g.logMsg s!"{g.name o} has no counters"
        | none => g.logMsg "The target is no longer legal"
      | Target.player pid =>
        let pl := g.player pid
        if pl.poison > 0 then
          let g := g.record (GameEvent.poisoned g.turnNumber pid 1 (byPlayer := some controller) (cause := effCause))
          (g.record (GameEvent.proliferated g.turnNumber controller (players := #[pid]) (cause := some effCause)))
            |>.logMsg s!"{pl.name} gets a poison counter"
        else g.logMsg s!"{pl.name} has no counters"
      | Target.card _ => g.logMsg "The target is no longer legal") none
    (some "The target is no longer legal")

/-- Put the chosen artifact creature onto the battlefield with `x` +1/+1
counters. Shuffle when the library was searched (Vision Quest; ruling 506). -/
def finishVisionQuest (g : Game) (p : PlayerId) (id? : Option ObjectId)
    (x : Nat) (shuffle : Bool) : Game :=
  let g :=
    if shuffle then
      let foundFromLib :=
        match id? with
        | some id =>
          if (g.findObject? id).any (fun o =>
              o.zone == .library p && g.isArtifact o && g.isCreature o &&
                g.objectManaValue o ≤ x) then #[id]
          else #[]
        | none => #[]
      g.record (GameEvent.searched g.turnNumber p p foundFromLib
        (cause := some (g.resolvingOrRuleCause p)))
    else g
  match id? with
  | none =>
    let g := g.logMsg s!"{(g.player p).name} finds no artifact creature card"
    if shuffle then g.shuffleThen p .none else g
  | some id =>
    match g.findObject? id with
    | some o =>
      if (o.zone == .library p || o.zone == .graveyard p) &&
          g.isArtifact o && g.isCreature o &&
          g.objectManaValue o ≤ x then
        let name := o.name
        let (g, newId) := g.putOntoBattlefield id p
          (extraEntersWith := if x > 0 then #[(.plusOnePlusOne, x)] else #[])
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishPostStep 25 p x none (some id) (shuffle := shuffle))
        else
          let g := g.afterPermanentEnters (g.object! newId)
          let g :=
            if x ≥ 4 then g.grantUntilEotLogged (g.object! newId) Keyword.haste else g
          let g := g.logMsg s!"{name} is put onto the battlefield"
          if shuffle then g.shuffleThen p .none else g
      else
        let g := g.logMsg "That card can't be found"
        if shuffle then g.shuffleThen p .none else g
    | none =>
      let g := g.logMsg "That card can't be found"
      if shuffle then g.shuffleThen p .none else g

/-- Search the library and/or graveyard for an artifact creature with mana
value `x` or less (Vision Quest). -/
def beginVisionQuest (g : Game) (p : PlayerId) (x : Nat) : Game :=
  let ok (o : GameObject) : Bool :=
    g.isArtifact o && g.isCreature o && g.objectManaValue o ≤ x
  let lib := (g.player p).library.filter (fun id => (g.findObject? id).any ok)
  let gy := (g.player p).graveyard.filter (fun id => (g.findObject? id).any ok)
  if lib.isEmpty && gy.isEmpty then
    let g := g.record (GameEvent.searched g.turnNumber p p #[]
      (cause := some (g.resolvingOrRuleCause p)))
    (g.logMsg s!"{(g.player p).name} finds no artifact creature card").shuffleThen p .none
  else
    g.change (.pending (.fraChoice p (.visionQuestZones lib gy x)))
      |>.logMsg s!"{(g.player p).name} may search their library and their graveyard"

/-- Connive `id` when it is still a creature the spell's controller controls. -/
def conniveTricksterTarget (g : Game) (controller : PlayerId) (id? : Option ObjectId) : Game :=
  match id? with
  | none => g
  | some id =>
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield && g.isCreature o && g.controlledBy o controller then
        g.applyConnive controller (some id)
      else g.logMsg "The target is no longer legal"
    | none => g.logMsg "The target is no longer legal"

/-- Mana value of spells `p` has cast this turn other than the spell resolving
now (ruling 110). Cascade spells that were actually cast are included. A
resolving copy was not cast, so its mana value is not subtracted. -/
def otherSpellsManaValue (g : Game) (p : PlayerId) : Nat :=
  let total := (g.loggedCastManaValues p).foldl (· + ·) 0
  let own :=
    match g.resolvingSpell.bind g.findObject? with
    | some spell =>
      if spell.isCopy || g.controllerOf spell != some p then 0
      else g.objectManaValue spell
    | none => 0
  total - own

/-- Creature types present on the battlefield, one word each. -/
def battlefieldCreatureTypes (g : Game) : Array CardSubtype :=
  g.battlefield.foldl (fun acc o =>
    if !g.isCreature o then acc
    else
      (g.subtypes o).foldl (fun acc t =>
        if t.isCreatureType && !acc.contains t then acc.push t else acc) acc) #[]

/-- Return each creature that doesn't have `chosen` to its owner's hand. -/
def returnCreaturesNotOfType (g : Game) (chosen : CardSubtype) : Game :=
  g.withBatch none fun g =>
    g.foldBattlefield (fun o => g.isCreature o && !g.hasSubtype o chosen)
      (fun g o => g.returnToHand o.id o.owner)

/-- Step through `remaining` looked-at cards for `finishRevealPutCreatures`,
pausing on `Pending.chooseReplacement` and running `afterPermanentEnters` once
every chosen card has entered. -/
def finishRevealPutCreaturesStep (g : Game) (p : PlayerId)
    (remaining put enteredFromIds : Array ObjectId)
    (cause : Option EventCause := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishPostStep 26 p 0 none none
        (ids := remaining)
        (targets := put.map Target.card)
        (modes := enteredFromIds.map (·.raw))
        (cause := cause))
  let mut g := g
  let mut entered := enteredFromIds
  for i in [0:remaining.size] do
    let id := remaining[i]!
    match g.findObject? id with
    | some o =>
      if put.contains id && g.isCreature o && o.zone == .library p then
        let name := o.name
        let (g', _) := g.putOntoBattlefield id p (cause := cause)
        g := g'.logMsg s!"{(g'.player p).name} puts {name} onto the battlefield"
        entered := entered.push id
      else if o.zone == .library o.owner then
        let (g', _) := g.move id (.graveyard o.owner) none (cause := cause)
        g := g'
      if let .chooseReplacement .. := g.pending then
        let rem := remaining.extract (i + 1) remaining.size
        return g.chainPendingReplacement
          (.finishPostStep 26 p 0 none none
            (ids := rem)
            (targets := put.map Target.card)
            (modes := entered.map (·.raw))
            (cause := cause))
    | none => pure ()
  for fromId in entered do
    match g.followMovedToZone? fromId (· == .battlefield) with
    | some enteredObj => g := g.afterPermanentEnters enteredObj
    | none => pure ()
  return g

/-- Put `put` onto the battlefield, then the rest of `looked` into their
owners' graveyards. Enters abilities run after every chosen creature is on
the battlefield. -/
def finishRevealPutCreatures (g : Game) (p : PlayerId) (looked put : Array ObjectId) : Game :=
  let (g0, cause?) : Game × Option EventCause :=
    if looked.isEmpty then (g, none)
    else
      let (g, c) := g.allocDelayedCause (some p)
      (g, some c)
  g0.withBatch cause? fun g =>
    g.finishRevealPutCreaturesStep p looked put #[] (cause := cause?)

/-- Carry out a `chooseCards` answer. -/
def finishChooseCards (g : Game) (p : PlayerId) (chosen : Array ObjectId)
    (purpose : CardChoice) (cause : Option EventCause := none) : Game :=
  let stashed := cause.orElse (fun _ => g.stashedCause.orElse (fun _ => chosen[0]?.bind g.lastMoveCauseOf?))
  let g := if g.stashedCause.isSome then g.change (.stashedCause none) else g
  let allocIfResolving (g : Game) : Game × Option EventCause :=
    match g.currentResolvingContext? with
    | some (src, ctrl) =>
      let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some p)) src
      (g, some c)
    | none => (g, none)
  match purpose with
  | .toHand _ =>
    let (g, cause?) : Game × Option EventCause :=
      if chosen.isEmpty then (g, none)
      else
        match stashed with
        | some c => (g, some c)
        | none => allocIfResolving g
    g.withBatch cause? fun g =>
      chosen.foldl (fun g id =>
        match g.findObject? id with
        | some o =>
          if isPublicZone o.zone || o.zone == .hand o.owner then
            let name := o.name
            (g.move id (.hand p) none (cause := cause?)).1.logMsg s!"{(g.player p).name} puts {name} into their hand"
          else g
        | none => g) g
  | .creaturesToBattlefield =>
    let valid := chosen.filter fun id =>
      (g.findObject? id).any (fun o => o.zone == .hand o.owner && g.isCreature o)
    let (g, cause?) : Game × Option EventCause :=
      if valid.isEmpty then (g, none)
      else
        match stashed with
        | some c => (g, some c)
        | none => allocIfResolving g
    let g := valid.foldl (fun g id =>
      match g.findObject? id with
      | some o => g.logMsg s!"{o.name} enters the battlefield"
      | none => g) g
    g.withBatch cause? fun g =>
      g.putToBattlefieldLoop p valid (cause := cause?)
  | .landsTappedGainLife life =>
    let valid := chosen.filter fun id =>
      (g.findObject? id).any (fun o => g.isLand o && o.zone == .library o.owner)
    let (g, cause?) : Game × Option EventCause :=
      if valid.isEmpty then (g, none)
      else
        match stashed with
        | some c => (g, some c)
        | none => allocIfResolving g
    let g := valid.foldl (fun g id =>
      match g.findObject? id with
      | some o => g.logMsg s!"{o.name} enters tapped"
      | none => g) g
    let g := g.withBatch cause? fun g =>
      g.putToBattlefieldLoop p valid (tapped := true) (isLandEnters := true) (cause := cause?)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep 27 p life)
    else
      let g := g.requestShuffle p (.gainLife p life)
      g.continueIfShuffled
  | .keepDestroyRest =>
    let preBf := g.battlefield
    let doomed := (preBf.filter (fun o => g.isCreature o && !chosen.contains o.id)).map (·.id)
    let (g, cause?) : Game × Option EventCause :=
      if !doomed.isEmpty then
        match stashed with
        | some c => (g, some c)
        | none => allocIfResolving g
      else (g, none)
    g.withBatch cause? fun g =>
      g.destroyPermanentsLoop doomed
        (logMsgAfter := some "Chosen creatures are kept; the rest are destroyed")
        (preBattlefield := some preBf) (cause := cause?)
  | .amassArmy subtype n attach =>
    match chosen[0]? with
    | some id => g.finishAmassOn p id subtype n attach (cause := cause)
    | none => g.logMsg s!"{(g.player p).name} doesn't choose an Army"

/-- Ask `p` to choose up to `max` of `ids`, or resolve immediately when there
is nothing to decide. -/
def offerCardChoice (g : Game) (p : PlayerId) (ids : Array ObjectId) (max : Nat)
    (purpose : CardChoice) (msg : String) (cause : Option EventCause := none) : Game :=
  if ids.isEmpty || max == 0 then g.finishChooseCards p #[] purpose (cause := cause)
  else
    let g :=
      match cause with
      | some c => g.change (.stashedCause (some c))
      | none => g
    g.beginFraChoice p (.chooseCards ids max purpose) msg

/-- Finish `millThenChooseForHand` once `mill` completes (CR 701.17c). -/
def finishMillChooseForHand (g : Game) (p : PlayerId) (preIds : Array ObjectId)
    (pred : ObjectId → GameObject → Bool) (max : Nat) (mustOne : Bool)
    (cause : Option EventCause := none) : Game :=
  let eligible := preIds.filterMap (fun id =>
    match g.followMilledPublic? id with
    | some o => if pred id o then some o.id else none
    | none => none)
  if eligible.isEmpty then g
  else if mustOne && eligible.size == 1 then
    g.finishChooseCards p eligible (.toHand true) (cause := cause)
  else
    g.offerCardChoice p eligible max (.toHand mustOne)
      s!"{(g.player p).name} chooses cards to put into their hand"
      (cause := cause)

/-- Mill `n`, then choose matching cards from among them for your hand (CR 610.1 / 701.17). -/
def millThenChooseForHand (g : Game) (p : PlayerId) (n : Nat)
    (pred : GameObject → Bool) (max : Nat) (mustOne : Bool)
    (types : Array CardType := #[]) : Game :=
  let lib := (g.player p).library
  let count := min n lib.size
  let tops := (lib.extract (lib.size - count) lib.size).reverse
  let matchedPreIds := tops.filter (fun id => (g.findObject? id).any pred)
  let (g, cause?) : Game × Option EventCause :=
    if n == 0 || lib.isEmpty then (g, none)
    else
      match g.currentResolvingContext? with
      | some (src, ctrl) =>
        let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some p)) src
        (g, some c)
      | none => (g, none)
  let g := g.mill p n (cause := cause?)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement
      (.finishMillChooseForHand p tops types matchedPreIds max mustOne false none cause?)
  else
    g.finishMillChooseForHand p tops (fun _ o => pred o) max mustOne (cause := cause?)

/-- True when a targeted sequence must not resolve (CR 608.2b).
A missing or illegal required target means none of the steps happen, so
destroy-then-surveil does not surveil and pump-then-draw does not draw.
“Up to” effects with no announced target still resolve. -/
def sequenceAllTargetsIllegal (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (sourceId : Option ObjectId := none) : Bool :=
  let kind := effect.targetKind
  let slots := if kind.spec.slots.isEmpty then #[kind] else kind.spec.slots
  -- A skipped “up to” slot is absent from `targets`, so a later target is not
  -- at the same index as its slot. A target keeps the sequence when it is
  -- legal for any slot of the effect.
  effect.requiresTarget &&
    !(effect.allowsZeroTargets && targets.isEmpty) &&
    (targets.isEmpty ||
      targets.all fun t =>
        slots.all fun slot =>
          !(g.legalTargetsForAtomicKind controller slot sourceId).contains t)

/-- Log why a sequence with a required target did not resolve. -/
def logIllegalSequenceTargets (g : Game) (targets : Array Target) : Game :=
  if targets.isEmpty then
    g.logMsg "The target is no longer legal"
  else
    targets.foldl (fun g t => g.illegalAbilityTarget t) g

/-- Tap, then scry `scryN` and draw `drawN`. The draw waits until the scry
finishes. An illegal required target runs `fizzle` and skips every step
(Hithlain Knots, ruling 188). -/
def resolveTapScryDraw (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (scryN drawN : Nat)
    (sourceId : Option ObjectId := none)
    (fizzle : Game → Game := fun g => g.logMsg "The spell doesn't resolve") : Game :=
  if g.sequenceAllTargetsIllegal controller effect targets sourceId then
    fizzle g
  else
    let g := g.applyOnPermanent controller effect.targetKind targets .tap sourceId
    g.scryThenDraw controller scryN drawN

/-- Ask `controller` whether to resolve `r`. Attaching Equipment is the
existing choice of one Equipment or declining. Any other resolution is
accept or decline. -/
def beginMay (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (r : SpellResolution) : Game :=
  match r with
  | .attachEquipment =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      ((g.clearMay).change (.pending (.mayAttachEquipment controller o.id))).logMsg
        s!"{(g.player controller).name} may attach an Equipment to {g.name o}")
  | r =>
    let phrase := SpellResolution.toPhrase r effect.targeting.kind.noun
    let phrase := if phrase.startsWith "you " then (phrase.drop 4).toString else phrase
    let inner := { effect with resolution := Resolution.ofSpell r }
    (g.changes #[
      .pending (.mayResolve controller),
      .mayEffect (some inner),
      .mayController controller,
      .mayTargets targets]).logMsg
      s!"{(g.player controller).name} may {phrase}"

/-- Ask a player to choose one resolution in `rs`. A library top-or-bottom
pair is the owner's choice; any other list is the caster's. One alternative
is applied by `applyUnified` before this is called. -/
def beginSpellOr (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (rs : List SpellResolution) : Game :=
  let asEffect (r : SpellResolution) : Effect :=
    { effect with resolution := Resolution.ofSpell r }
  let g := g.clearSpellOr
  match rs with
  | [.onPermanent .putOnTopOfLibrary, .onPermanent .putOnBottomOfLibrary]
  | [.onPermanent .putOnBottomOfLibrary, .onPermanent .putOnTopOfLibrary] =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield then
          (g.changes #[
            .pending (.chooseLibraryPlacement o.owner id),
            .spellOr #[
              asEffect (.onPermanent .putOnTopOfLibrary),
              asEffect (.onPermanent .putOnBottomOfLibrary)],
            .spellOrController controller,
            .spellOrTargets targets,
            .spellOrLibrary true]).logMsg
            s!"{(g.player o.owner).name} chooses top or bottom of their library for {g.name o}"
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | _ =>
    (g.changes #[
      .pending (.chooseLibraryPlacement controller ⟨g.nextObjectId⟩),
      .spellOr (rs.map asEffect).toArray,
      .spellOrController controller,
      .spellOrTargets targets,
      .spellOrLibrary false]).logMsg
      s!"{(g.player controller).name} chooses {SpellResolution.toPhrase (.or rs) effect.targeting.kind.noun}"

/-- Apply `whenHolds` when `cond` is true and `whenNot` otherwise.
An illegal target applies neither (CR 608.2b). -/
private def branchOnSpellIf (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (cond : TriggeredAbility.ConditionSelector) (castFromGraveyard : Bool)
    (whenHolds whenNot : Game → Game) (giftPromised : Bool := false) : Game :=
  match cond with
  | .subtype subtype =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      if g.hasSubtype o subtype then whenHolds g else whenNot g)
  | .mvAtMost n =>
    match targets[0]? with
    | some (Target.card id) =>
      -- `{X}` remains after the spell leaves the stack. That announced
      -- value is the mana value the spell had (CR 202.3e).
      let mv? : Option Nat :=
        match g.findObject? id with
        | some o => some (g.objectManaValue o (includeLkiX := true))
        | none => (g.lastKnownBefore? id).map (·.manaValue)
      match mv? with
      | none => g.logMsg "The target is no longer legal"
      | some mv =>
        if mv ≤ n then whenHolds g else whenNot g
    | _ => g.logMsg "The target is no longer legal"
  | .castFromGraveyard =>
    if castFromGraveyard then whenHolds g else whenNot g
  | .teamwork =>
    if g.resolvingTeamworkPaid then whenHolds g else whenNot g
  | .giftPromised =>
    if giftPromised then whenHolds g else whenNot g
  | _ => whenNot g

mutual
/-- Execute `steps` sequentially for `applyUnified`, pausing on `Pending` or
`afterRandom` and chaining `.continueUnified` so later steps run after the pause. -/
partial def runUnifiedSteps (g : Game) (controller : PlayerId) (effect : Effect)
    (steps : Array Resolution) (targets : Array Target)
    (castFromGraveyard kicked giftPromised : Bool) (chosenX : Nat)
    (sourceId : Option ObjectId) : Game := Id.run do
  let mut g := g
  for i in [0:steps.size] do
    let pendingBefore := g.pending
    let randomBefore := g.afterRandom
    g := g.applyUnified controller { effect with resolution := steps[i]! } targets
      (castFromGraveyard := castFromGraveyard) (kicked := kicked)
      (giftPromised := giftPromised) (chosenX := chosenX)
      (sourceId := sourceId)
    let rem := steps.extract (i + 1) steps.size
    if !rem.isEmpty then
      let opened :=
        (g.pending != pendingBefore && g.pending != .none) ||
          (g.afterRandom != randomBefore && g.afterRandom != .none)
      if opened then
        return g.chainPendingReplacement
          (.continueUnified controller effect rem targets
            castFromGraveyard kicked giftPromised chosenX sourceId)
  return g

/-- Resolve a unified `Effect` as a spell (CR 608). -/
partial def applyUnified (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) : Game :=
  if g.continuations.isEmpty then
    g.withContinuationFrame fun g =>
      g.applyUnified controller effect targets
        (castFromGraveyard := castFromGraveyard) (kicked := kicked)
        (giftPromised := giftPromised) (chosenX := chosenX)
        (sourceId := sourceId)
  else
  let sourceId := sourceId.orElse (fun _ => g.resolvingSpell)
  match g.applyFraResolution? controller effect targets sourceId with
  | some g => g
  | none =>
  match effect.resolution with
  | .sequence rs =>
    match rs.flatMap Resolution.flatten with
    | [.onPermanent .tap, .scry (.fixed scryN), .draw (.fixed drawN)] =>
      g.resolveTapScryDraw controller effect targets scryN.toNat drawN.toNat
    | steps =>
      if g.sequenceAllTargetsIllegal controller effect targets then
        g.logIllegalSequenceTargets targets
      else
        match steps with
        | [.shuffleSource, .draw (.fixed n)] =>
          g.shuffleSourceIntoLibrary none (.draw controller n.toNat)
        | steps =>
          g.runUnifiedSteps controller effect steps.toArray targets
            castFromGraveyard kicked giftPromised chosenX sourceId
  | .shuffleSource =>
    g.shuffleSourceIntoLibrary none
  | .gainLife (.fixed n) => g.gainLife controller n.toNat
  | .teamGain k =>
    g.grantUntilEotToControlledCreatures controller k k.joinedAnd
  | .recruit _ => g.beginRecruit controller
  | .addMana types (.fixed 1) =>
    g.addManaLogged controller types (source := sourceId)
  | .discard (.cards n) =>
    g.beginDiscardCards #[controller] n
  | .onSource a =>
    g.applyOnPermanent controller effect.targetKind targets a sourceId
  | _ =>
  match effect.spellResolution with
  | .fight .announced (.timesPower k) =>
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
  | .mutualFight .both =>
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
  | .mutualFight .upToOne =>
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
  | .extraLand =>
    let g := g.createEffect (.additionalLandsThisTurn controller 1)
    g.logMsg s!"{(g.player controller).name} may play an additional land this turn"
  | .unrecognized =>
    match effect.resolution with
    | .searchBasicLand => g.resolveSearchBasicLandTapped controller
    | .searchLandTypeToHand t =>
      match CardSubtype.ofOracle? t with
      | some st => g.resolveSearchLandTypeToHand controller st
      | none => g.resolveLibrarySearchToHand controller (fun _ => false) s!"{t} card"
    | .searchBasicLandToHand => g.resolveSearchBasicLandToHand controller
    | .exileTop => g.resolveExileTopPlayUntilEndOfNextTurn controller
    | _ => g.logMsg "The effect does nothing"
  | .onPermanent action =>
    g.applyOnPermanent controller effect.targetKind targets action sourceId
  | .creaturesPump p t scope =>
    match scope with
    | .youControl =>
      g.pumpControlledCreatures controller p t
    | .all =>
      g.foldBattlefield (fun o => g.isCreature o) (fun g o => g.pumpPermanent o p t)
    | .ofTargetPlayer =>
      g.withLegalKindPlayer controller effect.targetKind targets
        (fun g pid => g.pumpControlledCreatures pid p t)
  | .exileGraveyardCreaturesGrantCast ty =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.exileCreaturesFromGraveyard controller pid ty)
  | .draw (.fixed n) .you => g.draw controller n.toNat
  | .draw (.fixed n) .player =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.draw pid n.toNat)
  | .scry (.fixed n) =>
    g.beginScry controller n.toNat
  | .tapTargets =>
    g.foldPermanentTargets targets (fun g o =>
      if o.isOnBattlefield && g.isCreature o then g.applyPermanentAction o .tap else g)
  | .counter =>
    match targets[0]? with
    | some (Target.card id) => g.counterStackSpell id (controller := some controller)
    | _ => g.logMsg "The target is no longer legal"
  | .unlessPays r n =>
    g.beginUnlessPays controller effect targets r n
  | .counterExilePermanentMayCast =>
    match targets[0]? with
    | some (Target.card id) =>
      g.counterStackSpell id (exilePermanent := true) (grantFreeCast := true)
        (controller := some controller)
    | _ => g.logMsg "The target is no longer legal"
  | .or rs =>
    match rs with
    | [] => g.logMsg "The effect does nothing"
    | [r] =>
      g.applyUnified controller { effect with resolution := Resolution.ofSpell r } targets
        (castFromGraveyard := castFromGraveyard) (kicked := kicked)
        (giftPromised := giftPromised) (chosenX := chosenX) (sourceId := sourceId)
    | rs =>
      g.beginSpellOr controller effect targets rs
  | .attachEquipment =>
    g.beginMay controller effect targets .attachEquipment
  | .may r _ _ =>
    g.beginMay controller effect targets r
  | .recruit _ =>
    g.beginRecruit controller
  | .«if» cond r =>
    let run (g : Game) : Game :=
      g.applyUnified controller { effect with resolution := Resolution.ofSpell r } targets
        (castFromGraveyard := castFromGraveyard) (kicked := kicked)
        (giftPromised := giftPromised) (chosenX := chosenX) (sourceId := sourceId)
    g.branchOnSpellIf controller effect targets cond castFromGraveyard run id giftPromised
  | .ifElse cond whenTrue whenFalse =>
    let run (r : SpellResolution) (g : Game) : Game :=
      g.applyUnified controller { effect with resolution := Resolution.ofSpell r } targets
        (castFromGraveyard := castFromGraveyard) (kicked := kicked)
        (giftPromised := giftPromised) (chosenX := chosenX) (sourceId := sourceId)
    g.branchOnSpellIf controller effect targets cond castFromGraveyard
      (run whenTrue) (run whenFalse) giftPromised
  | .exchangeControl =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent a), some (Target.permanent b) =>
      match g.findObject? a, g.findObject? b with
      | some oa, some ob =>
        -- Both must still be nonland permanents that share a card type.
        -- If either is illegal, the exchange does not happen (CR 701.12a).
        let nonland (o : GameObject) :=
          o.isOnBattlefield && !(g.types o).any (· == .land)
        let share := (g.types oa).any (fun t => (g.types ob).contains t)
        if a != b && nonland oa && nonland ob && share then
          match g.controllerOf oa, g.controllerOf ob with
          | some pa, some pb =>
            -- CR 701.12a / 104.5 / 800.4a–b: if the entire exchange can't be
            -- completed (e.g. a controller has left the game), no part occurs.
            if (g.player pa).lost || (g.player pb).lost then
              g.logMsg "The exchange can't be completed (CR 701.12a)."
            -- CR 701.12b: if both permanents are controlled by the same player,
            -- the exchange effect does nothing.
            else if pa == pb then
              g
            else
              let oaName := g.name oa
              let obName := g.name ob
              let batchCause := some (EventCause.oneShotEffect none sourceId (some controller))
              let g := g.withBatch batchCause fun g =>
                let g := g.changeControl oa pb (cause := batchCause)
                match g.findObject? b with
                | some ob => g.changeControl ob pa (cause := batchCause)
                | none => g
              g.logMsg s!"{oaName} and {obName} exchange control"
          | _, _ =>
            g.logMsg "A target is no longer legal. The exchange doesn't happen."
        else
          g.logMsg "A target is no longer legal. The exchange doesn't happen."
      | _, _ =>
        g.logMsg "A target is no longer legal. The exchange doesn't happen."
    | _, _ =>
      g.logMsg "A target is no longer legal. The exchange doesn't happen."
  | .countersOnCreatureTargets kind n which =>
    match which with
    | .firstYouControl =>
      match targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some o =>
          if o.isOnBattlefield && g.isCreature o && g.controlledBy o controller then
            g.addCounters o kind n
          else g.logMsg "The target is no longer legal"
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "The target is no longer legal"
    | .each =>
      Id.run do
        let creatureLegal := g.legalTargetsForAtomicKind controller .creature none
        let mut g := g
        for t in targets do
          match t with
          | Target.permanent oid =>
            if creatureLegal.contains t then
              match g.findObject? oid with
              | some o => g := g.addCounters o kind n
              | none => g := g.logMsg "The target is no longer in play"
            else
              g := g.illegalAbilityTarget t
          | Target.card _ =>
            g := g.illegalAbilityTarget t
          | Target.player _ => pure ()
        return g
  | .gainLife (.fixed n) => g.gainLife controller n.toNat
  | .targetPlayersGainLife n =>
    Id.run do
      let playerLegal := g.legalTargetsForAtomicKind controller .player none
      let (g, cause?) : Game × Option EventCause :=
        if n == 0 || targets.isEmpty then (g, none)
        else
          match g.currentResolvingContext? with
          | some (src, ctrl) =>
            let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some controller)) src
            (g, some c)
          | none => (g, none)
      let mut g := g
      for t in targets do
        match t with
        | Target.player pid =>
          if playerLegal.contains t then
            g := g.gainLife pid n (cause := cause?)
          else
            g := g.illegalAbilityTarget t
        | _ => pure ()
      return g
  | .amass (.fixed n) subtype =>
    g.amass controller subtype n.toNat
  | .searchCard s ty how =>
    let pred := fun c => c.hasType ty && c.hasSupertype s
    let card := s!"{s.oracleWord} {ty.oracleWord} card"
    match how with
    | .youToHand =>
      g.resolveLibrarySearchToHand controller pred card
    | .ownerMayToBattlefield =>
      match targets[0]? with
      | some (Target.permanent id) =>
        let owner? :=
          (g.findObject? id).map (·.owner) |>.orElse
            (fun _ => (g.lastKnownBefore? id).map (·.owner))
        match owner? with
        | some owner =>
          g.beginLibrarySearch owner pred s!"a {card}" (.battlefield true) (optional := true)
        | none => g
      | _ => g
  | .dealDamageToEachCreature n which amount =>
    let n := match amount with
      | .fixed => n
      | .otherSpellsManaValue => g.otherSpellsManaValue controller
    let srcEvent? := (sourceId.bind g.damageSourceById?).map g.snapshotDamageSource
    let g := match which with
      | .each => g.dealDamageToEachCreatureMatching n (source := srcEvent?)
      | .opponentsControl =>
        g.dealDamageToEachCreatureMatching n (fun o => !g.controlledBy o controller) (source := srcEvent?)
      | .nonSubtype subtype => g.dealDamageToEachNonDragon n subtype (source := srcEvent?)
    match amount, which with
    | .otherSpellsManaValue, .opponentsControl =>
      g.logMsg s!"deals {n} damage to each opposing creature"
    | _, _ => g
  | .replace what instead =>
    match what, instead with
    | .diesThisTurn, .exile =>
      g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
        let g := g.createEffect (.exileIfDiesUntilEot o.id)
        g.logMsg s!"If {g.name o} would die this turn, exile it instead")
  | .addRedPerOppArtifacts ty =>
    let n := g.battlefield.filter (fun o =>
      g.hasType o ty && !g.controlledBy o controller) |>.size
    let g := g.addMana controller (.colored .red) n (source := sourceId)
    g.logMsg s!"{(g.player controller).name} adds {n} red mana"
  | .chooseTypeReturnOthers =>
    let types := g.battlefieldCreatureTypes
    if types.isEmpty then
      g.logMsg s!"{(g.player controller).name} has no creature type to choose"
    else
      g.beginFraChoice controller (.palisadeCreatureType types)
        s!"{(g.player controller).name} chooses a creature type"
  | .drawEqualToughnessThenPutCreatures =>
    let greatest :=
      (g.permanentsOf controller).foldl (fun acc o =>
        if g.isCreature o then max acc (g.toughness o).toNat else acc) 0
    let (g, cause?) : Game × Option EventCause :=
      match g.currentResolvingContext? with
      | some (src, ctrl) =>
        let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some controller)) (src.orElse (fun _ => sourceId))
        (g, some c)
      | none => (g, none)
    let g := g.draw controller greatest (cause := cause?)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep 28 controller 0 none none (cause := cause?))
    else
      let creatures :=
        (g.player controller).hand.filter (fun id =>
          (g.findObject? id).any (g.isCreature ·))
      g.offerCardChoice controller creatures creatures.size .creaturesToBattlefield
        s!"{(g.player controller).name} may put any number of creature cards from their hand onto the battlefield"
        (cause := cause?)
  | .millThenPut n which =>
    match which with
    | .oneOf a b =>
      g.millThenChooseForHand controller n
        (fun o => g.hasType o a || g.hasType o b) 1 true (types := #[a, b])
    | .upTo max ty =>
      g.millThenChooseForHand controller n (fun o => g.hasType o ty) max false (types := #[ty])
    | .allOf a b =>
      g.millThenPutFromGy controller n
        (fun o => g.hasType o a || g.hasType o b) (types := #[a, b])
  | .addFourManaDragonSpells n subtype =>
    g.beginFraChoice controller (.addManaColors n (.forSubtype subtype))
      s!"{(g.player controller).name} chooses the colors of {englishNumber n} mana that can be spent only on {subtype} spells"
  | .exileAttackersSearchBasics =>
    g.withLegalKindTarget controller effect.targetKind targets (fun g tgt =>
      match tgt with
      | Target.player pid =>
        let attackers :=
          g.battlefield.filter (fun o => g.isCreature o && o.status.attacking && g.controlledBy o pid)
        if attackers.isEmpty then
          g.logMsg s!"{(g.player pid).name} controls no attacking creatures"
        else
          let startIdx := g.events.size
          let attackerIds := attackers.map (·.id)
          let (g, cause) := g.allocDelayedCause (some controller) sourceId
          let g := g.withBatch (some cause) fun g =>
            g.exilePermanentsLoop attackerIds (logExile := true) (cause := some cause)
          if let .chooseReplacement .. := g.pending then
            g.chainPendingReplacement
              (.finishPostStep 69 pid (n := startIdx) (ids := attackerIds))
          else
            let count := attackerIds.foldl (fun acc id =>
              if g.wasPermanentExiled id startIdx then acc + 1 else acc) 0
            g.offerMaySearchBasics pid count
      | _ => g.logMsg "The target is no longer legal")
  | .exileTopPlayIfYouControlSubtype n subtype =>
    g.exileTopPlayIfYouControlSubtype controller n subtype
  | .exileThenReturnYouControl =>
    let ids := targets.filterMap fun t =>
      match t with
      | .permanent id =>
        match g.findObject? id with
        | some o => if g.controlledBy o controller && o.isOnBattlefield then some id else none
        | none => none
      | _ => none
    let (g, cause) : Game × Option EventCause :=
      if ids.isEmpty then (g, none)
      else
        match g.currentResolvingContext? with
        | some (src, ctrl) =>
          let (g, c) :=
            g.allocDelayedCause (ctrl.orElse (fun _ => some controller))
              (sourceId.orElse (fun _ => src))
          (g, some c)
        | none => (g, none)
    g.flickerPermanents ids
      (logText := "is exiled, then returned to the battlefield")
      (cause := cause)
  | .playersCantCastThisTurn =>
    g.createEffects (g.players.map (fun pl => .cantCastSpellsThisTurn pl.id))
      |>.logMsg "Players can't cast spells this turn"
  | .exileTopXOppPlayForLife =>
    match targets[0]? with
    | some (Target.player pid) =>
      Id.run do
        let (g0, cause?) : Game × Option EventCause :=
          if chosenX == 0 || (g.player pid).library.isEmpty then (g, none)
          else
            let (g, c) := g.allocDelayedCause (some controller) sourceId
            (g, some c)
        let mut g := g0
        for _ in List.range chosenX do
          let pl := g.player pid
          if pl.library.isEmpty then
            g := g.logMsg s!"{pl.name} has no cards in their library to exile"
          else
            let top := pl.library.back!
            let name := (g.object! top).name
            let (g', newId) := g.move top .exile none (cause := cause?)
            g := g'
            g := g.createEffect (.playPermission newId {
              player := controller,
              payLifeEqualManaValue := true })
              (cause := cause?)
            g := g.logMsg s!"{(g.player controller).name} exiles {name}"
        return g
    | _ => g.logMsg "The target is no longer legal"
  | .riddlesInTheDark n =>
    let looked := g.scryLookedIds controller n
    if looked.isEmpty then
      g.logMsg s!"{(g.player controller).name}'s library has no cards to look at"
    else
      let g := g.logLookAtTop controller looked.size looked sourceId
      g.beginFraChoice controller (.riddlesSplit looked)
        s!"{(g.player controller).name} separates {looked.size} cards into a face-up pile and a face-down pile"
  | .supperForSpiders =>
    let ids :=
      g.loggedCreaturesToGraveyard.filter (fun id =>
        match g.findObject? id with
        | some o =>
          o.zone == .graveyard o.owner && o.owner != controller
        | none => false)
    g.supperForSpidersReturn controller ids
  | .eaglesAreComing =>
    let ids :=
      targets.filterMap (fun
        | Target.permanent id => some id
        | _ => none)
    let (g, cause) := g.allocDelayedCause (some controller) sourceId
    g.withBatch (some cause) fun g =>
      Id.run do
        if let .chooseReplacement .. := g.pending then
          return g.chainPendingReplacement
            (.finishPostStep 52 controller (n := 0) (sourceId := sourceId) (ids := ids) (cause := some cause))
        let mut g := g
        let mut count : Nat := 0
        for i in [0:ids.size] do
          let id := ids[i]!
          match g.findObject? id with
          | none => pure ()
          | some o =>
            if o.isOnBattlefield && g.isCreature o && o.owner == controller then
              let name := g.name o
              let owner := o.owner
              let (g', _) := g.move o.id (.hand owner) none (cause := some cause)
              g := g'.logMsg s!"{name} is returned to {(g'.player owner).name}'s hand"
              count := count + 1
              if let .chooseReplacement .. := g.pending then
                let rem := ids.extract (i + 1) ids.size
                return g.chainPendingReplacement
                  (.finishPostStep 52 controller (n := count) (sourceId := sourceId) (ids := rem) (cause := some cause))
        if count > 0 then
          let src := sourceId.bind g.damageSourceById?
          g := g.registerDelayedTrigger { controller, source := src, kind := .eaglesBirds count, cause }
          g := g.logMsg
            s!"At the beginning of the next upkeep, {count} Bird Soldier token(s) will be created"
        return g
  | .lookAtTopLandsGainLife n life =>
    let ids := g.scryLookedIds controller n
    let g := g.logLookAtTop controller ids.size ids sourceId
    let lands := ids.filter (fun id => (g.findObject? id).any (g.isLand ·))
    if lands.isEmpty then
      let g := g.requestShuffle controller (.gainLife controller life)
      g.continueIfShuffled
    else
      g.offerCardChoice controller lands lands.size (.landsTappedGainLife life)
        s!"{(g.player controller).name} may put any number of land cards from among them onto the battlefield tapped"
  | .gainControlOppArtifacts =>
    g.foldPermanentTargets targets (fun g o =>
      if o.isOnBattlefield && g.isArtifact o && !g.controlledBy o controller then
        g.changeControl o controller
      else g)
  | .phaseOutKicker =>
    let cause := g.resolvingOneShotCause controller sourceId
    if kicked then
      match targets[0]? with
      | some (Target.player pid) =>
        g.withBatch cause fun g =>
          (g.permanentsOf pid).foldl (fun acc o =>
            if acc.isCreature o then acc.phaseOut o (cause := cause) else acc) g
      | some (Target.permanent oid) =>
        match g.findObject? oid with
        | some o =>
          let pid := (g.controllerOf o).getD controller
          g.withBatch cause fun g =>
            (g.permanentsOf pid).foldl (fun acc x =>
              if acc.isCreature x then acc.phaseOut x (cause := cause) else acc) g
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "The target is no longer legal"
    else
      match targets[0]? with
      | some (Target.permanent oid) =>
        match g.findObject? oid with
        | some o => g.phaseOut o (cause := cause)
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "The target is no longer legal"
  | .dealDamageToControllerOfTarget n =>
    let src? := (sourceId.bind g.damageSourceById?).orElse (fun _ => g.resolvingMovedDamageSource?)
    match targets[0]? with
    | some (Target.permanent id) =>
      let pid? :=
        match g.findObject? id with
        | some o =>
          if o.isOnBattlefield then g.controllerOf o
          else (g.lastKnownBefore? id).bind (fun eo => eo.controller.orElse (fun _ => some eo.owner))
        | none =>
          (g.lastKnownBefore? id).bind (fun eo => eo.controller.orElse (fun _ => some eo.owner))
      match pid? with
      | some pid => g.dealDamageToPlayer pid n (source := src?)
      | none => g
    | _ => g
  | .exileCreatureMvAtMostOrAnyIfTeamwork n life =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let teamwork := g.resolvingTeamworkPaid
      if o.isOnBattlefield && g.isCreature o &&
          (teamwork || (g.copiableValues o).manaValue ≤ n) then
        let (g, cause?) : Game × Option EventCause :=
          match g.currentResolvingContext? with
          | some (src, ctrl) =>
            let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some controller)) src
            (g, some c)
          | none => (g, none)
        let (g, _) := g.move o.id .exile none (cause := cause?)
        if teamwork then g.gainLife controller life (cause := cause?) else g
      else g.logMsg "The target is no longer legal")
      none (some "The target is no longer legal")
  | .returnGyCreatureMvAtMostOrAny n =>
    match targets[0]? with
    | some (Target.card id) =>
      match g.findObject? id with
      | some o =>
        let teamwork := g.resolvingTeamworkPaid
        if o.zone == Zone.graveyard controller && g.isCreature o &&
            (teamwork || g.objectManaValue o ≤ n) then
          let (g, newId) := g.putOntoBattlefield id controller
          if let .chooseReplacement .. := g.pending then
            g.chainPendingReplacement (.finishPostStep 20 controller 0 none (some id) (shuffle := false))
          else
            g.afterPermanentEnters (g.object! newId)
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | .revealTopPutCreatures n =>
    let top := g.scryLookedIds controller n
    let g :=
      if top.isEmpty then g
      else g.record (GameEvent.revealed g.turnNumber controller top
        (cause := some (g.resolvingOrRuleCause controller sourceId)))
    let g :=
      top.foldl (fun g id =>
        match g.findObject? id with
        | some o => g.logMsg s!"{(g.player controller).name} reveals {o.name}"
        | none => g) g
    let creatures :=
      top.filter (fun id => (g.findObject? id).any (g.isCreature ·))
    if creatures.isEmpty then
      g.finishRevealPutCreatures controller top #[]
    else
      g.beginFraChoice controller
        (.revealPutCreatures top creatures g.resolvingTeamworkPaid)
        s!"{(g.player controller).name} may put creature cards from among them onto the battlefield"
  | .createTokens kind amount tapped _ who _ =>
    let pid := match who with
      | .you => controller
      | .player =>
        match targets[0]? with
        | some (Target.player p) => p
        | _ => controller
      | _ => controller
    let count := match amount with
      | .fixed n => n.toNat
      | .chosenX => chosenX
      | .perSubtype subtype => g.countSubtype pid subtype
      | _ => 0
    g.createKindTokens pid kind count (tapped := tapped)
  | .returnOneOrTwoNonlands =>
    g.withBatch none fun g =>
      targets.foldl (fun g t =>
        match t with
        | Target.permanent oid =>
          match g.findObject? oid with
          | some o =>
            if o.isOnBattlefield && !g.isLand o then
              g.returnToHand o.id o.owner
            else
              g.logMsg "The target is no longer legal"
          | none => g.logMsg "The target is no longer legal"
        | _ => g.logMsg "The target is no longer legal") g
  | .targetPlayerInvestigates =>
    match targets.findSome? (fun t =>
        match t with
        | Target.player pid => some pid
        | _ => none) with
    | some pid =>
      if (g.player pid).lost then g.logMsg "The target is no longer legal"
      else (g.createToken pid clueToken).1
    | none => g.logMsg "The target is no longer legal"
  | .onCreatureAmongTargets action =>
    match targets.findSome? (fun t =>
        match t with
        | Target.permanent id => some id
        | _ => none) with
    | none => g.logMsg "The target is no longer legal"
    | some id =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield && g.isCreature o then
          g.applyPermanentAction o action (sourceId := g.resolvingDamageSource?.map (·.id))
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
  | .returnGySubtypeToHand subtype =>
    match targets[0]? with
    | some (Target.card id) =>
      match g.findObject? id with
      | some o =>
        if o.zone == Zone.graveyard controller && g.hasSubtype o subtype then
          g.returnToHand o.id o.owner
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | .becomeArtifactCreature44Flying p t kw =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      g.setUntilEotForm o (p, t) ((Keywords.ofName? kw).getD Keywords.none)
        s!"{g.name o} becomes a {p}/{t} artifact creature with {kw} until end of turn"
        (additionalCreature := true) (additionalArtifact := true))
  | .discardTwoUnlessArtifact n ty =>
    let g := g.changes #[.thirstDiscardsLeft n, .thirstDiscardType ty]
    g.beginDiscardCards #[controller]
  | .loseLife (.fixed n) .eachOpponent =>
    g.loseLifeEachOpponent controller n.toNat
  | .plusOneOnEachYouControl n which =>
    let exclude :=
      match which with
      | .each => none
      | .eachOther =>
        match targets[0]? with
        | some (Target.permanent oid) => some oid
        | _ => none
    g.forEachControlledCreature controller
      (fun g o => g.addPlusOnePlusOneTo o n) exclude
  | .plusOneOnCreatureN n =>
    g.withLegalKindPermanent controller .creatureYouControl targets
      (fun g o => g.addPlusOnePlusOneTo o n)
  | .exileTopPlayUntilNext n =>
    g.exileTopPlayThisTurn controller n
  | .destroyUpToOneNonland =>
    g.withLegalKindPermanent controller .nonland targets
      (fun g o => g.destroyPermanent o) none none
  | .createGalactus =>
    g.createNamedToken controller galactusToken
  | .worldsWithinWorlds =>
    g.applyWorldsWithinWorlds controller none
  | .exileHandDrawPlayUntilNext =>
    g.exileHandDrawPlayUntilNext controller
  | .copyNontokenCreaturesYouControl =>
    g.copyNontokenCreaturesYouControl controller
  | .gainControlUntilEotOrNextIfVillain =>
    g.applyEvilsThrall controller targets
  | .millThenPutPermanentGainLife n life =>
    g.millMayPutPermanentGainLife controller n life
  | .searchLibraryOrGyArtifactCreatureX =>
    g.beginVisionQuest controller chosenX
  | .gainLifeSearchBasicPlusOne life =>
    g.applyGainLifeSearchBasicPlusOne controller targets life
  | .nextFreeRGCreature =>
    g.createEffect (.pendingFreeRGCreatureThisTurn controller)
      |>.logMsg "The next red or green creature spell you cast this turn can be cast without paying its mana cost"
  | .ownerPutsLibraryThenConnive =>
    let connive :=
      match targets[1]? with
      | some (Target.permanent id) => some id
      | _ => none
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield && g.isCreature o && !g.controlledBy o controller then
          g.change (.pending (.fraChoice o.owner (.tricksterLibrary controller id connive)))
            |>.logMsg s!"{(g.player o.owner).name} puts {g.name o} second from the top or on the bottom of their library"
        else
          let g := g.logMsg "The target is no longer legal"
          g.conniveTricksterTarget controller connive
      | none =>
        g.conniveTricksterTarget controller connive
    | _ =>
      g.conniveTricksterTarget controller connive
  | .copyThisSpellXTimesThenDamage n =>
    g.applyDamageToKindTarget controller .creature targets n sourceId
  | .mayDrawPerArtifactOppsDraw ty =>
    g.mayDrawPerArtifact controller ty
  | .mayPutHeroMvOrDraw n subtype =>
    g.mayPutHeroOrDraw controller n subtype
  | .maySacArtifactOrDiscardDraw cards =>
    g.change (.pending (.maySacArtifactOrDiscard controller cards))
      |>.logMsg s!"{(g.player controller).name} may sacrifice an artifact or discard a card. If they do, they draw {cards}"
  | .returnUpToTwoGyModal =>
    g.returnChosenGraveyardCards controller targets
  | .spellsCostLessThisTurn which n =>
    match which with
    | .cardType ty => g.grantTypeCostLessThisTurn controller ty n
    | .supertype s => g.grantSupertypeCostLessThisTurn controller s n
  | _ =>
    -- Shared steps (`draw`, `loseLife`, `surveil`, …) resolve on `Resolution`
    -- before this match. A leftover spell shape does nothing here.
    g.logMsg "The effect does nothing"
end

/-- Resolve a stashed `unlessPays` effect after its payer left without paying
(CR 800.4f). -/
partial def flushUnlessPays (g : Game) : Game :=
  if !g.unlessPaysDue || g.over then g
  else
    match g.unlessPaysInstead with
    | none => g.change (.unlessPaysDue false)
    | some effect =>
      let controller := g.unlessPaysController
      let targets := g.unlessPaysTargets
      let g := g.clearUnlessPays
      let g := g.applyUnified controller effect targets
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.receivePriority g.activePlayer)
      else if g.pending != .none || g.over then g
      else g.receivePriority g.activePlayer

/-- Resolve a printed spell effect (CR 608). -/
def applyEffect (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) : Game :=
  g.withContinuationFrame fun g =>
    g.applyUnified controller effect targets
      (castFromGraveyard := castFromGraveyard) (kicked := kicked)
      (giftPromised := giftPromised) (chosenX := chosenX)
      (sourceId := sourceId)

/-- Apply `action` if `sourceId` is still on the battlefield. -/
def applyOnSource (g : Game) (sourceId : Option ObjectId) (action : PermanentAction)
    (missing := "The ability's source is no longer in play") : Game :=
  g.withSourceOnBattlefield sourceId (fun g o => g.applyPermanentAction o action (sourceId := sourceId)) missing

/-- Return a graveyard source to the battlefield tapped or to its owner's hand. -/
def returnSourceFromGraveyard (g : Game) (sourceId : Option ObjectId)
    (controller : PlayerId) (tapped := false) (toHand := false) : Game :=
  match sourceId.bind g.findObject? with
  | none => g.logMsg "The ability's source is no longer in the graveyard"
  | some o =>
    if o.zone != .graveyard o.owner then
      g.logMsg s!"{o.name} is no longer in the graveyard"
    else if toHand then
      g.returnToHand o.id o.owner
    else
      let name := o.name
      let (g, newId) := g.putOntoBattlefield o.id controller (tapped := tapped)
      let g := g.logMsg
        (if tapped then s!"{name} returns to the battlefield tapped"
         else s!"{name} returns to the battlefield")
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep 20 controller 0 none (some o.id) (shuffle := false))
      else
        g.afterPermanentEnters (g.object! newId)

/-- True when `o` has the looked-at type, including an Equipment artifact (CR 205.3 / 702.73a). -/
def cardHasLookType (g : Game) (o : GameObject) (t : CardSubtype) : Bool :=
  g.hasSubtype o t || (t == .equipment && g.isEquipment o)

/-- Put `ids` on the bottom. One card needs no order. Two or more are ordered
by the player, first card on the bottom. -/
def offerBottomAnyOrder (g : Game) (p : PlayerId) (ids : Array ObjectId)
    (cause : Option EventCause := none) : Game :=
  if ids.size ≤ 1 then
    (g.moveIdsInOrder ids (.library p) (cause := cause)).logMsg
      s!"{(g.player p).name} puts the rest on the bottom of their library"
  else
    let g :=
      match cause with
      | some c => g.change (.stashedCause (some c))
      | none => g
    g.beginFraChoice p (.orderLibraryBottom ids)
      s!"{(g.player p).name} puts the rest on the bottom of their library in any order"

/-- Look at the top `n` cards. You may reveal one matching card to your hand. -/
def beginLookRevealToHand (g : Game) (p : PlayerId) (n : Nat)
    (ok : GameObject → Bool) (anyOrder : Bool) : Game :=
  let looked := g.scryLookedIds p n
  let g := g.logLookAtTop p looked.size looked
  if looked.isEmpty then g
  else
    let eligible := looked.filter (fun id => (g.findObject? id).any ok)
    if eligible.isEmpty then
      if anyOrder then g.offerBottomAnyOrder p looked
      else g.putRestOnBottomRandom p looked
    else
      g.beginFraChoice p (.mayRevealToHand looked eligible anyOrder)
        s!"{(g.player p).name} may reveal a card from among them and put it into their hand"

/-- Look at the top `n` cards. You may put one card of `types` onto the
battlefield (Nick Fury). -/
def beginLookPutTypes (g : Game) (p : PlayerId) (n : Nat) (types : Array CardSubtype) : Game :=
  let looked := g.scryLookedIds p n
  let g := g.logLookAtTop p looked.size looked
  if looked.isEmpty then g
  else
    let eligible := looked.filter (fun id =>
      (g.findObject? id).any (fun o => types.any (g.cardHasLookType o)))
    if eligible.isEmpty then g.putRestOnBottomRandom p looked
    else
      g.beginFraChoice p (.nickFuryPut looked eligible)
        s!"{(g.player p).name} may put a card from among them onto the battlefield"

/-- Resolve Arwen, Mortal Queen's activated ability. An illegal target means
no counters are put on Arwen or the target (ruling 189). -/
def resolveArwenShare (g : Game) (arwenId : ObjectId) (targetId : Option ObjectId) : Game :=
  match targetId.bind g.findObject? with
  | none =>
    g.logMsg "The target is no longer legal. The ability does nothing."
  | some o =>
    if !o.isOnBattlefield || !g.isCreature o || o.id == arwenId then
      g.logMsg "The target is no longer legal. The ability does nothing."
    else
      let putCounters (g : Game) (oid : ObjectId) : Game :=
        match g.findObject? oid with
        | none => g
        | some x =>
          let g := g.addPlusOnePlusOneTo x 1
          g.addLifelinkCounter (g.object! x.id)
      let g := g.createEffect (.keywordsUntilEot o.id Keyword.indestructible)
      let g := g.logMsg s!"{g.name o} gains indestructible until end of turn"
      g.withBatch none fun g =>
        let g := putCounters g o.id
        putCounters g arwenId

/-- Put the +1/+1 counter that waited for each opponent's discard. -/
def finishPlusOneAfterDiscards (g : Game) : Game :=
  match g.plusOneAfterDiscards with
  | none => g
  | some id =>
    let g := g.change (.plusOneAfterDiscards none)
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield then g.addPlusOnePlusOneTo o 1 else g
    | none => g

/-- Transform the source permanent on the battlefield (CR 701.27a). When `cause`
is supplied, `PermanentEvent.transformed` uses that cause; otherwise a fresh
`.oneShotEffect` cause is allocated when resolving. -/
def transformPermanent (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (cause : Option EventCause := none) : Game :=
  g.withSourceOnBattlefield sourceId fun g o =>
    if g.cantTransform o then
      g.logMsg s!"{g.name o} can't transform (entered back face up at night)"
    else
      match (g.baseCard o).otherFace with
      | none => g.logMsg s!"{g.name o} has no other face"
      | some face =>
        let oldName := g.name o
        let batchCause :=
          cause.orElse (fun _ =>
            g.currentResolvingContext?.map fun (s, c) =>
              .oneShotEffect none (s.orElse (fun _ => some o.id)) (c.orElse (fun _ => some controller)))
        g.withBatch batchCause fun g =>
          let fallback := batchCause.getD (.gameRule .spellCast)
          let g := g.record
            (GameEvent.transformed g.turnNumber (g.snapshot o) (!o.status.transformed)
              (cause := fallback))
          g.logMsg s!"{oldName} transforms into {face.name}"

mutual
/-- Execute `steps` sequentially for `applyUnifiedAbility`, pausing on `Pending`
or `afterRandom` and chaining `.continueUnifiedAbility` so later steps run after
the pause. -/
partial def runUnifiedAbilitySteps (g : Game) (controller : PlayerId) (effect : Effect)
    (steps : Array Resolution) (targets : Array Target)
    (sourceId : Option ObjectId) (lastKnownPower : Option Int) (chosenX : Nat) : Game := Id.run do
  let mut g := g
  for i in [0:steps.size] do
    let pendingBefore := g.pending
    let randomBefore := g.afterRandom
    g := g.applyUnifiedAbility controller { effect with resolution := steps[i]! } targets
      sourceId lastKnownPower chosenX
    let rem := steps.extract (i + 1) steps.size
    if !rem.isEmpty then
      let opened :=
        (g.pending != pendingBefore && g.pending != .none) ||
          (g.afterRandom != randomBefore && g.afterRandom != .none)
      if opened then
        return g.chainPendingReplacement
          (.continueUnifiedAbility controller effect rem targets
            sourceId lastKnownPower chosenX)
  return g

/-- Resolve a unified activated-ability `Effect` (CR 608). -/
partial def applyUnifiedAbility (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (sourceId : Option ObjectId := none)
    (lastKnownPower : Option Int := none) (chosenX : Nat := 0) : Game :=
  if g.continuations.isEmpty then
    g.withContinuationFrame fun g =>
      g.applyUnifiedAbility controller effect targets sourceId lastKnownPower chosenX
  else
  match g.applyFraResolution? controller effect targets sourceId (lastKnownPower := lastKnownPower) with
  | some g => g
  | none =>
  match effect.resolution with
  | .sequence rs =>
    match rs.flatMap Resolution.flatten with
    | [.onPermanent .tap, .scry (.fixed scryN), .draw (.fixed drawN)] =>
      g.resolveTapScryDraw controller effect targets scryN.toNat drawN.toNat sourceId
        (fizzle := fun g => g.logIllegalSequenceTargets targets)
    | steps =>
      if g.sequenceAllTargetsIllegal controller effect targets sourceId then
        g.logIllegalSequenceTargets targets
      else
        match steps with
        | [.shuffleSource, .draw (.fixed n)] =>
          g.shuffleSourceIntoLibrary sourceId (.draw controller n.toNat)
        | steps =>
          g.runUnifiedAbilitySteps controller effect steps.toArray targets
            sourceId lastKnownPower chosenX
  | .shuffleSource =>
    g.shuffleSourceIntoLibrary sourceId
  | .amass (.fixed n) .goblin false .you => g.amassGoblins controller n.toNat
  | .discard (.cards n) =>
    g.beginDiscardCards #[controller] n
  | .mill (.fixed n) .player _ =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.mill pid n.toNat)
  | .connive .source =>
    g.applyConnive controller sourceId
  | .attach .source .target =>
    g.withLegalKindPermanent controller effect.targetKind targets fun g host =>
      g.withSourceOnBattlefield sourceId (fun g src =>
        if src.attachedTo == some host.id then
          g.logMsg s!"{g.name src} is already attached to {g.name host}"
        else
          g.attachSourceTo src host)
        "The Equipment is no longer in play"
  | .onPermanent action =>
    g.applyOnPermanent controller effect.targetKind targets action sourceId
  | .exile (.target .eachPermanent) .untilSourceLeaves _ =>
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
  | r =>
    match Resolution.toSpell r with
    | some _ =>
      g.applyUnified controller { effect with resolution := r } targets
        (chosenX := chosenX) (sourceId := sourceId)
    | none =>
      match r with
      | .searchBasicLand => g.resolveSearchBasicLandTapped controller
      | .searchLandTypeToHand t =>
        match CardSubtype.ofOracle? t with
        | some st => g.resolveSearchLandTypeToHand controller st
        | none => g.resolveLibrarySearchToHand controller (fun _ => false) s!"{t} card"
      | .exileTop => g.resolveExileTopPlayUntilEndOfNextTurn controller
      | .onSource action =>
        g.applyOnSource sourceId action
      | .becomeSubtypeWithLandsPT subtype =>
        g.withSourceOnBattlefield sourceId fun g o =>
          let g := g.createEffect (.additionalCreature o.id false)
          let g :=
            if g.hasSubtype o subtype then g
            else g.createEffect (.additionalSubtype o.id subtype)
          let g :=
            if g.hasLandsYouControlPT o then g
            else g.createEffect (.grantedStatic o.id .powerToughnessEqualLandsYouControl)
          g.logMsg
            s!"{g.name o} becomes {indefinite subtype.englishName} {subtype} creature. Its power and toughness are each equal to the number of lands you control"
      | .returnFromGraveyardTapped =>
        g.returnSourceFromGraveyard sourceId controller (tapped := true)
      | .returnFromGraveyardToHand =>
        g.returnSourceFromGraveyard sourceId controller (toHand := true)
      | .creaturesYouControlPump pw tw =>
        g.pumpControlledCreatures controller pw tw
      | .addAnyColor =>
        let g := g.addMana controller (.colored .white) 1 (source := sourceId)
        g.logMsg s!"{(g.player controller).name} adds one mana of any color"
      | .returnFromGyAttach =>
        match sourceId.bind g.findObject? with
        | none => g.logMsg "The source is no longer in the graveyard"
        | some src =>
          g.withLegalKindPermanent controller effect.targetKind targets (fun g host =>
            let (g, newId) := g.putOntoBattlefield src.id controller
              (attachedTo := some host.id)
            if let .chooseReplacement .. := g.pending then
              g.chainPendingReplacement (.finishPostStep 29 controller 0 (some host.id) (some src.id))
            else
              let o := g.object! newId
              let g := g.logMsg s!"{g.name o} enters the battlefield attached to {g.name host}"
              g.afterPermanentEnters (g.object! newId))
            sourceId (some "The target is no longer legal. Eagle's Rescue remains in the graveyard.")
      | .searchBasicLandToHand =>
        g.resolveSearchBasicLandToHand controller
      | .createTokensX kind =>
        g.createKindTokens controller kind chosenX
      | .searchTwoBasicsSplit =>
        g.beginLibrarySearch controller isBasicLandCard "a basic land card"
          .battlefieldTappedThenHand (count := 2)
      | .subtypesGainMenace subtypes =>
        g.grantUntilEotToControlledCreatures controller Keyword.menace "menace"
          (fun g o => subtypes.any (fun s => g.hasSubtype o s))
      | .exileThenReturnNextEnd =>
        let (g, cause) := g.allocDelayedCause (some controller) sourceId
        let src := sourceId.bind g.findObject?
        g.withBatch (some cause) fun g =>
          g.foldPermanentTargets targets (fun g o =>
            if o.isOnBattlefield && g.controlledBy o controller && !g.isLand o &&
                some o.id != sourceId then
              let name := g.name o
              let isNontoken := !o.printed.isToken || o.isCopy
              let (g, newId) := g.move o.id .exile none (cause := some cause)
              let g :=
                if isNontoken then
                  g.registerDelayedTrigger
                    { controller, source := src.orElse (fun _ => some o), kind := .endStepReturn newId, cause }
                else g
              g.logMsg s!"{name} is exiled until the beginning of the next end step"
            else g.logMsg "The target is no longer legal")
      | .searchBasicBeholdSubtypeUntap subtype =>
        g.beginLibrarySearch controller isBasicLandCard "a basic land card"
          (.battlefieldTappedBeholdUntap subtype)
      | .twoPlayersDraw =>
        match targets[0]?, targets[1]? with
        | some (Target.player a), some (Target.player b) =>
          if a == b then g.logMsg "Two target players must be different"
          else
            let (g, cause?) : Game × Option EventCause :=
              match g.currentResolvingContext? with
              | some (src, ctrl) =>
                let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some controller)) (src.orElse (fun _ => sourceId))
                (g, some c)
              | none => (g, none)
            g.draw a 1 (cause := cause?) |>.draw b 1 (cause := cause?)
        | _, _ => g.logMsg "The targets are no longer legal"
      | .discardLegendarySameNameDraw =>
        g.draw controller 2
      | .dealDamageToAny n =>
        g.applyEffect controller (Effect.dealDamage n) targets (sourceId := sourceId)
      | .drawEqualToLastKnownPower =>
        g.draw controller ((lastKnownPower.getD 0).toNat)
      | .arwenShare =>
        match sourceId, targets[0]? with
        | some sid, some (Target.permanent tid) => g.resolveArwenShare sid (some tid)
        | some sid, _ => g.resolveArwenShare sid none
        | _, _ => g.logMsg "The ability's source is no longer in play"
      | .grantCombatDamageCreateTreasure =>
        g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
          let g := g.createEffect (.combatDamageCreatesTreasureUntilEot o.id)
          g.logMsg
            s!"{g.name o} gains \"Whenever this creature deals combat damage to a player, create a Treasure token\"")
          sourceId (some "The target is no longer legal")
      | .putShadowCounter =>
        g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
          g.putShadowCounter o) sourceId (some "The target is no longer legal")
      | .damageEachOpponent n =>
        let src? := sourceId.bind g.damageSourceById?
        g.dealDamageToEachOpponent controller n (source := src?)
      | .chooseTwoDestroyRest =>
        let creatures := (g.battlefield.filter (g.isCreature ·)).map (·.id)
        g.offerCardChoice controller creatures 2 .keepDestroyRest
          s!"{(g.player controller).name} chooses up to two creatures to keep"
      | .blackGateUnblockable =>
        match targets[0]? with
        | some (Target.permanent oid) =>
          match g.findObject? oid with
          | some o =>
            if o.isOnBattlefield && g.isCreature o then
              let tied := g.playersWithMostLife
              match tied.toList with
              | [] => g
              | [pid] => g.applyBlackGateUnblockable oid pid
              | _ =>
                g.beginFraChoice controller (.blackGatePlayer oid tied)
                  s!"{(g.player controller).name} chooses a player with the most life"
            else g.logMsg "The target is no longer legal"
          | none => g.logMsg "The target is no longer legal"
        | _ => g.logMsg "The target is no longer legal"
      | .plusOneOnEachOtherSubtype subtype n =>
        g.withBatch none fun g =>
          g.foldBattlefield (fun o =>
              g.controlledBy o controller && some o.id != sourceId && g.hasSubtype o subtype)
            (fun g o => g.addPlusOnePlusOneTo o n)
      | .plusOneX =>
        g.withSourceOnBattlefield sourceId fun g o =>
          g.addPlusOnePlusOneTo o chosenX
      | .eachOppDiscardThenPlusOne =>
        let opps := (g.livingOpponents controller).map (·.id)
        let g := g.change (.plusOneAfterDiscards sourceId)
        let g := g.beginDiscardCards opps
        if g.pending == .none then
          (g.finishPlusOneAfterDiscards).receivePriority g.activePlayer
        else g
      | .lookAtTopPutTypes n types =>
        g.beginLookPutTypes controller n types
      | .transform =>
        g.transformPermanent controller sourceId
      | .drawX =>
        g.draw controller chosenX
      | .lookAtTopRevealArtifact n =>
        g.beginLookRevealToHand controller n (fun o => g.isArtifact o) false
      | .addAnyColorSpendOnlySubtype subtype =>
        match subtype with
        | .hero =>
          g.addMana controller (.colored .white) 1 (source := sourceId) (restriction := some .hero)
        | .villain =>
          g.addMana controller (.colored .black) 1 (source := sourceId) (restriction := some .villain)
        | _ =>
          g.addMana controller (.colored .white) 1 (source := sourceId)
      | .addAnyColorSpendOnlyArtifactSpell =>
        g.addMana controller (.colored .white) 1 (source := sourceId)
      | .addTwoAnyColorCreatureSources =>
        g.addMana controller (.colored .green) 2 (source := sourceId) (restriction := some .creatureSource)
      | .addBlueCantNonartifact =>
        g.addMana controller (.colored .blue) 1 (source := sourceId) (restriction := some .cantNonartifact)
      | .addAnyColorEqualToSourcePower =>
        let x :=
          match sourceId.bind g.findObject? with
          | some o => (g.power o).toNat
          | none => 0
        g.addMana controller (.colored .green) x (source := sourceId)
      | .addFourAnyCombination =>
        g.addMana controller (.colored .white) 4 (source := sourceId)
      | .addTwoAnyColorEquipment =>
        g.addMana controller (.colored .white) 2 (source := sourceId)
      | .drawPerDiscardedThisTurn =>
        g.draw controller (g.loggedDiscards controller)
      | .createTokensEqualRemovedPlusOnes kind =>
        g.createKindTokens controller kind chosenX
      | .exileTopXPlayThisTurn =>
        let x := g.sourcePowerNatAtResolution sourceId lastKnownPower
        g.exileTopPlayThisTurn controller x
      | .targetPlayerDraw n =>
        g.withLegalKindPlayer controller effect.targetKind targets
          (fun g pid => g.draw pid n)
      | .copyControlledAbility _ =>
        match targets[0]? with
        | some (Target.card id) | some (Target.permanent id) =>
          match g.findObject? id with
          | some o =>
            if o.zone == .stack && (o.abilityEffect.isSome || o.triggeredAbility.isSome) then
              let g := g.copyStackAbility o controller
              let copyId := (g.stack.back?.map (·.objectId)).getD o.id
              let hasTargets :=
                match g.stack.find? (fun e => e.objectId == copyId) with
                | some e => !e.targets.isEmpty
                | none => false
              if hasTargets then
                g.change (.pending (.fraChoice controller (.newTargetsForCopies #[copyId])))
                  |>.logMsg s!"{(g.player controller).name} may choose new targets for the copy"
              else g
            else g.logMsg "The target is no longer legal"
          | none => g.logMsg "The target is no longer legal"
        | _ => g
      | .createTokensEqualSubtype kind subtype =>
        let n := g.countSubtype controller subtype
        g.createKindTokens controller kind n
      | .proliferateEachKind =>
        g.proliferateTarget controller targets
      | .equipmentBecomesConstructHero =>
        match sourceId.bind g.findObject? with
        | some o =>
          if !o.isOnBattlefield then
            g.logMsg "The Equipment is no longer in play"
          else if g.isCreature o then
            g.logMsg s!"{g.name o} is already a creature"
          else
            let g :=
              match o.attachedTo with
              | some hostId =>
                let unattCause := g.resolveOptionalCause none (fallbackSrc := sourceId) (fallbackCtrl := some controller)
                g.record (GameEvent.unattached g.turnNumber (g.snapshot o) hostId (cause := unattCause))
                  |>.logMsg s!"{g.name o} becomes unattached"
              | none => g
            let o := g.object! o.id
            g.setUntilEotForm o (0, 0) Keyword.flying
              s!"{g.name o} becomes a 0/0 Construct Hero artifact creature"
              (types := some #[.construct, .hero])
              (additionalCreature := true) (additionalArtifact := true)
              (pumpPerArtifact := true)
        | none => g.logMsg "The Equipment is no longer in play"
      | .lookAtTopRevealSubtype n subtype =>
        g.beginLookRevealToHand controller n (fun o => g.hasSubtype o subtype) true
      | .millThenPutSubtypeOrEnchantment n subtype =>
        g.millMayPutSubtypeOrEnchantment controller n subtype
      | .returnFromGyFinalityAttach =>
        g.returnFromGyFinalityAttach controller sourceId
      | .revealTopDrawIfArtifact =>
        g.revealTopDrawIfArtifact controller
      | .copyArtifactYouControlNotLegendary =>
        match targets[0]?, targets[1]? with
        | some (Target.permanent a), some (Target.permanent b) =>
          match g.findObject? a, g.findObject? b with
          | some dest, some src =>
            if dest.isOnBattlefield && src.isOnBattlefield &&
                g.controlledBy dest controller && g.controlledBy src controller &&
                g.isArtifact dest && g.isArtifact src then
              g.becomeCopyOf dest src (untilEot := true) (removeSupertypes := #[.legendary])
            else
              g.logMsg "The target is no longer legal. The ability has no effect."
          | _, _ =>
            g.logMsg "The target is no longer legal. The ability has no effect."
        | _, _ =>
          g.logMsg "The target is no longer legal. The ability has no effect."
      | .becomeTypes types p t k =>
        let typeNames := types.map CardSubtype.englishName
        let typeWords := String.intercalate " " typeNames.toList
        g.withSourceOnBattlefield sourceId (fun g o =>
          g.setUntilEotForm o (p, t) k
            s!"{g.name o} becomes a {p}/{t} {typeWords}"
            (types := some types))
          "The source is no longer in play"
      | .nextInstantSorceryCopyIfMvAtMostSourcePower =>
        let pw := g.sourcePowerAtResolution sourceId lastKnownPower
        let (g, cause) := g.allocDelayedCause (some controller) sourceId
        let src := sourceId.bind g.damageSourceById?
        g.registerDelayedTrigger {
          controller
          source := src
          kind := .lokiCopyNextInstantSorceryThisTurn sourceId pw
          cause
        }
          |>.logMsg s!"The next instant or sorcery with mana value {pw} or less will be copied"
      | .harnessInfinityStone =>
        g.withSourceOnBattlefield sourceId (fun g o =>
          let effCause := g.resolveOptionalCause none (fallbackSrc := sourceId) (fallbackCtrl := some controller)
          let g := g.record (GameEvent.designation g.turnNumber (g.snapshot o) .harnessed true (cause := effCause))
          g.logMsg s!"{g.name o} is harnessed") "The source is no longer in play"
      | .targetSubtypeConnives _ =>
        match targets[0]? with
        | some (Target.permanent id) => g.applyConnive controller (some id)
        | _ => g.applyConnive controller none
      | _ => g
end

/-- Resolve a printed activated ability (CR 608). -/
def applyAbilityEffect (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (sourceId : Option ObjectId := none)
    (lastKnownPower : Option Int := none) (chosenX : Nat := 0) : Game :=
  g.applyUnifiedAbility controller effect targets
    sourceId lastKnownPower chosenX

end Game
end Mtg.Engine
