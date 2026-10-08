import Mtg.Engine.Game.FraResolve

/-!
# Unified effect resolution (CR 608)

`applyUnified` and `applyUnifiedAbility`: the interpreters for the
unified `Effect` vocabulary shared by spells, activated abilities, and
triggered abilities.
-/

namespace Mtg.Engine
namespace Game

/-- Move the source into its owner's library and shuffle (CR 701.19).
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
    g.requestShuffle owner after |>.continueIfShuffled

/-- Damage beyond lethal damage dealt to `o` by `dealt` damage (CR 120.4a):
beyond its toughness minus damage already marked for a creature, beyond its
loyalty for a planeswalker (ruling 790), and beyond the greater of the two
when it is both. -/
def excessDamage (g : Game) (o : GameObject) (dealt : Nat) : Nat :=
  let creatureLethal :=
    if o.isCreature then (g.toughness o - o.status.damage).toNat else 0
  let loyalty := if o.printed.isPlaneswalker then o.status.loyaltyCounters else 0
  dealt - Nat.max creatureLethal loyalty

/-- `pid` sacrifices a creature or planeswalker with the greatest mana value
among creatures and planeswalkers they control, as one group (rulings
771–773). With a tie, the most recent of them is sacrificed. -/
def sacrificeGreatestManaValue (g : Game) (pid : PlayerId) : Game :=
  let candidates := (g.permanentsOf pid).filter (fun o =>
    o.isCreature || o.printed.isPlaneswalker)
  let best := candidates.foldl (fun best o =>
    match best with
    | none => some o
    | some b =>
      let mo := g.objectManaValue o
      let mb := g.objectManaValue b
      if mo > mb || (mo == mb && o.timestamp ≥ b.timestamp) then some o else best) none
  match best with
  | none => g.logMsg s!"{(g.player pid).name} has no creature or planeswalker to sacrifice"
  | some o => g.sacrificeToGraveyard o s!"{(g.player pid).name} sacrifices {o.name}"

/-- Resolutions added for Reality Fracture, shared by spells and activated
abilities. `none` for every other resolution. -/
def applyFraResolution? (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (sourceId : Option ObjectId) : Option Game :=
  match effect.resolution with
  | .empowerJace n => some (g.empowerJace controller n)
  | .surveil n => some (g.beginSurveil controller n)
  | .millSelf n => some (g.mill controller n)
  | .mayDiscardDraw n =>
    let pl := g.player controller
    if pl.hand.isEmpty then some (g.logMsg s!"{pl.name} has no card to discard")
    else
      some ({ g with pending := .mayDiscardDraw controller n }.logMsg
        s!"{pl.name} may discard a card. If they do, they draw {n}")
  | .createTokensLifeGained kind =>
    -- Ruling 755: counts life gained, ignoring life lost this turn.
    some (g.createKindTokens controller kind (g.player controller).lifeGainedThisTurn)
  | .oppSacrificesGreatestMv =>
    some (g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.sacrificeGreatestManaValue pid) sourceId)
  | .createTigerGod => some (g.createNamedToken controller tigerGodToken)
  | .extraTurn =>
    some ({ g with extraTurns := g.extraTurns.push controller }
      |>.logMsg s!"{(g.player controller).name} takes an extra turn after this one. During that turn, power-up abilities can't be activated.")
  | .drawEqualToBurdenCounters =>
    some (g.withSourceOnBattlefield sourceId fun g o => g.draw controller o.status.burden)
  | .creaturesWithoutFlyingCantBlock =>
    some ({ g with creaturesWithoutFlyingCantBlock := true }
      |>.logMsg "Creatures without flying can't block this turn")
  | .targetPlayerLoseLife n =>
    some (g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.loseLife pid n))
  | .controllerOfTargetLosesLife n =>
    some (match targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? (g.followMoved id) with
        | some o =>
          let pid? :=
            if o.zone == .battlefield then o.controller
            else o.lastController.orElse (fun _ => o.controller)
          match pid? with
          | some pid => g.loseLife pid n
          | none => g
        | none => g
      | _ => g)
  | .returnTargetSpell =>
    some (match targets[0]? with
      | some (Target.card id) => g.returnStackSpell id
      | _ => g.logMsg "The target is no longer legal")
  | .chooseOddOrEvenDestroy =>
    some ({ g with pending := .fraChoice controller (.oddOrEvenDestroy sourceId) }
      |>.logMsg s!"{(g.player controller).name} chooses odd or even")
  | .eachCreatureYouControlBecomesPrepared =>
    some ((g.permanentsOf controller).foldl (fun g o =>
      if o.isCreature && o.printed.prepareFace.isSome then g.becomePrepared (g.object! o.id)
      else g) g)
  | .damageThenEmpowerExcess n =>
    some (g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let before := o.status.damage
      let g := g.dealDamageToPermanent o n
      let dealt := ((g.object! o.id).status.damage - before).toNat
      let excess := g.excessDamage o dealt
      if excess > 0 then g.empowerJace controller excess
      else g) sourceId (some "The target is no longer legal"))
  | .exileTopMayCastElseDamageOpponents n =>
    match (g.player controller).library.back? with
    | none =>
      some (g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid n))
    | some top =>
      let (g, id) := g.move top .exile none
      let card := g.object! id
      let g := g.logMsg s!"{(g.player controller).name} exiles {card.name}"
      if card.printed.isLand then
        -- Ruling 855: a land can't be cast, so the damage is dealt.
        some (g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid n))
      else
        some ({ g with pending := .mayCastExiledElseDamage controller id n }.logMsg
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
        some (g.dealDamageFrom src.name dst (max n 0) (source := some src))
    | _, _ => some (g.logMsg "The targets are no longer legal")
  | .returnFromGyWithFinality =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.zone == .graveyard o.owner then
        let (g, newId) := g.putOntoBattlefield o.id controller
        let g := g.logMsg s!"{o.name} returns to the battlefield"
        let g := g.addFinalityTo (g.object! newId) 1
        some (g.afterPermanentEnters (g.object! newId))
      else some (g.logMsg s!"{o.name} is no longer in the graveyard")
    | none => some (g.logMsg "The card is no longer in the graveyard")
  | .copyNextInstantSorceryThisTurn =>
    let g := g.modifyPlayer controller (fun pl =>
      { pl with copyNextInstantSorceryThisTurn := pl.copyNextInstantSorceryThisTurn + 1 })
    some (g.logMsg s!"When {(g.player controller).name} next casts an instant or sorcery spell this turn, it is copied")
  | .proliferatePlaneswalkerTypesTimes =>
    -- Ruling 878: X is determined once, as the ability resolves.
    let types := (g.permanentsOf controller).foldl (fun acc o =>
      if o.printed.isPlaneswalker then
        o.subtypes.foldl (fun acc t => if acc.contains t then acc else acc.push t) acc
      else acc) (#[] : Array String)
    if types.isEmpty then
      some (g.logMsg s!"{(g.player controller).name} controls no planeswalker types. X is 0")
    else
      some ({ g with pending := .chooseProliferate controller types.size }.logMsg
        s!"{(g.player controller).name} proliferates {types.size} time(s)")
  | .copyEachCreatureOfTargetPlayer =>
    -- Rulings 784–789: each token copies the creature's copiable values only
    -- (no counters or status). All tokens are created before any of them is
    -- treated as entering, so they see each other enter.
    some (g.withLegalKindPlayer controller effect.targetKind targets (fun g pid =>
      let sacrifice : TriggeredAbility :=
        .triggered .fromEffect (Effect.ofTrigger .sacrificeSourceIfNoPlaneswalker)
      let (g, ids) := (g.creaturesControlledBy pid).foldl
        (fun (acc : Game × Array ObjectId) c =>
          let printed := { c.printed with
            keywords := c.printed.keywords.merge Keyword.haste
            triggeredAbilities := c.printed.triggeredAbilities.push sacrifice }
          let (g, tok) := acc.1.createToken controller printed
          (g, acc.2.push tok.id)) (g, #[])
      ids.foldl (fun g id =>
        match g.findObject? id with
        | some o => g.afterPermanentEnters o
        | none => g) g) sourceId)
  | .becomeCopyLegendRuleOff =>
    some (g.withLegalKindPermanent controller effect.targetKind targets (fun g target =>
      g.withSourceOnBattlefield sourceId (fun g src =>
        -- Rulings 812 / 815 / 816: copy the copiable values (already those
        -- of anything the target copies); the land doesn't enter, keeps its
        -- status, and both effects end together in cleanup (ruling 817).
        let g := g.becomeCopyOf src target (untilEot := true)
        let g := g.modifyPlayer controller (fun pl => { pl with legendRuleOffThisTurn := true })
        g.logMsg s!"The legend rule doesn't apply to permanents {(g.player controller).name} controls this turn")
        "The source is no longer in play") sourceId (some "The target is no longer legal"))
  | .fra r => some (g.applyFra controller effect r targets sourceId)
  | .teamGain k => some (g.grantUntilEotToControlledCreatures controller k k.joinedAnd)
  | .jaceLoyaltyAtInstantSpeed =>
    let g := g.modifyPlayer controller (fun pl => { pl with jaceLoyaltyAtInstantSpeed := true })
    some (g.logMsg s!"Until end of turn, {(g.player controller).name} may activate loyalty abilities of Jace planeswalkers they control any time they could cast an instant")
  | _ => none

/-- Exile every card in `p`'s hand, then draw that many. Those cards may be
played until the end of `p`'s next turn (Hex Magic; ruling 421). -/
def exileHandDrawPlayUntilNext (g : Game) (p : PlayerId) : Game :=
  let ids := (g.player p).hand
  let n := ids.size
  let g := ids.foldl (fun g id =>
    match g.findObject? id with
    | none => g
    | some _ =>
      let (g, newId) := g.move id .exile none
      let o := g.object! newId
      g.setObject { o with
        playPermission := some { player := p, turnEndsRemaining := 2 } }) g
  let g :=
    if n == 0 then g
    else g.logMsg s!"{(g.player p).name} may play the exiled cards until the end of their next turn"
  g.draw p n

/-- A token copy of each nontoken creature `p` controls, except it isn't
legendary (Multiversal Incursion; rulings 468 / 508). -/
def copyNontokenCreaturesYouControl (g : Game) (p : PlayerId) : Game :=
  let ids :=
    ((g.creaturesControlledBy p).filter (fun o => !o.printed.isToken)).map (·.id)
  ids.foldl (fun g id =>
    match g.findObject? id with
    | none => g
    | some src =>
      let blank : CardDef := {
        name := "Copy"
        types := #[.creature]
        power := some 0
        toughness := some 0
        isToken := true }
      let (g, tok) := g.createOneToken p blank
      let g := g.becomeCopyOf (g.object! tok.id) src (notLegendary := true)
      let tok := g.object! tok.id
      g.setObject { tok with printed := { tok.printed with isToken := true } }) g

/-- Gain control of the targeted creature until end of turn, or until the end
of your next turn when you control a Villain with greater mana value. Untap
it and it gains haste until end of turn (Evil's Thrall; ruling 514). -/
def applyEvilsThrall (g : Game) (controller : PlayerId) (targets : Array Target) : Game :=
  g.withLegalKindPermanent controller .creature targets (fun g o =>
    let mv := g.objectManaValue o
    let longer := (g.creaturesControlledBy controller).any (fun v =>
      g.hasSubtype v "Villain" && g.objectManaValue v > mv)
    let g :=
      if longer then
        let g := g.changeControl o controller
        match g.findObject? o.id with
        | some o =>
          g.setObject { o with status := { o.status with controlTurnEndsLeft := 2 } }
        | none => g
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

/-- Mill `n`, then you may put one permanent card from among them into your
hand. `life` is gained either way (Rapid Rescue). -/
def millMayPutPermanentGainLife (g : Game) (p : PlayerId) (n life : Nat) : Game :=
  let lib := (g.player p).library
  let count := min n lib.size
  let tops := lib.extract (lib.size - count) lib.size
  let g := g.mill p n
  let milled := tops.map (fun id => g.followMoved id)
  let permanents := milled.filter (fun id =>
    (g.findObject? id).any (fun o =>
      o.zone == .graveyard p && o.printed.isPermanentCard))
  if permanents.isEmpty then g.gainLife p life
  else
    { g with pending := .fraChoice p (.mayTakeMilled permanents life) }
      |>.logMsg s!"{(g.player p).name} may put a permanent card from among the milled cards into their hand"

/-- Mill `n`. You may put a card of subtype `subtype`, or an enchantment, from
among those cards into your hand (Rick Jones). -/
def millMayPutSubtypeOrEnchantment (g : Game) (p : PlayerId) (n : Nat) (subtype : String) : Game :=
  let lib := (g.player p).library
  let count := min n lib.size
  let tops := lib.extract (lib.size - count) lib.size
  let g := g.mill p n
  let milled := tops.map (fun id => g.followMoved id)
  let eligible := milled.filter (fun id =>
    (g.findObject? id).any (fun o =>
      o.zone == .graveyard p &&
        (g.hasSubtype o subtype || o.printed.isEnchantment)))
  if eligible.isEmpty then
    g.logMsg s!"{(g.player p).name} has no {subtype} or enchantment card among the milled cards"
  else
    { g with pending := .fraChoice p (.mayTakeMilled eligible 0) }
      |>.logMsg s!"{(g.player p).name} may put a {subtype} or enchantment card into their hand"

/-- Target player gains `life`, searches for a basic land tapped, then a
+1/+1 counter goes on the creature target if it is still legal
(Restorative Technique). -/
def applyGainLifeSearchBasicPlusOne (g : Game) (_controller : PlayerId)
    (targets : Array Target) (life : Nat) : Game :=
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
      let g := g.gainLife pid life
      let g :=
        match creature? with
        | none => g
        | some id =>
          match g.findObject? id with
          | some o =>
            if o.isOnBattlefield && o.isCreature then
              { g with plusOneAfterSearch := some id }
            else g.logMsg "The target is no longer legal"
          | none => g.logMsg "The target is no longer legal"
      g.beginLibrarySearch pid isBasicLandCard "a basic land card" (.battlefield true)

/-- You may draw one card for each permanent of type `ty` you control. If you
do, each opponent draws a card (Armor Wars). -/
def mayDrawPerArtifact (g : Game) (p : PlayerId) (ty : CardType := .artifact) : Game :=
  let n := ((g.permanentsOf p).filter (fun o => o.printed.hasType ty)).size
  if n == 0 then
    let what := if ty == .artifact then "artifacts" else ty.pluralName
    g.logMsg s!"{(g.player p).name} controls no {what}, so no cards are drawn"
  else
    { g with pending := .fraChoice p (.mayDrawThenEachOpponentDraws n) }
      |>.logMsg s!"{(g.player p).name} may draw {n}"

/-- You may put a Hero creature card with mana value `maxMv` or less from
your hand onto the battlefield. If you don't, draw a card (Origin of the
Avengers; ruling 507). -/
def mayPutHeroOrDraw (g : Game) (p : PlayerId) (maxMv : Nat)
    (subtype : String := "Hero") : Game :=
  let ids := (g.player p).hand.filter (fun id =>
    (g.findObject? id).any (fun o =>
      o.printed.isCreature && g.hasSubtype o subtype && o.printed.manaValue ≤ maxMv))
  if ids.isEmpty then g.draw p 1
  else
    { g with pending := .fraChoice p (.mayPutHeroFromHandOrDraw ids) }
      |>.logMsg s!"{(g.player p).name} may put {indefinite subtype} {subtype} creature card onto the battlefield"

/-- Spells of type `ty` cost `{n}` less this turn. -/
def grantTypeCostLessThisTurn (g : Game) (p : PlayerId) (ty : CardType) (n : Nat) : Game :=
  g.modifyPlayer p (fun pl =>
    { pl with typeSpellCostLessThisTurn := pl.typeSpellCostLessThisTurn.push (ty, n) })
    |>.logMsg s!"{ty} spells {(g.player p).name} casts this turn cost \{{n}} less"

/-- Spells with supertype `s` cost `{n}` less this turn. -/
def grantSupertypeCostLessThisTurn (g : Game) (p : PlayerId) (s : Supertype) (n : Nat) : Game :=
  g.modifyPlayer p (fun pl =>
    { pl with supertypeSpellCostLessThisTurn :=
        pl.supertypeSpellCostLessThisTurn.push (s, n) })
    |>.logMsg s!"{s} spells {(g.player p).name} casts this turn cost \{{n}} less"

/-- Return up to two graveyard cards, each using a different mode among
artifact, creature, enchantment, and land (Call Damage Control). -/
def returnChosenGraveyardCards (g : Game) (controller : PlayerId)
    (targets : Array Target) : Game :=
  let kinds : Array CardType := #[.artifact, .creature, .enchantment, .land]
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
              !used.contains ty && objectHasCardType o ty)
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
    let g := g.addPlusOnePlusOneTo o 1
    let o := g.object! o.id
    let g := g.mapObjectStatus o (fun s => { s with keywordCounters :=
      { s.keywordCounters with doubleStrike := s.keywordCounters.doubleStrike + 1 } })
    g.logMsg s!"{o.name} gets a double strike counter")
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
    g.withLegalKindPermanent controller .oppCreature targets (fun g tgt =>
      match (sourceId.map g.followMoved).bind g.findObject? with
      | some src =>
        if src.isOnBattlefield && src.isCreature then g.fightCreatures src tgt
        else g.logMsg "The source is no longer in play"
      | none => g.logMsg "The source is no longer in play") sourceId
      (some "The target is no longer legal")

/-- Destroy each creature other than `sourceId` whose mana value is even
(`even := true`) or odd. Zero is even (Thanos). -/
def destroyCreaturesByManaParity (g : Game) (sourceId : Option ObjectId) (even : Bool) : Game :=
  let self := sourceId.map g.followMoved
  let ids := (g.battlefield.filter (·.isCreature)).map (·.id)
  let quality := if even then "even" else "odd"
  let g := g.logMsg s!"Destroy each other creature with {quality} mana value"
  ids.foldl (fun g id =>
    if self == some id then g
    else
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield && o.isCreature &&
            ((g.objectManaValue o % 2 == 0) == even) then
          g.destroyPermanent o
        else g
      | none => g) g

/-- Reveal the top card. Draw it when it is an artifact (Iron Lad). -/
def revealTopDrawIfArtifact (g : Game) (p : PlayerId) : Game :=
  match (g.player p).library.back? with
  | none => g.logMsg s!"{(g.player p).name} has no cards in their library"
  | some id =>
    let o := g.object! id
    let g := g.logMsg s!"{(g.player p).name} reveals {o.name}"
    if o.printed.isArtifact then g.draw p 1 else g

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
        if o.zone == Zone.graveyard controller && o.printed.isCreature then
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
      let g := g.addFinalityTo (g.object! newId) 1
      let g := g.afterPermanentEnters (g.object! newId)
      if g.pending != .none then g
      else if (g.permanentsOf controller).any (fun eq => eq.printed.isEquipment) then
        { g with pending := .mayAttachEquipment controller newId }
          |>.logMsg s!"{(g.player controller).name} may attach an Equipment to {name}"
      else g

/-- One more counter of each kind already on the target (Powerful Broker). -/
def proliferateTarget (g : Game) (controller : PlayerId) (targets : Array Target) : Game :=
  g.withLegalKindTarget controller .permanentOrPlayer targets (fun g t =>
    match t with
    | Target.permanent id =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield && o.status.hasCounters then
          let plus := o.status.plusOnePlusOne
          let extra := g.docSamsonBonus (some controller) o.controller
          let g :=
            if plus > 0 then g.addPlusOnePlusOneTo o 1 (byPlayer := some controller) else g
          let o := g.object! id
          g.setObject { o with status := o.status.proliferatedExceptPlusOne extra }
            |>.logMsg s!"{o.name} gets another counter of each kind"
        else g.logMsg s!"{o.name} has no counters"
      | none => g.logMsg "The target is no longer legal"
    | Target.player pid =>
      let pl := g.player pid
      if pl.poison > 0 then
        g.modifyPlayer pid (fun pl => { pl with poison := pl.poison + 1 })
          |>.logMsg s!"{pl.name} gets a poison counter"
      else g.logMsg s!"{pl.name} has no counters"
    | Target.card _ => g.logMsg "The target is no longer legal") none
    (some "The target is no longer legal")

/-- Put the chosen artifact creature onto the battlefield with `x` +1/+1
counters. Shuffle when the library was searched (Vision Quest; ruling 506). -/
def finishVisionQuest (g : Game) (p : PlayerId) (id? : Option ObjectId)
    (x : Nat) (shuffle : Bool) : Game :=
  let g :=
    match id? with
    | none => g.logMsg s!"{(g.player p).name} finds no artifact creature card"
    | some id =>
      match g.findObject? id with
      | some o =>
        if (o.zone == .library p || o.zone == .graveyard p) &&
            o.printed.isArtifact && o.printed.isCreature &&
            o.printed.manaValue ≤ x then
          let name := o.name
          let (g, newId) := g.putOntoBattlefield id p
          let g :=
            if x > 0 then
              g.addPlusOnePlusOneTo (g.object! newId) x (entersWith := true)
            else g
          let g := g.afterPermanentEnters (g.object! newId)
          let g :=
            if x ≥ 4 then g.grantUntilEotLogged (g.object! newId) Keyword.haste else g
          g.logMsg s!"{name} is put onto the battlefield"
        else g.logMsg "That card can't be found"
      | none => g.logMsg "That card can't be found"
  if shuffle then g.shuffleThen p .none else g

/-- Search the library and/or graveyard for an artifact creature with mana
value `x` or less (Vision Quest). -/
def beginVisionQuest (g : Game) (p : PlayerId) (x : Nat) : Game :=
  let ok (o : GameObject) : Bool :=
    o.printed.isArtifact && o.printed.isCreature && o.printed.manaValue ≤ x
  let lib := (g.player p).library.filter (fun id => (g.findObject? id).any ok)
  let gy := (g.player p).graveyard.filter (fun id => (g.findObject? id).any ok)
  if lib.isEmpty && gy.isEmpty then
    (g.logMsg s!"{(g.player p).name} finds no artifact creature card").shuffleThen p .none
  else
    { g with pending := .fraChoice p (.visionQuestZones lib gy x) }
      |>.logMsg s!"{(g.player p).name} may search their library and their graveyard"

/-- Connive `id` when it is still a creature the spell's controller controls. -/
def conniveTricksterTarget (g : Game) (controller : PlayerId) (id? : Option ObjectId) : Game :=
  match id? with
  | none => g
  | some id =>
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield && o.isCreature && o.controlledBy controller then
        g.applyConnive controller (some id)
      else g.logMsg "The target is no longer legal"
    | none => g.logMsg "The target is no longer legal"

/-- Mana value of spells `p` has cast this turn other than the spell resolving
now (ruling 110). Cascade spells that were actually cast are included. A
resolving copy was not cast, so its mana value is not subtracted. -/
def otherSpellsManaValue (g : Game) (p : PlayerId) : Nat :=
  let total := (g.player p).castManaValuesThisTurn.foldl (· + ·) 0
  let own :=
    match g.resolvingSpell.bind g.findObject? with
    | some spell =>
      if spell.isCopy || spell.controller != some p then 0
      else g.objectManaValue spell
    | none => 0
  total - own

/-- Creature types present on the battlefield, one word each. -/
def battlefieldCreatureTypes (g : Game) : Array String :=
  g.battlefield.foldl (fun acc o =>
    if !o.isCreature then acc
    else
      o.subtypes.foldl (fun acc t =>
        if isCreatureType t && !acc.contains t then acc.push t else acc) acc) #[]

/-- Return each creature that doesn't have `chosen` to its owner's hand. -/
def returnCreaturesNotOfType (g : Game) (chosen : String) : Game :=
  g.foldBattlefield (fun o => o.isCreature && !g.hasSubtype o chosen)
    (fun g o => g.returnToHand o.id o.owner)

/-- Put `put` onto the battlefield, then the rest of `looked` into their
owners' graveyards. Enters abilities run after every chosen creature is on
the battlefield. -/
def finishRevealPutCreatures (g : Game) (p : PlayerId) (looked put : Array ObjectId) : Game :=
  Id.run do
    let mut g := g
    let mut entered : Array ObjectId := #[]
    for id in looked do
      match g.findObject? id with
      | some o =>
        if put.contains id && o.printed.isCreature && o.zone == .library p then
          let (g', newId) := g.putOntoBattlefield id p
          g := g'
          entered := entered.push newId
          g := g.logMsg s!"{(g.player p).name} puts {o.name} onto the battlefield"
        else if o.zone == .library o.owner then
          let (g', _) := g.move id (.graveyard o.owner) none
          g := g'
        else pure ()
      | none => pure ()
    for id in entered do
      match g.findObject? id with
      | some o => g := g.afterPermanentEnters o
      | none => pure ()
    return g

/-- Carry out a `chooseCards` answer. -/
def finishChooseCards (g : Game) (p : PlayerId) (chosen : Array ObjectId)
    (purpose : CardChoice) : Game :=
  match purpose with
  | .toHand _ =>
    chosen.foldl (fun g id =>
      match g.findObject? id with
      | some o =>
        if o.zone == .graveyard o.owner || o.zone == .hand o.owner then
          let name := o.name
          (g.move id (.hand p) none).1.logMsg s!"{(g.player p).name} puts {name} into their hand"
        else g
      | none => g) g
  | .creaturesToBattlefield =>
    chosen.foldl (fun g id =>
      match g.findObject? id with
      | some o =>
        if o.zone == .hand o.owner && o.printed.isCreature then
          let sick := !o.printed.keywords.haste
          let (g, newId) := g.putOntoBattlefield id p (summoningSick := sick)
          let g := g.logMsg s!"{o.name} enters the battlefield"
          g.afterPermanentEnters (g.object! newId)
        else g
      | none => g) g
  | .landsTappedGainLife life =>
    let g :=
      chosen.foldl (fun g id =>
        match g.findObject? id with
        | some o =>
          if o.printed.isLand && o.zone == .library o.owner then
            let name := o.name
            let (g, newId) := g.putOntoBattlefield id p (tapped := true)
            let g := g.setObject { (g.object! newId) with
              status := { (g.object! newId).status with tapped := true } }
            let g := g.logMsg s!"{name} enters tapped"
            g.afterLandEnters (g.object! newId)
          else g
        | none => g) g
    let g := g.requestShuffle p (.gainLife p life)
    g.continueIfShuffled
  | .keepDestroyRest =>
    g.battlefield.foldl (fun g o =>
      if o.isCreature && !chosen.contains o.id then
        match g.findObject? o.id with
        | some o => g.destroyPermanent o
        | none => g
      else g) g
      |>.logMsg "Chosen creatures are kept; the rest are destroyed"
  | .amassArmy subtype n attach =>
    match chosen[0]? with
    | some id => g.finishAmassOn p id subtype n attach
    | none => g.logMsg s!"{(g.player p).name} doesn't choose an Army"

/-- Ask `p` to choose up to `max` of `ids`, or resolve immediately when there
is nothing to decide. -/
def offerCardChoice (g : Game) (p : PlayerId) (ids : Array ObjectId) (max : Nat)
    (purpose : CardChoice) (msg : String) : Game :=
  if ids.isEmpty || max == 0 then g.finishChooseCards p #[] purpose
  else g.beginFraChoice p (.chooseCards ids max purpose) msg

/-- Mill `n`, then choose matching cards from among them for your hand. -/
def millThenChooseForHand (g : Game) (p : PlayerId) (n : Nat)
    (pred : GameObject → Bool) (max : Nat) (mustOne : Bool) : Game :=
  let g := g.mill p n
  let gy := (g.player p).graveyard
  let take := gy.size.min n
  let milled := gy.extract (gy.size - take) gy.size
  let eligible := milled.filter (fun id => (g.findObject? id).any pred)
  if eligible.isEmpty then g
  else if mustOne && eligible.size == 1 then
    g.finishChooseCards p eligible (.toHand true)
  else
    g.offerCardChoice p eligible max (.toHand mustOne)
      s!"{(g.player p).name} chooses cards to put into their hand"

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
      { g.clearMay with pending := .mayAttachEquipment controller o.id }.logMsg
        s!"{(g.player controller).name} may attach an Equipment to {o.name}")
  | r =>
    let phrase := SpellResolution.toPhrase r effect.targeting.kind.noun
    let phrase := if phrase.startsWith "you " then (phrase.drop 4).toString else phrase
    let inner := { effect with resolution := Resolution.ofSpell r }
    { g with
        pending := .mayResolve controller
        mayEffect := some inner
        mayController := controller
        mayTargets := targets }.logMsg
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
          { g with
              pending := .chooseLibraryPlacement o.owner id
              spellOr := #[
                asEffect (.onPermanent .putOnTopOfLibrary),
                asEffect (.onPermanent .putOnBottomOfLibrary)]
              spellOrController := controller
              spellOrTargets := targets
              spellOrLibrary := true }.logMsg
            s!"{(g.player o.owner).name} chooses top or bottom of their library for {o.name}"
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | _ =>
    { g with
        pending := .chooseLibraryPlacement controller ⟨g.nextObjectId⟩
        spellOr := (rs.map asEffect).toArray
        spellOrController := controller
        spellOrTargets := targets
        spellOrLibrary := false }.logMsg
      s!"{(g.player controller).name} chooses {SpellResolution.toPhrase (.or rs) effect.targeting.kind.noun}"

/-- Resolve a unified `Effect` as a spell (CR 608). -/
partial def applyUnified (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0) : Game :=
  match g.applyFraResolution? controller effect targets none with
  | some g => g
  | none =>
  match effect.resolution with
  | .sequence rs =>
    match rs.flatMap Resolution.flatten with
    | [.onPermanent .tap, .scry scryN, .draw drawN] =>
      g.resolveTapScryDraw controller effect targets scryN drawN
    | steps =>
      if g.sequenceAllTargetsIllegal controller effect targets then
        g.logIllegalSequenceTargets targets
      else
        match steps with
        | [.shuffleSource, .draw n] =>
          g.shuffleSourceIntoLibrary none (.draw controller n)
        | steps =>
          steps.foldl (fun g r =>
            g.applyUnified controller { effect with resolution := r } targets
              (castFromGraveyard := castFromGraveyard) (kicked := kicked)
              (giftPromised := giftPromised) (chosenX := chosenX)) g
  | .shuffleSource =>
    g.shuffleSourceIntoLibrary none
  | .gainLife n => g.gainLife controller n
  | .teamGain k =>
    g.grantUntilEotToControlledCreatures controller k k.joinedAnd
  | .recruit => g.beginRecruit controller
  | .addMana types =>
    g.addManaLogged controller types
  | .discard n =>
    g.beginDiscardCards #[controller] n
  | .onSource a =>
    g.applyOnPermanent controller effect.targetKind targets a
  | _ =>
  match effect.spellResolution with
  | .fight =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent srcId), some (Target.permanent destId) =>
      let srcOk := (g.legalCreatureYouControlTargets controller).contains
        (Target.permanent srcId)
      let destOk := (g.legalOppCreatureTargets controller).contains
        (Target.permanent destId)
      if srcOk && destOk then
        g.dealFightDamage (g.object! srcId) (g.object! destId)
      else
        let logIllegal (g : Game) (ok : Bool) (id : ObjectId) : Game :=
          if ok then g else g.illegalAbilityTarget (Target.permanent id)
        logIllegal (logIllegal g srcOk srcId) destOk destId
    | _, _ => g.logMsg "The target is no longer legal"
  | .mutualFight =>
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
  | .extraLand =>
    let g := g.modifyPlayer controller (fun pl =>
      { pl with additionalLandsThisTurn := pl.additionalLandsThisTurn + 1 })
    g.logMsg s!"{(g.player controller).name} may play an additional land this turn"
  | .unrecognized =>
    match effect.resolution with
    | .searchBasicLand => g.resolveSearchBasicLandTapped controller
    | .searchLandTypeToHand t => g.resolveSearchLandTypeToHand controller t
    | .searchBasicLandToHand => g.resolveSearchBasicLandToHand controller
    | .exileTop => g.resolveExileTopPlayUntilEndOfNextTurn controller
    | _ => g.logMsg "The effect does nothing"
  | .onPermanent action =>
    g.applyOnPermanent controller effect.targetKind targets action
  | .creaturesPump p t scope =>
    match scope with
    | .youControl =>
      g.pumpControlledCreatures controller p t
    | .all =>
      g.foldBattlefield (fun o => o.isCreature) (fun g o => g.pumpPermanent o p t)
    | .ofTargetPlayer =>
      g.withLegalKindPlayer controller effect.targetKind targets
        (fun g pid => g.pumpControlledCreatures pid p t)
  | .exileGraveyardCreaturesGrantCast ty =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.exileCreaturesFromGraveyard controller pid ty)
  | .draw n =>
    g.draw controller n
  | .scry n =>
    g.beginScry controller n
  | .tapTargets =>
    g.foldPermanentTargets targets (fun g o =>
      if o.isOnBattlefield && o.isCreature then g.applyPermanentAction o .tap else g)
  | .counter =>
    match targets[0]? with
    | some (Target.card id) => g.counterStackSpell id
    | _ => g.logMsg "The target is no longer legal"
  | .unlessPays r n =>
    g.beginUnlessPays controller effect targets r n
  | .counterExilePermanentMayCast =>
    match targets[0]? with
    | some (Target.card id) =>
      g.counterStackSpell id (exilePermanent := true) (grantFreeCast := true)
        controller
    | _ => g.logMsg "The target is no longer legal"
  | .or rs =>
    match rs with
    | [] => g.logMsg "The effect does nothing"
    | [r] =>
      g.applyUnified controller { effect with resolution := Resolution.ofSpell r } targets
        (castFromGraveyard := castFromGraveyard) (kicked := kicked)
        (giftPromised := giftPromised) (chosenX := chosenX)
    | rs =>
      g.beginSpellOr controller effect targets rs
  | .attachEquipment =>
    g.beginMay controller effect targets .attachEquipment
  | .may r =>
    g.beginMay controller effect targets r
  | .recruit =>
    g.beginRecruit controller
  | .«if» r cond =>
    let run (g : Game) : Game :=
      g.applyUnified controller { effect with resolution := Resolution.ofSpell r } targets
        (castFromGraveyard := castFromGraveyard) (kicked := kicked)
        (giftPromised := giftPromised) (chosenX := chosenX)
    match cond with
    | .subtype subtype =>
      g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
        if g.hasSubtype o subtype then run g else g)
    | .mvAtMost n =>
      match targets[0]? with
      | some (Target.card id) =>
        -- `{X}` remains after the spell leaves the stack. That announced
        -- value is the mana value the spell had (CR 202.3e).
        match g.findObject? (g.followMoved id) with
        | none => g.logMsg "The target is no longer legal"
        | some o =>
          let mv := o.printed.manaValue + o.chosenX.getD 0
          if mv ≤ n then run g else g
      | _ => g.logMsg "The target is no longer legal"
    | .castFromGraveyard =>
      if castFromGraveyard then run g else g
  | .exchangeControl =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent a), some (Target.permanent b) =>
      match g.findObject? a, g.findObject? b with
      | some oa, some ob =>
        -- Both must still be nonland permanents that share a card type.
        -- If either is illegal, the exchange does not happen.
        let nonland (o : GameObject) :=
          o.isOnBattlefield && !o.types.any (· == .land)
        let share := oa.types.any (fun t => ob.types.contains t)
        if a != b && nonland oa && nonland ob && share then
          let ca := oa.controller
          let cb := ob.controller
          let g :=
            match cb with
            | some p => g.changeControl oa p
            | none => g.setObject { oa with controller := none }
          let g :=
            match g.findObject? b, ca with
            | some ob, some p => g.changeControl ob p
            | some ob, none => g.setObject { ob with controller := none }
            | none, _ => g
          g.logMsg s!"{oa.name} and {ob.name} exchange control"
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
          if o.isOnBattlefield && o.isCreature && o.controlledBy controller then
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
  | .gainLife n who =>
    match who with
    | .you => g.gainLife controller n
    | .targetPlayers =>
      Id.run do
        let playerLegal := g.legalTargetsForAtomicKind controller .player none
        let mut g := g
        for t in targets do
          match t with
          | Target.player pid =>
            if playerLegal.contains t then
              g := g.gainLife pid n
            else
              g := g.illegalAbilityTarget t
          | _ => pure ()
        return g
  | .amassGoblins n subtype =>
    g.amass controller subtype n
  | .drawIfFromGy n fromGy =>
    g.draw controller (if castFromGraveyard then fromGy else n)
  | .amassGoblinsOrFromGy n fromGy subtype =>
    g.amass controller subtype (if castFromGraveyard then fromGy else n)
  | .searchLegendaryCreatureToHand s ty =>
    g.resolveLibrarySearchToHand controller (fun c =>
      c.hasType ty && c.hasSupertype s) s!"{s.oracleWord} {ty.oracleWord} card"
  | .dealDamageToEachOppCreature n =>
    g.dealDamageToEachCreatureMatching n (fun o => !o.controlledBy controller)
  | .targetPlayerDraw n =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.draw pid n)
  | .exileIfDiesThisTurn =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      g.mapObjectStatus o (fun s => { s with untilEotExileIfDies := true }))
  | .addRedPerOppArtifacts ty =>
    let n := g.battlefield.filter (fun o =>
      o.printed.hasType ty && !o.controlledBy controller) |>.size
    let g := g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .red) n })
    g.logMsg s!"{(g.player controller).name} adds {n} red mana"
  | .dealDamageToEachNonDragon n subtype =>
    g.dealDamageToEachNonDragon n subtype
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
        if o.isCreature then max acc (g.toughness o).toNat else acc) 0
    let g := g.draw controller greatest
    let creatures :=
      (g.player controller).hand.filter (fun id =>
        (g.findObject? id).any (·.printed.isCreature))
    g.offerCardChoice controller creatures creatures.size .creaturesToBattlefield
      s!"{(g.player controller).name} may put any number of creature cards from their hand onto the battlefield"
  | .millThenPutInstantOrSorcery n a b =>
    g.millThenChooseForHand controller n
      (fun o => o.printed.hasType a || o.printed.hasType b) 1 true
  | .millThenPutLands n max ty =>
    g.millThenChooseForHand controller n (fun o => o.printed.hasType ty) max false
  | .addFourManaDragonSpells n subtype =>
    g.beginFraChoice controller (.addManaColors n (.forSubtype subtype))
      s!"{(g.player controller).name} chooses the colors of {englishNumber n} mana that can be spent only on {subtype} spells"
  | .millThenPutAllInstantsOrSorceries n a b =>
    g.millThenPutFromGy controller n
      (fun o => o.printed.hasType a || o.printed.hasType b)
  | .exileAttackersSearchBasics =>
    g.withLegalKindTarget controller effect.targetKind targets (fun g tgt =>
      match tgt with
      | Target.player pid =>
        Id.run do
          let mut g := g
          let mut n : Nat := 0
          for o in g.battlefield do
            if o.isCreature && o.status.attacking && o.controlledBy pid then
              let name := o.name
              let (g', _) := g.move o.id (.exile) none
              g := g'.logMsg s!"{name} is exiled"
              n := n + 1
          if n == 0 then
            g.logMsg s!"{(g.player pid).name} controls no attacking creatures"
          else
            g.offerMaySearchBasics pid n
      | _ => g.logMsg "The target is no longer legal")
  | .createTokensX kind =>
    g.createKindTokens controller kind chosenX
  | .exileTopPlayIfYouControlSubtype n subtype =>
    g.exileTopPlayIfYouControlSubtype controller n subtype
  | .exileThenReturnYouControl =>
    g.foldPermanentTargets targets (fun g o =>
      if o.controlledBy controller && o.isOnBattlefield then
        g.exileThenReturn o "is exiled, then returned to the battlefield"
          (land := o.printed.isLand)
      else g)
  | .playersCantCastIfGift =>
    if giftPromised then
      g.players.foldl (fun acc pl =>
        acc.setPlayer { pl with cantCastSpellsThisTurn := true }) g
        |>.logMsg "Players can't cast spells this turn"
    else g
  | .exileTopXOppPlayForLife =>
    match targets[0]? with
    | some (Target.player pid) =>
      Id.run do
        let mut g := g
        for _ in List.range chosenX do
          let pl := g.player pid
          if pl.library.isEmpty then
            g := g.logMsg s!"{pl.name} has no cards in their library to exile"
          else
            let top := pl.library.back!
            let name := (g.object! top).name
            let (g', newId) := g.move top .exile none
            g := g'
            let o := g.object! newId
            g := g.setObject { o with
              playPermission := some {
                player := controller
                turnEndsRemaining := 1
                payLifeEqualManaValue := true } }
            g := g.logMsg s!"{(g.player controller).name} exiles {name}"
        return g
    | _ => g.logMsg "The target is no longer legal"
  | .riddlesInTheDark n =>
    let looked := g.scryLookedIds controller n
    if looked.isEmpty then
      g.logMsg s!"{(g.player controller).name}'s library has no cards to look at"
    else
      let g := g.logLookAtTop controller looked.size
      g.beginFraChoice controller (.riddlesSplit looked)
        s!"{(g.player controller).name} separates {looked.size} cards into a face-up pile and a face-down pile"
  | .supperForSpiders =>
    let ids :=
      g.battlefieldCreaturesToGyThisTurn.filter (fun id =>
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
    Id.run do
      let mut g := g
      let mut n : Nat := 0
      for id in ids do
        match g.findObject? id with
        | none => pure ()
        | some o =>
          if o.isOnBattlefield && o.isCreature && o.owner == controller then
            let name := o.name
            let owner := o.owner
            let (g', _) := g.move o.id (.hand owner) none
            g := g'.logMsg s!"{name} is returned to {(g'.player owner).name}'s hand"
            n := n + 1
      if n > 0 then
        g := g.modifyPlayer controller (fun pl =>
          { pl with eaglesBirdsNextUpkeep := pl.eaglesBirdsNextUpkeep + n })
        g := g.logMsg
          s!"At the beginning of the next upkeep, {n} Bird Soldier token(s) will be created"
      return g
  | .lookAtTopLandsGainLife n life =>
    let ids := g.scryLookedIds controller n
    let g := g.logLookAtTop controller ids.size
    let lands := ids.filter (fun id => (g.findObject? id).any (·.printed.isLand))
    if lands.isEmpty then
      let g := g.requestShuffle controller (.gainLife controller life)
      g.continueIfShuffled
    else
      g.offerCardChoice controller lands lands.size (.landsTappedGainLife life)
        s!"{(g.player controller).name} may put any number of land cards from among them onto the battlefield tapped"
  | .gainControlOppArtifacts =>
    g.foldPermanentTargets targets (fun g o =>
      if o.isOnBattlefield && o.printed.isArtifact && !o.controlledBy controller then
        g.changeControl o controller
      else g)
  | .damageOppCreaturesEqualOtherSpellsMv =>
    let n := g.otherSpellsManaValue controller
    g.dealDamageToEachCreatureMatching n (fun o => !o.controlledBy controller)
      |>.logMsg s!"deals {n} damage to each opposing creature"
  | .phaseOutKicker =>
    if kicked then
      match targets[0]? with
      | some (Target.player pid) =>
        (g.permanentsOf pid).foldl (fun acc o =>
          if o.isCreature then acc.phaseOut o else acc) g
      | some (Target.permanent oid) =>
        match g.findObject? oid with
        | some o =>
          let pid := o.controller.getD controller
          (g.permanentsOf pid).foldl (fun acc x =>
            if x.isCreature then acc.phaseOut x else acc) g
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "The target is no longer legal"
    else
      match targets[0]? with
      | some (Target.permanent oid) =>
        match g.findObject? oid with
        | some o => g.phaseOut o
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "The target is no longer legal"
  | .dealDamageTeamwork n teamworkN =>
    let amt := g.teamworkAmount n teamworkN
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      g.dealDamageToPermanent o amt)
  | .damageControllerIfTeamwork n =>
    if !g.resolvingTeamworkPaid then g
    else
      match targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? (g.followMoved id) with
        | some o =>
          let pid? :=
            if o.zone == .battlefield then o.controller
            else o.lastController.orElse (fun _ => o.controller)
          match pid? with
          | some pid => g.dealDamageToPlayer pid n
          | none => g
        | none => g
      | _ => g
  | .grantTrampleIfTeamwork kw =>
    if g.resolvingTeamworkPaid then
      g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
        match Keywords.ofName? kw with
        | some k => g.mapObjectStatus o (·.grantUntilEot k)
        | none => g)
    else g
  | .counterUnlessPaysTeamwork n teamworkN =>
    let amt := g.teamworkAmount n teamworkN
    g.beginPayOrLetCounter targets amt
  | .exileCreatureMvAtMostOrAnyIfTeamwork n life =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let teamwork := g.resolvingTeamworkPaid
      if o.isOnBattlefield && o.isCreature &&
          (teamwork || o.printed.manaValue ≤ n) then
        let (g, _) := g.move o.id .exile none
        if teamwork then g.gainLife controller life else g
      else g.logMsg "The target is no longer legal")
      none (some "The target is no longer legal")
  | .returnGyCreatureMvAtMostOrAny n =>
    match targets[0]? with
    | some (Target.card id) =>
      match g.findObject? id with
      | some o =>
        let teamwork := g.resolvingTeamworkPaid
        if o.zone == Zone.graveyard controller && o.printed.isCreature &&
            (teamwork || o.printed.manaValue ≤ n) then
          let (g, newId) := g.putOntoBattlefield id controller
          g.afterPermanentEnters (g.object! newId)
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | .revealTopPutCreatures n =>
    let top := g.scryLookedIds controller n
    let g :=
      top.foldl (fun g id =>
        match g.findObject? id with
        | some o => g.logMsg s!"{(g.player controller).name} reveals {o.name}"
        | none => g) g
    let creatures :=
      top.filter (fun id => (g.findObject? id).any (·.printed.isCreature))
    if creatures.isEmpty then
      g.finishRevealPutCreatures controller top #[]
    else
      g.beginFraChoice controller
        (.revealPutCreatures top creatures g.resolvingTeamworkPaid)
        s!"{(g.player controller).name} may put creature cards from among them onto the battlefield"
  | .createTokens kind n =>
    g.createKindTokens controller kind n
  | .exileTarget =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      (g.move o.id .exile none).1)
  | .returnOneOrTwoNonlands =>
    targets.foldl (fun g t =>
      match t with
      | Target.permanent oid =>
        match g.findObject? oid with
        | some o =>
          if o.isOnBattlefield && !o.types.any (· == .land) then
            g.returnToHand o.id o.owner
          else
            g.logMsg "The target is no longer legal"
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "The target is no longer legal") g
  | .targetPlayerCreatesTokens kind n =>
    let pid :=
      match targets[0]? with
      | some (Target.player p) => p
      | _ => controller
    g.createKindTokens pid kind n
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
        if o.isOnBattlefield && o.isCreature then
          g.applyPermanentAction o action
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
  | .dealDamageToEachCreature n =>
    g.dealDamageToEachCreatureMatching n
  | .ownerMaySearchBasic s ty =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? (g.followMoved id) with
      | some o =>
        g.beginLibrarySearch o.owner
          (fun c => c.hasType ty && c.hasSupertype s)
          s!"a {s.oracleWord} {ty.oracleWord} card"
          (.battlefield true) (optional := true)
      | none => g
    | _ => g
  | .doublePowerAndToughness =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let p := g.power o
      let t := g.toughness o
      g.applyPermanentAction o (.pump p t))
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
        s!"{o.name} becomes a {p}/{t} artifact creature with {kw} until end of turn"
        (additionalCreature := true) (additionalArtifact := true))
  | .discardTwoUnlessArtifact n ty =>
    let g := { g with thirstDiscardsLeft := n, thirstDiscardType := ty }
    g.beginDiscardCards #[controller]
  | .eachOpponentLosesLife n =>
    g.forEachOpponent controller (fun g pid => g.loseLife pid n)
  | .fightUpToOne =>
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
  | .creatureYouControlDealsTwicePower k =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent a), some (Target.permanent b) =>
      match g.findObject? a, g.findObject? b with
      | some src, some dest =>
        if src.isOnBattlefield && dest.isOnBattlefield && src.isCreature &&
            dest.isCreature && src.controlledBy controller &&
            !dest.controlledBy controller then
          let n :=
            let pw := g.power src
            if pw > 0 then pw * (k : Int) else 0
          g.dealDamageFrom src.name dest n (source := some src)
        else g.logMsg "The target is no longer legal"
      | _, _ => g.logMsg "The target is no longer legal"
    | _, _ => g.logMsg "The target is no longer legal"
  | .createTokensPerSubtype kind subtype =>
    g.createKindTokens controller kind (g.countSubtype controller subtype)
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
    { g with pendingFreeRGCreature := some controller }
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
        if o.isOnBattlefield && o.isCreature && !o.controlledBy controller then
          { g with pending := .fraChoice o.owner (.tricksterLibrary controller id connive) }
            |>.logMsg s!"{(g.player o.owner).name} puts {o.name} second from the top or on the bottom of their library"
        else
          let g := g.logMsg "The target is no longer legal"
          g.conniveTricksterTarget controller connive
      | none =>
        g.conniveTricksterTarget controller connive
    | _ =>
      g.conniveTricksterTarget controller connive
  | .copyThisSpellXTimesThenDamage n =>
    g.applyDamageToKindTarget controller .creature targets n
  | .mayDrawPerArtifactOppsDraw ty =>
    g.mayDrawPerArtifact controller ty
  | .mayPutHeroMvOrDraw n subtype =>
    g.mayPutHeroOrDraw controller n subtype
  | .maySacArtifactOrDiscardDraw cards =>
    { g with pending := .maySacArtifactOrDiscard controller cards }
      |>.logMsg s!"{(g.player controller).name} may sacrifice an artifact or discard a card. If they do, they draw {cards}"
  | .returnUpToTwoGyModal =>
    g.returnChosenGraveyardCards controller targets
  | .artifactSpellsCostLessThisTurn ty n =>
    g.grantTypeCostLessThisTurn controller ty n
  | .supertypeSpellsCostLessThisTurn s n =>
    g.grantSupertypeCostLessThisTurn controller s n
  | _ =>
    -- Shared steps (`draw`, `loseLife`, `surveil`, …) resolve on `Resolution`
    -- before this match. A leftover spell shape does nothing here.
    g.logMsg "The effect does nothing"

/-- Resolve a stashed `unlessPays` effect after its payer left without paying
(CR 800.4f). -/
partial def flushUnlessPays (g : Game) : Game :=
  if !g.unlessPaysDue || g.over then g
  else
    match g.unlessPaysInstead with
    | none => { g with unlessPaysDue := false }
    | some effect =>
      let controller := g.unlessPaysController
      let targets := g.unlessPaysTargets
      let g := g.clearUnlessPays
      let g := g.applyUnified controller effect targets
      if g.pending != .none || g.over then g
      else g.receivePriority g.activePlayer

/-- Resolve a printed spell effect (CR 608). -/
def applyEffect (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0) : Game :=
  g.applyUnified controller effect targets
    (castFromGraveyard := castFromGraveyard) (kicked := kicked)
    (giftPromised := giftPromised) (chosenX := chosenX)

/-- Apply `action` if `sourceId` is still on the battlefield. -/
def applyOnSource (g : Game) (sourceId : Option ObjectId) (action : PermanentAction)
    (missing := "The ability's source is no longer in play") : Game :=
  g.withSourceOnBattlefield sourceId (fun g o => g.applyPermanentAction o action) missing

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
      let sick := !o.printed.keywords.haste
      let (g, newId) := g.putOntoBattlefield o.id controller (tapped := tapped)
        (summoningSick := sick)
      let g := g.logMsg
        (if tapped then s!"{name} returns to the battlefield tapped"
         else s!"{name} returns to the battlefield")
      g.afterPermanentEnters (g.object! newId)

/-- True when `o` has the looked-at type, including an Equipment artifact. -/
def cardHasLookType (o : GameObject) (t : String) : Bool :=
  o.printed.hasSubtype t || (t == "Equipment" && o.printed.isEquipment)

/-- Put `ids` on the bottom. One card needs no order. Two or more are ordered
by the player, first card on the bottom. -/
def offerBottomAnyOrder (g : Game) (p : PlayerId) (ids : Array ObjectId) : Game :=
  if ids.size ≤ 1 then
    (g.moveIdsInOrder ids (.library p)).logMsg
      s!"{(g.player p).name} puts the rest on the bottom of their library"
  else
    g.beginFraChoice p (.orderLibraryBottom ids)
      s!"{(g.player p).name} puts the rest on the bottom of their library in any order"

/-- Look at the top `n` cards. You may reveal one matching card to your hand. -/
def beginLookRevealToHand (g : Game) (p : PlayerId) (n : Nat)
    (ok : GameObject → Bool) (anyOrder : Bool) : Game :=
  let looked := g.scryLookedIds p n
  let g := g.logLookAtTop p looked.size
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
def beginLookPutTypes (g : Game) (p : PlayerId) (n : Nat) (types : Array String) : Game :=
  let looked := g.scryLookedIds p n
  let g := g.logLookAtTop p looked.size
  if looked.isEmpty then g
  else
    let eligible := looked.filter (fun id =>
      (g.findObject? id).any (fun o => types.any (cardHasLookType o)))
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
    if !o.isOnBattlefield || !o.isCreature || o.id == arwenId then
      g.logMsg "The target is no longer legal. The ability does nothing."
    else
      let putCounters (g : Game) (oid : ObjectId) : Game :=
        match g.findObject? oid with
        | none => g
        | some x =>
          let g := g.addPlusOnePlusOneTo x 1
          g.addLifelinkCounter (g.object! x.id)
      let g := g.setObject { o with status := o.status.grantUntilEot Keyword.indestructible }
      let g := g.logMsg s!"{o.name} gains indestructible until end of turn"
      let g := putCounters g o.id
      putCounters g arwenId

/-- Put the +1/+1 counter that waited for each opponent's discard. -/
def finishPlusOneAfterDiscards (g : Game) : Game :=
  match g.plusOneAfterDiscards with
  | none => g
  | some id =>
    let g := { g with plusOneAfterDiscards := none }
    match g.findObject? (g.followMoved id) with
    | some o =>
      if o.isOnBattlefield then g.addPlusOnePlusOneTo o 1 else g
    | none => g

/-- Resolve a unified activated-ability `Effect` (CR 608). -/
partial def applyUnifiedAbility (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (sourceId : Option ObjectId := none)
    (lastKnownPower : Option Int := none) (chosenX : Nat := 0) : Game :=
  match g.applyFraResolution? controller effect targets sourceId with
  | some g => g
  | none =>
  match effect.resolution with
  | .sequence rs =>
    match rs.flatMap Resolution.flatten with
    | [.onPermanent .tap, .scry scryN, .draw drawN] =>
      g.resolveTapScryDraw controller effect targets scryN drawN sourceId
        (fizzle := fun g => g.logIllegalSequenceTargets targets)
    | steps =>
      if g.sequenceAllTargetsIllegal controller effect targets sourceId then
        g.logIllegalSequenceTargets targets
      else
        match steps with
        | [.shuffleSource, .draw n] =>
          g.shuffleSourceIntoLibrary sourceId (.draw controller n)
        | steps =>
          steps.foldl (fun g r =>
            g.applyUnifiedAbility controller { effect with resolution := r } targets
              sourceId lastKnownPower chosenX) g
  | .shuffleSource =>
    g.shuffleSourceIntoLibrary sourceId
  | .amassGoblins n => g.amassGoblins controller n
  | .discard n =>
    g.beginDiscardCards #[controller] n
  | .spell r =>
    g.applyUnified controller { effect with resolution := .spell r } targets
      (chosenX := chosenX)
  | _ =>
  match effect.resolution with
  | .searchBasicLand => g.resolveSearchBasicLandTapped controller
  | .searchLandTypeToHand t => g.resolveSearchLandTypeToHand controller t
  | .exileTop => g.resolveExileTopPlayUntilEndOfNextTurn controller
  | .attach =>
    g.withLegalKindPermanent controller effect.targetKind targets fun g host =>
      g.withSourceOnBattlefield sourceId (fun g src =>
        if src.attachedTo == some host.id then
          g.logMsg s!"{src.name} is already attached to {host.name}"
        else
          g.attachSourceTo src host)
        "The Equipment is no longer in play"
  | .onPermanent action =>
    g.applyOnPermanent controller effect.targetKind targets action sourceId
  | .onSource action =>
    g.applyOnSource sourceId action
  | .becomeSubtypeWithLandsPT subtype =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let subtypes :=
        if g.hasSubtype o subtype then o.status.additionalSubtypes
        else o.status.additionalSubtypes.push subtype
      let granted :=
        if g.hasLandsYouControlPT o then o.status.grantedStaticAbilities
        else o.status.grantedStaticAbilities.push .powerToughnessEqualLandsYouControl
      let g := g.mapObjectStatus o (fun s =>
        { s with
          additionalCreature := true
          additionalSubtypes := subtypes
          grantedStaticAbilities := granted })
      g.logMsg
        s!"{o.name} becomes {indefinite subtype} {subtype} creature. Its power and toughness are each equal to the number of lands you control"
  | .returnFromGraveyardTapped =>
    g.returnSourceFromGraveyard sourceId controller (tapped := true)
  | .returnFromGraveyardToHand =>
    g.returnSourceFromGraveyard sourceId controller (toHand := true)
  | .creaturesYouControlPump pw tw =>
    g.pumpControlledCreatures controller pw tw
  | .mill n =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.mill pid n)
  | .addAnyColor =>
    let g := g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .white) })
    g.logMsg s!"{(g.player controller).name} adds one mana of any color"
  | .recruit =>
    g.beginRecruit controller
  | .scry n =>
    g.beginScry controller n
  | .gainLife n =>
    g.gainLife controller n
  | .createTokens kind n tapped =>
    g.createKindTokens controller kind n (tapped := tapped)
  | .returnFromGyAttach =>
    match sourceId.bind g.findObject? with
    | none => g.logMsg "The source is no longer in the graveyard"
    | some src =>
      g.withLegalKindPermanent controller effect.targetKind targets (fun g host =>
        let (g, newId) := g.putOntoBattlefield src.id controller
          (attachedTo := some host.id)
        let o := g.object! newId
        let g := g.logMsg s!"{o.name} enters the battlefield attached to {host.name}"
        g.afterPermanentEnters (g.object! newId))
        sourceId (some "The target is no longer legal. Eagle's Rescue remains in the graveyard.")
  | .addMana types =>
    g.addManaLogged controller types
  | .searchBasicLandToHand =>
    g.resolveSearchBasicLandToHand controller
  | .createTokensX kind =>
    g.createKindTokens controller kind chosenX
  | .draw n =>
    g.draw controller n
  | .searchTwoBasicsSplit =>
    g.beginLibrarySearch controller isBasicLandCard "a basic land card"
      .battlefieldTappedThenHand (count := 2)
  | .subtypesGainMenace subtypes =>
    g.grantUntilEotToControlledCreatures controller Keyword.menace "menace"
      (fun g o => subtypes.any (g.hasSubtype o))
  | .exileThenReturnNextEnd =>
    g.foldPermanentTargets targets (fun g o =>
      if o.isOnBattlefield && o.controlledBy controller && !o.printed.isLand &&
          some o.id != sourceId then
        let name := o.name
        let (g, newId) := g.move o.id .exile none
        { g with delayedEndStepReturns := g.delayedEndStepReturns.push newId }
          |>.logMsg s!"{name} is exiled until the beginning of the next end step"
      else g.logMsg "The target is no longer legal")
  | .searchBasicBeholdSubtypeUntap subtype =>
    g.beginLibrarySearch controller isBasicLandCard "a basic land card"
      (.battlefieldTappedBeholdUntap subtype)
  | .twoPlayersDraw =>
    match targets[0]?, targets[1]? with
    | some (Target.player a), some (Target.player b) =>
      if a == b then g.logMsg "Two target players must be different"
      else g.draw a 1 |>.draw b 1
    | _, _ => g.logMsg "The targets are no longer legal"
  | .discardLegendarySameNameDraw =>
    g.draw controller 2
  | .dealDamageToAny n =>
    g.applyEffect controller (Effect.dealDamage n) targets
  | .drawEqualToLastKnownPower =>
    g.draw controller ((lastKnownPower.getD 0).toNat)
  | .arwenShare =>
    match sourceId, targets[0]? with
    | some sid, some (Target.permanent tid) => g.resolveArwenShare sid (some tid)
    | some sid, _ => g.resolveArwenShare sid none
    | _, _ => g.logMsg "The ability's source is no longer in play"
  | .grantCombatDamageCreateTreasure =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.mapObjectStatus o (fun s => { s with combatDamageCreatesTreasure := true })
      g.logMsg
        s!"{o.name} gains \"Whenever this creature deals combat damage to a player, create a Treasure token\"")
      sourceId (some "The target is no longer legal")
  | .putShadowCounter =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      g.putShadowCounter o) sourceId (some "The target is no longer legal")
  | .damageEachOpponent n =>
    g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid n)
  | .chooseTwoDestroyRest =>
    let creatures := (g.battlefield.filter (·.isCreature)).map (·.id)
    g.offerCardChoice controller creatures 2 .keepDestroyRest
      s!"{(g.player controller).name} chooses up to two creatures to keep"
  | .blackGateUnblockable =>
    match targets[0]? with
    | some (Target.permanent oid) =>
      match g.findObject? oid with
      | some o =>
        if o.isOnBattlefield && o.isCreature then
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
  | .teamGain k =>
    g.grantUntilEotToControlledCreatures controller k k.joinedAnd
  | .plusOneOnEachOtherSubtype subtype n =>
    g.foldBattlefield (fun o =>
        o.controlledBy controller && o.id != sourceId.getD ⟨0⟩ && g.hasSubtype o subtype)
      (fun g o => g.addPlusOnePlusOneTo o n)
  | .plusOneX =>
    g.withSourceOnBattlefield sourceId fun g o =>
      g.addPlusOnePlusOneTo o chosenX
  | .eachOppDiscardThenPlusOne =>
    let opps := (g.livingOpponents controller).map (·.id)
    let g := { g with plusOneAfterDiscards := sourceId }
    let g := g.beginDiscardCards opps
    if g.pending == .none then
      (g.finishPlusOneAfterDiscards).receivePriority g.activePlayer
    else g
  | .lookAtTopPutTypes n types =>
    g.beginLookPutTypes controller n types
  | .transform =>
    g.withSourceOnBattlefield sourceId fun g o =>
      if o.status.cantTransform then
        g.logMsg s!"{o.name} can't transform (entered back face up at night)"
      else
        match o.printed.otherFace with
        | none => g.logMsg s!"{o.name} has no other face"
        | some face =>
          let back := { face with otherFace := some { o.printed with otherFace := none } }
          let g := g.setObject { o with
            printed := back
            status := { o.status with transformed := !o.status.transformed } }
          g.logMsg s!"{o.name} transforms into {back.name}"
  | .drawX =>
    g.draw controller chosenX
  | .lookAtTopRevealArtifact n =>
    g.beginLookRevealToHand controller n (fun o => o.printed.isArtifact) false
  | .connive =>
    g.applyConnive controller sourceId
  | .addAnyColorSpendOnlySubtype subtype =>
    match subtype with
    | "Hero" =>
      g.modifyPlayer controller (fun pl =>
        { pl with manaPool :=
          pl.manaPool.add (.colored .white) 1 (heroRestricted := true) })
    | "Villain" =>
      g.modifyPlayer controller (fun pl =>
        { pl with manaPool :=
          pl.manaPool.add (.colored .black) 1 (villainRestricted := true) })
    | _ =>
      g.modifyPlayer controller (fun pl =>
        { pl with manaPool := pl.manaPool.add (.colored .white) 1 })
  | .addAnyColorSpendOnlyArtifactSpell =>
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .white) 1 })
  | .addTwoAnyColorCreatureSources =>
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool :=
        pl.manaPool.add (.colored .green) 2 (creatureRestricted := true) })
  | .addBlueCantNonartifact =>
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool :=
        pl.manaPool.add (.colored .blue) 1 (cantNonartifact := true) })
  | .addAnyColorEqualToSourcePower =>
    let x :=
      match sourceId.bind g.findObject? with
      | some o => (g.power o).toNat
      | none => 0
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .green) x })
  | .addFourAnyCombination =>
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .white) 4 })
  | .addTwoAnyColorEquipment =>
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool :=
        pl.manaPool.add (.colored .white) 2 })
  | .drawPerDiscardedThisTurn =>
    g.draw controller (g.player controller).cardsDiscardedThisTurn
  | .dealDamageToEachCreature n =>
    g.dealDamageToEachCreatureMatching n
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
            { g with pending := .fraChoice controller (.newTargetsForCopies #[copyId]) }
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
      else if o.isCreature then
        g.logMsg s!"{o.name} is already a creature"
      else
        let wasAttached := o.attachedTo.isSome
        let g :=
          if wasAttached then
            g.setObject { o with attachedTo := none }
              |>.logMsg s!"{o.name} becomes unattached"
          else g
        let o := g.object! o.id
        g.setUntilEotForm o (0, 0) Keyword.flying
          s!"{o.name} becomes a 0/0 Construct Hero artifact creature"
          (types := some #["Construct", "Hero"])
          (additionalCreature := true) (additionalArtifact := true)
          (pumpPerArtifact := true)
    | none => g.logMsg "The Equipment is no longer in play"
  | .lookAtTopRevealSubtype n subtype =>
    g.beginLookRevealToHand controller n (fun o => o.printed.hasSubtype subtype) true
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
            dest.controlledBy controller && src.controlledBy controller &&
            dest.printed.isArtifact && src.printed.isArtifact then
          g.becomeCopyOf dest src (untilEot := true) (notLegendary := true)
        else
          g.logMsg "The target is no longer legal. The ability has no effect."
      | _, _ =>
        g.logMsg "The target is no longer legal. The ability has no effect."
    | _, _ =>
      g.logMsg "The target is no longer legal. The ability has no effect."
  | .becomeTypes types p t k =>
    let typeWords := String.intercalate " " types.toList
    g.withSourceOnBattlefield sourceId (fun g o =>
      g.setUntilEotForm o (p, t) k
        s!"{o.name} becomes a {p}/{t} {typeWords}"
        (types := some types))
      "The source is no longer in play"
  | .nextInstantSorceryCopyIfMvAtMostSourcePower =>
    let pw :=
      match sourceId.bind g.findObject? with
      | some o =>
        if o.isOnBattlefield then g.power o else o.power
      | none => (0 : Int)
    { g with pendingLokiCopy := some (controller, sourceId, pw) }
      |>.logMsg s!"The next instant or sorcery with mana value {pw} or less will be copied"
  | .harnessInfinityStone =>
    g.withSourceOnBattlefield sourceId (fun g o =>
      let g := g.mapObjectStatus o (fun s => { s with harnessed := true })
      g.logMsg s!"{o.name} is harnessed") "The source is no longer in play"
  | .targetSubtypeConnives _ =>
    match targets[0]? with
    | some (Target.permanent id) => g.applyConnive controller (some id)
    | _ => g.applyConnive controller none
  | .trigger .exileOppNonlandEachUntilLeaves =>
    g.withSourceStillOnBattlefield sourceId fun g _ =>
      targets.foldl (fun acc t =>
        match t with
        | Target.permanent oid =>
          match acc.findObject? oid with
          | some o => acc.exileUntilSourceLeaves sourceId o
          | none => acc
        | _ => acc) g
  | .sequence _ | .shuffleSource | .amassGoblins _ | .discard _ | .spell _ | .trigger _ =>
    g
  | .empowerJace _ | .surveil _ | .millSelf _ | .mayDiscardDraw _
  | .createTokensLifeGained _ | .oppSacrificesGreatestMv
  | .createTigerGod | .extraTurn | .drawEqualToBurdenCounters
  | .creaturesWithoutFlyingCantBlock | .targetPlayerLoseLife _
  | .controllerOfTargetLosesLife _ | .returnTargetSpell | .chooseOddOrEvenDestroy
  | .eachCreatureYouControlBecomesPrepared | .damageThenEmpowerExcess _
  | .jaceLoyaltyAtInstantSpeed | .becomeCopyLegendRuleOff | .copyEachCreatureOfTargetPlayer
  | .proliferatePlaneswalkerTypesTimes | .copyNextInstantSorceryThisTurn | .returnFromGyWithFinality
  | .firstDealsStatDamageToSecond _
  | .exileTopMayCastElseDamageOpponents _ | .emblemCastSpellDamage _ | .fra _ =>
    g

/-- Resolve a printed activated ability (CR 608). -/
def applyAbilityEffect (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (sourceId : Option ObjectId := none)
    (lastKnownPower : Option Int := none) (chosenX : Nat := 0) : Game :=
  g.applyUnifiedAbility controller effect targets
    sourceId lastKnownPower chosenX

end Game
end Mtg.Engine
