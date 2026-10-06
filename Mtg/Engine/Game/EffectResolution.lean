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
  | .oppSacrificesGreatestMvGainLife life =>
    some (g.withLegalKindPlayer controller effect.targetKind targets (fun g pid =>
      (g.sacrificeGreatestManaValue pid).gainLife controller life) sourceId)
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

/-- You may draw one card for each artifact you control. If you do, each
opponent draws a card (Armor Wars). -/
def mayDrawPerArtifact (g : Game) (p : PlayerId) : Game :=
  let n := ((g.permanentsOf p).filter (fun o => o.printed.isArtifact)).size
  if n == 0 then
    g.logMsg s!"{(g.player p).name} controls no artifacts, so no cards are drawn"
  else
    { g with pending := .fraChoice p (.mayDrawThenEachOpponentDraws n) }
      |>.logMsg s!"{(g.player p).name} may draw {n}"

/-- You may put a Hero creature card with mana value `maxMv` or less from
your hand onto the battlefield. If you don't, draw a card (Origin of the
Avengers; ruling 507). -/
def mayPutHeroOrDraw (g : Game) (p : PlayerId) (maxMv : Nat) : Game :=
  let ids := (g.player p).hand.filter (fun id =>
    (g.findObject? id).any (fun o =>
      o.printed.isCreature && g.hasSubtype o "Hero" && o.printed.manaValue ≤ maxMv))
  if ids.isEmpty then g.draw p 1
  else
    { g with pending := .fraChoice p (.mayPutHeroFromHandOrDraw ids) }
      |>.logMsg s!"{(g.player p).name} may put a Hero creature card onto the battlefield"

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
          let g :=
            if plus > 0 then g.addPlusOnePlusOneTo o 1 else g
          let o := g.object! id
          g.setObject { o with status := o.status.proliferatedExceptPlusOne }
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
  | .drawAndLoseLife cards life =>
    g.drawThenLoseLife controller cards life
  | .onPermanent action =>
    g.applyOnPermanent controller effect.targetKind targets action
  | .allCreaturesPump p t =>
    g.foldBattlefield (fun o => o.isCreature) (fun g o => g.pumpPermanent o p t)
  | .playerDrawLoseLife cards life =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.drawThenLoseLife pid cards life)
  | .creaturesOfPlayerPump pw tw =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.pumpControlledCreatures pid pw tw)
  | .destroyAndControllerLosesLife n =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let ctrl := o.controller
      let g := g.destroyPermanent o
      match ctrl with
      | some pid => g.loseLife pid n
      | none => g)
  | .exileGraveyardCreaturesGrantCast =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.exileCreaturesFromGraveyard controller pid)
  | .draw n =>
    g.draw controller n
  | .drawThenDiscard n =>
    g.drawThenBeginDiscard controller n
  | .scry n =>
    g.beginScry controller n
  | .tapScryDraw scryN drawN =>
    let legal := g.legalTargetsForKind controller effect.targetKind
    match targets[0]? with
    | some t =>
      if legal.contains t then
        let g := g.applyOnPermanent controller effect.targetKind targets .tap
        let g := { g with pendingDrawAfterScry := some (controller, drawN) }
        let g := g.beginScry controller scryN
        if g.pendingDrawAfterScry.isSome &&
            (match g.pending with | .scry _ _ => false | _ => true) then
          let g := { g with pendingDrawAfterScry := none }
          g.draw controller drawN
        else g
      else
        g.logMsg "The spell doesn't resolve"
    | none => g.logMsg "The spell doesn't resolve"
  | .tapTargets =>
    g.foldPermanentTargets targets (fun g o =>
      if o.isOnBattlefield && o.isCreature then g.applyPermanentAction o .tap else g)
  | .counter =>
    match targets[0]? with
    | some (Target.card id) => g.counterStackSpell id
    | _ => g.logMsg "The target is no longer legal"
  | .counterUnlessPays n =>
    g.beginPayOrLetCounter targets n
  | .counterExilePermanentMayCast =>
    match targets[0]? with
    | some (Target.card id) =>
      g.counterStackSpell id (exilePermanent := true) (grantFreeCast := true)
        controller
    | _ => g.logMsg "The target is no longer legal"
  | .putOnTopOrBottom =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield then
          { g with pending := .chooseLibraryPlacement o.owner id }.logMsg
            s!"{(g.player o.owner).name} chooses top or bottom of their library for {o.name}"
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | .untapPumpMaybeAttach p t =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.applyPermanentAction o .untap
      let o := g.object! o.id
      let g := g.pumpPermanent o p t
      let o := g.object! o.id
      if g.hasSubtype o "Dwarf" then
        { g with pending := .mayAttachEquipment controller o.id }.logMsg
          s!"{(g.player controller).name} may attach an Equipment to {o.name}"
      else g)
  | .exchangeControl =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent a), some (Target.permanent b) =>
      match g.findObject? a, g.findObject? b with
      | some oa, some ob =>
        if oa.isOnBattlefield && ob.isOnBattlefield then
          let ca := oa.controller
          let cb := ob.controller
          let g :=
            match cb with
            | some p => g.changeControl oa p
            | none => g.setObject { oa with controller := none }
          let g :=
            match ca with
            | some p => g.changeControl (g.object! b) p
            | none => g.setObject { (g.object! b) with controller := none }
          g.logMsg s!"{oa.name} and {ob.name} exchange control"
        else g.logMsg "The target is no longer legal"
      | _, _ => g.logMsg "The target is no longer legal"
    | _, _ => g.logMsg "The target is no longer legal"
  | .plusOneAndPlayerGainsLife n =>
    Id.run do
      let creatureLegal := g.legalTargetsForAtomicKind controller .creature none
      let playerLegal := g.legalTargetsForAtomicKind controller .player none
      let mut g := g
      for t in targets do
        match t with
        | Target.permanent oid =>
          if creatureLegal.contains t then
            match g.findObject? oid with
            | some o => g := g.addPlusOnePlusOneTo o 1
            | none => g := g.logMsg "The target is no longer in play"
          else
            g := g.illegalAbilityTarget t
        | Target.player pid =>
          if playerLegal.contains t then
            g := g.gainLife pid n
          else
            g := g.illegalAbilityTarget t
        | Target.card _ =>
          g := g.illegalAbilityTarget t
      return g
  | .returnSpellDraw =>
    let g :=
      match targets[0]? with
      | some (Target.card id) => g.returnStackSpell id
      | _ => g.logMsg "The target is no longer legal"
    g.draw controller 1
  | .creaturesYouControlPump pw tw =>
    g.pumpControlledCreatures controller pw tw
  | .amassGoblins n =>
    g.amassGoblins controller n
  | .drawLoseLifeThenAmass n =>
    let g := g.draw controller 1
    let g := g.loseLife controller 1
    g.amassGoblins controller n
  | .returnCreatureFromGyThenAmass n =>
    let g :=
      match targets[0]? with
      | some (Target.card oid) =>
        match g.findObject? oid with
        | none => g.logMsg "The target is no longer in the graveyard"
        | some o =>
          g.returnToHand o.id controller
      | _ => g
    g.amassGoblins controller n
  | .counterThenRecruitIfMvAtMost n =>
    match targets[0]? with
    | some (Target.card id) =>
      match g.findObject? id with
      | none => g.logMsg "The target is no longer legal"
      | some o =>
        let mv := o.printed.manaValue
        let g := g.counterStackSpell id
        if mv <= n then g.beginRecruit controller else g
    | _ => g.logMsg "The target is no longer legal"
  | .plusOneThenFight n =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent srcId), some (Target.permanent destId) =>
      match g.findObject? srcId, g.findObject? destId with
      | some src, some dest =>
        let g := g.addPlusOnePlusOneTo src n
        g.fightCreatures (g.object! src.id) (g.object! dest.id)
      | _, _ => g.logMsg "The target is no longer legal"
    | _, _ => g.logMsg "The target is no longer legal"
  | .plusOneThenEachOtherIfFromGy =>
    match targets[0]? with
    | some (Target.permanent oid) =>
      match g.findObject? oid with
      | none => g.logMsg "The target is no longer legal"
      | some o =>
        let g := g.addPlusOnePlusOneTo o 1
        if !castFromGraveyard then g
        else
          g.forEachControlledCreature controller
            (fun g c => g.addPlusOnePlusOneTo c 1) (some oid)
    | _ => g.logMsg "The target is no longer legal"
  | .drawIfFromGy n fromGy =>
    g.draw controller (if castFromGraveyard then fromGy else n)
  | .amassGoblinsOrFromGy n fromGy =>
    g.amassGoblins controller (if castFromGraveyard then fromGy else n)
  | .searchLegendaryCreatureToHand =>
    g.resolveLibrarySearchToHand controller (fun c =>
      c.isCreature && c.hasSupertype .legendary) "legendary creature card"
  | .dealDamageToEachOppCreature n =>
    g.dealDamageToEachCreatureMatching n (fun o => !o.controlledBy controller)
  | .targetPlayerDraw n =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.draw pid n)
  | .dealDamageToCreatureExileIfDies n =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.mapObjectStatus o (fun s => { s with untilEotExileIfDies := true })
      g.applyPermanentAction (g.object! o.id) (.dealDamage n))
  | .addRedPerOppArtifacts =>
    let n := g.countOpponentArtifacts controller
    let g := g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .red) n })
    g.logMsg s!"{(g.player controller).name} adds {n} red mana"
  | .dealDamageToEachNonDragon n =>
    g.dealDamageToEachNonDragon n
  | .chooseTypeReturnOthers =>
    let chosen :=
      (g.battlefield.find? (fun o => o.isCreature && o.controlledBy controller)
        |>.bind (fun o => o.printed.subtypes[0]?)).getD "Elf"
    g.foldBattlefield (fun o => o.isCreature && !g.hasSubtype o chosen)
      (fun g o => g.returnToHand o.id o.owner)
  | .drawEqualToughnessThenPutCreatures =>
    let greatest :=
      (g.permanentsOf controller).foldl (fun acc o =>
        if o.isCreature then max acc (g.toughness o).toNat else acc) 0
    let g := g.draw controller greatest
    Id.run do
      let mut g := g
      for id in (g.player controller).hand do
        let o := g.object! id
        if o.printed.isCreature then
          let sick := !o.printed.keywords.haste
          let (g', newId) := g.putOntoBattlefield id controller (summoningSick := sick)
          g := g'.logMsg s!"{o.name} enters the battlefield"
          g := g.afterPermanentEnters (g.object! newId)
      return g
  | .millThenPutInstantOrSorcery n =>
    g.millThenPutFromGy controller n
      (fun o => o.printed.isInstant || o.printed.isSorcery) (some 1)
  | .millThenPutLands n max =>
    g.millThenPutFromGy controller n (fun o => o.printed.isLand) (some max)
  | .dealDamageToEachNonDragonThenAddDragonMana n =>
    let g := g.dealDamageToEachNonDragon n
    g.beginFraChoice controller (.addManaColors 4 .dragonSpell)
      s!"{(g.player controller).name} chooses the colors of four mana that can be spent only on Dragon spells"
  | .millThenPutAllInstantsOrSorceries n =>
    g.millThenPutFromGy controller n
      (fun o => o.printed.isInstant || o.printed.isSorcery)
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
      if o.controlledBy controller then
        g.exileThenReturn o "is exiled, then returned to the battlefield"
      else g)
  | .destroyArtifactOrEnchantmentGainLife n =>
    let g := g.applyOnPermanent controller effect.targetKind targets .destroy
    if n == 0 then g
    else
      let pl := g.player controller
      g.setLife controller (pl.life + (n : Int))
        s!"{pl.name} gains {n} life ({pl.life + (n : Int)} life)"
  | .returnSpellCantCastIfGift =>
    let g :=
      match targets[0]? with
      | some (Target.card sid) => g.returnStackSpell sid
      | _ => g.logMsg "The target is no longer legal"
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
                whileExiled := true
                payLifeEqualManaValue := true } }
            g := g.logMsg s!"{(g.player controller).name} exiles {name}"
        return g
    | _ => g.logMsg "The target is no longer legal"
  | .riddlesInTheDark =>
    g.riddlesInTheDark controller 2 false
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
    Id.run do
      let mut g := g
      let ids := g.scryLookedIds controller n
      for id in ids do
        match g.findObject? id with
        | some o =>
          if o.printed.isLand then
            let name := o.name
            let (g', newId) := g.putOntoBattlefield id controller (tapped := true)
            g := g'
            g := g.setObject { (g.object! newId) with
              status := { (g.object! newId).status with tapped := true } }
            g := g.logMsg s!"{name} enters tapped"
            g := g.afterLandEnters (g.object! newId)
          else pure ()
        | none => pure ()
      g := g.requestShuffle controller (.gainLife controller life)
      return g.continueIfShuffled
  | .gainControlOppArtifacts =>
    g.foldPermanentTargets targets (fun g o =>
      if o.isOnBattlefield && o.printed.isArtifact && !o.controlledBy controller then
        g.changeControl o controller
      else g)
  | .damageOppCreaturesEqualOtherSpellsMv =>
    let xs := (g.player controller).castManaValuesThisTurn
    let n : Nat := (xs.extract 0 xs.size.pred).foldl (fun a b => a + b) 0
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
  | .dealDamageThenControllerIfTeamwork n extra =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.dealDamageToPermanent o n
      if g.resolvingTeamworkPaid then
        match o.controller with
        | some pid => g.dealDamageToPlayer pid extra
        | none => g
      else g)
  | .grantDoubleStrikeTeamworkTrample =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.mapObjectStatus o (·.grantUntilEot Keyword.doubleStrike)
      if g.resolvingTeamworkPaid then
        g.mapObjectStatus (g.object! o.id) (·.grantUntilEot Keyword.trample)
      else g)
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
    Id.run do
      let mut g := g
      let top := g.scryLookedIds controller n
      let teamwork := g.resolvingTeamworkPaid
      let mut putOne := false
      for id in top do
        let o := g.object! id
        if o.printed.isCreature && (teamwork || !putOne) then
          let (g', _) := g.putOntoBattlefield id controller
          g := g'
          putOne := true
        else
          let (g', _) := g.move id (.graveyard o.owner) none
          g := g'
      return g
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
        | some o => (g.move o.id (.hand o.owner) none).1
        | none => g
      | _ => g) g
  | .targetPlayerCreatesTokens kind n =>
    let pid :=
      match targets[0]? with
      | some (Target.player p) => p
      | _ => controller
    g.createKindTokens pid kind n
  | .destroyCreatureSurveil =>
    let stillLegal :=
      match targets[0]? with
      | some t => (g.legalTargetsForKind controller effect.targetKind).contains t
      | none => false
    if stillLegal then
      let g := g.withLegalKindPermanent controller effect.targetKind targets
        (fun g o => g.destroyPermanent o)
      g.beginSurveil controller 1
    else
      g.logMsg "The target is no longer legal. You won't surveil."
  | .investigatePumpFlyingUntap =>
    let player? := targets.findSome? (fun t =>
      match t with
      | Target.player pid => some pid
      | _ => none)
    let creature? := targets.findSome? (fun t =>
      match t with
      | Target.permanent id => some id
      | _ => none)
    let g :=
      match player? with
      | some pid =>
        if (g.player pid).lost then g.logMsg "The target is no longer legal"
        else (g.createToken pid clueToken).1
      | none => g.logMsg "The target is no longer legal"
    match creature? with
    | none => g.logMsg "The target is no longer legal"
    | some id =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield && o.isCreature then
          let g := g.mapObjectStatus o (·.grantUntilEot Keyword.flying)
          let o := g.object! o.id
          let g := g.applyPermanentAction o .untap
          g.applyPermanentAction (g.object! o.id) (.pump 1 0)
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
  | .plusOneLifelinkIndestructible =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.mapObjectStatus o (fun s =>
        { s with plusOnePlusOne := s.plusOnePlusOne + 1 })
      g.grantUntilEotKeywords (g.object! o.id) [Keyword.lifelink, Keyword.indestructible])
  | .dealDamageToEachCreature n =>
    g.dealDamageToEachCreatureMatching n
  | .destroyLandSearchBasic =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let owner := o.owner
      let g := g.destroyPermanent o
      g.offerMaySearchBasics owner)
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
  | .grantVigilanceUnblockable =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.grantUntilEotKeywords o [Keyword.vigilance, Keyword.cantBeBlocked]
      g.draw controller 1)
      none (some "The target is no longer legal. You won't draw a card.")
  | .becomeArtifactCreature44Flying =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      g.setUntilEotForm o (4, 4) Keyword.flying
        s!"{o.name} becomes a 4/4 artifact creature with flying until end of turn"
        (additionalCreature := true) (additionalArtifact := true))
  | .drawThreeDiscardUnlessArtifact =>
    let g := g.draw controller 3
    let g := { g with thirstDiscardsLeft := 2 }
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
  | .plusOneOnEachYouControl =>
    g.forEachControlledCreature controller (fun g o => g.addPlusOnePlusOneTo o 1)
  | .plusOneOnCreatureN n =>
    g.withLegalKindPermanent controller .creatureYouControl targets
      (fun g o => g.addPlusOnePlusOneTo o n)
  | .pumpThenDraw p t =>
    g.withLegalKindPermanent controller .creature targets (fun g o =>
      let g := g.pumpPermanent o p t
      g.draw controller 1)
      none (some "The target is no longer legal. You won't draw a card.")
  | .pumpThenExileTopPlay p t =>
    g.withLegalKindPermanent controller .creature targets (fun g o =>
      let g := g.pumpPermanent o p t
      g.exileTopPlayThisTurn controller 1)
      none (some "The target is no longer legal. No card will be exiled.")
  | .creatureYouControlDealsTwicePower =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent a), some (Target.permanent b) =>
      match g.findObject? a, g.findObject? b with
      | some src, some dest =>
        if src.isOnBattlefield && dest.isOnBattlefield && src.isCreature &&
            dest.isCreature && src.controlledBy controller &&
            !dest.controlledBy controller then
          let n :=
            let pw := g.power src
            if pw > 0 then pw * 2 else 0
          g.dealDamageFrom src.name dest n (source := some src)
        else g.logMsg "The target is no longer legal"
      | _, _ => g.logMsg "The target is no longer legal"
    | _, _ => g.logMsg "The target is no longer legal"
  | .createTokensThenTeamPump kind n p t =>
    let g := g.createKindTokens controller kind n
    g.pumpControlledCreatures controller p t
  | .createTokensPerSubtype kind subtype =>
    g.createKindTokens controller kind (g.countSubtype controller subtype)
  | .creaturesYouControlGetAndGrant p t k =>
    let g := g.pumpControlledCreatures controller p t
    let label :=
      match k.toList with
      | [a] => a
      | [a, b] => s!"{a} and {b}"
      | ks => String.intercalate ", " ks
    g.grantUntilEotToControlledCreatures controller k label
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
  | .mayDrawPerArtifactOppsDraw =>
    g.mayDrawPerArtifact controller
  | .mayPutHeroMvOrDraw n =>
    g.mayPutHeroOrDraw controller n
  | .maySacArtifactOrDiscardDraw cards =>
    { g with pending := .maySacArtifactOrDiscard controller cards }
      |>.logMsg s!"{(g.player controller).name} may sacrifice an artifact or discard a card. If they do, they draw {cards}"
  | .chooseTargetDoubleAndTrample =>
    g.withLegalKindPermanent controller .creatureYouControl targets
      (fun g o =>
        let p := g.power o
        let t := g.toughness o
        let g := g.applyPermanentAction o (.pump p t)
        g.grantUntilEotLogged (g.object! o.id) Keyword.trample) none none
  | .returnUpToTwoGyModal =>
    g.returnChosenGraveyardCards controller targets
  | .artifactSpellsCostLessThisTurn ty n =>
    g.grantTypeCostLessThisTurn controller ty n
  | .supertypeSpellsCostLessThisTurn s n =>
    g.grantSupertypeCostLessThisTurn controller s n

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
    -- Return immediately for this engine (next end step is modeled as a
    -- delayed return at the next end step via eagles-style bookkeeping:
    -- bounce now, then put back tapped next end).
    g.foldPermanentTargets targets (fun g o =>
      if o.controlledBy controller && !o.printed.isLand && some o.id != sourceId then
        g.exileThenReturn o "is exiled, then returned" (clearExileFields := true)
      else g)
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
  | .drawEqualSacrificedPowerThenDiscard =>
    g.drawThenBeginDiscard controller ((lastKnownPower.getD 0).toNat)
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
    let keep :=
      targets.filterMap (fun | Target.permanent id => some id | _ => none)
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.isCreature && !keep.contains o.id then
          g := g.destroyPermanent o
      return g.logMsg "Chosen creatures are kept; the rest are destroyed"
  | .blackGateUnblockable =>
    match targets[0]? with
    | some (Target.permanent oid) =>
      match g.playersWithMostLife[0]? with
      | some pid => g.applyBlackGateUnblockable oid pid
      | none => g
    | _ => g.logMsg "The target is no longer legal"
  | .burdenThenDraw =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let g := g.setObject { o with status := { o.status with burden := o.status.burden + 1 } }
      let n := (g.object! o.id).status.burden
      let g := g.logMsg s!"{o.name} gets a burden counter ({n})"
      g.draw controller n
  | .teamGain k =>
    g.grantUntilEotToControlledCreatures controller k k.joinedAnd
  | .sourceGainsIndestructibleTap =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let g := g.mapObjectStatus o (·.grantUntilEot Keyword.indestructible)
      let o := g.object! o.id
      let g := g.logMsg s!"{o.name} gains indestructible until end of turn"
      g.becomeTapped o
  | .plusOneOnEachOtherSubtype subtype n =>
    g.foldBattlefield (fun o =>
        o.controlledBy controller && o.id != sourceId.getD ⟨0⟩ && g.hasSubtype o subtype)
      (fun g o => g.mapObjectStatus o (fun s =>
        { s with plusOnePlusOne := s.plusOnePlusOne + n }))
  | .plusOneAndIndestructibleCounter =>
    g.withSourceOnBattlefield sourceId fun g o =>
      g.setObject { o with status := { o.status with
        plusOnePlusOne := o.status.plusOnePlusOne + 1
        indestructibleCounters := o.status.indestructibleCounters + 1 } }
  | .plusOneAndExtraTurn =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let g := g.setObject { o with status := { o.status with
        plusOnePlusOne := o.status.plusOnePlusOne + 1 } }
      g.logMsg s!"{(g.player controller).name} takes an extra turn after this one"
  | .plusOneX =>
    g.withSourceOnBattlefield sourceId fun g o =>
      g.addPlusOnePlusOneTo o chosenX
  | .eachOppDiscardThenPlusOne =>
    let g :=
      (g.livingOpponents controller).foldl (fun acc pl =>
        acc.beginDiscardCards #[pl.id]) g
    g.withSourceOnBattlefield sourceId fun g o =>
      g.setObject { o with status := { o.status with
        plusOnePlusOne := o.status.plusOnePlusOne + 1 } }
  | .lookAtTopPutTypes n _types =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let g := g.setObject { o with status := { o.status with
        plusOnePlusOne := o.status.plusOnePlusOne + 2 } }
      g.logLookAtTop controller n
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
    g.logLookAtTop controller n
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
        if o.zone == .stack then g.copyStackAbility o controller
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
  | .lookAtTopRevealSubtype n _subtype =>
    g.logLookAtTop controller n
  | .millThenPutSubtypeOrEnchantment n subtype =>
    g.millMayPutSubtypeOrEnchantment controller n subtype
  | .plusOneAndDoubleStrikeCounter =>
    g.plusOneAndDoubleStrike sourceId
  | .plusOneThenFightUpToOne =>
    g.plusOneThenFight controller sourceId targets
  | .plusOneAndCreateTigerGod =>
    let g :=
      g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 1)
        "The source is no longer in play"
    g.createNamedToken controller tigerGodToken
  | .plusTwoThenOddEvenDestroy =>
    let g :=
      g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 2)
        "The source is no longer in play"
    { g with pending := .fraChoice controller (.oddOrEvenDestroy sourceId) }
      |>.logMsg s!"{(g.player controller).name} chooses odd or even"
  | .returnFromGyFinalityAttach =>
    g.returnFromGyFinalityAttach controller sourceId
  | .returnGyCreatureThenPlusOne n =>
    g.returnGyCreatureThenPlusOne controller sourceId targets n
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
  | .pumpAttackingAloneGainLife =>
    g.withLegalKindPermanent controller .creatureYouControl targets (fun g o =>
      let g := g.pumpPermanent o 1 0
      g.gainLife controller 1)
      sourceId (some "The target is no longer legal. You won't gain life.")
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
  | .destroyTargetNoncreatureArtOrEnch =>
    g.withLegalKindPermanent controller .noncreatureArtifactOrEnchantment targets
      (fun g o => g.applyPermanentAction o .destroy) sourceId none
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
  | .createTokensLifeGained _ | .oppSacrificesGreatestMvGainLife _
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
