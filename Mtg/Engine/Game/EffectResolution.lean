import Mtg.Engine.Game.TriggerArgs

/-!
# Unified effect resolution (CR 608)

`applyUnified` and `applyUnifiedAbility`: the interpreters for the
unified `Effect` vocabulary shared by spells, activated abilities, and
triggered abilities.
-/

namespace Mtg.Engine
namespace Game

private def spellX (g : Game) : Nat :=
  let chosen := fun (id? : Option ObjectId) => id?.bind g.findObject? |>.bind (·.chosenX)
  (chosen g.resolvingSpell).getD ((chosen g.resolvingAbility).getD 0)

private def knownN (g : Game) : Nat :=
  ((g.resolvingAbilityObject?.bind (·.lastKnownPower)).getD 0).toNat

private def exileId (g : Game) (id : ObjectId) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    let name := o.name
    let (g, _) := g.move id .exile none
    g.logMsg s!"{name} is exiled"

private def handDiscard (g : Game) (p : PlayerId) : Game :=
  match (g.player p).hand.back? with
  | none => g.logMsg s!"{(g.player p).name} has no card to discard"
  | some id =>
    let name := (g.object! id).name
    let (g, _) := g.move id (.graveyard p) none
    g.logMsg s!"{(g.player p).name} discards {name}"

private def destroyIds (g : Game) (ids : Array ObjectId) (pred : GameObject → Bool := fun _ => true) : Game :=
  ids.foldl (fun g id =>
    match g.findObject? id with
    | some o => if o.isOnBattlefield && pred o then g.destroyPermanent o else g
    | none => g) g

private def revealUntil (g : Game) (p : PlayerId) (pred : CardDef → Bool) (limit : Nat) :
    Game × Array ObjectId × Array ObjectId :=
  Id.run do
    let mut g := g
    let mut hits : Array ObjectId := #[]
    let mut rest : Array ObjectId := #[]
    let mut fuel := (g.player p).library.size
    while hits.size < limit && fuel > 0 do
      fuel := fuel - 1
      let lib := (g.player p).library
      if lib.isEmpty then
        fuel := 0
      else
        let top := lib.back!
        let card := g.object! top
        let (g', newId) := g.move top .exile none
        g := g'.logMsg s!"{(g.player p).name} reveals {card.name}"
        if pred card.printed then hits := hits.push newId
        else rest := rest.push newId
    return (g, hits, rest)

private def putHits (g : Game) (p : PlayerId) (hits : Array ObjectId) (haste := false) : Game :=
  hits.foldl (fun g id =>
    match g.findObject? id with
    | none => g
    | some _ =>
      let (g, newId) := g.putOntoBattlefield id p (summoningSick := !haste)
      g.afterPermanentEnters (g.object! newId)) g

private def restBottom (g : Game) (p : PlayerId) (rest : Array ObjectId) (shuffle : Bool) : Game :=
  if rest.isEmpty then if shuffle then g.requestShuffle p else g
  else if shuffle then
    let g := g.moveIdsInOrder rest (.library p)
    g.requestShuffle p
  else
    g.requestOrderInto rest (.library p)
      s!"{(g.player p).name} puts the rest on the bottom of their library in a random order"

private def historicCard (c : CardDef) : Bool :=
  c.isPermanentCard && (c.isArtifact || c.hasSupertype .legendary || c.hasSubtype "Saga")

private def creatureOrWalker (c : CardDef) : Bool :=
  c.isCreature || c.isPlaneswalker

private def basicOf (kinds : Array String) (c : CardDef) : Bool :=
  isBasicLandCard c && kinds.any c.hasSubtype

private def handDiscardToBottom (g : Game) (controller : PlayerId) : Game :=
  match (g.player controller).hand.back? with
  | none => g
  | some id =>
    let name := (g.object! id).name
    let (g, newId) := g.move id (.library controller) none
    let pl := g.player controller
    let lib := pl.library.filter (· != newId)
    g.setPlayer { pl with library := #[newId] ++ lib }
      |>.logMsg s!"{(g.player controller).name} puts {name} on the bottom of their library"

/-- Reveal creature cards exiled by Synthetic Destiny at the end step. -/
def applyDelayedSynthetic (g : Game) : Game :=
  let synth := g.delayedSynthetic
  let g := { g with delayedEndStep := g.delayedEndStep.filter fun
    | .syntheticDestiny .. => false
    | _ => true }
  synth.foldl (fun g (who, n) =>
    let (g, hits, rest) := g.revealUntil who (·.isCreature) n
    let g := g.putHits who hits
    g.restBottom who rest true) g

/-- Keyword coded by `code` in `Resolution.chooseKeyword`. -/
def fraKeywordOfCode : Nat → Keywords
  | 0 => Keyword.trample
  | 1 => Keyword.hexproof
  | 2 => Keyword.haste
  | 3 => Keyword.deathtouch
  | _ => Keywords.none

/-- Name of the keyword coded by `code`. -/
def fraKeywordName : Nat → String
  | 0 => "trample"
  | 1 => "hexproof"
  | 2 => "haste"
  | 3 => "deathtouch"
  | _ => "nothing"

/-- Ask `p` which of `options` the permanent `id` gains until end of turn. -/
def beginChooseKeyword (g : Game) (p : PlayerId) (id : ObjectId) (options : Array Nat) : Game :=
  match g.findObject? id with
  | some o =>
    if !o.isOnBattlefield then g
    else
      let names := String.intercalate ", " (options.toList.map fraKeywordName)
      g.beginFraChoice p (.chooseKeyword id options)
        s!"{(g.player p).name} chooses {names} for {o.name}"
  | none => g

/-- Give `p` an emblem or effect object in the command zone (CR 114). -/
def createCommandObject (g : Game) (p : PlayerId) (card : CardDef)
    (untilTurnOf : Option PlayerId := none) : Game :=
  let (g, obj) := g.allocObject card p .command (some p)
  g.setObject { obj with fraEffectUntilTurnOf := untilTurnOf }

/-- Ask the next player in `players` to sacrifice a creature for Garruk,
Veiled Butcher, or sacrifice the chosen creatures and finish. -/
def continueSacrificeEach (g : Game) (controller : PlayerId) (players : Array PlayerId)
    (chosen : Array ObjectId) : Game :=
  match (players.filter (fun p => !(g.creaturesControlledBy p).isEmpty)).toList with
  | p :: rest =>
    g.beginFraChoice p (.sacrificeCreatureEach controller rest.toArray chosen)
      s!"{(g.player p).name} sacrifices a creature"
  | [] =>
    let youSacrificed := chosen.any (fun id =>
      (g.findObject? id).any (fun o => o.controlledBy controller))
    let g := chosen.foldl (fun g id =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield then
          g.sacrificeToGraveyard o s!"{(g.player (o.controller.getD o.owner)).name} sacrifices {o.name}"
        else g
      | none => g) g
    if youSacrificed then g.createKindTokens controller .beast44trample 1 else g

/-- Ask the next opponent in `players` to discard two cards for Garruk,
Veiled Butcher, or draw `draws` cards for `controller` and finish. -/
partial def continueDiscardTwo (g : Game) (controller : PlayerId) (players : Array PlayerId)
    (draws : Nat) : Game :=
  match players.toList with
  | [] => g.draw controller draws
  | p :: rest =>
    let hand := (g.player p).hand
    if hand.size ≤ 2 then
      let nonland := (hand.filter (fun id => !(g.object! id).printed.isLand)).size
      let g := hand.foldl (fun g id => g.discardFromHand p id) g
      let g :=
        if hand.isEmpty then g.logMsg s!"{(g.player p).name} has no cards to discard" else g
      g.continueDiscardTwo controller rest.toArray (if nonland < 2 then draws + 1 else draws)
    else
      g.beginFraChoice p (.discardTwo controller rest.toArray draws)
        s!"{(g.player p).name} discards two cards"

/-- Creatures attacking `p` directly (not a planeswalker). -/
def creaturesAttackingPlayer (g : Game) (p : PlayerId) : Array GameObject :=
  g.battlefield.filter (fun o =>
    o.isCreature && o.status.attacking && o.status.attackingWhom == some p &&
      o.status.attackingPlaneswalker.isNone)

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
              { g with afterLibrarySearch := .plusOneOn id }
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

/-- Spells matching `which` cost `{n}` less this turn (CR 601.2f). -/
def grantSpellsCostLessThisTurn (g : Game) (p : PlayerId) (which : SpellCostLess) (n : Nat) : Game :=
  let kind := match which with | .supertype s => toString s | .spellCostLessKind ty _ => toString ty
  g.modifyPlayer p (fun pl =>
    { pl with spellsCostLessThisTurn := pl.spellsCostLessThisTurn.push (which, n) })
    |>.logMsg s!"{kind} spells {(g.player p).name} casts this turn cost \{{n}} less"

/-- Spells of type `ty` cost `{n}` less this turn. -/
def grantTypeCostLessThisTurn (g : Game) (p : PlayerId) (ty : CardType) (n : Nat) : Game :=
  g.grantSpellsCostLessThisTurn p (.cardType ty) n

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
    let g := g.mapObjectStatus o (·.addCounters .doubleStrike 1)
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
  | _ => g

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
  | .attach .equipmentYouControl .target =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      { g.clearMay with pending := .mayAttachEquipment controller o.id }.logMsg
        s!"{(g.player controller).name} may attach an Equipment to {o.name}")
  | r =>
    let phrase := SpellResolution.toPhrase r effect.targeting.kind.noun
    let phrase := if phrase.startsWith "you " then (phrase.drop 4).toString else phrase
    let inner := { effect with resolution := r }
    { g with
        pending := .mayResolve controller
        mayEffectState := { effect := some inner, controller, targets } }.logMsg
      s!"{(g.player controller).name} may {phrase}"

/-- Ask a player to choose one resolution in `rs`. A library top-or-bottom
pair is the owner's choice; any other list is the caster's. One alternative
is applied by `applyUnified` before this is called. -/
def beginSpellOr (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (rs : List SpellResolution) : Game :=
  let asEffect (r : SpellResolution) : Effect :=
    { effect with resolution := r }
  let g := g.clearSpellOr
  match rs with
  | [.putOnLibrary .top .target, .putOnLibrary .bottom .target]
  | [.putOnLibrary .bottom .target, .putOnLibrary .top .target] =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield then
          { g with
              pending := .chooseLibraryPlacement o.owner id
              spellOrState := {
                effects := #[
                  asEffect (.onPermanent .putOnTopOfLibrary),
                  asEffect (.onPermanent .putOnBottomOfLibrary)]
                controller
                targets
                isLibrary := true } }.logMsg
            s!"{(g.player o.owner).name} chooses top or bottom of their library for {o.name}"
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | _ =>
    { g with
        pending := .chooseLibraryPlacement controller ⟨g.nextObjectId⟩
        spellOrState := {
          effects := (rs.map asEffect).toArray
          controller
          targets
          isLibrary := false } }.logMsg
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
      match g.findObject? (g.followMoved id) with
      | none => g.logMsg "The target is no longer legal"
      | some o =>
        let mv := o.printed.manaValue + o.chosenX.getD 0
        if mv ≤ n then whenHolds g else whenNot g
    | _ => g.logMsg "The target is no longer legal"
  | .castFromGraveyard =>
    if castFromGraveyard then whenHolds g else whenNot g
  | .teamwork =>
    if g.resolvingTeamworkPaid then whenHolds g else whenNot g
  | .giftPromised =>
    if giftPromised then whenHolds g else whenNot g
  | .notFromHand =>
    let fromHand := (g.resolvingSpell.bind g.findObject?).any (·.castFromHand)
    if !fromHand then whenHolds g else whenNot g
  | _ => whenNot g

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
    let g := { g with discardReq := { g.discardReq with plusOneAfterDiscards := none } }
    match g.findObject? (g.followMoved id) with
    | some o =>
      if o.isOnBattlefield then g.addPlusOnePlusOneTo o 1 else g
    | none => g

/-- Apply `act` to the first targeted creature in `targets` if still on the battlefield. -/
private def applyCreatureTargetAction (g : Game) (targets : Array Target) (act : PermanentAction) : Game :=
  match targets.findSome? (fun | Target.permanent id => some id | _ => none) with
  | some id =>
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield && o.isCreature then g.applyPermanentAction o act
      else g.logMsg "The target is no longer legal"
    | none => g.logMsg "The target is no longer legal"
  | none => g.logMsg "The target is no longer legal"

/-- Fallback for `applyUnified` when no specialized arm matches (`onPermanent?` / `onSource?`). -/
def applyUnifiedFallback (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (sourceId : Option ObjectId := none)
    (isAbility : Bool := false) : Game :=
  let r := effect.resolution
  match r.onPermanent? with
  | some a => g.applyOnPermanent controller effect.targetKind targets a sourceId
  | none =>
    match r.onSource? with
    | some a =>
      if isAbility then g.applyOnSource sourceId a
      else g.applyOnPermanent controller effect.targetKind targets a
    | none =>
      if isAbility then g
      else g.logMsg "The effect does nothing"

/-- Resolve a `.pump` `Effect` (CR 613.4c). -/
def applyUnifiedPump (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .pump (.count .artifact) (.fixed 0) who@(.creaturesYouControl)
  | .pump (.count .artifact) (.fixed 0) who@(.source) =>
    let ctx : TriggerRead := { controller, sourceId, targets }
    match g.triggerInt ctx (.count .artifact), g.permanentsNamed ctx who with
    | some n, some objs =>
      objs.foldl (fun g o =>
        match g.findObject? o.id with
        | some o => if o.isOnBattlefield then g.pumpPermanent o n 0 else g
        | none => g) g
    | _, _ => g
  | .pump .causePower (.fixed 0) .source =>
    let x : Int :=
      match g.fraCause? with
      | some o => if o.isOnBattlefield then g.power o
                  else (g.resolvingAbilityObject?.bind (·.fraCausePower)).getD 0
      | none => (g.resolvingAbilityObject?.bind (·.fraCausePower)).getD 0
    match sourceId.bind g.findObject? with
    | some o => if o.isOnBattlefield then g.pumpPermanent o x 0 else g
    | none => g
  | .pump amt@(.minusGraveyardCards) (.fixed 0) .target
  | .pump amt@(.count .artifact) (.fixed 0) .target =>
    match g.triggerInt { controller, sourceId, targets } amt with
    | some n =>
      g.withLegalKindPermanent controller kind targets (fun g o => g.pumpPermanent o n 0)
        sourceId illegal
    | none => g
  | .pump _ _ (.battlefield (.attackersFilter true againstOpponents)) =>
    let effectCard : CardDef :=
      if againstOpponents then {
        name := s!"{srcName} effect", types := #[]
        triggeredAbilities := #[TriggeredAbility.fra (.fra .creaturesAttackYourOpponent)
          "Whenever one or more creatures attack one of your opponents, those creatures get +2/+2 and gain trample until end of turn."
          (.pump (.fixed 2) (.fixed 2) .attackersOfCauseControllerWithTrample)] }
      else {
        name := s!"{srcName} effect", types := #[]
        triggeredAbilities := #[TriggeredAbility.fra (.fra .creatureAttacksYouOrYourPlaneswalker)
          "Whenever a creature attacks you or a planeswalker you control, it gets -5/-0 until end of turn."
          (.pump (.fixed (-5)) (.fixed 0) .cause)] }
    let msg :=
      if againstOpponents then
        s!"Until {pl.name}'s next turn, creatures attacking their opponents get +2/+2 and gain trample"
      else
        s!"Until {pl.name}'s next turn, whenever a creature attacks them or a planeswalker they control, it gets -5/-0 until end of turn"
    (g.createCommandObject controller effectCard (untilTurnOf := some controller)).logMsg msg
  | .pump (.fixed (-4)) (.fixed (-1)) (.target .untilYourNextTurn) =>
    if targets.isEmpty then g
    else
      g.withLegalKindPermanent controller kind targets (fun g o =>
        (g.mapObjectStatus o (fun s =>
          { s with untilTurnOfPump := s.untilTurnOfPump.push (controller, -4, -1) })).logMsg
          s!"{o.name} gets -4/-1 until {(g.player controller).name}'s next turn") sourceId illegal
  | .pump (.fixed p) (.fixed t) (.cause none) =>
    match g.fraCause? with
    | some o => if o.isOnBattlefield then g.pumpPermanent o p t else g
    | none => g
  | .pump (.fixed 2) (.fixed 2) .attackersOfCauseControllerWithTrample =>
    match g.fraCauseController? with
    | some defender =>
      (g.creaturesAttackingPlayer defender).foldl (fun g o =>
        let g := g.pumpPermanent (g.object! o.id) 2 2
        g.grantKeywordsUntilEot (g.object! o.id) Keyword.trample) g
    | none => g
  | .pump (.fixed p) (.fixed t) .creaturesYouControl =>
    g.pumpControlledCreatures controller p t
  | .pump (.fixed p) (.fixed t) .allCreatures =>
    g.foldBattlefield (fun o => o.isCreature) (fun g o => g.pumpPermanent o p t)
  | .pump (.fixed p) (.fixed t) .creaturesOfTargetPlayer =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.pumpControlledCreatures pid p t)
  | .pump (.fixed p) (.fixed t) .creatureTargets =>
    g.applyCreatureTargetAction targets (.pump p t)
  | _ => fallback g

/-- Resolve a `.dealDamage` `Effect` (CR 120), part 1. -/
def applyUnifiedDamage1 (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .dealDamage (.power (.targetAt 0)) (.targetAt 1) _
  | .dealDamage (.loyalty (.targetAt 0)) (.targetAt 1) _ =>
    -- Ruling 791: the power or loyalty is checked as the spell resolves; if
    -- that permanent is gone, no damage is dealt.
    let useLoyalty :=
      match effect.resolution with
      | .dealDamage (.loyalty _) .. => true
      | _ => false
    let kinds := effect.targetKind.spec.slots
    let legalAt (i : Nat) (t : Target) : Bool :=
      match kinds[i]? with
      | some k => (g.legalTargetsForAtomicKind controller k none).contains t
      | none => false
    match targets[0]?, targets[1]? with
    | some (Target.permanent srcId), some (Target.permanent dstId) =>
      if !legalAt 0 (Target.permanent srcId) then
        g.logMsg "The first target is no longer legal. No damage is dealt"
      else if !legalAt 1 (Target.permanent dstId) then
        g.logMsg "The second target is no longer legal. No damage is dealt"
      else
        let src := g.object! srcId
        let dst := g.object! dstId
        let n : Int := if useLoyalty then Int.ofNat src.status.loyaltyCounters else g.power src
        g.dealDamageFrom src.name dst (max n 0) (source := some src)
    | _, _ => g.logMsg "The targets are no longer legal"
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
  | .dealDamage (.fixed n) who@(.oppCreaturesAndPlaneswalkers) _
  | .dealDamage (.fixed n) who@(.creaturesExceptYourTokens) _ =>
    match g.permanentsNamed { controller, sourceId, targets } who with
    | some victims =>
      victims.foldl (fun g o =>
        match g.findObject? o.id with
        | some o => if o.isOnBattlefield then g.dealDamageFrom srcName o n.toNat (source := src?) else g
        | none => g) g
    | none => g
  | .dealDamage amt@(.power (.targetAt fromIdx)) (.targetAt toIdx) _
  | .dealDamage amt@(.loyalty (.targetAt fromIdx)) (.targetAt toIdx) _ =>
    match g.legalPermanentAt? controller kind targets toIdx sourceId,
        g.legalPermanentAt? controller kind targets fromIdx sourceId with
    | some victim, some striker =>
      let dmg := match amt with
        | .loyalty _ => Int.ofNat striker.status.loyaltyCounters
        | _ => max (g.power striker) 0
      g.dealDamageFrom striker.name (g.object! victim.id) dmg
        (source := some striker)
    | _, _ => g.logMsg "The target is no longer legal. No damage is dealt"
  | .dealDamage .chosenX .target _ =>
    let x := (sourceId.bind g.findObject?).bind (·.chosenX) |>.getD 0
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.player pid => g.dealDamageToPlayer pid x (source := src?)
      | Target.permanent id => g.dealDamageFrom srcName (g.object! id) x (source := src?)
      | Target.card _ => g) sourceId illegal
  | .dealDamage (.fixed n) (.player .eachOpponent) .fromCause =>
    let cause := g.fraCause?
    let name := (cause.map (·.name)).getD "The creature"
    g.forEachOpponent controller (fun g pid =>
      (g.dealDamageToPlayer pid n.toNat (source := cause)).logMsg s!"{name} deals {n.toNat} damage")
  | _ => fallback g

/-- Resolve a `.dealDamage` `Effect` (CR 120), part 2. -/
def applyUnifiedDamage2 (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (recurse : Game → Effect → Array Target → Bool → Bool → Bool → Nat → Option ObjectId → Option Int → Bool → Game)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .dealDamage (.fixed n) (.player (.controller .cause)) _ =>
    match g.fraCauseController? with
    | some pid => g.dealDamageToPlayer pid n.toNat (source := src?)
    | none => g
  | .dealDamage (.fixed 1) (.player .eachOpponent) .addRedIfMountain =>
    let g := g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid 1 (source := src?))
    match g.fraCause? with
    | some land => if g.hasSubtype land "Mountain" then g.addManaLogged controller #[.colored .red] else g
    | none => g
  | .dealDamage .equalSourcePower .target _ | .dealDamage (.power .source) .target _ =>
    let n :=
      match sourceId.bind g.findObject? with
      | some o => (g.power o).toNat
      | none => 0
    let srcName := (sourceId.bind g.findObject?).map (·.name) |>.getD "The creature"
    g.withLegalKindPermanent controller .creature targets (fun g o =>
      g.dealDamageFrom srcName o n (source := sourceId.bind g.findObject?))
      sourceId illegal
  | .dealDamage (.fixed n) (.player .eachOpponent) .none =>
    let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
    g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid n.toNat (source := src?))
  | .dealDamage (.fixed n) .target _ =>
    if !isAbility then
      g.applyDamageToKindTarget controller effect.targetKind targets n.toNat none
        (some "The target is no longer legal")
    else if effect.targetKind == .creature && effect.phrase.startsWith "This creature deals" then
      g.applyOnPermanent controller effect.targetKind targets (.dealDamage n.toNat) sourceId
    else if effect.targetKind == .playerOrCreature && sourceId.isSome then
      recurse g (Effect.dealDamage n.toNat) targets false false false 0 none none false
    else
      let srcName := g.fraSourceName sourceId
      let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
      g.withLegalKindTarget controller effect.targetKind targets (fun g t =>
        match t with
        | Target.player pid => g.dealDamageToPlayer pid n.toNat (source := src?)
        | Target.permanent id => g.dealDamageFrom srcName (g.object! id) n.toNat (source := src?)
        | Target.card _ => g) sourceId (some "The target is no longer legal")
  | .dealDamage amount .allCreatures _
  | .dealDamage amount .opponentsCreatures _
  | .dealDamage amount (.nonSubtypeCreatures _) _ =>
    let n := match amount with
      | .fixed k => k.toNat
      | .otherSpellsManaValue => g.otherSpellsManaValue controller
      | _ => 0
    match effect.resolution with
    | .dealDamage _ .allCreatures _ => g.dealDamageToEachCreatureMatching n
    | .dealDamage _ .opponentsCreatures _ =>
      let g := g.dealDamageToEachCreatureMatching n (fun o => !o.controlledBy controller)
      if amount == .otherSpellsManaValue then
        g.logMsg s!"deals {n} damage to each opposing creature"
      else g
    | .dealDamage _ (.nonSubtypeCreatures subtype) _ => g.dealDamageToEachNonDragon n subtype
    | _ => g
  | .dealDamage (.fixed n) (.player (.controller .target)) _ =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? (g.followMoved id) with
      | some o =>
        let pid? :=
          if o.zone == .battlefield then o.controller
          else o.lastController.orElse (fun _ => o.controller)
        match pid? with
        | some pid => g.dealDamageToPlayer pid n.toNat
        | none => g
      | none => g
    | _ => g
  | _ => fallback g

/-- Resolve a `.putCounters` `Effect` (CR 122 / CR 701.34), part 1. -/
def applyUnifiedCounters1 (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .putCounters (.ofKind .stun _) .combatDamagerIfMonarch =>
    if !(g.player controller).isMonarch then g
    else
      match g.fraCause? with
      | some o =>
        if o.isOnBattlefield && o.isCreature then
          let g := g.becomeTapped o
          let n := g.countersYouPut (g.object! o.id) 1 (putter := some controller)
          g.mapObjectStatus (g.object! o.id) (fun s => { s with stun := s.stun + n })
            |>.logMsg s!"{o.name} gets a stun counter"
        else g
      | none => g
  | .putCounters (.ofKind .story _) .source =>
    match source? with
    | some o =>
      g.mapObjectStatus o (fun s => { s with story := s.story + 1 })
        |>.logMsg s!"{o.name} gets a story counter"
    | none => g
  | .putCounters (.ofKind .plusOnePlusOne n) (.targetAt index) =>
    match g.legalPermanentAt? controller kind targets index sourceId with
    | some o => g.addPlusOnePlusOneTo o n
    | none => g
  | .putCounters (.ofKind .plusOnePlusOne n) (.target .eachPermanent) =>
    targets.foldl (fun g t =>
      match t with
      | Target.permanent id =>
        if g.targetLegalAt controller kind 0 t sourceId then
          g.addPlusOnePlusOneTo (g.object! id) n
        else g.illegalAbilityTarget t
      | _ => g) g
  | .putCounters (.ofKind .plusOnePlusOne n) who@(.wizardTokensExceptRecent)
  | .putCounters (.ofKind .plusOnePlusOne n) who@(.creaturesWithPlusOne) =>
    match g.permanentsNamed { controller, sourceId, targets } who with
    | some objs =>
      (objs.map (·.id)).foldl (fun g id =>
        match g.findObject? id with
        | some o => if o.isOnBattlefield then g.addPlusOnePlusOneTo o n else g
        | none => g) g
    | none => g
  | .putCounters .plusOnePerThreeGraveyardIfFromGy .createdToken =>
    let fromGy := (g.resolvingSpell.bind g.findObject?).any (·.castFromGraveyard)
    let counters := if fromGy then (g.player controller).graveyard.size / 3 else 0
    if counters == 0 then g
    else
      g.recentTokenIds.foldl (fun g id =>
        match g.findObject? id with
        | some o => if o.isOnBattlefield then g.addPlusOnePlusOneTo o counters else g
        | none => g) g
  | .putCounters (.ofKind .plusOnePlusOne 1) (.creaturesControlledBy (.targetAt index)) =>
    match targets[index]? with
    | some t@(Target.player pid) =>
      if g.targetLegalAt controller kind index t sourceId then
        (g.creaturesControlledBy pid).foldl (fun g o => g.addPlusOnePlusOneTo o 1) g
      else g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | .putCounters .plusOneEqualToHand .creaturesYouControl =>
    let x := (g.player controller).hand.size
    if x == 0 then g
    else
      ((g.creaturesControlledBy controller).map (·.id)).foldl (fun g id =>
        match g.findObject? id with
        | some o => g.addPlusOnePlusOneTo o x
        | none => g) g
  | .putCounters (.ofKind .loyalty _) .planeswalkersYouControl => g.loyaltyOnEachPlaneswalkerOf controller
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
  | .removeCounters (.upTo n) .target =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      g.removeUpToCountersFrom controller o n) sourceId illegal
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
  | _ => fallback g

/-- Resolve a `.putCounters` `Effect` (CR 122 / CR 701.34), part 2. -/
def applyUnifiedCounters2 (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .putCounters .stunRemovedLoyalty .target =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let g := if o.status.tapped then g else g.becomeTapped o
      if chosenX == 0 then g
      else
        let n := g.countersYouPut (g.object! o.id) chosenX (putter := some controller)
        (g.mapObjectStatus (g.object! o.id) (fun s => { s with stun := s.stun + n })).logMsg
          s!"{n} stun counter(s) are put on {o.name}") sourceId illegal
  | .putCounters .plusOnePerLand .target =>
    let n := ((g.permanentsOf controller).filter (·.printed.isLand)).size
    g.withLegalKindPermanent controller kind targets (fun g o =>
      if n == 0 then g else g.addPlusOnePlusOneTo o n) sourceId illegal
  | .putCounters .causeCounters .source =>
    match g.resolvingAbilityObject?.bind (·.fraCauseStatus), source? with
    | some st, some o =>
      if !o.isOnBattlefield then g
      else
        let g := g.setObject { o with status := o.status.addCountersExceptPlusOne st }
        let g := if st.plusOnePlusOne > 0 then g.addPlusOnePlusOneTo (g.object! o.id) st.plusOnePlusOne else g
        g.logMsg s!"Counters are put on {o.name}"
    | _, _ => g
  | .proliferate amount .youControl =>
    match g.triggerCount { controller, sourceId, targets } amount with
    | some times =>
      if times == 0 then
        if amount == .planeswalkerTypes then
          g.logMsg s!"{(g.player controller).name} controls no planeswalker types. X is 0"
        else g
      else
        { g with pending := .chooseProliferate controller times }.logMsg
          s!"{(g.player controller).name} proliferates {times} time(s)"
    | none => g
  | .putCounters (.ofKind kind n) .firstTargetCreatureYouControl =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield && o.isCreature && o.controlledBy controller then
          g.addCounters o kind n
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | .putCounters (.ofKind kind n) .creatureTargets =>
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
  | .putCounters (.ofKind .plusOnePlusOne n) (.youControl .eachCreature) =>
    g.forEachControlledCreature controller
      (fun g o => g.addPlusOnePlusOneTo o n) none
  | .putCounters (.ofKind .plusOnePlusOne n) .eachOther =>
    let exclude :=
      match targets[0]? with
      | some (Target.permanent oid) => some oid
      | _ => none
    g.forEachControlledCreature controller
      (fun g o => g.addPlusOnePlusOneTo o n) exclude
  | .putCounters (.ofKind .plusOnePlusOne n) .permanent =>
    g.withLegalKindPermanent controller effect.targetKind targets
      (fun g o => g.addPlusOnePlusOneTo o n)
  | .putCounters (.ofKind .shadow _) .target =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      g.putShadowCounter o) sourceId (some "The target is no longer legal")
  | .putCounters (.ofKind .plusOnePlusOne n) (.othersOfSubtype subtype) =>
    g.foldBattlefield (fun o =>
        o.controlledBy controller && o.id != sourceId.getD ⟨0⟩ && g.hasSubtype o subtype)
      (fun g o => g.addPlusOnePlusOneTo o n)
  | .putCounters .plusOneChosenX .source =>
    g.withSourceOnBattlefield sourceId fun g o =>
      g.addPlusOnePlusOneTo o chosenX
  | .proliferate (.fixed 1) .target =>
    g.proliferateTarget controller targets
  | _ => fallback g

/-- Resolve a `.scry`, `.surveil`, or `.mill` `Effect` (CR 701.13 / CR 701.18 / CR 701.25). -/
def applyUnifiedScryOrMill (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .surveil (.fixed n) .none => g.beginSurveil controller n.toNat
  | .mill (.fixed n) .you .none => g.mill controller n.toNat
  | .mill .lastKnownPower .eachPlayer .freeCastFromGraveyard =>
    let n := g.knownN
    g.livingPlayers.foldl (fun g q =>
      Id.run do
        let mut g := g
        for _ in [0:n] do
          let lib := (g.player q.id).library
          if lib.isEmpty then
            g := g.logMsg s!"{q.name} mills nothing (empty library)"
          else
            let top := lib.back!
            let name := (g.object! top).name
            let (g', newId) := g.move top (.graveyard q.id) none
            g := g'.logMsg s!"{q.name} mills {name}"
            match g.findObject? newId with
            | some card =>
              g := g.setObject { card with status := { card.status with freeCastFromGraveyard := true } }
            | none => pure ()
        return g) g
  | .surveil (.fixed 1) .eyeOfJace =>
    let g := g.beginSurveil controller 1
    match g.pending with
    | .surveil .. => { g with afterScrySurveil := { g.afterScrySurveil with fraAfterLook := some (controller, sourceId, .sacrifice .source .eyeOfJaceIfSevenInGy) } }
    | _ =>
      if (g.player controller).graveyard.size < 7 then g
      else
        match sourceId.bind g.findObject? with
        | some o =>
          if !o.isOnBattlefield then g
          else
            let g := g.sacrificeToGraveyard o s!"{(g.player controller).name} sacrifices {o.name}"
            g.drainOpponents controller 2 (some o)
        | none => g
  | .surveil (.fixed 1) .returnNoncreatureNonland =>
    let g := g.beginSurveil controller 1
    match g.pending with
    | .surveil .. => { g with afterScrySurveil := { g.afterScrySurveil with surveilReturnNoncreatureNonland := true } }
    | _ => g
  | .scry (.fixed n) =>
    g.beginScry controller n.toNat
  | .mill (.fixed n) _ (.toHand which) =>
    match which with
    | .oneOf a b =>
      g.millThenChooseForHand controller n.toNat
        (fun o => o.printed.hasType a || o.printed.hasType b) 1 true
    | .upTo max ty =>
      g.millThenChooseForHand controller n.toNat (fun o => o.printed.hasType ty) max false
    | .milledPickKind a b _ _ =>
      g.millThenPutFromGy controller n.toNat
        (fun o => o.printed.hasType a || o.printed.hasType b)
  | .mill (.fixed n) _ (.permanentAndGainLife life) =>
    g.millMayPutPermanentGainLife controller n.toNat life
  | .mill (.fixed n) .player _ =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.mill pid n.toNat)
  | .mill (.fixed n) .you (.subtypeOrEnchantmentToHand subtype) =>
    g.millMayPutSubtypeOrEnchantment controller n.toNat subtype
  | _ => fallback g

/-- Resolve a `.draw`, `.gainLife`, or `.loseLife` `Effect` (CR 118 / CR 121). -/
def applyUnifiedDrawOrLife (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .loseLife (.fixed 1) .eachOpponentAndYouGain1 =>
    let g := g.forEachOpponent controller (fun g pid => g.loseLife pid 1)
    g.gainLife controller 1
  | .loseLife .lifeLostThisTurn .eachOpponent =>
    g.forEachOpponent controller fun g pid =>
      g.loseLife pid (g.player pid).lifeLostThisTurn
  | .draw .milledByTargetPlayerThisTurn _ =>
    g.withLegalKindPlayer controller kind targets (fun g pid =>
      g.draw controller (g.player pid).cardsMilledThisTurn) sourceId illegal
  | .draw .greatestPowerAndLoseLife _ =>
    let n := (g.greatestPowerAmongCreatures controller).toNat
    let before := (g.player controller).cardsDrawnThisTurn
    let g := g.draw controller n
    let drawn := (g.player controller).cardsDrawnThisTurn - before
    g.loseLife controller drawn
  | .loseLife (.fixed 1) .extort =>
    g.beginFraChoice controller (.mayPayExtort sourceId)
      s!"{(g.player controller).name} may pay \{W/B} (extort)"
  | .draw .perBurden _ =>
    g.withSourceOnBattlefield sourceId fun g o => g.draw controller o.status.burden
  | .loseLife (.fixed n) .player =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.loseLife pid n.toNat)
  | .loseLife (.fixed n) .you
  | .loseLife (.fixed n) .eachOpponent
  | .loseLife (.fixed n) (.controller .target) =>
    let who := match effect.resolution with | .loseLife _ w => w | _ => .you
    match g.collectPlayers { controller, sourceId, targets } who with
    | some pids => pids.foldl (fun g pid => g.loseLife pid n.toNat) g
    | none => g
  | .gainLife (.fixed n) .you => g.gainLife controller n.toNat
  | .draw (.fixed _) .you
  | .draw (.perControlled .creature) _
  | .draw .colorsAmongOtherArtifacts _
  | .draw .cardsDiscardedThisTurn _
  | .draw .lastKnownPower _ =>
    let amt := match effect.resolution with | .draw a _ => a | _ => .fixed 0
    match g.triggerCount { controller, sourceId, targets, lastKnownPower } amt with
    | some n => g.draw controller n
    | none => g
  | .draw (.fixed n) .player =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.draw pid n.toNat)
  | .gainLife (.fixed n) .player =>
    Id.run do
      let playerLegal := g.legalTargetsForAtomicKind controller .player none
      let mut g := g
      for t in targets do
        match t with
        | Target.player pid =>
          if playerLegal.contains t then
            g := g.gainLife pid n.toNat
          else
            g := g.illegalAbilityTarget t
        | _ => pure ()
      return g
  | .draw .greatestToughnessThenPutCreatures _ =>
    let greatest :=
      (g.permanentsOf controller).foldl (fun acc o =>
        if o.isCreature then max acc (g.toughness o).toNat else acc) 0
    let g := g.draw controller greatest
    let creatures :=
      (g.player controller).hand.filter (fun id =>
        (g.findObject? id).any (·.printed.isCreature))
    g.offerCardChoice controller creatures creatures.size .creaturesToBattlefield
      s!"{(g.player controller).name} may put any number of creature cards from their hand onto the battlefield"
  | .draw (.fixed 1) .targetPlayers =>
    match targets[0]?, targets[1]? with
    | some (Target.player a), some (Target.player b) =>
      if a == b then g.logMsg "Two target players must be different"
      else g.draw a 1 |>.draw b 1
    | _, _ => g.logMsg "The targets are no longer legal"
  | .draw .chosenX _ =>
    g.draw controller chosenX
  | _ => fallback g

/-- Resolve a `.createOrAmass` `Effect` (CR 111.10 / CR 701.47). -/
def applyUnifiedCreateOrAmass (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .createTokens .citizen .chosenX false _ .teamIndestructible =>
    let g := g.createKindTokens controller .citizen g.spellX
    g.grantUntilEotToControlledCreatures controller Keyword.indestructible "indestructible"
  | .createTokens .soldier11white .chosenX false _ .destroyOthersIfXAtLeast5 =>
    let x := g.spellX
    let g := g.createKindTokens controller .soldier11white x
    if x >= 5 then
      g.destroyIds (g.battlefield.filter (·.isCreature) |>.map (·.id))
        (fun o => !g.recentTokenIds.contains o.id)
    else g
  | .createTokens .mite .chosenX false _ .gainXLifeAndDestroyOthersIf5 =>
    let x := g.spellX
    let g := g.gainLife controller x
    let g := g.createKindTokens controller .mite x
    if x >= 5 then
      g.destroyIds (g.battlefield.filter (·.isCreature) |>.map (·.id))
        (fun o => !g.recentTokenIds.contains o.id)
    else g
  | .createTokens .angel (.fixed 1) false _ .ifGainedLife =>
    if (g.player controller).lifeGainedThisTurn > 0 then g.createKindTokens controller .angel else g
  | .createTokens .gingerbrute (.fixed 1) false _ .ifMonarch =>
    if (g.player controller).isMonarch then g.createKindTokens controller .gingerbrute else g
  | .createTokens .goblin (.fixed 1) false _ .ifNotMarduLifelinkHaste =>
    match source? with
    | some src =>
      if src.status.windcragMardu then g
      else
        let g := g.createKindTokens controller .goblin
        match (g.permanentsOf controller).reverse.find? (fun o => o.name == "Goblin" && o.printed.isToken) with
        | some tok =>
          g.mapObjectStatus tok (fun s =>
            s.grantUntilEot (Keywords.merge Keyword.lifelink Keyword.haste))
            |>.logMsg s!"{tok.name} gains lifelink and haste until end of turn"
        | none => g
    | none => g
  | .createTokens .rogue (.fixed 1) false _ .currencyReturn =>
    match source? with
    | none => g
    | some src =>
      match src.linkedExile.find? (fun id => (g.findObject? id).any (·.zone == .exile)) with
      | none => g.logMsg s!"{src.name} has no exiled card"
      | some id =>
        match g.findObject? id with
        | none => g
        | some card =>
          let land := card.printed.isLand
          let (g, _) := g.move id (.graveyard card.owner) none
          let cur := g.object! src.id
          let g := g.setObject { cur with exileLinks :=
            { cur.exileLinks with linkedExile := src.linkedExile.filter (· != id) } }
          if land then g.createKindTokens controller .treasure else g.createKindTokens controller .rogue
  | .amass (.fixed 1) "Zombie" false .youLose1Life =>
    (g.loseLife controller 1).amassZombies controller 1
  | .createTokens .shark .spellManaValue false _ _ =>
    let x :=
      match g.fraCause? with
      | some spell => g.objectManaValue spell
      | none => 0
    g.createKindTokens controller .shark 1 (size := x)
  | .createTokens .shark .lastKnownPower false _ _ =>
    g.createKindTokens controller .shark 1 (size := g.knownN)
  | .createTokens .mite (.fixed 1) false _ .lose1Life =>
    (g.loseLife controller 1).createKindTokens controller .mite
  | .createTokens .tigerGod (.fixed 1) false _ _ => g.createNamedToken controller tigerGodToken
  | .amass (.fixed n) subtype =>
    g.amass controller subtype n.toNat
  | .createTokens .galactus _ _ _ _ =>
    g.createNamedToken controller galactusToken
  | .createTokens kind amount tapped who _ =>
    let pid := match who with
      | .you => controller
      | .player =>
        match targets[0]? with
        | some (Target.player p) => p
        | _ => controller
      | _ => controller
    let count := match amount with
      | .fixed n => n.toNat
      | .chosenX | .removedPlusOnes => chosenX
      | .perSubtype subtype => g.countSubtype pid subtype
      | .lifeGainedThisTurn => (g.player controller).lifeGainedThisTurn
      | _ => 0
    g.createKindTokens pid kind count (tapped := tapped)
  | _ => fallback g

/-- Resolve a `.tap`, `.untap`, or `.discard` `Effect` (CR 701.8 / CR 701.21). -/
def applyUnifiedTapOrDiscard (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .discard .drawAndDiscardXCreateSpiritPerType =>
    let x := g.spellX
    let g := g.draw controller x
    let hand := (g.player controller).hand
    let n := min x hand.size
    let ids := hand.extract (hand.size - n) hand.size
    let discarded := ids.filterMap g.findObject?
    let g := ids.foldl (fun g id => (g.move id (.graveyard controller) none).1) g
    let types := discarded.foldl (fun acc o =>
      o.printed.types.foldl (fun acc t =>
        let name := CardType.englishName t
        if acc.contains name then acc else acc.push name) acc) (#[] : Array String)
    g.createKindTokens controller .spirit types.size
  | .discard .drawOneDiscardOne =>
    let g := g.draw controller
    g.handDiscard controller
  | .discard .chosenNonland =>
    g.withLegalKindPlayer controller kind targets (fun g pid =>
      g.beginRevealDiscard controller pid false) sourceId illegal
  | .discard .chosenNonlandPermanent =>
    g.withLegalKindPlayer controller kind targets (fun g pid =>
      g.beginRevealDiscard controller pid true) sourceId illegal
  | .discard .hand =>
    (g.player controller).hand.foldl (fun g id => g.discardFromHand controller id) g
  | .discard (.mayWheel n .eachPlayer) =>
    match g.apnapFrom.toList with
    | [] => g
    | p :: rest =>
      g.beginFraChoice p (.mayWheel n rest.toArray)
        s!"{(g.player p).name} may discard their hand and draw {n} cards"
  | .untap who@(.landsYouControl) | .untap who@(.tokensYouControl) =>
    match g.permanentsNamed { controller, sourceId, targets } who with
    | some objs =>
      objs.foldl (fun g o =>
        let o := g.object! o.id
        if o.isOnBattlefield && o.status.tapped then g.applyPermanentAction o .untap
        else g) g
    | none => g
  | .discard .drawTwoDiscardTwoStun =>
    let g := g.draw controller 2
    let n := Nat.min 2 (g.player controller).hand.size
    if n == 0 then g
    else
      g.beginFraChoice controller (.discardThenStun n sourceId)
        s!"{(g.player controller).name} discards {n} card(s)"
  | .discard .random =>
    let hand := (g.player controller).hand
    if hand.isEmpty then g
    else
      let (rng, r) := g.rng.next
      let g := { g with rng }
      g.discardFromHandRandomly controller hand[(r.toNat % hand.size)]!
  | .discard .lootThenCountersPerDiscard =>
    if (g.player controller).hand.isEmpty then
      let g := g.draw controller 1
      let n := (g.player controller).cardsDiscardedThisTurn
      match g.fraCause? with
      | some o => if o.isOnBattlefield && n > 0 then g.addPlusOnePlusOneTo o n else g
      | none => g
    else
      g.beginFraChoice controller
        (.discardThen (g.resolvingAbilityObject?.bind (·.fraCauseId)))
        s!"{(g.player controller).name} discards a card"
  | .discard .eachOpponentTwoDrawPerNonlandShortfall =>
    g.continueDiscardTwo controller (g.apnapOrder.filter (· != controller)) 0
  | .untap (.target .eachPermanent) =>
    (List.range targets.size).foldl (fun g i =>
      match targets[i]! with
      | t@(Target.permanent id) =>
        if g.targetLegalAt controller kind i t sourceId then
          match g.findObject? id with
          | some o => g.applyPermanentAction o .untap
          | none => g
        else g.illegalAbilityTarget t
      | _ => g) g
  | .discard (.cards n) =>
    g.beginDiscardCards #[controller] n
  | .tap (.target .eachPermanent) =>
    g.foldPermanentTargets targets (fun g o =>
      if o.isOnBattlefield && o.isCreature then g.applyPermanentAction o .tap else g)
  | .untap .creatureTargets =>
    g.applyCreatureTargetAction targets .untap
  | .discard (.cardsUnlessType n ty) =>
    let g := { g with discardReq := { g.discardReq with thirstDiscardsLeft := n, thirstDiscardType := ty } }
    g.beginDiscardCards #[controller]
  | _ => fallback g

/-- Resolve a `.returnToHand` or `.putOnLibrary` `Effect` (CR 400.7 / CR 401). -/
def applyUnifiedReturnOrLibrary (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .putOnLibrary (.topAfterDraw drawN putN) .cardFromHand =>
    let g := g.draw controller drawN
    let hand := (g.player controller).hand
    let n := min putN hand.size
    let back := hand.extract (hand.size - n) hand.size
    let g := back.foldl (fun g id =>
      match g.findObject? id with
      | some o =>
        if o.zone == .hand controller then
          let (g, newId) := g.move id (.library controller) none
          g.putIdsOnTop controller #[newId]
        else g
      | none => g) g
    g.logMsg s!"{pl.name} puts {n} card(s) on top of their library"
  | .putOnLibrary .bottomRevealCreature .target =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        let owner := o.controller.getD o.owner
        let g := g.moveIdsInOrder #[id] (.library owner)
        let (g, hits, rest) := g.revealUntil owner (·.isCreature) 1
        let g := g.putHits owner hits
        g.restBottom owner rest false
      | none => g
    | _ => g
  | .putOnLibrary .bottomAfterDrawTwo .cardFromHand =>
    let g := g.draw controller 2
    g.handDiscardToBottom controller
  | .returnToHand .target .none =>
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
  | .returnToHand (.target .graveyardCard) .none =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        match g.findObject? id with
        | some o => g.returnToHand id o.owner
        | none => g
      | _ => g) sourceId none
  | .returnToHand .outsideGameOpponentChoice _ =>
    let g := g.materializeSideboard controller
    let names := (g.outsideCards controller).foldl (fun acc o =>
      if acc.contains o.name then acc else acc.push o.name) (#[] : Array String)
    if names.size < 2 then
      g.logMsg s!"{(g.player controller).name} has no two cards with different names outside the game"
    else
      g.beginFraChoice controller .extrapolateReveal
        s!"{(g.player controller).name} may reveal two cards with different names from outside the game"
  | .putOnLibrary .topOrBottomDamage2 .target =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      g.beginFraChoice o.owner (.topOrBottomDamage o.id 2)
        s!"{(g.player o.owner).name} may put {o.name} on top of their library") sourceId illegal
  | .putOnLibrary .topOrBottom .target =>
    if targets.isEmpty then g
    else
      g.withLegalKindPermanent controller kind targets (fun g o =>
        g.beginFraChoice o.owner (.topOrBottomDamage o.id 0)
          s!"{(g.player o.owner).name} puts {o.name} on the top or bottom of their library")
        sourceId illegal
  | .putOnLibrary .bottom .graveyardCard =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        let card := g.object! id
        (g.moveIdsInOrder #[id] (.library card.owner)).logMsg
          s!"{card.name} is put on the bottom of {(g.player card.owner).name}'s library"
      | _ => g) sourceId illegal
  | .putOnLibrary .shuffled .target =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let (g, _) := g.move o.id (.library o.owner) none
      let g := g.logMsg s!"{(g.player o.owner).name} shuffles {o.name} into their library"
      g.shuffleLibrary o.owner) sourceId illegal
  | .returnToHand (.target .eachPermanent) .none =>
    (List.range targets.size).foldl (fun g i =>
      match targets[i]! with
      | t@(Target.permanent id) =>
        if g.targetLegalAt controller kind i t sourceId then
          match g.findObject? id with
          | some o => g.returnToHand id o.owner
          | none => g
        else g.illegalAbilityTarget t
      | _ => g) g
  | .returnToHand .source _ =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.zone == .graveyard o.owner then g.returnToHand o.id o.owner
      else g.logMsg s!"{o.name} is no longer in the graveyard"
    | none => g.logMsg "The ability's source is no longer in the graveyard"
  | .returnToHand .targetSpell _ =>
    match targets[0]? with
    | some (Target.card id) => g.returnStackSpell id
    | _ => g.logMsg "The target is no longer legal"
  | .putOnLibrary .shuffled .source =>
    g.shuffleSourceIntoLibrary sourceId
  | .returnToHand .creaturesNotChosenType _ =>
    let types := g.battlefieldCreatureTypes
    if types.isEmpty then
      g.logMsg s!"{(g.player controller).name} has no creature type to choose"
    else
      g.beginFraChoice controller (.palisadeCreatureType types)
        s!"{(g.player controller).name} chooses a creature type"
  | .returnToHand .ownedCreaturesKicker .delayedBirds =>
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
  | .returnToHand .eachPermanent _ =>
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
  | .returnToHand (.graveyardSubtype subtype) _ =>
    match targets[0]? with
    | some (Target.card id) =>
      match g.findObject? id with
      | some o =>
        if o.zone == Zone.graveyard controller && g.hasSubtype o subtype then
          g.returnToHand o.id o.owner
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | .putOnLibrary .secondOrBottomThenConnive .target =>
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
  | .returnToHand .upToTwoGyModal _ =>
    g.returnChosenGraveyardCards controller targets
  | _ => fallback g

/-- Resolve a `.manaPayOrCast` `Effect` (CR 106 / CR 118 / CR 601). -/
def applyUnifiedManaPayOrCast (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .mayCast .uldarosGraveyardTypes .unlimited .withoutPaying _ =>
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
  | .addMana #[.colored .blue] (.fixed 1) .noncreatureSpell =>
    (g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .blue) 1 (fra := some .noncreatureSpell) })).logMsg
      s!"{(g.player controller).name} adds \{U} (noncreature spells only)"
  | .mayCast .milledSpell .causingSpell .withoutPaying =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        match g.findObject? id with
        | some o =>
          if !(o.zone == .graveyard o.owner) ||
              !(o.printed.isEnchantment || o.printed.isInstantOrSorcery) then
            g.logMsg "The target is no longer legal"
          else
            let name := o.name
            let (g, exId) := g.move id .exile none
            let g := g.logMsg s!"{name} is exiled"
            let card := g.object! exId
            let (g, copy) := g.allocObject card.printed controller .exile (some controller)
            let g := g.setObject { copy with castState := { copy.castState with isCopy := true } }
            g.beginFraChoice controller (.mayCastCopy copy.id)
              s!"{(g.player controller).name} may cast the copy of {name} without paying its mana cost"
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "The target is no longer legal") sourceId illegal
  | .mayCast .boastExiled .unlimited .withoutPaying =>
    let exiled := (g.resolvingAbilityObject?.map (·.boastExiled)).getD #[]
    let (g, copies) := exiled.foldl (fun (acc : Game × Array ObjectId) id =>
      let (g, cs) := acc
      match g.findObject? id with
      | some card =>
        if card.zone != .exile then (g, cs)
        else
          let (g, copy) := g.allocObject { card.printed with isToken := card.printed.isPermanentCard }
            controller .exile (some controller)
          let g := g.setObject { copy with
            castState := { copy.castState with isCopy := true }
            playPermission := some { player := controller, turnEndsRemaining := 0
                                     whileExiled := true, withoutManaCost := true, ignoreTiming := true } }
          (g, cs.push copy.id)
      | none => (g, cs)) (g, #[])
    if copies.isEmpty then g.logMsg "No exiled card is left to copy"
    else
      g.beginFraChoice controller (.castCopiesFree copies 1000 3)
        s!"{(g.player controller).name} may cast up to three of the copies without paying their mana costs"
  | .addMana types (.fixed 1) .none =>
    g.addManaLogged controller types
  | .unrecognized => if isAbility then g else g.logMsg "The effect does nothing"
  | .addMana #[.colored .red] (.count (.oppPermanents ty)) _ =>
    let n := g.battlefield.filter (fun o =>
      o.printed.hasType ty && !o.controlledBy controller) |>.size
    let g := g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .red) n })
    g.logMsg s!"{(g.player controller).name} adds {n} red mana"
  | .addMana #[] (.fixed n) (.subtypeSpells subtype) =>
    g.beginFraChoice controller (.addManaColors n.toNat (.forSubtype subtype))
      s!"{(g.player controller).name} chooses the colors of {englishNumber n.toNat} mana that can be spent only on {subtype} spells"
  | .mayCast .nextRedOrGreenCreature .unlimited .withoutPaying =>
    { g with pendingFreeRGCreature := some controller }
      |>.logMsg "The next red or green creature spell you cast this turn can be cast without paying its mana cost"
  | .addMana #[] (.fixed 1) .anyColor =>
    let g := g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .white) })
    g.logMsg s!"{(g.player controller).name} adds one mana of any color"
  | .addMana #[] (.fixed 1) (.subtypeSpellsOrAbilities subtype) =>
    let color : Color :=
      if subtype == "Villain" then .black else if subtype == "Elf" then .green else .white
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool :=
        pl.manaPool.add (.colored color) 1 (fra := some (.subtypeSpellOrAbility subtype)) })
  | .addMana #[] (.fixed 1) .artifactSpell =>
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .white) 1 })
  | .addMana #[] (.fixed 2) .creatureSources =>
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool :=
        pl.manaPool.add (.colored .green) 2 (creatureRestricted := true) })
  | .addMana #[.colored .blue] (.fixed 1) .cantNonartifact =>
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool :=
        pl.manaPool.add (.colored .blue) 1 (cantNonartifact := true) })
  | .addMana #[] .equalSourcePower .anyColor =>
    let x :=
      match sourceId.bind g.findObject? with
      | some o => (g.power o).toNat
      | none => 0
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .green) x })
  | .addMana #[] (.fixed 4) .anyCombination =>
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .white) 4 })
  | .addMana #[] (.fixed 2) .equipment =>
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool :=
        pl.manaPool.add (.colored .white) 2 })
  | _ => fallback g

/-- Resolve a `.put` `Effect` (CR 403). -/
def applyUnifiedPut (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .put (.cause none) .atNextEndStep _ =>
    match g.fraCause? with
    | some o =>
      if o.zone == .graveyard o.owner then
        { g with delayedEndStep := g.delayedEndStep.push (.returnFromGraveyard o.id controller) }
          |>.logMsg s!"{o.name} returns at the beginning of the next end step"
      else g
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
  | .put .source how@.asPrinted note@.none
  | .put .source how note@(.entering [.counter .plusOnePlusOne _ _]) =>
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
  | .put .cause .tapped .none =>
    match g.fraCause? with
    | some card =>
      if card.zone == .graveyard card.owner then
        let (g, newId) := g.putOntoBattlefield card.id card.owner (tapped := true)
        let g := g.logMsg s!"{card.name} returns to the battlefield tapped"
        g.afterPermanentEnters (g.object! newId)
      else g.logMsg s!"{card.name} is no longer in the graveyard"
    | none => g.logMsg "The card is no longer in the graveyard"
  | .put .landCard .tapped .none =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        let (g, newId) := g.returnCardToBattlefield controller id 0 (tapped := true)
        g.afterLandEnters (g.object! newId)
      | _ => g) sourceId illegal
  | .put .source .asPrinted (.entering [.counter .finality 1 false]) =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.zone == .graveyard o.owner then
        let (g, newId) := g.putOntoBattlefield o.id controller
        let g := g.logMsg s!"{o.name} returns to the battlefield"
        let g := g.addFinalityTo (g.object! newId) 1
        g.afterPermanentEnters (g.object! newId)
      else g.logMsg s!"{o.name} is no longer in the graveyard"
    | none => g.logMsg "The card is no longer in the graveyard"
  | .put .creaturesDiedThisTurn .tapped .asFood =>
    let ids :=
      g.battlefieldCreaturesToGyThisTurn.filter (fun id =>
        match g.findObject? id with
        | some o =>
          o.zone == .graveyard o.owner && o.owner != controller
        | none => false)
    g.supperForSpidersReturn controller ids
  | .put (.creatureMvAtMostOrTeamwork n) .asPrinted _ =>
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
  | .put .source .tapped _ =>
    g.returnSourceFromGraveyard sourceId controller (tapped := true)
  | .put .source .asPrinted .forAttach =>
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
  | .put .source .asPrinted (.entering [.counter .finality 1 true]) =>
    g.returnFromGyFinalityAttach controller sourceId
  | _ => fallback g

/-- Resolve an `.exile` `Effect` (CR 406), part 1. -/
def applyUnifiedExile1 (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .exile .target .forLater .despark =>
    match targets[0]? with
    | some (Target.permanent id) => g.exileId id
    | some (Target.card id) => g.exileId id
    | _ => g.logMsg "Despark has no legal target"
  | .exile .target .forLater .controllerMaySearchBasic =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        let owner := o.controller.getD o.owner
        let g := g.exileId id
        g.offerMaySearchBasics owner
      | none => g
    | _ => g
  | .exile .target .forLater .controllerGainsLifePower =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        let owner := o.controller.getD o.owner
        let pw := (g.snapshotPower o).toNat
        let g := g.exileId id
        g.gainLife owner pw
      | none => g
    | _ => g
  | .exile .allCreatures .forLater .incubateCount =>
    let ids := (g.battlefield.filter (·.isCreature)).map (·.id)
    let g := ids.foldl (fun g id => g.exileId id) g
    let g := g.createKindTokens controller .incubator
    match (g.recentTokenIds.back?).bind g.findObject? with
    | some tok =>
      g.setObject { tok with status := { tok.status with plusOnePlusOne := ids.size } }
        |>.logMsg s!"Incubator enters with {ids.size} +1/+1 counters"
    | none => g
  | .exile .creaturesYouControl .forLater .revealCreaturesToBattlefield =>
    let yours := (g.permanentsOf controller).filter (·.isCreature) |>.map (·.id)
    let g := yours.foldl (fun g id => g.exileId id) g
    let (g, hits, rest) := g.revealUntil controller (·.isCreature) yours.size
    let g := g.putHits controller hits
    g.restBottom controller rest true
  | .exile .creaturesYouControl .forLater .revealCreaturesAtEndStep =>
    let yours := (g.permanentsOf controller).filter (·.isCreature) |>.map (·.id)
    let g := yours.foldl (fun g id => g.exileId id) g
    { g with delayedEndStep := g.delayedEndStep.push (.syntheticDestiny controller yours.size) }
      |>.logMsg "Those creatures return as revealed cards at the next end step"
  | .exile (.target .another) .forLater .revealUntilCreatureOrPlaneswalker =>
    match targets[0]? with
    | some (Target.permanent id) =>
      let g := g.exileId id
      let (g, hits, rest) := g.revealUntil controller creatureOrWalker 1
      let g := g.putHits controller hits
      g.restBottom controller rest false
    | _ => g
  | .exile (.cause none) .untilSourceLeaves _ =>
    match g.fraCause? with
    | some card =>
      if card.zone == .graveyard card.owner then
        match source? with
        | some src => g.exileSearchedLinked controller card.id (some src.id)
        | none => g.exileId card.id
      else g
    | none => g
  | .exile .target .forLater .none =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let (g, _) := g.move o.id .exile none
      g.logMsg s!"{o.name} is exiled") sourceId illegal
  | .exile .allCreatures .forLater .empowerJace =>
    let creatures := g.battlefield.filter (·.isCreature)
    let g := creatures.foldl (fun g o =>
      let (g, _) := g.move o.id .exile none
      g.logMsg s!"{o.name} is exiled") g
    g.empowerJace controller creatures.size
  | .exile .sphinxsApproach .forLater _ =>
    match g.resolvingSpell.bind g.findObject? with
    | some spell =>
      if spell.zone == .stack && !spell.isCopy &&
          (g.sphinxsApproachesInGraveyard controller).size ≥ 4 then
        g.beginFraChoice controller (.sphinxsApproach spell.id)
          s!"{(g.player controller).name} may exile Sphinx's Approach and four cards named Sphinx's Approach"
      else g
    | none => g
  | .exile .target (.returnBrieflyIfMvAtMost n) _ =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let mv := g.objectManaValue o
      let (g, exiled) := g.move o.id .exile none
      let g := g.logMsg s!"{o.name} is exiled"
      if mv ≤ n && !o.printed.isToken then
        let (g, back) := g.putOntoBattlefield exiled controller (tapped := true)
        let g := g.logMsg s!"{o.name} returns to the battlefield tapped under {(g.player controller).name}'s control"
        let g := { g with delayedEndStep := g.delayedEndStep.push (.exilePermanent back) }
        g.afterPermanentEnters (g.object! back)
      else g) sourceId illegal
  | .exile .target .returnImmediately .none =>
    if targets.isEmpty then g
    else
      g.withLegalKindPermanent controller kind targets (fun g o =>
        g.exileThenReturn o "is exiled and returns to the battlefield") sourceId illegal
  | .exile .graveyardCard .forLater .none | .exile (.target .graveyardCard) .forLater .none =>
    if targets.isEmpty then g
    else
      g.withLegalKindTarget controller kind targets (fun g t =>
        match t with
        | Target.card id =>
          let name := (g.object! id).name
          let (g, _) := g.move id .exile none
          g.logMsg s!"{name} is exiled"
        | _ => g) sourceId illegal
  | .exile .target .untilSourceLeaves .none =>
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
  | .exile .target .forLater .revealUntilCreatureOrPlaneswalker =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let (g, _) := g.move o.id .exile none
      let g := g.logMsg s!"{o.name} is exiled"
      let lib := (g.player controller).library
      let (revealed, hit) := Id.run do
        let mut revealed : Array ObjectId := #[]
        for i in [0:lib.size] do
          let id := lib[lib.size - 1 - i]!
          let c := g.object! id
          if c.printed.isCreature || c.printed.isPlaneswalker then
            return (revealed, some id)
          revealed := revealed.push id
        return (revealed, none)
      let g := (revealed ++ hit.toArray).foldl (fun g id =>
        g.logMsg s!"{(g.player controller).name} reveals {(g.object! id).name}") g
      let g :=
        match hit with
        | some id =>
          let (g, newId) := g.putOntoBattlefield id controller
          let g := g.logMsg s!"{(g.object! newId).name} enters the battlefield"
          g.afterPermanentEnters (g.object! newId)
        | none => g.logMsg "No creature or planeswalker card is revealed"
      if revealed.isEmpty then g
      else
        let (rng, ordered) := if g.norandom then (g.rng, revealed) else g.rng.shuffle revealed
        ({ g with rng }.moveIdsInOrder ordered (.library controller)).logMsg
          s!"{(g.player controller).name} puts the rest on the bottom of their library in a random order")
      sourceId illegal
  | _ => fallback g

/-- Resolve an `.exile` `Effect` (CR 406), part 2. -/
def applyUnifiedExile2 (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .exile .opponentLibrariesButBottom .forLater _ =>
    g.forEachOpponent controller (fun g pid =>
      let lib := (g.player pid).library
      let g := (lib.extract 1 lib.size).foldl (fun g id => (g.move id .exile none).1) g
      g.logMsg s!"All but the bottom card of {(g.player pid).name}'s library are exiled")
  | .exile .top (.mayCastElseDamageOpponents n) _ =>
    match (g.player controller).library.back? with
    | none =>
      g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid n)
    | some top =>
      let (g, id) := g.move top .exile none
      let card := g.object! id
      let g := g.logMsg s!"{(g.player controller).name} exiles {card.name}"
      if card.printed.isLand then
        -- Ruling 855: a land can't be cast, so the damage is dealt.
        g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid n)
      else
        { g with pending := .mayCastExiledElseDamage controller id n }.logMsg
          s!"{(g.player controller).name} may cast {card.name}"
  | .exile .top .playUntilNextTurn .. => g.resolveExileTopPlayUntilEndOfNextTurn controller
  | .exile (.graveyardCardsOfType ty (.target .player)) .anyManaWhileExiled _ =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.exileCreaturesFromGraveyard controller pid ty)
  | .exile .targetSpell .forLater .counteredPermanentMayCast =>
    match targets[0]? with
    | some (Target.card id) =>
      g.counterStackSpell id (exilePermanent := true) (grantFreeCast := true)
        controller
    | _ => g.logMsg "The target is no longer legal"
  | .exile .attackingCreatures .forLater .controllerMaySearchBasic =>
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
  | .exile (.topN n) (.playIfYouControlSubtype subtype) _ =>
    g.exileTopPlayIfYouControlSubtype controller n subtype
  | .exile .eachPermanent .returnImmediately _ =>
    g.foldPermanentTargets targets (fun g o =>
      if o.controlledBy controller && o.isOnBattlefield then
        g.exileThenReturn o "is exiled, then returned to the battlefield"
          (land := o.printed.isLand)
      else g)
  | .exile .opponentTopX .playForLifeThisTurn _ =>
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
  | .exile (.creatureMvAtMostOrTeamwork n) .forLater (.gainLifeIfTeamwork life) =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let teamwork := g.resolvingTeamworkPaid
      if o.isOnBattlefield && o.isCreature &&
          (teamwork || o.printed.manaValue ≤ n) then
        let (g, _) := g.move o.id .exile none
        if teamwork then g.gainLife controller life else g
      else g.logMsg "The target is no longer legal")
      none (some "The target is no longer legal")
  | .exile (.topN n) .playUntilNextTurn _ =>
    g.exileTopPlayThisTurn controller n
  | .exile .allCreatures .forLater .worldsWithinWorlds =>
    g.applyWorldsWithinWorlds controller none
  | .exile .hand .playUntilNextTurn .thenDrawThree =>
    g.exileHandDrawPlayUntilNext controller
  | .exile (.target .eachPermanent) .untilSourceLeaves _ =>
    g.withSourceStillOnBattlefield sourceId fun g _ =>
      targets.foldl (fun acc t =>
        match t with
        | Target.permanent oid =>
          match acc.findObject? oid with
          | some o => acc.exileUntilSourceLeaves sourceId o
          | none => acc
        | _ => acc) g
  | .exile (.target .eachPermanent) .nextEndStep _ =>
    g.foldPermanentTargets targets (fun g o =>
      if o.isOnBattlefield && o.controlledBy controller && !o.printed.isLand &&
          some o.id != sourceId then
        let name := o.name
        let (g, newId) := g.move o.id .exile none
        { g with delayedEndStep := g.delayedEndStep.push (.returnExiled newId) }
          |>.logMsg s!"{name} is exiled until the beginning of the next end step"
      else g.logMsg "The target is no longer legal")
  | .exile .topPower .playThisTurn _ =>
    let x := g.sourcePowerNatAtResolution sourceId lastKnownPower
    g.exileTopPlayThisTurn controller x
  | _ => fallback g

/-- Resolve a `.sacrificeOrDestroy` `Effect` (CR 701.7 / CR 701.17). -/
def applyUnifiedSacrificeOrDestroy (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .destroy .target .controllerCreatesHuman =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        let owner := o.controller.getD o.owner
        let g := g.destroyPermanent o
        g.createKindTokens owner .human
      | none => g
    | _ => g
  | .sacrifice .archonCruelty _ =>
    match targets[0]? with
    | some (Target.player pid) =>
      let victim :=
        ((g.permanentsOf pid).find? (·.isCreature)).orElse
          (fun _ => (g.permanentsOf pid).find? (·.printed.isPlaneswalker))
      let g :=
        match victim with
        | some o => g.sacrificeToGraveyard o s!"{(g.player pid).name} sacrifices {o.name}"
        | none => g.logMsg s!"{(g.player pid).name} has no creature or planeswalker to sacrifice"
      let g := g.handDiscard pid
      let g := g.loseLife pid 3
      let g := g.draw controller 1
      g.gainLife controller 3
    | _ => g
  | .destroy .oppTappedCreatures .gainLifeEach =>
    let ids := g.battlefield.filter (fun o =>
      o.isCreature && o.status.tapped &&
        match o.controller with
        | some c => c != controller && !(g.player c).lost
        | none => false) |>.map (·.id)
    let g := g.destroyIds ids
    g.gainLife controller ids.size
  | .destroy .creaturesPowerAtLeast4 _ =>
    g.destroyIds (g.battlefield.filter (fun o => o.isCreature && g.snapshotPower o >= 4) |>.map (·.id))
  | .destroy .target .drawIfNotAttacking =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let wasAttacking := o.status.attacking
      let ctrl := o.controller.getD o.owner
      let g := g.destroyPermanent o
      if wasAttacking then g else g.draw ctrl 1) sourceId illegal
  | .destroy .creaturesNotChosenType _ =>
    let chosen := g.chooseCreatureTypeFor controller
    let g := g.logMsg s!"{(g.player controller).name} chooses {chosen}"
    let doomed := g.battlefield.filter (fun o => o.isCreature && !g.hasSubtype o chosen)
    doomed.foldl (fun g o =>
      match g.findObject? o.id with
      | some o => g.destroyPermanent o
      | none => g) g
  | .destroy (.targetAt index) .none =>
    match g.legalPermanentAt? controller kind targets index sourceId with
    | some o => g.destroyPermanent o
    | none => g.logMsg "The target is no longer legal"
  | .sacrifice .source .none =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield then g.sacrificeToGraveyard o s!"{(g.player controller).name} sacrifices {o.name}"
      else g
    | none => g
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
  | .destroy (.target .eachPermanent) .none =>
    targets.foldl (fun g t =>
      match t with
      | Target.permanent id =>
        match g.findObject? id with
        | some o =>
          if o.isOnBattlefield && g.canBeTargetedBy controller o then g.destroyPermanent o
          else g.illegalAbilityTarget t
        | none => g
      | _ => g) g
  | .sacrifice .eachOpponentsCreature _ =>
    g.beginSacrificeCreatures ((g.livingOpponents controller).map (·.id)) #[]
  | .destroy .target .drawIfLegendaryEnchantment =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let legendaryEnchantment := o.isLegendary && o.printed.isEnchantment
      let g := g.destroyPermanent o
      if legendaryEnchantment then g.draw controller 1 else g) sourceId illegal
  | .destroy .allCreatures .none =>
    (g.battlefield.filter (·.isCreature)).foldl (fun g o =>
      match g.findObject? o.id with
      | some o => if o.isOnBattlefield then g.destroyPermanent o else g
      | none => g) g
  | .sacrifice .eachPlayersCreature .ifYouDoCreateBeast =>
    g.continueSacrificeEach controller g.apnapOrder #[]
  | .sacrifice .oppGreatestMvCreatureOrPlaneswalker _ =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.sacrificeGreatestManaValue pid) sourceId
  | .destroy .otherCreaturesOddOrEvenMv _ =>
    { g with pending := .fraChoice controller (.oddOrEvenDestroy sourceId) }
      |>.logMsg s!"{(g.player controller).name} chooses odd or even"
  | .destroy .target =>
    g.withLegalKindPermanent controller effect.targetKind targets
      (fun g o => g.destroyPermanent o) none
      (if effect.allowsZeroTargets || effect.phrase == s!"Destroy {effect.targetKind.noun}" then none
       else some "The target is no longer legal")
  | .destroy .allCreaturesExceptTwoChosen _ =>
    let creatures := (g.battlefield.filter (·.isCreature)).map (·.id)
    g.offerCardChoice controller creatures 2 .keepDestroyRest
      s!"{(g.player controller).name} chooses up to two creatures to keep"
  | _ => fallback g

/-- Resolve a `.revealOrReflexive` `Effect` (CR 603.12 / CR 701.16 / CR 701.20 / CR 701.23), part 1. -/
def applyUnifiedRevealOrReflexive1 (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .searchLibrary (.put (.basicSubtypesUntapAt kinds untapAt) _ _) =>
    let g := if untapAt == 0 then g else { g with afterLibrarySearch := .untapSearchedIfLands untapAt }
    g.beginLibrarySearch controller (basicOf kinds) "a basic land card" (.battlefield true)
  | .revealLibrary .untilCreaturesPerOpponent _ _ =>
    let n := (g.livingOpponents controller).size
    let (g, hits, rest) := g.revealUntil controller (·.isCreature) n
    let g := g.putHits controller hits
    let g := hits.foldl (fun g id =>
      match g.followMoved id |> g.findObject? with
      | some o => g.setObject { o with status := { o.status with goaded := true } }
      | none => g) g
    let opps := g.livingOpponents controller
    let g := Id.run do
      let mut g := g
      let mut i := 0
      for id in hits do
        match opps[i]?, g.followMoved id |> g.findObject? with
        | some opp, some o =>
          g := g.changeControl o opp.id
          i := i + 1
        | _, _ => pure ()
      return g
    g.restBottom controller rest true
  | .revealLibrary .untilHistoric _ _ =>
    match targets[0]? with
    | some (Target.player pid) =>
      let (g, hits, rest) := g.revealUntil pid historicCard 1
      let g :=
        match hits[0]? with
        | some id =>
          match g.findObject? id with
          | some card =>
            let mv := card.printed.manaValue
            let g := g.putHits controller #[id]
            g.loseLife controller mv
          | none => g
        | none => g.logMsg s!"{(g.player pid).name} reveals no historic permanent"
      g.restBottom pid rest false
    | _ => g
  | .revealLibrary .firstResolveUntilCreature _ _ =>
    let g := g.draw controller
    match source? with
    | some src =>
      if src.status.optionalOnceUsed then g
      else
        let g := g.mapObjectStatus src (fun s => { s with optionalOnceUsed := true })
        let (g, hits, rest) := g.revealUntil controller (·.isCreature) 1
        let g := g.putHits controller hits
        g.restBottom controller rest false
    | none => g
  | .revealLibrary (.top 5) (.returnToHand .factOrFiction _) _ =>
    let lib := (g.player controller).library
    let n := min 5 lib.size
    let ids := (List.range n).foldl (fun (acc : Game × Array ObjectId) _ =>
      let (g, acc) := acc
      let top := (g.player controller).library.back!
      let (g, newId) := g.move top .exile none
      (g, acc.push newId)) (g, #[])
    let (g, shown) := ids
    let handN := (shown.size + 1) / 2
    let toHand := shown.extract 0 handN
    let toGy := shown.extract handN shown.size
    let g := toHand.foldl (fun g id =>
      match g.findObject? id with
      | some o =>
        let (g, _) := g.move id (.hand controller) none
        g.logMsg s!"{o.name} goes to {pl.name}'s hand"
      | none => g) g
    toGy.foldl (fun g id =>
      match g.findObject? id with
      | some o =>
        let (g, _) := g.move id (.graveyard controller) none
        g.logMsg s!"{o.name} goes to {pl.name}'s graveyard"
      | none => g) g
  | .searchLibrary (.putOnLibrary .top .planeswalkerCard) =>
    g.beginLibrarySearch controller (·.isPlaneswalker) "a planeswalker card" .topAfterShuffle
  | .searchLibrary (.mill (.fixed 1) _ _) =>
    g.beginLibrarySearch controller (·.isLand) "a land card" .graveyard
  | .searchLibrary (.returnToHand .card _) =>
    g.resolveLibrarySearchToHand controller (fun _ => true) "card"
  | .revealFromHand .hand (.exile .chosenNonland .untilSourceLeaves _) =>
    g.withLegalKindPlayer controller kind targets (fun g pid =>
      let g := g.revealHand pid
      if (g.revealedHandChoices pid false).isEmpty then
        g.logMsg s!"{(g.player pid).name} has no nonland card"
      else
        g.beginFraChoice controller (.exileFromRevealedHand pid sourceId)
          s!"{(g.player controller).name} chooses a nonland card to exile") sourceId illegal
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
  | .searchLibrary (.put (.landsUpTo n) .tapped _) =>
    g.beginLibrarySearch controller (·.isLand) "a land card" (.battlefield true) (count := n)
  | .searchLibrary (.returnToHand .enchantmentCard _) =>
    g.resolveLibrarySearchToHand controller (·.isEnchantment) "enchantment card"
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
  | _ => fallback g

/-- Resolve a `.revealOrReflexive` `Effect` (CR 603.12 / CR 701.16 / CR 701.20 / CR 701.23), part 2. -/
def applyUnifiedRevealOrReflexive2 (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .queueReflexive (.mshReflexive kind paid) =>
    if kind == 2 then
      g.beginFraChoice controller (.hawkeyeModes paid #[] sourceId)
        s!"{(g.player controller).name} chooses up to {paid} Trick Arrows modes"
    else g.queueModeledReflexive controller sourceId kind paid
  | .searchLibrary (.put .basicLand .tapped _) => g.resolveSearchBasicLandTapped controller
  | .searchLibrary (.returnToHand (.landSubtype t) _) => g.resolveSearchLandTypeToHand controller t
  | .searchLibrary (.returnToHand .basicLand _) => g.resolveSearchBasicLandToHand controller
  | .searchLibrary (.returnToHand (.supertypeCard s ty) _) =>
    let pred := fun c => c.hasType ty && c.hasSupertype s
    let card := s!"{s.oracleWord} {ty.oracleWord} card"
    g.resolveLibrarySearchToHand controller pred card
  | .searchLibrary (.put (.supertypeCard s ty) .tapped _) =>
    let pred := fun c => c.hasType ty && c.hasSupertype s
    let card := s!"{s.oracleWord} {ty.oracleWord} card"
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? (g.followMoved id) with
      | some o =>
        g.beginLibrarySearch o.owner pred s!"a {card}" (.battlefield true) (optional := true)
      | none => g
    | _ => g
  | .revealLibrary (.top n) (.returnToHand .twoPiles _) _ =>
    let looked := g.scryLookedIds controller n
    if looked.isEmpty then
      g.logMsg s!"{(g.player controller).name}'s library has no cards to look at"
    else
      let g := g.logLookAtTop controller looked.size
      g.beginFraChoice controller (.riddlesSplit looked)
        s!"{(g.player controller).name} separates {looked.size} cards into a face-up pile and a face-down pile"
  | .revealLibrary (.top n) (.sequence [.put .landsYouControl .tapped _, .gainLife (.fixed life) _]) _ =>
    let ids := g.scryLookedIds controller n
    let g := g.logLookAtTop controller ids.size
    let lands := ids.filter (fun id => (g.findObject? id).any (·.printed.isLand))
    if lands.isEmpty then
      let g := g.requestShuffle controller (.gainLife controller life.toNat)
      g.continueIfShuffled
    else
      g.offerCardChoice controller lands lands.size (.landsTappedGainLife life.toNat)
        s!"{(g.player controller).name} may put any number of land cards from among them onto the battlefield tapped"
  | .revealLibrary (.top n) (.put .creaturesYouControl _ _) _ =>
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
  | .searchLibrary (.put .artifactCreatureX _ _) =>
    g.beginVisionQuest controller chosenX
  | .searchLibrary (.sequence [.put .basicLand .tapped _, .returnToHand .basicLand _]) =>
    g.beginLibrarySearch controller isBasicLandCard "a basic land card"
      .battlefieldTappedThenHand (count := 2)
  | .searchLibrary (.put (.basicBeholdUntap subtype) .tapped _) =>
    g.beginLibrarySearch controller isBasicLandCard "a basic land card"
      (.battlefieldTappedBeholdUntap subtype)
  | .revealLibrary (.top n) (.put (.lookedTypes types) _ _) _ =>
    g.beginLookPutTypes controller n types
  | .revealLibrary (.top n) (.returnToHand .artifact _) _ =>
    g.beginLookRevealToHand controller n (fun o => o.printed.isArtifact) false
  | .revealLibrary (.top n) (.returnToHand (.milledSubtype subtype) _) _ =>
    g.beginLookRevealToHand controller n (fun o => o.printed.hasSubtype subtype) true
  | .revealLibrary (.top 1) (.draw (.fixed 1) _) _ =>
    g.revealTopDrawIfArtifact controller
  | _ => fallback g

/-- Resolve a `.sequenceOrModes` `Effect` (CR 608.2c / CR 700.2). -/
def applyUnifiedSequenceOrModes (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (recurse : Game → Effect → Array Target → Bool → Bool → Bool → Nat → Option ObjectId → Option Int → Bool → Game)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .chooseModes _ (.fraTrigger _) => g
  | .chooseModes _ (.hawkeyeIndices modes) =>
    let src := sourceId.bind g.findObject?
    let (g, _) := modes.foldl (fun (acc : Game × Nat) m =>
      let (g, i) := acc
      let slice := targets.extract i (i + 1)
      match m with
      | 0 =>
        (g.withLegalKindPermanent controller .creature slice (fun g o =>
          (g.mapObjectStatus o (fun s => { s with cantBlockUntilEot := true })).logMsg
            s!"{o.name} can't block this turn") sourceId illegal, i + 1)
      | 1 =>
        (g.withLegalKindPlayer controller .player slice
          (fun g pid => g.dealDamageToPlayer pid 2 (source := src)) sourceId illegal, i + 1)
      | _ =>
        if (g.player controller).hand.isEmpty then (g.draw controller 1, i)
        else
          (g.beginFraChoice controller .discardThenDraw
            s!"{(g.player controller).name} discards a card, then draws a card", i)) (g, 0)
    g
  | .sequence [.dealDamage (.fixed n) .target .excess, .empowerJace .notedExcess] =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let before := o.status.damage
      let g := g.dealDamageToPermanent o n.toNat
      let dealt := ((g.object! o.id).status.damage - before).toNat
      let excess := g.excessDamage o dealt
      if excess > 0 then g.empowerJace controller excess
      else g) sourceId (some "The target is no longer legal")
  | .sequence rs =>
    match effect.resolution.onPermanent? with
    | some a => g.applyOnPermanent controller effect.targetKind targets a sourceId
    | none =>
      match effect.resolution.onSource? with
      | some a =>
        if isAbility then g.applyOnSource sourceId a
        else g.applyOnPermanent controller effect.targetKind targets a
      | none =>
        match rs.flatMap Resolution.flatten with
        | [.tap .target true, .scry (.fixed scryN), .draw (.fixed drawN)] =>
          if isAbility then
            g.resolveTapScryDraw controller effect targets scryN.toNat drawN.toNat sourceId
              (fizzle := fun g => g.logIllegalSequenceTargets targets)
          else
            g.resolveTapScryDraw controller effect targets scryN.toNat drawN.toNat
        | [.gainLife (.fixed life) .player, .searchLibrary (.put .basicLand .asPrinted _), .putCounters (.ofKind .plusOnePlusOne 1) .target] =>
          g.applyGainLifeSearchBasicPlusOne controller targets life.toNat
        | [.becomeCopy .sourceSpellXTimes, .dealDamage (.fixed n) .target .none] =>
          g.applyDamageToKindTarget controller .creature targets n.toNat
        | [.discard (.cards 1 .eachOpponent), .putCounters (.ofKind .plusOnePlusOne 1) .source] =>
          let opps := (g.livingOpponents controller).map (·.id)
          let g := { g with discardReq := { g.discardReq with plusOneAfterDiscards := sourceId } }
          let g := g.beginDiscardCards opps
          if g.pending == .none then
            (g.finishPlusOneAfterDiscards).receivePriority g.activePlayer
          else g
        | steps =>
          if g.sequenceAllTargetsIllegal controller effect targets sourceId then
            g.logIllegalSequenceTargets targets
          else
            match steps with
            | [.putOnLibrary .shuffled .source, .draw (.fixed n) _] =>
              g.shuffleSourceIntoLibrary sourceId (.draw controller n.toNat)
            | [.put .source .asPrinted (.entering [.counter .finality 1 true]),
               .may (.attach .equipmentYouControl .target) (.sequence []) _] =>
              g.returnFromGyFinalityAttach controller sourceId
            | steps =>
              steps.foldl (fun g r =>
                recurse g { effect with resolution := r } targets
                  castFromGraveyard kicked giftPromised chosenX
                  sourceId lastKnownPower isAbility) g
  | .unlessPays r n =>
    if effect.allowsZeroTargets && targets.isEmpty then g
    else g.beginUnlessPays controller effect targets r n
  | .or rs =>
    match rs with
    | [] => g.logMsg "The effect does nothing"
    | [r] =>
      recurse g { effect with resolution := r } targets
        castFromGraveyard kicked giftPromised chosenX none none false
    | rs =>
      g.beginSpellOr controller effect targets rs
  | .«if» cond r =>
    let run (g : Game) : Game :=
      recurse g { effect with resolution := r } targets
        castFromGraveyard kicked giftPromised chosenX none none false
    g.branchOnSpellIf controller effect targets cond castFromGraveyard run id giftPromised
  | .ifElse cond whenTrue whenFalse =>
    let run (r : SpellResolution) (g : Game) : Game :=
      recurse g { effect with resolution := r } targets
        castFromGraveyard kicked giftPromised chosenX none none false
    g.branchOnSpellIf controller effect targets cond castFromGraveyard
      (run whenTrue) (run whenFalse) giftPromised
  | _ => fallback g

/-- Resolve a `.may` `Effect` (CR 608.2c). -/
def applyUnifiedMay (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .may (.discard (.cards 1 .you)) (.draw (.fixed n) _) .ifYouDo =>
    if pl.hand.isEmpty then g.logMsg s!"{pl.name} has no card to discard"
    else
      { g with pending := .mayDiscardDraw controller n.toNat }.logMsg
        s!"{pl.name} may discard a card. If they do, they draw {n.toNat}"
  | .may (.loseLife .lastKnownPower _) (.draw .lastKnownPower _) .ifYouDo =>
    let n := g.knownN
    if (g.player controller).life > Int.ofNat n && n > 0 then
      (g.loseLife controller n).draw controller n
    else g.logMsg s!"{pl.name} declines to pay {n} life"
  | .may (.sacrifice .planeswalker _) (.searchLibrary (.put .planeswalkerCard _ _)) .ifYouDo =>
    if (g.permanentsOf controller).any (·.printed.isPlaneswalker) then
      g.beginFraChoice controller .maySacrificePlaneswalker
        s!"{(g.player controller).name} may sacrifice a planeswalker"
    else g.logMsg s!"{(g.player controller).name} controls no planeswalker to sacrifice"
  | .may (.removeCounters (.upTo 1) .source) (.putCounters (.ofKind .plusOnePlusOne 1) .eachOther) .ifYouDo =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield && o.status.plusOnePlusOne > 0 then
        g.beginFraChoice controller (.mayMovePlusOne o.id)
          s!"{(g.player controller).name} may remove a +1/+1 counter from {o.name}"
      else g
    | none => g
  | .may (.pay (.mana #[.generic n])) thenStep .ifYouDo =>
    g.beginFraChoice controller (.mayPayThen n thenStep sourceId)
      s!"{(g.player controller).name} may pay \{{n}}"
  | .may (.discard (.cards 1 .you)) thenStep .ifYouDo =>
    if (g.player controller).hand.isEmpty then g
    else
      g.beginFraChoice controller (.mayDiscardThen thenStep sourceId)
        s!"{(g.player controller).name} may discard a card"
  | .may (.searchLibrary (.put .landsEqualDamage .tapped _)) (.sequence []) _ =>
    let n := (g.resolvingAbilityObject?.bind (·.lastKnownPower)).getD 0 |>.toNat
    if n == 0 then g
    else
      g.beginFraChoice controller (.mayThen (.searchLibrary (.put (.landsUpTo n) .tapped)) sourceId)
        s!"{(g.player controller).name} may search for up to {n} land cards"
  | .may act@(.searchLibrary (.put .basicLand .tapped _)) (.sequence []) .ifYouDo =>
    g.beginFraChoice controller (.mayThen act sourceId)
      s!"{(g.player controller).name} may search for a basic land card"
  | .may (.sacrifice .land) thenStep@(.createTokens .heartwood (.fixed 2) true _ _) .ifYouDo =>
    if (g.permanentsOf controller).any (·.printed.isLand) then
      g.beginFraChoice controller (.maySacrificeThen .land thenStep sourceId)
        s!"{(g.player controller).name} may sacrifice a land"
    else g
  | .may (.sacrifice .creatureOrPlaneswalker) thenStep@(.sacrifice .eachOpponentsCreature _) .ifYouDo =>
    if (g.permanentsOf controller).any (fun o => o.isCreature || o.printed.isPlaneswalker) then
      g.beginFraChoice controller
        (.maySacrificeThen .creatureOrPlaneswalker thenStep sourceId)
        s!"{(g.player controller).name} may sacrifice a creature or planeswalker"
    else g
  | .may (.sacrifice .another) thenStep@(.createTokens .beast44trample (.fixed 1) false _ _) .ifYouDo =>
    if (g.creaturesControlledBy controller).isEmpty then g
    else
      g.beginFraChoice controller (.maySacrificeThen .creature thenStep sourceId)
        s!"{(g.player controller).name} may sacrifice a creature"
  | .may (.removeCounters .all .source) (.putCounters .sourceCounters .target) .ifYouDo =>
    match source? with
    | some src =>
      g.withLegalKindPermanent controller kind targets (fun g o =>
        if src.isOnBattlefield && src.status.hasCounters then
          g.beginFraChoice controller (.mayMoveAllCounters src.id o.id)
            s!"{(g.player controller).name} may move all counters from {src.name} onto {o.name}"
        else g) sourceId illegal
    | none => g
  | .may (.draw (.perControlled ty) _) (.draw (.fixed 1) .eachOpponent) .ifYouDo =>
    g.mayDrawPerArtifact controller ty
  | .may (.put (.creatureFromHand subtype n) _ _) (.draw (.fixed 1) _) _ =>
    g.mayPutHeroOrDraw controller n subtype
  | .may (.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .card])) (.draw (.fixed cards) _) .ifYouDo =>
    { g with pending := .maySacArtifactOrDiscard controller cards.toNat }
      |>.logMsg s!"{(g.player controller).name} may sacrifice an artifact or discard a card. If they do, they draw {cards.toNat}"
  | .may r _ _ =>
    g.beginMay controller effect targets r
  | _ => fallback g

/-- Resolve a `.grant` `Effect` (CR 613 / CR 614), part 1. -/
def applyUnifiedGrant1 (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .empowerJace amount =>
    match g.triggerCount { controller, sourceId, targets } amount with
    | some n => g.empowerJace controller n
    | none => g
  | .grant (.animateLand p t flying first) .source =>
    match source? with
    | none => g
    | some o =>
      let kws :=
        Keywords.merge (if flying then Keyword.flying else Keywords.none)
          (if first then Keywords.none else Keywords.none)
      let g := g.setUntilEotForm o (Int.ofNat p, Int.ofNat t) kws
        s!"{o.name} becomes a {p}/{t} until end of turn"
        (additionalCreature := true)
      if first then g.mapObjectStatus (g.object! o.id) (fun s => { s with firstStrikeOnYourTurn := true })
      else g
  | .grant (.ruleEffect (.emblemCreaturesGetTwoTwo flying)) .youIfCast =>
    if flying then
      let (g, emb) := g.allocObject {
          name := "Elspeth emblem"
          types := #[.enchantment]
          staticRule := .grantTeamPlusTwoFlying
        } controller .command (some controller)
      g.logMsg s!"{pl.name} gets an emblem ({emb.name})"
    else
      let emblem : CardDef := {
        name := s!"{srcName} Emblem", types := #[]
        staticAbilities := #[.fra .emblemCreaturesGetTwoTwo] }
      (g.createCommandObject controller emblem).logMsg
        s!"{pl.name} gets an emblem with \"Creatures you control get +2/+2.\""
  | .cant (.attackJaces _) =>
    if g.activePlayer == controller then g
    else
      g.modifyPlayer g.activePlayer (fun q => { q with cantAttackJaces := true })
        |>.logMsg s!"{(g.player g.activePlayer).name}'s creatures can't attack Jaces this turn"
  | .grant .monarch .youIfCast =>
    let g := g.players.foldl (fun g q =>
      if q.isMonarch && q.id != controller then
        g.setPlayer { q with isMonarch := false }
      else g) g
    g.modifyPlayer controller (fun q => { q with isMonarch := true })
      |>.logMsg s!"{pl.name} becomes the monarch"
  | .grant .teferisReproach (.player (.target .opponent)) =>
    match targets[0]? with
    | some (Target.player pid) =>
      let g := g.modifyPlayer pid (fun q =>
        { q with protectionFromEverything := true, lifeCantChange := true })
      let g := g.logMsg s!"{(g.player pid).name} has protection from everything and their life total can't change"
      let ids := (g.permanentsOf pid).filter (fun o => !o.printed.isLand) |>.map (·.id)
      let g := ids.foldl (fun g id =>
        match g.findObject? id with
        | some o => if o.isOnBattlefield then g.phaseOut o else g
        | none => g) g
      match g.resolvingSpell.bind g.findObject? with
      | some spell =>
        g.setObject { spell with castState := { spell.castState with exileInstantSorceryInstead := true } }
          |>.logMsg s!"{spell.name} will be exiled"
      | none => g
    | _ => g
  | .becomeCopy .targetSpellTwice =>
    match targets[0]? with
    | some (Target.card id) =>
      match g.findObject? id with
      | some spell => (g.copyStackSpell spell controller).copyStackSpell spell controller
      | none => g
    | _ => g
  | .becomeCopy .targetPermanentTwoTokensHasteSacrifice =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some src =>
        Id.run do
          let mut g := g
          for _ in [0:2] do
            let (g', tok) := g.copyBattlefieldPermanent src controller
            g := g'
            g := g.mapObjectStatus tok (·.grantUntilEot Keyword.haste)
            g := { g with delayedEndStep := g.delayedEndStep.push (.sacrificePermanent tok.id) }
          return g.logMsg "The token copies gain haste and are sacrificed at the next end step"
      | none => g
    | _ => g
  | .becomeCopy .anyCreatureOnBattlefieldWithHaste =>
    match source? with
    | none => g
    | some art =>
      match g.battlefield.find? (fun o => o.isCreature && o.id != art.id) with
      | none => g.logMsg s!"{art.name} does not become a copy"
      | some src =>
        let g := g.becomeCopyOf art src (untilEot := true)
        g.mapObjectStatus (g.object! art.id) (·.grantUntilEot Keyword.haste)
          |>.logMsg s!"{art.name} has haste until end of turn"
  | .grant .explored .source =>
    let lib := (g.player controller).library
    if lib.isEmpty then g.logMsg s!"{pl.name} explores (empty library)"
    else
      let top := lib.back!
      let card := g.object! top
      if card.printed.isLand then
        let (g, _) := g.move top (.hand controller) none
        g.logMsg s!"{pl.name} explores and puts {card.name} into their hand"
      else
        let g := g.putIdsOnTop controller #[top]
        match source? with
        | some o =>
          if o.isCreature then
            g.mapObjectStatus o (fun s => s.addPlusOnePlusOne 1)
              |>.logMsg s!"{pl.name} explores; {o.name} gets a +1/+1 counter"
          else g.logMsg s!"{pl.name} explores and leaves {card.name} on top"
        | none => g.logMsg s!"{pl.name} explores and leaves {card.name} on top"
  | .grant .transformedIncubator .source =>
    match source? with
    | some o =>
      let counters := o.status.plusOnePlusOne
      g.setObject { o with printed :=
        { creatureToken "Phyrexian" #["Phyrexian"] 0 0 (types := #[.artifact, .creature]) with
          name := "Phyrexian" } }
        |>.logMsg s!"{o.name} transforms into a 0/0 Phyrexian with {counters} +1/+1 counters"
    | none => g
  | .grant .faceUp .source =>
    match source? with
    | some o =>
      g.setObject { o with status := { o.status with faceDown := false } }
        |>.logMsg s!"{o.name} is turned face up"
    | none => g
  | .cant (.beBlockedExceptByHaste .source) =>
    match source? with
    | some o =>
      g.mapObjectStatus o (fun s => { s with cantBeBlockedExceptByHasteUntilEot := true })
        |>.logMsg s!"{o.name} can't be blocked this turn except by creatures with haste"
    | none => g
  | .lose .allAbilities (.targetAt index) =>
    match g.legalPermanentAt? controller kind targets index sourceId with
    | none => g.logMsg "The target is no longer legal"
    | some o =>
      let g := g.mapObjectStatus o (fun s => { s with losesAbilitiesUntilEot := true })
      g.logMsg s!"{o.name} loses all abilities until end of turn"
  | .grant (.keywords _) .createdToken =>
    g.recentTokenIds.foldl (fun g id =>
      match g.findObject? id with
      | some o => g.grantKeywordsUntilEot o Keyword.haste
      | none => g) g
  | .grant .mountainsAddExtraRed .landsYouControl =>
    let g := g.modifyPlayer controller (fun pl =>
      { pl with mountainExtraRedThisTurn := pl.mountainExtraRedThisTurn + 1 })
    g.logMsg s!"Until end of turn, whenever {(g.player controller).name} taps a Mountain for mana, they add an additional \{R}"
  | .becomePrepared .enchanted false =>
    match (sourceId.bind g.findObject?).bind (·.attachedTo) |>.bind g.findObject? with
    | some host =>
      let g := if host.status.tapped then g else g.becomeTapped host
      g.unprepare (g.object! host.id)
    | none => g.logMsg "The Aura isn't attached to a creature"
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
  | .grant (.keywords k) (.cause none) =>
    match g.fraCause? with
    | some o => if o.isOnBattlefield then g.grantKeywordsUntilEot o k else g
    | none => g
  | .fight (.targetAt 0) .mutual =>
    match g.legalPermanentAt? controller kind targets 0 sourceId,
        g.legalPermanentAt? controller kind targets 1 sourceId with
    | some a, some b => g.fightCreatures a b
    | _, _ => g
  | .fight .source .mutual =>
    if targets.isEmpty then g
    else
      match sourceId.bind g.findObject? with
      | some src =>
        g.withLegalKindPermanent controller kind targets (fun g o =>
          if src.isOnBattlefield then g.fightCreatures (g.object! src.id) o else g) sourceId illegal
      | none => g
  | .grant .emrakulManaAndCast .target =>
    match source? with
    | none => g
    | some card =>
      let g :=
        if card.zone == .exile then
          let perm : PlayPermission :=
            { player := controller, turnEndsRemaining := 0, whileExiled := true }
          (g.setObject { card with playPermission := some perm }).logMsg
            s!"{(g.player controller).name} may cast {card.name} for as long as it remains exiled"
        else g
      g.withLegalKindPermanent controller kind targets (fun g land =>
        let g := g.mapObjectStatus land (fun s =>
          { s with colorlessGrantUntilCast := s.colorlessGrantUntilCast.push card.id })
        g.logMsg s!"{land.name} gains \"\{T}: Add \{C}\{C}\" until {card.name} is cast from exile")
        sourceId illegal
  | _ => fallback g

/-- Resolve a `.grant` `Effect` (CR 613 / CR 614), part 2. -/
def applyUnifiedGrant2 (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .cant (.beCountered .nextSpellThisTurn) =>
    (g.modifyPlayer controller (fun pl => { pl with nextSpellCantBeCountered := true })).logMsg
      s!"The next spell {(g.player controller).name} casts this turn can't be countered"
  | .grant (.choiceOfKeywords options) .source =>
    onSource (fun g o => g.beginChooseKeyword controller o.id options.toArray)
  | .grant .combatDamageDrawTwo .source =>
    onSource (fun g o =>
      let ab := TriggeredAbility.fra .combatDamageToPlayer
        "Whenever this creature deals combat damage to a player, draw two cards." (.draw 2)
      (g.mapObjectStatus o (fun s =>
        { s with grantedTriggersUntilEot := s.grantedTriggersUntilEot.push ab })).logMsg
        s!"Until end of turn, whenever {o.name} deals combat damage to a player, {(g.player controller).name} draws two cards")
  | .grant .emblemDrawOnCast .youIfCast =>
    let emblem : CardDef := {
      name := "Chandra, Chill of Compliance Emblem", types := #[]
      triggeredAbilities := #[TriggeredAbility.fra .youCastSpell
        "Whenever you cast a spell, draw a card." (.draw 1)] }
    (g.createCommandObject controller emblem).logMsg
      s!"{(g.player controller).name} gets an emblem with \"Whenever you cast a spell, draw a card.\""
  | .grant .artifactCreatureVehicle .source =>
    onSource (fun g o =>
      (g.mapObjectStatus o (fun s => { s with additionalCreatureUntilEot := true })).logMsg
        s!"{o.name} becomes an artifact creature until end of turn")
  | .mshReflexive kind paid =>
    g.resolveModeledReflexive controller sourceId kind paid targets g.resolvingDivision
  | .becomeCopy .sourceSpellXTimes =>
    match sourceId.bind g.findObject? with
    | some spell =>
      if spell.zone != .stack then g.logMsg s!"{spell.name} is no longer on the stack"
      else
        let x := spell.chosenX.getD 0
        let (g, copies) := (List.range x).foldl (fun (acc : Game × Array ObjectId) _ =>
          let g := acc.1.copyStackSpell spell controller
          (g, acc.2.push ((g.stack.back?.map (·.objectId)).getD spell.id))) (g, #[])
        let targeted := ((g.stackEntry? spell.id).map (!·.targets.isEmpty)).getD false
        if copies.isEmpty || !targeted then g
        else
          g.beginFraChoice controller (.newTargetsForCopies copies)
            s!"{(g.player controller).name} may choose new targets for the copies"
    | none => g
  | .grant .extraTurn .youIfCast =>
    { g with turnControl := { g.turnControl with extraTurns := g.extraTurns.push controller } }
      |>.logMsg s!"{(g.player controller).name} takes an extra turn after this one. During that turn, power-up abilities can't be activated."
  | .cant (.block .creaturesWithoutFlying) =>
    { g with creaturesWithoutFlyingCantBlock := true }
      |>.logMsg "Creatures without flying can't block this turn"
  | .becomePrepared .creaturesYouControl _ =>
    (g.permanentsOf controller).foldl (fun g o =>
      if o.isCreature && o.printed.prepareFace.isSome then g.becomePrepared (g.object! o.id)
      else g) g
  | .grant (.emblemCastSpellDamage n) .youIfCast =>
    -- Ruling 858: the emblem is colorless.
    let emblem : CardDef := {
      name := "Chandra Emblem", types := #[]
      triggeredAbilities := #[.triggered .youCastSpell
        (Effect.ofTrigger (.onPermanent .playerOrCreature (.dealDamage n)))] }
    let (g, _) := g.allocObject emblem controller .command (some controller)
    g.logMsg s!"{(g.player controller).name} gets an emblem"
  | .grant (.nextSpellCopy false) .source =>
    let g := g.modifyPlayer controller (fun pl =>
      { pl with copyNextInstantSorceryThisTurn := pl.copyNextInstantSorceryThisTurn + 1 })
    g.logMsg s!"When {(g.player controller).name} next casts an instant or sorcery spell this turn, it is copied"
  | .becomeCopy (.creaturesControlledBy (.target .player)) =>
    -- Rulings 784–789: each token copies the creature's copiable values only
    -- (no counters or status). All tokens are created before any of them is
    -- treated as entering, so they see each other enter.
    g.withLegalKindPlayer controller effect.targetKind targets (fun g pid =>
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
        | none => g) g) sourceId
  | .becomeCopy .targetLegendRuleOff =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g target =>
      g.withSourceOnBattlefield sourceId (fun g src =>
        -- Rulings 812 / 815 / 816: copy the copiable values (already those
        -- of anything the target copies); the land doesn't enter, keeps its
        -- status, and both effects end together in cleanup (ruling 817).
        let g := g.becomeCopyOf src target (untilEot := true)
        let g := g.modifyPlayer controller (fun pl => { pl with legendRuleOffThisTurn := true })
        g.logMsg s!"The legend rule doesn't apply to permanents {(g.player controller).name} controls this turn")
        "The source is no longer in play") sourceId (some "The target is no longer legal")
  | .grant .jaceLoyaltyAtInstantSpeed .youIfCast =>
    let g := g.modifyPlayer controller (fun pl => { pl with jaceLoyaltyAtInstantSpeed := true })
    g.logMsg s!"Until end of turn, {(g.player controller).name} may activate loyalty abilities of Jace planeswalkers they control any time they could cast an instant"
  | .grant (.keywords k) .creaturesYouControl =>
    g.grantUntilEotToControlledCreatures controller k k.joinedAnd
  | .recruit _ => g.beginRecruit controller
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
          g.dealDamageFrom src.name dest n (source := some src)
      else
        let logIllegal (g : Game) (ok : Bool) (id : ObjectId) : Game :=
          if ok then g else g.illegalAbilityTarget (Target.permanent id)
        logIllegal (logIllegal g srcOk srcId) destOk destId
    | _, _ => g.logMsg "The target is no longer legal"
  | .fight .announced .mutual =>
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
  | .fight .announced .upToOneOther =>
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
  | .grant .extraLand .youIfCast =>
    let g := g.modifyPlayer controller (fun pl =>
      { pl with additionalLandsThisTurn := pl.additionalLandsThisTurn + 1 })
    g.logMsg s!"{(g.player controller).name} may play an additional land this turn"
  | .counter =>
    g.withLegalKindTarget controller effect.targetKind targets (fun g t =>
      match t with
      | Target.card id => g.counterStackSpell id
      | _ => g) none (some "The target is no longer legal")
  | .attach .equipmentYouControl .target =>
    g.beginMay controller effect targets (.attach .equipmentYouControl .target)
  | .gainControl .exchangeTargets =>
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
  | _ => fallback g

/-- Resolve a `.grant` `Effect` (CR 613 / CR 614), part 3. -/
def applyUnifiedGrant3 (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false)
    (fallback : Game → Game) : Game :=
  let pl := g.player controller
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  let source? : Option GameObject :=
    (sourceId.map g.followMoved).bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := if chosenX != 0 then chosenX else g.spellX
  let _ := (pl, kind, illegal, srcName, src?, source?, onSource, chosenX, castFromGraveyard, kicked, giftPromised, lastKnownPower, isAbility)
  match effect.resolution with
  | .replace =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.mapObjectStatus o (fun s => { s with untilEotExileIfDies := true })
      g.logMsg s!"If {o.name} would die this turn, exile it instead")
  | .cant (.castSpellsThisTurn .any) =>
    g.players.foldl (fun acc pl =>
      acc.setPlayer { pl with cantCastSpellsThisTurn := true }) g
      |>.logMsg "Players can't cast spells this turn"
  | .gainControl .oppArtifacts =>
    g.foldPermanentTargets targets (fun g o =>
      if o.isOnBattlefield && o.printed.isArtifact && !o.controlledBy controller then
        g.changeControl o controller
      else g)
  | .grant .phaseOutKicker .target =>
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
  | .investigate (.target .player) =>
    match targets.findSome? (fun t =>
        match t with
        | Target.player pid => some pid
        | _ => none) with
    | some pid =>
      if (g.player pid).lost then g.logMsg "The target is no longer legal"
      else (g.createToken pid clueToken).1
    | none => g.logMsg "The target is no longer legal"
  | .grant (.keywords k) .creatureTargets =>
    g.applyCreatureTargetAction targets (.grantKeywords k)
  | .grant (.artifactCreature p t kw) .target =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      g.setUntilEotForm o (p, t) ((Keywords.ofName? kw).getD Keywords.none)
        s!"{o.name} becomes a {p}/{t} artifact creature with {kw} until end of turn"
        (additionalCreature := true) (additionalArtifact := true))
  | .becomeCopy .nontokenCreaturesYouControl =>
    g.copyNontokenCreaturesYouControl controller
  | .gainControl .untilEotOrNextIfVillain =>
    g.applyEvilsThrall controller targets
  | .spellsCostLess which (.fixed n) =>
    g.grantSpellsCostLessThisTurn controller which n.toNat
  | .connive .source =>
    g.applyConnive controller sourceId
  | .attach .source .target =>
    g.withLegalKindPermanent controller effect.targetKind targets fun g host =>
      g.withSourceOnBattlefield sourceId (fun g src =>
        if src.attachedTo == some host.id then
          g.logMsg s!"{src.name} is already attached to {host.name}"
        else
          g.attachSourceTo src host)
        "The Equipment is no longer in play"
  | .grant (.subtypeWithLandsPT subtype) .source =>
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
  | .grant (.keywords k) (.intersection [.creaturesYouControl, .union subs]) =>
    let subtypes := subs.filterMap (fun | .youControl (.subtype s) => some s | _ => none)
    g.grantUntilEotToControlledCreatures controller k k.joinedAnd
      (fun g o => subtypes.any (g.hasSubtype o))
  | .grant .arwenShare .target =>
    match sourceId, targets[0]? with
    | some sid, some (Target.permanent tid) => g.resolveArwenShare sid (some tid)
    | some sid, _ => g.resolveArwenShare sid none
    | _, _ => g.logMsg "The ability's source is no longer in play"
  | .grant .combatDamageCreateTreasure .target =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.mapObjectStatus o (fun s => { s with combatDamageCreatesTreasure := true })
      g.logMsg
        s!"{o.name} gains \"Whenever this creature deals combat damage to a player, create a Treasure token\"")
      sourceId (some "The target is no longer legal")
  | .cant (.beBlockedByMostLifePlayer .target) =>
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
  | .grant .transformed .source =>
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
  | .becomeCopy (.stackAbility _) =>
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
  | .grant .constructHero .source =>
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
  | .becomeCopy .secondArtifactTargetNotLegendary =>
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
  | .grant (.typesPTAndKeywords types p t k) .source =>
    let typeWords := String.intercalate " " types.toList
    g.withSourceOnBattlefield sourceId (fun g o =>
      g.setUntilEotForm o (p, t) k
        s!"{o.name} becomes a {p}/{t} {typeWords}"
        (types := some types))
      "The source is no longer in play"
  | .grant (.nextSpellCopy true) .source =>
    let pw :=
      match sourceId.bind g.findObject? with
      | some o =>
        if o.isOnBattlefield then g.power o else o.power
      | none => (0 : Int)
    { g with pendingLokiCopy := some (controller, sourceId, pw) }
      |>.logMsg s!"The next instant or sorcery with mana value {pw} or less will be copied"
  | .grant .harnessed .source =>
    g.withSourceOnBattlefield sourceId (fun g o =>
      let g := g.mapObjectStatus o (fun s => { s with harnessed := true })
      g.logMsg s!"{o.name} is harnessed") "The source is no longer in play"
  | .connive (.target (.youControl (.subtype _))) =>
    match targets[0]? with
    | some (Target.permanent id) => g.applyConnive controller (some id)
    | _ => g.applyConnive controller none
  | _ => fallback g

/-- Resolve a unified `Effect` as a spell or ability (CR 608). -/
partial def applyUnified (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0)
    (sourceId : Option ObjectId := none) (lastKnownPower : Option Int := none)
    (isAbility : Bool := false) : Game :=
  let recurse (g : Game) (effect : Effect) (targets : Array Target)
      (castFromGraveyard kicked giftPromised : Bool) (chosenX : Nat)
      (sourceId : Option ObjectId) (lastKnownPower : Option Int) (isAbility : Bool) : Game :=
    g.applyUnified controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility
  let fallback (g : Game) : Game :=
    g.applyUnifiedFallback controller effect targets sourceId isAbility
  match effect.resolution with
  | .pumpOrDamage none .. =>
    g.applyUnifiedPump controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility fallback
  | .pumpOrDamage (some _) .. =>
    g.applyUnifiedDamage1 controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility (fun g =>
      g.applyUnifiedDamage2 controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility recurse fallback)
  | .putCounters .. =>
    g.applyUnifiedCounters1 controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility (fun g =>
      g.applyUnifiedCounters2 controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility fallback)
  | .playerNumeric false .. =>
    g.applyUnifiedScryOrMill controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility fallback
  | .playerNumeric true .. =>
    g.applyUnifiedDrawOrLife controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility fallback
  | .createOrAmass .. =>
    g.applyUnifiedCreateOrAmass controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility fallback
  | .tapDiscardOrReturn none none .. =>
    g.applyUnifiedTapOrDiscard controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility fallback
  | .tapDiscardOrReturn .. =>
    g.applyUnifiedReturnOrLibrary controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility fallback
  | .manaPayOrCast .. =>
    g.applyUnifiedManaPayOrCast controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility fallback
  | .putOrExile (some _) .. =>
    g.applyUnifiedPut controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility fallback
  | .putOrExile none .. =>
    g.applyUnifiedExile1 controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility (fun g =>
      g.applyUnifiedExile2 controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility fallback)
  | .sacrificeOrDestroy .. =>
    g.applyUnifiedSacrificeOrDestroy controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility fallback
  | .revealOrReflexive .. =>
    g.applyUnifiedRevealOrReflexive1 controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility (fun g =>
      g.applyUnifiedRevealOrReflexive2 controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility fallback)
  | .sequenceOrModes .. =>
    g.applyUnifiedSequenceOrModes controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility recurse fallback
  | .may .. =>
    g.applyUnifiedMay controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility fallback
  | .grant .. =>
    g.applyUnifiedGrant1 controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility (fun g =>
      g.applyUnifiedGrant2 controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility (fun g =>
        g.applyUnifiedGrant3 controller effect targets castFromGraveyard kicked giftPromised chosenX sourceId lastKnownPower isAbility fallback))

/-- Resolve a single `Resolution` step in ability context. -/
def applyFra (g : Game) (controller : PlayerId) (effect : Effect) (r : Resolution)
    (targets : Array Target) (sourceId : Option ObjectId) : Game :=
  g.applyUnified controller { effect with resolution := r } targets
    (sourceId := sourceId) (isAbility := true)

/-- Resolve a stashed `unlessPays` effect after its payer left without paying
(CR 800.4f). -/
partial def flushUnlessPays (g : Game) : Game :=
  if !g.unlessPaysDue || g.over then g
  else
    match g.unlessPaysInstead with
    | none => { g with unlessPays := { g.unlessPays with due := false } }
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

/-- Resolve a unified activated-ability `Effect` (CR 608). -/
def applyUnifiedAbility (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (sourceId : Option ObjectId := none)
    (lastKnownPower : Option Int := none) (chosenX : Nat := 0) : Game :=
  g.applyUnified controller effect targets (chosenX := chosenX)
    (sourceId := sourceId) (lastKnownPower := lastKnownPower) (isAbility := true)

/-- Resolve a printed activated ability (CR 608). -/
def applyAbilityEffect (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (sourceId : Option ObjectId := none)
    (lastKnownPower : Option Int := none) (chosenX : Nat := 0) : Game :=
  g.applyUnifiedAbility controller effect targets
    sourceId lastKnownPower chosenX

end Game
end Mtg.Engine
