import Mtg.Engine.Game.Casting

/-!
# Resolution choices

Choices made while resolving: sacrifice choices, lifetime modal choices
(Alliance, Gollum), and card-specific helpers such as beholding a
quality, Riddles in the Dark, The Black Gate, and Gríma's exile.
-/

namespace Mtg.Engine
namespace Game

/-- Creatures `p` may sacrifice to a “sacrifices a creature of their choice” effect. -/
def sacrificeCreatureChoices (g : Game) (p : PlayerId) : Array GameObject :=
  g.creaturesControlledBy p

/-- Whether `sac` is a legal “another creature or artifact” sacrifice for `sourceId`. -/
def canSacrificeAsCreatureOrArtifact (g : Game) (p : PlayerId) (sourceId : ObjectId)
    (sac : GameObject) : Bool :=
  (g.sacrificeCreatureOrArtifactChoices p sourceId).any (·.id == sac.id)

/-- Whether `sac` is a legal creature for `p` to sacrifice to an edict. -/
def canSacrificeCreature (g : Game) (p : PlayerId) (sac : GameObject) : Bool :=
  (g.sacrificeCreatureChoices p).any (·.id == sac.id)

/-- Creatures `p` controls that are tied for least power. -/
def leastPowerCreatures (g : Game) (p : PlayerId) : Array GameObject :=
  let cs := g.sacrificeCreatureChoices p
  match cs[0]? with
  | none => #[]
  | some first =>
    let minP := cs.foldl (fun acc o => min acc (g.power o)) (g.power first)
    cs.filter (fun o => g.power o == minP)

/-- Sacrifice a least-power creature `p` controls. If several are tied and
`chosen` is none, the player still chooses (logged; no sacrifice yet). -/
def sacrificeLeastPowerCreature (g : Game) (p : PlayerId)
    (chosen : Option ObjectId := none) : Game :=
  let tied := g.leastPowerCreatures p
  if tied.isEmpty then
    g.logMsg s!"{(g.player p).name} controls no creatures to sacrifice"
  else
    let pick :=
      match chosen with
      | some chosenId => tied.find? (fun (o : GameObject) => o.id == chosenId)
      | none => if tied.size == 1 then some tied[0]! else none
    match pick with
    | some o =>
      g.sacrificeToGraveyard o
        s!"{(g.player p).name} sacrifices {o.name} (least power)"
    | none =>
      let ids : Array ObjectId := tied.map (fun (o : GameObject) => o.id)
      (g.change (.pending (.fraChoice p (.sacrificeLeastPower ids)))).logMsg
        s!"{(g.player p).name} chooses one of the creatures tied for least power to sacrifice"

/-- Modes in `all` that have not yet been chosen. -/
def unusedModes (chosen : Array Nat) (all : Array Nat := #[0, 1, 2]) : Array Nat :=
  all.filter (fun m => !chosen.contains m)

/-- Unused Alliance modes on `src` (0 = add GGG, 1 = +1/+1 each, 2 = scry 2
then draw). -/
def unusedAllianceModes (g : Game) (src : GameObject) : Array Nat :=
  unusedModes (g.modesChosenThisTurn src.id)

/-- Unused Gollum modes on `src` (0 = +1/+1, 1 = drain, 2 = draw). Modes last
for the object's lifetime (ruling 164). -/
def unusedGollumModes (g : Game) (src : GameObject) : Array Nat :=
  unusedModes (g.modesChosenEver src.id)

/-- Behold a quality: choose a matching permanent you control or reveal a
matching card from your hand. Later zone changes do not un-behold (117). -/
def beholdQuality (g : Game) (p : PlayerId) (quality : CardSubtype)
    (cause : Option EventCause := none) : Game :=
  let hasPerm := (g.permanentsOf p).any (fun o => g.hasSubtype o quality)
  let handMatch? :=
    (g.player p).hand.find? (fun id =>
      match g.findObject? id with
      | some o => g.hasSubtype o quality
      | none => false)
  if hasPerm || handMatch?.isSome then
    let effCause := g.resolveOptionalCause cause (fallbackCtrl := some p)
    let g := g.withBatch (some effCause) fun g =>
      let g :=
        if !hasPerm then
          match handMatch? with
          | some hid => g.record (GameEvent.revealed g.turnNumber p #[hid] (cause := some effCause))
          | none => g
        else g
      g.record (GameEvent.beheld g.turnNumber p quality (cause := effCause))
    g.logMsg s!"{(g.player p).name} beholds a {quality}"
  else
    g.logMsg s!"{(g.player p).name} does not behold a {quality}"

/-- True when `p` has beheld `quality`, even if the card or permanent later left. -/
def qualityWasBeheld (g : Game) (p : PlayerId) (quality : CardSubtype) : Bool :=
  (g.beheldQualities p).contains quality

/-- Draw one card for each graveyard with seven or more cards. -/
def drawPerSevenCardGraveyard (g : Game) (p : PlayerId) : Game :=
  let n := g.players.filter (fun pl => pl.graveyard.size >= 7) |>.size
  if n == 0 then
    g.logMsg s!"{(g.player p).name} draws no cards (no graveyard has seven cards)"
  else
    g.draw p n

/-- Pause-safe loop discarding `ids` from `p`'s hand inside an open batch. -/
def discardHandIdsLoop (g : Game) (p : PlayerId) (ids : Array ObjectId)
    (logEach : Bool := false) (cause : Option EventCause := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishPostStep (.discardHandIdsLoop p ids logEach cause))
  let mut g := g
  for i in [0:ids.size] do
    let id := ids[i]!
    match g.findObject? id with
    | none => pure ()
    | some o =>
      if o.zone == .hand p then
        let msg := s!"{(g.player p).name} discards {o.name}"
        let (g', _) := g.move id (.graveyard o.owner) none (verb := some .discard)
          (actor := some p) (cause := cause)
        g := g'
        if let .chooseReplacement .. := g.pending then
          if logEach then
            g := g.chainPendingReplacement (.logMessage msg)
          let rem := ids.extract (i + 1) ids.size
          if !rem.isEmpty then
            g := g.chainPendingReplacement
              (.finishPostStep (.discardHandIdsLoop p rem logEach cause))
          return g
        if logEach then
          g := g.logMsg msg
  return g

/-- Discard every card in `p`'s hand. Zero cards is a legal discard and is
logged (Sauron, the Dark Lord). -/
def discardEntireHand (g : Game) (p : PlayerId) (cause : Option EventCause := none) : Game :=
  let ids := (g.player p).hand
  let preDiscards := g.loggedDiscards p
  let (g, cause?) : Game × Option EventCause :=
    match cause with
    | some c => (g, some c)
    | none =>
      if ids.isEmpty then (g, none)
      else
        match g.currentResolvingContext? with
        | some (src, ctrl) =>
          let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some p)) src
          (g, some c)
        | none => (g, none)
  let g := g.withBatch cause? fun g =>
    g.discardHandIdsLoop p ids (logEach := false) (cause := cause?)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishPostStep (.logDiscardedCount p preDiscards))
  else
    let discarded := g.loggedDiscards p - preDiscards
    g.logMsg s!"{(g.player p).name} discards {discarded} card(s)"

/-- Discard the hand (zero cards is legal) and draw that many. The choice is
made during resolution; nothing happens between discard and draw. -/
def mayDiscardHandDrawThatMany (g : Game) (p : PlayerId) (doDiscard : Bool) : Game :=
  if !doDiscard then
    g.logMsg s!"{(g.player p).name} does not discard their hand"
  else
    let n := (g.player p).hand.size
    let g := g.discardEntireHand p
    if n == 0 then g
    else if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.wheelDrawThenOfferNext p n))
    else g.draw p n

/-- Discard the hand, then draw `n` cards. An empty hand is a legal discard
(Sauron, the Dark Lord). -/
def discardHandThenDraw (g : Game) (p : PlayerId) (n : Nat) : Game :=
  let g := g.discardEntireHand p
  if n == 0 then g
  else if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishPostStep (.wheelDrawThenOfferNext p n))
  else g.draw p n

/-- Move or put each card in `remainingIds` onto the battlefield sequentially,
pausing on `Pending.chooseReplacement` (`PendingReplacement.putToBattlefieldLoop`)
and running `afterPermanentEnters` / `afterLandEnters` (plus optional haste,
entry log, or Food-artifact log) only after all cards have finished entering. -/
def putToBattlefieldLoop (g : Game) (controller : PlayerId)
    (remainingIds : Array ObjectId)
    (enteredFromIds : Array ObjectId := #[])
    (useCardOwner : Bool := false)
    (haste : Bool := false)
    (tapped : Bool := false)
    (isLandEnters : Bool := false)
    (onlyFoodArtifact : Bool := false)
    (entryLog : PutBattlefieldEntryLog := .none)
    (cause : Option EventCause := none)
    (preBattlefield : Option (Array GameObject) := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.putToBattlefieldLoop controller remainingIds enteredFromIds
        useCardOwner haste tapped isLandEnters onlyFoodArtifact entryLog cause preBattlefield)
  let preBf := preBattlefield.getD g.battlefield
  let mut g := g
  let mut entered := enteredFromIds
  for i in [0:remainingIds.size] do
    let id := remainingIds[i]!
    match g.findObject? id with
    | none => pure ()
    | some o =>
      if onlyFoodArtifact && o.zone != .graveyard o.owner then
        pure ()
      else
        let ctrl := if useCardOwner then o.owner else controller
        let (g', _) :=
          if onlyFoodArtifact then
            g.move id .battlefield (some ctrl)
              (summoningSick := true) (applyHope := false)
              (onlyFoodArtifact := true) (preBattlefield := some preBf) (cause := cause)
          else
            g.putOntoBattlefield id ctrl (tapped := tapped)
              (preBattlefield := some preBf) (cause := cause)
        g := g'
        entered := entered.push id
        if let .chooseReplacement .. := g.pending then
          let rem := remainingIds.extract (i + 1) remainingIds.size
          return g.chainPendingReplacement
            (.putToBattlefieldLoop controller rem entered
              useCardOwner haste tapped isLandEnters onlyFoodArtifact entryLog cause (some preBf))
  for j in [0:entered.size] do
    let fromId := entered[j]!
    match g.followMovedToZone? fromId (· == .battlefield) with
    | none => pure ()
    | some enteredObj =>
      match entryLog with
      | .none => pure ()
      | .enters => g := g.logMsg s!"{enteredObj.name} enters the battlefield"
      | .entersTapped => g := g.logMsg s!"{enteredObj.name} enters tapped"
      if haste then
        g := g.createEffect (.keywordsUntilEot enteredObj.id { haste := true }) (cause := cause)
      if onlyFoodArtifact then
        if let some cur := g.findObject? enteredObj.id then
          g := g.logMsg s!"{cur.name} returns as a Food artifact"
      g :=
        if isLandEnters then g.afterLandEnters (g.object! enteredObj.id)
        else g.afterPermanentEnters (g.object! enteredObj.id)
      if let .chooseReplacement .. := g.pending then
        let remEntered := entered.extract (j + 1) entered.size
        if !remEntered.isEmpty then
          g := g.chainPendingReplacement
            (.putToBattlefieldLoop controller #[] remEntered
              useCardOwner haste tapped isLandEnters onlyFoodArtifact entryLog cause (some preBf))
        return g
  return g

/-- Put the returned cards onto the battlefield as Food artifacts only.
They keep name, mana cost, mana value, abilities, and legendary. -/
def supperForSpidersReturn (g : Game) (controller : PlayerId)
    (ids : Array ObjectId) : Game :=
  g.withBatch none fun g =>
    g.putToBattlefieldLoop controller ids (onlyFoodArtifact := true)

/-- Exile the top `n` cards face down. They may be played while exiled if you
control `subtype` (CR 610.1 / 701.18). Timing and costs are unchanged. -/
def exileTopPlayIfYouControlSubtype (g : Game) (p : PlayerId) (n : Nat)
    (subtype : CardSubtype) : Game :=
  if n == 0 then g
  else
    let (g0, cause?) : Game × Option EventCause :=
      if (g.player p).library.isEmpty then (g, none)
      else
        let (g, c) := g.allocDelayedCause (some p)
        (g, some c)
    g0.withBatch cause? fun g0 => Id.run do
      let mut g := g0
      for _ in List.range n do
        let pl := g.player p
        if pl.library.isEmpty then
          g := g.logMsg s!"{pl.name} has no cards in their library to exile"
        else
          let top := pl.library.back!
          let cardName := (g.object! top).name
          let (g', newId) := g.move top .exile none (cause := cause?)
          g := g'
          g := g.createEffect (.playPermission newId {
              player := p
              whileExiled := true
              requireSubtype := some subtype
              faceDown := true })
            (cause := cause?)
          g := g.logMsg s!"{pl.name} exiles a card face down"
          let _ := cardName
      return g

/-- Finish the direct-cast step of `grimaExileUntilInstantOrSorcery` once
moving `fromId` to `.stack` completes, then put `others` on the bottom of
`victim`'s library in a random order. -/
def finishGrimaDirectCast (g : Game) (controller victim : PlayerId)
    (fromId : ObjectId) (others : Array ObjectId)
    (cause : Option EventCause) : Game :=
  let g :=
    match g.followMovedToZone? fromId (· == .stack) with
    | some moved =>
      g.logMsg s!"{(g.player controller).name} casts {moved.name} as the ability resolves"
    | none => g
  g.requestOrderInto others (.library victim)
    s!"{(g.player victim).name} puts the remaining exiled cards on the bottom of their library in a random order"
    (cause := cause)

/-- Pause-safe loop exiling cards from the top of `victim`'s library face up
until an instant or sorcery card is exiled (or the library is empty), following
each moved card via `followMovedToZone?` across `Pending.chooseReplacement`
pauses and then finishing via `mode` (`GrimaExileMode`). -/
partial def exileUntilInstantOrSorceryLoop (g : Game) (victim : PlayerId)
    (mode : GrimaExileMode) (cause : Option EventCause := none)
    (others : Array ObjectId := #[])
    (pendingFromId : Option ObjectId := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishPostStep (.exileUntilInstantOrSorceryLoop victim mode cause others pendingFromId))
  let mut g := g
  let mut others := others
  let mut found : Option ObjectId := none
  if let some fid := pendingFromId then
    if let some moved := g.followMovedToZone? fid (· == .exile) then
      g := g.logMsg s!"{(g.player victim).name} exiles {moved.name} face up"
      if g.isInstantOrSorcery moved then
        found := some moved.id
      else
        others := others.push moved.id
  while found.isNone && !(g.player victim).library.isEmpty do
    let top := (g.player victim).library.back!
    let name := (g.object! top).name
    let (g', _) := g.move top .exile none (cause := cause)
    g := g'
    if let .chooseReplacement .. := g.pending then
      return g.chainPendingReplacement
        (.finishPostStep (.exileUntilInstantOrSorceryLoop victim mode cause others (some top)))
    if let some moved := g.followMovedToZone? top (· == .exile) then
      g := g.logMsg s!"{(g.player victim).name} exiles {name} face up"
      if g.isInstantOrSorcery moved then
        found := some moved.id
      else
        others := others.push moved.id
  match mode with
  | .impulseState =>
    if g.continuations.isEmpty then
      g := g.change (.pushContinuationFrame {})
    return g.changes #[
      .grimaImpulseReady true,
      .grimaImpulseVictim (some victim),
      .grimaImpulseFound found,
      .grimaImpulseOthers others]
  | .directCastOrBottom controller castTheCard =>
    match found with
    | none =>
      return g.requestOrderInto others (.library victim)
        s!"{(g.player victim).name} randomizes the exiled cards; they become that player's library"
        (cause := cause)
    | some instId =>
      if castTheCard then
        let (g', _) := g.move instId .stack (some controller)
          (verb := some .cast) (actor := some controller) (cause := cause)
        if let .chooseReplacement .. := g'.pending then
          return g'.chainPendingReplacement
            (.finishPostStep (.finishGrimaDirectCast controller victim instId others cause))
        return g'.finishGrimaDirectCast controller victim instId others cause
      else
        let (g', _) := g.move instId (.library victim) none (cause := cause)
        return g'.requestOrderInto others (.library victim)
          s!"{(g'.player victim).name} puts the remaining exiled cards on the bottom of their library in a random order"
          (cause := cause)

/-- Exile cards from `victim`'s library until an instant or sorcery, face up.
An empty library becomes that player's library again. The found card may be
cast as this ability resolves, ignoring timing. Uncast cards go on the bottom
in a random order. -/
def grimaExileUntilInstantOrSorcery (g : Game) (controller victim : PlayerId)
    (castTheCard : Bool) : Game :=
  let (g, cause) := g.allocDelayedCause (some controller)
  g.exileUntilInstantOrSorceryLoop victim (.directCastOrBottom controller castTheCard)
    (cause := some cause)

/-- True when `p` can pay Saruman's ward (discard an enchantment, instant,
or sorcery card). -/
def canPaySarumanWard (g : Game) (p : PlayerId) : Bool :=
  (g.player p).hand.any (fun id =>
    match g.findObject? id with
    | some o => g.isEnchantment o || g.isInstantOrSorcery o
    | none => false)

/-- Legendary artifacts and creatures `p` may sacrifice to Sauron's ward. -/
def legendaryWardSacrificeChoices (g : Game) (p : PlayerId) : Array GameObject :=
  (g.permanentsOf p).filter (fun o =>
    g.isLegendary o && (g.isCreature o || g.isArtifact o))

/-- Put one Riddles pile into `p`'s hand and the other into the graveyard.
The face-down pile is not revealed when it is the one that goes to hand. -/
def applyRiddlesPiles (g : Game) (p : PlayerId) (faceUp faceDown : Array ObjectId)
    (chooseFaceDown : Bool) (alreadyRevealed : Bool := false) : Game :=
  let g := g.logMsg
    s!"{(g.player p).name} separates {faceUp.size} face-up and {faceDown.size} face-down"
  let g :=
    if !alreadyRevealed && !faceUp.isEmpty then
      let g := g.record (GameEvent.revealed g.turnNumber p faceUp
        (cause := some (g.resolvingOrRuleCause p)))
      faceUp.foldl (fun acc id =>
        match acc.findObject? id with
        | some o => acc.logMsg s!"{(acc.player p).name} reveals {o.name}"
        | none => acc) g
    else g
  let toHand := if chooseFaceDown then faceDown else faceUp
  let toGy := if chooseFaceDown then faceUp else faceDown
  let g :=
    if chooseFaceDown then
      g.logMsg "The face-down pile is put into hand without being revealed"
    else
      g.logMsg "The face-up pile is put into hand"
  let outerCont? := g.pendingReplacement
  let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
  let g := g.withBatch none fun g =>
    toHand.foldl (fun acc id =>
      (acc.move id (.hand p) none).1) g
  let g := g.withBatch none fun g =>
    g.moveCardsToGraveyardLoop toGy
  match outerCont? with
  | some outer => g.chainPendingReplacement outer
  | none => g

/-- Split the top four library cards into a face-up pile and a face-down pile.
A 4/0 split is legal. The face-down pile is not revealed if it is put into
hand. -/
def riddlesInTheDark (g : Game) (p : PlayerId) (faceUpCount : Nat)
    (chooseFaceDown : Bool) : Game :=
  let lib := (g.player p).library
  let n := min 4 lib.size
  let taken := lib.extract (lib.size - n) lib.size
  let g :=
    if !taken.isEmpty then
      g.record (GameEvent.lookedAt g.turnNumber p taken (cause := some (g.resolvingOrRuleCause p)))
    else g
  let faceUpN := min faceUpCount taken.size
  let faceUp := taken.extract (taken.size - faceUpN) taken.size
  let faceDown := taken.extract 0 (taken.size - faceUpN)
  g.applyRiddlesPiles p faceUp faceDown chooseFaceDown

/-- Linked activated abilities last only while the copier still has them. -/
def linkedAbilitiesStillLinked (stillHasThoseAbilities : Bool) : Bool :=
  stillHasThoseAbilities

/-- Treat a copied activated ability as referring to the copier's name. -/
def rewriteAbilityCardName (abilityText printedName copierName : String) : String :=
  abilityText.replace printedName copierName

/-- Must-attack-if-able may be declined when every legal attack would cost. -/
def mustAttackCanDeclineIfOnlyAttackCosts (onlyAttacksRequireCost : Bool) : Bool :=
  onlyAttacksRequireCost

/-- Ares and similar “attacks each combat if able” statics (MSH 130). -/
def hasAttacksIfAble (g : Game) (o : GameObject) : Bool :=
  (g.staticAbilities o).any (fun
    | .attacksEachCombatIfAble => true
    | _ => false)

/-- Every legal attack target (player or planeswalker) charges a cost to be attacked. -/
def everyAttackCosts (g : Game) (o : GameObject) : Bool :=
  match g.controllerOf o with
  | none => false
  | some p =>
    let opps := g.livingOpponents p
    let noJace := g.cantAttackJaces p
    !opps.isEmpty && opps.all (fun pl =>
      g.attackTaxPerCreature pl.id > 0 &&
        !(g.permanentsOf pl.id).any (fun pw =>
          g.isPlaneswalker pw &&
            !(noJace && ((g.name pw).startsWith "Jace" || g.hasSubtype pw .jace))))

/-- Whether `o` has at least one legal attack target (an opponent player or
opponent-controlled planeswalker) that does not charge an attack cost
(CR 508.1b,c,d / 506.4c). -/
def hasCostFreeLegalAttackTarget (g : Game) (o : GameObject) : Bool :=
  match g.controllerOf o with
  | none => false
  | some p =>
    let opps := g.livingOpponents p
    let flyer := g.hasFlying o
    let noJace := g.cantAttackJaces p
    opps.any fun pl =>
      (g.attackTaxPerCreature pl.id == 0 && !(flyer && g.leftoverFlyingRestriction pl.id)) ||
        (g.permanentsOf pl.id).any (fun pw =>
          g.isPlaneswalker pw &&
            !(noJace && ((g.name pw).startsWith "Jace" || g.hasSubtype pw .jace)))

/-- True when `o` must attack this combat. Summoning sickness, being tapped,
having no legal attack target, or an unpaid attack cost means it does not have
to attack (CR 508.1d / MSH 130). -/
def mustAttackIfAble (g : Game) (o : GameObject) (attackRequiresCost := false) : Bool :=
  (g.hasAttacksIfAble o || o.status.goaded) && g.canAttack o &&
    g.hasCostFreeLegalAttackTarget o &&
    !mustAttackCanDeclineIfOnlyAttackCosts (attackRequiresCost || g.everyAttackCosts o)

/-- Failed Adventure from Bilbo's graveyard ability is exiled by Bilbo, not
as an Adventure, so it cannot be cast as a permanent later. -/
def exileFailedAdventureFromBilbo (g : Game) (id : ObjectId) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    let name := o.name
    let (g, _) := g.move id .exile none
    g.logMsg s!"{name} is exiled (Bilbo's replacement). It cannot be cast as a permanent"

/-- Create `remaining` token copies of `template` under `controller` with haste
and end-step sacrifice (Venser) as a two-pass simultaneous entry batch inside
`withBatch` (CR 603.6a / 603.10), pausing on `Pending.chooseReplacement`
(`PendingReplacement.copyPermanentTokens`) if token creation or ETB choices
require interactive CR 616.1 selection. -/
partial def createPermanentCopyTokens (g : Game) (controller : PlayerId) (template : CardDef)
    (remaining : Nat) (cause : Option EventCause := none)
    (priorRecentCount : Option Nat := none) (pushedFrame : Bool := false) : Game :=
  if let .chooseReplacement .. := g.pending then
    let baseCount := priorRecentCount.getD g.recentTokenIds.size
    g.chainPendingReplacement
      (.copyPermanentTokens controller template remaining cause baseCount pushedFrame)
  else
    let baseCount := priorRecentCount.getD g.recentTokenIds.size
    let pushed := pushedFrame || (remaining > 0 && g.continuations.isEmpty)
    let g := if !pushedFrame && pushed then g.change (.pushContinuationFrame {}) else g
    let g := g.withBatch cause fun g => Id.run do
      let batchCause := cause.orElse (fun _ => g.currentBatch.bind (·.2))
      let mut g := g
      if remaining > 0 then
        let (g', _) := g.createToken controller template (recordRecent := true)
          (cause := batchCause) (count := remaining)
        g := g'
        if let .chooseReplacement .. := g.pending then
          return g.chainPendingReplacement
            (.copyPermanentTokens controller template 0 batchCause baseCount pushed)
      let allIds := g.recentTokenIds
      let ids := allIds.extract baseCount allIds.size
      if !g.continuations.isEmpty && allIds.size > baseCount then
        g := g.change (.recentTokenIds (allIds.extract 0 baseCount))
      let mut anyEntered := false
      for tid in ids do
        if let some tok := g.findObject? tid then
          if tok.isOnBattlefield then
            anyEntered := true
            g := g.afterPermanentEntersInBatch tok
            if let some tok := g.findObject? tid then
              if tok.isOnBattlefield then
                g := g.createEffect (.keywordsUntilEot tok.id Keyword.haste) (cause := batchCause)
                g := g.registerDelayedTrigger {
                  controller
                  source := some tok
                  kind := .endStepSacrifice tok.id
                  cause := batchCause.getD (.oneShotEffect none none (some controller))
                }
      if anyEntered || remaining == 0 then
        g := g.logMsg "The token copies gain haste and are sacrificed at the next end step"
      if pushed && g.continuations.back? == some {} then
        g := g.change .popContinuationFrame
      return g
    if let .chooseReplacement .. := g.pending then g
    else if g.currentBatch.isNone then g.promptTriggerTargetsIfNeeded
    else g

/-- Whether the source of a proposed activated ability can still pay tap/sacrifice/discard/loyalty. -/
def sourceStillPayable (g : Game) (prop : ProposedSpell) : Bool :=
  match prop.sourceId with
  | none => true
  | some sid =>
    match g.findObject? sid with
    | none => false
    | some src =>
      if prop.kind == .turnFaceUp then
        src.isOnBattlefield && g.controlledBy src prop.caster && src.status.faceDown
      else
      let loyaltyPayable :=
        match prop.activation.bind (·.cost.loyalty) with
        | none => true
        | some sym =>
          src.isOnBattlefield && g.controlledBy src prop.caster &&
          !g.loyaltyActivatedThisTurn src.id &&
          match sym.counters with
          | some k => k ≥ 0 || (src.status.loyaltyCounters : Int) ≥ -k
          | none =>
            let x := ((g.findObject? prop.spellId).bind (·.chosenX)).getD 0
            sym == LoyaltySymbol.minusX && src.status.loyaltyCounters ≥ x
      loyaltyPayable &&
      ((src.isOnBattlefield && g.controlledBy src prop.caster &&
        (!prop.tapSource || !src.status.tapped) && !prop.discardSource) ||
      (src.zone == .graveyard src.owner && src.owner == prop.caster &&
        !prop.tapSource && !prop.sacrificeSource && !prop.discardSource) ||
      (src.zone == .hand src.owner && src.owner == prop.caster &&
        (prop.discardSource || prop.activation.any (·.cost.fra == .exileSourceFromHand)) &&
        !prop.tapSource && !prop.sacrificeSource))

end Game
end Mtg.Engine
