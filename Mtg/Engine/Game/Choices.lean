import Mtg.Engine.Game.Casting

/-!
# Resolution choices

Choices made while resolving: sacrifice choices, lifetime modal choices
(Alliance, Gollum), and card-specific helpers such as beholding a
quality, Riddles in the Dark, The Black Gate, and Gríma's exile.
-/

namespace Mtg.Engine
namespace Game

/-- Permanents `p` may sacrifice to pay “sacrifice another creature or artifact”. -/
def sacrificeCreatureOrArtifactChoices (g : Game) (p : PlayerId) (sourceId : ObjectId) :
    Array GameObject :=
  let src := g.findObject? sourceId
  let creatureOrPlaneswalker := src.any (fun s => (g.baseCard s).additionalCostSacrificeCreatureOrPlaneswalker)
  let creatureOnly := src.any (fun s => (g.baseCard s).additionalCostSacrificeCreature)
  g.permanentsOf p |>.filter (fun o =>
    o.id != sourceId &&
      if creatureOrPlaneswalker then g.isCreature o || g.isPlaneswalker o
      else if creatureOnly then g.isCreature o
      else g.isCreature o || g.isArtifact o)

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

/-- Apply the first unused mode of `sourceId`, or log `gone` / `exhausted`. -/
def applyNextUnusedMode (g : Game) (sourceId : Option ObjectId)
    (unused : GameObject → Array Nat)
    (apply : Game → ObjectId → Nat → Game)
    (exhausted : String)
    (gone := "The ability is removed from the stack with no effect") : Game :=
  match sourceId with
  | none => g.logMsg gone
  | some sid =>
    match g.findObject? sid with
    | none => g.logMsg gone
    | some src =>
      match (unused src)[0]? with
      | none => g.logMsg exhausted
      | some mode => apply g sid mode

/-- As Gollum enters, choose odd (`true`) or even (`false`). Zero is even. -/
def chooseGollumParity (g : Game) (sourceId : ObjectId) (odd : Bool) : Game :=
  match g.findObject? sourceId with
  | none => g
  | some src =>
    let g := g.changeStatus sourceId (.chosenOdd (some odd))
    g.logMsg
      (if odd then s!"{src.name}: odd is chosen" else s!"{src.name}: even is chosen")

/-- Behold a quality: choose a matching permanent you control or reveal a
matching card from your hand. Later zone changes do not un-behold (117). -/
def beholdQuality (g : Game) (p : PlayerId) (quality : CardSubtype)
    (cause : Option EventCause := none) : Game :=
  let hasPerm := (g.permanentsOf p).any (fun o => g.hasSubtype o quality)
  let hasHand :=
    (g.player p).hand.any (fun id =>
      match g.findObject? id with
      | some o => o.printed.hasSubtype quality
      | none => false)
  if hasPerm || hasHand then
    let effCause := g.resolveOptionalCause cause (fallbackCtrl := some p)
    let g := g.record (GameEvent.beheld g.turnNumber p quality (cause := effCause))
    g.logMsg s!"{(g.player p).name} beholds a {quality}"
  else
    g.logMsg s!"{(g.player p).name} does not behold a {quality}"

/-- True when `p` has beheld `quality`, even if the card or permanent later left. -/
def qualityWasBeheld (g : Game) (p : PlayerId) (quality : CardSubtype) : Bool :=
  (g.beheldQualities p).contains quality

/-- Choose a creature type as this permanent enters. The static pump applies
immediately; no player may act between the choice and the bonus. -/
def chooseCreatureTypeAsEnters (g : Game) (sourceId : ObjectId) (creatureType : CardSubtype) :
    Game :=
  match g.findObject? sourceId with
  | none => g
  | some src =>
    let g := g.changeStatus sourceId (.chosenCreatureType (some creatureType))
    g.logMsg s!"{src.name}: {creatureType} is chosen as it enters"

/-- Draw one card for each graveyard with seven or more cards. -/
def drawPerSevenCardGraveyard (g : Game) (p : PlayerId) : Game :=
  let n := g.players.filter (fun pl => pl.graveyard.size >= 7) |>.size
  if n == 0 then
    g.logMsg s!"{(g.player p).name} draws no cards (no graveyard has seven cards)"
  else
    g.draw p n

/-- Discard every card in `p`'s hand. Zero cards is a legal discard and is
logged (Sauron, the Dark Lord). -/
def discardEntireHand (g : Game) (p : PlayerId) (cause : Option EventCause := none) : Game :=
  let ids := (g.player p).hand
  let discarded := ids.size
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
    ids.foldl (fun acc id =>
      match acc.findObject? id with
      | none => acc
      | some o =>
        let (acc, _) := acc.move id (.graveyard o.owner) none (cause := cause?)
        acc) g
  g.logMsg s!"{(g.player p).name} discards {discarded} card(s)"

/-- Discard the hand (zero cards is legal) and draw that many. The choice is
made during resolution; nothing happens between discard and draw. -/
def mayDiscardHandDrawThatMany (g : Game) (p : PlayerId) (doDiscard : Bool) : Game :=
  if !doDiscard then
    g.logMsg s!"{(g.player p).name} does not discard their hand"
  else
    let n := (g.player p).hand.size
    let g := g.discardEntireHand p
    if n == 0 then g else g.draw p n

/-- Discard the hand, then draw `n` cards. An empty hand is a legal discard
(Sauron, the Dark Lord). -/
def discardHandThenDraw (g : Game) (p : PlayerId) (n : Nat) : Game :=
  let g := g.discardEntireHand p
  if n == 0 then g else g.draw p n

/-- Players currently tied for most life. -/
def playersWithMostLife (g : Game) : Array PlayerId :=
  let living := g.livingPlayers
  match living[0]? with
  | none => #[]
  | some first =>
    let best := living.foldl (fun acc pl => max acc pl.life) first.life
    living.filter (fun pl => pl.life == best) |>.map (·.id)

/-- The Black Gate: check most life as the ability resolves, then those
creatures (including later ones) cannot block the target this turn. -/
def applyBlackGateUnblockable (g : Game) (attackerId : ObjectId)
    (chosen : PlayerId) : Game :=
  if !(g.playersWithMostLife).contains chosen then
    g.logMsg "The chosen player does not have the most life. The ability does nothing."
  else
    match g.findObject? attackerId with
    | none => g.logMsg "The target is no longer legal"
    | some o =>
      if !o.isOnBattlefield then
        g.logMsg "The target is no longer legal"
      else
        let g := g.createEffect (.cantBeBlockedByPlayerUntilEot attackerId chosen)
        g.logMsg
          s!"{o.name} can't be blocked by creatures {(g.player chosen).name} controls this turn"

/-- Put the returned cards onto the battlefield as Food artifacts only.
They keep name, mana cost, mana value, abilities, and legendary. -/
def supperForSpidersReturn (g : Game) (controller : PlayerId)
    (ids : Array ObjectId) : Game :=
  ids.foldl (fun acc id =>
    match acc.findObject? id with
    | none => acc
    | some o =>
      if o.zone != .graveyard o.owner then acc
      else
        let (acc, newId) := acc.move id .battlefield (some controller)
          (summoningSick := true) (applyHope := false) (onlyFoodArtifact := true)
        let acc := acc.afterPermanentEnters (acc.object! newId)
        let o := acc.object! newId
        acc.logMsg s!"{o.name} returns as a Food artifact") g

/-- Exile the top `n` cards face down. They may be played while exiled if you
control `subtype` (CR 610.1 / 701.14). Timing and costs are unchanged. -/
def exileTopPlayIfYouControlSubtype (g : Game) (p : PlayerId) (n : Nat)
    (subtype : CardSubtype) : Game :=
  Id.run do
    let (g0, cause?) : Game × Option EventCause :=
      if n == 0 || (g.player p).library.isEmpty then (g, none)
      else
        let (g, c) := g.allocDelayedCause (some p)
        (g, some c)
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

/-- Exile cards from the top of `victim`'s library until an instant or
sorcery, face up. Returns the game, that card, and the other exiled cards
in the order they were exiled. -/
partial def exileUntilInstantOrSorcery (g : Game) (victim : PlayerId)
    (cause : Option EventCause := none) :
    Game × Option ObjectId × Array ObjectId :=
  Id.run do
    let (g0, cause?) : Game × Option EventCause :=
      match cause with
      | some c => (g, some c)
      | none =>
        if (g.player victim).library.isEmpty then (g, none)
        else
          let (g, c) := g.allocDelayedCause (some victim)
          (g, some c)
    let mut g := g0
    let mut exiled : Array ObjectId := #[]
    let mut found : Option ObjectId := none
    while found.isNone && !(g.player victim).library.isEmpty do
      let top := (g.player victim).library.back!
      let name := (g.object! top).name
      let (g', newId) := g.move top .exile none (cause := cause?)
      g := g'
      let o := g.object! newId
      g := g.logMsg s!"{(g.player victim).name} exiles {name} face up"
      if o.printed.isInstantOrSorcery then
        found := some newId
      else
        exiled := exiled.push newId
    return (g, found, exiled)

/-- Exile cards from `victim`'s library until an instant or sorcery, face up.
An empty library becomes that player's library again. The found card may be
cast as this ability resolves, ignoring timing. Uncast cards go on the bottom
in a random order. -/
def grimaExileUntilInstantOrSorcery (g : Game) (controller victim : PlayerId)
    (castTheCard : Bool) : Game :=
  let (g, cause) := g.allocDelayedCause (some controller)
  let (g, found, exiled) := g.exileUntilInstantOrSorcery victim (cause := some cause)
  match found with
  | none =>
    g.requestOrderInto exiled (.library victim)
      s!"{(g.player victim).name} randomizes the exiled cards; they become that player's library"
      (cause := some cause)
  | some instId =>
    let g :=
      if castTheCard then
        let o := g.object! instId
        let (g, _) := g.move instId .stack (some controller)
          (verb := some .cast) (actor := some controller) (cause := some cause)
        g.logMsg
          s!"{(g.player controller).name} casts {o.name} as the ability resolves"
      else
        (g.move instId (.library victim) none (cause := some cause)).1
    g.requestOrderInto exiled (.library victim)
      s!"{(g.player victim).name} puts the remaining exiled cards on the bottom of their library in a random order"
      (cause := some cause)

/-- An uncast copy ceases the next time state-based actions are checked. -/
def ceaseUncastCopies (g : Game) : Game :=
  g.objects.foldl (fun acc o =>
    if o.isCopy && o.zone != .stack && o.zone != .battlefield then
      let acc := acc.ceaseToExist o.id (cause := some (.stateBased .copyOutsideStackOrBf))
      acc.logMsg s!"{o.name} ceases to exist"
    else acc) g

/-- True when `p` can pay Saruman's ward (discard an enchantment, instant,
or sorcery card). -/
def canPaySarumanWard (g : Game) (p : PlayerId) : Bool :=
  (g.player p).hand.any (fun id =>
    match g.findObject? id with
    | some o => o.printed.isEnchantment || o.printed.isInstant || o.printed.isSorcery
    | none => false)

/-- Legendary artifacts and creatures `p` may sacrifice to Sauron's ward. -/
def legendaryWardSacrificeChoices (g : Game) (p : PlayerId) : Array GameObject :=
  (g.permanentsOf p).filter (fun o =>
    g.isLegendary o && (g.isCreature o || g.isArtifact o))

/-- Split the top four library cards into a face-up pile and a face-down pile.
A 4/0 split is legal. The face-down pile is not revealed if it is put into
hand. -/
def riddlesInTheDark (g : Game) (p : PlayerId) (faceUpCount : Nat)
    (chooseFaceDown : Bool) : Game :=
  let lib := (g.player p).library
  let n := min 4 lib.size
  let taken := lib.extract (lib.size - n) lib.size
  let faceUpN := min faceUpCount taken.size
  let faceUp := taken.extract (taken.size - faceUpN) taken.size
  let faceDown := taken.extract 0 (taken.size - faceUpN)
  let g := g.logMsg
    s!"{(g.player p).name} separates {faceUp.size} face-up and {faceDown.size} face-down"
  let toHand := if chooseFaceDown then faceDown else faceUp
  let toGy := if chooseFaceDown then faceUp else faceDown
  let g :=
    if chooseFaceDown then
      g.logMsg "The face-down pile is put into hand without being revealed"
    else
      g.logMsg "The face-up pile is put into hand"
  let g := g.withBatch none fun g =>
    toHand.foldl (fun acc id =>
      (acc.move id (.hand p) none).1) g
  g.withBatch none fun g =>
    toGy.foldl (fun acc id =>
      (acc.move id (.graveyard p) none).1) g

/-- Put one Riddles pile into `p`'s hand and the other into the graveyard.
The face-down pile is not revealed when it is the one that goes to hand. -/
def applyRiddlesPiles (g : Game) (p : PlayerId) (faceUp faceDown : Array ObjectId)
    (chooseFaceDown : Bool) (alreadyRevealed : Bool := false) : Game :=
  let g := g.logMsg
    s!"{(g.player p).name} separates {faceUp.size} face-up and {faceDown.size} face-down"
  let toHand := if chooseFaceDown then faceDown else faceUp
  let toGy := if chooseFaceDown then faceUp else faceDown
  let g :=
    if chooseFaceDown then
      g.logMsg "The face-down pile is put into hand without being revealed"
    else
      let g :=
        if !alreadyRevealed && !faceUp.isEmpty then
          g.record (GameEvent.revealed g.turnNumber p faceUp
            (cause := some (g.resolvingOrRuleCause p)))
        else g
      let g := g.logMsg "The face-up pile is put into hand"
      faceUp.foldl (fun acc id =>
        match acc.findObject? id with
        | some o => acc.logMsg s!"{(acc.player p).name} reveals {o.name}"
        | none => acc) g
  let g := g.withBatch none fun g =>
    toHand.foldl (fun acc id =>
      (acc.move id (.hand p) none).1) g
  g.withBatch none fun g =>
    toGy.foldl (fun acc id =>
      (acc.move id (.graveyard p) none).1) g

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
def hasAttacksIfAble (o : GameObject) : Bool :=
  o.staticAbilities.any (fun
    | .attacksEachCombatIfAble => true
    | _ => false)

/-- Generic mana each creature must pay to attack `defender` (Dáin). -/
def attackTaxPerCreature (g : Game) (defender : PlayerId) : Nat :=
  if !g.hasEnduringStory defender then 0
  else
    (g.permanentsOf defender).foldl (fun acc src =>
      (g.staticAbilities src).foldl (fun acc ab =>
        match ab.attackTaxIfEnduringStory? with
        | some n => acc + n
        | none => acc) acc) 0

/-- Every legal defending player charges a cost to be attacked. -/
def everyAttackCosts (g : Game) (o : GameObject) : Bool :=
  match g.controllerOf o with
  | none => false
  | some p =>
    let opps := g.livingOpponents p
    !opps.isEmpty && opps.all (fun pl => g.attackTaxPerCreature pl.id > 0)

/-- True when `o` must attack this combat. Summoning sickness, being tapped,
or an unpaid attack cost means it does not have to attack (MSH 130). -/
def mustAttackIfAble (g : Game) (o : GameObject) (attackRequiresCost := false) : Bool :=
  let attacksEachCombat :=
    (g.staticAbilities o).any (fun
      | .attacksEachCombatIfAble => true
      | _ => false)
  (attacksEachCombat || o.status.goaded) && g.canAttack o &&
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

/-- A token copy of a battlefield permanent. The copy is not kicked. -/
def copyBattlefieldPermanent (g : Game) (src : GameObject) (controller : PlayerId)
    (cause : Option EventCause := none) : Game × GameObject :=
  g.createToken controller (g.copiableValues src) (cause := cause)

/-- Whether the source of a proposed activated ability can still pay tap/sacrifice/discard/loyalty. -/
def sourceStillPayable (g : Game) (prop : ProposedSpell) : Bool :=
  match prop.sourceId with
  | none => true
  | some sid =>
    match g.findObject? sid with
    | none => false
    | some src =>
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
