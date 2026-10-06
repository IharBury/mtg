import Mtg.Engine.Game.ResolutionHelpers

/-!
# Named resolution effects

Card-specific resolution helpers: casting during resolution (CR 608.2f),
countering spells (CR 701.5), exile-until-source-leaves (CR 610.3),
named tokens, extort, reflexive triggers (CR 603.12), and copy effects
(CR 706 / 707).
-/

namespace Mtg.Engine
namespace Game

/-- Palantír of Orthanc: an illegal target means no influence, scry, draw,
or mill. -/
def applyPalantir (g : Game) (sourceId : ObjectId) (target : Option PlayerId) : Game :=
  match target with
  | none =>
    g.logMsg
      "The target is no longer legal. No influence counter, scry, draw, or mill."
  | some pid =>
    if (g.player pid).lost then
      g.logMsg
        "The target is no longer legal. No influence counter, scry, draw, or mill."
    else
      match g.findObject? sourceId with
      | none =>
        g.logMsg
          "The target is no longer legal. No influence counter, scry, draw, or mill."
      | some src =>
        if !src.isOnBattlefield || pid == src.you then
          g.logMsg
            "The target is no longer legal. No influence counter, scry, draw, or mill."
        else
          let n := g.countersYouPut src 1 (putter := src.controller)
          let g := g.setObject { src with status :=
            { src.status with influence := src.status.influence + n } }
          let g := g.logMsg s!"{src.name} gets an influence counter"
          g.beginScry src.you 2

/-- Copy a spell on the stack, with its modes, targets, X, and paid optional
costs (CR 707.10). The copy is not cast. -/
def copyStackSpell (g : Game) (src : GameObject) (controller : PlayerId) : Game :=
  if (g.player controller).lost then
    g.logMsg s!"{src.name} remains in its current zone (CR 800.4b)"
  else
    let (g, copy) := g.allocObject src.printed controller .stack (some controller)
    let g := g.setObject { copy with
      kicked := src.kicked
      giftPromisedTo := src.giftPromisedTo
      teamworkPaid := src.teamworkPaid
      sneakPaid := src.sneakPaid
      sneakAttackWhom := src.sneakAttackWhom
      chosenX := src.chosenX
      isCopy := true
      adventurerCard := src.adventurerCard }
    let g := g.putStackEntry controller copy.id
    let g :=
      match g.stackEntry? src.id, g.stack.findIdx? (fun e => e.objectId == copy.id) with
      | some orig, some i =>
        { g with stack := g.stack.set! i { g.stack[i]! with
            targets := orig.targets, dividedDamage := orig.dividedDamage
            chosenMode := orig.chosenMode, extraModes := orig.extraModes
            targetsAnnounced := true } }
      | _, _ => g
    g.logMsg s!"A copy of {src.name} is created"

/-- Announce the modes and targets of a spell cast while an ability resolves
(CR 601.2b–c), then finish casting it. A spell that needs a target but has
none can't be cast and returns to where it was (CR 601.2c / 733.1). -/
def beginResolutionCastTargets (g : Game) (p : PlayerId) (prop : ProposedSpell) :
    Game :=
  let face := prop.original.printed
  let g := { g with proposedSpell := some prop }
  if face.isModal then
    if !face.spellModes.any (g.spellModeIsChoosable p) && !face.allowsZeroTargets then
      g.reverseProposedSpell
    else
      { g with pending := .chooseMode p }
        |>.logMsg s!"{(g.player p).name} must choose a mode (CR 601.2b)"
  else if face.requiresTarget || face.isAura then
    if (g.legalCastTargets p face).isEmpty && !face.allowsZeroTargets then
      (g.logMsg s!"{face.name} has no legal target and can't be cast").reverseProposedSpell
    else
      let what := if face.isAura then "a target to enchant" else "a target"
      { g with pending := .chooseTargets p }
        |>.logMsg s!"{(g.player p).name} must choose {what} (CR 601.2c)"
  else if prop.cost.includesManaPayment || prop.needsSacrificeOther || prop.needsDiscardCard then
    { g with pending := .activateManaAbilities p }
      |>.logMsg s!"{(g.player p).name} may activate mana abilities (CR 601.2g)"
  else
    let g := { g with proposedSpell := none }
    g.becomeCast p (g.object! prop.spellId)

/-- Put a card onto the stack as an ability is resolving. Timing may be
ignored. The permission does not last after this ability finishes.
An Aura still announces a target to enchant (CR 601.2c / 303.4). -/
def castAsPartOfResolution (g : Game) (p : PlayerId) (id : ObjectId)
    (ignoreTiming := true) (withoutManaCost := true)
    (exileInstantSorceryInstead := false) : Game :=
  match g.findObject? id with
  | none => g.logMsg "There is no card to cast"
  | some o =>
    if g.splitSecondOnStack then
      g.logMsg s!"{o.name} can't be cast while a spell with split second is on the stack (ruling 839)"
    else if !ignoreTiming && !g.timingAllowsCast p o.printed then
      g.logMsg s!"{o.name} cannot be cast now (timing)"
    else if !withoutManaCost &&
        !(g.player p).manaPool.canPay (g.playManaCost o o.printed) then
      g.logMsg s!"{o.name} cannot be cast (costs)"
    else
      let name := o.name
      let original := o
      let pl := g.player p
      let handBefore := pl.hand
      let stackBefore := g.stack
      let manaBefore := pl.manaPool
      let fromGy := original.zone == .graveyard original.owner
      let wasCopy := original.isCopy
      let (g, newId) := g.move id .stack (some p)
      let g := g.setObject { (g.object! newId) with
        castFromGraveyard := fromGy
        exileInstantSorceryInstead := exileInstantSorceryInstead && fromGy
        isCopy := wasCopy }
      let g := g.putStackEntry p newId
      let g := g.logMsg s!"{(g.player p).name} casts {name} as the ability resolves"
      let cost :=
        if withoutManaCost then ManaCost.empty else g.playManaCost original original.printed
      g.beginResolutionCastTargets p {
        caster := p
        cost
        spellId := newId
        original
        handBefore
        stackBefore
        manaBefore
      }

/-- Cast the first instant or sorcery card with mana value at most `maxMv`
from `p`'s hand as part of a resolution, without paying its mana cost. -/
def castInstantSorceryFromHandMvAtMost (g : Game) (p : PlayerId) (maxMv : Nat) : Game :=
  match (g.player p).hand.findSome? (fun id =>
    match g.findObject? id with
    | some o =>
      if o.printed.isInstantOrSorcery && o.printed.manaValue <= maxMv then some id
      else none
    | none => none) with
  | none => g.logMsg "No instant or sorcery to cast"
  | some id => g.castAsPartOfResolution p id

/-- Why `id` cannot be cast from a pending Cosmic Cube look, if it cannot. -/
def mayCastFromLookedError (g : Game) (p : PlayerId) (ids : Array ObjectId)
    (maxMv : Int) (id : ObjectId) : Option String :=
  if !ids.contains id then
    some "That card is not among the cards you looked at"
  else
    match g.findObject? id with
    | none => some "There is no card to cast"
    | some o =>
      if o.zone != .library p then
        some s!"{o.name} is no longer among the cards you looked at"
      else if o.printed.isLand then
        some "A land cannot be cast"
      else if (o.printed.manaValue : Int) > maxMv then
        some s!"{o.name}'s mana value is greater than the greatest power among attacking creatures you control"
      else if o.printed.isAura && !o.printed.allowsZeroTargets &&
          (g.legalCastTargets p o.printed).isEmpty then
        some s!"{o.name} requires a target to enchant"
      else none

/-- Look at the top `n` cards and wait for the controller to choose whether
to cast one with mana value at most `maxMv` (Cosmic Cube; MSH 356). -/
def beginMayCastFromLooked (g : Game) (p : PlayerId) (n : Nat) (maxMv : Int) :
    Game :=
  let lib := (g.player p).library
  let take := min n lib.size
  let ids := lib.extract (lib.size - take) lib.size
  if ids.isEmpty then
    g.logMsg "No cards to look at"
  else
    { g with pending := .mayCastFromLooked p ids maxMv }.logMsg
      s!"{(g.player p).name} looks at the top {ids.size} cards. You may cast a spell from among them with mana value {maxMv} or less as this ability resolves"

/-- After the Cosmic Cube choice, put unchosen looked-at cards on the bottom
in a random order, then grant priority unless another choice is pending
(for example choosing a target for an Aura just cast). -/
def finishMayCastFromLooked (g : Game) (p : PlayerId) (rest : Array ObjectId) :
    Game :=
  let rest :=
    rest.filter (fun id =>
      match g.findObject? id with
      | some o => o.zone == .library p
      | none => false)
  let msg :=
    s!"{(g.player p).name} puts the rest on the bottom of their library in a random order"
  let g :=
    if rest.isEmpty then g
    else if g.pending != .none then
      -- Keep a pending target choice (CR 601.2c). `requestOrderInto` would
      -- overwrite it when `--norandom` asks for an order.
      if rest.size ≤ 1 || g.norandom then
        g.moveIdsInOrder rest (.library p) |>.logMsg msg
      else
        let (rng, ordered) := g.rng.shuffle rest
        { g with rng }.moveIdsInOrder ordered (.library p) |>.logMsg msg
    else
      g.requestOrderInto rest (.library p) msg
  if g.pending != .none then g
  else g.receivePriority g.activePlayer

/-- Cast one looked-at card as Cosmic Cube resolves, or decline (`none`). -/
def chooseCastFromLooked (g : Game) (p : PlayerId) (castId : Option ObjectId) :
    Except String Game := do
  match g.pending with
  | .mayCastFromLooked q ids maxMv =>
    if p != q then
      throw s!"Only {(g.player q).name} may choose whether to cast a spell"
    match castId with
    | none =>
      let g := g.logMsg s!"{(g.player p).name} declines to cast a spell"
      return finishMayCastFromLooked { g with pending := .none } p ids
    | some id =>
      match g.mayCastFromLookedError p ids maxMv id with
      | some err => throw err
      | none =>
        let g := { g with pending := .none }
        let g := g.castAsPartOfResolution p id
        return g.finishMayCastFromLooked p (ids.filter (· != id))
  | _ => throw "Not time to choose a spell from among looked-at cards"

/-- Put an artifact from hand onto the battlefield, attaching Equipment to `hostId`. -/
def choosePutArtifactFromHand (g : Game) (p : PlayerId) (cardId : ObjectId) :
    Except String Game := do
  match g.pending with
  | .mayPutArtifactFromHand q hostId =>
    if p != q then
      throw s!"Only {(g.player q).name} may put an artifact onto the battlefield"
    let some o := g.findObject? cardId | throw "no such object"
    if o.zone != .hand p then
      throw s!"{o.name} is not in your hand"
    if !o.printed.isArtifact then
      throw s!"{o.name} is not an artifact card"
    let name := o.name
    let (g, newId) := g.putOntoBattlefield cardId p
    let g := g.logMsg s!"{(g.player p).name} puts {name} onto the battlefield"
    let g := g.afterPermanentEnters (g.object! newId)
    let o := g.object! newId
    let g :=
      if o.printed.isEquipment then
        match g.findObject? hostId with
        | some host =>
          if host.isOnBattlefield then g.attachSourceTo o host
          else g.logMsg s!"{host.name} is no longer on the battlefield"
        | none => g.logMsg "The source is no longer in play"
      else g
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | _ => throw "Not time to put an artifact from your hand"

/-- Mill opponents, then a reflexive trigger exists only if cards were milled. -/
def millThenReflexive (g : Game) (opponents : Array PlayerId) (n : Nat) : Game × Bool :=
  let before :=
    opponents.foldl (fun acc pid => acc + (g.player pid).graveyard.size) 0
  let g := opponents.foldl (fun acc pid => acc.mill pid n) g
  let after :=
    opponents.foldl (fun acc pid => acc + (g.player pid).graveyard.size) 0
  (g, after > before)

/-- Put +1/+1 and lifelink until end of turn on a creature (Bard the Bowman). -/
def applyBardBowman (g : Game) (targetId : ObjectId) : Game :=
  match g.findObject? targetId with
  | none => g.logMsg "The target is no longer legal"
  | some o =>
    if !o.isOnBattlefield || !o.isCreature then
      g.logMsg "The target is no longer legal"
    else
      let g := g.addPlusOnePlusOneTo o 1
      let o := g.object! o.id
      let g := g.mapObjectStatus o (·.grantUntilEot Keyword.lifelink)
      g.logMsg s!"{o.name} gains lifelink until end of turn"

/-- Counter a spell on the stack. `exile` puts a permanent spell into exile
and may grant a free cast (CR 701.5 / Thranduil's Decree). -/
def counterStackSpell (g : Game) (spellId : ObjectId) (exilePermanent := false)
    (grantFreeCast := false) (controller : PlayerId := ⟨0⟩) : Game :=
  match g.findObject? spellId with
  | none => g.logMsg "The spell is no longer on the stack"
  | some o =>
    if o.zone != .stack then
      g.logMsg s!"{o.name} is no longer on the stack"
    else if o.abilityEffect.isSome || o.triggeredAbility.isSome then
      let name := o.name
      let g := g.removeFromZoneList o.id .stack |>.ceaseToExist o.id
      g.logMsg s!"{name} is countered"
    else if o.printed.cantBeCountered || o.uncounterableThisCast then
      g.logMsg s!"{o.name} can't be countered"
    else
      let dest :=
        if exilePermanent && o.printed.isPermanentCard then Zone.exile
        else Zone.graveyard o.owner
      let name := o.name
      let (g, newId) := g.move spellId dest none
      let g :=
        if dest == .exile && grantFreeCast then
          let o := g.object! newId
          g.setObject { o with
            playPermission := some {
              player := controller
              turnEndsRemaining := 0
              whileExiled := true
              withoutManaCost := true } }
        else g
      let destNote := if dest == .exile then "exiled" else "countered"
      g.logMsg s!"{name} is {destNote}"

/-- Exile `o` until `source` leaves the battlefield, linking the new exile id. -/
def exileUntilSourceLeaves (g : Game) (sourceId : Option ObjectId) (o : GameObject) :
    Game :=
  let name := o.name
  let fromZone := o.zone
  let (g, newId) := g.move o.id .exile none
  let o := g.object! newId
  let g := g.setObject { o with returnToZone := some fromZone }
  let g :=
    match sourceId.bind g.findObject? with
    | some src =>
      g.setObject { src with linkedExile := src.linkedExile.push newId }
    | none => g
  g.logMsg s!"{name} is exiled until the source leaves the battlefield"

/-- Exile `o` for a leave-the-battlefield trigger (Fiend Hunter). The card
does not return automatically when the source leaves. -/
def exileForLeaveTrigger (g : Game) (sourceId : Option ObjectId) (o : GameObject) :
    Game :=
  let name := o.name
  let (g, newId) := g.move o.id .exile none
  let g :=
    match sourceId.bind g.findObject? with
    | some src =>
      g.setObject { src with leaveTriggerExile := src.leaveTriggerExile.push newId }
    | none => g
  g.logMsg s!"{name} is exiled"

/-- Return one exiled id to the battlefield under its owner. Auras attach
without targeting; if they cannot attach, they remain in exile. -/
def returnExiledId (g : Game) (id : ObjectId) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    if o.zone != .exile then g
    else
      let name := o.name
      let owner := o.owner
      match o.returnToZone with
      | some (.hand p) =>
        let (g, _) := g.move id (.hand p) none
        g.logMsg s!"{name} returns to {(g.player p).name}'s hand"
      | some (.graveyard p) =>
        let (g, _) := g.move id (.graveyard p) none
        g.logMsg s!"{name} returns to {(g.player p).name}'s graveyard"
      | _ =>
        if o.printed.isAura then
          match g.battlefield.find? (fun h => h.auraCanEnchant o.printed) with
          | none =>
            g.logMsg s!"{name} remains in exile (can't be attached legally; CR 614.6)"
          | some host =>
            let hostId := host.id
            let hostName := host.name
            let (g, newId) := g.move id .battlefield (some owner)
            let o := g.object! newId
            let g := g.setObject { o with attachedTo := some hostId }
            let g := g.logMsg s!"{name} returns attached to {hostName} (does not target)"
            g.afterPermanentEnters (g.object! newId)
        else
          let (g, newId) := g.move id .battlefield (some owner)
          let o := g.object! newId
          let sick := !o.printed.keywords.haste
          let g := g.setObject { o with status := { o.status with summoningSick := sick } }
          let g := g.logMsg s!"{name} returns to the battlefield"
          g.afterPermanentEnters (g.object! newId)

/-- Return cards linked-exiled by `source` (leave-trigger list first, then
until-leaves). -/
def returnLinkedExile (g : Game) (source : GameObject) : Game :=
  (source.leaveTriggerExile ++ source.linkedExile).foldl
    (fun acc id => acc.returnExiledId id) g

/-- Named MSH tokens that carry extra rules text. -/
def zabuToken : CardDef :=
  { (creatureToken "Zabu" #["Cat"] 2 2 (some .green)) with
    supertypes := #[.legendary]
    triggeredAbilities := #[.onLandYouControlEntersPlusOnePlusOne] }

def redwingToken : CardDef :=
  { (creatureToken "Redwing" #["Bird", "Scout"] 1 1 (some .blue) Keyword.flying) with
    supertypes := #[.legendary]
    triggeredAbilities := #[.onAttackScry 1] }

def theVoidToken : CardDef :=
  { (creatureToken "The Void" #["Horror", "Villain"] 5 5 (some .black)
      ((Keyword.flying).merge Keyword.indestructible)) with
    supertypes := #[.legendary]
    staticAbilities := #[.attacksEachCombatIfAble] }

def galactusAttackTrigger : Effect := {
  targeting := .of (.filtered { noun := "target land", types := #[.land] })
  resolution := .onPermanent .destroy
  phrase := "Whenever Galactus attacks, destroy target land."
}

def galactusToken : CardDef :=
  { (creatureToken "Galactus" #["Elder", "Alien"] 16 16 (some .black)
      ((Keyword.flying).merge Keyword.trample)) with
    supertypes := #[.legendary]
    triggeredAbilities := #[.triggered .attack galactusAttackTrigger] }

def tigerGodToken : CardDef :=
  { (creatureToken "The Tiger God" #["Cat", "God"] 4 4 (some .green)) with
    supertypes := #[.legendary]
    staticAbilities := #[.cantBeBlockedByMoreThan 1] }

def sturdyShieldToken : CardDef :=
  { name := "Sturdy Shield"
    types := #[.artifact]
    subtypes := #["Equipment"]
    staticAbilities := #[.equippedCreatureGets 1 2]
    activatedAbilities := #[
      { cost := { mana := ManaCost.ofGeneric 2 }
        effect := Effect.attachToTargetCreatureYouControl
        onlyAsSorcery := true }]
    isToken := true }

def createNamedToken (g : Game) (controller : PlayerId) (printed : CardDef) : Game :=
  let (g, _) := g.createToken controller printed
  g

def withSourceOnBattlefield (g : Game) (sourceId : Option ObjectId)
    (f : Game → GameObject → Game)
    (missing := "The ability's source is no longer in play")
    (leftMsg : Option String := none) : Game :=
  match sourceId.bind g.findObject? with
  | some o =>
    if o.isOnBattlefield then f g o
    else g.logMsg (leftMsg.getD s!"{o.name} is no longer on the battlefield")
  | none =>
    g.logMsg missing

/-- Run `f` if the source is still on the battlefield; otherwise log the same
`missing` message whether the source is gone or was never found. -/
def withSourceStillOnBattlefield (g : Game) (sourceId : Option ObjectId)
    (f : Game → GameObject → Game)
    (missing := "The source has left the battlefield. Nothing is exiled.") : Game :=
  g.withSourceOnBattlefield sourceId f missing (leftMsg := some missing)

/-- Increment the source's plan counter, queue the matching chapter trigger,
then run `k`. -/
def incrementPlanThen (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (k : Game → GameObject → Game) : Game :=
  g.withSourceOnBattlefield sourceId fun g o =>
    let n := g.countersYouPut o 1 (putter := some controller)
    let g := Id.run do
      let mut g := g
      for _ in [0:n] do
        match g.findObject? o.id with
        | some cur =>
          g := g.setObject { cur with status := { cur.status with plan := cur.status.plan + 1 } }
          let cur := g.object! cur.id
          g := g.putMatchingSourceTriggers controller cur (.nthPlanCounter cur.status.plan)
        | none => pure ()
      return g
    k g (g.object! o.id)

/-- Current power of `sourceId` if it is still on the battlefield; otherwise
last-known power, falling back to the object's current power. -/
def sourcePowerAtResolution (g : Game) (sourceId : Option ObjectId)
    (lastKnownPower : Option Int := none) : Int :=
  match sourceId.bind g.findObject? with
  | some o =>
    if o.isOnBattlefield then g.power o
    else lastKnownPower.getD (g.power o)
  | none => lastKnownPower.getD (0 : Int)

/-- `sourcePowerAtResolution` as a `Nat`. -/
def sourcePowerNatAtResolution (g : Game) (sourceId : Option ObjectId)
    (lastKnownPower : Option Int := none) : Nat :=
  (g.sourcePowerAtResolution sourceId lastKnownPower).toNat

/-- Current P/T of `sourceId` if it is still on the battlefield; otherwise
last-known values (defaulting to 0). -/
def sourcePTAtResolution (g : Game) (sourceId : Option ObjectId)
    (lastKnownPower lastKnownToughness : Option Int := none) : Int × Int :=
  match sourceId.bind g.findObject? with
  | some src =>
    if src.isOnBattlefield then (g.power src, g.toughness src)
    else (lastKnownPower.getD 0, lastKnownToughness.getD 0)
    | none => (lastKnownPower.getD 0, lastKnownToughness.getD 0)

/-- Top `count` cards of `p`'s library (last = current top). -/
def scryLookedIds (g : Game) (p : PlayerId) (count : Nat) : Array ObjectId :=
  let lib := (g.player p).library
  let n := min count lib.size
  lib.extract (lib.size - n) lib.size

/-- Log that `p` looks at the top `n` cards of their library. -/
def logLookAtTop (g : Game) (p : PlayerId) (n : Nat) : Game :=
  g.logMsg s!"{(g.player p).name} looks at the top {n} cards"

/-- Exile the top `n` cards of `fromPlayer`'s library. `caster` may play
them this turn. `logAfter ownerName cardName` is the per-card message. -/
def exileTopForPlay (g : Game) (fromPlayer caster : PlayerId) (n : Nat)
    (logAfter : String → String → String) : Game :=
  Id.run do
    let mut g := g
    for _ in [0:n] do
      let pl := g.player fromPlayer
      if pl.library.isEmpty then
        g := g.logMsg s!"{pl.name} has no cards in their library to exile"
      else
        let top := pl.library.back!
        let cardName := (g.object! top).name
        let (g', newId) := g.move top .exile none
        g := g'
        let o := g.object! newId
        g := g.setObject { o with
          playPermission := some { player := caster, turnEndsRemaining := 1 } }
        g := g.logMsg (logAfter pl.name cardName)
    return g

/-- Exile the top `n` cards of `p`'s library. They may be played this turn. -/
def exileTopPlayThisTurn (g : Game) (p : PlayerId) (n : Nat) : Game :=
  g.exileTopForPlay p p n fun owner card =>
    s!"{owner} exiles {card} and may play it this turn"

/-- Extort is paid: each opponent loses 1 life and `controller` gains the
life actually lost (CR 702.101a / MSH 292). Extort does not target (MSH 296). -/
def extortDrain (g : Game) (controller : PlayerId) : Game :=
  let (g, lost) :=
    (g.livingOpponents controller).foldl (fun (acc : Game × Nat) pl =>
      let before := (acc.1.player pl.id).life
      let g := acc.1.loseLife pl.id 1
      let after := (g.player pl.id).life
      let delta := if before > after then (before - after).toNat else 0
      (g, acc.2 + delta)) (g, 0)
  g.gainLife controller lost |>.logMsg "Extort is paid"

/-- A stack object to stand for `sourceId` as an ability's source. -/
def abilitySourceFor (g : Game) (controller : PlayerId) (sourceId : Option ObjectId) : GameObject :=
  match sourceId.bind g.findObject? with
  | some o => o
  | none =>
    { id := sourceId.getD ⟨0⟩, printed := { name := "The ability", types := #[] }
      owner := controller, controller := some controller, zone := .battlefield }

/-- Put a reflexive triggered ability (“When you do, …”) on the stack with
`effect` (CR 603.12). Its targets are chosen now. -/
def putReflexiveTrigger (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (effect : Effect) : Game :=
  let src := g.abilitySourceFor controller sourceId
  let marker : TriggeredAbility := .triggered .enter effect {}
  if effect.requiresTarget && !effect.allowsZeroTargets &&
      (g.legalTargetsForKind controller effect.targetKind sourceId).isEmpty then
    g.logMsg s!"{src.name}'s reflexive ability has no legal target and is removed (CR 603.3d)"
  else
    let (g, obj) := g.putStackAbility src controller (abilityEffect := some effect)
      (triggeredAbility := some marker)
    let g := g.setObject { obj with sourceId := sourceId }
    let g := g.logMsg s!"{src.name}'s reflexive ability is put on the stack"
    g.promptTriggerTargetsIfNeeded

/-- The reflexive triggered ability `kind` of an MSH card, with its targets
(MSH 359–369). -/
def modeledReflexiveEffect (kind paid : Nat) : Effect :=
  let base : Effect := { resolution := .fra (.mshReflexive kind paid) }
  let creature (f : TargetFilter) : TargetFilter := { f with types := #[.creature] }
  match kind with
  | 0 =>
    { base with
      targeting := .of (.filtered (creature
        { noun := "another target nonattacking creature you control", controller := .you
          another := true, nonattacking := true }))
      phrase := "Another target nonattacking creature you control gains indestructible until end of turn" }
  | 1 => { base with targeting := .of .playerOrCreature, phrase := "This deals 2 damage to any target" }
  | 3 =>
    { base with targeting := .of .creatureYouControl
                phrase := "Put an indestructible counter on target creature you control" }
  | 4 =>
    { base with targeting := .of .opponent
                phrase := "You control target opponent during their next turn" }
  | 5 =>
    { base with targeting := .of .opponent
                phrase := "Target opponent exiles the top five cards of their library" }
  | 6 =>
    { base with targeting := .of .creatureCardInYourGraveyard
                phrase := "Return target creature card from your graveyard to the battlefield tapped and attacking with a finality counter on it" }
  | 7 =>
    { base with targeting := .of .oppNonland
                phrase := "Destroy target nonland permanent an opponent controls" }
  | 8 =>
    { base with
      targeting := .of (.filtered { noun := "any other target", zone := .anyTarget, another := true })
      phrase := "This deals damage equal to the number of +1/+1 counters on it to any other target" }
  | 9 =>
    { base with
      targeting := .of (.filtered (creature { noun := "target creature with haste", withHaste := true }))
      phrase := "Target creature with haste can't be blocked this turn except by creatures with haste" }
  | 10 =>
    { base with targeting := .of .playerOrCreature, dividedDamage := some (7, 2)
                phrase := "It deals 7 damage divided as you choose among one or two targets" }
  | 11 =>
    { base with
      targeting := .of (.filtered
        { noun := "up to two target instant and/or sorcery cards from your graveyard"
          zone := .yourGraveyard, types := #[.instant, .sorcery] })
      maxTargets := 2, allowsZeroTargets := true
      phrase := "Return up to two target instant and/or sorcery cards from your graveyard to your hand" }
  | 12 =>
    { base with targeting := .of .creature, phrase := "Put a +1/+1 counter on target creature" }
  | _ => base

/-- Put MSH reflexive ability `kind` on the stack; its targets are chosen now
(CR 603.12 / MSH 359–369). -/
def queueModeledReflexive (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (kind : Nat) (paid : Nat := 0) : Game :=
  g.putReflexiveTrigger controller sourceId (modeledReflexiveEffect kind paid)

/-- Run `act` when `paid` is positive; otherwise log `unpaid`. -/
def ifPaid (g : Game) (paid : Nat) (unpaid : String) (act : Game → Game) : Game :=
  if paid == 0 then g.logMsg unpaid else act g

/-- Offer to pay `cost` up to `maxTimes` times; when the player does, MSH
reflexive ability `kind` triggers (MSH 359–369). -/
def offerPayForReflexive (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (cost : Array ManaSymbol) (kind : Nat) (maxTimes : Nat := 1) : Game :=
  let shown := String.join (cost.toList.map toString)
  let times := if maxTimes > 1 then s!" up to {maxTimes} times" else ""
  { g with pending := .fraChoice controller (.mayPayManaForReflexive cost maxTimes kind sourceId) }
    |>.logMsg s!"{(g.player controller).name} may pay {shown}{times}"

/-- Sacrifice the Plan if it is still on the battlefield. `gone` is logged
when the source left; `missing` when it was never found. -/
def sacrificePlanIfOnBattlefield (g : Game) (sourceId : Option ObjectId)
    (gone := fun (name : String) => s!"{name} is no longer on the battlefield")
    (missing := "The Plan is no longer on the battlefield") : Game :=
  match sourceId.bind g.findObject? with
  | some o =>
    if o.isOnBattlefield then g.sacrificeToGraveyard o "the Plan is completed"
    else g.logMsg (gone o.name)
  | none =>
    g.logMsg missing

/-- Sacrifice the Plan if it is still on the battlefield. Queue the
reflexive second ability only if the sacrifice happened (MSH 360–362,
368–369). -/
def sacrificePlanThenQueueReflexive (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (kind : Nat) : Game :=
  let stillThere :=
    match sourceId.bind g.findObject? with
    | some o => o.isOnBattlefield
    | none => false
  let g := g.sacrificePlanIfOnBattlefield sourceId
    (gone := fun name =>
      s!"{name} is no longer on the battlefield. The reflexive ability doesn't trigger.")
    (missing :=
      "The Plan is no longer on the battlefield. The reflexive ability doesn't trigger.")
  if stillThere then g.queueModeledReflexive controller sourceId kind else g

/-- Ask `caster` to cast up to `casts` of the exiled nonland cards. -/
def offerExileCasts (g : Game) (caster : PlayerId) (spells : Array ObjectId)
    (casts : Nat) : Game :=
  { g with pending := .fraChoice caster (.mayCastUpToFromExile spells casts) }
    |>.logMsg s!"{(g.player caster).name} may cast up to {casts} spells from among the exiled cards without paying their mana costs"

/-- Exile the top `n` cards of `fromPlayer`'s library. `caster` may cast up
to `casts` nonland cards from among them without paying their mana costs. -/
def exileTopMayCastUpTo (g : Game) (fromPlayer caster : PlayerId) (n casts : Nat) : Game :=
  Id.run do
    let mut g := g
    let mut ids : Array ObjectId := #[]
    for _ in [0:n] do
      let pl := g.player fromPlayer
      if pl.library.isEmpty then
        g := g.logMsg s!"{pl.name} has no cards in their library to exile"
      else
        let top := pl.library.back!
        let name := (g.object! top).name
        let (g', newId) := g.move top .exile none
        g := g'
        ids := ids.push newId
        g := g.logMsg s!"{pl.name} exiles {name}"
    let spells := ids.filter (fun id =>
      (g.findObject? id).any (fun o => !o.printed.isLand))
    if spells.isEmpty || casts == 0 then g
    else g.offerExileCasts caster spells casts

/-- Exile the top `n` cards of `fromPlayer`'s library. `caster` may play
them this turn. -/
def exileTopMayCast (g : Game) (fromPlayer caster : PlayerId) (n : Nat) : Game :=
  g.exileTopForPlay fromPlayer caster n fun owner card =>
    s!"{owner} exiles {card}; {(g.player caster).name} may cast it"

/-- Return a graveyard creature tapped and attacking with a finality
counter (Grim Reaper). -/
def returnFromGyTappedAttackingFinality (g : Game) (controller : PlayerId)
    (cardId : ObjectId) (attackingWhom : Option PlayerId := none) : Game :=
  match g.findObject? cardId with
  | none => g.logMsg "The target is no longer in the graveyard"
  | some o =>
    if !(o.printed.isCreature && o.zone == .graveyard controller) then
      g.logMsg "The target is no longer a creature card in your graveyard"
    else
      let whom :=
        match attackingWhom with
        | some pid => some pid
        | none =>
          match (g.livingOpponents controller)[0]? with
          | some pl => some pl.id
          | none => none
      let (g, newId) := g.putOntoBattlefield o.id controller (tapped := true)
      let o := g.object! newId
      let g := g.setObject { o with status := { o.status with
        attacking := true
        attackingWhom := whom } }
      let o := g.object! newId
      let g := g.addFinalityTo o
      let o := g.object! newId
      g.afterPermanentEnters o |>.logMsg s!"{o.name} enters tapped and attacking"

/-- Resolve MSH reflexive ability `kind` with its announced targets. A target
that is no longer legal is skipped (MSH 125). -/
def resolveModeledReflexive (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (kind paid : Nat) (targets : Array Target) (division : Array Nat := #[]) : Game :=
  let tkind := (modeledReflexiveEffect kind paid).targetKind
  let illegal := some "The target is no longer legal"
  match kind with
  | 0 =>
    g.withLegalKindPermanent controller tkind targets
      (fun g o => g.grantUntilEotLogged o Keyword.indestructible) sourceId illegal
  | 1 =>
    g.withLegalKindTarget controller tkind targets
      (fun g tgt => g.dealDamageToTarget tgt 2) sourceId illegal
  | 3 =>
    g.withLegalKindPermanent controller tkind targets
      (fun g o => g.addIndestructibleCounter o) sourceId illegal
  | 4 =>
    g.withLegalKindPlayer controller tkind targets (fun g pid =>
      let g := g.setPlayerControl controller pid
      { g with controlOnNextTakenTurn := true })
      sourceId illegal
  | 5 =>
    g.withLegalKindPlayer controller tkind targets
      (fun g pid => g.exileTopMayCastUpTo pid controller 5 2) sourceId illegal
  | 6 =>
    g.withLegalKindTarget controller tkind targets (fun g tgt =>
      match tgt with
      | Target.card id | Target.permanent id => g.returnFromGyTappedAttackingFinality controller id
      | _ => g) sourceId illegal
  | 7 =>
    g.withLegalKindPermanent controller tkind targets
      (fun g o => g.destroyPermanent o) sourceId illegal
  | 8 =>
    let counters :=
      match sourceId.bind g.findObject? with
      | some o => if o.isOnBattlefield then o.status.plusOnePlusOne else paid
      | none => paid
    g.withLegalKindTarget controller tkind targets
      (fun g tgt => g.dealDamageToTarget tgt (Int.ofNat counters)) sourceId illegal
  | 9 =>
    g.withLegalKindPermanent controller tkind targets
      (fun g o =>
        g.mapObjectStatus o (fun s => { s with cantBeBlockedExceptByHasteUntilEot := true })
          |>.logMsg s!"{o.name} can't be blocked this turn except by creatures with haste")
      sourceId illegal
  | 10 =>
    let legal := g.legalTargetsForKind controller tkind sourceId
    (List.range targets.size).foldl (fun g i =>
      let tgt := targets[i]!
      if legal.contains tgt then g.dealDamageToTarget tgt (Int.ofNat (division[i]?.getD 0))
      else g.illegalAbilityTarget tgt) g
  | 11 =>
    let legal := g.legalTargetsForKind controller tkind sourceId
    targets.foldl (fun g tgt =>
      match tgt with
      | Target.card id =>
        if legal.contains tgt then g.returnToHand id controller else g.illegalAbilityTarget tgt
      | _ => g) g
  | 12 =>
    g.withLegalKindPermanent controller tkind targets
      (fun g o => g.addPlusOnePlusOneTo o 1) sourceId illegal
  | _ => g

/-- Whether an MSH reflexive ability is on the stack. -/
def hasModeledReflexiveOnStack (g : Game) : Bool :=
  g.stack.any (fun e =>
    match ((g.findObject? e.objectId).bind (·.abilityEffect)).map Effect.resolution with
    | some (Resolution.fra (FraResolution.mshReflexive _ _)) => true
    | _ => false)

/-- Resolve the newest MSH reflexive ability on the stack with `targets`
(and `division` for divided damage), as if they had been announced. -/
def applyModeledReflexive (g : Game) (targets : Array Target := #[])
    (division : Array Nat := #[]) : Game :=
  let found := g.stack.reverse.findSome? (fun e =>
    match ((g.findObject? e.objectId).bind (·.abilityEffect)).map Effect.resolution with
    | some (Resolution.fra (FraResolution.mshReflexive kind paid)) =>
      some (e.objectId, e.controller, kind, paid)
    | _ => none)
  match found with
  | none => g.logMsg "No reflexive triggered ability is on the stack"
  | some (id, controller, kind, paid) =>
    let sourceId := (g.findObject? id).bind (·.sourceId)
    let g := { (g.removeFromZoneList id .stack).ceaseToExist id with pending := .none }
    if kind == 10 then
      let division :=
        if !division.isEmpty then division
        else if targets.size == 1 then #[7] else #[4, 3]
      if targets.isEmpty || targets.size > 2 || division.size != targets.size then
        g.logMsg "Choose one or two targets, each assigned a damage amount (CR 601.2d)"
      else if division.any (· == 0) then
        g.logMsg "Each target must receive at least 1 damage (CR 601.2d)"
      else if division.foldl (· + ·) 0 != 7 then
        g.logMsg "Must assign all 7 damage among the chosen targets (CR 601.2d)"
      else g.resolveModeledReflexive controller sourceId kind paid targets division
    else g.resolveModeledReflexive controller sourceId kind paid targets division

/-- Merge subtype names without duplicates. -/
def mergeSubtypes (xs ys : Array String) : Array String :=
  ys.foldl (fun acc y => if acc.any (· == y) then acc else acc.push y) xs

/-- `o` becomes a copy of `src`'s copiable values. The permanent does not
enter or leave the battlefield (MSH 322 / 326 / 329 / 330). Counters,
attachments, and status are unchanged. If `src` is already a copy, `o`
copies whatever `src` copied (MSH 194 / 198 / 199 / 201). -/
def becomeCopyOf (g : Game) (o : GameObject) (src : GameObject)
    (untilEot := false) (untilNextTurn := false)
    (untilSourceLeaves : Option ObjectId := none)
    (exceptName : Option String := none)
    (forceLegendary := false) (notLegendary := false)
    (addCreature := false) (addSubtypes : Array String := #[])
    (setPT : Option (Int × Int) := none)
    (addVigilance := false) (replaceCreatureLine := false) : Game :=
  let restore := o.copyRestore.getD o.printed
  let printed0 := src.printed
  let types :=
    if replaceCreatureLine then #[.creature]
    else if addCreature && !printed0.types.any (· == .creature) then
      printed0.types.push .creature
    else printed0.types
  let supertypes :=
    if notLegendary then printed0.supertypes.filter (· != .legendary)
    else if forceLegendary && !printed0.supertypes.any (· == .legendary) then
      printed0.supertypes.push .legendary
    else printed0.supertypes
  let printed : CardDef :=
    { printed0 with
      name := exceptName.getD printed0.name
      types
      subtypes :=
        if replaceCreatureLine then addSubtypes
        else mergeSubtypes printed0.subtypes addSubtypes
      supertypes
      power :=
        match setPT with
        | some (p, _) => some p
        | none => printed0.power
      toughness :=
        match setPT with
        | some (_, t) => some t
        | none => printed0.toughness
      keywords :=
        if addVigilance then Keywords.merge printed0.keywords Keyword.vigilance
        else printed0.keywords }
  let g := g.setObject { o with
    printed
    copyRestore := some restore
    copyUntilEot := untilEot
    copyUntilNextTurn := untilNextTurn
    copyUntilSourceLeaves := untilSourceLeaves }
  g.logMsg s!"{restore.name} becomes a copy of {printed0.name}"

/-- Copy an activated or triggered ability on the stack. The copy is not
cast or activated (MSH 34 / 40 / 66) and uses the same source and X
(MSH 47 / 302 / 303). -/
def copyStackAbility (g : Game) (src : GameObject) (controller : PlayerId) : Game :=
  if (g.player controller).lost then
    g.logMsg s!"{src.name} remains in its current zone (CR 800.4b)"
  else
    let (g, copy) := g.allocObject src.printed controller .stack (some controller)
      (abilityEffect := src.abilityEffect)
      (triggeredAbility := src.triggeredAbility)
      (sourceId := src.sourceId)
      (lastKnownPower := src.lastKnownPower)
      (lastKnownToughness := src.lastKnownToughness)
    let g := g.setObject { copy with
      chosenX := src.chosenX
      isCopy := true
      teamworkPaid := src.teamworkPaid }
    let g := g.putStackEntry controller copy.id
    let g :=
      match g.stack.findIdx? (fun e => e.objectId == src.id) with
      | some i =>
        let orig := g.stack[i]!
        let last := g.stack.size - 1
        { g with stack := g.stack.set! last { g.stack[last]! with
          targets := orig.targets
          dividedDamage := orig.dividedDamage
          chosenMode := orig.chosenMode } }
      | none => g
    g.logMsg s!"A copy of {src.name} is created"

/-- Reveal `p`'s hand (Cloak and Dagger; MSH 132 / 225). -/
def revealHand (g : Game) (p : PlayerId) : Game :=
  let names :=
    (g.player p).hand.foldl (fun acc id =>
      match g.findObject? id with
      | some o => if acc == "" then o.name else s!"{acc}, {o.name}"
      | none => acc) ""
  g.logMsg s!"{(g.player p).name} reveals their hand ({names})"

/-- After every player has chosen, the chosen creature cards enter together,
the exiled cards return to their owners' hands, and the spell is exiled. -/
def finishWorldsWithinWorlds (g : Game) (exiled chosen : Array ObjectId)
    (sourceId : Option ObjectId) : Game :=
  Id.run do
    let mut g := g
    let mut entered : Array ObjectId := #[]
    for id in chosen do
      match g.findObject? id with
      | some o =>
        if o.zone == .hand o.owner && o.printed.isCreature then
          let pid := o.owner
          let (g', newId) := g.putOntoBattlefield id pid
          g := g'
          entered := entered.push newId
          g := g.logMsg s!"{(g.player pid).name} puts {o.name} onto the battlefield"
        else pure ()
      | none => pure ()
    for id in entered do
      match g.findObject? id with
      | some o => g := g.afterPermanentEnters o
      | none => pure ()
    for nid in exiled do
      match g.findObject? nid with
      | some o =>
        if o.zone == .exile then
          let (g', _) := g.move o.id (.hand o.owner) none
          g := g'.logMsg s!"{o.name} is returned to its owner's hand"
        else pure ()
      | none => pure ()
    match sourceId.bind g.findObject? with
    | some src =>
      if src.zone == .exile then return g
      else
        let (g', _) := g.move src.id .exile none
        return g'.logMsg s!"{src.name} is exiled"
    | none => return g

/-- Ask the next player who has a creature card in hand, in the order given. -/
def offerWorldsCreatures (g : Game) (rest : List PlayerId)
    (exiled chosen : Array ObjectId) (sourceId : Option ObjectId) : Game :=
  match rest with
  | [] => g.finishWorldsWithinWorlds exiled chosen sourceId
  | pid :: more =>
    let eligible :=
      (g.player pid).hand.filter (fun id =>
        (g.findObject? id).any (·.printed.isCreature))
    if eligible.isEmpty then
      g.offerWorldsCreatures more exiled chosen sourceId
    else
      { g with pending :=
          .fraChoice pid (.worldsPutCreatures eligible more.toArray exiled chosen sourceId) }
        |>.logMsg
          s!"{(g.player pid).name} may put any number of creature cards from their hand onto the battlefield"

/-- Worlds Within Worlds (MSH 96 / ruling 449): exile creatures, then each
player may put any number of creature cards from hand. Those creatures enter
together, the exiled cards return to their owners' hands, then the spell
is exiled. -/
def applyWorldsWithinWorlds (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) : Game :=
  Id.run do
    let mut g := g
    let creatures := g.battlefield.filter (fun o => o.isCreature)
    let mut exiled : Array ObjectId := #[]
    for o in creatures do
      let name := o.name
      let (g', nid) := g.move o.id .exile none
      g := g'
      exiled := exiled.push nid
      g := g.logMsg s!"{name} is exiled"
    let order :=
      let apnap := g.apnapOrder
      if apnap.isEmpty then #[controller]
      else apnap
    return g.offerWorldsCreatures order.toList exiled #[] sourceId

end Game
end Mtg.Engine
