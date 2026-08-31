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
          let g := g.setObject { src with status :=
            { src.status with influence := src.status.influence + 1 } }
          let g := g.logMsg s!"{src.name} gets an influence counter"
          g.beginScry src.you 2

/-- After putting a resolving-cast spell on the stack, announce the Aura's
enchant target (CR 601.2c / 303.4). The mana cost may have been skipped. -/
def beginResolutionCastTargets (g : Game) (p : PlayerId) (prop : ProposedSpell) :
    Game :=
  let face := prop.original.printed
  if face.isAura &&
      (face.allowsZeroTargets || !(g.legalCastTargets p face).isEmpty) then
    { g with pending := .chooseTargets p, proposedSpell := some prop }
      |>.logMsg s!"{(g.player p).name} must choose a target to enchant (CR 601.2c)"
  else g

/-- Put a card onto the stack as an ability is resolving. Timing may be
ignored. The permission does not last after this ability finishes.
An Aura still announces a target to enchant (CR 601.2c / 303.4). -/
def castAsPartOfResolution (g : Game) (p : PlayerId) (id : ObjectId)
    (ignoreTiming := true) (withoutManaCost := true) : Game :=
  match g.findObject? id with
  | none => g.logMsg "There is no card to cast"
  | some o =>
    if !ignoreTiming && !g.timingAllowsCast p o.printed then
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
      let (g, newId) := g.move id .stack (some p)
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
          match g.battlefield.find? (fun h => h.isCreature) with
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
    oracleText := "Flying, indestructible\nThe Void attacks each combat if able." }

def galactusToken : CardDef :=
  { (creatureToken "Galactus" #["Elder", "Alien"] 16 16 (some .black)
      ((Keyword.flying).merge Keyword.trample)) with
    supertypes := #[.legendary] }

def tigerGodToken : CardDef :=
  { (creatureToken "The Tiger God" #["Cat", "God"] 4 4 (some .green)) with
    supertypes := #[.legendary]
    staticAbilities := #[.cantBeBlockedExceptBy 2] }

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
    let g := g.setObject { o with status := { o.status with plan := o.status.plan + 1 } }
    let o := g.object! o.id
    let g := g.putMatchingSourceTriggers controller o (.nthPlanCounter o.status.plan)
    k g o

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

/-- Resolve one pending extort trigger. You may pay at most once (MSH 371).
Life gained equals life actually lost (MSH 292). Extort does not target
(MSH 296). -/
def applyExtort (g : Game) (pay : Bool) : Game :=
  match g.pendingExtortController with
  | none => g.logMsg "No extort trigger is pending"
  | some controller =>
    if g.pendingExtort == 0 then
      g.logMsg "No extort trigger is pending"
    else
      let g := { g with
        pendingExtort := g.pendingExtort - 1
        pendingExtortController :=
          if g.pendingExtort - 1 == 0 then none else some controller }
      if !pay then
        g.logMsg "Extort is not paid"
      else
        let (g, lost) :=
          (g.livingOpponents controller).foldl (fun (acc : Game × Nat) pl =>
            let before := (acc.1.player pl.id).life
            let g := acc.1.loseLife pl.id 1
            let after := (g.player pl.id).life
            let delta :=
              if before > after then (before - after).toNat else 0
            (g, acc.2 + delta)) (g, 0)
        g.gainLife controller lost |>.logMsg "Extort is paid"

/-- Queue a reflexive MSH trigger. The first ability has no targets; the
second is chosen after the "if you do" (MSH 359–369). -/
def queueModeledReflexive (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (kind : Nat) (paid : Nat := 0) : Game :=
  { g with
      pendingMshReflexive := some (controller, sourceId, kind)
      pendingMshReflexivePaid := paid }
    |>.logMsg "A reflexive triggered ability triggers"

/-- Run `act` when `paid` is positive; otherwise log `unpaid`. -/
def ifPaid (g : Game) (paid : Nat) (unpaid : String) (act : Game → Game) : Game :=
  if paid == 0 then g.logMsg unpaid else act g

/-- Queue a reflexive trigger when a cost (`paid`) was actually paid. -/
def queueModeledReflexiveIfPaid (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (kind : Nat) (paid : Nat) (unpaid : String) :
    Game :=
  g.ifPaid paid unpaid fun g => g.queueModeledReflexive controller sourceId kind paid

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

/-- Exile the top `n` cards of `fromPlayer`'s library. `caster` may play
them this turn (Doom Reigns Supreme). -/
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

/-- Resolve the pending MSH reflexive trigger with the now-chosen targets.
If every target is illegal, nothing happens (MSH 125). -/
def applyModeledReflexive (g : Game) (targets : Array Target := #[])
    (division : Array Nat := #[]) : Game :=
  match g.pendingMshReflexive with
  | none => g.logMsg "No reflexive triggered ability is pending"
  | some (controller, sourceId, kind) =>
    let paid := g.pendingMshReflexivePaid
    let g := { g with pendingMshReflexive := none, pendingMshReflexivePaid := 0 }
    if kind == 0 then
      g.withLegalKindPermanent controller .creatureYouControl targets
        (fun g o => g.grantUntilEotLogged o Keyword.indestructible)
        sourceId (some "The target is no longer legal")
    else if kind == 1 then
      g.withLegalKindTarget controller .playerOrCreature targets (fun g tgt =>
        match tgt with
        | Target.player pid => g.dealDamageToPlayer pid 2
        | Target.permanent id =>
          match g.findObject? id with
          | some o => g.dealDamageToPermanent o 2
          | none => g
        | _ => g) sourceId (some "The target is no longer legal")
    else if kind == 2 then
      if targets.isEmpty then
        g.drawThenBeginDiscard controller
      else
        g.withLegalKindTarget controller .playerOrCreature targets (fun g tgt =>
          match tgt with
          | Target.player pid =>
            let _ := paid
            g.dealDamageToPlayer pid 2
          | Target.permanent id =>
            match g.findObject? id with
            | some o => g.mapObjectStatus o (·.grantUntilEot Keyword.cantBeBlocked)
            | none => g
          | Target.card _ => g) sourceId (some "The target is no longer legal")
    else if kind == 3 then
      g.withLegalKindPermanent controller .creatureYouControl targets
        (fun g o =>
          g.mapObjectStatus o (fun s =>
            { s with indestructibleCounters := s.indestructibleCounters + 1 })
            |>.logMsg s!"{o.name} gets an indestructible counter")
        sourceId (some "The target is no longer legal")
    else if kind == 4 then
      g.withLegalKindPlayer controller .opponent targets (fun g pid =>
        let g := g.setPlayerControl controller pid
        { g with controlOnNextTakenTurn := true })
        sourceId (some "The target is no longer legal")
    else if kind == 5 then
      g.withLegalKindPlayer controller .opponent targets
        (fun g pid => g.exileTopMayCast pid controller 5)
        sourceId (some "The target is no longer legal")
    else if kind == 6 then
      match targets[0]? with
      | some (Target.card id) | some (Target.permanent id) =>
        g.returnFromGyTappedAttackingFinality controller id
      | _ => g.logMsg "The target is no longer legal"
    else if kind == 7 then
      g.withLegalKindPermanent controller .oppNonland targets
        (fun g o => g.destroyPermanent o) sourceId (some "The target is no longer legal")
    else if kind == 8 then
      let amt : Int := Int.ofNat paid
      g.withLegalKindTarget controller .playerOrCreature targets (fun g tgt =>
        match tgt with
        | Target.player pid => g.dealDamageToPlayer pid amt
        | Target.permanent id =>
          if sourceId == some id then
            g.logMsg "Red Hulk can't target himself"
          else
            match g.findObject? id with
            | some o => g.dealDamageToPermanent o amt
            | none => g
        | _ => g) sourceId (some "The target is no longer legal")
    else if kind == 9 then
      g.withLegalKindPermanent controller .creature targets
        (fun g o =>
          if g.hasHaste o then
            g.mapObjectStatus o (fun s =>
              { s with cantBeBlockedExceptByHasteUntilEot := true })
              |>.logMsg s!"{o.name} can't be blocked this turn except by creatures with haste"
          else
            g.logMsg s!"{o.name} doesn't have haste")
        sourceId (some "The target is no longer legal")
    else if kind == 10 then
      if targets.isEmpty then
        g.logMsg "No targets were chosen"
      else if targets.size > 2 then
        g.logMsg "Choose one or two targets"
      else
        let amounts :=
          if division.isEmpty then
            if targets.size == 1 then #[7] else #[4, 3]
          else division
        if amounts.size != targets.size then
          g.logMsg "Each target must be assigned a damage amount"
        else if amounts.any (· == 0) then
          g.logMsg "Each target must receive at least 1 damage"
        else if amounts.foldl (· + ·) 0 != 7 then
          g.logMsg "Must assign all 7 damage among the chosen targets"
        else
          Id.run do
            let mut g := g
            for i in [0:targets.size] do
              let tgt := targets[i]!
              let n := amounts[i]!
              g := g.withLegalKindTarget controller .playerOrCreature #[tgt]
                (fun g t => g.dealDamageToTarget t (Int.ofNat n))
                sourceId (some "The target is no longer legal")
            return g
    else if kind == 11 then
      targets.foldl (fun g tgt =>
        match tgt with
        | Target.card id | Target.permanent id =>
          match g.findObject? id with
          | some o =>
            if o.zone == .graveyard controller && o.printed.isInstantOrSorcery then
              g.returnToHand id controller
            else g
          | none => g
        | _ => g) g
    else
      g

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
    (addVigilance := false) : Game :=
  let restore := o.copyRestore.getD o.printed
  let printed0 := src.printed
  let types :=
    if addCreature && !printed0.types.any (· == .creature) then
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
      subtypes := mergeSubtypes printed0.subtypes addSubtypes
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

/-- Worlds Within Worlds (MSH 96): exile creatures, put creature cards from
hands onto the battlefield, return the exiled cards to hands, exile the spell. -/
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
    for pid in order do
      let ids := (g.player pid).hand
      for id in ids do
        match g.findObject? id with
        | some o =>
          if o.printed.isCreature then
            let (g', _) := g.putOntoBattlefield o.id pid
            g := g'
            g := g.logMsg s!"{(g.player pid).name} puts {o.name} onto the battlefield"
          else g := g
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
      let (g', _) := g.move src.id .exile none
      return g'.logMsg s!"{src.name} is exiled"
    | none =>
      return g

end Game
end Mtg.Engine
