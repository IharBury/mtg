import Mtg.Engine.Game.ModeledTriggers

/-!
# Optional costs, cascade, and the Ring

Kicker (CR 702.33), gift, and teamwork announcements, cascade
(CR 702.85), copying spells, the Ring tempts you (CR 701.54), and
related resolution helpers.
-/

namespace Mtg.Engine
namespace Game

/-- Start an optional “discard a card. If you do, draw `n`” (CR 701.9 / 608.2d). -/
def beginMayDiscardDraw (g : Game) (p : PlayerId) (n : Nat) : Game :=
  if !g.stillInGame p then g
  else
    let pl := g.player p
    if (g.discardableHandIds p).isEmpty then
      g.logMsg s!"{pl.name} has no card to discard"
    else
      g.change (.pending (.mayDiscardDraw p n))
        |>.logMsg s!"{pl.name} may discard a card. If they do, they draw {n}"

/-- Start “sacrifices a creature of their choice” for `p` (CR 701.21 / 608.2d). -/
def beginSacrificeCreature (g : Game) (p : PlayerId) : Game :=
  if !g.stillInGame p then g
  else if (g.sacrificeCreatureChoices p).isEmpty then
    g.logMsg s!"{(g.player p).name} has no creature to sacrifice"
  else
    g.change (.pending (.sacrificeCreature p))
      |>.logMsg s!"{(g.player p).name} must sacrifice a creature of their choice"

/-- As the Ring tempts `p`: get The Ring emblem if needed, gain its next
ability, then choose a Ring-bearer if `p` controls a creature. Re-choosing
the same creature still counts as choosing it. -/
def temptWithTheRing (g : Game) (p : PlayerId) (chosen : Option ObjectId := none) : Game :=
  if !g.stillInGame p then g
  else
    let pl := g.player p
    let nextAbilities := min 4 (pl.theRingAbilities + 1)
    let gainedEmblem := pl.theRingAbilities == 0
    let g :=
      if gainedEmblem then
        g.logMsg s!"{(g.player p).name} gets an emblem named The Ring"
      else g
    let g := g.logMsg
      s!"{(g.player p).name}'s emblem named The Ring gains its next ability ({nextAbilities})"
    let choices := g.ringBearerChoices p
    let pick :=
      match chosen with
      | some id =>
        if choices.any (fun o => o.id == id) then some id else choices[0]?.map (·.id)
      | none => choices[0]?.map (·.id)
    let cause := some (g.resolvingOrRuleCause p)
    g.withBatch cause fun g =>
      let g := if pick.isSome then g.setRingBearer p pick (cause := cause) else g
      let g :=
        match pick with
        | some id =>
          g.logMsg s!"{(g.player p).name} chooses {g.name (g.object! id)} as their Ring-bearer"
        | none =>
          g.logMsg s!"{(g.player p).name} controls no creature to become Ring-bearer"
      g.record (GameEvent.ringTempted g.turnNumber p pick nextAbilities
        (cause := some (g.resolvingOrRuleCause p)))

/-- A targeted spell or ability that would tempt only does so if it resolves. -/
def resolveTargetedTempt (g : Game) (p : PlayerId) (spec : TargetSpec)
    (targets : Array Target) : Game :=
  if !spec.isEmpty && targets.isEmpty then
    g.logMsg "The spell doesn't resolve. The Ring won't tempt you."
  else
    g.withLegalSpecTarget p spec targets (fun g _ => g.temptWithTheRing p)
      (missing := some "The spell doesn't resolve. The Ring won't tempt you.")

/-- Give the promised gift (a Treasure) to `to` before other effects. -/
def givePromisedGift (g : Game) (to : PlayerId) : Game :=
  if !g.stillInGame to then g
  else
    let (g, _) := g.createToken to treasureToken
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.logGiftTreasureGiven to))
    else
      g.logMsg s!"{(g.player to).name} is given a Treasure (gift)"

/-- Pause-safe loop for `resolveCascade` (CR 702.85a / 616.1). -/
partial def resolveCascadeLoop (g : Game) (p : PlayerId) (maxMv : Nat)
    (cause : EventCause) (exiled : Array ObjectId := #[])
    (pendingFromId : Option ObjectId := none) : Game :=
  match pendingFromId with
  | some fid =>
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.resolveCascadeLoop p maxMv cause exiled (some fid)))
    else if !g.stillInGame p then g
    else
      match g.followMovedToZone? fid (· == .exile) with
      | some card =>
        let exiled := exiled.push card.id
        if !g.isLand card && g.objectManaValue card < maxMv then
          let g := g.logMsg s!"{(g.player p).name} exiles cards for cascade (less than {maxMv})"
          let others := exiled.filter (· != card.id)
          g.beginResolutionChoice p (.mayCastCascade card.id others)
            s!"{(g.player p).name} may cast {g.name card} without paying its mana cost (cascade)"
        else
          g.resolveCascadeLoop p maxMv cause exiled none
      | none =>
        g.resolveCascadeLoop p maxMv cause exiled none
  | none =>
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep (.resolveCascadeLoop p maxMv cause exiled none))
    else if !g.stillInGame p then g
    else
      match (g.player p).library.back? with
      | none =>
        let g := g.logMsg s!"{(g.player p).name} exiles cards for cascade (less than {maxMv})"
        g.requestOrderInto exiled (.library p)
          s!"No cheaper nonland card was exiled; {(g.player p).name} puts the exiled cards on the bottom of their library in a random order"
          (cause := some cause)
      | some id =>
        let (g, _) := g.move id .exile none (cause := some cause)
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement
            (.finishPostStep (.resolveCascadeLoop p maxMv cause exiled (some id)))
        else
          g.resolveCascadeLoop p maxMv cause exiled (some id)

/-- Cascade (CR 702.85a): exile from the top until a nonland card with mana
value less than `maxMv`. The player may cast it without paying its mana
cost; the other exiled cards go on the bottom in a random order. -/
def resolveCascade (g : Game) (p : PlayerId) (maxMv : Nat) : Game :=
  if !g.stillInGame p then g
  else
    let (g, cause) := g.allocDelayedCause (some p)
    g.resolveCascadeLoop p maxMv cause

/-- Mark the proposed spell kicked and add the kicker cost. Cannot kick twice. -/
def applyKickerToProposed (g : Game) (kick : Bool) : Except String Game := do
  let some prop := g.proposedSpell | throw "No spell is waiting for kicker"
  if prop.kicked && kick then
    throw "The kicker ability doesn't let you pay a kicker cost more than once"
  let some spell := g.findObject? prop.spellId | throw "The spell left the stack"
  let face := { g.baseCard spell with keywords := g.currentKeywords spell }
  if !kick then
    if prop.sneakAttacker.isNone && face.morph.isSome && face.kicker.isNone then
      let effPerm :=
        if prop.resolutionCast then
          some { (prop.origPerm.getD { player := prop.caster }) with
            ignoreTiming :=
              prop.resolutionIgnoreTiming || prop.origPerm.any (·.ignoreTiming) }
        else prop.origPerm
      g.validateFrontFaceCast prop.caster prop.original face
        (origPermOverride := effPerm)
        (excludeIdOverride := some prop.spellId)
    return g.changeProposals #[.kicked false, .kickerAnnounced true]
  let preSpell := { spell with
    id := prop.original.id
    zone := prop.original.zone
    exiledBy := prop.original.exiledBy
    controller := some prop.caster }
  let extraGen := ManaCost.ofGeneric prop.additionalGeneric
  match face.morph, face.impending, face.kicker with
  | some _, _, none =>
    if g.spellNameForbidden "" then
      throw "Nameless spells can't be cast"
    if prop.sneakAttacker.isSome ||
        GameEvent.castWithFlashback g.events prop.spellId ||
        (prop.origPerm.bind (·.prepareSource)).isSome ||
        g.isForcedWithoutManaCostProposal prop then
      throw "You can't apply more than one alternative cost to a spell (CR 118.9a)"
    if prop.original.zone == .graveyard prop.original.owner then
      throw "Morph can't be used when casting from a graveyard (CR 702.37a)"
    let some morphPerm := g.proposalAltCleanPerm? prop morphSpellFace
      | do
        let allExilePerms := g.playPermissionsFor prop.caster preSpell
        let contClean :=
          allExilePerms.filter fun pm =>
            !pm.withoutManaCost && !pm.payLifeEqualManaValue && pm.prepareSource.isNone
        let hasNullSummoner := preSpell.zone == .exile && g.mayCastExiledBySource prop.caster preSpell
        if !allExilePerms.isEmpty && contClean.isEmpty && !prop.resolutionCast && !hasNullSummoner then
          throw "You can't apply more than one alternative cost to a spell (CR 118.9a)"
        throw "Morph can be cast face down only when you could cast a creature spell (CR 702.37a)"
    let g := g.record (GameEvent.announced g.turnNumber spell.id (costs := #[.morph]))
    let cost :=
      g.playManaCost preSpell morphSpellFace extraGen
        (origPerm := morphPerm)
        (flashback := some (GameEvent.castWithFlashback g.events prop.spellId))
        (explicitAltCost := true)
        (useImplicitPermissions := false)
    return g.changeProposals
      #[.kicked true, .kickerAnnounced true, .cost cost, .payLife 0, .alternativeCost true,
        .needsSacrificeOther false, .needsDiscardCard false]
  | _, some (n, alt), none =>
    if prop.sneakAttacker.isSome ||
        GameEvent.castWithFlashback g.events prop.spellId ||
        (prop.origPerm.bind (·.prepareSource)).isSome ||
        g.isForcedWithoutManaCostProposal prop then
      throw "You can't apply more than one alternative cost to a spell (CR 118.9a)"
    let impFace : CardDef := { face with manaCost := alt }
    let some impPerm := g.proposalAltCleanPerm? prop impFace
      | do
        let allExilePerms := g.playPermissionsFor prop.caster preSpell
        let contClean :=
          allExilePerms.filter fun pm =>
            !pm.withoutManaCost && !pm.payLifeEqualManaValue && pm.prepareSource.isNone
        let hasNullSummoner := preSpell.zone == .exile && g.mayCastExiledBySource prop.caster preSpell
        if !allExilePerms.isEmpty && contClean.isEmpty && !prop.resolutionCast && !hasNullSummoner then
          throw "You can't apply more than one alternative cost to a spell (CR 118.9a)"
        throw s!"{face.name} has sorcery speed"
    let g := g.record (GameEvent.announced g.turnNumber spell.id (costs := #[.impending n]))
    let cost :=
      g.playManaCost preSpell impFace extraGen
        (origPerm := impPerm)
        (flashback := some (GameEvent.castWithFlashback g.events prop.spellId))
        (explicitAltCost := true)
        (useImplicitPermissions := false)
    return g.changeProposals
      #[.kicked true, .kickerAnnounced true, .cost cost, .payLife 0, .alternativeCost true]
  | _, _, none => throw "That spell has no kicker"
  | _, _, some kicker =>
    let g := g.record (GameEvent.announced g.turnNumber spell.id (costs := #[.kicker]))
    let effPerm :=
      prop.origPerm <|>
        (if prop.alternativeCost && prop.sneakAttacker.isNone &&
            !g.castFromGraveyard spell.id &&
            !(match prop.original.zone with | .graveyard _ => true | _ => false) then
          some { player := prop.caster, withoutManaCost := true }
        else none)
    let cost :=
      g.playManaCost preSpell face (kicker.addCost extraGen)
        (origPerm := effPerm)
        (flashback := some (GameEvent.castWithFlashback g.events prop.spellId))
        (explicitAltCost := prop.sneakAttacker.isSome)
        (useImplicitPermissions := false)
    return g.changeProposals #[.kicked true, .kickerAnnounced true, .cost cost]

/-- Promise a gift to `to`. Cannot promise more than once. -/
def applyGiftToProposed (g : Game) (to : Option PlayerId) : Except String Game := do
  let some prop := g.proposedSpell | throw "No spell is waiting for a gift"
  if prop.giftTo.isSome && to.isSome then
    throw "You can't pay a gift cost more than once"
  let some spell := g.findObject? prop.spellId | throw "The spell left the stack"
  let g :=
    match to with
    | some opp =>
      g.record (GameEvent.announced g.turnNumber spell.id (costs := #[.gift opp]))
    | none => g
  return g.changeProposals #[.giftTo to, .giftAnnounced true]

/-- Untapped creatures `p` controls, taken in battlefield order until their
total power is at least `need` (heuristic / test idle choice). -/
def pickTeamworkCreatures (g : Game) (p : PlayerId) (need : Nat) : Array ObjectId :=
  let rec pick (cs : List GameObject) (acc : Array ObjectId) (total : Int) :
      Array ObjectId :=
    if total >= (need : Int) then acc
    else
      match cs with
      | [] => acc
      | o :: rest =>
        if o.status.tapped || g.power o ≤ 0 then pick rest acc total
        else pick rest (acc.push o.id) (total + g.power o)
  pick (g.creaturesControlledBy p).toList #[] 0

/-- Target opponent reveals their hand; you discard a nonland of your choice. -/
def discardNonlandFrom (g : Game) (controller victim : PlayerId) : Game :=
  let handIds := (g.player victim).hand
  let names :=
    handIds.filterMap (fun id =>
      (g.findObject? id).map g.name)
  let g :=
    if !handIds.isEmpty then
      g.record (GameEvent.revealed g.turnNumber victim handIds
        (cause := some (g.resolvingOrRuleCause controller)))
    else g
  let g :=
    if names.isEmpty then
      g.logMsg s!"{(g.player victim).name} reveals an empty hand"
    else
      g.logMsg
        s!"{(g.player victim).name} reveals {String.intercalate ", " names.toList}"
  match (g.player victim).hand.findSome? (fun id =>
      match g.findObject? id with
      | some o => if isDiscardableCard o && !g.isLand o then some o else none
      | none => none) with
  | none => g.logMsg s!"{(g.player victim).name} has no nonland card to discard"
  | some o =>
    g.discardFromHand victim o.id (chooser := some controller)

/-- Finish registering `.endStepReturn` for `exileUntilNextEndStep` once `g.move`
to `.exile` completes. -/
def finishExileUntilNextEndStep (g : Game) (ctrl : PlayerId) (fromId : ObjectId)
    (cause : EventCause) : Game :=
  match g.followMovedToZone? fromId (· == .exile) with
  | none => g
  | some moved =>
    let g := g.registerDelayedTrigger
      { controller := ctrl, source := some moved, kind := .endStepReturn moved.id, cause }
    g.logMsg s!"{g.name moved} is exiled until the beginning of the next end step"

/-- Exile `o` and return it at the beginning of the next end step. -/
def exileUntilNextEndStep (g : Game) (o : GameObject)
    (cause : Option EventCause := none) : Game :=
  let curCtrl := g.controllerOf o
  let (g, cause) :=
    match cause with
    | some c => (g, c)
    | none => g.allocDelayedCause curCtrl
  let ctrl := curCtrl.getD o.owner
  let (g, _) := g.move o.id .exile none (cause := some cause)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement
      (.finishPostStep (.finishExileUntilNextEndStep ctrl o.id cause))
  else
    g.finishExileUntilNextEndStep ctrl o.id cause

/-- Post-entry continuation for `putLandFromHandTapped`. -/
def finishPutLandFromHand (g : Game) (fromId : ObjectId) : Game :=
  match g.followMovedToZone? fromId (· == Zone.battlefield) with
  | some land => g.afterLandEnters land
  | none => g

/-- Put a land from `p`'s hand onto the battlefield tapped (H.E.R.B.I.E.). -/
def putLandFromHandTapped (g : Game) (p : PlayerId) (id : ObjectId) :
    Except String Game := do
  match g.pending with
  | .mayPutLandFromHand q =>
    if p != q then
      throw s!"Only {(g.player q).name} may put a land onto the battlefield"
    let pl := g.player p
    if !pl.hand.contains id then
      throw "That card is not in your hand"
    let some land := g.findObject? id | throw "no such object"
    if !isDiscardableCard land || !g.isLand land then
      throw s!"{g.name land} is not a land card"
    let outerCont? := g.pendingReplacement
    let g := if outerCont?.isSome then g.change (.pendingReplacement none) else g
    let g := g.change (.pending .none)
    let (g, _) := g.putOntoBattlefield id p (tapped := true)
    let g :=
      if g.pending != .none then
        g.chainPendingReplacement (.finishPutLandFromHand id)
      else
        g.finishPutLandFromHand id
    return match outerCont? with
      | some outer => g.chainPendingReplacement outer
      | none => g
  | _ => throw "Not time to put a land from hand onto the battlefield"

end Game
end Mtg.Engine
