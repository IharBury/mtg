import Mtg.Engine.Game.Mulligans

/-!
# Decision handlers

Handlers for `Pending` decisions: finishing scry and surveil, discarding, paying
generic costs, library-side and permanent choices, declining, keeping
the opening hand, the legend rule, ordering triggers, taking mulligans,
and supplying outside randomness.
-/

namespace Mtg.Engine
namespace Game

def uniqueObjectIds (ids : Array ObjectId) : Bool :=
  Id.run do
    let mut seen : Array ObjectId := #[]
    for id in ids do
      if seen.contains id then
        return false
      seen := seen.push id
    return true

def isPermutation (a b : Array ObjectId) : Bool :=
  a.size == b.size && uniqueObjectIds a && a.all (fun x => b.contains x)

/-- Check that `top ++ rest` rearranges the `count` cards `p` is looking at
as `q`'s pending scry or surveil. -/
def checkLookedPiles (g : Game) (p q : PlayerId) (count : Nat)
    (top rest : Array ObjectId) (verb rule : String) : Except String Unit := do
  if p != q then
    throw s!"Only {(g.player q).name} may {verb}"
  if !uniqueObjectIds (top ++ rest) then
    throw "Duplicate card"
  if !isPermutation (top ++ rest) (g.scryLookedIds p count) then
    throw s!"{verb.capitalize} must rearrange the cards you looked at ({rule})"

/-- Clear the finished scry or surveil, draw any follow-up cards, offer
Palantír's opponent their choice, and give the active player priority. -/
def finishLibraryLook (g : Game) : Game :=
  let g := { g with pending := .none, surveilReturnMvAtMost := none
                    surveilReturnNoncreatureNonland := false }
  let g :=
    match g.fraAfterLook with
    | some (c, src, next) =>
      ({ g with fraAfterLook := none }).applyFra c default next.toResolution #[] src
    | none => g
  let g :=
    match g.pendingDrawAfterScry with
    | some (q, n) =>
      let g := { g with pendingDrawAfterScry := none }
      g.draw q n
    | none => g
  if g.pending != .none then g
  else
    match g.palantirAfterScry with
    | some (controller, opp, sid) =>
      ({ g with palantirAfterScry := none }).offerPalantirChoice controller opp sid
    | none => g.receivePriority g.activePlayer

/-- Log putting `top` back on top, unless they stay in the looked-at order. -/
def logPutOnTop (g : Game) (p : PlayerId) (looked top : Array ObjectId) : Game :=
  Id.run do
    let mut g := g
    if top != looked then
      for id in top do
        g := g.logMsg
          s!"{(g.player p).name} puts {(g.object! id).name} on top of their library"
    return g

/-- Finish scrying: put `bottom` on the bottom (first = new bottom) and `top`
on top (last = new top) of the library, each pile in the given order (CR 701.20). -/
def finishScry (g : Game) (p : PlayerId) (top bottom : Array ObjectId) :
    Except String Game := do
  match g.pending with
  | .scry q count =>
    g.checkLookedPiles p q count top bottom "scry" "CR 701.20"
    let looked := g.scryLookedIds p count
    let pl := g.player p
    let lower := pl.library.extract 0 (pl.library.size - count)
    let mut g := g
    for id in bottom do
      g := g.logMsg
        s!"{(g.player p).name} puts {(g.object! id).name} on the bottom of their library"
    g := g.logPutOnTop p looked top
    g := g.setPlayer { (g.player p) with library := bottom ++ lower ++ top }
    return g.finishLibraryLook
  | .surveil _ _ => throw "You are surveilling, not scrying; use surveil (CR 701.25)"
  | _ => throw "Not time to scry (CR 701.20)"

/-- Finish surveilling: put `graveyard` into the graveyard in that order and
`top` back on top (last = new top) of the library (CR 701.25). -/
def finishSurveil (g : Game) (p : PlayerId) (top graveyard : Array ObjectId) :
    Except String Game := do
  match g.pending with
  | .surveil q count =>
    g.checkLookedPiles p q count top graveyard "surveil" "CR 701.25"
    let looked := g.scryLookedIds p count
    let pl := g.player p
    let lower := pl.library.extract 0 (pl.library.size - count)
    let mut g := g.logPutOnTop p looked top
    g := g.setPlayer { (g.player p) with library := graveyard ++ lower ++ top }
    for id in graveyard do
      let card := g.object! id
      let (g', newId) := g.move id (.graveyard p) none
      g := g'.logMsg s!"{(g.player p).name} puts {card.name} into their graveyard (surveil)"
      match g.surveilReturnMvAtMost with
      | some n =>
        if g.objectManaValue card ≤ n then
          let (g', _) := g.move newId (.hand p) none
          g := g'.logMsg s!"{(g.player p).name} puts {card.name} into their hand"
      | none =>
        if g.surveilReturnNoncreatureNonland && !card.printed.isCreature &&
            !card.printed.isLand then
          let (g', _) := g.move newId (.hand p) none
          g := g'.logMsg s!"{(g.player p).name} puts {card.name} into their hand"
    return g.finishLibraryLook
  | .scry _ _ => throw "You are scrying, not surveilling; use scry (CR 701.20)"
  | _ => throw "Not time to surveil (CR 701.25)"

/-- Remove one symbol a convoking creature of `colors` can pay: a colored
(or hybrid) symbol of one of its colors, else one generic mana (ruling 865). -/
def convokePayOne (cost : ManaCost) (colors : ColorSet) : Option ManaCost :=
  let syms := cost.symbols
  let without (i : Nat) : Array ManaSymbol := syms.extract 0 i ++ syms.extract (i + 1) syms.size
  let colored := syms.findIdx? (fun s =>
    match s with
    | .colored c => colors.contains c
    | .hybrid a b => colors.contains a || colors.contains b
    | .twobrid c => colors.contains c
    | _ => false)
  match colored with
  | some i => some { symbols := without i }
  | none =>
    match syms.findIdx? (fun s => match s with | .generic n => n > 0 | _ => false) with
    | some i =>
      match syms[i]! with
      | .generic n =>
        if n == 1 then some { symbols := without i }
        else some { symbols := syms.set! i (.generic (n - 1)) }
      | _ => none
    | none => none

/-- Convoke (CR 702.51a) and improvise (CR 702.126a): while paying for a spell
with convoke, tap untapped creatures you control; each pays for {1} or one
mana of its colors. With improvise, tap untapped artifacts you control; each
pays for {1}. Both apply to the total cost after alternative and additional
costs and don't change the mana value (rulings 864 / 869). A permanent
already tapped, for example for mana, can't be tapped again (ruling 863).
Summoning sickness doesn't matter, and an attacking creature stays attacking
(rulings 866 / 867). A creature artifact pays for convoke when the spell has
convoke. -/
def convoke (g : Game) (p : PlayerId) (ids : Array ObjectId) : Except String Game := do
  match g.pending, g.proposedSpell with
  | .activateManaAbilities q, some prop =>
    if p != q then
      throw s!"Only {(g.player q).name} may pay"
    let some spell := g.findObject? prop.spellId | throw "The spell left the stack"
    let hasConvoke := prop.kind == .spell && spell.printed.keywords.convoke
    let hasImprovise := prop.kind == .spell && g.spellHasImprovise spell.printed p
    if !hasConvoke && !hasImprovise then
      throw s!"{spell.name} doesn't have convoke or improvise (CR 702.51 / 702.126)"
    let mut g := g
    let mut cost := prop.cost
    let mut tapped := prop.tapped
    for id in ids do
      let some o := g.findObject? id | throw "no such object"
      if !(o.isOnBattlefield && o.controlledBy p) then
        throw s!"You don't control {o.name}"
      if o.status.tapped then
        throw s!"{o.name} is already tapped (ruling 863)"
      if hasConvoke && o.isCreature then
        match convokePayOne cost o.printed.colors with
        | none => throw s!"{o.name} can't pay for any of the remaining cost"
        | some c => cost := c
        g := g.becomeTapped o
        g := g.logMsg s!"{(g.player p).name} taps {o.name} to convoke {spell.name}"
      else if hasImprovise && o.types.contains .artifact then
        if cost.genericCount == 0 then
          throw s!"No generic mana is left for {o.name} to pay (CR 702.126a)"
        cost := cost.reduceGeneric 1
        g := g.becomeTapped o
        g := g.logMsg s!"{(g.player p).name} taps {o.name} for improvise"
      else
        throw s!"{o.name} can't help pay for {spell.name}"
      tapped := tapped.push id
    return { g with proposedSpell := some { prop with cost, tapped } }
  | _, _ => throw "No spell is being paid for (CR 601.2h)"

/-- Proliferate once (CR 701.34a): give each chosen permanent and player
another counter of each kind already there. Any subset may be chosen,
including none and opponents' permanents (rulings 881 / 882); cards in other
zones can't be (ruling 881). No player can act between proliferations
(ruling 880), and each one may choose a different set (ruling 886). -/
def finishProliferate (g : Game) (p : PlayerId) (chosen : Array Target) :
    Except String Game := do
  match g.pending with
  | .chooseProliferate q remaining =>
    if p != q then
      throw s!"Only {(g.player q).name} may proliferate"
    if chosen.toList.eraseDups.length != chosen.size then
      throw "Choose each permanent or player at most once"
    let mut g := g
    let mut loyaltyPut := false
    for t in chosen do
      match t with
      | .permanent id =>
        let some o := g.findObject? id | throw "no such object"
        if !o.isOnBattlefield then
          throw s!"{o.name} is not a permanent on the battlefield (CR 701.34a)"
        if !o.status.hasCounters then
          throw s!"{o.name} has no counters"
        let hadLoyalty := o.status.loyaltyCounters > 0
        g := g.mapObjectStatus o Status.proliferatedExceptPlusOne
        let o := g.object! id
        g := if o.status.plusOnePlusOne > 0 then g.addPlusOnePlusOneTo o 1 else g
        if hadLoyalty && o.printed.isPlaneswalker then loyaltyPut := true
        g := g.logMsg s!"{(g.player p).name} proliferates {o.name}"
      | .player pid =>
        let pl := g.player pid
        if pl.poison == 0 then
          throw s!"{pl.name} has no counters"
        g := g.setPlayer { pl with poison := pl.poison + 1 }
        g := g.logMsg s!"{(g.player p).name} gives {pl.name} another poison counter"
      | .card _ => throw "Only permanents and players can be chosen (CR 701.34a)"
    if loyaltyPut then
      g := g.queueLoyaltyPutTriggers p
    if chosen.isEmpty then
      g := g.logMsg s!"{(g.player p).name} proliferates, choosing nothing"
    -- “Whenever you proliferate” triggers even if nothing was chosen (ruling 884).
    g := g.putFraEventTriggers p .youProliferate
    if remaining > 1 then
      return { g with pending := .chooseProliferate p (remaining - 1) }
    else
      return ({ g with pending := .none }).receivePriority g.activePlayer
  | _ => throw "Not time to proliferate (CR 701.34)"

/-- Shared pending-discard core (CR 701.9): `p` must be the pending player
`q` and `id` must be in `p`'s hand; the discard is logged (with `logSuffix`)
and the card moves to its owner's graveyard. `countDiscard` bumps
`cardsDiscardedThisTurn`. Returns the discarded card. -/
def discardPendingCard (g : Game) (p q : PlayerId) (id : ObjectId)
    (logSuffix : String := "") (countDiscard := true) :
    Except String (Game × GameObject) := do
  if p != q then
    throw s!"Only {(g.player q).name} may discard"
  if !(g.player p).hand.contains id then
    throw "That card is not in your hand"
  let some card := g.findObject? id | throw "no such object"
  let g := g.logMsg s!"{(g.player p).name} discards {card.name}{logSuffix}"
  let (g, _) := g.move id (.graveyard card.owner) none
  let g :=
    if countDiscard then
      g.modifyPlayer p (fun pl =>
        { pl with cardsDiscardedThisTurn := pl.cardsDiscardedThisTurn + 1 })
    else g
  return (g, card)

/-- Discard `id` from hand; if this finishes a pending “may discard, then draw”,
draw that many cards (CR 701.9). -/
def discardForDraw (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  match g.pending with
  | .mayDiscardDraw q n =>
    let (g, _) ← g.discardPendingCard p q id
    let g := g.draw p n
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | .maySacArtifactOrDiscard q n =>
    let (g, _) ← g.discardPendingCard p q id
    return g.finishSacArtifactOrDiscardDraw p n
  | .chooseDiscardCard q remaining =>
    let (g, card) ← g.discardPendingCard p q id
    let g := g.finishConniveDiscard card
    let g : Game :=
      if !g.lootLandEntersTapped || !card.printed.isLand then
        { g with lootLandEntersTapped := false }
      else
        let landed := g.followMoved card.id
        let g : Game := { g with lootLandEntersTapped := false }
        match g.findObject? landed with
        | none => g
        | some o =>
          let entered := g.putOntoBattlefield o.id q (tapped := true) (summoningSick := false)
          let g : Game := entered.1.logMsg s!"{o.name} enters the battlefield tapped"
          g.afterLandEnters (g.object! entered.2)
    if g.thirstDiscardsLeft > 0 then
      let left := if card.printed.isArtifact then 0 else g.thirstDiscardsLeft - 1
      let g := { g with thirstDiscardsLeft := left }
      if left == 0 then
        return { g with pending := .none }.receivePriority g.activePlayer
      else
        return g.beginDiscardCards #[p]
    if g.pendingDiscardsLeft > 0 then
      let left := g.pendingDiscardsLeft - 1
      let g := { g with pendingDiscardsLeft := left }
      if left == 0 then
        return g.beginDiscardCards remaining
      else
        return g.beginDiscardCards #[p]
    return g.beginDiscardCards remaining
  | .recruitDiscard q =>
    let (g, card) ← g.discardPendingCard p q id (countDiscard := false)
    let g := { g with pending := .none }
    let g :=
      if card.printed.isLand then g
      else
        let (g, _) := g.createToken p humanSoldierToken
        g
    return g.receivePriority g.activePlayer
  | .discardForAdditionalCost q =>
    let (g, _) ← g.discardPendingCard p q id
    match g.proposedSpell with
    | some prop =>
      let g := { g with pending := .none, proposedSpell := none, consecutivePasses := 0 }
      return g.becomeCast prop.caster (g.object! prop.spellId)
    | none => throw "No spell is waiting for an additional cost"
  | .payWard q _ cost =>
    if p != q then
      throw s!"Only {(g.player q).name} may discard for ward"
    let legal :=
      match cost with
      | .discardEnchantmentInstantOrSorcery =>
        match g.findObject? id with
        | some o =>
          o.printed.isEnchantment || o.printed.isInstant || o.printed.isSorcery
        | none => false
      | .discardOrPay _ => true
      | .discardCard => true
      | _ => false
    if !legal then
      throw "That card cannot pay this ward"
    let (g, _) ← g.discardPendingCard p q id (logSuffix := " (ward)")
    return g.afterWardResolved
  | _ => throw "Not time to discard a card (CR 701.9)"

/-- Pay a pending generic-mana “you may pay” or “unless pays” cost. -/
def payGeneric (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .mayPayGeneric q n =>
    if p != q then
      throw s!"Only {(g.player q).name} may pay \{{n}}"
    if !(g.player p).manaPool.canPay (ManaCost.ofGeneric n) then
      throw s!"{(g.player p).name} cannot pay \{{n}}"
    let g ← g.payCost p (ManaCost.ofGeneric n)
    let g := g.logMsg s!"{(g.player p).name} pays \{{n}}"
    let g := { g with pending := .none }
    let g :=
      match g.mayPayAlsoPlusOneOn.bind g.findObject? with
      | some o => if o.isOnBattlefield then g.addPlusOnePlusOneTo o 1 else g
      | none => g
    let g := { g with mayPayAlsoPlusOneOn := none }
    let g := g.draw p 1
    return g.receivePriority g.activePlayer
  | .payOrLetCounter q n _spellId =>
    if p != q then
      throw s!"Only {(g.player q).name} may pay \{{n}}"
    if !(g.player p).manaPool.canPay (ManaCost.ofGeneric n) then
      throw s!"{(g.player p).name} cannot pay \{{n}}"
    let g ← g.payCost p (ManaCost.ofGeneric n)
    let g := g.logMsg s!"{(g.player p).name} pays \{{n}}"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | .payWard q _ (.genericMana n) | .payWard q _ (.discardOrPay n) =>
    if p != q then
      throw s!"Only {(g.player q).name} may pay ward"
    if !(g.player p).manaPool.canPay (ManaCost.ofGeneric n) then
      throw s!"{(g.player p).name} cannot pay \{{n}}"
    let g ← g.payCost p (ManaCost.ofGeneric n)
    let g := g.logMsg s!"{(g.player p).name} pays \{{n}} (ward)"
    return g.afterWardResolved
  | _ => throw "Not time to pay generic mana"

/-- Put the pending card on top or bottom of its owner's library. -/
def chooseLibrarySide (g : Game) (p : PlayerId) (top : Bool) : Except String Game := do
  match g.pending with
  | .chooseLibraryPlacement q id =>
    if p != q then
      throw s!"Only {(g.player q).name} may choose top or bottom"
    let some o := g.findObject? id | throw "no such object"
    if !o.isOnBattlefield then
      throw s!"{o.name} is no longer on the battlefield"
    let dest := if top then Zone.library o.owner else Zone.library o.owner
    let side := if top then "top" else "bottom"
    let name := o.name
    let owner := o.owner
    let (g, newId) := g.move id dest none
    let pl := g.player owner
    let without := stripId pl.library newId
    let g :=
      if top then
        g.setPlayer { pl with library := without ++ #[newId] }
      else
        g.setPlayer { (g.player owner) with library := #[newId] ++ without }
    let g := g.logMsg s!"{(g.player owner).name} puts {name} on the {side} of their library"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | _ => throw "Not time to choose library placement"

/-- Attach Equipment or tap Humans, depending on pending. -/
def choosePermanents (g : Game) (p : PlayerId) (ids : Array ObjectId) :
    Except String Game := do
  match g.pending with
  | .mayAttachEquipment q hostId =>
    if p != q then
      throw s!"Only {(g.player q).name} may attach Equipment"
    if ids.size != 1 then
      throw "Choose one Equipment to attach"
    let some eq := g.findObject? ids[0]! | throw "no such object"
    if !(eq.isOnBattlefield && eq.printed.isEquipment && eq.controlledBy p) then
      throw s!"{eq.name} is not an Equipment you control"
    let some host := g.findObject? hostId | throw "The creature is no longer in play"
    if !host.isOnBattlefield then
      throw s!"{host.name} is no longer on the battlefield"
    let (g, ts) := g.bumpTime
    let g := g.setObject { eq with attachedTo := some host.id, timestamp := ts }
    let g := g.logMsg s!"{eq.name} attaches to {host.name}"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | .tapHumans q =>
    if p != q then
      throw s!"Only {(g.player q).name} may tap Humans"
    if !uniqueObjectIds ids then
      throw "Duplicate card"
    let mut g := g
    let mut n : Nat := 0
    for id in ids do
      let some o := g.findObject? id | throw "no such object"
      if !(o.isOnBattlefield && o.controlledBy p && g.hasSubtype o "Human" &&
          !o.status.tapped) then
        throw s!"{o.name} is not an untapped Human you control"
      g := g.applyPermanentAction o .tap
      n := n + 1
    g := { g with pending := .none }
    g := if n == 0 then g else g.draw p n
    return g.receivePriority g.activePlayer
  | .chooseTeamworkCreatures _ _ =>
    g.payTeamworkCreatures p ids
  | _ => throw "Not time to choose permanents"

/-- Cast the card Chandra, Torch of Defiance exiled, as her ability resolves.
Timing permissions are ignored, but its costs are paid (rulings 857 /
859). A land can't be cast (ruling 855). -/
def castExiledAsAbilityResolves (g : Game) (p : PlayerId) (id : ObjectId) :
    Except String Game := do
  match g.pending with
  | .mayCastExiledElseDamage q cardId _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may cast that card"
    if id != cardId then
      throw "That isn't the exiled card"
    let some card := g.findObject? id | throw "no such object"
    let face := card.printed
    if face.isLand then
      throw "An effect that lets you cast a card doesn't let you play a land (ruling 855)"
    if face.requiresTarget && (g.legalCastTargets p face).isEmpty && !face.allowsZeroTargets then
      throw s!"{face.name} requires a target"
    let cost := g.playManaCost card face
    let pl := g.player p
    let some pool := pl.manaPool.pay? cost
      | throw s!"{pl.name} cannot pay {cost}"
    let g := g.setPlayer { pl with manaPool := pool }
    let stackBefore := g.stack
    let (g, newId) := g.move id .stack (some p)
    let g := g.putStackEntry p newId
    let g := { g with pending := .none }
    let g := g.logMsg s!"{(g.player p).name} casts {face.name} as the ability resolves"
    if face.requiresTarget then
      let prop : ProposedSpell := {
        caster := p, cost := ManaCost.empty, spellId := newId, original := card
        handBefore := (g.player p).hand, stackBefore, manaBefore := pool }
      return { g with pending := .chooseTargets p, proposedSpell := some prop }
    else
      return g.becomeCast p (g.object! newId)
  | _ => throw "No exiled card may be cast now"

/-- Decline an optional discard (CR 608.2d) or choose no target for an
“up to one” trigger (CR 601.2c / 115.1c). -/
def decline (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .chooseMode q =>
    if p != q then throw s!"Only {(g.player q).name} may choose modes"
    match g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) with
    | some spell =>
      if (g.chosenModesOf spell).isEmpty then throw "Choose a mode (CR 700.2)"
      return (g.logMsg s!"{(g.player p).name} chooses no more modes").afterModesChosen p
    | none => throw "Choose a mode (CR 700.2)"
  | .mayCastExiledElseDamage q _ n =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to cast"
    let g := g.logMsg s!"{(g.player p).name} doesn't cast the exiled card"
    let g := g.forEachOpponent p (fun g pid => g.dealDamageToPlayer pid n)
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | .mayDiscardDraw q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to discard"
    let g := g.logMsg s!"{(g.player p).name} declines to discard a card"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | .chooseTargets caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may choose targets (CR 601.2c)"
    let some obj := g.objectAwaitingTargets | throw "No spell is waiting for a target (CR 601.2c)"
    match obj.triggeredAbility with
    | some ab =>
      if !ab.allowsZeroTargets then
        throw "That ability requires a target (CR 601.2c)"
      let g := g.setStackEntryTargets obj.id #[]
      let g := g.logMsg
        s!"{(g.player p).name} chooses no target (CR 603.3d / 601.2c)"
      return g.afterTriggerTargetsChosen
    | none =>
      let allowZero :=
        match g.currentSpellEffect obj with
        | some e => e.allowsZeroTargets
        | none => false
      if allowZero then
        let g := g.setStackEntryTargets obj.id #[]
        let g := g.logMsg
          s!"{(g.player p).name} chooses no target (CR 603.3d / 601.2c)"
        if g.proposedSpell.isSome then
          return g.afterTargetsChosen
        return g.afterTriggerTargetsChosen
      else if g.canSkipCurrentOptionalSlot obj then
        let g := g.skipOptionalTargetSlot obj.id
        let g := g.logMsg
          s!"{(g.player p).name} chooses no target (CR 603.3d / 601.2c)"
        if g.currentTargetSlot obj < (g.targetingOf obj).kind.spec.slots.size then
          return { g with pending := .chooseTargets p }
        if g.proposedSpell.isSome then
          return g.afterTargetsChosen
        return (g.markTargetsAnnounced obj.id true).afterTriggerTargetsChosen
      else if g.canFinishOptionalTargets obj then
        let g := g.logMsg
          s!"{(g.player p).name} finishes choosing targets (CR 601.2c)"
        if g.proposedSpell.isSome then
          return g.afterTargetsChosen
        return (g.markTargetsAnnounced obj.id true).afterTriggerTargetsChosen
      throw "That spell requires a target (CR 601.2c)"
  | .mayPayGeneric q _ =>
    let g := { g with mayPayAlsoPlusOneOn := none }
    if p != q then
      throw s!"Only {(g.player q).name} may decline to pay"
    let g := g.logMsg s!"{(g.player p).name} declines to pay"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | .payOrLetCounter q _ spellId =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to pay"
    let g := g.logMsg s!"{(g.player p).name} does not pay"
    let g := { g with pending := .none }
    let g := g.counterStackSpell spellId
    return g.receivePriority g.activePlayer
  | .payWard _ _ (.sacrificePermanents _ (_ + 1)) =>
    throw s!"{(g.player p).name} already began sacrificing permanents for ward and must finish"
  | .payWard q spellId _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to pay ward"
    let g := g.logMsg s!"{(g.player p).name} does not pay ward"
    let g := g.counterStackSpell spellId
    return g.afterWardResolved
  | .mayAttachEquipment q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to attach Equipment"
    let g := g.logMsg s!"{(g.player p).name} declines to attach Equipment"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | .tapHumans q =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to tap Humans"
    let g := g.logMsg s!"{(g.player p).name} taps no Humans"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | .maySacrificeAnotherBolg q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to sacrifice"
    let g := g.logMsg
      s!"{(g.player p).name} declines to sacrifice a creature to Bolg"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | .mayCastFromLooked q _ _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to cast a spell"
    g.chooseCastFromLooked p none
  | .mayPutLandFromHand q =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to put a land onto the battlefield"
    let g := g.logMsg
      s!"{(g.player p).name} declines to put a land onto the battlefield"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | .maySacArtifactOrDiscard q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline"
    let g := g.logMsg
      s!"{(g.player p).name} declines to sacrifice an artifact or discard a card"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | .mayPutArtifactFromHand q _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to put an artifact onto the battlefield"
    let g := g.logMsg
      s!"{(g.player p).name} declines to put an artifact onto the battlefield"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | .mayHaveVillainConnive q _ _ =>
    if p != q then
      throw s!"Only {(g.player q).name} may decline to have the Villain connive"
    let g := g.logMsg s!"{(g.player p).name} declines to have the Villain connive"
    let g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | _ => throw "Not time to decline"

def keepOpeningHand (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .declareMulligan q =>
    if p != q then
      throw "It's not your turn to declare a mulligan (CR 103.5)"
    let g := g.modifyPlayer p (fun pl => { pl with keptOpeningHand := true })
    let g := g.logMsg
      s!"{g.player p |>.name} keeps their opening hand of {(g.player p).hand.size}"
    return g.afterDeclaration p
  | _ => throw "Not time to keep an opening hand (CR 103.5)"

/-- Choose which legendary permanent to keep; the rest go to their owners'
graveyards (CR 704.5j). Then resume the CR 704.3 loop: recheck state-based
actions, put waiting triggers on the stack if none remain, and grant
priority only once that process is idle. -/
def keepLegend (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  match g.pending with
  | .chooseLegend q name ids =>
    if p != q then
      throw s!"Only {(g.player q).name} may choose which {name} to keep (CR 704.5j)"
    if !ids.contains id then
      throw s!"Choose one of the legendary permanents named {name} (CR 704.5j)"
    let some kept := g.findObject? id | throw "no such object"
    if !kept.isOnBattlefield then
      throw s!"{kept.name} is not on the battlefield"
    let mut g := g.logMsg
      s!"{(g.player p).name} keeps {kept.name} (legend rule, CR 704.5j)"
    for other in ids do
      if other != id then
        match g.findObject? other with
        | some o =>
          if o.isOnBattlefield then
            g := g.logMsg
              s!"{o.name} is put into its owner's graveyard (legend rule, CR 704.5j)"
            let (g', _) := g.move o.id (.graveyard o.owner) none
            g := g'
        | none => pure ()
    g := { g with pending := .none }
    return g.receivePriority g.activePlayer
  | _ => throw "Not time to apply the legend rule (CR 704.5j)"

/-- Put this player's waiting triggered abilities on the stack in the listed
source order (CR 603.3b). First listed is put first (farthest from the top). -/
def stackTriggers (g : Game) (p : PlayerId) (ids : Array ObjectId) : Except String Game := do
  match g.pending with
  | .chooseTriggerToStack q =>
    if p != q then
      throw s!"Only {(g.player q).name} may choose the order of triggered abilities (CR 603.3b)"
    let mine := g.waitingTriggersOf p
    if ids.size != mine.size then
      throw "List each waiting triggered ability's source once (CR 603.3b)"
    let mut remaining := mine
    let mut ordered : Array WaitingTrigger := #[]
    for id in ids do
      match remaining.findIdx? (fun wt => wt.source.id == id) with
      | none =>
        throw "That permanent has no waiting triggered ability to put on the stack (CR 603.3b)"
      | some i =>
        ordered := ordered.push remaining[i]!
        remaining := remaining.eraseIdx! i
    let g := { g with pending := .none }.logMsg
      s!"{(g.player p).name} chooses the order of triggered abilities (CR 603.3b)"
    let g := g.putTriggerBatch ordered
    if g.over || g.pending != .none then
      return g
    return g.receivePriority g.activePlayer false
  | _ => throw "Not time to choose triggered-ability order (CR 603.3b)"

/-- Record that this player will mulligan. The mulligan itself is taken only
after every remaining player has declared (CR 103.5). -/
def takeMulligan (g : Game) (p : PlayerId) : Except String Game := do
  match g.pending with
  | .declareMulligan q =>
    if p != q then
      throw "It's not your turn to declare a mulligan (CR 103.5)"
    if (g.player p).keptOpeningHand then
      throw "You already kept your opening hand (CR 103.5)"
    if !g.canTakeMulligan p then
      throw "A player may not take further mulligans after their opening hand would be zero cards (CR 103.5)"
    let g := { g with willMulligan := g.willMulligan.push p }
    let g := g.logMsg s!"{g.player p |>.name} will take a mulligan (CR 103.5)"
    return g.afterDeclaration p
  | _ => throw "Not time to take a mulligan (CR 103.5)"

/-- Place the listed cards on the bottom of `p`'s library. The first listed
card becomes the new bottom; later cards sit above it. -/
def putCardsOnBottom (g : Game) (p : PlayerId) (ids : Array ObjectId) : Except String Game := do
  match g.pending with
  | .putOnBottom q n =>
    if p != q then
      throw "Only the player who took a mulligan may put cards on the bottom (CR 103.5)"
    if ids.size != n then
      throw s!"Put exactly {n} card(s) on the bottom of your library (CR 103.5)"
    if !uniqueObjectIds ids then
      throw "Duplicate card"
    let pl := g.player p
    for id in ids do
      if (g.findObject? id).isNone then
        throw "no such object"
      if !pl.hand.contains id then
        throw "That card is not in your hand"
    let mut g := g
    let mut newBottom : Array ObjectId := #[]
    for id in ids do
      let card := g.object! id
      let ownerName := (g.player p).name
      let (g', newId) := g.move id (.library p)
      g := g'
      newBottom := newBottom.push newId
      g := g.logMsg s!"{ownerName} puts {card.name} on the bottom of their library"
    let plNow := g.player p
    let without := newBottom.foldl (fun lib id => stripId lib id) plNow.library
    g := g.setPlayer { plNow with library := newBottom ++ without }
    if g.mulliganToBottom.isEmpty then
      g := { g with pending := .none }
      return g.receivePriority g.activePlayer
    -- After a mulligan to zero, the player may not take further mulligans.
    if !g.canTakeMulligan p then
      g := g.modifyPlayer p (fun pl => { pl with keptOpeningHand := true })
      g := g.logMsg
        s!"{g.player p |>.name} keeps their opening hand of {(g.player p).hand.size}"
    return g.afterBottom p
  | _ => throw "Not time to put cards on the bottom (CR 103.5)"

/-- CR 103.3: shuffle remaining libraries, then draw opening hands. -/
partial def continueOpeningShuffles (g : Game) (next : Nat) : Game :=
  if next >= g.players.size then
    Id.run do
      let mut g := { g with afterRandom := .none, pending := .none }
      for pl in g.players do
        g := g.draw pl.id (g.player pl.id).startingHandSize
      return g.beginMulliganRound
  else
    let p : PlayerId := ⟨next⟩
    let g := g.requestShuffle p (.openingShuffles (next + 1))
    match g.pendingRandom? with
    | some _ => g
    | none =>
      let g := { g with afterRandom := .none }
      continueOpeningShuffles g (next + 1)

/-- Run the stored after-action. `grantPriority` is true when the host just
supplied a `--norandom` result (the original caller is no longer on the
stack). -/
partial def finishAfterRandom (g : Game) (grantPriority : Bool) : Game :=
  let after := g.afterRandom
  let g := { g with afterRandom := .none }
  let g :=
    match after with
    | .none => g
    | .draw p n => g.draw p n
    | .gainLife p n => g.gainLife p n
    | .openingShuffles next => continueOpeningShuffles g next
    | .mulliganQueue p rest =>
      let g := g.draw p (g.player p).startingHandSize
      executeMulliganQueue g rest
    | .setStartingPlayer i =>
      let n := g.players.size
      let i := if n == 0 then 0 else i % n
      let sp : PlayerId := ⟨i⟩
      let g := { g with startingPlayer := sp, activePlayer := sp, priority := sp }
      let g := g.logMsg s!"Starting player: {(g.player sp).name}"
      continueOpeningShuffles g 0
    | .revealRandomCreatureThenBottom _ _ => g
    | .putOnTop p ids => g.putIdsOnTop p ids
    | .beholdUntap p landId subtype => g.beholdAndMaybeUntap p landId subtype
    | .plusOne id => g.addPlusOneIfStillCreature id
  if grantPriority && g.pending == .none && !g.openingHandsPending && !g.over
      && !g.players.isEmpty then
    g.receivePriority g.activePlayer
  else g

/-- Apply a `--norandom` permutation or chosen object. -/
def supplyOrder (g : Game) (ids : Array ObjectId) : Except String Game := do
  match g.pending with
  | .resolveRandom req =>
    match req with
    | .shuffleLibrary p =>
      let pl := g.player p
      let ids := if ids.isEmpty then pl.library else ids
      if !isPermutation ids pl.library then
        throw "Shuffle must list each library card once (bottom first), or omit the ids to keep the current order"
      let g := { g with pending := .none }
      let g := g.setPlayer { (g.player p) with library := ids }
      return g.finishAfterRandom true
    | .orderInto expected dest =>
      let ids := if ids.isEmpty then expected else ids
      if !isPermutation ids expected then
        throw "Order must list each of those cards once, or omit the ids to keep their current order"
      let g := { g with pending := .none }
      let g := g.moveIdsInOrder ids dest
      return g.finishAfterRandom true
    | .chooseObject choices =>
      match ids[0]?, ids.size with
      | some id, 1 =>
        if !choices.contains id then
          throw "That is not one of the random choices"
        match g.afterRandom with
        | .revealRandomCreatureThenBottom controller revealed =>
          let g := { g with pending := .none, afterRandom := .none }
          let g := g.resolveRandomCreatureReveal controller revealed id
          match g.pendingRandom? with
          | some _ => return g
          | none => return g.finishAfterRandom true
        | _ =>
          let g := { g with pending := .none }
          return g.finishAfterRandom true
      | _, _ => throw "Pick exactly one of the listed objects"
    | .chooseIndex _ =>
      throw "Supply an index (random <n> or flip heads/tails)"
  | _ => throw "No random event is waiting for a result"

/-- Apply a `--norandom` index (starting player, coin toss). -/
def supplyIndex (g : Game) (i : Nat) : Except String Game := do
  match g.pending with
  | .resolveRandom (.chooseIndex n) =>
    if i >= n then
      throw s!"Choose a number from 0 to {n - 1}"
    let g := { g with pending := .none }
    match g.afterRandom with
    | .setStartingPlayer _ =>
      return finishAfterRandom { g with afterRandom := .setStartingPlayer i } true
    | _ =>
      return g.finishAfterRandom true
  | .resolveRandom _ =>
    throw "This random event needs an order or a chosen object, not an index"
  | _ => throw "No random event is waiting for a result"

end Game
end Mtg.Engine
