import Mtg.Engine.Game.EffectResolution

/-!
# Optional costs, cascade, and the Ring

Kicker (CR 702.32), gift, and teamwork announcements, cascade
(CR 702.84), copying spells, the Ring tempts you (CR 701.40), and
related resolution helpers.
-/

namespace Mtg.Engine
namespace Game

/-- Start an optional “discard a card. If you do, draw `n`” (CR 701.9 / 608.2d). -/
def beginMayDiscardDraw (g : Game) (p : PlayerId) (n : Nat) : Game :=
  let pl := g.player p
  if pl.hand.isEmpty then
    g.logMsg s!"{pl.name} has no card to discard"
  else
    { g with pending := .mayDiscardDraw p n }.logMsg
      s!"{pl.name} may discard a card. If they do, they draw {n}"

/-- Start “sacrifices a creature of their choice” for `p` (CR 701.17 / 608.2d). -/
def beginSacrificeCreature (g : Game) (p : PlayerId) : Game :=
  if (g.sacrificeCreatureChoices p).isEmpty then
    g.logMsg s!"{(g.player p).name} has no creature to sacrifice"
  else
    { g with pending := .sacrificeCreature p }.logMsg
      s!"{(g.player p).name} must sacrifice a creature of their choice"

/-- Apply `f` if the trigger's source is still on the battlefield. -/
def withTriggerSource (g : Game) (sourceId : Option ObjectId)
    (f : Game → GameObject → Game) : Game :=
  g.withSourceOnBattlefield sourceId f
    "The triggered ability's source is no longer in play"

/-- Apply `action` if the trigger's source is still on the battlefield. -/
def applyOnTriggerSource (g : Game) (sourceId : Option ObjectId) (action : PermanentAction) :
    Game :=
  g.applyOnSource sourceId action "The triggered ability's source is no longer in play"

/-- Queue “whenever the Ring tempts you” and “whenever you choose a
Ring-bearer” triggers for `p`. -/
def putRingTemptTriggers (g : Game) (p : PlayerId) (choseBearer : Bool) : Game :=
  let g := g.putControlledTriggers p .theRingTemptsYou
  if choseBearer then g.putControlledTriggers p .youChooseRingBearer else g

/-- As the Ring tempts `p`: get The Ring emblem if needed, gain its next
ability, then choose a Ring-bearer if `p` controls a creature. Re-choosing
the same creature still counts as choosing it. -/
def temptWithTheRing (g : Game) (p : PlayerId) (chosen : Option ObjectId := none) : Game :=
  let pl := g.player p
  let nextAbilities := min 4 (pl.theRingAbilities + 1)
  let gainedEmblem := pl.theRingAbilities == 0
  let g := g.modifyPlayer p (fun pl => { pl with theRingAbilities := nextAbilities })
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
  let g := g.setRingBearer p pick
  let g :=
    match pick with
    | some id =>
      g.logMsg s!"{(g.player p).name} chooses {(g.object! id).name} as their Ring-bearer"
    | none =>
      g.logMsg s!"{(g.player p).name} controls no creature to become Ring-bearer"
  g.putRingTemptTriggers p pick.isSome

/-- A targeted spell or ability that would tempt only does so if it resolves. -/
def resolveTargetedTempt (g : Game) (p : PlayerId) (kind : EffectTargetKind)
    (targets : Array Target) : Game :=
  if kind != .none && targets.isEmpty then
    g.logMsg "The spell doesn't resolve. The Ring won't tempt you."
  else
    g.withLegalKindTarget p kind targets (fun g _ => g.temptWithTheRing p)
      (missing := some "The spell doesn't resolve. The Ring won't tempt you.")

/-- Give the promised gift (a Treasure) to `to` before other effects. -/
def givePromisedGift (g : Game) (to : PlayerId) : Game :=
  let (g, _) := g.createToken to treasureToken
  g.logMsg s!"{(g.player to).name} is given a Treasure (gift)"

/-- Copy a spell on the stack. The copy is also kicked / has the same
promised gift. It is not cast. -/
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
    g.logMsg s!"A copy of {src.name} is created"

/-- Exile from the top until a nonland with mana value less than `maxMv`.
The resulting spell must also have lesser mana value. Casting is optional. -/
def resolveCascade (g : Game) (p : PlayerId) (maxMv : Nat) : Game :=
  Id.run do
    let mut g := g
    let mut exiled : Array ObjectId := #[]
    let mut found : Option GameObject := none
    while found.isNone && !(g.player p).library.isEmpty do
      match (g.player p).library.back? with
      | none => pure ()
      | some id =>
        let (g', newId) := g.move id .exile none
        g := g'
        exiled := exiled.push newId
        let card := g.object! newId
        if !card.printed.isLand && card.printed.manaCost.manaValue < maxMv then
          found := some card
    g := g.logMsg s!"{(g.player p).name} exiles cards for cascade (less than {maxMv})"
    match found with
    | none =>
      if g.norandom && exiled.size > 1 then
        return g.requestOrderInto exiled (.library p)
          s!"{(g.player p).name} puts the exiled cards on the bottom of their library in a random order"
      for id in exiled.reverse do
        let (g', _) := g.move id (.library (g.object! id).owner) none
        g := g'
      return g.logMsg "No cheaper nonland card was exiled"
    | some card =>
      let others := exiled.filter (· != card.id)
      if g.norandom && others.size > 1 then
        let g2 :=
          if card.printed.manaCost.manaValue < maxMv then
            g.logMsg
              s!"{(g.player p).name} may cast {card.name} without paying its mana cost (cascade)"
          else
            let (g', _) := g.move card.id (.library card.owner) none
            g'.logMsg
              s!"{card.name}'s resulting spell does not have lesser mana value"
        return g2.requestOrderInto others (.library p)
          s!"{(g.player p).name} puts the remaining exiled cards on the bottom of their library in a random order"
      for id in others.reverse do
        let (g', _) := g.move id (.library (g.object! id).owner) none
        g := g'
      if card.printed.manaCost.manaValue < maxMv then
        return g.logMsg
          s!"{(g.player p).name} may cast {card.name} without paying its mana cost (cascade)"
      else
        let (g', _) := g.move card.id (.library card.owner) none
        return g'.logMsg
          s!"{card.name}'s resulting spell does not have lesser mana value"

/-- Cast `cardId` from exile without paying its mana cost (cascade). -/
def castCascadeCard (g : Game) (p : PlayerId) (cardId : ObjectId) (maxMv : Nat) :
    Except String Game := do
  let some card := g.findObject? cardId | throw "no such card"
  if card.printed.isLand then
    throw "A land cannot be cast"
  if card.printed.manaCost.manaValue >= maxMv then
    throw "The resulting spell must have lesser mana value than the cascade spell"
  let (g, newId) := g.move cardId .stack (some p)
  let o := g.object! newId
  let g := g.setObject { o with
    playPermission := some {
      player := p
      turnEndsRemaining := 0
      withoutManaCost := true } }
  let g := g.putStackEntry p newId
  return g.becomeCast p (g.object! newId)

/-- Mark the proposed spell kicked and add the kicker cost. Cannot kick twice. -/
def applyKickerToProposed (g : Game) (kick : Bool) : Except String Game := do
  let some prop := g.proposedSpell | throw "No spell is waiting for kicker"
  if prop.kicked && kick then
    throw "The kicker ability doesn't let you pay a kicker cost more than once"
  if !kick then
    return { g with proposedSpell := some { prop with
      kicked := false, kickerAnnounced := true } }
  let some spell := g.findObject? prop.spellId | throw "The spell left the stack"
  match spell.printed.kicker with
  | none => throw "That spell has no kicker"
  | some kicker =>
    let g := g.setObject { spell with kicked := true }
    let face := spell.printed
    let start :=
      if !prop.cost.includesManaPayment && (playCostStart spell face).includesManaPayment then
        ManaCost.empty
      else playCostStart spell face
    let cost :=
      ManaCost.afterReduction face.manaCost
        (g.applyCastCostReductions spell face (start.addCost kicker))
    return { g with proposedSpell := some { prop with
      kicked := true
      kickerAnnounced := true
      cost } }

/-- Promise a gift to `to`. Cannot promise more than once. -/
def applyGiftToProposed (g : Game) (to : Option PlayerId) : Except String Game := do
  let some prop := g.proposedSpell | throw "No spell is waiting for a gift"
  if prop.giftTo.isSome && to.isSome then
    throw "You can't pay a gift cost more than once"
  let some spell := g.findObject? prop.spellId | throw "The spell left the stack"
  let g := g.setObject { spell with giftPromisedTo := to }
  return { g with proposedSpell := some { prop with
    giftTo := to, giftAnnounced := true } }

/-- Continue the proposal window after kicker / gift announcements. -/
def afterOptionalAdditionalCost (g : Game) (p : PlayerId) : Game :=
  match g.proposedSpell, g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) with
  | some prop, some spell =>
    if spell.printed.giftTreasure && !prop.giftAnnounced then
      let g := { g with pending := .chooseGift p }
      g.logMsg s!"{(g.player p).name} may promise a gift (CR 702.185)"
    else if spell.printed.teamwork.isSome && !prop.teamworkAnnounced then
      let g := { g with pending := .chooseTeamwork p }
      g.logMsg s!"{(g.player p).name} may pay a teamwork cost (CR 702.194)"
    else
      g.afterAdditionalCostAnnounced
  | _, _ => g

def announceKicker (g : Game) (p : PlayerId) (kick : Bool) : Except String Game := do
  match g.pending with
  | .chooseKicker caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may announce kicker"
    let g ← g.applyKickerToProposed kick
    let g := g.logMsg
      (if kick then s!"{(g.player p).name} kicks the spell"
       else s!"{(g.player p).name} does not kick the spell")
    return g.afterOptionalAdditionalCost p
  | _ => throw "Not time to announce kicker"

def announceGift (g : Game) (p : PlayerId) (to : Option PlayerId) : Except String Game := do
  match g.pending with
  | .chooseGift caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may promise a gift"
    if let some opp := to then
      if opp == p then throw "You must promise the gift to an opponent"
    let g ← g.applyGiftToProposed to
    let g :=
      match to with
      | some opp =>
        g.logMsg s!"{(g.player p).name} promises a gift to {(g.player opp).name}"
      | none =>
        g.logMsg s!"{(g.player p).name} does not promise a gift"
    return g.afterOptionalAdditionalCost p
  | _ => throw "Not time to promise a gift"

def announceTeamwork (g : Game) (p : PlayerId) (pay : Bool) : Except String Game := do
  match g.pending with
  | .chooseTeamwork caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may announce teamwork"
    let some prop := g.proposedSpell | throw "No spell is waiting for teamwork"
    if !pay then
      let g := { g with proposedSpell := some { prop with
        teamworkPaid := false, teamworkAnnounced := true } }
      let g := g.logMsg s!"{(g.player p).name} does not pay a teamwork cost"
      return g.afterOptionalAdditionalCost p
    match prop.original.printed.teamwork.orElse (fun () =>
        (g.findObject? prop.spellId).bind (fun o => o.printed.teamwork)) with
    | none => throw "That spell has no teamwork"
    | some need =>
      let g := { g with
        pending := .chooseTeamworkCreatures p need
        proposedSpell := some { prop with teamworkAnnounced := true } }
      return g.logMsg
        s!"{(g.player p).name} chooses creatures to tap for teamwork {need}"
  | _ => throw "Not time to announce teamwork"

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
        if o.status.tapped then pick rest acc total
        else pick rest (acc.push o.id) (total + g.power o)
  pick (g.creaturesControlledBy p).toList #[] 0

def payTeamworkCreatures (g : Game) (p : PlayerId) (ids : Array ObjectId) :
    Except String Game := do
  match g.pending with
  | .chooseTeamworkCreatures caster need =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may tap creatures for teamwork"
    let some prop := g.proposedSpell | throw "No spell is waiting for teamwork"
    let mut total : Int := 0
    let mut seen : Array ObjectId := #[]
    for id in ids do
      if seen.contains id then
        throw "A creature cannot be tapped twice for the same teamwork cost"
      seen := seen.push id
      let some o := g.findObject? id | throw "no such object"
      if !(o.isOnBattlefield && o.isCreature && o.controlledBy p) then
        throw s!"{o.name} is not a creature you control"
      if o.status.tapped then
        throw s!"{o.name} is already tapped"
      total := total + g.power o
    if total < (need : Int) then
      throw s!"Tapped creatures must have total power {need} or more"
    let mut g := g
    for id in ids do
      match g.findObject? id with
      | none => pure ()
      | some o =>
        g := g.applyPermanentAction o .tap
        g := g.putMatchingSourceTriggers p (g.object! id) .tappedForTeamwork
    let some spell := g.findObject? prop.spellId | throw "The spell left the stack"
    g := g.setObject { spell with teamworkPaid := true }
    g := { g with
      pending := .none
      proposedSpell := some { prop with teamworkPaid := true, teamworkAnnounced := true } }
    g := g.logMsg s!"{(g.player p).name} pays a teamwork cost"
    return g.afterOptionalAdditionalCost p
  | _ => throw "Not time to tap creatures for teamwork"

def announceRingBearer (g : Game) (p : PlayerId) (id : Option ObjectId) : Except String Game := do
  match g.pending with
  | .chooseRingBearer caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may choose a Ring-bearer"
    let choices := g.ringBearerChoices p
    if id.isNone && !choices.isEmpty then
      throw "You must choose a creature if you control one"
    let g := { g with pending := .none }
    return g.temptWithTheRing p id
  | _ => throw "Not time to choose a Ring-bearer"

/-- Search for up to `max` basic Plains, exile them linked to `sourceId`,
shuffle, and gain `life`. -/
def resolveSearchBasicPlainsExile (g : Game) (p : PlayerId)
    (sourceId : Option ObjectId) (max life : Nat) : Game :=
  Id.run do
    let mut g := g
    for _ in [0:max] do
      match g.findLibraryCard? p (fun c => isBasicLandCard c && c.hasSubtype "Plains") with
      | none => pure ()
      | some id =>
        let name := (g.object! id).name
        let (g', newId) := g.move id .exile none
        g := g'
        match sourceId.bind g.findObject? with
        | some src =>
          g := g.setObject { src with linkedExile := src.linkedExile.push newId }
        | none => pure ()
        g := g.logMsg s!"{(g.player p).name} exiles {name}"
    g := g.requestShuffle p (.gainLife p life)
    return g.continueIfShuffled

/-- Target opponent reveals their hand; you discard a nonland of your choice. -/
def discardNonlandFrom (g : Game) (controller victim : PlayerId) : Game :=
  let names :=
    (g.player victim).hand.filterMap (fun id =>
      (g.findObject? id).map (·.name))
  let g :=
    if names.isEmpty then
      g.logMsg s!"{(g.player victim).name} reveals an empty hand"
    else
      g.logMsg
        s!"{(g.player victim).name} reveals {String.intercalate ", " names.toList}"
  match (g.player victim).hand.findSome? (fun id =>
      match g.findObject? id with
      | some o => if !o.printed.isLand then some o else none
      | none => none) with
  | none => g.logMsg s!"{(g.player victim).name} has no nonland card to discard"
  | some o =>
    let (g, _) := g.move o.id (.graveyard o.owner) none
    g.logMsg s!"{(g.player controller).name} chooses {o.name}. {(g.player victim).name} discards it"

/-- Exile `o` and return it at the beginning of the next end step. -/
def exileUntilNextEndStep (g : Game) (o : GameObject) : Game :=
  let name := o.name
  let (g, newId) := g.move o.id .exile none
  let g := { g with delayedEndStepReturns := g.delayedEndStepReturns.push newId }
  g.logMsg s!"{name} is exiled until the beginning of the next end step"

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
    if !land.printed.isLand then
      throw s!"{land.name} is not a land card"
    let (g, newId) := g.putOntoBattlefield id p (tapped := true) (summoningSick := false)
    let g := { g with pending := .none }
    return g.afterLandEnters (g.object! newId) |>.receivePriority g.activePlayer
  | _ => throw "Not time to put a land from hand onto the battlefield"

/-- Create a Food (0) or Treasure (1) token. -/
def chooseFoodOrTreasure (g : Game) (p : PlayerId) (idx : Nat) :
    Except String Game := do
  match g.pending with
  | .chooseFoodOrTreasure q =>
    if p != q then
      throw s!"Only {(g.player q).name} may choose Food or Treasure"
    if idx > 1 then
      throw "Choose Food or Treasure"
    let g := { g with pending := .none }
    let kind := if idx == 0 then TokenKind.food else TokenKind.treasure
    return g.createKindTokens p kind 1 |>.receivePriority g.activePlayer
  | _ => throw "Not time to choose Food or Treasure"

/-- Tap (0) or untap (1) the pending nonland. -/
def chooseTapOrUntap (g : Game) (p : PlayerId) (idx : Nat) (targetId : ObjectId) :
    Except String Game := do
  match g.pending with
  | .chooseTapOrUntap q tid =>
    if p != q then
      throw s!"Only {(g.player q).name} may choose tap or untap"
    if tid != targetId then
      throw "That is not the targeted permanent"
    if idx > 1 then
      throw "Choose tap or untap"
    let some o := g.findObject? tid | throw "The target is no longer legal"
    if !o.isOnBattlefield || o.printed.isLand then
      throw "The target is no longer legal"
    let g := { g with pending := .none }
    let g :=
      if idx == 0 then g.applyPermanentAction o .tap
      else g.applyPermanentAction o .untap
    return g.receivePriority g.activePlayer
  | _ => throw "Not time to choose tap or untap"

end Game
end Mtg.Engine
