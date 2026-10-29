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
    g.change (.pending (.mayDiscardDraw p n))
      |>.logMsg s!"{pl.name} may discard a card. If they do, they draw {n}"

/-- Start “sacrifices a creature of their choice” for `p` (CR 701.21 / 608.2d). -/
def beginSacrificeCreature (g : Game) (p : PlayerId) : Game :=
  if (g.sacrificeCreatureChoices p).isEmpty then
    g.logMsg s!"{(g.player p).name} has no creature to sacrifice"
  else
    g.change (.pending (.sacrificeCreature p))
      |>.logMsg s!"{(g.player p).name} must sacrifice a creature of their choice"

/-- Apply `f` if the trigger's source is still on the battlefield. -/
def withTriggerSource (g : Game) (sourceId : Option ObjectId)
    (f : Game → GameObject → Game) : Game :=
  g.withSourceOnBattlefield sourceId f
    "The triggered ability's source is no longer in play"

/-- Apply `action` if the trigger's source is still on the battlefield. -/
def applyOnTriggerSource (g : Game) (sourceId : Option ObjectId) (action : PermanentAction) :
    Game :=
  g.applyOnSource sourceId action "The triggered ability's source is no longer in play"

/-- As the Ring tempts `p`: get The Ring emblem if needed, gain its next
ability, then choose a Ring-bearer if `p` controls a creature. Re-choosing
the same creature still counts as choosing it. -/
def temptWithTheRing (g : Game) (p : PlayerId) (chosen : Option ObjectId := none) : Game :=
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
  let cause := g.resolvingOneShotCause p
  let g := g.setRingBearer p pick (cause := cause)
  let g :=
    match pick with
    | some id =>
      g.logMsg s!"{(g.player p).name} chooses {(g.object! id).name} as their Ring-bearer"
    | none =>
      g.logMsg s!"{(g.player p).name} controls no creature to become Ring-bearer"
  g.record (GameEvent.ringTempted g.turnNumber p pick nextAbilities (cause := cause))

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

/-- Cascade (CR 702.85a): exile from the top until a nonland card with mana
value less than `maxMv`. The player may cast it without paying its mana
cost; the other exiled cards go on the bottom in a random order. -/
def resolveCascade (g : Game) (p : PlayerId) (maxMv : Nat) : Game :=
  Id.run do
    let (g0, cause) := g.allocDelayedCause (some p)
    let mut g := g0
    let mut exiled : Array ObjectId := #[]
    let mut found : Option GameObject := none
    while found.isNone && !(g.player p).library.isEmpty do
      match (g.player p).library.back? with
      | none => pure ()
      | some id =>
        let (g', newId) := g.move id .exile none (cause := some cause)
        g := g'
        exiled := exiled.push newId
        let card := g.object! newId
        if !card.printed.isLand && card.printed.manaCost.manaValue < maxMv then
          found := some card
    g := g.logMsg s!"{(g.player p).name} exiles cards for cascade (less than {maxMv})"
    match found with
    | none =>
      return g.requestOrderInto exiled (.library p)
        s!"No cheaper nonland card was exiled; {(g.player p).name} puts the exiled cards on the bottom of their library in a random order"
        (cause := some cause)
    | some card =>
      let others := exiled.filter (· != card.id)
      return g.change (.pending (.fraChoice p (.mayCastCascade card.id others)))
        |>.logMsg s!"{(g.player p).name} may cast {card.name} without paying its mana cost (cascade)"

/-- Mark the proposed spell kicked and add the kicker cost. Cannot kick twice. -/
def applyKickerToProposed (g : Game) (kick : Bool) : Except String Game := do
  let some prop := g.proposedSpell | throw "No spell is waiting for kicker"
  if prop.kicked && kick then
    throw "The kicker ability doesn't let you pay a kicker cost more than once"
  if !kick then
    return g.changeProposals #[.kicked false, .kickerAnnounced true]
  let some spell := g.findObject? prop.spellId | throw "The spell left the stack"
  let face := spell.printed
  match face.morph, face.impending, face.kicker with
  | some alt, _, none =>
    let g := g.changeStatus spell.id (.faceDown true)
    let cost := ManaCost.afterReduction alt (g.applyCastCostReductions spell face alt)
    return g.changeProposals #[.kicked true, .kickerAnnounced true, .cost cost]
  | _, some (n, alt), none =>
    let g := g.record (GameEvent.announced g.turnNumber spell.id (costs := #[.impending n]))
    let cost := ManaCost.afterReduction alt (g.applyCastCostReductions spell face alt)
    return g.changeProposals #[.kicked true, .kickerAnnounced true, .cost cost]
  | _, _, none => throw "That spell has no kicker"
  | _, _, some kicker =>
    let g := g.record (GameEvent.announced g.turnNumber spell.id (costs := #[.kicker]))
    let start :=
      if !prop.cost.includesManaPayment && (g.playCostStart spell face).includesManaPayment then
        ManaCost.empty
      else g.playCostStart spell face
    let cost :=
      ManaCost.afterReduction face.manaCost
        (g.applyCastCostReductions spell face (start.addCost kicker))
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

/-- Continue the proposal window after kicker / gift announcements. -/
def afterOptionalAdditionalCost (g : Game) (p : PlayerId) : Game :=
  match g.proposedSpell, g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) with
  | some prop, some spell =>
    if spell.printed.giftTreasure && !prop.giftAnnounced then
      let g := g.change (.pending (.chooseGift p))
      g.logMsg s!"{(g.player p).name} may promise a gift (CR 702.185)"
    else if spell.printed.teamwork.isSome && !prop.teamworkAnnounced then
      let g := g.change (.pending (.chooseTeamwork p))
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
    let face? := g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) |>.map (·.printed)
    let g := g.logMsg
      (if kick && (face?.bind (·.morph)).isSome then s!"{(g.player p).name} casts the spell face down"
       else if kick && (face?.bind (·.impending)).isSome then s!"{(g.player p).name} casts the spell for its impending cost"
       else if kick then s!"{(g.player p).name} kicks the spell"
       else s!"{(g.player p).name} pays the printed cost")
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
      let g := g.changeProposals #[.teamworkPaid false, .teamworkAnnounced true]
      let g := g.logMsg s!"{(g.player p).name} does not pay a teamwork cost"
      return g.afterOptionalAdditionalCost p
    match prop.original.printed.teamwork.orElse (fun () =>
        (g.findObject? prop.spellId).bind (fun o => o.printed.teamwork)) with
    | none => throw "That spell has no teamwork"
    | some need =>
      let g := g.change (.pending (.chooseTeamworkCreatures p need))
        |>.changeProposal (.teamworkAnnounced true)
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
        g := g.becomeTapped o (cause := some (.costPayment .teamwork p (some prop.spellId)))
    let some spell := g.findObject? prop.spellId | throw "The spell left the stack"
    g := g.record (GameEvent.announced g.turnNumber spell.id (costs := #[.teamwork ids])
      (cause := some (.costPayment .teamwork p (some spell.id))))
    g := g.change (.pending .none)
      |>.changeProposals #[.teamworkPaid true, .teamworkAnnounced true]
    g := g.logMsg s!"{(g.player p).name} pays a teamwork cost"
    -- “If this spell was cast using teamwork, choose both instead.”
    if spell.printed.chooseBothIfTeamwork then
      let chosen := g.chosenModesOf spell
      for i in [0:spell.printed.spellModes.size] do
        if !chosen.contains i then
          g := (if (g.chosenModesOf spell).isEmpty then g.setProposedMode i else g.addProposedExtraMode i)
      g := g.logMsg s!"{(g.player p).name} chooses both modes (teamwork)"
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
    let g := g.change (.pending .none)
    return g.temptWithTheRing p id
  | _ => throw "Not time to choose a Ring-bearer"

/-- Search for up to `max` basic Plains, exile them linked to `sourceId`,
shuffle, and gain `life`. -/
def resolveSearchBasicPlainsExile (g : Game) (p : PlayerId)
    (sourceId : Option ObjectId) (max life : Nat) : Game :=
  g.beginLibrarySearch p (fun c => isBasicLandCard c && c.hasSubtype .plains)
    "a basic Plains card" (.exileLinked sourceId) (count := max)
    (after := some (.gainLife life))

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
def exileUntilNextEndStep (g : Game) (o : GameObject)
    (cause : Option EventCause := none) : Game :=
  let name := o.name
  let (g, cause) :=
    match cause with
    | some c => (g, c)
    | none => g.allocDelayedCause o.controller
  let (g, newId) := g.move o.id .exile none (cause := some cause)
  let ctrl := o.controller.getD o.owner
  let g := g.change (.pushDelayedTrigger { controller := ctrl, source := some o, kind := .endStepReturn newId, cause })
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
    let g := g.change (.pending .none)
    return g.afterLandEnters (g.object! newId) |>.receivePriority g.activePlayer
  | _ => throw "Not time to put a land from hand onto the battlefield"

end Game
end Mtg.Engine
